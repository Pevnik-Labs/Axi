{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections #-}

-- | Author: Mateusz Pyzik
module Main where

import Control.Monad (forM, forM_, forever, when)
import Control.Monad.Error.Class (MonadError (catchError, throwError))
import Control.Monad.Reader (ReaderT (..))
import Control.Monad.Reader.Class (MonadReader (..), asks)
import Control.Monad.State.Class (MonadState (..), put)
import Control.Monad.State.Strict (StateT, runStateT)
import Data.Foldable qualified as F
import Data.Functor ((<&>))
import Data.HashMap.Internal.Strict qualified as HM
import Data.IORef (IORef, newIORef, readIORef, writeIORef)
import Data.List (intersperse)
import Data.Map.Strict qualified as M
import Data.Maybe (fromMaybe)
import Data.Sequence (Seq (..))
import Data.Sequence qualified as S
import Data.String (IsString (fromString))
import Data.Text qualified as T
import Data.Text qualified as Text
import Data.Text.IO qualified as TIO
import Numeric.Natural (Natural)
import Qty (Qty, suffixQty)
import Syntax.Abs
import Syntax.Layout (resolveLayout)
import Syntax.Lex (Token, mkPosToken)
import Syntax.Par (myLexer, pListDec, pRepl)
import Syntax.Print (Print, printTree)
import System.Environment (getArgs)
import System.Exit (exitFailure)
import Tc
import Text.Read (readMaybe)

runTc :: Ctx -> StateT Ctx m a -> m (a, Ctx)
runTc = flip runStateT

runRb :: ReaderT RbCtx m a -> m a
runRb ma = runReaderT ma RbCtx {next = HM.empty, used = S.empty}

desugarDecs :: (MonadError TcErr m) => [Dec] -> m [(Name, Exp)]
desugarDecs = traverse desugarDec

desugarDec :: (MonadError TcErr m) => Dec -> m (Name, Exp)
desugarDec (ConstantD (ValueR pat e)) = case patToNameParamsAnn pat of
  Nothing -> todo Empty "desugarDec"
  Just (x, params, Nothing) -> pure (x, FunE params e)
  Just (x, params, Just t) -> pure (x, FunE params (AnnE e t))
desugarDec _ = todo Empty "desugarDec"

patToNameParamsAnn :: Pat -> Maybe (Name, [Param], Maybe Exp)
patToNameParamsAnn (AnnP pat t) =
  patToNameParams pat [] (Just t)
patToNameParamsAnn pat = patToNameParams pat [] Nothing

patToNameParams :: Pat -> [Param] -> c -> Maybe (Name, [Param], c)
patToNameParams (CallP p param params) acc t =
  patToNameParams p (param : params ++ acc) t
patToNameParams (VarP x) acc t = Just (idName x, acc, t)
patToNameParams _ _ _ = Nothing

data RbCtx = RbCtx
  { next :: HM.HashMap T.Text Word,
    used :: S.Seq OptName
  }

extendRb :: RbCtx -> Name -> (Int, Name, RbCtx)
extendRb RbCtx {next = n, used = u} x =
  let i = fromMaybe 0 (HM.lookup (nameText x) n)
      n' = HM.insert (nameText x) (i + 1) n
      x' = x {nameText = nameText x <> T.pack (show i)}
      d = S.length u
      u' = u :|> Just x'
   in (d, x, RbCtx {next = n', used = u'})

withName :: (MonadReader RbCtx m) => OptName -> (Int -> Name -> m a) -> m a
withName Nothing action = withName (Just "x") action
withName (Just x) action = do
  rbCtx <- ask
  let (d, name, rbCtx') = extendRb rbCtx x
  local (const rbCtx') (action d name)

nameE :: Name -> Exp
nameE x = VarE (nameId x)

numberE :: Natural -> Exp
numberE n = NumberE (Number (T.pack (show n)))

callE :: Exp -> [Arg] -> Exp
callE e [] = e
callE (CallE e args) args' = CallE e (args ++ args')
callE e args = CallE e args

appE :: [Exp] -> Maybe Exp
appE [] = Nothing
appE (e : es) = Just (callE e (argA Bare <$> es))

infixlE :: Exp -> Exp -> [Exp] -> Exp
infixlE e' e es = fromMaybe e' (appE (intersperse e es))

nameP :: Name -> Pat
nameP x = VarP (nameId x)

tupleE :: [Exp] -> Exp
tupleE [] = UnitE
tupleE (e : es) = TupleE e es

argA :: ArgFlavour -> Exp -> Arg
argA Bare e = BareA e
argA _ e = AtA e

argP :: ArgFlavour -> Pat -> Param
argP Bare p = BareP p
argP At p = AtP p
argP Hash p = HashP p

readbackVar :: (MonadReader RbCtx m) => Index -> m Exp
readbackVar (Here i) =
  asks (nameE . fromMaybe "??" . flip S.index i . used)
readbackVar _ = pure (nameE "??")

readbackExp :: (MonadReader RbCtx m) => Tm -> m Exp
readbackExp (Bot k) =
  AnnE (nameE "Bot") <$> readbackExp k
readbackExp (Top k) =
  AnnE (nameE "Top") <$> readbackExp k
readbackExp Level = pure (nameE "Level")
readbackExp (Max vs Zero) = do
  vs' <- traverse (readbackExp . (\(ix, (f, t)) -> Var f ix t)) (M.toList vs)
  pure (infixlE (numberE 0) (nameE "⊔") vs')
readbackExp (Max vs u) = do
  vs' <- traverse (readbackExp . (\(ix, (f, t)) -> Var f ix t)) (M.toList vs)
  u' <- readbackExp u
  pure (infixlE undefined (nameE "⊔") (vs' ++ [u']))
readbackExp Nat = pure (nameE "Nat")
readbackExp Zero = pure (numberE 0)
readbackExp (t :+$ n) = readbackPlus t (succ n)
readbackExp (Type r (Small l)) = do
  t' <- readbackExp l
  pure $ callE (readbackSort r) [argA At t']
readbackExp (Type r (Big l)) =
  pure $
    callE
      (readbackSort r)
      [argA At (infixlE undefined (nameE "+") [nameE "ω", numberE l])]
readbackExp (Var _ ix k) = do
  AnnE <$> readbackVar ix <*> readbackExp k
readbackExp (t :-> u) =
  ArrowE <$> readbackExp t <*> readbackExp u
readbackExp (Con x k ts) = do
  k' <- readbackExp k
  ts' <- traverse readbackArg ts
  pure $
    callE
      (AnnE (ExplicitE (nameId x)) k')
      (F.toList ts')
readbackExp (Product ts) =
  infixlE (nameE "Unit") (nameE "*") <$> traverse readbackExp (F.toList ts)
readbackExp (Tuple ts) = tupleE . F.toList <$> traverse readbackExp ts
readbackExp (Sum t u) = do
  t' <- readbackExp t
  u' <- readbackExp u
  pure $
    callE
      (nameE "Either")
      [ argA At t',
        argA At u'
      ]
readbackExp (Box r t) =
  readbackExp t <&> \t' ->
    callE (readbackBox r) [BareA t']
readbackExp (Forall a x k t) = do
  k' <- readbackExp k
  withName x $ \i x' -> do
    ForallE (MkP [argP a (AnnP (nameP x') k')] NoAnn)
      <$> readbackExp (enter (var i k) t)
readbackExp (Fun a x k t) = do
  k' <- readbackExp k
  withName x $ \i x' -> do
    FunE
      [argP a (AnnP (nameP x') k')]
      <$> readbackExp (enter (var i k) t)

readbackPlus :: (MonadReader RbCtx m) => Tm -> Natural -> m Exp
readbackPlus Zero n = pure (numberE n)
readbackPlus (t :+$ m) n = readbackPlus t (succ m + n)
readbackPlus t n =
  readbackExp t <&> \t' -> infixlE undefined (nameE "+") [t', numberE n]

readbackSort :: Qty -> Exp
readbackSort r = nameE (fromString ("Type" <> suffixQty r))

readbackBox :: Qty -> Exp
readbackBox r = nameE (fromString ("Box" <> suffixQty r))

readbackArg :: (MonadReader RbCtx m) => (ArgFlavour, Tm) -> m Arg
readbackArg (Bare, t) = BareA <$> readbackExp t
readbackArg (_, t) = argA At <$> readbackExp t

type Parser a = [Token] -> Either String a

run :: (Print a, Show a) => Parser a -> Text.Text -> IO a
run p s = case p ts of
  Left err -> do
    putStrLn "\nParse failed!\n"
    putStrLn "Tokens:"
    forM_ ts $ \t ->
      putStrLn (showPosToken (mkPosToken t))
    putStrLn err
    exitFailure
  Right tree -> pure tree
  where
    ts = resolveLayout True (myLexer s)
    showPosToken ((l, c), t) = concat [show l, ":", show c, " ", show t]

main :: IO ()
main = do
  args <- getArgs
  env <- newIORef mempty
  ctx <- newIORef Empty
  loadFile env ctx "Prelude.txt"
  buffer <- newIORef Text.empty
  case args of
    ["--help"] -> do
      putStrLn $
        unlines
          [ "usage: Call with one of the following argument combinations:",
            "  --help          Display this help message.",
            "  (files)         Load content of files, then enter REPL"
          ]
    fs -> do
      mapM_ (loadFile env ctx) fs
      forever $ do
        putStrLn "repl>"
        nextPart <- getNextPart buffer
        run pRepl nextPart >>= evalAndPrint env ctx

delimiter :: Text.Text
delimiter = ";;"

getNextPart :: IORef Text.Text -> IO Text.Text
getNextPart bufferRef = readIORef bufferRef >>= go
  where
    go oldBuffer = do
      let (chunk, newBuffer) = Text.breakOn delimiter oldBuffer
      if Text.null newBuffer
        then do
          line <- TIO.getLine
          go $! Text.append oldBuffer (Text.snoc line '\n')
        else do
          writeIORef bufferRef $!
            fromMaybe newBuffer (Text.stripPrefix delimiter newBuffer)
          return chunk

type SemEnv = [()]

evalExp :: Exp -> SemEnv -> (Exp, SemEnv)
evalExp = (,)

evalDecs :: [Dec] -> SemEnv -> ([Dec], SemEnv)
evalDecs = (,)

loadFile :: IORef SemEnv -> IORef Ctx -> FilePath -> IO ()
loadFile ref ctx m = do
  putStrLn m
  text <- TIO.readFile m
  decs <- run pListDec text
  putStrLn (printTree decs)
  ok <- checkDecsIO ctx decs
  when ok $ do
    env <- readIORef ref
    let (decs', env') = evalDecs decs env
    putStrLn (printTree decs')
    writeIORef ref env'

evalAndPrint :: IORef SemEnv -> IORef Ctx -> Repl -> IO ()
evalAndPrint ref ctx entry = do
  env <- readIORef ref
  case entry of
    LetR decs -> do
      ok <- checkDecsIO ctx decs
      when ok $ do
        let (_, env') = evalDecs decs env
        writeIORef ref env'
    ExpR e -> do
      ctx0 <- readIORef ctx
      case runTc ctx0 (infer e >>= runRb . readbackExp) of
        Left err -> printTcErr err
        Right (sig, ctx1) -> do
          writeIORef ctx ctx1
          putStrLn (printTree e ++ " : " ++ printTree sig)
          let (e', env') = evalExp e env
          writeIORef ref env'
          putStrLn (printTree e')
    RequireR str ->
      case fromStrToString str of
        Nothing -> putStrLn "Syntax error: not a file name"
        Just fp -> loadFile ref ctx fp

fromStrToString :: Str -> Maybe FilePath
fromStrToString (Str txt) = readMaybe (T.unpack txt)

printTcErr :: TcErr -> IO ()
printTcErr (Nested msg err) = do
  TIO.putStrLn msg
  printTcErr err
printTcErr (TypeError ctx t) = do
  mapM_ print ctx
  TIO.putStrLn "|-"
  print t
printTcErr (Anomaly msg) = TIO.putStrLn msg
printTcErr (NotImplemented ctx msg) = do
  mapM_ print ctx
  TIO.putStrLn "|-"
  TIO.putStr "Not implemented: "
  TIO.putStrLn msg

printName :: Name -> T.Text
printName x = case namePos x of
  Nothing -> nameText x
  Just (l, c) -> nameText x <> T.pack (':' : show l ++ ':' : show c)

checkDecsIO :: IORef Ctx -> [Dec] -> IO Bool
checkDecsIO ctx decs = do
  ctx0 <- readIORef ctx
  case runStateT (checkDecs decs) ctx0 of
    Left err -> False <$ printTcErr err
    Right (sigs, ctx1) -> do
      writeIORef ctx ctx1
      forM_ sigs $ \(x, t) ->
        TIO.putStrLn (nameText x <> " : " <> T.pack (printTree t))
      pure True

checkDecs ::
  (MonadState Ctx m, MonadError TcErr m) =>
  [Dec] ->
  m [(Name, Exp)]
checkDecs decs = do
  case desugarDecs decs of
    Left err -> throwError (Nested "Desugaring failed..." err)
    Right decs' -> forM decs' $ \(x, e) -> do
      s <- catchError (infer e) $ \err ->
        throwError (Nested ("Error at " <> printName x <> ":") err)
      (x,) <$> runRb (readbackExp s)

infer :: (MonadState Ctx m, MonadError TcErr m) => Exp -> m Tm
infer e = do
  ctx <- get
  (_, (t, ctx')) <- ctx |- Elab mempty e [] Infer
  put ctx'
  pure t
