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
import Data.HashMap.Internal.Strict qualified as HM
import Data.IORef (IORef, newIORef, readIORef, writeIORef)
import Data.Maybe (fromMaybe)
import Data.Sequence (Seq (..))
import Data.Sequence qualified as S
import Data.Text qualified as T
import Data.Text qualified as Text
import Data.Text.IO qualified as TIO
import Qty
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
desugarDec (ConstantD _ (ValueR p pat e)) = case patToNameParamsAnn pat of
  Nothing -> todo Empty "desugarDec"
  Just (x, params, Nothing) -> pure (x, FunE p params e)
  Just (x, params, Just t) -> pure (x, FunE p params (AnnE p e t))
desugarDec _ = todo Empty "desugarDec"

patToNameParamsAnn :: Pat -> Maybe (Name, [Param], Maybe Exp)
patToNameParamsAnn (AnnP _ pat t) =
  patToNameParams pat [] (Just t)
patToNameParamsAnn pat = patToNameParams pat [] Nothing

patToNameParams :: Pat -> [Param] -> c -> Maybe (Name, [Param], c)
patToNameParams (CallP _ p param params) acc t =
  patToNameParams p (param : params ++ acc) t
patToNameParams (VarP px x) acc t = Just (mkName px x, acc, t)
patToNameParams _ _ _ = Nothing

data RbCtx = RbCtx
  { next :: HM.HashMap T.Text Word,
    used :: S.Seq OptName
  }

extendRb :: RbCtx -> Name -> (Int, Name, RbCtx)
extendRb RbCtx {next = n, used = u} (Name p x) =
  let i = fromMaybe 0 (HM.lookup x n)
      n' = HM.insert x (i + 1) n
      x' = x <> T.pack (show i)
      name = Name p x'
      d = S.length u
      u' = u :|> Just name
   in (d, name, RbCtx {next = n', used = u'})

withName :: (MonadReader RbCtx m) => Name -> (Int -> Name -> m a) -> m a
withName (Name p x) action = do
  rbCtx <- ask
  let (d, name, rbCtx') = extendRb rbCtx (Name p x)
  local (const rbCtx') (action d name)

nameE :: Name -> Exp
nameE (Name p x) = VarE p (Id x)

callE :: Exp -> [Arg] -> Exp
callE e [] = e
callE (CallE p e args) args' = CallE p e (args ++ args')
callE e args = CallE (hasPosition e) e args

nameP :: Name -> Pat
nameP (Name p x) = VarP p (Id x)

tupleE :: [Exp] -> Exp
tupleE [] = UnitE BNFC'NoPosition
tupleE (e : es) = TupleE (hasPosition e) e es

argA :: ArgKind -> Exp -> Arg
argA Bare e = BareA (hasPosition e) e
argA Explicit e = ExplicitA (hasPosition e) e

readbackVar :: (MonadReader RbCtx m) => Index -> m Exp
readbackVar (Here i) =
  asks (nameE . fromMaybe (mkName Nothing "??") . flip S.index i . used)
readbackVar _ = pure (nameE (mkName Nothing "??"))

readbackExp :: (MonadReader RbCtx m) => Ty -> m Exp
readbackExp (Bot k) =
  AnnE BNFC'NoPosition (VarE BNFC'NoPosition "Core.Bot") <$> readbackExp k
readbackExp (Top k) =
  AnnE BNFC'NoPosition (VarE BNFC'NoPosition "Core.Top") <$> readbackExp k
readbackExp (Type r l) =
  pure $
    callE
      (VarE BNFC'NoPosition (readbackSort r))
      [ ExplicitA BNFC'NoPosition $
          NumberE BNFC'NoPosition (Number (T.pack (show l)))
      ]
readbackExp (Var _ ix k) = do
  AnnE BNFC'NoPosition <$> readbackVar ix <*> readbackExp k
readbackExp (t :-> u) =
  ArrowE BNFC'NoPosition <$> readbackExp t <*> readbackExp u
readbackExp (Con x k ts) = do
  k' <- readbackExp k
  ts' <- traverse readbackArg ts
  pure $
    callE
      (AnnE BNFC'NoPosition (ExplicitE BNFC'NoPosition (Id x)) k')
      (F.toList ts')
readbackExp (Product ts) = tupleE . F.toList <$> traverse readbackExp ts
readbackExp (Sum t u) = do
  t' <- readbackExp t
  u' <- readbackExp u
  pure $
    callE
      (VarE BNFC'NoPosition "Core.Either")
      [ ExplicitA BNFC'NoPosition t',
        ExplicitA BNFC'NoPosition u'
      ]
readbackExp (Box r t) = do
  t' <- readbackExp t
  pure $
    callE
      (VarE BNFC'NoPosition (readbackSort r))
      [ ExplicitA BNFC'NoPosition t'
      ]
readbackExp (Forall Bare x k t) = do
  k' <- readbackExp k
  withName x $ \i x' -> do
    ForallE
      BNFC'NoPosition
      ( MkP
          BNFC'NoPosition
          [ BareP BNFC'NoPosition $
              AnnP BNFC'NoPosition (nameP x') k'
          ]
          (NoTAO BNFC'NoPosition)
      )
      <$> readbackExp (enter i (var i k) t)
readbackExp (Forall Explicit x k t) = do
  k' <- readbackExp k
  withName x $ \i x' -> do
    ForallE
      BNFC'NoPosition
      ( MkP
          BNFC'NoPosition
          [ ExplicitP BNFC'NoPosition $
              AnnP BNFC'NoPosition (nameP x') k'
          ]
          (NoTAO BNFC'NoPosition)
      )
      <$> readbackExp (enter i (var i k) t)
readbackExp (Generalised k t) = do
  k' <- readbackExp k
  withName (mkName Nothing "x") $ \i x' -> do
    ForallE
      BNFC'NoPosition
      ( MkP
          BNFC'NoPosition
          [ InvisibleP BNFC'NoPosition $
              AnnP BNFC'NoPosition (nameP x') k'
          ]
          (NoTAO BNFC'NoPosition)
      )
      <$> readbackExp (enter i (var i k) t)

readbackSort :: Qty -> Id
readbackSort r = Id ("Core.Type" <> printQty r)

readbackBox :: Qty -> Id
readbackBox r = Id ("Core.Box" <> printQty r)

printQty :: Qty -> T.Text
printQty O = "0"
printQty I = "1"
printQty (:?) = "?"
printQty (:+) = "+"
printQty (:*) = ""

readbackArg :: (MonadReader RbCtx m) => (ArgKind, Ty) -> m Arg
readbackArg (Bare, t) = BareA BNFC'NoPosition <$> readbackExp t
readbackArg (Explicit, t) = ExplicitA BNFC'NoPosition <$> readbackExp t

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
    LetR _ decs -> do
      ok <- checkDecsIO ctx decs
      when ok $ do
        let (_, env') = evalDecs decs env
        writeIORef ref env'
    ExpR _ e -> do
      ctx0 <- readIORef ctx
      case runTc ctx0 (infer e >>= runRb . readbackExp) of
        Left err -> printTcErr err
        Right (sig, ctx1) -> do
          writeIORef ctx ctx1
          putStrLn (printTree e ++ " : " ++ printTree sig)
          let (e', env') = evalExp e env
          writeIORef ref env'
          putStrLn (printTree e')
    RequireR _ str ->
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
  putStrLn "|-"
  print t
printTcErr (Anomaly msg) = TIO.putStrLn msg
printTcErr (NotImplemented ctx msg) = do
  mapM_ print ctx
  putStrLn "|-"
  TIO.putStr "Not implemented: "
  TIO.putStrLn msg

checkDecsIO :: IORef Ctx -> [Dec] -> IO Bool
checkDecsIO ctx decs = do
  ctx0 <- readIORef ctx
  case runStateT (checkDecs decs) ctx0 of
    Left err -> False <$ printTcErr err
    Right (sigs, ctx1) -> do
      writeIORef ctx ctx1
      forM_ sigs $ \(Name _ x, t) ->
        putStrLn (T.unpack x ++ " : " ++ printTree t)
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

infer :: (MonadState Ctx m, MonadError TcErr m) => Exp -> m Ty
infer e = do
  ctx <- get
  (t, ctx') <- ctx |- Infer (Sj mempty e) []
  put ctx'
  pure t
