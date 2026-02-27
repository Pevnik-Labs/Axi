{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE OverloadedStrings #-}

-- | Author: Mateusz Pyzik
module Main where

import Control.Monad (forM, forM_, forever, when)
import Control.Monad.Error.Class (MonadError (catchError))
import Control.Monad.RWS.CPS (RWST, runRWST)
import Control.Monad.Reader.Class (MonadReader (..), asks)
import Control.Monad.State.Class (MonadState (..))
import Data.Foldable qualified as F
import Data.Functor ((<&>))
import Data.IORef (IORef, newIORef, readIORef, writeIORef)
import Data.List (intersperse)
import Data.Map.Strict qualified as M
import Data.Maybe (fromMaybe)
import Data.Sequence (Seq (..))
import Data.Sequence qualified as S
import Data.String (IsString (fromString))
import Data.Text qualified as T
import Data.Text.IO qualified as TIO
import Name
import Numeric.Natural (Natural)
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

runTc :: Env -> Ctx -> RWST Env Warnings Ctx m a -> m (a, Ctx, Warnings)
runTc env ctx m = runRWST m env ctx

desugarDecs :: (MonadError TcErr m) => [Dec] -> m [(Id, Exp)]
desugarDecs = traverse desugarDec

desugarDec :: (MonadError TcErr m) => Dec -> m (Id, Exp)
desugarDec (ConstantD (ValueR pat e)) = case patToHeadParamsAnn pat of
  Nothing -> todo Empty "desugarDec"
  Just (x, params, Nothing) -> pure (x, LamE params e)
  Just (x, params, Just t) -> pure (x, LamE params (AnnE e t))
desugarDec _ = todo Empty "desugarDec"

patToHeadParamsAnn :: Pat -> Maybe (Id, [Param], Maybe Exp)
patToHeadParamsAnn (AnnP pat t) =
  patToHeadParams pat [] (Just t)
patToHeadParamsAnn pat = patToHeadParams pat [] Nothing

patToHeadParams :: Pat -> [Param] -> c -> Maybe (Id, [Param], c)
patToHeadParams (CallP p param params) acc t =
  patToHeadParams p (param : params ++ acc) t
patToHeadParams (VarP x) acc t = Just (x, acc, t)
patToHeadParams _ _ _ = Nothing

numberE :: Natural -> Exp
numberE n = NumberE (Number (T.pack (show n)))

callE :: Exp -> [Arg] -> Exp
callE e [] = e
callE (CallE e args) args' = CallE e (args ++ args')
callE e args = CallE e args

appE :: [Exp] -> Maybe Exp
appE [] = Nothing
appE (e : es) = Just (callE e (ArgE Bare <$> es))

infixlE :: Exp -> Exp -> [Exp] -> Exp
infixlE e' e es = fromMaybe e' (appE (intersperse e es))

tupleE :: [Exp] -> Exp
tupleE [] = UnitE
tupleE (e : es) = TupleE e es

readbackVar :: (MonadReader Rb m) => Index -> m Exp
readbackVar (Here i) = asks (VarE . flip S.index i . rbIds)
readbackVar _ = pure (VarE "??")

readbackExp :: (MonadReader Rb m) => Tm -> m Exp
readbackExp (Var _ ix _) = readbackVar ix
readbackExp (Bot k) = AnnE (VarE "Bot") <$> readbackExp k
readbackExp (Top k) = AnnE (VarE "Top") <$> readbackExp k
readbackExp Level = pure (VarE "Level")
readbackExp (Max vs Zero) = do
  vs' <- traverse (readbackExp . (\(ix, (f, t)) -> Var f ix t)) (M.toList vs)
  pure (infixlE (numberE 0) (VarE "⊔") vs')
readbackExp (Max vs u) = do
  vs' <- traverse (readbackExp . (\(ix, (f, t)) -> Var f ix t)) (M.toList vs)
  u' <- readbackExp u
  pure (infixlE undefined (VarE "⊔") (vs' ++ [u']))
readbackExp Nat = pure (VarE "Nat")
readbackExp Zero = pure (numberE 0)
readbackExp (Succ n t) = readbackPlus t (succ n)
readbackExp (Type r (Small l)) = do
  t' <- readbackExp l
  pure $ callE (readbackSort r) [ArgE At t']
readbackExp (Type r (Big l)) =
  pure $
    callE
      (readbackSort r)
      [ArgE At (infixlE undefined (VarE "+") [VarE "ω", numberE l])]
readbackExp (t :-> u) =
  ArrowE <$> readbackExp t <*> readbackExp u
readbackExp (Con (IdName x) k ts) = do
  k' <- readbackExp k
  ts' <- traverse readbackArg ts
  pure $
    callE
      (AnnE (VarE x) k')
      (F.toList ts')
readbackExp (Product ts) =
  infixlE (VarE "Unit") (VarE "×") <$> traverse readbackExp (F.toList ts)
readbackExp (Tuple ts) = tupleE . F.toList <$> traverse readbackExp ts
readbackExp (Sum t u) = do
  t' <- readbackExp t
  u' <- readbackExp u
  pure $
    callE
      (VarE "Either")
      [ ArgE Bare t',
        ArgE Bare u'
      ]
readbackExp (Box r t) =
  readbackExp t <&> \t' ->
    callE (readbackBox r) [bareA t']
readbackExp (Fn h x k t) = do
  k' <- readbackExp k
  withId x $ \i x' -> do
    forallE (MkP [ArgP (decorTy h) (AnnP (VarP x') k')] NoAnn)
      <$> readbackExp (enter (var i k) t)
readbackExp (Lam a x k t) = do
  k' <- readbackExp k
  withId x $ \i x' -> do
    LamE [ArgP (decorTm a) (AnnP (VarP x') k')]
      <$> readbackExp (enter (var i k) t)
readbackExp (App e as) =
  callE <$> readbackExp e <*> traverse readbackArg (F.toList as)

forallE :: Patterns -> Exp -> Exp
forallE (MkP ps NoAnn) (ForallE (MkP ps' NoAnn) e) =
  ForallE (MkP (ps ++ ps') NoAnn) e
forallE ps e = ForallE ps e

readbackPlus :: (MonadReader Rb m) => Tm -> Natural -> m Exp
readbackPlus Zero n = pure (numberE n)
readbackPlus (Succ m t) n = readbackPlus t (succ m + n)
readbackPlus t n =
  readbackExp t <&> \t' -> infixlE undefined (VarE "+") [t', numberE n]

readbackSort :: Qty -> Exp
readbackSort r = VarE (fromString ("Type" <> suffixQty r))

readbackBox :: Qty -> Exp
readbackBox r = VarE (fromString ("Box" <> suffixQty r))

readbackArg :: (MonadReader Rb m) => Ar -> m Arg
readbackArg (MkAr h t) = ArgE (decorTm h) <$> readbackExp t

type Parser a = [Token] -> Either String a

run :: (Print a, Show a) => Parser a -> T.Text -> IO a
run p s = case p ts of
  Left err -> do
    putStrLn "\nParse failed!\n"
    putStrLn "Tokens:"
    mapM_ (putStrLn . showPosToken . mkPosToken) ts
    putStrLn err
    exitFailure
  Right tree -> pure tree
  where
    ts = resolveLayout True (myLexer s)
    showPosToken ((l, c), t) = shows l (':' : shows c (' ' : show t))

main :: IO ()
main = do
  args <- getArgs
  env <- newIORef prelude
  ctx <- newIORef Empty
  loadFile env ctx "Prelude.txt"
  buffer <- newIORef T.empty
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

delimiter :: T.Text
delimiter = ";;"

getNextPart :: IORef T.Text -> IO T.Text
getNextPart bufferRef = readIORef bufferRef >>= go
  where
    go oldBuffer = do
      let (chunk, newBuffer) = T.breakOn delimiter oldBuffer
      if T.null newBuffer
        then do
          line <- TIO.getLine
          go $! T.append oldBuffer (T.snoc line '\n')
        else do
          writeIORef bufferRef $!
            fromMaybe newBuffer (T.stripPrefix delimiter newBuffer)
          return chunk

evalExp :: Exp -> Env -> (Exp, Env)
evalExp = (,)

evalDecs :: [Dec] -> Env -> ([Dec], Env)
evalDecs = (,)

loadFile :: IORef Env -> IORef Ctx -> FilePath -> IO ()
loadFile ref ctx m = do
  putStrLn m
  text <- TIO.readFile m
  decs <- run pListDec text
  putStrLn (printTree decs)
  ok <- checkDecsIO ref ctx decs
  when ok $ do
    env <- readIORef ref
    let (decs', env') = evalDecs decs env
    putStrLn (printTree decs')
    writeIORef ref env'

evalAndPrint :: IORef Env -> IORef Ctx -> Repl -> IO ()
evalAndPrint ref ctx entry = do
  env <- readIORef ref
  case entry of
    LetR decs -> do
      ok <- checkDecsIO ref ctx decs
      when ok $ do
        let (_, env') = evalDecs decs env
        writeIORef ref env'
    ExpR e -> do
      ctx0 <- readIORef ctx
      case runTc env ctx0 (infer e) of
        Left err -> printTcErr err
        Right (sig, ctx1, _) -> do
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
printTcErr err = do
  F.for_ (tcErrNested err) TIO.putStrLn
  F.for_ (tcErrCtx err) $ \ctx -> do
    F.for_ ctx print
    TIO.putStrLn "|-"
  case tcErrTag err of
    TypeError -> TIO.putStrLn "Type error:"
    Anomaly -> TIO.putStrLn "Anomaly:"
    NotImplemented -> TIO.putStrLn "Not implemented:"
  F.for_ (tcErrJudgment err) $ \(MkAnyJudgment j) -> print j
  F.for_ (tcErrMsg err) TIO.putStrLn

checkDecsIO :: IORef Env -> IORef Ctx -> [Dec] -> IO Bool
checkDecsIO env ctx decs = do
  env0 <- readIORef env
  ctx0 <- readIORef ctx
  case runRWST (checkDecs decs) env0 ctx0 of
    Left err -> False <$ printTcErr err
    Right (sigs, ctx1, ()) -> do
      writeIORef ctx ctx1
      forM_ sigs $ \(x, t) ->
        TIO.putStrLn (idText x <> " : " <> T.pack (printTree t))
      pure True

checkDecs ::
  (MonadError TcErr m, MonadReader Env m, MonadState Ctx m) =>
  [Dec] ->
  m [(Id, Exp)]
checkDecs decs = case desugarDecs decs of
  Left err -> rethrowError "Desugaring failed..." err
  Right decs' -> forM decs' $ \(x, e) -> do
    s <- catchError (infer e) $ \err ->
      rethrowError ("Error at " <> printId x <> ":") err
    pure (x, s)

infer ::
  (MonadError TcErr m, MonadReader Env m, MonadState Ctx m) =>
  Exp ->
  m Exp
infer e = do
  ctx <- get
  env <- ask
  ((_, t), ctx') <- ctx |- Elab env e [] Out
  runRb (readbackExp (unIn t)) <$ put ctx'

oneShot :: (MonadFail m) => T.Text -> m ((Ctx, Id), (Tm, Tm))
oneShot text = do
  Right [dec] <- pure (pListDec (resolveLayout True (myLexer text)))
  Right (x, e) <- pure (desugarDec dec)
  Right ((e', t), ctx) <- pure (Empty |- Elab prelude e [] Out)
  pure ((ctx, x), (e', unIn t))
