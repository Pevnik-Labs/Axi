{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE ViewPatterns #-}

module Tc where

import Control.Arrow (second)
import Control.Monad (foldM, join)
import Control.Monad.Error.Class (MonadError (..))
import Data.Function (on)
import Data.Functor ((<&>))
import Data.Generics qualified as SYB
import Data.HashMap.Strict qualified as HM
import Data.IntMap.Strict qualified as IM
import Data.Map.Strict qualified as M
import Data.Maybe (fromMaybe)
import Data.Ord (Down (..))
import Data.Sequence (Seq (..), (><))
import Data.Sequence qualified as S
import Data.String (IsString (..))
import Data.Text qualified as T
import Numeric.Natural (Natural)
import Qty (Qty, supQty, (<:), pattern (:#))
import Syntax.Abs

type Ctx = Seq Local

newtype Warning = UnusedVariable Name
  deriving (Show)

data TcErr where
  Nested :: T.Text -> TcErr -> TcErr
  TypeError :: Ctx -> Judgment a -> TcErr
  Anomaly :: T.Text -> TcErr
  NotImplemented :: Ctx -> T.Text -> TcErr

deriving instance Show TcErr

typeError :: (MonadError TcErr m) => Ctx -> Judgment a -> m a
typeError ctx j = throwError (TypeError ctx j)

anomaly :: (MonadError TcErr m) => T.Text -> m a
anomaly = throwError . Anomaly

todo :: (MonadError TcErr m) => Ctx -> T.Text -> m a
todo ctx = throwError . NotImplemented ctx

data Bound = Of | Is Ctx Tm
  deriving (Show, SYB.Data)

type OptName = Maybe Name

data Name = MkName {namePos :: BNFC'Position, nameText :: T.Text}
  deriving (Show, SYB.Data)

instance Eq Name where
  (==) = (==) `on` nameText

instance IsString Name where
  fromString s = MkName {namePos = Nothing, nameText = T.pack s}

idText :: Id -> T.Text
idText (Id (_, x)) = x

idName :: Id -> Name
idName (Id ((0, 0), x)) = MkName {namePos = Nothing, nameText = x}
idName (Id (px, x)) = MkName {namePos = Just px, nameText = x}

nameId :: Name -> Id
nameId (MkName px x) = Id (fromMaybe (0, 0) px, x)

data Level = Small Tm | Big Natural
  deriving (Show, SYB.Data)

zeroL :: Level
zeroL = Small Zero

succL :: Level -> Level
succL (Small t) = Small (succT t)
succL (Big n) = Big (succ n)

succT :: Tm -> Tm
succT (t :+$ n) = t :+$ succ n
succT t = t :+$ 0

maxL :: (MonadError TcErr m) => Level -> Level -> m Level
maxL (Small t) (Small u) = Small <$> maxT t u
maxL (Small _) (Big n) = pure $ Big n
maxL (Big n) (Small _) = pure $ Big n
maxL (Big m) (Big n) = pure $ Big (max m n)

maxT :: (MonadError TcErr m) => Tm -> Tm -> m Tm
maxT Zero t = pure t
maxT t Zero = pure t
maxT v@(Var f1 ix1 t1) (Var f2 ix2 t2) = pure $ case compare ix1 ix2 of
  LT -> Max (M.fromDistinctAscList [(ix1, (f1, t1)), (ix2, (f2, t2))]) Zero
  EQ -> v
  GT -> Max (M.fromDistinctAscList [(ix2, (f2, t2)), (ix1, (f1, t1))]) Zero
maxT (Var f ix t) u@(_ :+$ _) = pure $ Max (M.singleton ix (f, t)) u
maxT (Var f ix t) (Max vs u) = pure $ Max (M.insert ix (f, t) vs) u
maxT u@(_ :+$ _) (Var f ix t) = pure $ Max (M.singleton ix (f, t)) u
maxT (Max vs u) (Var f ix t) = pure $ Max (M.insert ix (f, t) vs) u
maxT (t :+$ m) (u :+$ n) = case compare m n of
  LT -> maxT t (u :+$ (n - succ m)) <&> (:+$ m)
  EQ -> maxT t u
  GT -> maxT (t :+$ (m - succ n)) u <&> (:+$ n)
maxT t@(_ :+$ _) (Max vs u) = Max vs <$> maxT t u
maxT (Max vs t) u@(_ :+$ _) = Max vs <$> maxT t u
maxT (Max vs t) (Max ws u) = Max (vs <> ws) <$> maxT t u
maxT _ _ = anomaly "Ill-formed level"

omegaL :: Level
omegaL = Big 0

data VarFlavour
  = -- | Existential (flexible) variable, treated as monotype
    Meta
  | -- | Universal (rigid) variable, treated as monotype
    Plain
  | -- | Universal (rigid) variable, treated as polytype
    Stable
  deriving (Eq, Show, SYB.Data)

isMono :: VarFlavour -> Bool
isMono Meta = True
isMono Plain = True
isMono Stable = False

data Local = Local [Qty] VarFlavour OptName Bound Tm
  deriving (Show, SYB.Data)

mkLocal :: VarFlavour -> OptName -> Bound -> Tm -> Local
mkLocal = Local [0]

mkPlain :: OptName -> Bound -> Tm -> Local
mkPlain = mkLocal Plain

mkMeta :: Tm -> Local
mkMeta = mkLocal Meta Nothing Of

data ArgFlavour = Bare | At | Hash
  deriving (Eq, Show, SYB.Data)

data OpenTm = OpenTm Action Int Tm
  deriving (Show, SYB.Data)

enter :: Tm -> OpenTm -> Tm
enter t (OpenTm (Subst a) d u) = act (Subst (IM.insert d t a)) u

force :: OpenTm -> (Int, Tm)
force (OpenTm a d u) = (d, act a u)

strengthen :: OpenTm -> Maybe Tm
strengthen t | let (d, u) = force t, fresh d u = Just u
strengthen _ = Nothing

infixr 5 :.

infixl 5 .:

data Index = Index Int Path
  deriving (Eq, Ord, Show, SYB.Data)

newtype Path = Path (Seq Int)
  deriving (Show, SYB.Data)
  deriving (Eq, Ord) via (Down (Seq (Down Int)))

viewIndex :: Index -> Either (Int, Index) Int
viewIndex (Index i (Path (i' :<| is))) = Left (i, Index i' (Path is))
viewIndex (Index i (Path Empty)) = Right i

pattern (:.) :: Int -> Index -> Index
pattern (:.) i is <- (viewIndex -> Left (i, is))
  where
    (:.) i (Index i' (Path is)) = Index i (Path (i' :<| is))

pattern Here :: Int -> Index
pattern Here i <- (viewIndex -> Right i)
  where
    Here i = Index i (Path Empty)

{-# COMPLETE (:.), Here #-}

(.:) :: Index -> Int -> Index
Index i (Path is) .: j = Index i (Path (is :|> j))

data Tm
  = Var VarFlavour Index Tm
  | Bot Tm
  | Top Tm
  | Type Qty Level
  | Level
  | Max (M.Map Index (VarFlavour, Tm)) Tm
  | Nat
  | Zero
  | Tm :+$ Natural
  | Sum Tm Tm
  | Product (Seq Tm)
  | Tuple (Seq Tm)
  | Con Name Tm (Seq (ArgFlavour, Tm))
  | Box Qty Tm
  | Forall ArgFlavour OptName Tm OpenTm
  | Fun ArgFlavour OptName Tm OpenTm
  deriving (Show, SYB.Data)

viewArrow :: Tm -> Maybe (Tm, Tm)
viewArrow (Forall At _ t u) | Just u' <- strengthen u = Just (t, u')
viewArrow _ = Nothing

pattern (:->) :: Tm -> Tm -> Tm
pattern t :-> u <- (viewArrow -> Just (t, u))

newtype Action = Subst (IM.IntMap Tm)
  deriving (Show, SYB.Data)

instance Semigroup Action where
  a@(Subst im) <> Subst im' = Subst (IM.union (actTm a <$> im') im)

instance Monoid Action where
  mempty = Subst mempty

(|->) :: Int -> Tm -> Action
i |-> t = Subst (IM.singleton i t)

trim :: Int -> Action -> Action
trim d (Subst im) = Subst (fst (IM.split d im))

type Closure = HM.HashMap T.Text Tm

data Subject a = Sj Closure a
  deriving (Show, SYB.Data)

extend :: Subject a -> T.Text -> Tm -> Subject a
extend (Sj cl a) x t = Sj (HM.insert x t cl) a

data Mode a where
  Check :: Tm -> Mode Ctx
  Infer :: Mode (Tm, Ctx)

deriving instance Show (Mode a)

inferType :: Mode Ctx
inferType = Check (Type maxBound omegaL)

data Judgment a where
  Sub :: Tm -> Tm -> Judgment Ctx
  Conv :: (ArgFlavour, Tm) -> (ArgFlavour, Tm) -> Judgment Ctx
  Elab :: Closure -> Exp -> [Subject Arg] -> Mode a -> Judgment (Tm, a)
  Apply :: Tm -> Tm -> [Subject Arg] -> Mode a -> Judgment (Tm, a)
  Generalise :: ArgFlavour -> Int -> Tm -> Tm -> Judgment (Tm, (Tm, Ctx))

deriving instance Show (Judgment a)

act :: (SYB.Data a) => Action -> a -> a
act s =
  SYB.gmapT (act s)
    `SYB.extT` actOpenTm s
    `SYB.extT` actTm s
    `SYB.extT` actCtx s
    `SYB.extT` (s <>)

actOpenTm :: Action -> OpenTm -> OpenTm
actOpenTm a (OpenTm a' d t) = OpenTm (act (trim d a) a') d t

actTm :: Action -> Tm -> Tm
actTm s@(Subst im) (Var f (Here i) k) =
  fromMaybe (Var f (Here i) (act s k)) (IM.lookup i im)
actTm s t = SYB.gmapT (act s) t

actCtx :: Action -> Ctx -> Ctx
actCtx = fmap . act

typeOf :: (MonadError TcErr m) => Tm -> m Tm
typeOf (Var _ _ k) = pure k
typeOf (Bot k) = pure k
typeOf (Top k) = pure k
typeOf (Type _ l) = pure (Type maxBound (succL l))
typeOf Level = pure (Type maxBound omegaL)
typeOf (Max _ _) = pure Level
typeOf Nat = pure leastSort
typeOf Zero = pure Nat
typeOf (t :+$ _) = typeOf t
typeOf (Con _ k ts) = codomain k ts
typeOf (Sum t u) = join $ liftA2 supT (typeOf t) (typeOf u)
typeOf (Product ts) = foldM supT leastSort =<< traverse typeOf ts
typeOf (Tuple ts) = Tuple <$> traverse typeOf ts
typeOf (Box r t) =
  typeOf t >>= \case
    Type r' l -> pure (Type (r * r') l)
    _ -> anomaly "Ill-formed box type"
typeOf (Forall _ _ t u) =
  liftA2 (,) (typeOf t) (sortOf u) >>= \case
    (Type r1 l1, Type r2 l2) -> Type (piQty r1 r2) <$> maxL l1 l2
    _ -> anomaly "Ill-formed function type"
typeOf (Fun h x t (OpenTm s d e)) = Forall h x t . OpenTm s d <$> typeOf e

leastSort :: Tm
leastSort = Type minBound zeroL

leastBigSort :: Tm
leastBigSort = Type minBound omegaL

fresh :: (SYB.Data a) => Int -> a -> Bool
fresh i =
  SYB.gmapQr (&&) True (fresh i)
    `SYB.extQ` (i /=)
    `SYB.extQ` freshOpenTm i

freshOpenTm :: Int -> OpenTm -> Bool
freshOpenTm i t = let (d, u) = force t in d <= i || fresh i u

sortOf :: (MonadError TcErr m) => OpenTm -> m Tm
sortOf (OpenTm _ d e) = do
  t <- typeOf e
  if fresh d t
    then
      pure t -- sort is not dependent, go ahead
    else
      supT leastBigSort t -- mix in big sort to kill dependency

codomain :: (MonadError TcErr m) => Tm -> Seq (ArgFlavour, Tm) -> m Tm
codomain (_ :-> k) (_ :<| ts) = codomain k ts
codomain k Empty = pure k
codomain _ _ = anomaly "Ill-formed type constructor application"

supT :: (MonadError TcErr m) => Tm -> Tm -> m Tm
supT (Type r1 l1) (Type r2 l2) = Type (supQty r1 r2) <$> maxL l1 l2
supT _ _ = anomaly "Ill-formed type"

piSort :: (MonadError TcErr m) => Tm -> Tm -> m Tm
piSort (Type r1 l1) (Type r2 l2) = Type (piQty r1 r2) <$> maxL l1 l2
piSort _ _ = anomaly "Ill-formed type"

piQty :: Qty -> Qty -> Qty
piQty 0 r = r
piQty _ _ = 1

infixr 2 |-

infixr 3 :->

(|-) :: (MonadError TcErr m) => Ctx -> Judgment a -> m a
ctx |- Sub (Var _ i _) u | Right (Is _ t) <- ctx ! i = ctx |- Sub t u
ctx |- Sub t (Var _ i _) | Right (Is _ u) <- ctx ! i = ctx |- Sub t u
ctx |- Sub (Var _ i1 _) (Var _ i2 _) | i1 == i2 = pure ctx
ctx |- Sub e@(Var f j t) (Var Meta i u) | isMono f && j < i = do
  ctx |- Sub t u >>= i .= Is [] e
ctx |- Sub (Var Meta i u) e@(Var f j t) | isMono f && j < i = do
  ctx |- Sub t u >>= i .= Is [] e
ctx |- Sub (Bot t) e = typeOf e >>= \u -> ctx |- Sub t u
ctx |- Sub e (Top u) = typeOf e >>= \t -> ctx |- Sub t u
ctx |- Sub (Var Meta i u) e@(Type _ (Small _)) = do
  t <- typeOf e
  ctx |- Sub t u >>= i .= Is [] e
ctx |- Sub t@(Var Meta _ _) (Type r (Big _)) = do
  let i = length ctx
  let u = Type r (Small (Var Meta (Here i) Level))
  ctx :|> mkMeta Level |- Sub t u >>= clear i
ctx |- Sub t@(Var Meta _ _) Level = ctx |- Sub t Nat
ctx |- Sub (Var Meta i u) e@Nat = do
  t <- typeOf e
  ctx |- Sub t u >>= i .= Is [] e
ctx |- Sub (Var Meta i u) Zero = do
  ctx |- Sub Nat u >>= i .= Is [] Zero
ctx |- Sub (Var Meta i u) (e :+$ n) = do
  t <- typeOf e
  let v = Var Meta (i .: 0) t
  let e' = v :+$ n
  ctx |- Sub t u >>= i .= Is [mkMeta t] e' >>= (|- Sub v e)
ctx |- Sub e@(Type _ (Small _)) (Var Meta i u) = do
  t <- typeOf e
  ctx |- Sub t u >>= i .= Is [] e
ctx |- Sub (Type r (Small t)) (Type s (Small u)) | r <: s = ctx |- Sub t u
ctx |- Sub (Type r (Small _)) (Type s (Big _)) | r <: s = pure ctx
ctx |- Sub (Type r (Big m)) (Type s (Big n)) | r <: s, m <= n = pure ctx
ctx |- Sub Level Level = pure ctx
ctx |- Sub Nat Level = pure ctx
ctx |- Sub (Max vs t) u = do
  ctx1 <- ctx |- Sub t u
  foldM (\ctx2 (i, (f, s)) -> ctx2 |- Sub (Var f i s) u) ctx1 (M.toList vs)
ctx |- Sub u@(:+$) {} e@Max {} = do
  ctx' <- typeOf e >>= \t -> ctx |- Sub t Level
  t <- maxT e u
  ctx' |- Sub t u
ctx |- Sub Nat Nat = pure ctx
ctx |- Sub Zero t = typeOf t >>= \k -> ctx |- Sub k Level
ctx |- Sub (t :+$ m) (u :+$ n) = case compare m n of
  LT -> ctx |- Sub t (u :+$ (n - succ m))
  EQ -> ctx |- Sub t u
  GT -> ctx |- Sub (t :+$ (m - succ n)) u
ctx |- Sub (Sum a b) (Sum c d) = ctx |- Sub a c >>= (|- Sub b d)
ctx |- Sub (Product ts) (Product us) | length ts == length us = do
  foldM (|-) ctx (S.zipWith Sub ts us)
ctx |- Sub (Con c1 _ as1) (Con c2 _ as2) | c1 == c2 = do
  foldM (|-) ctx (S.zipWith Conv as1 as2)
ctx |- Sub (Con c1 _ Empty) (Con c2 _ Empty) | c1 == c2 = pure ctx
ctx |- Sub (Forall At _ a b) (Forall At x c d) = do
  ctx1 <- ctx |- Sub c a
  let i = length ctx1
  let v = var i c
  ctx1 :|> mkPlain x Of c |- Sub (enter v b) (enter v d) >>= clear i
ctx |- Conv (a, t) (a', t') | a == a' = ctx |- Sub t t' >>= (|- Sub t' t)
ctx |- Elab cl (VarE x) as u
  | Just e@(Var _ ix t) <- cl HM.!? idText x = do
      ctx' <- use ix ctx
      ctx' |- Apply e t as u
ctx |- Elab cl (AnnE e a) as u = do
  (t, ctx1) <- ctx |- Elab cl a [] inferType
  (e', ctx2) <- ctx1 |- Elab cl e [] (Check t)
  ctx2 |- Apply e' t as u
ctx |- Elab cl (ForallE (MkP ps (HasAnn a)) e) as t = do
  let ps' = SYB.gmapT (SYB.mkT (`AnnP` a)) <$> ps
  ctx |- Elab cl (ForallE (MkP ps' NoAnn) e) as t
ctx |- Elab cl (ForallE (MkP [] NoAnn) e) as t = ctx |- Elab cl e as t
ctx |- Elab cl (FunE [] e) as t = ctx |- Elab cl e as t
ctx |- Elab cl (FunE (p : ps) e) [] (Check (Forall At _ t u))
  | BareP (AnnP (VarP x) e') <- p = do
      (t', ctx1) <- ctx |- Elab cl e' [] inferType
      ctx2 <- ctx1 |- Sub t t'
      checkVarP ctx2 (Sj cl (x, ps, e)) t' u
  | BareP (VarP x) <- p = checkVarP ctx (Sj cl (x, ps, e)) t u
ctx |- Elab cl (FunE (p : ps) e) [] (Check (Forall Bare _ t u))
  | AtP (AnnP (VarP x) e') <- p = do
      (t', ctx1) <- ctx |- Elab cl e' [] inferType
      ctx2 <- ctx1 |- Sub t t'
      checkVarP ctx2 (Sj cl (x, ps, e)) t' u
  | AtP (VarP x) <- p = checkVarP ctx (Sj cl (x, ps, e)) t u
ctx |- Elab cl (FunE (p : ps) e) [] Infer
  | BareP (AnnP (VarP x) a) <- p = do
      let i = length ctx
      (t, ctx1) <- ctx |- Elab cl a [] inferType
      (e', (u, ctx2)) <- inferVarP ctx1 (Sj cl (x, ps, e)) t
      ctx2 |- Generalise At i e' u
  | BareP (VarP x) <- p = do
      let i = length ctx
      let hk = Type maxBound (Small (Var Meta (Here i) Level :+$ 0))
      let k = Var Meta (Here (i + 1)) hk
      let t = Var Meta (Here (i + 2)) k
      let ctx1 = ctx :|> mkMeta Level :|> mkMeta hk :|> mkMeta k
      (e', (u, ctx2)) <- inferVarP ctx1 (Sj cl (x, ps, e)) t
      ctx2 |- Generalise At i e' u
  | AtP (AnnP (VarP x) a) <- p = do
      let i = length ctx
      (t, ctx1) <- ctx |- Elab cl a [] inferType
      (e', (u, ctx2)) <- inferVarP ctx1 (Sj cl (x, ps, e)) t
      ctx2 |- Generalise Bare i e' u
  | AtP (VarP x) <- p = do
      let i = length ctx
      let hk = Type maxBound (Small (Var Meta (Here i) Level :+$ 0))
      let k = Var Meta (Here (i + 1)) hk
      let t = Var Meta (Here (i + 2)) k
      let ctx1 = ctx :|> mkMeta Level :|> mkMeta hk :|> mkMeta k
      (e', (u, ctx2)) <- inferVarP ctx1 (Sj cl (x, ps, e)) t
      ctx2 |- Generalise Bare i e' u
ctx |- Elab cl (CallE e as') as t = do
  ctx |- Elab cl e (map (Sj cl) as' ++ as) t
ctx |- Elab cl e [] (Check (Box r t)) =
  pushQty ctx |- Elab cl e [] (Check t) <&> popQty r
ctx |- Elab cl e [] (Check (Forall Bare x t u)) = do
  let i = length ctx
  let ctx' = ctx :|> mkPlain x Of t
  ctx' |- Elab cl e [] (Check (enter (var i t) u))
ctx |- Elab cl e [] (Check (Forall Hash x t u)) = do
  let i = length ctx
  let ctx' = ctx :|> mkPlain x Of t
  ctx' |- Elab cl e [] (Check (enter (var i t) u))
ctx |- Apply e t [] (Check u) = ctx |- Sub t u <&> (e,)
ctx |- Apply e t [] Infer = pure (e, (t, ctx))
ctx |- Generalise _ i e u | i == length ctx = pure (e, (u, ctx))
ctx :|> Local [r] Plain x Of t |- Generalise h i e u | i <= length ctx = do
  ctx' <- ctx |- Sub t (Top (Type r omegaL))
  let e' = Fun h x t (OpenTm mempty (length ctx') e)
  let u' = Forall h x t (OpenTm mempty (length ctx') u)
  ctx' |- Generalise h i e' u'
ctx :|> Local [r] Meta x Of t |- Generalise h i e u | i <= length ctx = do
  ctx' <- ctx |- Sub t (Top (Type r omegaL))
  let u' = Forall Hash x t (OpenTm mempty (length ctx') u)
  ctx' |- Generalise h i e u'
pfx :|> Local [r] Meta x (Is sfx t) k |- Generalise h i e u
  | i <= length pfx = do
      let j = length pfx
      (action, sfx') <- flatten j sfx
      let ctx = pfx <> sfx' :|> Local [r] Meta x Of k
      let u' = act (action <> (j |-> t)) u
      ctx |- Generalise h i e u'
ctx |- j = typeError ctx j

checkVarP ::
  (MonadError TcErr m) =>
  Ctx ->
  Subject (Id, [Param], Exp) ->
  Tm ->
  OpenTm ->
  m (Tm, Ctx)
checkVarP ctx (Sj cl (x, ps, e)) t u | isWildcard x = do
  let i = length ctx
      v = var i t
      u' = enter v u
      ctx1 = ctx :|> mkPlain (Just (idName x)) Of t
  (e', ctx2) <- ctx1 |- Elab cl (FunE ps e) [] (Check u')
  abstract i e' ctx2
checkVarP ctx (Sj cl (x, ps, e)) t u = do
  let i = length ctx
      v = var i t
      u' = enter v u
      ctx1 = ctx :|> mkPlain (Just (idName x)) Of t
      cl' = HM.insert (idText x) v cl
  (e', ctx2) <- ctx1 |- Elab cl' (FunE ps e) [] (Check u')
  abstract i e' ctx2

inferVarP ::
  (MonadError TcErr m) =>
  Ctx ->
  Subject (Id, [Param], Exp) ->
  Tm ->
  m (Tm, (Tm, Ctx))
inferVarP ctx (Sj cl (x, ps, e)) t | isWildcard x = do
  let ctx' = ctx :|> mkPlain (Just (idName x)) Of t
  ctx' |- Elab cl (FunE ps e) [] Infer
inferVarP ctx (Sj cl (x, ps, e)) t = do
  let i = length ctx
      v = var i t
      ctx' = ctx :|> mkPlain (Just (idName x)) Of t
      cl' = HM.insert (idText x) v cl
  ctx' |- Elab cl' (FunE ps e) [] Infer

var :: Int -> Tm -> Tm
var i = Var Plain (Here i)

isWildcard :: Id -> Bool
isWildcard (idText -> x) = T.length x == 0 || T.head x == '_'

infixr 9 !

(!) :: (MonadError TcErr m) => Ctx -> Index -> m Bound
ctx ! (i :. is) = case ctx S.!? i of
  Just (Local _ _ _ (Is ctx' _) _) -> ctx' ! is
  _ -> anomaly "Variable not found"
ctx ! Here i = case ctx S.!? i of
  Just (Local _ _ _ b _) -> pure b
  Nothing -> anomaly "Variable not found"

infixl 4 .=

(.=) :: (MonadError TcErr m) => Index -> Bound -> Ctx -> m Ctx
(i :. is .= b) ctx = case S.splitAt i ctx of
  (pfx, Local qs f x (Is ctx1 e) t :<| sfx) -> do
    ctx2 <- (is .= b) ctx1
    pure (pfx >< Local qs f x (Is ctx2 e) t :<| sfx)
  _ -> anomaly "Variable not found"
(Here i .= b) ctx = case S.splitAt i ctx of
  (pfx, Local qs Meta x Of t :<| sfx) ->
    pure (pfx >< Local qs Meta x b t :<| sfx)
  (_, _ :<| _) -> anomaly "Not a meta variable"
  (_, Empty) -> anomaly "Variable not found"

use :: (MonadError TcErr m) => Index -> Ctx -> m Ctx
use (i :. is) ctx = case S.splitAt i ctx of
  (pfx, Local qs f x (Is ctx1 e) t :<| sfx) -> do
    ctx2 <- use is ctx1
    pure (pfx >< Local qs f x (Is ctx2 e) t :<| sfx)
  (_, _) -> anomaly "Variable not found"
use (Here i) ctx = case S.splitAt i ctx of
  (pfx, Local (q :# qs) f x b t :<| sfx) ->
    pure (pfx >< Local (q + 1 : qs) f x b t :<| sfx)
  (_, _) -> anomaly "Variable not found"

clear :: (MonadError TcErr m) => Int -> Ctx -> m Ctx
clear i ctx = ctx |- Generalise Hash i Zero Nat <&> snd . snd

abstract :: (MonadError TcErr m) => Int -> Tm -> Ctx -> m (Tm, Ctx)
abstract i e ctx = ctx |- Generalise Hash i e undefined <&> second snd

flatten :: (MonadError TcErr m) => Int -> Ctx -> m (Action, Ctx)
flatten _ Empty = pure (mempty, Empty)
flatten _ ctx = todo ctx "flatten"

pushQty :: (SYB.Data a) => a -> a
pushQty = SYB.gmapT pushQty `SYB.extT` (0 :#)

popQty :: (SYB.Data a) => Qty -> a -> a
popQty r =
  SYB.gmapT (popQty r) `SYB.extT` \(q1 :# q2 :# qs) -> r * q1 + q2 :# qs
