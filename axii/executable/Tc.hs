{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE ViewPatterns #-}

module Tc where

import Control.Monad (foldM, join)
import Control.Monad.Error.Class (MonadError (..))
import Data.Functor ((<&>))
import Data.Generics qualified as SYB
import Data.HashMap.Strict (HashMap)
import Data.HashMap.Strict qualified as HM
import Data.IntMap.Strict (IntMap)
import Data.IntMap.Strict qualified as IM
import Data.Maybe (fromMaybe)
import Data.Ord (Down (..))
import Data.Sequence (Seq (..), (><))
import Data.Sequence qualified as S
import Data.Text qualified as T
import Numeric.Natural (Natural)
import Qty
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

data Bound = Of Kind | Is Ty
  deriving (Show, SYB.Data)

type OptName = Maybe Name

data Name = Name BNFC'Position T.Text
  deriving (Show, SYB.Data)

mkName :: BNFC'Position -> Id -> Name
mkName p (Id name) = Name p name

data Level = Level Natural | BigLevel Natural
  deriving (Eq, Ord, Show, SYB.Data)

nextLevel :: Level -> Level
nextLevel (Level n) = Level (n + 1)
nextLevel (BigLevel n) = BigLevel (n + 1)

data VarFlavour = Meta | Mono | Poly
  deriving (Eq, Show, SYB.Data)

data Local
  = Local Ctx [Qty] VarFlavour OptName Bound
  deriving (Show, SYB.Data)

data ArgKind = Bare | Explicit
  deriving (Eq, Show, SYB.Data)

type Kind = Ty

data OpenTy = OpenTy Action Int Ty
  deriving (Show, SYB.Data)

enter :: Int -> Ty -> OpenTy -> Ty
enter i t (OpenTy a d u)
  | d <= i = act ((i |-> t) <> a <> Offset d (i - d)) u
  | otherwise = error "enter: open type escaped its scope"

infixr 5 :.

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

data Ty
  = Var VarFlavour Index Kind
  | Bot Kind
  | Top Kind
  | Type Qty Level
  | Ty :-> Ty
  | Sum Ty Ty
  | Product (Seq Ty)
  | Con T.Text Kind (Seq (ArgKind, Ty))
  | Box Qty Ty
  | Forall ArgKind Name Kind OpenTy
  | Generalised Kind OpenTy
  deriving (Show, SYB.Data)

data Action
  = Subst (IntMap Ty)
  | Offset Int Int
  | Compose (Seq Action)
  deriving (Show, SYB.Data)

instance Semigroup Action where
  Compose Empty <> a = a
  Compose (Empty :|> a) <> a' = a <> a'
  a <> Compose Empty = a
  a <> Compose (a' :<| Empty) = a <> a'
  Compose as <> Compose as' = Compose (as <> as')
  Compose as <> a = Compose (as :|> a)
  a <> Compose as = Compose (a :<| as)
  a@(Subst im) <> Subst im' = Subst (IM.union (actTy a <$> im') im)
  a <> a' = Compose (pure a <> pure a')

instance Monoid Action where
  mempty = Compose Empty

(|->) :: Int -> Ty -> Action
i |-> t = Subst (IM.singleton i t)

type Closure = HashMap T.Text Ty

data Subject a = Sj !Closure a
  deriving (Show, SYB.Data)

extend :: Subject a -> T.Text -> Ty -> Subject a
extend (Sj cl a) x t = Sj (HM.insert x t cl) a

data Judgment a where
  Sub :: Ty -> Ty -> Judgment Ctx
  Conv :: (ArgKind, Ty) -> (ArgKind, Ty) -> Judgment Ctx
  Check :: Subject Exp -> [Subject Arg] -> Ty -> Judgment Ctx
  Infer :: Subject Exp -> [Subject Arg] -> Judgment (Ty, Ctx)
  Apply :: Ty -> [Subject Arg] -> Judgment (Ty, Ctx)
  Elab :: Subject Exp -> Judgment (Ty, Ctx)

deriving instance Show (Judgment a)

act :: (SYB.Data a) => Action -> a -> a
act s =
  SYB.gmapT (act s)
    `SYB.extT` actOpenTy s
    `SYB.extT` actTy s
    `SYB.extT` actCtx s
    `SYB.extT` (s <>)

actOpenTy :: Action -> OpenTy -> OpenTy
actOpenTy a (OpenTy a' d t) = OpenTy (act a a') d t

actTy :: Action -> Ty -> Ty
actTy s@(Subst im) (Var f (Here i) k) =
  fromMaybe (Var f (Here i) (act s k)) (IM.lookup i im)
actTy s@(Offset d o) (Var f (Here i) k) =
  Var f (Here (if i < d then i else i + o)) (act s k)
actTy _ k@Type {} = k
actTy s (t :-> u) = act s t :-> act s u
actTy s t = SYB.gmapT (act s) t

actCtx :: Action -> Ctx -> Ctx
actCtx = fmap . act

typeOf :: (MonadError TcErr m) => Ty -> m Kind
typeOf (Bot k) = pure k
typeOf (Top k) = pure k
typeOf (Type _ l) = pure (Type 0 (nextLevel l))
typeOf (Var _ _ k) = pure k
typeOf (t :-> u) =
  (,) <$> typeOf t <*> typeOf u >>= \case
    (Type r1 l1, Type r2 l2) -> pure (Type (piQty r1 r2) (max l1 l2))
    _ -> anomaly "Ill-formed function type"
typeOf (Con _ k ts) = codomain k ts
typeOf (Product ts) = do
  ks <- traverse typeOf ts
  foldM supKind (Type maxBound (Level 0)) ks
typeOf (Sum t u) = join $ supKind <$> typeOf t <*> typeOf u
typeOf (Box r t) =
  typeOf t >>= \case
    Type r' l -> pure (Type (r * r') l)
    _ -> anomaly "Ill-formed box type"
typeOf (Forall _ _ k t) =
  (,) <$> typeOf k <*> sortOf t >>= \case
    (Type r1 l1, Type r2 l2) -> pure (Type (piQty r1 r2) (max l1 l2))
    _ -> anomaly "Ill-formed polymorphic type"
typeOf (Generalised k t) =
  (,) <$> typeOf k <*> sortOf t >>= \case
    (Type r1 l1, Type r2 l2) -> pure (Type (piQty r1 r2) (max l1 l2))
    _ -> anomaly "Ill-formed polymorphic type"

sortOf :: (MonadError TcErr m) => OpenTy -> m Kind
sortOf (OpenTy _ _ t) = typeOf t -- sorts are closed

codomain :: (MonadError TcErr m) => Kind -> Seq (ArgKind, Ty) -> m Kind
codomain (_ :-> k) (_ :<| ts) = codomain k ts
codomain k Empty = pure k
codomain _ _ = anomaly "Ill-formed type constructor application"

supKind :: (MonadError TcErr m) => Kind -> Kind -> m Kind
supKind (Type r1 l1) (Type r2 l2) = pure (Type (supQty r1 r2) (max l1 l2))
supKind _ _ = anomaly "Ill-formed data type"

piQty :: Qty -> Qty -> Qty
piQty 0 r = r
piQty _ _ = 1

infixr 2 |-, `Sub`

infixr 3 :->

(|-) :: (MonadError TcErr m) => Ctx -> Judgment a -> m a
ctx |- Sub (Var _ i _) u | Right (Is t) <- ctx ! i = ctx |- Sub t u
ctx |- Sub t (Var _ i _) | Right (Is u) <- ctx ! i = ctx |- Sub t u
ctx |- Sub (Var _ i1 _) (Var _ i2 _) | i1 == i2 = pure ctx
ctx |- Sub t@(Var f i1 k1) (Var Meta i2 k2) | f /= Poly && i1 < i2 = do
  ctx |- Sub k1 k2 >>= i2 .= t
ctx |- Sub (Var Meta i1 k1) u@(Var f i2 k2) | f /= Poly && i1 > i2 = do
  ctx |- Sub k2 k1 >>= i1 .= u
ctx |- Sub (Bot k1) t = typeOf t >>= \k2 -> ctx |- Sub k1 k2
ctx |- Sub t (Top k2) = typeOf t >>= \k1 -> ctx |- Sub k1 k2
ctx |- Sub (Type r1 l1) (Type r2 l2) | r1 <: r2, l1 <= l2 = pure ctx
ctx |- Sub (a :-> b) (c :-> d) = ctx |- Sub c a >>= (|- Sub b d)
ctx |- Sub (Sum a b) (Sum c d) = ctx |- Sub a c >>= (|- Sub b d)
ctx |- Sub (Sum a b) (Sum c d) = ctx |- Sub a c >>= (|- Sub b d)
ctx |- Sub (Product ts) (Product us) | S.length ts == S.length us = do
  foldM (\ctx' (t, u) -> ctx' |- Sub t u) ctx (S.zip ts us)
ctx |- Sub (Con c1 k1 (as1 :|> a1)) (Con c2 k2 (as2 :|> a2)) = do
  ctx |- Sub (Con c1 k1 as1) (Con c2 k2 as2) >>= (|- Conv a1 a2)
ctx |- Sub (Con c1 _ Empty) (Con c2 _ Empty) | c1 == c2 = pure ctx
ctx |- Conv (a, t) (a', t') | a == a' = ctx |- Sub t t' >>= (|- Sub t' t)
ctx |- Check e [] (Generalised t u) = do
  let i = S.length ctx
  let ctx' = ctx :|> Local Empty [] Mono Nothing (Of t)
  ctx' |- Check e [] (enter i (var i t) u)
ctx |- Check e [] (Box r t) = pushQty ctx |- Check e [] t <&> popQty r
ctx |- Check (Sj cl (FunE _ [] e)) as t =
  ctx |- Check (Sj cl e) as t
ctx |- Check (Sj cl (FunE _ (p : ps) e)) [] (Forall Explicit _ t u)
  | BareP _ (AnnP _ (VarP px x) e') <- p = do
      (t', ctx1) <- ctx |- Elab (Sj cl e')
      ctx2 <- ctx1 |- Sub t t'
      checkVarP ctx2 (Sj cl (px, x, ps, e)) t' u
  | BareP _ (VarP px x) <- p = checkVarP ctx (Sj cl (px, x, ps, e)) t u
ctx |- Check (Sj cl (FunE _ (p : ps) e)) [] (Forall Bare _ t u)
  | ExplicitP _ (AnnP _ (VarP px x) e') <- p = do
      (t', ctx1) <- ctx |- Elab (Sj cl e')
      ctx2 <- ctx1 |- Sub t t'
      checkVarP ctx2 (Sj cl (px, x, ps, e)) t' u
  | ExplicitP _ (VarP px x) <- p = checkVarP ctx (Sj cl (px, x, ps, e)) t u
ctx |- Check (Sj cl (CallE _ e as')) as t = do
  ctx |- Check (Sj cl e) (map (Sj cl) as' ++ as) t
ctx |- Check e as u = do
  (t, ctx') <- ctx |- Infer e as
  ctx' |- Sub t u
ctx |- Infer (Sj cl (VarE _ (Id x))) as | Just e <- cl HM.!? x = do
  t <- typeOf e
  ctx |- Apply t as
ctx |- Infer (Sj cl (FunE _ [] e)) as =
  ctx |- Infer (Sj cl e) as
ctx |- Infer (Sj cl (FunE _ (p : ps) e)) []
  | BareP _ (AnnP _ (VarP px x) e') <- p = do
      let i = S.length ctx
      (t, ctx1) <- ctx |- Elab (Sj cl e')
      (u, ctx2) <- inferVarP ctx1 (Sj cl (px, x, ps, e)) t
      generalise Explicit i u ctx2
  | BareP _ (VarP px x) <- p = do
      let i = S.length ctx
      let hk = Type 0 (BigLevel 0)
      let k = Var Meta (Here i) hk
      let t = Var Meta (Here (i + 1)) k
      let ctx1 = ctx :|> Local Empty [] Meta Nothing (Of hk)
      let ctx2 = ctx1 :|> Local Empty [] Meta Nothing (Of k)
      (u, ctx3) <- inferVarP ctx2 (Sj cl (px, x, ps, e)) t
      generalise Explicit i u ctx3
  | ExplicitP _ (AnnP _ (VarP px x) e') <- p = do
      let i = S.length ctx
      (t, ctx1) <- ctx |- Elab (Sj cl e')
      (u, ctx2) <- inferVarP ctx1 (Sj cl (px, x, ps, e)) t
      generalise Bare i u ctx2
  | ExplicitP _ (VarP px x) <- p = do
      let i = S.length ctx
      let hk = Type 0 (BigLevel 0)
      let k = Var Meta (Here i) hk
      let t = Var Meta (Here (i + 1)) k
      let ctx1 = ctx :|> Local Empty [] Meta Nothing (Of hk)
      let ctx2 = ctx1 :|> Local Empty [] Meta Nothing (Of k)
      (u, ctx3) <- inferVarP ctx2 (Sj cl (px, x, ps, e)) t
      generalise Bare i u ctx3
ctx |- Infer (Sj cl (CallE _ e as')) as = do
  ctx |- Infer (Sj cl e) (map (Sj cl) as' ++ as)
ctx |- Apply t [] = pure (t, ctx)
ctx |- j = typeError ctx j

checkVarP ::
  (MonadError TcErr m) =>
  Seq Local ->
  Subject (BNFC'Position, Id, [Param], Exp) ->
  Ty ->
  OpenTy ->
  m Ctx
checkVarP ctx (Sj cl (px, x, ps, e)) t u | isWildcard x = do
  let i = S.length ctx
      v = var i t
      u' = enter i v u
      ctx1 = ctx :|> Local Empty [] Mono (Just (mkName px x)) (Of t)
  ctx2 <- ctx1 |- Check (Sj cl (FunE Nothing ps e)) [] u'
  clear i ctx2
checkVarP ctx (Sj cl (px, x@(Id txt), ps, e)) t u = do
  let i = S.length ctx
      v = var i t
      u' = enter i v u
      ctx1 = ctx :|> Local Empty [] Mono (Just (mkName px x)) (Of t)
      cl' = HM.insert txt v cl
  ctx2 <- ctx1 |- Check (Sj cl' (FunE Nothing ps e)) [] u'
  clear i ctx2

inferVarP ::
  (MonadError TcErr m) =>
  Seq Local ->
  Subject (BNFC'Position, Id, [Param], Exp) ->
  Ty ->
  m (Ty, Ctx)
inferVarP ctx (Sj cl (px, x, ps, e)) t | isWildcard x = do
  let ctx' = ctx :|> Local Empty [] Mono (Just (mkName px x)) (Of t)
  ctx' |- Infer (Sj cl (FunE Nothing ps e)) []
inferVarP ctx (Sj cl (px, x@(Id txt), ps, e)) t = do
  let i = S.length ctx
      v = var i t
      ctx' = ctx :|> Local Empty [] Mono (Just (mkName px x)) (Of t)
      cl' = HM.insert txt v cl
  ctx' |- Infer (Sj cl' (FunE Nothing ps e)) []

var :: Int -> Ty -> Ty
var i = Var Mono (Here i)

isWildcard :: Id -> Bool
isWildcard (Id x) = T.length x == 0 || T.head x == '_'

infixr 9 !

(!) :: (MonadError TcErr m) => Ctx -> Index -> m Bound
ctx ! (i :. is) = case ctx S.!? i of
  Just (Local ctx' _ _ _ _) -> ctx' ! is
  Nothing -> anomaly "Variable not found"
ctx ! Here i = case ctx S.!? i of
  Just (Local _ _ _ _ b) -> pure b
  Nothing -> anomaly "Variable not found"

infixl 4 .=

(.=) :: (MonadError TcErr m) => Index -> Ty -> Ctx -> m Ctx
(i :. is .= t) ctx = case S.splitAt i ctx of
  (pfx, Local ctx1 qs f x b :<| sfx) -> do
    ctx2 <- (is .= t) ctx1
    pure (pfx >< Local ctx2 qs f x b :<| sfx)
  (_, Empty) -> anomaly "Variable not found"
(Here i .= t) ctx = case S.splitAt i ctx of
  (pfx, Local ctx' qs Meta x (Of _) :<| sfx) ->
    pure (pfx >< Local ctx' qs Meta x (Is t) :<| sfx)
  (_, _ :<| _) -> anomaly "Not a meta variable"
  (_, Empty) -> anomaly "Variable not found"

use :: (MonadError TcErr m) => Index -> Ctx -> m Ctx
use (i :. is) ctx = case S.splitAt i ctx of
  (pfx, Local ctx1 qs f x b :<| sfx) -> do
    ctx2 <- use is ctx1
    pure (pfx >< Local ctx2 qs f x b :<| sfx)
  (_, Empty) -> anomaly "Variable not found"
use (Here i) ctx = case S.splitAt i ctx of
  (pfx, Local ctx' [] f x b :<| sfx) ->
    pure (pfx >< Local ctx' [1] f x b :<| sfx)
  (pfx, Local ctx' (q : qs) f x b :<| sfx) ->
    pure (pfx >< Local ctx' (q + 1 : qs) f x b :<| sfx)
  (_, Empty) -> anomaly "Variable not found"

clear :: (MonadError TcErr m) => Int -> Ctx -> m Ctx
clear i ctx | i >= S.length ctx = anomaly "Variable not found"
clear _ ctx = todo ctx "clear"

generalise ::
  (MonadError TcErr m) => ArgKind -> Int -> Ty -> Ctx -> m (Ty, Ctx)
generalise _ _ _ ctx = todo ctx "generalise"

pushQty :: (SYB.Data a) => a -> a
pushQty = SYB.gmapT pushQty `SYB.extT` (0 :#)

popQty :: (SYB.Data a) => Qty -> a -> a
popQty r =
  SYB.gmapT (popQty r) `SYB.extT` \(q1 :# q2 :# qs) -> r * q1 + q2 :# qs

attrs :: Exp' a -> a
attrs = \case
  EqE p _ _ -> p
  ApplyE p _ -> p
  ProofDecInE p _ _ -> p
  WitnessSuchThatE p _ _ -> p
  AnnE p _ _ -> p
  FunE p _ _ -> p
  ProvingByE p _ _ -> p
  SufficesByE p _ _ -> p
  ExistsE p _ _ -> p
  ForallE p _ _ -> p
  ArrowE p _ _ -> p
  ImplicationE p _ _ -> p
  EquivalenceE p _ _ -> p
  DisjunctionE p _ _ -> p
  ConjunctionE p _ _ -> p
  NegationE p _ -> p
  EqualE p _ _ -> p
  ExplicitE p _ -> p
  CallE p _ _ -> p
  LamCasesE p _ _ -> p
  CaseE p _ _ -> p
  MatchWith p _ _ -> p
  InstantiateWithE p _ -> p
  UnitE p -> p
  TupleE p _ _ -> p
  RecordE p _ -> p
  RecordUpdateE p _ _ -> p
  AssumptionE p -> p
  NumberE p _ -> p
  CharE p _ -> p
  StringE p _ -> p
  HoleE p _ -> p
  VarE p _ -> p

printName :: Name -> T.Text
printName (Name Nothing x) = x
printName (Name (Just (l, c)) x) =
  x <> T.pack (":" ++ show l ++ ":" ++ show c)

printPos :: BNFC'Position -> String
printPos Nothing = "<no position>"
printPos (Just (l, c)) = show l ++ ":" ++ show c
