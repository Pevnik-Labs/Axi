{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveTraversable #-}
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

import Control.Arrow (first, second)
import Control.Monad (foldM, join)
import Control.Monad.Error.Class (MonadError (..))
import Data.Foldable qualified as F
import Data.Function ((&))
import Data.Functor ((<&>))
import Data.Generics qualified as SYB
import Data.HashMap.Strict qualified as HM
import Data.IntMap.Strict qualified as IM
import Data.Map.Strict qualified as M
import Data.Maybe (fromMaybe)
import Data.Ord (Down (..))
import Data.Sequence (Seq (..), (><))
import Data.Sequence qualified as S
import Data.Text qualified as T
import Data.Type.Bool (Not)
import Name (Name, OptName, idName, idText, isWildcard)
import Numeric.Natural (Natural)
import Qty (Qty (..), infQty, supQty, (<:), pattern (:#))
import Syntax.Abs

type Ctx = Seq Local

newtype Warning = UnusedVariable Name
  deriving (Show)

data TcErr = MkTcErr
  { tcErrNested :: Seq T.Text,
    tcErrTag :: TcErrTag,
    tcErrCtx :: Maybe Ctx,
    tcErrMsg :: Maybe T.Text,
    tcErrJudgment :: Maybe AnyJudgment
  }

data TcErrTag = TypeError | Anomaly | NotImplemented

data AnyJudgment = forall a. MkAnyJudgment (Judgment a)

mkTcErr :: TcErr
mkTcErr =
  MkTcErr
    { tcErrNested = Empty,
      tcErrTag = Anomaly,
      tcErrCtx = Nothing,
      tcErrMsg = Nothing,
      tcErrJudgment = Nothing
    }

rethrowError :: (MonadError TcErr m) => T.Text -> TcErr -> m a
rethrowError msg err = throwError err {tcErrNested = msg :<| tcErrNested err}

typeError :: (MonadError TcErr m) => Ctx -> Judgment a -> m b
typeError ctx j =
  throwError
    mkTcErr
      { tcErrTag = TypeError,
        tcErrCtx = Just ctx,
        tcErrJudgment = Just (MkAnyJudgment j)
      }

anomaly :: (MonadError TcErr m) => T.Text -> m a
anomaly msg = throwError mkTcErr {tcErrMsg = Just msg}

anomalyWith :: (MonadError TcErr m) => Ctx -> T.Text -> m a
anomalyWith ctx msg =
  throwError mkTcErr {tcErrCtx = Just ctx, tcErrMsg = Just msg}

todo :: (MonadError TcErr m) => Ctx -> T.Text -> m a
todo ctx msg =
  throwError
    mkTcErr
      { tcErrTag = NotImplemented,
        tcErrCtx = Just ctx,
        tcErrMsg = Just msg
      }

test :: (MonadError TcErr m) => Bool -> Ctx -> Judgment a -> b -> m b
test b ctx j result = if b then pure result else typeError ctx j

data Bound = Of | Is Ctx Tm
  deriving (Show, SYB.Data)

data Level = Small Tm | Big Natural
  deriving (Show, SYB.Data)

zeroL :: Level
zeroL = Small Zero

succL :: Level -> Level
succL (Small t) = Small (succT t)
succL (Big n) = Big (succ n)

succT :: Tm -> Tm
succT (Succ n t) = Succ (succ n) t
succT t = Succ 0 t

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
maxT (Var f ix t) u@(Succ _ _) = pure $ Max (M.singleton ix (f, t)) u
maxT (Var f ix t) (Max vs u) = pure $ Max (M.insert ix (f, t) vs) u
maxT u@(Succ _ _) (Var f ix t) = pure $ Max (M.singleton ix (f, t)) u
maxT (Max vs u) (Var f ix t) = pure $ Max (M.insert ix (f, t) vs) u
maxT (Succ m t) (Succ n u) = case compare m n of
  LT -> maxT t (Succ (n - succ m) u) <&> Succ m
  EQ -> maxT t u
  GT -> maxT (Succ (m - succ n) t) u <&> Succ n
maxT t@(Succ _ _) (Max vs u) = Max vs <$> maxT t u
maxT (Max vs t) u@(Succ _ _) = Max vs <$> maxT t u
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

data Decor = Bare | At | Hash
  deriving (Eq, Show, SYB.Data)

flipDecor :: Decor -> Decor
flipDecor At = Bare
flipDecor _ = At

data OpenTm = OpenTm Action Int Tm
  deriving (Show, SYB.Data)

enter :: Tm -> OpenTm -> Tm
enter t (OpenTm (Subst a) d u) = act (Subst (IM.insert d t a)) u

force :: OpenTm -> (Int, Tm)
force (OpenTm a d u) = (d, act a u)

strengthen :: OpenTm -> Maybe Tm
strengthen (force -> (d, e)) | fresh d e = Just e
strengthen _ = Nothing

isDependent :: OpenTm -> Bool
isDependent (force -> (d, e)) = fresh d e

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

type Spine = Seq Ar

data Ar = MkAr Decor Tm
  deriving (Show, SYB.Data)

data Tm
  = Var VarFlavour Index Tm
  | Bot Tm
  | Top Tm
  | Type Qty Level
  | Level
  | Max (M.Map Index (VarFlavour, Tm)) Tm
  | Nat
  | Zero
  | Succ Natural Tm
  | Sum Tm Tm
  | Product (Seq Tm)
  | Tuple (Seq Tm)
  | Con Name Tm Spine
  | Box Qty Tm
  | Forall Decor OptName Tm OpenTm
  | Fun Decor OptName Tm OpenTm
  deriving (Show, SYB.Data)

viewArrow :: Tm -> Maybe (Tm, Tm)
viewArrow (Forall At _ t (strengthen -> Just u)) = Just (t, u)
viewArrow _ = Nothing

pattern (:->) :: Tm -> Tm -> Tm
pattern t :-> u <- (viewArrow -> Just (t, u))

boxT :: (MonadError TcErr m) => Qty -> Tm -> m Tm
boxT 1 e = pure e
boxT r (Type s l) = pure (Type (r * s) l)
boxT r (Box s e) = boxT (r * s) e
boxT r e = do
  t <- typeOf e
  case t of
    Type 0 _ -> pure e
    Type s _ -> pure (Box (r / s) e)
    _ -> pure (Box r e)

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

type Scope = HM.HashMap T.Text Tm

data Subject a = Sj Scope a
  deriving (Show, SYB.Data)

extendScope :: Id -> Tm -> Scope -> Scope
extendScope x _ sc | isWildcard x = sc
extendScope x e sc = HM.insert (idText x) e sc

data Mode b a where
  Out :: Mode 'False a
  In :: a -> Mode 'True a

getInput :: Mode 'True a -> a
getInput (In x) = x

deriving instance Functor (Mode b)

deriving instance Foldable (Mode b)

deriving instance Traversable (Mode b)

deriving instance (Show a) => Show (Mode b a)

type Pass b = (Tm, (Mode b Tm, Ctx))

type Result b = Pass (Not b)

inferType :: Mode 'True Tm
inferType = In (Type maxBound omegaL)

data Judgment a where
  Sub :: Tm -> Qty -> Tm -> Judgment (Qty, Ctx)
  Super :: Qty -> Tm -> Tm -> Judgment (Qty, Ctx)
  Usage :: Qty -> Tm -> Judgment (Qty, Ctx)
  Conv :: Ar -> Ar -> Judgment Ctx
  Elab :: Scope -> Exp -> [Subject Arg] -> Mode b Tm -> Judgment (Result b)
  Apply :: Tm -> Tm -> [Subject Arg] -> Mode b Tm -> Judgment (Result b)
  Generalise :: Decor -> Int -> Tm -> Mode b Tm -> Judgment (Pass b)

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
typeOf (Succ _ t) = typeOf t
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
sortOf (force -> (d, t)) = do
  k <- typeOf t
  if fresh d k
    then
      pure k -- sort is non-dependent, go ahead
    else
      supT leastBigSort k -- mix in big sort to kill dependency

codomain :: (MonadError TcErr m) => Tm -> Spine -> m Tm
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
ctx |- Sub (Var _ i _) r u | Right (Is _ t) <- ctx ! i = ctx |- Sub t r u
ctx |- Sub t r (Var _ i _) | Right (Is _ u) <- ctx ! i = ctx |- Sub t r u
ctx |- Sub (Var _ j _) r (Var Meta i t) | j == i = do
  (s, ctx') <- ctx |- Sub t r t
  if 1 <: s
    then pure (s, ctx')
    else (i .= Is [mkMeta t] (Box s (Var Meta (i .: 0) t))) (signum s, ctx')
ctx |- Sub (Var _ j _) r (Var _ i t) | j == i = ctx |- Sub t r t
ctx |- Sub e@(Var f j t) r (Var Meta i u) | isMono f && j < i = do
  ctx |- Sub t r u >>= i .= Is [] e
ctx |- Sub (Var Meta i u) r e@(Var f j t) | isMono f && j < i = do
  (s, ctx') <- ctx |- Sub (Box r t) 1 u
  (i .= Is [] (Box s e)) (signum s, ctx')
ctx |- Sub (Bot t) r e = typeOf e >>= \u -> ctx |- Sub t r u
ctx |- Sub e r (Top u) = typeOf e >>= \t -> ctx |- Sub t r u
ctx |- Sub t r (Type s l) | not (1 <: s) = do
  ctx |- Sub t (r * s) (Type (signum s) l)
ctx |- Sub t r (Box s u) = ctx |- Sub t (r * s) u
ctx |- Sub (Box s t) r u = ctx |- Sub t (r / s) u
ctx |- Sub (Var Meta i u) r (Type s (Small l)) = do
  let e = Type (r * s) (Small l)
  t <- typeOf e
  ctx |- Sub t 1 u >>= i .= Is [] e
ctx |- Sub t@(Var Meta _ _) r (Type s (Big _)) = do
  let i = length ctx
  let u = Type s (Small (Var Meta (Here i) Level))
  ctx :|> mkMeta Level |- Sub t r u >>= clear i
ctx |- Sub t@(Var Meta _ _) r Level = ctx |- Sub t r Nat
ctx |- Sub (Var Meta i u) r e@Nat = do
  t <- typeOf e
  ctx |- Sub t r u >>= i .= Is [] e
ctx |- Sub (Var Meta i u) _ Zero = do
  ctx |- Sub Nat 1 u >>= i .= Is [] Zero
ctx |- Sub (Var Meta i u) r (Succ n e) = do
  t <- typeOf e
  let v = Var Meta (i .: 0) t
  let e' = Succ n v
  (s, ctx') <- ctx |- Sub t r u >>= i .= Is [mkMeta t] e'
  ctx' |- Sub v s e
ctx |- Sub e@(Type _ (Small _)) r (Var Meta i u) = do
  t <- typeOf e
  ctx |- Sub t r u >>= i .= Is [] e
ctx |- Sub e@Nat r (Var Meta i u) = do
  t <- typeOf e
  ctx |- Sub t r u >>= i .= Is [] e
ctx |- Sub (Type r1 (Small t)) r (Type r2 (Small u)) = do
  ctx |- Super 1 u t <&> first (const (r * r2 / r1))
ctx |- Sub (Type r1 (Small _)) r (Type r2 (Big _)) = do
  pure (r * r2 / r1, ctx)
ctx |- Sub (Type r1 (Big m)) r (Type r2 (Big n)) | m <= n = do
  pure (r * r2 / r1, ctx)
ctx |- Sub Level _ Level = pure (0, ctx)
ctx |- Sub Nat _ Level = pure (0, ctx)
ctx |- Sub Nat r Nat = pure (signum r, ctx)
ctx |- Sub Zero r Zero = pure (signum r, ctx)
ctx |- Sub Zero r (Succ _ t) = ctx |- Sub Zero r t
ctx |- Sub Zero _ (Max _ t) = ctx |- Sub Zero 0 t
ctx |- Sub (Succ m t) r (Succ n u) = case compare m n of
  LT -> ctx |- Sub t r (Succ (n - succ m) u)
  EQ -> ctx |- Sub t r u
  GT -> ctx |- Sub (Succ (m - succ n) t) r u
ctx |- Sub (Succ n t) r (Max _ u) = ctx |- Sub (Succ n t) r u
ctx |- Sub (Max vs t) r u = do
  (r1, ctx1) <- ctx |- Sub t r u
  let combine (r2, ctx2) (i, (f, s)) = ctx2 |- Sub (Var f i s) r2 u
  foldM combine (r1, ctx1) (M.toList vs)
ctx |- Sub (Sum a b) r (Sum c d) = do
  (r1, ctx1) <- ctx |- Sub a r c
  (r2, ctx2) <- ctx1 |- Sub b r d
  pure (infQty r1 r2, ctx2)
ctx |- Sub (Product ts) r (Product us) | length ts == length us = do
  let combine (r', ctx') (t, u) = ctx' |- Sub t r u <&> first (infQty r')
  foldM combine (r, ctx) (zip (F.toList ts) (F.toList us))
ctx |- Sub (Tuple ts) r (Tuple us) | length ts == length us = do
  let combine (r', ctx') (t, u) = ctx' |- Sub t r u <&> first (infQty r')
  foldM combine (1, ctx) (zip (F.toList ts) (F.toList us))
ctx |- Sub (Con c1 _ as1) r (Con c2 _ as2) | c1 == c2 = do
  foldM (|-) ctx (zipWith Conv (F.toList as1) (F.toList as2)) <&> (r,)
ctx |- Sub (Forall Bare _ a b) r (Forall Bare x c d) = do
  (r1, ctx1) <- ctx |- Super 1 a c
  let r2 = piQty r1 r
  let i = length ctx1
  let v = Var Stable (Here i) c
  let ctx2 = ctx1 :|> mkLocal Stable x Of c
  ctx2 |- Sub (enter v b) r2 (enter v d) >>= clear i <&> first (piQty r1)
ctx |- Sub (Forall Bare x a b) r t | isDependent b = do
  (r1, ctx1) <- ctx |- Usage 1 a
  let r2 = piQty r1 r
  let i = length ctx
  let v = Var Meta (Here i) a
  let ctx2 = ctx1 :|> mkLocal Meta x Of a
  ctx2 |- Sub (enter v b) r2 t >>= clear i <&> first (piQty r1)
ctx |- Sub (Forall At _ a b) r (Forall At x c d) = do
  (r1, ctx1) <- ctx |- Super 1 a c
  let r2 = piQty r1 r
  let i = length ctx1
  let v = var i c
  let ctx2 = ctx1 :|> mkPlain x Of c
  ctx2 |- Sub (enter v b) r2 (enter v d) >>= clear i <&> first (piQty r1)
ctx |- Sub t r (Forall Hash x a b) = do
  (r1, ctx1) <- ctx |- Usage 1 a
  let r2 = piQty r1 r
  let i = length ctx1
  let v = Var Plain (Here i) a
  let ctx2 = ctx1 :|> mkLocal Plain x Of a
  ctx2 |- Sub t r2 (enter v b) >>= clear i <&> first (piQty r1)
ctx |- Sub (Forall Hash x a b) r t = do
  (r1, ctx1) <- ctx |- Usage 1 a
  let r2 = piQty r1 r
  let i = length ctx
  let v = Var Meta (Here i) a
  let ctx2 = ctx1 :|> mkLocal Meta x Of a
  ctx2 |- Sub (enter v b) r2 t >>= clear i <&> first (piQty r1)
ctx |- Sub (Fun h _ a b) r (Fun h' x c d) | h == h' = do
  (r1, ctx1) <- ctx |- Super 1 a c
  let r2 = piQty r1 r
  let i = length ctx1
  let v = var i c
  let ctx2 = ctx1 :|> mkPlain x Of c
  ctx2 |- Sub (enter v b) r2 (enter v d) >>= clear i <&> first (piQty r1)
ctx |- j@Sub {} = typeError ctx j
ctx |- j@(Super r u t) = do
  (r', ctx') <- ctx |- Sub t r u
  test (1 <: r') ctx j (r', ctx')
ctx |- j@(Usage r t) = do
  (r', ctx') <- ctx |- Sub t r t
  test (1 <: r') ctx j (r', ctx')
ctx |- Conv (MkAr h t) (MkAr h' u) | h == h' = do
  ctx |- Super 1 u t >>= (|- Super 1 t u) . snd <&> snd
ctx |- j@Conv {} = typeError ctx j
ctx |- Elab sc (VarE x) as u
  | Just e@(Var _ ix t) <- sc HM.!? idText x = do
      pushQty ctx & use ix >>= (|- Apply e t as u)
  | Just e@(Con _ t Empty) <- sc HM.!? idText x = do
      pushQty ctx |- Apply e t as u
ctx |- Elab sc (AnnE e a) as u = do
  (t, (_, ctx1)) <- ctx |- Elab sc a [] inferType
  (e', (_, ctx2)) <- pushQty ctx1 |- Elab sc e [] (In t)
  ctx2 |- Apply e' t as u
ctx |- Elab sc (ForallE (MkP ps (HasAnn a)) e) as t = do
  let ps' = SYB.gmapT (SYB.mkT (`AnnP` a)) <$> ps
  ctx |- Elab sc (ForallE (MkP ps' NoAnn) e) as t
ctx |- Elab sc (ForallE (MkP [] NoAnn) e) as t = ctx |- Elab sc e as t
ctx |- Elab sc (ForallE (MkP (p : ps) NoAnn) e) as u
  | BareP (VarP x) <- p = do
      let (i, (t, ctx1)) = newTypeMeta ctx
      todo ctx1 "Elab" >>= \k -> k sc ps e as u x i t
ctx |- Elab sc (FunE [] e) as t = ctx |- Elab sc e as t
ctx |- Elab sc (FunE (BareP p : ps) e) [] u
  | Just cmd <- elabFunE ctx sc Bare p ps e u = cmd
ctx |- Elab sc (FunE (AtP p : ps) e) [] u
  | Just cmd <- elabFunE ctx sc At p ps e u = cmd
ctx |- Elab sc (CallE e as') as t = do
  ctx |- Elab sc e (map (Sj sc) as' ++ as) t
ctx |- Elab sc e [] (In (Box r t)) =
  pushQty ctx |- Elab sc e [] (In t) <&> second (second (popQty r))
ctx |- Elab sc e [] (In (Forall Bare x t u)) = do
  let i = length ctx
  let ctx' = ctx :|> mkPlain x Of t
  ctx' |- Elab sc e [] (In (enter (var i t) u))
ctx |- Elab sc e [] (In (Forall Hash x t u)) = do
  let i = length ctx
  let ctx' = ctx :|> mkPlain x Of t
  ctx' |- Elab sc e [] (In (enter (var i t) u))
ctx |- j@Elab {} = typeError ctx j
ctx |- Apply e t [] (In u) =
  ctx |- Sub t 1 u <&> (e,) . (Out,) . uncurry popQty
ctx |- Apply e t [] Out =
  ctx |- Usage 1 t <&> (e,) . (In t,) . uncurry popQty
ctx |- j@Apply {} = typeError ctx j
ctx |- Generalise _ i e u | i == length ctx = pure (e, (u, ctx))
ctx :|> Local [r] Plain x Of t |- Generalise h i e u | i <= length ctx = do
  ctx' <- ctx |- Usage r t <&> snd
  let e' = Fun h x t (OpenTm mempty (length ctx') e)
  let u' = Forall h x t . OpenTm mempty (length ctx') <$> u
  ctx' |- Generalise h i e' u'
ctx :|> Local [r] Meta x Of t |- Generalise h i e u | i <= length ctx = do
  ctx' <- ctx |- Usage r t <&> snd
  let u' = Forall Hash x t . OpenTm mempty (length ctx') <$> u
  ctx' |- Generalise h i e u'
pfx :|> Local [r] Meta x (Is sfx t) k |- Generalise h i e u
  | i <= length pfx = do
      let j = length pfx
      (action, sfx') <- flatten j sfx
      let ctx = pfx <> sfx' :|> Local [r] Meta x Of k
      let u' = act (action <> (j |-> t)) <$> u
      ctx |- Generalise h i e u'
ctx |- j@Generalise {} = typeError ctx j

elabFunE ::
  (MonadError TcErr m) =>
  Ctx ->
  Scope ->
  Decor ->
  Pat ->
  [Param] ->
  Exp ->
  Mode a Tm ->
  Maybe (m (Result a))
elabFunE ctx sc h (AnnP (VarP x) a) ps e (In (Forall h' _ t u))
  | h' == flipDecor h = Just $ do
      let i = length ctx
      (a', (_, ctx1)) <- ctx |- Elab sc a [] inferType
      ctx2 <- ctx1 |- Super 1 a' t <&> snd
      elabVarP ctx2 sc h' x ps i e t (In u)
elabFunE ctx sc h (AnnP (VarP x) a) ps e Out
  | h' <- flipDecor h = Just $ do
      let i = length ctx
      (t, (_, ctx')) <- ctx |- Elab sc a [] inferType
      elabVarP ctx' sc h' x ps i e t Out
elabFunE ctx sc h (VarP x) ps e (In (Forall h' _ t u))
  | h' == flipDecor h = Just $ do
      let i = length ctx
      elabVarP ctx sc h' x ps i e t (In u)
elabFunE ctx sc h (VarP x) ps e Out
  | h' <- flipDecor h = Just $ do
      let (i, (t, ctx')) = newTypeMeta ctx
      elabVarP ctx' sc h' x ps i e t Out
elabFunE _ _ _ _ _ _ _ = Nothing

newTypeMeta :: Ctx -> (Int, (Tm, Ctx))
newTypeMeta ctx = do
  let i = length ctx
  let hk = Type maxBound (Small (Var Meta (Here i) Level))
  let k = Var Meta (Here (i + 1)) hk
  let t = Var Meta (Here (i + 2)) k
  (i, (t, ctx :|> mkMeta Level :|> mkMeta hk :|> mkMeta k))

elabVarP ::
  (MonadError TcErr m) =>
  Ctx ->
  Scope ->
  Decor ->
  Id ->
  [Param] ->
  Int ->
  Exp ->
  Tm ->
  Mode b OpenTm ->
  m (Result b)
elabVarP ctx sc h x ps i e t u = do
  let v = var i t
      ctx1 = ctx :|> mkPlain (Just (idName x)) Of t
      sc' = extendScope x v sc
  (e', (u', ctx2)) <- ctx1 |- Elab sc' (FunE ps e) [] (enter v <$> u)
  ctx2 |- Generalise h i e' u'

var :: Int -> Tm -> Tm
var i = Var Plain (Here i)

infixr 9 !

(!) :: (MonadError TcErr m) => Ctx -> Index -> m Bound
ctx ! (i :. is) = case ctx S.!? i of
  Just (Local _ _ _ (Is ctx' _) _) -> ctx' ! is
  _ -> anomaly "Variable not found"
ctx ! Here i = case ctx S.!? i of
  Just (Local _ _ _ b _) -> pure b
  Nothing -> anomaly "Variable not found"

infixl 4 .=

(.=) :: (MonadError TcErr m) => Index -> Bound -> (Qty, Ctx) -> m (Qty, Ctx)
(i :. is .= b) (q, ctx) = case S.splitAt i ctx of
  (pfx, Local qs f x (Is ctx1 e) t :<| sfx) -> do
    (q', ctx2) <- (is .= b) (q, ctx1)
    pure (q', pfx >< Local qs f x (Is ctx2 e) t :<| sfx)
  _ -> anomaly "Variable not found"
(Here i .= b) (q, ctx) = case S.splitAt i ctx of
  (pfx, Local qs Meta x Of t :<| sfx) ->
    pure (q, pfx >< Local qs Meta x b t :<| sfx)
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

clear :: (MonadError TcErr m) => Int -> (Qty, Ctx) -> m (Qty, Ctx)
clear i (q, ctx) = ctx |- Generalise Hash i Zero Out <&> (q,) . snd . snd

flatten :: (MonadError TcErr m) => Int -> Ctx -> m (Action, Ctx)
flatten _ Empty = pure (mempty, Empty)
flatten _ ctx = todo ctx "flatten"

pushQty :: Ctx -> Ctx
pushQty = fmap go
  where
    go :: SYB.GenericT
    go = SYB.gmapT go `SYB.extT` (0 :#)

popQty :: Qty -> Ctx -> Ctx
popQty r = fmap go
  where
    go :: SYB.GenericT
    go = SYB.gmapT go `SYB.extT` \(q1 :# q2 :# qs) -> r * q1 + q2 :# qs
