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

import Control.Arrow (first, second, (***))
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
import Name (Name (IdName), idText, isWildcard)
import Numeric.Natural (Natural)
import Qty (Qty (..), infQty, maximal, supQty, (<:), pattern (:#))
import Syntax.Abs

type Ctx = Seq Local

newtype Warning = UnusedVariable Name
  deriving (Show)

type Warnings = Seq Warning

data TcErr = MkTcErr
  { tcErrNested :: Maybe T.Text,
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
    { tcErrNested = Nothing,
      tcErrTag = Anomaly,
      tcErrCtx = Nothing,
      tcErrMsg = Nothing,
      tcErrJudgment = Nothing
    }

rethrowError :: (MonadError TcErr m) => T.Text -> TcErr -> m a
rethrowError msg err = throwError err {tcErrNested = Just msg}

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

data Flavour
  = -- | Existential (flexible) monomorphic variable
    Meta
  | -- | Universal (rigid) monomorphic variable
    Plain
  | -- | Universal (rigid) polymorphic variable
    Stable
  deriving (Eq, Show, SYB.Data)

isMono :: Flavour -> Bool
isMono Meta = True
isMono Plain = True
isMono Stable = False

data Local = Local [Qty] Flavour Name Bound Tm
  deriving (Show, SYB.Data)

mkLocal :: Flavour -> Name -> Bound -> Tm -> Local
mkLocal = Local [0]

mkPlain :: Name -> Bound -> Tm -> Local
mkPlain = mkLocal Plain

mkMeta :: Name -> Tm -> Local
mkMeta x = mkLocal Meta x Of

data AbsTm = MkAbs Action Int Tm
  deriving (Show, SYB.Data)

enter :: Tm -> AbsTm -> Tm
enter t (MkAbs (Subst a) d u) = actTm (Subst (IM.insert d t a)) u

pattern MkAbs' :: Int -> Tm -> AbsTm
pattern MkAbs' d u <- (MkAbs a d (actTm a -> u))
  where
    MkAbs' d u = MkAbs mempty d u

{-# COMPLETE MkAbs' #-}

strengthen :: AbsTm -> Maybe Tm
strengthen (MkAbs' d e) | fresh d e = Just e
strengthen _ = Nothing

isDependent :: AbsTm -> Bool
isDependent (MkAbs' d e) = fresh d e

infixr 5 :.

infixl 5 .:

data Index = Index Int Path
  deriving (Eq, Ord, SYB.Data)

instance Show Index where
  showsPrec p (Here i) =
    showParen (p > 10) $ showString "Here " . showsPrec 11 i
  showsPrec p (i :. is) =
    showParen (p > 5) $
      showsPrec 6 i
        . showString " :. "
        . showsPrec 5 is

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
  = Var Flavour Index Tm
  | Bot Tm
  | Top Tm
  | Type Qty Level
  | Level
  | Max (M.Map Index (Flavour, Tm)) Tm
  | Nat
  | Zero
  | Succ Natural Tm
  | Sum Tm Tm
  | Product (Seq Tm)
  | Tuple (Seq Tm)
  | Con Name Tm Spine
  | Box Qty Tm
  | Fn Flavour Name Tm AbsTm
  | Lam Flavour Name Tm AbsTm
  deriving (Show, SYB.Data)

viewArrow :: Tm -> Maybe (Tm, Tm)
viewArrow (Fn Plain _ t (strengthen -> Just u)) = Just (t, u)
viewArrow _ = Nothing

pattern (:->) :: Tm -> Tm -> Tm
pattern t :-> u <- (viewArrow -> Just (t, u))

boxT :: (MonadError TcErr m) => Qty -> Tm -> m Tm
boxT 1 e = pure e
boxT r (Box s e) = boxT (r * s) e
boxT r e =
  typeOf e >>= \case
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

type Env = HM.HashMap T.Text Tm

type Scope = HM.HashMap T.Text Tm

data Subject a = Sj Scope a
  deriving (Show, SYB.Data)

lookupScope :: Id -> Scope -> Maybe Tm
lookupScope x = HM.lookup (idText x)

extendScope :: Id -> Tm -> Scope -> Scope
extendScope x _ sc | isWildcard x = sc
extendScope x e sc = HM.insert (idText x) e sc

data Mode b a where
  Out :: Mode 'False a
  In :: a -> Mode 'True a

deriving instance Functor (Mode b)

deriving instance Foldable (Mode b)

deriving instance Traversable (Mode b)

deriving instance (Show a) => Show (Mode b a)

unIn :: Mode 'True a -> a
unIn (In x) = x

flipMode :: a -> Mode b a -> (a, Mode (Not b) a)
flipMode _ (In a) = (a, Out)
flipMode a Out = (a, In a)

type Pass b = (Tm, Mode b Tm)

type Result b = Pass (Not b)

data Judgment a where
  Sub :: Tm -> Qty -> Tm -> Judgment Qty
  Super :: Qty -> Tm -> Tm -> Judgment Qty
  Usage :: Qty -> Tm -> Judgment Qty
  Conv :: Ar -> Ar -> Judgment ()
  Elab :: Scope -> Exp -> [Subject Arg] -> Mode b Tm -> Judgment (Result b)
  Apply :: Tm -> Tm -> [Subject Arg] -> Mode b Tm -> Judgment (Result b)
  Gen ::
    Flavour ->
    Int ->
    Mode b1 Tm ->
    Mode b2 Tm ->
    Mode b3 Tm ->
    Judgment (Mode b1 Tm, (Mode b2 Tm, Mode b3 Tm))

deriving instance Show (Judgment a)

actTm :: Action -> Tm -> Tm
actTm s@(Subst im) (Var f (Here i) k) =
  fromMaybe (Var f (Here i) (actTm s k)) (IM.lookup i im)
actTm s t = SYB.gmapT go t
  where
    go :: SYB.GenericT
    go =
      SYB.gmapT go
        `SYB.extT` actTm s
        `SYB.extT` \(MkAbs a d u) -> MkAbs (trim d (s <> a)) d u

typeOf :: (MonadError TcErr m) => Tm -> m Tm
typeOf (Var _ _ k) = pure k
typeOf (Bot k) = pure k
typeOf (Top k) = pure k
typeOf (Type _ l) = pure (Type Er (succL l))
typeOf Level = pure (Type Er omegaL)
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
typeOf (Fn _ _ t (MkAbs' d u)) = piSort t d =<< typeOf u
typeOf (Lam h x t (MkAbs s d e)) = Fn h x t . MkAbs s d <$> typeOf e

leastSort :: Tm
leastSort = Type Un zeroL

leastBigSort :: Tm
leastBigSort = Type Un omegaL

fresh :: (SYB.Data a) => Int -> a -> Bool
fresh i =
  SYB.gmapQr (&&) True (fresh i)
    `SYB.extQ` (i /=)
    `SYB.extQ` freshAbsTm i

freshAbsTm :: Int -> AbsTm -> Bool
freshAbsTm i (MkAbs' d u) = d <= i || fresh i u

killDependency :: (MonadError TcErr m) => Int -> Tm -> m Tm
killDependency d k
  | fresh d k = pure k -- sort is non-dependent, go ahead
  | otherwise = supT leastBigSort k -- mix in big sort to kill dependency

codomain :: (MonadError TcErr m) => Tm -> Spine -> m Tm
codomain (_ :-> k) (_ :<| ts) = codomain k ts
codomain k Empty = pure k
codomain _ _ = anomaly "Ill-formed type constructor application"

supT :: (MonadError TcErr m) => Tm -> Tm -> m Tm
supT (Type r1 l1) (Type r2 l2) = Type (supQty r1 r2) <$> maxL l1 l2
supT _ _ = anomaly "Ill-formed type"

piSort :: (MonadError TcErr m) => Tm -> Int -> Tm -> m Tm
piSort t d u =
  (,) <$> typeOf t <*> killDependency d u >>= \case
    (Type r1 l1, Type r2 l2) -> Type (piQty r1 r2) <$> maxL l1 l2
    _ -> anomaly "Ill-formed function type"

piQty :: Qty -> Qty -> Qty
piQty 0 r = r
piQty _ _ = 1

infixr 2 |-

infixr 3 :->

(|-) :: (MonadError TcErr m) => Ctx -> Judgment a -> m (a, Ctx)
ctx |- Sub (Var _ i _) r u | Right (Is _ t) <- ctx ! i = ctx |- Sub t r u
ctx |- Sub t r (Var _ i _) | Right (Is _ u) <- ctx ! i = ctx |- Sub t r u
ctx |- Sub (Var _ j _) r (Var Meta i t) | j == i = do
  (s, ctx') <- ctx |- Sub t r t
  if maximal s
    then pure (s, ctx')
    else do
      b <- boxT s (Var Meta (i .: 0) t)
      (i .= Is [mkMeta "t" t] b) (signum s, ctx')
ctx |- Sub (Var _ j _) r (Var _ i t) | j == i = ctx |- Sub t r t
ctx |- Sub e@(Var f j t) r (Var Meta i u) | isMono f && j < i = do
  ctx |- Sub t r u >>= i .= Is [] e
ctx |- Sub (Var Meta i u) r e@(Var f j t) | isMono f && j < i = do
  t' <- boxT r t
  (s, ctx') <- ctx |- Sub t' 1 u
  e' <- boxT s e
  (i .= Is [] e') (signum s, ctx')
ctx |- Sub (Bot t) r e = typeOf e >>= \u -> ctx |- Sub t r u
ctx |- Sub e r (Top u) = typeOf e >>= \t -> ctx |- Sub t r u
ctx |- Sub t r (Type s l) | not (maximal s) = do
  ctx |- Sub t (r * s) (Type (signum s) l)
ctx |- Sub t r (Box s u) = ctx |- Sub t (r * s) u
ctx |- Sub (Box s t) r u | Just q <- s <: r = ctx |- Sub t q u
ctx |- Sub (Var Meta i u) r (Type s (Small l)) = do
  let e = Type (r * s) (Small l)
  t <- typeOf e
  ctx |- Sub t 1 u >>= i .= Is [] e
ctx |- Sub t@(Var Meta _ _) r (Type s (Big _)) = do
  let i = length ctx
  let u = Type s (Small (Var Meta (Here i) Level))
  ctx :|> mkMeta "l" Level |- Sub t r u >>= clear i
ctx |- Sub t@(Var Meta _ _) r Level = ctx |- Sub t r Nat
ctx |- Sub (Var Meta i u) r e@Nat = do
  t <- typeOf e
  ctx |- Sub t r u >>= i .= Is [] e
ctx |- Sub (Var Meta i u) _ Zero = do
  ctx |- Sub Nat 1 u >>= i .= Is [] Zero
ctx |- Sub (Var Meta i u) r (Succ n e) = do
  let v = Var Meta (i .: 0) u
  ctx |- Sub v r e >>= i .= Is [mkMeta "n" u] (Succ n v)
ctx |- Sub (Var Meta i _) r (Max vs _) | M.member i vs = pure (r, ctx)
ctx |- Sub t@(Var Meta _ _) r (Max _ u) = ctx |- Sub t r u
ctx |- Sub e@(Type _ (Small _)) r (Var Meta i u) = do
  t <- typeOf e
  ctx |- Sub t r u >>= i .= Is [] e
ctx |- Sub e@Nat r (Var Meta i u) = do
  t <- typeOf e
  ctx |- Sub t r u >>= i .= Is [] e
ctx |- Sub Zero r (Var f _ u) | isMono f = do
  ctx |- Sub Nat r u
ctx |- Sub (Succ n e) r (Var Meta i u) = do
  let v = Var Meta (i .: 0) u
  ctx |- Sub e r v >>= i .= Is [mkMeta "n" u] (Succ n v)
ctx |- Sub (Type r1 (Small t)) r (Type r2 (Small u))
  | Just q <- r1 <: (r * r2) = do
      ctx |- Super 1 u t <&> first (const q)
ctx |- Sub (Type r1 (Small _)) r (Type r2 (Big _))
  | Just q <- r1 <: (r * r2) = do
      pure (q, ctx)
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
  let combine ctx' (t, u) = ctx' |- Conv t u <&> snd
  foldM combine ctx (zip (F.toList as1) (F.toList as2)) <&> (r,)
ctx |- Sub (Fn Stable _ a b) r (Fn Stable x c d) = do
  (r1, ctx1) <- ctx |- Super 1 a c
  let r2 = piQty r1 r
  let i = length ctx1
  let v = Var Stable (Here i) c
  let ctx2 = ctx1 :|> mkLocal Stable x Of c
  ctx2 |- Sub (enter v b) r2 (enter v d) >>= clear i <&> first (piQty r1)
ctx |- Sub (Fn Stable x a b) r t | isDependent b = do
  (r1, ctx1) <- ctx |- Usage 1 a
  let r2 = piQty r1 r
  let i = length ctx
  let v = Var Meta (Here i) a
  let ctx2 = ctx1 :|> mkMeta x a
  ctx2 |- Sub (enter v b) r2 t >>= clear i <&> first (piQty r1)
ctx |- Sub (Fn Plain _ a b) r (Fn Plain x c d) = do
  (r1, ctx1) <- ctx |- Super 1 a c
  let r2 = piQty r1 r
  let i = length ctx1
  let v = var i c
  let ctx2 = ctx1 :|> mkPlain x Of c
  ctx2 |- Sub (enter v b) r2 (enter v d) >>= clear i <&> first (piQty r1)
ctx |- Sub t r (Fn Meta x a b) = do
  (r1, ctx1) <- ctx |- Usage 1 a
  let r2 = piQty r1 r
  let i = length ctx1
  let v = Var Plain (Here i) a
  let ctx2 = ctx1 :|> mkLocal Plain x Of a
  ctx2 |- Sub t r2 (enter v b) >>= clear i <&> first (piQty r1)
ctx |- Sub (Fn Meta x a b) r t = do
  (r1, ctx1) <- ctx |- Usage 1 a
  let r2 = piQty r1 r
  let i = length ctx
  let v = Var Meta (Here i) a
  let ctx2 = ctx1 :|> mkMeta x a
  ctx2 |- Sub (enter v b) r2 t >>= clear i <&> first (piQty r1)
ctx |- Sub (Lam h _ a b) r (Lam h' x c d) | h == h' = do
  (r1, ctx1) <- ctx |- Super 1 a c
  let r2 = piQty r1 r
  let i = length ctx1
  let v = var i c
  let ctx2 = ctx1 :|> mkPlain x Of c
  ctx2 |- Sub (enter v b) r2 (enter v d) >>= clear i <&> first (piQty r1)
ctx |- j@Sub {} = typeError ctx j
ctx |- j@(Super r u t) = do
  (r', ctx') <- ctx |- Sub t r u
  test (maximal r') ctx j (r', ctx')
ctx |- j@(Usage r t) = do
  (r', ctx') <- ctx |- Sub t r t
  test (maximal r') ctx j (r', ctx')
ctx |- Conv (MkAr h t) (MkAr h' u) | h == h' = do
  ctx |- Super 1 u t >>= (|- Super 1 t u) . snd <&> ((),) . snd
ctx |- j@Conv {} = typeError ctx j
ctx |- Elab sc (VarE x) as u
  | Just e@(Var _ ix t) <- lookupScope x sc = do
      pushQty ctx & use ix >>= (|- Apply e t as u)
  | Just e <- lookupScope x sc = do
      let (e', ctx') = instantiateLevels e ctx
      t <- typeOf e'
      pushQty ctx' |- Apply e' t as u
ctx |- Elab sc (AnnE e a) as u = do
  ((t, _), ctx1) <- elabType ctx sc a []
  ((e', _), ctx2) <- pushQty ctx1 |- Elab sc e [] (In t)
  ctx2 |- Apply e' t as u
ctx |- Elab sc (ArrowE e1 e2) [] u
  | Just cmd <- elabArrowE ctx sc e1 e2 u = cmd
ctx |- Elab sc (ForallE (MkP ps (HasAnn a)) e) as t = do
  let ps' = SYB.gmapT (SYB.mkT (`AnnP` a)) <$> ps
  ctx |- Elab sc (ForallE (MkP ps' NoAnn) e) as t
ctx |- Elab sc (ForallE (MkP [] NoAnn) e) as t = ctx |- Elab sc e as t
ctx |- Elab sc (ForallE (MkP (ArgP h p : ps) NoAnn) e) [] u
  | Just cmd <- elabForallE ctx sc (flavourTy h) p ps e u = cmd
ctx |- Elab sc (LamE [] e) as t = ctx |- Elab sc e as t
ctx |- Elab sc (LamE (ArgP h p : ps) e) as u
  | Just cmd <- elabLamE ctx sc (flavourTm h) p ps e as u = cmd
ctx |- Elab sc (CallE e as') as t = do
  ctx |- Elab sc e (map (Sj sc) as' ++ as) t
ctx |- Elab sc e [] (In (Box r t)) =
  pushQty ctx |- Elab sc e [] (In t) <&> second (popQty r)
ctx |- Elab sc e [] (In (Fn Stable x t u)) = do
  let i = length ctx
  let ctx' = ctx :|> mkPlain x Of t
  ctx' |- Elab sc e [] (In (enter (var i t) u))
ctx |- Elab sc e [] (In (Fn Meta x t u)) = do
  let i = length ctx
  let ctx' = ctx :|> mkPlain x Of t
  ctx' |- Elab sc e [] (In (enter (var i t) u))
ctx |- j@Elab {} = typeError ctx j
ctx |- Apply e t [] (flipMode t -> (t', u)) =
  ctx |- Sub t 1 t' <&> ((e, u),) . uncurry popQty
ctx |- j@Apply {} = typeError ctx j
ctx |- Gen _ i e t u | i == length ctx = pure ((e, (t, u)), ctx)
ctx :|> Local [r] Meta x Of tx |- Gen h i e t u
  | i <= length ctx = do
      ctx' <- ctx |- Usage r tx <&> snd
      let j = length ctx'
      let t' = Fn Meta x tx . MkAbs' j <$> t
      u' <- traverse (piSort tx j) u
      ctx' |- Gen h i e t' u'
pfx :|> Local [r] Meta x (Is sfx ex) tx |- Gen h i e t u
  | i <= length pfx = do
      let j = length pfx
      (action, sfx') <- flatten j sfx
      let action' = action <> (j |-> ex)
      let ctx = pfx <> sfx' :|> Local [r] Meta x Of tx
      let e' = actTm action' <$> e
      let t' = actTm action' <$> t
      let u' = actTm action' <$> u
      ctx |- Usage r tx >>= (|- Gen h i e' t' u') . snd
ctx :|> Local [r] _ x Of tx |- Gen h i e t u
  | i <= length ctx = do
      ctx' <- ctx |- Usage r tx <&> snd
      let j = length ctx'
      let e' = Lam h x tx . MkAbs' j <$> e
      let t' = Fn h x tx . MkAbs' j <$> t
      u' <- traverse (piSort tx j) u
      ctx' |- Gen h i e' t' u'
ctx |- j@Gen {} = typeError ctx j

elabType ::
  (MonadError TcErr m) =>
  Ctx ->
  Scope ->
  Exp ->
  [Subject Arg] ->
  m ((Tm, Tm), Ctx)
elabType ctx sc e as = do
  ((t, unIn -> k), ctx1) <- ctx |- Elab sc e as Out
  (_, ctx2) <- ctx1 |- Super 1 k leastSort
  pure ((t, k), ctx2)

elabArrowE ::
  (MonadError TcErr m) =>
  Ctx ->
  Scope ->
  Exp ->
  Exp ->
  Mode b Tm ->
  Maybe (m ((Tm, Mode (Not b) Tm), Ctx))
elabArrowE ctx sc e e' u = Just $ do
  ((t, _), ctx') <- elabType ctx sc e []
  elabForallEAnnP ctx' sc Plain "_" t [] e' u

elabForallE ::
  (MonadError TcErr m) =>
  Ctx ->
  Scope ->
  Flavour ->
  Pat ->
  [Param] ->
  Exp ->
  Mode a Tm ->
  Maybe (m (Result a, Ctx))
elabForallE ctx sc h (AnnP (VarP x) a) ps e u = Just $ do
  ((t, _), ctx') <- elabType ctx sc a []
  elabForallEAnnP ctx' sc h x t ps e u
elabForallE ctx sc h (VarP x) ps e u = Just $ do
  let ((_, t), ctx') = newSort ctx
  elabForallEAnnP ctx' sc h x t ps e u
elabForallE _ _ _ _ _ _ _ = Nothing

elabForallEAnnP ::
  (MonadError TcErr m) =>
  Ctx ->
  Scope ->
  Flavour ->
  Id ->
  Tm ->
  [Param] ->
  Exp ->
  Mode a Tm ->
  m (Result a, Ctx)
elabForallEAnnP ctx sc h x a ps e u = do
  let i = length ctx
  let v = var i a
  let ctx1 = ctx :|> mkPlain (IdName x) Of a
  let sc' = extendScope x v sc
  let e' = ForallE (MkP ps NoAnn) e
  ((t, u2), ctx2) <- ctx1 |- Elab sc' e' [] Out
  ((_, (t', u')), ctx3) <- ctx2 |- Gen h i Out (In t) u2
  ctx3 |- Apply (unIn t') (unIn u') [] u

flipDecor :: Decor -> Decor
flipDecor At = Bare
flipDecor Bare = At
flipDecor h = h

flavourTm :: Decor -> Flavour
flavourTm Bare = Plain
flavourTm At = Stable
flavourTm Hash = Meta

decorTm :: Flavour -> Decor
decorTm Meta = Hash
decorTm Plain = Bare
decorTm Stable = At

flavourTy :: Decor -> Flavour
flavourTy = flavourTm . flipDecor

decorTy :: Flavour -> Decor
decorTy = flipDecor . decorTm

elabLamE ::
  (MonadError TcErr m) =>
  Ctx ->
  Scope ->
  Flavour ->
  Pat ->
  [Param] ->
  Exp ->
  [Subject Arg] ->
  Mode a Tm ->
  Maybe (m (Result a, Ctx))
elabLamE ctx sc h (AnnP (VarP x) t) ps e (Sj sca (ArgE h' a) : as) u
  | h == flavourTm h' = Just $ do
      let i = length ctx
      ((t', _), ctx1) <- elabType ctx sc t []
      ((a', _), ctx2) <- ctx1 |- Elab sca a [] (In t')
      let v = var i t'
      let ctx3 = ctx2 :|> mkPlain (IdName x) (Is [] a') t'
      let sc' = extendScope x v sc
      ((e', u'), ctx4) <- ctx3 |- Elab sc' (LamE ps e) as u
      generalise ctx4 h i e' u'
elabLamE ctx sc h (AnnP (VarP x) t) ps e [] (In (Fn h' y u w))
  | h == h' = Just $ do
      let i = length ctx
      ((t', _), ctx1) <- elabType ctx sc t []
      ctx2 <- ctx1 |- Super 1 t' u <&> snd
      let v1 = var i u
      let v2 = var (succ i) t'
      let ctx3 = ctx2 :|> mkPlain y Of u
      let ctx4 = ctx3 :|> mkLocal Meta (IdName x) (Is [] v1) t'
      let sc' = extendScope x v2 sc
      ((e', w'), ctx5) <- ctx4 |- Elab sc' (LamE ps e) [] (In (enter v1 w))
      generalise ctx5 h i e' w'
elabLamE ctx sc h (AnnP (VarP x) a) ps e [] Out = Just $ do
  let i = length ctx
  ((t, _), ctx') <- elabType ctx sc a []
  elabVarP ctx' sc h x ps i e t Out
elabLamE ctx sc h (VarP x) ps e (Sj sca (ArgE h' a) : as) u
  | h == flavourTm h' = Just $ do
      let i = length ctx
      ((a', unIn -> t), ctx') <- ctx |- Elab sca a [] Out
      let v = var i t
      let ctx1 = ctx' :|> mkPlain (IdName x) (Is [] a') t
      let sc' = extendScope x v sc
      ((e', u'), ctx2) <- ctx1 |- Elab sc' (LamE ps e) as u
      generalise ctx2 h i e' u'
elabLamE ctx sc h (VarP x) ps e [] (In (Fn h' _ t u))
  | h == h' = Just $ do
      let i = length ctx
      elabVarP ctx sc h x ps i e t (In u)
elabLamE ctx sc h (VarP x) ps e [] Out = Just $ do
  let ((i, t), ctx') = newTypeMeta ctx
  elabVarP ctx' sc h x ps i e t Out
elabLamE _ _ _ _ _ _ _ _ = Nothing

newSort :: Ctx -> ((Int, Tm), Ctx)
newSort ctx = do
  let i = length ctx
  let ctx1 = ctx :|> mkMeta "l" Level
  let k = Type Un (Small (Var Meta (Here i) Level))
  ((i, k), ctx1)

newTypeMeta :: Ctx -> ((Int, Tm), Ctx)
newTypeMeta ctx = do
  let i = length ctx
  let ((_, k), ctx1) = newSort ctx
  let ctx2 = ctx1 :|> mkMeta "t" k
  let t = Var Meta (Here (succ i)) k
  ((i, t), ctx2)

elabVarP ::
  (MonadError TcErr m) =>
  Ctx ->
  Scope ->
  Flavour ->
  Id ->
  [Param] ->
  Int ->
  Exp ->
  Tm ->
  Mode b AbsTm ->
  m (Result b, Ctx)
elabVarP ctx sc h x ps i e t u = do
  let j = length ctx
      v = var j t
      ctx1 = ctx :|> mkPlain (IdName x) Of t
      sc' = extendScope x v sc
  ((e1, u1), ctx2) <- ctx1 |- Elab sc' (LamE ps e) [] (enter v <$> u)
  generalise ctx2 h i e1 u1

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
clear i (q, ctx) = ctx |- Gen Meta i Out Out Out <&> (q,) . snd

generalise ::
  (MonadError TcErr m) =>
  Ctx ->
  Flavour ->
  Int ->
  Tm ->
  Mode a Tm ->
  m (Pass a, Ctx)
generalise ctx h i e t = ctx |- Gen h i (In e) t Out <&> first (unIn *** fst)

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

prelude :: Env
prelude =
  [ ("Type", mkType Un),
    ("Type+", mkType Re),
    ("Type?", mkType Af),
    ("Type1", mkType Li),
    ("Type0", mkType Er)
  ]

mkType :: Qty -> Tm
mkType r = do
  Lam Stable "l" Level $
    MkAbs' 0 $
      Type r (Small (Var Plain (Here 0) Level))

instantiateLevels :: Tm -> Ctx -> (Tm, Ctx)
instantiateLevels (Lam Stable x t@Level e) ctx = do
  let i = length ctx
  let ctx' = ctx :|> mkMeta x t
  let v = Var Meta (Here i) t
  let e' = enter v e
  (e', ctx')
instantiateLevels e ctx = (e, ctx)
