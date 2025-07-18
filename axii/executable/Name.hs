{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedStrings #-}

module Name where

import Control.Monad.Reader.Class (MonadReader (..))
import Control.Monad.Trans.Reader (ReaderT (..))
import Data.Char (isDigit)
import Data.Function ((&))
import Data.Functor.Identity (Identity (..))
import Data.Generics qualified as SYB
import Data.HashMap.Strict qualified as HM
import Data.Maybe (fromMaybe)
import Data.Sequence (Seq (..))
import Data.Sequence qualified as S
import Data.String qualified
import Data.Text qualified as T
import Numeric.Natural (Natural)
import Syntax.Abs (BNFC'Position, Id (..))
import Text.Read (readMaybe)

type OptName = Maybe Name

data Name = MkName
  { nameBinder :: BNFC'Position,
    nameBase :: T.Text,
    nameSub :: Natural
  }
  deriving (Eq, Ord, Show, SYB.Data)

instance Data.String.IsString Name where
  fromString str = textName (T.pack str)

textName :: T.Text -> Name
textName txt = MkName {nameBinder = Nothing, nameBase, nameSub}
  where
    (nameBase, nameSub) = textSubscript txt

-- | Break text into a base name and a natural number.
-- Zeroes before the trailing positive integer are included in the base name.
-- Lack of a trailing positive integer is interpreted as a number zero.
textSubscript :: T.Text -> (T.Text, Natural)
textSubscript t =
  (prefix <> zeroes, suffix & T.unpack & readMaybe & fromMaybe 0 & succ)
  where
    (prefix, digits) = runIdentity $ T.spanEndM (pure . isDigit) t
    (zeroes, suffix) = runIdentity $ T.spanM (pure . (== '0')) digits

idText :: Id -> T.Text
idText (Id (_, x)) = x

idName :: Id -> Name
idName (Id ((0, 0), x)) = textName x
idName (Id (px, x)) = (textName x) {nameBinder = Just px}

nameId :: Name -> Id
nameId x = Id (fromMaybe (0, 0) (nameBinder x), nameText x)

nameText :: Name -> T.Text
nameText (MkName _ x s) = addSub x s

addSub :: T.Text -> Natural -> T.Text
addSub x 0 = x
addSub x i = x <> T.pack (show i)

data Rb = MkRb
  { rbSubs :: HM.HashMap T.Text Natural,
    rbIds :: Seq Id
  }

runRb :: ReaderT Rb m a -> m a
runRb ma = runReaderT ma MkRb {rbSubs = HM.empty, rbIds = S.empty}

extendRb :: Rb -> Name -> (Int, Id, Rb)
extendRb MkRb {rbSubs, rbIds} x =
  (d, x', MkRb {rbSubs = HM.insert t (i + 1) rbSubs, rbIds = rbIds :|> x'})
  where
    d = S.length rbIds
    t = nameBase x
    i = HM.findWithDefault 0 t rbSubs
    x' = nameId x {nameSub = i}

withId :: (MonadReader Rb m) => OptName -> (Int -> Id -> m a) -> m a
withId Nothing action = withId (Just "x") action
withId (Just x) action = do
  rbCtx <- ask
  let (d, name, rbCtx') = extendRb rbCtx x
  local (const rbCtx') (action d name)

printId :: Id -> T.Text
printId (Id ((l, c), x)) = x <> T.pack (':' : show l ++ ':' : show c)

isWildcard :: Id -> Bool
isWildcard (Id (_, x)) = T.length x == 0 || T.head x == '_'
