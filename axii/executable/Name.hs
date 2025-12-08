{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns #-}

module Name
  ( Name (IdName),
    idText,
    Rb (..),
    runRb,
    withId,
    printId,
    IsWildcard (..),
  )
where

import Control.Monad.Reader.Class (MonadReader (..))
import Data.Char (isDigit)
import Data.Data (Data)
import Data.Function ((&))
import Data.Functor.Identity (Identity (..))
import Data.HashMap.Strict qualified as HM
import Data.Maybe (fromMaybe)
import Data.Sequence (Seq (..))
import Data.String (IsString (..))
import Data.Text qualified as T
import Numeric.Natural (Natural)
import Syntax.Abs (BNFC'Position, Id (..))
import Text.Read (readMaybe)

data Name = MkName
  { nameBinder :: BNFC'Position,
    nameBase :: T.Text,
    nameSub :: Natural
  }
  deriving (Eq, Ord, Data)

instance Show Name where
  showsPrec p n =
    showParen (p > 10) $
      showString "IdName "
        . showsPrec 11 (nameId n)

instance IsString Name where
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
  (prefix <> zeroes, suffix & T.unpack & readMaybe & fromMaybe 0)
  where
    (prefix, digits) = runIdentity $ T.spanEndM (pure . isDigit) t
    (zeroes, suffix) = T.span (== '0') digits

idText :: Id -> T.Text
idText (Id (_, x)) = x

pattern IdName :: Id -> Name
pattern IdName x <- (nameId -> x)
  where
    IdName (Id ((0, 0), x)) = textName x
    IdName (Id (px, x)) = (textName x) {nameBinder = Just px}

{-# COMPLETE IdName #-}

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

runRb :: (Rb -> a) -> a
runRb f = f MkRb {rbSubs = HM.empty, rbIds = Empty}

extendRb :: Rb -> Name -> (Int, Id, Rb)
extendRb MkRb {rbSubs, rbIds} x =
  (d, x', MkRb {rbSubs = HM.insert t (i + 1) rbSubs, rbIds = rbIds :|> x'})
  where
    d = length rbIds
    t = nameBase x
    i = HM.findWithDefault 0 t rbSubs
    x' = nameId x {nameSub = i}

withId :: (MonadReader Rb m) => Name -> (Int -> Id -> m a) -> m a
withId x action = do
  rbCtx <- ask
  let (d, name, rbCtx') = extendRb rbCtx x
  local (const rbCtx') (action d name)

printId :: Id -> T.Text
printId (Id ((l, c), x)) = x <> T.pack (':' : show l ++ ':' : show c)

class IsWildcard a where
  isWildcard :: a -> Bool

instance IsWildcard T.Text where
  isWildcard x = T.length x == 0 || T.head x == '_'

instance IsWildcard Id where
  isWildcard (Id (_, x)) = isWildcard x

instance IsWildcard Name where
  isWildcard (MkName _ x _) = isWildcard x
