{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns #-}

module Qty where

import Data.Data (Data)
import Data.Ratio (denominator, numerator)

infix 0 <~, <:

data Qty = O | I | (:?) | (:+) | (:*)
  deriving (Eq, Ord, Read, Show, Enum, Bounded, Data)

instance Num Qty where
  fromInteger n | n > 1 = (:+)
  fromInteger 1 = I
  fromInteger 0 = O
  fromInteger _ = error "fromInteger{Qty}: negative integer"
  O + r = r
  r + O = r
  (:?) + (:?) = (:*)
  (:?) + (:*) = (:*)
  (:*) + (:?) = (:*)
  (:*) + (:*) = (:*)
  _ + _ = (:+)
  r - s | Just d <- diffQty r s = d
  _ - _ = error "(-){Qty}: underflow"
  _ * O = O
  O * _ = O
  r * I = r
  I * r = r
  (:?) * (:?) = (:?)
  (:+) * (:+) = (:+)
  _ * _ = (:*)
  abs O = (:?)
  abs r = r
  signum O = O
  signum _ = I

instance Real Qty where
  toRational O = 0
  toRational I = 1
  toRational (:+) = 2
  toRational _ = undefined

instance Integral Qty where
  toInteger O = 0
  toInteger I = 1
  toInteger (:+) = 2
  toInteger _ = undefined
  divMod r O = ((:*), r)
  divMod O _ = (O, O)
  divMod I I = (I, O)
  divMod I _ = (O, I)
  divMod (:?) r | (:?) <~ r = ((:?), O)
  divMod (:?) _ = (O, (:?))
  divMod (:+) r | (:+) <~ r = ((:+), O)
  divMod (:+) _ = ((:*), I)
  divMod (:*) _ = ((:*), O)
  quotRem = divMod

instance Fractional Qty where
  fromRational q = fromInteger (numerator q) / fromInteger (denominator q)
  r / s | Just q <- overQty r s = q
  _ / _ = error "(/){Qty}: division by zero"

(<~) :: Qty -> Qty -> Bool
(:*) <~ _ = True
(:+) <~ I = True
(:?) <~ I = True
(:?) <~ O = True
r <~ s = r == s

(<:) :: Qty -> Qty -> Bool
(:*) <: _ = True
(:+) <: I = True
(:?) <: I = True
_ <: O = True
r <: s = r == s

upperQty :: Qty -> [Qty]
upperQty O = [O]
upperQty I = [I]
upperQty (:?) = [(:?), I, O]
upperQty (:+) = [(:+), I]
upperQty (:*) = [(:*), (:+), (:?), I, O]

infQty :: Qty -> Qty -> Qty
infQty O O = O
infQty O I = (:?)
infQty I O = (:?)
infQty O (:?) = (:?)
infQty (:?) O = (:?)
infQty I r = r
infQty r I = r
infQty (:?) (:?) = (:?)
infQty (:+) (:+) = (:+)
infQty _ _ = (:*)

supQty :: Qty -> Qty -> Qty
supQty r s = complQty (complQty r * complQty s)

complQty :: Qty -> Qty
complQty O = O
complQty I = (:*)
complQty (:?) = (:+)
complQty (:+) = (:?)
complQty (:*) = I

-- | @diffQty x y@ is the @(<~)@ supremum of @{r | x <~ r + y}@
diffQty :: Qty -> Qty -> Maybe Qty
diffQty r O = Just r
diffQty O _ = Nothing
diffQty I I = Just 0
diffQty I _ = Nothing
diffQty (:?) r | (:?) <~ r = Just O
diffQty (:?) _ = Nothing
diffQty (:+) r | (:+) <~ r = Just (:*)
diffQty (:+) _ = Just (:+)
diffQty (:*) _ = Just (:*)

-- | @overQty x y@ is the @(<:)@ supremum of @{r | r * y <~ x}@
overQty :: Qty -> Qty -> Maybe Qty
overQty O _ = Just O
overQty _ O = Nothing
overQty r s | s <~ r = Just I
overQty (:*) r = Just (complQty r)
overQty r _ = Just r

infixr 5 :#

pattern (:#) :: Qty -> [Qty] -> [Qty]
pattern q :# qs <- (\case [] -> (O, []); q : qs -> (q, qs) -> (q, qs))
  where
    O :# [] = []
    q :# qs = q : qs

{-# COMPLETE (:#) #-}
