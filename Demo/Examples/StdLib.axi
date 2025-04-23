data type Empty where

data type Unit where
  unit

data type Nat where
  zero : Nat
  succ : Nat -> Nat

data type List A where
  nil  : List A
  cons : A -> List A -> List A