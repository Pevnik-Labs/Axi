// Basic kinds of objects: types, terms, propositions, proofs

// Term definition
answer : Nat => 42

answer : Nat
answer => 42

answer : Nat
_ => 42

// Function definition (lambda)
id : Nat -> Nat => fn n => n

// Function definition (short)
id (n : Nat) : Nat => n

// (Implicitly) Polymorphic function (should we overload forall?)
id : forall a, a -> a
id x => x

// (Explicitly) Polymorphic function
id : forall a -> a -> a
id a x => x

id : forall a, a -> a => fn a x => x

// Very implicit arguments (auto-generalise free type variables)
id : a -> a
id x => x

comp : (b -> c) -> (a -> b) -> a -> c
_ f g x => f (g x)

// Nameless axiom
axiom : 2 + 2 = 42

// Named axiom
axiom why-not-lol : False

// Theorem ('by' notation)
theorem comp_id_r : forall a b (f : a -> b), comp id f = f => by
  assume a b f
  funext x
  refl

// Theorem (term style)
theorem : forall a b (f : a -> b). comp id f = f =>
  assume a b f => funext x => refl

theorem hyp-distrib : (a -> b -> c) -> (a -> b) -> a -> c =>
  assume (G : a -> b -> c) (H : a -> b) `a =>
    apply G `a (H `a)

// Type declaration
type T

// Type definition (synonym)
type NatToNat => Nat -> Nat

// Type definition (record)
type Point => {x of Nat; y of Nat}

// Type definition (variant)
data Bool where
  no
  yes

// Type definition (polymorphic variant)
data Option a where
  no
  yes of a

data Sum a b where
  no of a
  yes of b

// Type definition (inductive)
data List a where
  nil
  (::) of a, List a

// Type definition (desugared)
type List a => data L where
  nil
  (::) of a, L

// Type definition (inductive)
type Expr => data E a where
  var of a
  lam of E (Option a)
  app of E a, E a

// Relation declaration (kinding)
decl R : Nat -> Nat -> Prop

// Proposition definition
proposition and P Q => P /\ Q
proposition or P Q => P \/ Q
proposition impl P Q => P -> Q
proposition iff P Q => P <-> Q
proposition not P => ~ P

// Recursive functions
map (f : a -> b) : List a -> List b
_ nil => nil
_ (h :: t) => f h :: map f t

app : List a -> List a -> List a
_ nil l => l
_ (cons h t) l => cons h (app t l)

app (l1 l2 : List a) : List a => match l1 with
  nil => l2
  (cons h t) => cons h (app t l2)

// Proof by induction
theorem map_id : forall a (l : List a), map id l = l => by
  assume a l
  induction l with
    nil => refl
    cons h t =>
      rewrite `(map id t = t)
      refl

// Proof by induction (alternative layout, and explicit ind use)
theorem map_id : forall a l. map id l = l =>
  assume a l =>
    induction l with
      nil => refl
      cons h t =>
        rewrite (ind t) =>
        refl
