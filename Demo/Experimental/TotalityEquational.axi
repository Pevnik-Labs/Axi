// Fails the syntactic check.
weird-id : Nat -> Nat
| zero => zero
| succ n => succ (weird-id (weird-id n))
// WARNING: Cannot establish the totality of `weird-id` with a syntactic check.

// t1 : A   t2 : A   (t1, t2 not necessarily total)
// ---------------------------------------------
// t1 =?= t2 : Prop

// t : A (t total)
// --------------------------------------------
// prefl {t} : t =?= t

// t1 : A   t2 : A   (t1, t2 total)   e : t1 =?= t2
// ------------------------------------------------
// totalize e : t1 === t2

// We should be able to prove that the graph of `weird-id` is deterministic.
theorem weird-id-det :
  forall x r1 r2 : Nat,
    weird-id x =?= r1 --> weird-id x =?= r2 --> r1 === r2
proof
  pick-any x r1 r2
  assume xr1 xr2                       // x r1 r2 : Nat, xr1 : weird-id x =?= r1, xr2 : weird-id x =?= r2 |- r1 === r2
  totalize                             // x r1 r2 : Nat, xr1 : weird-id x =?= r1, xr2 : weird-id x =?= r2 |- r1 =?= r2
  chaining
    =?= r1
    =?= weird-id x  by quarantine-rewrite <-xr1
    =?= r2          by quarantine-rewrite xr2
qed

// Now it's legal to state theorems about the graph of `weird-id`.
theorem weird-id-aux :
  forall x : Nat, weird-id x =?= x
proof                                  // |- forall x : Nat, weird-id x =?= x
  pick-any x                           // x : Nat |- weird-id x =?= x
  induction x with                     // Termination by syntactic check (ISC).
  | zero =>                            // x : Nat |- weird-id zero =?= zero
    step                               // x : Nat |- zero =?= zero
    prefl                              // Goal solved!
  | succ (n & ind IH) =>               // x : Nat, n : Nat, IH : weird-id n =?= n |- weird-id (succ n) =?= succ n
    chaining
      =?= weird-id (succ n)
      =?= succ (weird-id (weird-id n))  by step
      =?= succ (weird-id n)             by quarantine-rewrite IH
      =?= succ n                        by quarantine-rewrite IH
qed

// Proving totality of `weird-id` (RTP).
// Note an amusing fact: even though this function is not structurally
// recursive, its totality was proven using structural induction
// (in the previous lemma, that is).
totality weird-id
proof                                  // |- forall n : Nat, exists r : Nat, weird-id n =?= r
  pick-any n : Nat                     // n : Nat |- exists r : Nat, weird-id n =?= r
  witness n                            // n : Nat |- weird-id n =?= n
  instantiate weird-id-aux with n      // Theorem proved!
qed

// Now it's legal to state theorems about `weird-id`.
// Moreover, we don't need to reprove the theorem below from scratch.
// We can use the lemma about the graph that we already proved.
theorem weird-id-spec :
  forall n : Nat, weird-id n === n
proof                                  // |- forall n : Nat, weird-id n === n
  pick-any n                           // n : Nat |- weird-id n === n
  totalize                             // n : Nat |- weird-id n =?= n
  instantiate weird-id-aux with n      // Theorem proved!
qed

bad (x : Unit) : Bool = notb (bad x)
// WARNING: Cannot establish the totality of `bad` with a syntactic check.

theorem notb-nofix :
  forall b : Bool, ~ b === notb b
proof
  // TODO
qed

theorem bad-diverges :
  forall (x : Unit) (b : Bool), ~ bad x =?= b
proof                                  // |- forall (x : Unit) (b : Bool), ~ bad x =?= b
  pick-any x b                         // x : Unit, b : Bool |- ~ bad x =?= b
  assume heq                           // x : Unit, b : Bool, heq : bad x =?= b |- False
  apply notb-nofix                     // x : Unit, b : Bool, heq : bad x =?= b |- b === notb b
  totalize                             // x : Unit, b : Bool, heq : bad x =?= b |- b =?= notb b
  chaining
    =?= b
    =?= bad x         by quarantine-rewrite <- heq
    =?= notb (bad x)  by step
    =?= notb b        by quarantine-rewrite heq
qed

// `>>` is forward function composition
// `<<` is backward function composition
// `|>` is forward function application

funpow {A} (f : A -> A) : Nat -> A -> A
| zero => id
| succ n => f >> funpow f n

// This function breaks Coq's Function command (I didn't check Equations),
// and is listed as breaking HOL's tool for defining weird functions.
weirdest-zero (n : Nat) : Nat =
  funpow weirdest-zero n zero
// WARNING: Cannot establish the totality of `weirdest-zero` with a syntactic check.

theorem weirdest-zero-zero :
  weirdest-zero zero =?= zero
proof
  chaining
    =?= weirdest-zero zero
    =?= funpow weirdest-zero zero zero  by step
    =?= id zero
    =?= zero
qed

theorem weirdest-zero-spec :
  forall x : Nat, weirdest-zero x =?= zero
proof                                  // |- forall x : Nat, weirdest-zero x =?= zero
  pick-any x                           // x : Nat |- weirdest-zero x =?= zero
  induction x with                     // Termination by syntactic check (ISC).
  | zero =>                            // x : Nat |- weirdest-zero zero =?= zero
    weirdest-zero-zero                 // Goal solved!
  | succ (n & IH) =>                   // x n : Nat, IH : weirdest-zero n =?= zero |- weirdest-zero (succ n) =?= zero
    chaining
      =?= weirdest-zero (succ n)
      =?= funpow weirdest-zero (succ n) zero              by step
      =?= (weirdest-zero >> funpow weirdest-zero n) zero  by step
      =?= funpow weirdest-zero n (weirdest-zero zero)     by unfold (>>)
      =?= funpow weirdest-zero n zero                     by quarantine-rewrite weirdest-zero-zero
      =?= weirdest-zero n                                 by step // `step` also works in the reverse direction, i.e. to fold the definition
      =?= zero                                            by quarantine-rewrite IH
qed

// Even weirder...
weirdest-id : Nat -> Nat
| zero => zero
| succ n => succ (funpow weirdest-id n n)

theorem funpow-weirdest-id :
  forall r : Nat, weirdest-id r =?= r -->
    forall x : Nat, funpow weirdest-id x r =?= r
proof
  pick-any r : Nat
  assume hwid : weirdest-id r =?= r
  pick-any x : Nat
  induction x with
  | zero =>
    chaining
      =?= funpow weirdest-id zero r
      =?= id r                       by step
      =?= r
  | succ (n & ind (IH : funpow weirdest-id n r =?= r)) =>
    chaining
      =?= funpow weirdest-id (succ n) r
      =?= (weirdest-id >> funpow weirdest-id n) r  by step
      =?= funpow weirdest-id n (weirdest-id r)     by unfold (>>)
      =?= funpow weirdest-id n r                   by quarantine-rewrite hwid
      =?= r                                        by quarantine-rewrite IH
qed

theorem weirdest-id-spec :
  forall x : Nat, weirdest-id x =?= x
proof
  pick-any x : Nat
  induction x with
  | zero =>
    chaining
      =?= weirdest-id zero
      =?= zero              by step
  | succ (n & ind (IH : weirdest-id n =?= n)) =>
    chaining
      =?= weirdest-id (succ n)
      =?= succ (funpow weirdest-id n n)                   by step
      =?= succ n                                          by quarantine-rewrite (funpow-weirdest-id n IH n)
qed

totality weirdest-id
proof
  proving forall n : Nat, exists r : Nat, weirdest-id n =?= r
  pick-any n
  witness n
  instantiate weirdest-id-spec with n
qed

search (p : Nat -> Bool) (n : Nat) : Nat =
  if p n then n else search p (succ n)

// It's not hard to have some flavour of functional induction...
// but it's hard to have a clever one that isn't just generating
// all the cases under the hood.
// Fixed point induction doesn't seem to be helpful here.
theorem search-aux :
  forall (p : Nat -> Bool) (n r : Nat),
    search p n =?= r --> p r === true
proof                                  // |- forall (p : Nat -> Bool) (n r : Nat), search p n =?= r --> p r === true
  pick-any p n r                       // p : Nat -> Bool, n r : Nat |- search p n =?= r --> p r === true
  assume heq                           // p : Nat -> Bool, n r : Nat, heq : search p n =?= r |- p r === true
  functional induction heq
                                       // p : Nat -> Bool, n r : Nat, heq : n =?= r |- p n === true --> p r === true
  . assume hpn                         // p : Nat -> Bool, n r : Nat, heq : n =?= r, hpn : p n === true |- p r === true
    totalize                           // ... |- p r =?= true
    chaining
      =?= p r
      =?= p n             by quarantine-rewrite heq
      =?= true            by rewrite hpn
                                       // p : Nat -> Bool, n r : Nat, heq : search p (succ n) =?= r |- p n === false --> p r === true --> p r === true
  . assume hpn hpr                     // p : Nat -> Bool, n r : Nat, heq : search p (succ n) =?= r, hpn : p n === false hpr : p r === true |- p r === true
    assumption                         // Theorem proved!
qed

theorem search-concrete :
  forall (p : Nat -> Bool) (n r : Nat),
    search p n =?= r --> exists k : Nat, r === add k n
proof
  pick-any p n r
  assume heq                           // p : Nat -> Bool, n r : Nat, heq : search p n =?= r |- exists k : Nat, r === add k n
  functional induction heq
                                       // p : Nat -> Bool, n r : Nat, heq : n =?= r |- p n === true --> exists k : Nat, r === add k n
  . assume hpn                         // p : Nat -> Bool, n r : Nat, heq : n =?= r, hpn : p n === true |- exists k : Nat, r === add k n
    witness zero                       // p : Nat -> Bool, n r : Nat, heq : n =?= r, hpn : p n === true |- r === add zero n
    simpl                              // p : Nat -> Bool, n r : Nat, heq : n =?= r, hpn : p n === true |- r === n
    totalize                           // p : Nat -> Bool, n r : Nat, heq : n =?= r, hpn : p n === true |- r =?= n
    quarantine-rewrite heq
    prefl
                                       // p : Nat -> Bool, n r : Nat, heq : n =?= r
                                       // |- p n === false --> (exists k : Nat, r === add k (succ n)) --> exists k : Nat, r === add k n
  . assume hpn (witness k such-that IH)// ..., hpn : p n === false, k : Nat, IH : r === add k (succ n) |- exists k : Nat, r === add k n
    witness (succ k)                   // ... |- r === add (succ k) n
    totalize                           // ... |- r =?= add (succ k) n
    quarantine-rewrite IH              // ... |- add k (succ n) =?= add (succ k) n
    // At this point, it's just arithmetic.
qed

// (forall r : Nat, ~ search p n =?= r) --> forall k : Nat, p (add k n) === false
// (exists k : Nat, p (add k n) === true) --> exists r : Nat, search p n =?= r

theorem search-aux :
  forall p : Nat -> Bool,
    (forall n : Nat, exists k : Nat, p (add k n) === true) -->
    forall n : Nat, exists r : Nat, search p n =?= r
proof
  pick-any p
  assume eventually-p
  pick-any n                           // p : Nat -> Bool, eventually-p : (forall n : Nat, exists k : Nat, p (add k n) === true), n : Nat
                                       // |- exists r : Nat, search p n =?= r
  suffices ~ forall r : Nat, ~ search p n =?= r by
    // TODO

  assume diverges : forall r : Nat, ~ search p n =?= r
  proving False

  pick-witness k (h : p (add k n) === true) for eventually-p n
  apply diverges (add n k)

  proving search p n =?= add n k

qed