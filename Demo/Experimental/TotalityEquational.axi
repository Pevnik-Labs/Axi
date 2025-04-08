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

theorem bad-diverges :
  forall (x : Unit) (b : Bool), ~ bad x =?= b
proof                                  // |- forall (x : Unit) (b : Bool), ~ bad x =?= b
  pick-any x b                         // x : Unit, b : Bool |- ~ bad x =?= b
  assume heq                           // x : Unit, b : Bool, heq : bad x =?= b |- False
  suffices b === notb b by
    // TODO
                                       // x : Unit, b : Bool, heq : bad x =?= b |- b === notb b
  totalize                             // x : Unit, b : Bool, heq : bad x =?= b, hb : b === true |- b =?= notb b
  chaining
    =?= b
    =?= bad x        by quarantine-rewrite <- heq
    =?= notb (bad x) by step
    =?= notb b        by quarantine-rewrite heq
qed