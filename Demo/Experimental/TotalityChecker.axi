// Totality checker steps in when:
// - Defining a function by pattern matching or recursion.
// - Proving by induction.

// The totality checker for function definitions has two modes:
// (RSC) A syntactic check (coverage check for pattern matching, a check for structural recursion).
// (RTP) A totality proof.

// The totality checker for proof by induction has three modes:
// (ISC) A syntactic check (coverage check for cases, a check for structural induction).
// (IWF) Well-founded induction as a basic principle of the system (or not, it's provable using classical logic).
// (IFI) Functional induction as a basic principle of the system
//       (only when the corresponding function was proved total).

data Nat where
  zero
  succ : Nat -> Nat

// The simplest flavour of structural recursion,
// accepted because of a syntactic check (RSC).
idNat1 : Nat -> Nat
| zero => zero
| succ n => succ (idNat1 n)

// Structural recursion (deep),
// accepted because of a syntactic check (RSC).
idNat2 : Nat -> Nat
| zero => zero
| succ zero => succ zero
| succ (succ n) => succ (succ (idNat2 n))

// Structural recursion (deep, a bit more complicated),
// accepted because of a syntactic check (RSC).
idNat3 : Nat -> Nat
| zero => zero
| succ zero => succ zero
| succ (succ n) => succ (idNat3 (succ n))

// Higher-order recursive call, but structural (RSC).
transform (n : Nat) (f : Nat -> Nat) : Nat =
  match n with
  | zero => f zero
  | succ n' => transform n' (\ x -> f (transform n' (\ y -> f (x + y))))

// Fails the syntactic check.
weird-id : Nat -> Nat
| zero => zero
| succ n => succ (weird-id (weird-id n))
// WARNING: Cannot establish the totality of `weird-id` with a syntactic check.

data weird-id-graph : Nat -> Nat -> Prop where
  w-id-zero : weird-id-graph zero zero
  w-id-succ : forall n r2 : Nat, (exists r1 : Nat, weird-id-graph n r1 /\ weird-id-graph r1 r2) --> weird-id-graph (succ n) (succ r2)

data (| weird-id |) : Nat -> Nat -> Prop where
  dequarantine-zero : (| weird-id |) zero zero
  dequarantine-succ : forall n r2 : Nat, (exists r1 : Nat, (| weird-id |) n r1 /\ (| weird-id |) r1 r2) --> (| weird-id |) (succ n) (succ r2)

data (| weird-id |) : Nat -> Nat -> Prop where
  dequarantine-zero : (| weird-id |) zero zero
  dequarantine-succ : forall n r2 : Nat, (| weird-id (weird-id n) |) r2 --> (| weird-id |) (succ n) (succ r2)

// At this point, it's illegal to state theorems about `weird-id` because it is
// not known to be total.
theorem weird-id-spec :
  forall n : Nat, weird-id n === n
// ERROR: Prove termination of `weird-id` before reasoning about it.

// [| . |] : Type -> LogicalKind
// [| A -> B |] = A -> [| B |]
// [| X |] = X -> Prop

// t : A (possibly lacking coverage, termination or totality in some way)
// ----------------------------------------------------------------------
// (| t |) : [| A |]

// t : A (t is total)
// ------------------------
// dequarantine {t} : (| t |) t

// Beware: for now `dequarantine` also acts as a congruence

// f : A -> B   t1 : A   t2 : A   e : (| t1 |) t2
// ----------------------------------------------
// dequarantine e : (| f t1 |) (f t2)

// t1 : A   t2 : A   (| t1 |) t2   t1 total
// ----------------------------------------
// quarantine e : t1 === t2

// t1 : A (t1 total)   t2 : A   e : t1 === t2
// ------------------------------------------
// dequarantine' e : (| t1 |) t2

// Now it's legal to state theorems about the graph of `weird-id`.
theorem weird-id-aux :
  forall x : Nat, (| weird-id |) x x
proof                                  // |- forall x : Nat, (| weird-id |) x x
  pick-any x                           // x : Nat |- (| weird-id |) x x
  devour                               // x : Nat |- (| weird-id x |) x
  induction x with                     // Termination by syntactic check (ISC).
  | zero =>                            // x : Nat |- (| weird-id zero |) zero
    // There's a pattern matching branch in the definition of `weird-id` that says `weird-id zero` computes to `zero`.
    step                               // x : Nat |- (| zero |) zero
    dequarantine                       // Goal solved!
  | succ (n & ind IH) =>               // x : Nat, n : Nat, IH : (| weird-id n |) n |- (| weird-id (succ n) |) (succ n)
    step                               // x : Nat, n : Nat, IH : (| weird-id n |) n |- (| succ (weird-id (weird-id n)) |) (succ n)
    // In fact, `dequarantine` is not a finisher, but applies a kind of congruence.
    dequarantine                       // x : Nat, n : Nat, IH : (| weird-id n |) n |- (| weird-id (weird-id n) |) n
    // `undevour` pushes a part of the quarantine into a separate top-level quarantine.
    undevour (weird-id n)              // x : Nat, n : Nat, IH : (| weird-id n |) n |- exists r : Nat, (| weird-id n |) r /\ (| weird-id r |) n
    witness n                          // x : Nat, n : Nat, IH : (| weird-id n |) n |- (| weird-id n |) n /\ (| weird-id n |) n
    both IH IH                         // Theorem proved!
qed

// Proving totality of `weird-id` (RTP).
// Note an amusing fact: even though this function is not structurally
// recursive, its totality was proven using structural induction
// (in the previous lemma, that is).
totality weird-id
proof                                  // |- forall n : Nat, exists r : Nat, (| weird-id |) n r
  pick-any n : Nat                     // n : Nat |- exists r : Nat, (| weird-id |) n r
  witness n                            // n : Nat |- (| weird-id |) n n
  instantiate weird-id-aux with n      // Theorem proved!
qed

// Now it's legal to state theorems about `weird-id`.
// Moreover, we don't need to reprove the theorem below from scratch.
// We can use the lemma about the graph that we already proved.
theorem weird-id-spec :
  forall n : Nat, weird-id n === n
proof                                  // |- forall n : Nat, weird-id n === n
  pick-any n                           // n : Nat |- weird-id n === n
  quarantine                           // n : Nat |- (| weird-id n |) n
  instantiate weird-id-aux with n      // Theorem proved!
qed

// We should be able to prove that the graph of `weird-id` is deterministic.
theorem weird-id-det :
  forall x r1 r2 : Nat,
    (| weird-id x |) r1 --> (| weird-id x |) r2 --> r1 === r2
proof
  pick-any x : Nat
  induction x with
  | zero =>
    pick-any r1 r2
    assume nr1 nr2                     // x r1 r2 : Nat, nr1 : (| weird-id zero |) r1, nr2 : (| weird-id zero |) r2 |- r1 === r2
    step at nr1
    step at nr2                        // x r1 r2 : Nat, nr1 : (| zero |) r1, nr2 : (| zero |) r2 |- r1 === r2
                                       // x r1 r2 : Nat, nr1 : (| zero |) r1, nr2 : (| zero |) r2, nr1' : zero === r1, nr2' : zero === r2 |- r1 === r2
    chaining
      === r1
      === zero  by rewrite <- (quarantine nr1)
      === r2    by rewrite (quarantine nr2)
  | succ (n & ind IH) =>
    pick-any r1 r2
    assume nr1 nr2                     // x r1 r2 n : Nat, IH : forall r1 r2, (| weird-id n |) r1 --> (| weird-id n |) r2 --> r1 == r2,
                                       // nr1 : (| weird-id (succ n) |) r1, nr2 : (| weird-id (succ n) |) r2 |- r1 === r2
    step at nr1
    step at nr2                        // x r1 r2 n : Nat, nr1 : (| succ (weird-id (weird-id n)) |) r1, nr2 : (| succ (weird-id (weird-id n)) |) r2 |- r1 === r2
    quarantine                         // x r1 r2 n : Nat, nr1 : (| succ (weird-id (weird-id n)) |) r1, nr2 : (| succ (weird-id (weird-id n)) |) r2 |- (| r1 |) r2
qed

weird-zero : Nat -> Nat
| zero => zero
| succ n => weird-zero (weird-zero n)
// WARNING: Cannot establish the totality of `weird-zero` with a syntactic check.

theorem weird-zero-aux :
  forall x : Nat, (| weird-zero |) x zero
proof                                  // |- forall x : Nat, (| weird-zero |) x zero
  pick-any x                           // x : Nat |- (| weird-zero |) x zero
  devour                               // x : Nat |- (| weird-zero x |) zero
  induction x with                     // Termination by syntactic check (ISC).
  | zero =>                            // x : Nat |- (| weird-zero zero |) zero
    step                               // x : Nat |- (| zero |) zero
    dequarantine                       // Goal solved!
  | succ (n & ind IH) =>               // x : Nat, n : Nat, IH : (| weird-zero n |) zero |- (| weird-zero (succ n) |) zero
    step                               // x : Nat, n : Nat, IH : (| weird-zero n |) zero |- (| weird-zero (weird-zero n) |) zero

    undevour (weird-zero n)            // x : Nat, n : Nat, IH : (| weird-zero n |) zero |- exists r : Nat, (| weird-zero n |) r /\ (| weird-zero r |) zero
    witness zero                       // x : Nat, n : Nat, IH : (| weird-zero n |) zero |- (| weird-zero n |) zero /\ (| weird-zero zero |) zero
    both IH                            // x : Nat, n : Nat, IH : (| weird-zero n |) zero |- (| weird-zero zero |) zero
    step                               // x : Nat, n : Nat, IH : (| weird-zero n |) zero |- (| zero |) zero
    dequarantine                       // Theorem proved!
qed

totality weird-zero
proof                                  // |- forall n : Nat, exists r : Nat, (| weird-zero |) n r
  pick-any n : Nat                     // n : Nat |- exists r : Nat, (| weird-zero |) n r
  instantiate weird-zero-aux with n    // Theorem proved!
qed

data Unit where
  unit

loop (x : Unit) : Unit = loop x
// WARNING: Cannot establish the totality of `loop` with a syntactic check.

// The function is not total, so the proof should always fail.
fail totality loop
proof                                  // |- forall x : Unit, exists r : Unit, (| loop |) x r
  pick-any x                           // x : Unit |- exists r : Unit, (| loop |) x r
  witness unit                         // x : Unit |- (| loop |) x unit
  devour                               // x : Unit |- (| loop x |) unit
  step                                 // x : Unit |- (| loop x |) unit
  // Nothing can be done at this point.
  cases x with
  | unit =>                            // x : Unit |- (| loop unit |) unit
  // Still nothing to do...
qed

missing-case-ok (n : Nat) : Nat =
  match succ n with
  | succ n' => n'
// WARNING: Cannot establish the totality of `missing-case` with a syntactic check.

// The function is total, so we succeed.
totality missing-case-ok
proof                                  // |- forall n : Nat, exists r : Nat, (| missing-case-ok |) n r
  pick-any n : Nat                     // n : Nat |- exists r : Nat, (| missing-case-ok |) n r
  witness n                            // n : Nat |- (| missing-case-ok |) n n
  devour                               // n : Nat |- (| missing-case-ok n |) n
  step                                 // n : Nat |- (| n |) n
  dequarantine                         // Theorem proved!
qed

missing-case-bad : Nat -> Nat
| succ n => succ n
// WARNING: Missing case: `zero`.

// The function is not total, so the proof fails no matter what we do.
fail totality missing-case-bad
proof                                  // |- forall x : Nat, exists r : Nat, (| missing-case-bad |) x r
  pick-any x                           // x : Nat |- exists r : Nat, (| missing-case-bad |) x r
  devour                               // x : Nat |- exists r : Nat, (| missing-case-bad x |) r
  cases x with
  | succ n' =>                         // x : Nat, n : Nat |- exists r : Nat, (| missing-case-bad (succ n) |) r
    witness succ n'                    // x : Nat, n : Nat |- (| missing-case-bad (succ n) |) (succ n)
    step                               // x : Nat, n : Nat |- (| succ n |) (succ n)
    dequarantine                       // Goal solved!
  | zero =>                            // x : Nat |- exists r : Nat, (| missing-case-bad zero |) r
    step                               // x : Nat |- exists r : Nat, False
    // Nothing can be done at this point.
qed

theorem missing-case-bad-contra :
  forall r : Nat, ~ (| missing-case-bad zero |) r
proof                                  // |- forall r : Nat, ~ (| missing-case-bad zero |) r
  pick-any r                           // r : Nat |- ~ (| missing-case-bad zero |) r
  assume contra                        // r : Nat, contra : (| missing-case-bad zero |) r |- False
  step at contra                       // r : Nat, contra : False |- False
  assumption
qed

// RSC
sub (n : Nat) : Nat -> Nat
| zero => n
| succ m => pred (sub n m)

// A modified Hofstadter H function.
hof : Nat -> Nat
| zero => zero
| succ n => sub n (hof (hof n))
// WARNING: Cannot establish the totality of `hof` with a syntactic check.

// The function is total, but the proof won't go through by structural induction.
fail totality hof
proof                        // |- forall x : Nat, exists r : Nat, (| hof |) x r
  pick-any x                 // x : Nat |- exists r : Nat, (| hof |) x r
  devour                     // x : Nat |- exists r : Nat, (| hof x |) r
  induction x with           // Termination by syntactic check (ISC).
  | zero =>                  // x : Nat |- exists r : Nat, (| hof zero |) r
    witness zero             // x : Nat |- exists r : Nat, (| hof zero |) zero
    step                     // x : Nat |- exists r : Nat, (| zero |) zero
    dequarantine             // Goal solved!
  | succ (n & ind (witness rn such-that IH)) =>
                             // x : Nat, n : Nat, rn : Nat, IH : (| hof n |) rn |- exists r : Nat, (| hof (succ n) |) r
    step                     // x : Nat, n : Nat, rn : Nat, IH : (| hof n |) rn |- exists r : Nat, (| sub n (hof (hof n)) |) r
    undevour (hof n)         // x : Nat, n : Nat, rn : Nat, IH : (| hof n |) rn |- exists rr, (| hof n |) rr /\ exists r : Nat, (| sub n (hof rr) |) r
    witness rn               // x : Nat, n : Nat, rn : Nat, IH : (| hof n |) rn |- (| hof n |) rn /\ exists r : Nat, (| sub n (hof rn) |) r
    both IH                  // x : Nat, n : Nat, rn : Nat, IH : (| hof n |) rn |- exists r : Nat, (| sub n (hof rn) |) r
    undevour (hof rn)        // x : Nat, n : Nat, rn : Nat, IH : (| hof n |) rn |- exists rr : Nat, (| hof rn |) rr /\ exists r : Nat, (| sub n rr |) r
    // Now we're stuck.
qed

data FreeMon A where
  e  : FreeMon A
  i  : A -> FreeMon A
  op : FreeMon A -> FreeMon A -> FreeMon A

norm {A} : FreeMon A -> FreeMon A
| e => e
| i a => op (i a) e
| op l r =>
  match norm l with
  | e => norm r
  //| i a => op (i a) (norm r)
  | op l1 l2 => op l1 (norm (op l2 r))
// WARNING: Cannot establish the totality of `norm` with a syntactic check.

// The function is total, but the proof won't go through by structural induction.
fail totality norm
proof                                  // |- forall {A} (x : FreeMon A), exists res : FreeMon A, (| norm |) x res
  pick-any A x                         // A : Type, x : FreeMon A |- exists res : FreeMon A, (| norm |) x res
  devour                               // A : Type, x : FreeMon A |- exists res : FreeMon A, (| norm x |) res
  induction x with                     // Termination by syntactic check (ISC).
  | e =>                               // A : Type, x : FreeMon A |- exists res : FreeMon A, (| norm e |) res
    witness e                          // A : Type, x : FreeMon A |- (| norm e |) e
    step                               // A : Type, x : FreeMon A |- (| e |) e
    dequarantine                       // Goal solved!
  | i a =>                             // A : Type, x : FreeMon A, a : A |- exists res : FreeMon A, (| norm (i a) |) res
    witness op (i a) e                 // A : Type, x : FreeMon A, a : A |- (| norm (i a) |) (op (i a) e)
    step                               // A : Type, x : FreeMon A, a : A |- (| op (i a) e |) (op (i a) e)
    dequarantine                       // Goal solved!
  | op (l & ind (witness res-l such-that IHl)) (r & ind (witness res-r such-that IHr)) =>
                                       // A : Type, x l r res-l res-r : FreeMon A, IHl : (| norm l |) res-l), IHr : (| norm r |) res-r |- exists res : FreeMon A, (| norm (op l r) |) res
    step                               // ... |- exists res, (| match norm l with | e => norm r | op l1 l2 => op l1 (norm (op l2 r)) |) res
    undevour (norm l)                  // ... |- exists res-l, (| norm l |) res-l /\ exists res, (| match res-l with | e => norm r | op l1 l2 => op l1 (norm (op l2 r)) |) res
    witness res-l                      // ... |- (| norm l |) res-l /\ exists res, (| match res-l with | e => norm r | op l1 l2 => op l1 (norm (op l2 r)) |) res
    both IHl'                          // ... |- exists res, (| match res-l with | e => norm r | op l1 l2 => op l1 (norm (op l2 r)) |) res
    cases res-l with
    | e =>                             // ... |- exists res, (| match e with | e => norm r | op l1 l2 => op l1 (norm (op l2 r)) |) res
      step                             // ... |- exists res, (| norm r |) res
      witness res-r                    // ... |- (| norm r |) res-r
      assumption                       // Goal solved!
    | i a =>                           // ... |- exists res, (| match i a with | e => norm r | op l1 l2 => op l1 (norm (op l2 r)) |) res
      step                             // ... |- exists res, False
      lemma contra : ~ (| norm l |) (i a) by
        // TODO
      absurd
      contradiction contra IHl
    | op l1 l2 =>                      // ... |- exists res, (| match op l1 l2 with | e => norm r | op l1 l2 => op l1 (norm (op l2 r)) |) res
      step                             // ... |- exists res, (| op l1 (norm (op l2 r)) |) res
      undevour (norm (op l2 r))        // ... |- exists res', (| norm (op l2 r) |) res' /\ exists res, (| op l1 res' |) res
      // At this point we can see that it won't go through by structural induction, as expected.
      // The style of quarantine wtih `devour`, `undevour` and `step` seems useful, however.
qed

silly (b : Bool) : Bool =
  if b then true else silly true
// WARNING: Cannot establish the totality of `silly` with a syntactic check.

// The function is total.
totality silly
proof                                  // |- forall b : Bool, exists r : Bool, (| silly |) b r
  pick-any b                           // b : Bool |- exists r : Bool, (| silly |) b r
  witness true                         // b : Bool |- (| silly |) b true
  devour                               // b : Bool |- (| silly b |) true
  cases b with
  | true =>                            // b : Bool |- (| silly true |) true
    step                               // b : Bool |- (| true |) true
    dequarantine                       // Goal solved!
  | false =>                           // b : Bool |- (| silly false |) true
    step                               // b : Bool |- (| silly true |) true
    step                               // b : Bool |- (| true |) true
    dequarantine                       // Theorem proved!
qed

even : Nat -> Bool
| zero => true
| succ n => notb (even n)

search (n : Nat) : Nat =
  if even n then n else search (succ n)
// WARNING: Cannot establish the totality of `search` with a syntactic check.

// Proving `search` total isn't very hard.
totality search
proof                                  // |- forall n : Nat, exists r : Nat, (| search |) n r
  pick-any n                           // n : Nat |- exists r : Nat, (| search |) n r
  devour                               // n : Nat |- exists r : Nat, (| search n |) r
  step                                 // n : Nat |- exists r : Nat, (| if even n then n else search (succ n) |) r
  cases even n with
  | true =>                            // n : Nat |- exists r : Nat, (| if true then n else search (succ n) |) r
    witness n                          // n : Nat |- (| if true then n else search (succ n) |) n
    step                               // n : Nat |- (| n |) n
    dequarantine                       // Goal solved!
  | false & eqn odd-n =>               // n : Nat, odd-n : even n === false |- exists r : Nat, (| if false then n else search (succ n) |) r
    // We need to give ourselves an equation `even n === false` for rewriting later.
    witness succ n                     // n : Nat, odd-n : even n === false |- (| if false then n else search (succ n) |) (succ n)
    step                               // n : Nat, odd-n : even n === false |- (| search (succ n) |) (succ n)
    step                               // n : Nat, odd-n : even n === false |- (| if notb (even n) then succ n else search (succ (succ n)) |) (succ n)
    rewrite odd-n                      // n : Nat, odd-n : even n === false |- (| if notb false then succ n else search (succ (succ n)) |) (succ n)
    step                               // n : Nat, odd-n : even n === false |- (| succ n |) (succ n)
    dequarantine                       // Theorem proved!
qed

data List A where
  nil
  cons : A -> List A -> List A

interleave {A} (l1 l2 : List A) : List A =
  match l1 with
  | nil => l2
  | cons h t => cons h (interleave l2 t)
// WARNING: Cannot establish the totality of `interleave` with a syntactic check.

// We can prove totality by structural induction, because we could just as well
// have defined this function with structural recursion...
totality interleave
proof                                  // |- forall {A} (l1 l2 : List A), exists r : List A, (| interleave |) l1 l2 r
  pick-any A l1                        // A : Type, l1 : List A |- forall l2 : List A, exists r : List A, (| interleave |) l1 l2 r
  devour                               // A : Type, l1 : List A |- forall l2 : List A, exists r : List A, (| interleave l1 |) l2 r
  devour                               // A : Type, l1 : List A |- forall l2 : List A, exists r : List A, (| interleave l1 l2 |) r
  induction l1 with                    // Termination by syntactic check (ISC).
  | nil =>                             // A : Type, l1 : List A |- forall l2 : List A, exists r : List A, (| interleave nil l2 |) r
    pick-any l2                        // A : Type, l1 l2 : List A |- exists r : List A, (| interleave nil l2 |) r
    witness l2                         // A : Type, l1 l2 : List A |- (| interleave nil l2 |) l2
    step                               // A : Type, l1 l2 : List A |- (| l2 |) l2
    dequarantine                       // Goal solved!
  | cons h1 (t1 & ind IH) =>           // A : Type, l1 : List A, IH : forall l2, exists r, (| interleave t1 l2 |) r |- forall l2, exists r, (| interleave (cons h1 t1) l2 |) r
    pick-any l2                        // A : Type, l1 : List A, IH : forall l2, exists r, (| interleave t1 l2 |) r, l2 : List A |- exists r, (| interleave (cons h1 t1) l2 |) r
    cases l2 with
    | nil =>                           // A : Type, l1 : List A, IH : forall l2, exists r, (| interleave t1 l2 |) r, l2 : List A |- exists r, (| interleave (cons h1 t1) nil |) r
      witness cons h1 t1               // A : Type, l1 : List A, IH : forall l2, exists r, (| interleave t1 l2 |) r, l2 : List A |- (| interleave (cons h1 t1) nil |) (cons h1 t1)
      step                             // A : Type, l1 : List A, IH : forall l2, exists r, (| interleave t1 l2 |) r, l2 : List A |- (| cons h1 (interleave nil t1) |) (cons h1 t1)
      dequarantine                     // A : Type, l1 : List A, IH : forall l2, exists r, (| interleave t1 l2 |) r, l2 : List A |- (| interleave nil t1 |) t1
      step                             // A : Type, l1 : List A, IH : forall l2, exists r, (| interleave t1 l2 |) r, l2 : List A |- (| t1 |) t1
      dequarantine                     // Goal solved!
    | cons h2 t2 =>                    // A : Type, l1 : List A, IH : forall l2, exists r, (| interleave t1 l2 |) r, l2 : List A |- exists r, (| interleave (cons h1 t1) (cons h2 t2) |) r
      pick-witness r IH' for IH t2     // A : Type, l1 : List A, IH : forall l2, exists r, (| interleave t1 l2 |) r, l2 r : List A, IH' : (| interleave t1 t2 |) r
                                       // |- exists r, (| interleave (cons h1 t1) (cons h2 t2) |) r
      witness cons h1 (cons h2 r)      // ... |- (| interleave (cons h1 t1) (cons h2 t2) |) (cons h1 (cons h2 r))
      step                             // ... |- (| cons h1 (interleave (cons h2 t2) t1) |) (cons h1 (cons h2 r))
      dequarantine                     // ... |- (| interleave (cons h2 t2) t1 |) (cons h2 r)
      step                             // ... |- (| cons h2 (interleave t1 t2) |) r
      assumption
qed

// Termination by syntactic check (RSC).
interleave' {A} : List A -> List A -> List A
| nil, l2 => l2
| l1, nil => l1
| cons h1 t1, cons h2 t2 => cons h1 (cons h2 (interleave' t1 t2))

// Another proof, using `interleave'`.
totality interleave
proof                                  // |- forall {A} (l1 l2 : List A), exists r : List A, (| interleave |) l1 l2 r
  pick-any A l1 l2                     // A : Type, l1 l2 : List A |- exists r : List A, (| interleave |) l1 l2 r
  devour                               // A : Type, l1 l2 : List A |- exists r : List A, (| interleave l1 |) l2 r
  devour                               // A : Type, l1 l2 : List A |- exists r : List A, (| interleave l1 l2 |) r
  witness (interleave' l1 l2)          // A : Type, l1 l2 : List A |- (| interleave l1 l2 |) (interleave' l1 l2)
  induction l1 with                    // Termination by syntactic check (ISC).
  | nil =>                             // A : Type, l1 l2 : List A |- (| interleave nil l2 |) (interleave' nil l2)
    step                               // A : Type, l1 l2 : List A |- (| l2 |) (interleave' nil l2)
    simpl                              // A : Type, l1 l2 : List A |- (| l2 |) l2
    dequarantine                       // Goal solved!
  | cons h1 (t1 & ind IH) =>           // A : Type, l1 l2 : List A, IH : forall l2, (| interleave t1 l2 |) (interleave' t1 l2)
                                       // |- (| interleave (cons h1 t1) l2 |) (interleave' (cons h1 t1) l2)
    cases l2 with
    | nil =>                           // ... |- (| interleave (cons h1 t1) nil |) (interleave' (cons h1 t1) nil)
      step                             // ... |- (| cons h1 (interleave nil t1) |) (interleave' (cons h1 t1) nil)
      step                             // ... |- (| cons h1 t1 |) (interleave' (cons h1 t1) nil)
      simpl                            // ... |- (| cons h1 t1 |) (cons h1 t1)
      dequarantine                     // Goal solved!
    | cons h2 t2 =>                    // ..., h2 : A, t2 : List A |- (| interleave (cons h1 t1) (cons h2 t2) |) (interleave' (cons h1 t1) (cons h2 t2))
      step                             // ... |- (| cons h1 (interleave (cons h2 t2) t1) |) (interleave' (cons h1 t1) (cons h2 t2))
      step                             // ... |- (| cons h1 (cons h2 (interleave t1 t2)) |) (interleave' (cons h1 t1) (cons h2 t2))
      simpl                            // ... |- (| cons h1 (cons h2 (interleave t1 t2)) |) (cons h1 (cons h2 (interleave' t1 t2)))
      dequarantine                     // ... |- (| interleave t1 t2 |) (interleave' t1 t2)
      instantiate IH with t2
qed

data Z where
  z
  s : Z -> Z
  p : Z -> Z

// This is structurally recursive (RSC).
norm : Z -> Z
| z => z
| s k =>
  match norm k with
  | p k' => k'
  | k' => s k'
| p k =>
  match norm k with
  | s k' => k'
  | k' => p k'

data Tree A where
  node : A -> List (Tree A) -> Tree A

tmap {A B} (f : A -> B) : Tree A -> Tree B
| node x ts => node (f x) (map (tmap f) ts)
// WARNING: Cannot establish the totality of `tmap` with a syntactic check.

forall-list {A} (P : A -> Prop) : List A -> Prop
| nil => True
| cons h t => P h /\ forall-list P t

theorem list-ind-deep :
  forall {A} (P : A -> Prop) (Q : List A -> Prop),
    Q nil -->
    (forall (h : A) (t : List A), P h --> Q t --> Q (cons h t)) -->
    forall l : List A, forall-list P l --> Q l
proof
  pick-any A P Q
  assume qn qc
  pick-any l
  assume allp
  // Let Γ = A : Type, P : A -> Prop, Q : List A -> Prop, qn : Q nil, qc : (forall (h : A) (t : List A), P h --> Q t --> Q (cons h t)), l : List A, allp : forall-list P l
  induction l with                     // Termination by syntactic check (ISC).
  | nil =>                             // Γ |- Q nil
    assumption                         // Goal solved!
  | cons h (t & ind IH) =>             // Γ, h : A, t : List A, IH : Q t |- Q (cons h t)
    apply qc h t
                                       // Γ, h : A, t : List A, IH : Q t |- P h
    . and-left allp                    // Goal solved!
                                       // Γ, h : A, t : List A, IH : Q t |- Q t
    . IH                               // Theorem proved!
qed

theorem tmap-aux :
  forall {A B} (f : A -> B) (ts : List (Tree A)),
    forall-list (\t -> exists r : Tree B, (| tmap f t |) r) ts -->
      exists rs : List (Tree B), (| map (tmap f) ts |) rs
proof
  pick-any A B f
  // Let Γ = A B : Type, f : A -> B
  apply list-ind-deep {A} (\t -> exists r : Tree B, (| tmap f t |) r) (\ts -> exists rs : List (Tree B), (| map (tmap f) ts |) rs)
                                       // A B : Type, f : A -> B |- exists rs : List (Tree B), (| map (tmap f) nil |) rs
  . step                               // A B : Type, f : A -> B |- exists rs : List (Tree B), (| nil |) rs
    witness nil                        // A B : Type, f : A -> B |- (| nil |) nil
    dequarantine                       // Goal solved!
                                       // A B : Type, f : A -> B |- forall (t : Tree A) (ts : List (Tree A)), (exists r : Tree B, (| tmap f t |) r) --> (exists rs : List (Tree B), (| map (tmap f) ts |) rs) --> exists rs : List (Tree B), (| map (tmap f) (cons t ts) |) rs
  . pick-any t ts                      // A B : Type, f : A -> B, t : Tree A, ts : List (Tree A)
                                       // |- (exists r : Tree B, (| tmap f t |) r) --> (exists rs : List (Tree B), (| map (tmap f) ts |) rs) --> exists rs : List (Tree B), (| map (tmap f) (cons t ts) |) rs
    assume (witness rt such-that IHt) (witness rts such-that IHts)
                                       // A B : Type, f : A -> B, t : Tree A, ts : List (Tree A), rt : Tree B, IHt : (| tmap f t |) rt, rts : List (Tree B), IHts : (| map (tmap f) ts |) rts |- exists rs : List (Tree B), (| map (tmap f) (cons t ts) |) rs
    witness (cons rt rts)              // ... |- (| map (tmap f) (cons t ts) |) (cons rt rts)
    step                               // ... |- (| cons (tmap f t) (map (tmap f) ts) |) (cons rt rts)
    dequarantine
                                       // ... |- (| tmap f t |) rt
    . IHt
                                       // ... |- (| map (tmap f) ts |) rts
    . IHts
qed

theorem Tree-ind-deep :
  forall {A} (P : A -> Prop) (Q : Tree A -> Prop),
    (forall (x : A) (ts : List (Tree A)), P x --> forall-list Q ts --> Q (node x ts)) -->
      forall t : Tree A, Q t
proof
  pick-any A P Q
  assume all
  pick-any t
qed

totality tmap
proof                                  // |- forall {A B} (f : A -> B) (t : Tree A), exists r : Tree B, (| tmap f |) t r
  pick-any A B f t                     // A B : Type, f : A -> B, t : Tree A |- exists r : Tree B, (| tmap f |) t r
  devour                               // A B : Type, f : A -> B, t : Tree A |- exists r : Tree B, (| tmap f t |) r
  cases t with
  | node x ts =>                       // A B : Type, f : A -> B, t : Tree A, x : A, ts : List (Tree A) |- exists r : Tree B, (| tmap f (node x ts) |) r
    suffices exists rs : List (Tree B), (| map (tmap f) ts |) rs
      assume (witness rs such-that h)
                                        // A B : Type, f : A -> B, t : Tree A, x : A, ts : List (Tree A), rs : List (Tree B), h : (| map (tmap f) ts |) rs |- exists r : Tree B, (| tmap f (node x ts) |) r
      witness node (f x) rs              // ... |- (| tmap f (node x ts) |) (node (f x) rs)
      step                               // ... |- (| node (f x) (map (tmap f) ts) |) (node (f x) rs)
      dequarantine                       // ... |- (| map (tmap f) ts |) rs
      assumption                         // Goal solved!
                                         // A B : Type, f : A -> B, t : Tree A, x : A, ts : List (Tree A) |- exists rs : List (Tree B), (| map (tmap f) ts |) rs
    apply tmap-aux                       // ... |- forall-list (\t -> exists r : Tree B, (| tmap f t |) r) ts
    induction ts with                    // Termination by syntactic check (ISC).
    | nil =>                             // ... |- forall-list (\t -> exists r : Tree B, (| tmap f t |) r) nil
      simpl                              // ... |- True
      trivial                            // Goal solved!
    | cons 
qed

data RoseTree A where
  empty : A -> RoseTree A
  node  : List (RoseTree A) -> RoseTree A

data Bush A where
  nil  : Bush A
  cons : A -> Bush (Bush A) -> Bush A

cons 5 (cons (cons 5 nil) nil) : Bush Nat

bushmap {A B} (f : A -> B) : Bush A -> Bush B
| nil => nil
| cons h t => cons (f h) (bushmap (bushmap f) t)

data Queue A where
  nil  : Queue A
  cons : Option A -> Queue (Prod A A) -> Queue A