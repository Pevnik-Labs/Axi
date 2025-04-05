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

// Structural recursion (nested),
// accepted because of a syntactic check (RSC).
idNat2 : Nat -> Nat
| zero => zero
| succ zero => succ zero
| succ (succ n) => succ (succ (idNat2 n))

// Structural recursion (nested, a bit more complicated),
// accepted because of a syntactic check (RSC).
idNat3 : Nat -> Nat
| zero => zero
| succ zero => succ zero
| succ (succ n) => succ (idNat3 (succ n))

// Higher-order recursive call, but structural (RSC).
transform (n : Nat) (f : Nat -> Nat) : Nat =
  match n with
  | zero => f zero
  | succ n' => transform n' (\ x => f (transform n' (\ y => f (x + y))))

// Fails the syntactic check.
weird-id : Nat -> Nat
| zero => zero
| succ n => succ (weird-id (weird-id n))
// WARNING: Cannot establish the totality of `weird-id` with a syntactic check.

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

// t : A
// ------------------------
// dequarantine : (| t |) t

// Beware: for now `dequarantine` also acts as a congruence

// f : A -> B   t1 : A   t2 : A   e : (| t1 |) t2
// ----------------------------------------------
// dequarantine e : (| f t1 |) (f t2)

// Now it's legal to state theorems about the graph of `weird-id`.
theorem weird-id-aux :
  forall n : Nat, (| weird-id |) n n
proof                                  // |- forall n : Nat, (| weird-id |) n n
  pick-any n                           // n : Nat |- (| weird-id |) n n
  devour                               // n : Nat |- (| weird-id n |) n
  induction n with                     // Termination by syntactic check (ISC).
  | zero =>                            // n : Nat |- (| weird-id zero |) zero
    // There's a pattern matching branch in the definition of `weird-id` that says `weird-id zero` computes to `zero`.
    step                               // n : Nat |- (| zero |) zero
    dequarantine                       // Goal solved!
  | succ (n & ind IH) =>               // n : Nat, IH : (| weird-id n |) n |- (| weird-id (succ n) |) (succ n)
    step                               // n : Nat, IH : (| weird-id n |) n |- (| succ (weird-id (weird-id n)) |) (succ n)
    // In fact, `dequarantine` is not a finisher, but applies a kind of congruence.
    dequarantine                       // n : Nat, IH : (| weird-id n |) n |- (| weird-id (weird-id n) |) n
    // `undevour` pushes a part of the quarantine into a separate top-level quarantine.
    undevour (weird-id n)              // n : Nat, IH : (| weird-id n |) n |- exists r : Nat, (| weird-id n |) r /\ (| weird-id r |) n
    witness n                          // n : Nat, IH : (| weird-id n |) n |- (| weird-id n |) n /\ (| weird-id n |) n
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
  quarantine                           // n : Nat |- (| weird-id |) n n
  instantiate weird-id-aux with n      // Theorem proved!
qed

weird-zero : Nat -> Nat
| zero => zero
| succ n => weird-zero (weird-zero n)
// WARNING: Cannot establish the totality of `weird-zero` with a syntactic check.

theorem weird-zero-aux :
  forall n : Nat, (| weird-zero |) n zero
proof                                  // |- forall n : Nat, (| weird-zero |) n zero
  pick-any n                           // n : Nat |- (| weird-zero |) n zero
  devour                               // n : Nat |- (| weird-zero n |) zero
  induction n with                     // Termination by syntactic check (ISC).
  | zero =>                            // n : Nat |- (| weird-zero zero |) zero
    step                               // n : Nat |- (| zero |) zero
    dequarantine                       // Goal solved!
  | succ (n & ind IH) =>               // n : Nat, IH : (| weird-zero |) n zero |- (| weird-zero (succ n) |) zero
    step                               // n : Nat, IH : (| weird-zero |) n zero |- (| weird-zero (weird-zero n) |) zero
    undevour (weird-zero n)            // n : Nat, IH : (| weird-zero |) n zero |- exists r : Nat, (| weird-zero n |) r /\ (| weird-zero r |) zero
    witness zero                       // n : Nat, IH : (| weird-zero |) n zero |- (| weird-zero n |) zero /\ (| weird-zero zero |) zero
    both IH                            // n : Nat, IH : (| weird-zero |) n zero |- (| weird-zero zero |) zero
    step                               // n : Nat, IH : (| weird-zero |) n zero |- (| zero |) zero
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
qed

missing-case-ok (n : Nat) : Nat =
  match succ n with
  | succ n' => n'
// WARNING: Cannot establish the totality of `missing-case` with a syntactic check.

// The functional is total, so we succeed.
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

// The function is not total, so the proof should always fail.
fail totality missing-case-bad
proof                                  // |- forall n : Nat, exists r : Nat, (| missing-case-bad |) n r
  pick-any n                           // n : Nat |- exists r : Nat, (| missing-case-bad |) n r
  devour                               // n : Nat |- exists r : Nat, (| missing-case-bad n |) r
  cases n with
  | succ n' =>                         // n : Nat, n' : Nat |- exists r : Nat, (| missing-case-bad (succ n') |) r
    witness succ n'                    // n : Nat, n' : Nat |- (| missing-case-bad (succ n') |) (succ n')
    step                               // n : Nat, n' : Nat |- (| succ n' |) (succ n')
    dequarantine                       // Goal solved!
  | zero =>                            // n : Nat |- exists r : Nat, (| missing-case-bad zero |) r
    step                               // n : Nat |- exists r : Nat, False
    // Nothing can be done at this point.
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
proof                                  // |- forall n : Nat, exists r : Nat, (| hof |) n r
  pick-any n                           // n : Nat |- exists r : Nat, (| hof |) n r
  devour                               // n : Nat |- exists r : Nat, (| hof n |) r
  induction n with                     // Termination by syntactic check.
  | zero =>                            // n : Nat |- exists r : Nat, (| hof zero |) r
    witness zero                       // n : Nat |- exists r : Nat, (| hof zero |) zero
    step                               // n : Nat |- exists r : Nat, (| zero |) zero
    dequarantine                       // Goal solved!
  | succ (n & ind (witness res-n such-that IH)) =>
                                       // n : Nat, res-n : Nat, IH : (| hof n |) res-n |- exists r : Nat, (| hof (succ n) |) r
    step                               // n : Nat, res-n : Nat, IH : (| hof n |) res-n |- exists r : Nat, (| sub n (hof (hof n)) |) r
    undevour (hof n)                   // n : Nat, res-n : Nat, IH : (| hof n |) res-n |- exists rr, (| hof n |) rr /\ exists r : Nat, (| sub n (hof rr) |) r
    witness res-n                      // n : Nat, res-n : Nat, IH : (| hof n |) res-n |- (| hof n |) res-n /\ exists r : Nat, (| sub n (hof res-n) |) r
    both IH                            // n : Nat, res-n : Nat, IH : (| hof n |) res-n |- exists r : Nat, (| sub n (hof res-n) |) r
    undevour (hof res-n)               // n : Nat, res-n : Nat, IH : (| hof n |) res-n |- exists rr : Nat, (| hof res-n |) rr /\ exists r : Nat, (| sub n rr |) r
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
proof
  // `devour` is automatic.
  proving forall {A} (x : FreeMon A), exists res : FreeMon A, (| norm x |) res
  pick-any A x
  induction x with // ISC
  | e =>
    witness e
    proving (| norm e |) e
    step
    proving (| e |) e
    dequarantine
  | i a =>
    witness op (i a) e
    proving (| norm (i a) |) (op (i a) e)
    step
    proving (| op (i a) e |) (op (i a) e)
    dequarantine
  | op (l & ind (IHl : exists res-l, (| norm l |) res-l)) (r & (IHr : exists res-r, (| norm r |) res-r)) =>
    proving exists res : FreeMon A, (| norm (op l r) |) res
    pick-witness res-l IHl' for IHl
    pick-witness res-r IHr' for IHr
    step
    proving exists res : FreeMon A,
      (|
        match norm l with
        | e => norm r
        | op l1 l2 => op l1 (norm (op l2 r))
      |) res
    undevour (norm l)
    proving exists res-l, (| norm l |) res-l /\ exists res,
      (|
        match res-l with
        | e => norm r
        | op l1 l2 => op l1 (norm (op l2 r))
      |) res
    witness res-l
    both IHl'
    proving exists res,
      (|
        match res-l with
        | e => norm r
        | op l1 l2 => op l1 (norm (op l2 r))
      |) res
    cases res-l with
    | e =>
      step
      proving exists res, (| norm r |) res
      witness res-r
      proving (| norm r |) res-r
      assumption
    | i a =>
      step
      proving exists res, False
      lemma contra : ~ (| norm l |) (i a) by
        // TODO
      absurd
      contradiction contra IHl'
    | op l1 l2 =>
      proving exists res,
        (| op l1 (norm (op l2 r)) |) res
      undevour (norm (op l2 r))
      proving exists res', (| norm (op l2 r) |) res' /\
        exists res, (| op l1 res' |) res
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
  | cons h1 (t1 & ind IH) =>           // A : Type, l1 : List A, IH : forall l2, exists r, (| interleave t1 l2 |) r |- forall l2 : List A, exists r : List A, (| interleave (cons h1 t1) l2 |) r
    pick-any l2                        // A : Type, l1 : List A, IH : forall l2, exists r, (| interleave t1 l2 |) r, l2 : List A |- exists r : List A, (| interleave (cons h1 t1) l2 |) r
    cases l2 with
    | nil =>
      witness cons h1 t1
      proving (| interleave |) (cons h1 t1) nil (cons h1 t1)
      dequarantine
      proving (| interleave |) nil t1 t1
      dequarantine
    | cons h2 t2 =>
      pick-witness r IH' for IH t2
      witness cons h1 (cons h2 r)
      proving (| interleave |) (cons h1 t1) (cons h2 t2) (cons h1 (cons h2 r))
      dequarantine
      proving (| interleave |) (cons h2 t2) t1 (cons h2 r)
      dequarantine
      proving (| interleave |) t1 t2 r
      assumption // IH' : (| interleave |) t1 t2 r
qed

// Termination by syntactic check (RSC).
interleave' {A} : List A -> List A -> List A
| nil, l2 => l2
| l1, nil => l1
| cons h1 t1, cons h2 t2 => cons h1 (cons h2 (interleave' t1 t2))

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
| node x ts => node (f x) map (tmap f) ts
// WARNING: Cannot establish the totality of `tmap` with a syntactic check.

totality tmap
proof
  proving forall {A B} (f : A -> B) (t : Tree A), exists r : Tree B, (| tmap f |) t r
  pick-any A B f t
  devour
  proving exists r : Tree B, (| tmap f t |) r
  induction t with // ISC
  | node x ts =>
    // Usual problems with nested induction.
qed

data RoseTree A where
  empty : A -> RoseTree A
  node  : List (RoseTree A) -> RoseTree A