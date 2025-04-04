// Totality checker steps in when:
// - Defining a function by pattern matching or recursion.
// - In a proof by induction.

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
proof
  pick-any n
  proving (| weird-id |) n n
  devour // Pull an argument into the quarantine.
  proving (| weird-id n |) n
  induction n with // ISC
  | zero =>
    proving (| weird-id zero |) zero
    step // Perform a computation step inside the quarantine.
    proving (| zero |) zero
    dequarantine
    // The goal was solved, because there's a pattern matching branch
    // in the definition of `weird-id` that says `weird-id zero` computes to `zero`.
  | succ (n & (IH : (| weird-id n |) n)) =>
    proving (| weird-id (succ n) |) (succ n)
    step
    proving (| succ (weird-id (weird-id n)) |) (succ n)
    dequarantine // In fact, `dequarantine` is not a finisher, but applies a kind of congruence.
    proving (| weird-id (weird-id n) |) n
    undevour (weird-id n) // `undevour` pushes a part of the quarantine into a separate top-level quarantine.
    proving exists r, (| weird-id n |) r /\ (| weird-id r |) n
    witness n
    both IH IH
qed

// Proving totality of `weird-id` (RTP).
// Note an amusing fact: even though this function is not structurally
// recursive, its totality was proven using structural induction
// (in the previous lemma, that is).
totality weird-id
proof
  proving forall n : Nat, exists r : Nat, (| weird-id |) n r
  pick-any n : Nat
  witness n
  proving (| weird-id |) n n
  instantiate weird-id-aux with n
qed

// Now it's legal to state theorems about `weird-id`.
// Moreover, we don't need to reprove the theorem below from scratch.
// We can use the lemma about the graph that we already proved.
theorem weird-id-spec :
  forall n : Nat, weird-id n === n
proof
  pick-any n
  proving weird-id n === n
  quarantine
  proving (| weird-id |) n n
  instantiate weird-id-aux with n
qed

weird-zero : Nat -> Nat
| zero => zero
| succ n => weird-zero (weird-zero n)
// WARNING: Cannot establish the totality of `weird-zero` with a syntactic check.

theorem weird-zero-aux :
  forall n : Nat, (| weird-zero |) n zero
proof
  pick-any n
  induction n with // ISC
  | zero => dequarantine
  | succ (n & (IH : (| weird-zero |) n zero)) =>
    proving (| weird-zero |) (succ n) zero
    dequarantine
    proving exists r : Nat, (| weird-zero |) n r /\ (| weird-zero |) r zero
    witness zero
    both
    . proving (| weird-zero |) n zero
      IH
    . proving (| weird-zero |) zero zero
      dequarantine
qed

totality weird-zero
proof
  proving forall n : Nat, exists r : Nat, (| weird-zero |) n r
  pick-any n : Nat
  instantiate weird-zero-aux with n
qed

data Unit where
  unit

loop (x : Unit) : Unit = loop x
// WARNING: Cannot establish the totality of `loop` with a syntactic check.

// The function is not total, so the proof should always fail.
fail totality loop
proof
  proving forall x : Unit, exists r : Unit, (| loop |) x r
  pick-any x
  witness unit
  proving (| loop |) x unit
  devour
  proving (| loop x |) unit
  step
  proving (| loop x |) unit
  // Nothing to do here, really...
qed

missing-case-ok (n : Nat) : Nat =
  match succ n with
  | succ n' => n'
// WARNING: Cannot establish the totality of `missing-case` with a syntactic check.

// The functional is total, so we succeed.
totality missing-case-ok
proof
  proving forall n : Nat, exists r : Nat, (| missing-case-ok |) n r
  pick-any n : Nat
  witness n
  proving (| missing-case-ok |) n n
  devour
  proving (| missing-case-ok n |) n
  step
  proving (| n |) n
  dequarantine
qed

missing-case-bad : Nat -> Nat
| succ n => succ n
// WARNING: Missing case: `zero`.

// The function is not total, so the proof should always fail.
fail totality missing-case-bad
proof
  proving forall n : Nat, exists r : Nat, (| missing-case-bad |) n r
  pick-any n
  devour
  proving exists r : Nat, (| missing-case-bad n |) r
  cases n with // ISC
  | succ n' =>
    proving exists r : Nat, (| missing-case-bad (succ n') |) r
    witness succ n'
    proving (| missing-case-bad (succ n') |) (succ n')
    step
    proving (| succ n' |) (succ n')
    dequarantine
  | zero =>
    proving exists r : Nat, (| missing-case-bad zero |) r
    step
    proving exists r : Nat, False
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
proof
  proving forall n : Nat, exists r : Nat, (| hof |) n r
  pick-any n
  devour
  proving exists r : Nat, (| hof n |) r
  induction n with // ISC
  | zero =>
    witness zero
    proving (| hof zero |) zero
    step
    proving (| zero |) zero
    dequarantine
  | succ (n & (IH : exists r : Nat, (| hof n |) r)) =>
    proving exists r : Nat, (| hof (succ n) |) r
    step
    proving exists r : Nat, (| sub n (hof (hof n)) |) r
    pick-witness res-n (IH' : (| hof n |) res-n) for IH
    undevour (hof n)
    proving exists res-n, (| hof n |) res-n /\
      exists r : Nat, (| sub n (hof res-n) |) r
    witness res-n
    both IH
    proving exists r : Nat, (| sub n (hof res-n) |) r
    undevour (hof res-n)
    proving exists rr : Nat, (| hof resn |) rr /\
      exists r : Nat, (| sub n rr |) r
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
  | op (l & (IHl : exists res-l, (| norm l |) res-l)) (r & (IHr : exists res-r, (| norm r |) res-r)) =>
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
proof
  proving forall b : Bool, exists r : Bool, (| silly |) b r
  pick-any b
  witness true
  devour
  proving (| silly b |) true
  cases b with
  | true =>
    proving (| silly true |) true
    step
    proving (| if true then true esle silly true |) true
    step
    proving (| true |) true
    dequarantine
  | false =>
    proving (| silly false |) true
    step
    proving (| if false then true else silly true |) true
    step
    proving (| silly true |) true
    step
    proving (| if true then true esle silly true |) true
    step
    proving (| true |) true
    dequarantine
qed

even : Nat -> Bool
| zero => true
| succ n => notb (even n)

search (n : Nat) : Nat =
  if even n then n else search (succ n)
// WARNING: Cannot establish the totality of `search` with a syntactic check.

// Proving `search` total isn't very hard.
totality search
proof
  proving forall n : Nat, exists r : Nat, (| search |) n r
  pick-any n
  devour
  step
  proving exists r : Nat, (| if even n then n else search (succ n) |) r
  cases even n with
  | true =>
    witness n
    proving (| n |) n
    dequarantine
  | false & eqn (odd-n : even n === false) => // We need to give ourselves an equation `even n === false` for rewriting later.
    witness succ n
    proving (| search (succ n) |) (succ n)
    step
    proving (| if notb (even n) then succ n else search (succ (succ n)) |) (succ n)
    rewrite odd-n
    proving (| if notb false then succ n else search (succ (succ n)) |) (succ n)
    step
    proving (| succ n |) (succ n)
    dequarantine
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
proof
  proving forall {A} (l1 l2 : List A), exists r : List A, (| interleave |) l1 l2 r
  pick-any A l1
  induction l1 with
  | nil =>
    pick-any l2
    witness l2
    proving (| interleave |) nil l2 l2
    dequarantine
  | cons h1 (t1 & (IH : forall l2, exists r, (| interleave |) t1 l2 r)) =>
    pick-any l2
    proving exists r : List A, (| interleave |) (cons h1 t1) l2 r
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