data Nat where
  zero
  succ : Nat -> Nat

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

// Fails the syntactic check.
weird-id : Nat -> Nat
| zero => zero
| succ n => succ (weird-id (weird-id n))
// WARNING: Cannot establish the totality of `weird-id` with a syntactic check.

// It's illegal to state theorems about `weird-id` because it is not known to be total.
theorem weird-id-spec :
  forall n : Nat, weird-id n === n
// ERROR: Prove termination of `weird-id` before reasoning about it.

// But it's legal to state theorems about its graph.
theorem weird-id-aux :
  forall n : Nat, (| weird-id |) n n
proof
  pick-any n
  induction n with // ISC
  | zero =>
    proving (| weird-id |) zero zero
    dequarantine
    // The goal was solved, because there's a pattern matching branch
    // in the definition of `weird-id` that says `weird-id zero` computes to `zero`.
  | succ (n & (IH : (| weird-id |) n n)) =>
    proving (| weird-id |) (succ n) (succ n)
    dequarantine
    // TODO: comment
    proving exists r : Nat, (| weird-id |) n r /\ (| weird-id |) r n
    witness n
    proving (| weird-id |) n n /\ (| weird-id |) n n
    both IH IH
qed

// Proving totality of `weird-id` (RTP).
// Note an amusing fact: even though this function is not structurally
// recursive, we it's totality was proven using structural induction
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

theorme weird-zero-aux :
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

missing-case (n : Nat) : Nat =
  match succ n with
  | succ n' => n'

totality missing-case
proof
  proving forall n : Nat, exists r : Nat, (| missing-case |) n r
  pick-any n : Nat
  witness n
  proving (| missing-case |) n n
  dequarantine
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

totality norm
proof
  proving forall {A} (x : FreeMon A), exists res : FreeMon A, (| norm |) x res
  pick-any A x
  induction x with // ISC
  | e =>
    witness e
    proving (| norm |) e e
    dequarantine
  | i a =>
    witness op (i a) e
    proving (| norm |) (i a) (op (i a) e)
    dequarantine
  | op (l & (IHl : exists res-l, (| norm |) l res-l)) (r & (IHr : exists res-r, (| norm |) r res-r)) =>
    proving exists res : FreeMon A, (| norm |) (op l r) res
    pick-witness res-l IHl' for IHl
    pick-witness res-r IHr' for IHr
    dequarantine
    cases res-l with
    | e =>
      witness res-r
      proving (| norm |) (op l r) res-r
      dequarantine
      proving
        ((| norm |) l e /\ exists res : FreeMon A, (| norm |) r res) \/
        (exists l1 l2, (| norm |) l (op l1 l2) /\ exists res, (| norm |) (op l2 r) res)
      or-left
      both
      . assumption // IHl' : (| norm |) l e
      . proving exists res : FreeMon A, (| norm |) r res
        witness res-r
        proving (| norm |) r res-r
        assumption // IHr' : (| norm |) r res-r
    | i a =>
      proving exists res : FreeMon A, (| norm |) (op l r) res
      // TODO
    | op l1 l2 =>
      proving exists res : FreeMon A, (| norm |) (op l r) res
      // TODO: shouldn't go through.
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