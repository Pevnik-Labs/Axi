data Nat where
  zero
  succ : Nat -> Nat

weird-id : Nat -> Nat
| zero => zero
| succ n => succ (weird-id (weird-id n))
// WARNING: Cannot establish the totality of `weird-id` with a syntactic check.

theorem weird-id-aux :
  forall n : Nat, (| weird-id |) n n
proof
  pick-any n
  proving (| weird-id |) n n
  devour // Pulls an argument into the quarantine.
  proving (| weird-id n |) n
  induction n with // ISC
  | zero =>
    proving (| weird-id zero |) zero
    step // Perform a computation step inside the quarantine.
    proving (| zero |) zero
    dequarantine // Finish.
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

missing-case (n : Nat) : Nat =
  match succ n with
  | succ n' => n'

totality missing-case
proof
  proving forall n : Nat, exists r : Nat, (| missing-case |) n r
  pick-any n : Nat
  witness n
  proving (| missing-case |) n n
  devour
  proving (| missing-case n |) n
  step
  proving (| n |) n
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

// This shouldn't go through with structural induction.
totality norm
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


// RSC
sub (n : Nat) : Nat -> Nat
| zero => n
| succ m => pred (sub n m)

// A modified Hofstadter H function.
hof : Nat -> Nat
| zero => zero
| succ n => sub n (hof (hof n))
// WARNING: Cannot establish the totality of `hof` with a syntactic check.

totality hof
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