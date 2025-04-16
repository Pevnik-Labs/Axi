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

missing-case-ok (n : Nat) : Nat =
  match succ n with
  | succ n' => n'
// WARNING: Missing case: `zero`.

// The function is total, because the `zero` case is impossible.
totality missing-case-ok
proof                                  // |- forall n : Nat, exists r : Nat, missing-case-ok n =?= r
  pick-any n                           // n : Nat |- exists r : Nat, missing-case-ok n =?= r
  witness n                            // n : Nat |- missing-case-ok n =?= n
  step                                 // n : Nat |- n =?= n
  prefl                                // Theorem proved!
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

// Moreover, we can prove that `missing-case-bad` is not total.
theorem missing-case-bad-diverges :
  forall r : Nat, ~ missing-case-bad zero =?= r
proof                                  // |- forall r : Nat, ~ missing-case-bad zero =?= r
  pick-any r                           // r : Nat |- ~ missing-case-bad zero =?= r
  assume h                             // r : Nat, h : missing-case-bad zero =?= r |- False
  step at h                            // r : Nat, h : False |- False
  absurd                               // Theorem proved!
qed

// An alternative proof, using functional inversion.
theorem missing-case-bad-zero :
  forall r : Nat, ~ missing-case-bad zero =?= r
proof                                  // |- forall r : Nat, ~ missing-case-bad zero =?= r
  pick-any r                           // r : Nat |- ~ missing-case-bad zero =?= r
  assume h                             // r : Nat, h : missing-case-bad zero =?= r |- False
  functional inversion h               // Theorem proved! // The case for `zero` was undefined, which gives an instant contradiction.
qed

// But we can also prove that it returns results for non-zero naturals.
theorem missing-case-bad-succ :
  forall n : Nat, missing-case-bad (succ n) =?= succ n
proof                                  // |- forall n : Nat, missing-case-bad (succ n) =?= succ n
  pick-ay n                            // n : Nat |- missing-case-bad (succ n) =?= succ n
  step                                 // n : Nat |- succ n =?= succ n
  prefl                                // Theorem proved!
qed

// We can use `missing-case-bad` to define another function,
// which the syntactic check thinks is not total, but we will
// be able to prove that it is.
missing-case-good (n : Nat) : Nat :=
  missing-case-bad (succ n)
// WARNING: Cannot establish the totality of `missing-case-good` with a syntactic check.

totality missing-case-good
proof                                  // forall n : Nat, exists r : Nat, missing-case-good n =?= r
  pick-any n                           // n : Nat |- exists r : Nat, missing-case-good n =?= r
  witness succ n                       // n : Nat |- missing-case-good n =?= succ n
  unfold missing-case-good             // n : Nat |- missing-case-bad (succ n) =?= succ n
  step                                 // n : Nat |- succ n =?= succ n
  prefl                                // Theorem proved!
qed

data Unit where
  unit

bad (x : Unit) : Bool = notb (bad x)
// WARNING: Cannot establish the totality of `bad` with a syntactic check.

theorem notb-nofix :
  forall b : Bool, ~ b === notb b
proof                                  // |- forall b : Bool, ~ b === notb b
  pick-any b : Bool                    // b : Bool |- ~ b === notb b
  assume heq : b === notb b            // b : Bool, heq : b === notb b |- False
  let goal : Prop =
    match false with
    | false => False
    | true  => True
  proving goal                         // b : Bool, heq : false === notb false, goal : Prop = ... |- goal
  cases b with
  | false =>                           // b : Bool, heq : false === notb false, goal : Prop = ... |- goal
    unfold goal
    rewrite heq
    simpl                              // b : Bool, heq : false === notb false, goal : Prop = ... |- True
    trivial                            // Goal solved!
  | true =>                            // b : Bool, heq : true === notb true, goal : Prop = ... |- goal
    simpl at heq                       // b : Bool, heq : true === false, goal : Prop = ... |- goal
    unfold goal
    rewrite <- heq
    simpl                              // b : Bool, heq : true === false, goal : Prop = ... |- True
    trivial                            // Theorem proved!
qed

theorem bad-diverges :
  forall (x : Unit) (b : Bool),
    ~ bad x =?= b
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

loop (x : Unit) : Unit = loop x
// WARNING: Cannot establish the totality of `loop` with a syntactic check.

// The function is not total, so the proof fails.
fail totality loop
proof                                  // |- forall x : Unit, exists r : Unit, loop x =?= r
  pick-any x                           // x : Unit |- exists r : Unit, loop x =?= r
  witness unit                         // x : Unit |- loop x =?= unit
  step                                 // x : Unit |- loop x =?= unit
  // Nothing can be done at this point.
  cases x with
  | unit =>                            // x : Unit |- loop unit =?= unit
  // Still nothing to do...
qed

// Moreover, we can prove that `loop` doesn't termine using functional induction.
theorem loop-diverges :
  forall x r : Unit, ~ loop x =?= r
proof                                  // |- forall x r : Unit, ~ loop x =?= r
  pick-any x r                         // x r : Unit |- ~ loop x =?= r
  assume h                             // x r : Unit, h : loop x =?= r |- False
  functional induction h               // x r : Unit, h : loop x =?= r |- False --> False // There's just a single case.
  absurd                               // Theorem proved!
qed

silly (b : Bool) : Bool =
  if b then true else silly true
// WARNING: Cannot establish the totality of `silly` with a syntactic check.

// The function is total.
totality silly
proof                                  // |- forall b : Bool, exists r : Bool, silly b =?= r
  pick-any b                           // b : Bool |- exists r : Bool, silly b =?= r
  witness true                         // b : Bool |- silly b =?= true
  cases b with
  | true =>                            // b : Bool |- silly true =?= true
    step                               // b : Bool |- true =?= true
    prefl                              // Goal solved!
  | false =>                           // b : Bool |- silly false =?= true
    step                               // b : Bool |- silly true =?= true
    step                               // b : Bool |- true =?= true
    prefl                              // Theorem proved!
qed

even : Nat -> Bool
| zero => true
| succ n => notb (even n)

search (n : Nat) : Nat =
  if even n then n else search (succ n)
// WARNING: Cannot establish the totality of `search` with a syntactic check.

// Proving `search` total isn't very hard.
totality search
proof                                  // |- forall n : Nat, exists r : Nat, search n =?= r
  pick-any n                           // n : Nat |- exists r : Nat, search n =?= r
  cases even n with
  | true & eqn even-n =>               // n : Nat, even-n : even n === true |- exists r : Nat, search n =?= r
    witness n                          // n : Nat, even-n : even n === true |- search n =?= n
    chaining
      =?= search n
      =?= if even n then n else search (succ n)  by step
      =?= if true then n else search (succ n)    by rewrite even-n
      =?= n
  | false & eqn odd-n =>               // n : Nat, odd-n : even n === false |- exists r : Nat, search n =?= r
    witness succ n                     // n : Nat, odd-n : even n === false |- search n =?= succ n
    chaining
      =?= search n
      =?= if even n then n else search (succ n)                     by step
      =?= if false then n else search (succ n)                      by rewrite odd-n
      =?= search (succ n)
      =?= if notb (even n) then succ n else search (succ (succ n))  by step
      =?= if notb false then succ n else search (succ (succ n))     by rewrite odd-n
      =?= succ n
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
proof                                  // |- forall {A} (l1 l2 : List A), exists r : List A, interleave l1 l2 =?= r
  pick-any A l1                        // A : Type, l1 : List A |- forall l2 : List A, exists r : List A, interleave l1 l2 =?= r
  induction l1 with                    // Termination by syntactic check (ISC).
  | nil =>                             // A : Type, l1 : List A |- forall l2 : List A, exists r : List A, interleave nil l2 =?= r
    pick-any l2                        // A : Type, l1 l2 : List A |- exists r : List A, interleave nil l2 =?= r
    witness l2                         // A : Type, l1 l2 : List A |- interleave nil l2 =?= l2
    chaining
      =?= interleave nil l2
      =?= l2                 by step
  | cons h1 (t1 & ind IH) =>           // A : Type, l1 : List A, IH : forall l2, exists r, interleave t1 l2 =?= r |- forall l2, exists r, interleave (cons h1 t1) l2 =?= r
    pick-any l2                        // A : Type, l1 : List A, IH : forall l2, exists r, interleave t1 l2 =?= r, l2 : List A |- exists r, interleave (cons h1 t1) l2 =?= r
    cases l2 with
    | nil =>                           // A : Type, l1 : List A, IH : forall l2, exists r, interleave t1 l2 =?= r, l2 : List A |- exists r, interleave (cons h1 t1) nil =?= r
      witness cons h1 t1               // A : Type, l1 : List A, IH : forall l2, exists r, interleave t1 l2 =?= r, l2 : List A |- interleave (cons h1 t1) nil =?= cons h1 t1
      chaining
        =?= interleave (cons h1 t1) nil
        =?= cons h1 (interleave nil t1)  by step
        =?= cons h1 t1                   by step
    | cons h2 t2 =>                    // A : Type, l1 : List A, IH : forall l2, exists r, interleave t1 l2 =?= r, l2 : List A |- exists r, interleave (cons h1 t1) (cons h2 t2) =?= r
      pick-witness r IH' for IH t2     // A : Type, l1 : List A, IH : forall l2, exists r, interleave t1 l2 =?= r, l2 r : List A, IH' : interleave t1 t2 =?= r
                                       // |- exists r, interleave (cons h1 t1) (cons h2 t2) =?= r
      witness cons h1 (cons h2 r)      // ... |- interleave (cons h1 t1) (cons h2 t2) =?= cons h1 (cons h2 r)
      chaining
        =?= interleave (cons h1 t1) (cons h2 t2)
        =?= cons h1 (interleave (cons h2 t2) t1)  by step
        =?= cons h1 (cons h2 (interleave t1 t2))  by step
        =?= cons h1 (cons h2 r)                   by quarantine-rewrite IH'
qed

// Termination by syntactic check (RSC).
interleave' {A} : List A -> List A -> List A
| nil, l2 => l2
| l1, nil => l1
| cons h1 t1, cons h2 t2 => cons h1 (cons h2 (interleave' t1 t2))

// Another proof, using `interleave'`.
totality interleave
proof                                  // |- forall {A} (l1 l2 : List A), exists r : List A, interleave l1 l2 =?= r
  pick-any A l1 l2                     // A : Type, l1 l2 : List A |- exists r : List A, interleave l1 l2 =?= r
  witness (interleave' l1 l2)          // A : Type, l1 l2 : List A |- interleave l1 l2 =?= interleave' l1 l2
  induction l1 with                    // Termination by syntactic check (ISC).
  | nil =>                             // A : Type, l1 l2 : List A |- interleave nil l2 =?= interleave' nil l2
    chaining
      =?= interleave nil l2
      =?= l2                  by step
      =?= interleave' nil l2
  | cons h1 (t1 & ind IH) =>           // A : Type, l1 l2 : List A, IH : forall l2, interleave t1 l2 =?= interleave' t1 l2
                                       // |- interleave (cons h1 t1) l2 =?= interleave' (cons h1 t1) l2
    cases l2 with
    | nil =>                           // ... |- interleave (cons h1 t1) nil =?= interleave' (cons h1 t1) nil
      chaining
        =?= interleave (cons h1 t1) nil
        =?= cons h1 (interleave nil t1)   by step
        =?= cons h1 t1                    by step
        =?= interleave' (cons h1 t1) nil
    | cons h2 t2 =>                    // ..., h2 : A, t2 : List A |- interleave (cons h1 t1) (cons h2 t2) =?= interleave' (cons h1 t1) (cons h2 t2)
      chaining
        =?= interleave (cons h1 t1) (cons h2 t2)
        =?= cons h1 (interleave (cons h2 t2) t1)   by step
        =?= cons h1 (cons h2 (interleave t1 t2))   by step
        =?= cons h1 (cons h2 (interleave' t1 t2))  by quarantine-rewrite (IH t2)
        =?= interleave' (cons h1 t1) (cons h2 t2)
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