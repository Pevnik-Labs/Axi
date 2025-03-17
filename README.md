# T-Axi: A Logiced-Enhanced Functional Programming Language

T-Axi (short for "type-theoretical Axi") is a purely functional programming language that supports formal reasoning about its programs in classical higher-order logic. It features a unique two-layer architecture that strictly separates the programming layer from the logical layer.

## Core Features

### Two-Layer Architecture
- **Programming Layer**: A purely functional language based on System F with inductive types, records and type classes.
- **Logical Layer**: A classical higher-order logic.
- **One-way Interaction**: Logic can reason about programs, but programs cannot manipulate logical entities at runtime.

### Programming Layer
- Strong static type system.
- First-class functions, including support for higher-order functions.
- Polymorphism (parametric, impredicative).
- Inductive data types (like `Bool`, `List` or `Tree`), with functions defined by pattern matching.
- Records.
- Haskell-like type classes.

### Logical Layer
- Propositional logic with standard connectives and constants (`-->`, `/\`, `\/`, `<-->`, `~`, `True`, `False`).
- Quantification (`forall`, `exists`) over programs and types from the programming layer, as well as over logical entities like propositions, predicates and relations.
- Equality (`===`) and reasoning by rewriting.
- Classical logic via reasoning `by-contradiction` and convenient syntax for reasoning requiring the Axiom of Choice.
- Chaining, a unique way of representing reasoning based on long chains of equations, implications and biconditionals, which makes many proofs more readable.

## Example

We define the types of booleans and natural numbers, and two functions that check whether a number is `even` or `odd`. Then we state a theorem that for every natural number, either `even` or `odd` returns `true`.

```t-axi
// Booleans.
data type Bool where
  false
  true

// Natural numbers.
data type Nat where
  zero
  succ of Nat

// Check if a natural number is even.
even : Nat -> Bool
| zero => true
| succ zero => false
| succ (succ n) => even n

// Check if a natural number is odd.
odd : Nat -> Bool
| zero => false
| succ zero => true
| succ (succ n) => odd n

// Every natural number is either even or odd.
theorem even-or-odd :
  forall n : Nat,
    even n === true \/ odd n === true
proof
  pick-any n
  induction n with
  | zero => or-left refl
  | succ zero => or-right refl
  | succ (succ (n' & IH)) =>
    cases IH
    . assume (heven : even n' === true)
      or-left heven
    . assume (hodd : odd n' === true)
      or-right hodd
qed

// The same theorem, but with a chaining-based proof.
theorem even-or-odd-chaining :
  forall n : Nat,
    even n === true \/ odd n === true
proof
  pick-any n
  induction n with
  | zero =>
    or-left
    chaining
      === even zero
      === true       by refl
  | succ zero =>
    or-right
    chaining
      === odd (succ zero)
      === true             by refl
  | succ (succ (n' & IH)) =>
    cases IH
    . assume (heven : even n' === true)
      or-left
      chaining
        === even (succ (succ n'))
        === even n'                by refl
        === true                   by heven
    . assume (hodd : odd n' === true)
      or-right
      chaining
        === odd (succ (succ n'))
        === odd n'                 by refl
        === true                   by hodd
qed
```

## Repo Structure

The structure of this repo is as follows:
- In [Demo/](Demo/), you will find a demo of the language in the form of commented pseudocode with semi-formal syntax and semantics. See [Demo/README.md](Demo/README.md) for a reading plan.
- In [tree-sitter-axi/](tree-sitter-axi/) you will find a prototype grammar, parser and syntax highlighting tools.
- In [Slides/](Slides/) you will find a bunch of slide decks which are either more formal presentations of a simpler version of T-Axi, or incomplete research notes.