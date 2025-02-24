# Layers in T-Axi

T-Axi is a language with two layers: the programming layer and the logical layer. The interaction between these layers is supposed to be in one direction only: logic can talk about programs (after all, if it couldn't, it would be pointless to have it), but programs cannot manipulate logical entities (like propositions, predicates or relations) at runtime, nor can they use them for compile-time purposes (an example of which would be restricting the input to a function only to values satisfying a logical condition). Thus we can form an easy and memorable slogan: programs don't know about logic, but logic knows about programs.

The goal of this document is to describe the workings of this division into layers that is more precise than the above vague paragraph, but less precise than what we could have achieved by writing down the exact theory.

## Methodology

We'll use the notion of a **kind**, which is a "higher" analogue to the notions of **type** and **proposition**. We can think that:
- Types classify programs. "What does this program compute?" - "An integer, a boolean, a string, etc."
- Propositions classify proofs. "What does this proof prove?" - "`True`, `False`, a conjunction/disjunction of `P` and `Q`, etc."

In a similar manner:
- In the programming layer, (programming) kinds classify type-level entities. "What's this?" - "A type, a type parameterized by a type, etc."
- In the logical layer, (logical) kinds classify logical entities. "What's this?" - "A proposition, a predicate, a relation, a logical connective, etc."

To explain the stratification of T-Axi into programming and logical layers, we need to describe what entities can be formed and which kinds they inhabit. However, we are not interested in all entities, as most of them are somewhat easy. We are interested only in "functional" entities, like function types, implications and various flavours of universal quantifiers.

We won't explain the entire formalism used here. It suffices to say that a **PTS rule** of the form `(A, B, C)` means that given entities that inhabit kind `A` (the domain) and kind `B` (the codomain), we can form an entity which inhabits kind `C`.

For example, the rule `(Type, Type, Type)` means that given two types (`A` and `B`), we can form another type, which we interpret as the function type `A -> B`.

## Programming layer

The universe in which all programming happens is called `PKind` (which stands for "programming kind").

It's most important inhabitant is `Type` (i.e. `Type : PKind`). The inhabitants of `Type` (i.e. things `A` such that `A : Type`) are types. Some example types include:
- Base types, like `Int` and `String`.
- Compound types, like products `Int * Bool` or sums `String + Int`.

However, in this document we are not concerned with these - we only care about the interesting compound types, which are function types and polymorphic types.

Note: in the table, `A`, `B` are types and `K` is a programming kind.

| Name                | Demo?  | Syntax              | PTS rule            |
| ------------------- | ------ | ------------------- | ------------------- |
| Function type       | ✅ yes | `A -> B`            | (Type, Type, Type)  |
| Polymorphism        | ✅ yes | `forall {T : K}, B` | (PKind, Type, Type) |

Let's read the table:
- First row: given types `A` and `B`, we can form the type `A -> B`, which is the type of functions from `A` to `B`. A concrete example is `Int -> Int`, and a term of this type would be `fun x => x`, the identity function.
- Second row: given a kind `K` and a type `B` (which can depend on `T` of kind `K`), we can form the type `forall {T : K}, B`. A concrete example is `forall {A : Type}, A -> A`, the type of the polymorphic identity functions, and an example term would be `tfun A : Type => fun x : A => x`.

Are there any other entities besides types that inhabit `PKind`? In the current version of the demo there are none, but in the final version of T-Axi there could be entities called "type operators".

| Name                | Demo? | Syntax     | PTS rule              |
| ------------------- | ----- | ---------- | --------------------- |
| Type operators      | ❌ no | `K1 -> K2` | (PKind, PKind, PKind) |

Let's read the table:
- First row: given (programming) kinds `K1` and `K2`, we can form the kind `K1 -> K2`. A concrete example is the kind `Type -> Type`, the kind of unary type operators. A concrete example of an object of this kind would be the type constructor `List`.

## Logic layer

The universe in which all logic happens is called `LKind` (which stands for "logical kind").

It's most important inhabitant is `Prop` (i.e. `Prop : LKind`). The inhabitants of `Prop` (i.e. things `P` such that `P : Prop`) are propositions. Some example propositions:
- The propositional constants `True` and `False`.
- Complex propositions built with propositional connectives, like `P /\ Q`, `P \/ Q`, etc.

However, in this document we are not concerned with these - we only care about the interesting compound propositions, which are implications and various flavours of universal quantifiers.

| Name                        | Demo?  | Syntax              | PTS rule            |
| --------------------------- | ------ | ------------------- | ------------------- |
| Implication                 | ✅ yes | `P --> Q`           | (Prop, Prop, Prop)  |
| First-order quantification  | ✅ yes | `forall x : A, P`   | (Type, Prop, Prop)  |
| Type quantification         | ✅ yes | `forall {T : K}, P` | (PKind, Prop, Prop) |
| Higher-order quantification | ✅ yes | `forall P : L, Q`   | (LKind, Prop, Prop) |

Let's read the table:
- First row: given propositions `P` and `Q`, we can form the proposition `P --> Q`, which is the implication from `P` to `Q`. A concrete example is `True --> True` and a concrete proof of this propositions would be `assume True in trivial`.
- Second row: given a type `A` and a proposition `P` (which can depend on `x` of type `A`), we can form the proposition `forall x : A, P`. A concrete example is `forall x : Int, x === x`, the proof of which is `pick-any x in refl x`.
- Third row: given a programming kind `K` and a proposition `P` (which can depend on `T` of kind `K`), we can form the proposition `forall {T : K}, P`. A concrete example is `forall {A : Type}, forall x : A, x === x`, the proof of which is `pick-any {A} in pick-any x in refl x`.
- Fourth row: given a logical kind `L` and a proposition `Q` (which can depend on `P` of kind `L`), we can form the proposition `forall P : L, Q`. A concrete example is `forall P : Prop, P --> P`, the proof of which is `pick-any P in assume P in P`.

Are there any other logical entities besides propositions that inhabit `LKind`? Yes! There are at least predicates and relations (which are present in the demo), but there can be even more, including polymorphic predicates and "logical operators" (which include logical connectives and much more).

| Name                        | Demo?  | Syntax              | PTS rule              |
| --------------------------- | ------ | ------------------- | --------------------- |
| Predicates and relations    | ✅ yes | `A -> L`            | (Type, LKind, LKind)  |
| Polymorphic predicates      | ✅ yes | `forall {T : K}, L` | (PKind, LKind, LKind) |
| "Logical" operators         | ❌ no  | `L1 -> L2`          | (LKind, LKind, LKind) |

Let's read the table:
- First row: given a type `A` and a logical kind `L`, we can form the logical kind `A -> L`. A concrete example is `Int -> Prop`, the logical kind of predicates on the integers. A concrete object of this type would be `fun i : Int => i === 42`.
- Second row: given a programming kind `K` and a logical kind `L` (which can depend on `T` of kind `K`), we can form the logical kind `forall {T : K}, L`. A concrete example is `forall {A : Type}, A -> A -> Prop`, the logical kind of polymorphic homogenous binary relations. A concrete object of this type would be `tfun A : Type => fun x y : A => x === y \/ ~ (x === y)`.
- Third row: given logical kinds `L1` and `L2`, we can form another logical kind `L1 -> L2`. A concrete example is `Prop -> Prop -> Prop`, the logical kind of binary logical connectives, concrete examples of which are conjunction `/\` and disjunction `\/`.

## What's the metatheory?

You may wonder whether our logic is consistent (i.e. non-contradictory) and whether the programming language has desirable properties. The answer: yes!

In short: our programming and logic layers, when viewed **separately** from each other, correspond to the following well-known systems:
- The programming layer corresponds to System F (see the first table in the programming section). If we include type operators, which are missing in the demo, then it's System F omega (see the second table in the programming section).
- The logical layer also corresponds to System F, and if we include logical operators, then it's system F omega (see the second table in the logic section).

Both System F and System F omega can be viewed as Pure Type Systems (PTSes for short). All PTSes enjoy some nice metatheoretical properties:
- confluence - every program has at most one final result
- type preservation - the result of every program is of the same type as the program itself

Additionally, some PTSes enjoy another desired metatheoretical property called **strong normalization**. A PTS has strong normalization when every program terminates in finite time, no matter in which order computation proceeds. It is well-known that both System F and System F omega (viewed as programming languages) enjoy strong normalization.

From these three properties it follows that, when viewed as logics, both System F and System F omega are consistent. This is because if there was a proof of `False`, there would be a proof of `False` in normal form, but there is no such thing.

Okay, but in T-Axi the programming and logic layers are combined, not separated! To the rescue comes a nice paper called [The Structural Theory of Pure Type Systems](https://florisvandoorn.com/papers/struct_pts.pdf) which can help us see both layers as one. For an approachable overview, see [its accompanying slides](https://florisvandoorn.com/talks/TLCA2014.pdf).

The paper defines a construction, which takes two PTSes *P* and *Q* and creates a PTS *Q over P* that corresponds to the *Q*-logic which can quantify over *P*-terms.

It so happens that this construction corresponds exactly to the core of T-Axi (i.e. it covers the important parts, but not some fancy stuff), irrespective of which variant of it we consider (the demo is System F over System F, but if we include everything from both tables, then it's System F omega over System F omega).

Now, the paper proves some nice theorem about this *Q over P* construction:
- if *P* and *Q* are weakly normalizing, then so is *Q over P*
- *Q over P* is a conservative extension of *Q*, i.e. a theorem is provable in *Q over P* if and only if it is provable in *Q*

Together these theorems guarantee that thecore of T-Axi is weakly normalizing, from which follows that its logic is consistent.