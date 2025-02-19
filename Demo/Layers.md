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
- Second row: given a kind `K` and a type `B` (which can depend on `T` of kind `K`), we can form the type `forall {T : K}, B`. A concrete example is `forall {A : Type}, A -> A`, the type of the polymorphic identity functions, and an example term would be `tfun A => fun x : A => x`.

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
- Second row: given a type `A` and a proposition `P` (which can depend on `x` of type `A`), we can form the proposition `forall x : A, P`. A concrete example is `forall x : Int, x = x`, the proof of which is `pick-any x in refl x`.
- Third row: given a programming kind `K` and a proposition `P` (which can depend on `T` of kind `K`), we can form the proposition `forall {T : K}, P`. A concrete example is `forall {A : Type}, forall x : A, x = x`, the proof of which is `pick-any {A} in pick-any x in refl x`.
- Fourth row: given a logical kind `L` and a proposition `Q` (which can depend on `P` of kind `L`), we can form the proposition `forall P : L, Q`. A concrete example is `forall P : Prop, P --> P`, the proof of which is `pick-any P in assume P in P`.

Are there any other logical entities besides propositions that inhabit `LKind`? Yes! There are at least predicates and relations (which are present in the demo), but there can be even more, including polymorphic predicates and "logical operators" (which include logical connectives and much more).

| Name                        | Demo?  | Syntax              | PTS rule              |
| --------------------------- | ------ | ------------------- | --------------------- |
| Predicates and relations    | ✅ yes | `A -> L`            | (Type, LKind, LKind)  |
| Polymorphic predicates      | ❌ no  | `forall {T : K}, L` | (PKind, LKind, LKind) |
| "Logical" operators         | ❌ no  | `L1 -> L2`          | (LKind, LKind, LKind) |

Let's read the table:
- First row: given a type `A` and a logical kind `L`, we can form the logical kind `A -> L`. A concrete example is `Int -> Prop`, the logical kind of predicates on the integers. A concrete object of this type would be `fun i : Int => i = 42`.
- Second row: given a programming kind `K` and a logical kind `L` (which can depend on `T` of kind `K`), we can form the logical kind `forall {T : K}, L`. A concrete example is `forall {A : Type}, A -> A -> Prop`, the logical kind of polymorphic homogenous binary relations. A concrete object of this type would be `tfun A => fun x y : A => x = y \/ ~ (x = y)`.