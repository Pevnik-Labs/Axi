(** * Quantity *)

Require Export
  Bool
  Coq.Classes.RelationClasses
  Coq.Classes.DecidableClass.

Inductive Quantity : Type :=
| Zero
| One
| Few
| Many
| Any.

(**
  Quantities keep track of resource usage. They are a crude measure,
  best thought of in the following terms:
  - [Zero] means <<0>> uses
  - [One] means <<1>> use
  - [Few] means <<0>> or <<1>> use
  - [Many] means <<1>> or more uses
  - [Any] means <<0>> or more uses

  In code the quantity names are words, but on paper, the following symbols
  (inspired by regular expression syntax) are used:
  - [Zero] is <<0>>
  - [One] is <<1>>
  - [Few] is <<?>>
  - [Many] is <<+>>
  - [Any] is <<*>>
*)

(** [Quantity] has decidable equality. *)

#[refine, export] Instance Decidable_eq_Quantity :
  forall r s : Quantity,
    Decidable (r = s) :=
{
  Decidable_witness :=
    match r, s with
    | Zero, Zero => true
    | One , One  => true
    | Few , Few  => true
    | Many, Many => true
    | Any , Any  => true
    | _   , _    => false
    end;
}.
Proof.
  now destruct r, s; cbn.
Defined.

(** * Subusage ordering

  The [Subusage] ordering represents the following idea: quantity <<r>> is
  a subusage of quantity <<s>> when a resource that must be used <<r>> times
  can also be used whenever a resource that must be used <<s>> times is expected.

  For example, when we must use a resource [Many] times, i.e. 1 or more, but a
  resource which must be used [One] time is expected, then we have enough, so
  [Many] is a [Subusage] of [One].

  A picture is worth a thousand words:
*)

(*
    0     1
     \   / \
      \ /   \
       ?     +
        \   /
         \ /
          *
*)

(**
  The diagram is read as usual, with smaller elements at the bottom,
  and going upwards we move towards bigger elements. Explicitly:
  - [Any] is the bottom element of the [Subusage] ordering, as it means
    0 or more, placing no constraint on resource usage whatsoever.
  - Above [Any] we have [Few] (meaning 0 or 1) and [Many] (meaning 1 or more).
    Clearly when we must use a resource [Any] number of times, i.e. 0 or more,
    we have enough to use it 0 or 1 times, as well as enough to use it 1 or more
    times. Therefore [Any] is a [Subusage] of both [Few] and [Many].
  - Above [Few] we have [Zero] and [One]. Clearly if we must use a resource [Few]
    (meaning 0 or 1) times, then we have enough to use it 0 times or 1 times,
    hence [Few] is a [Subusage] of [Zero] and [One].
  - Above [Many] we have [One]. Clearly, if we must use a resource [Many]
    (i.e. 1 or more) times, then we have enough to use it 1 time, thus [Many]
    is a [Subusage] of [One].
  - Not directly depicted is the fact that [Subusage] is reflexive, i.e. any
    quantity is a [Subusage] of itself, which should be obvious.
*)

Inductive Subusage : Quantity -> Quantity -> Prop :=
| Subusage_refl     : forall r : Quantity, Subusage r r
| Subusage_Any_l    : forall r : Quantity, Subusage Any r
| Subusage_Many_One : Subusage Many One
| Subusage_Few_One  : Subusage Few One
| Subusage_Few_Zero : Subusage Few Zero.

#[export] Hint Constructors Subusage : core.

(**
  It is also worth pointing out the relationship between [One] and [Zero].
  Clearly if we must use a resource [One] time, then we cannot use it [Zero]
  times, so [One] is not a [Subusage] of [Zero].
*)

Lemma not_Subusage_One_Zero :
  ~ Subusage One Zero.
Proof.
  now inversion 1.
Qed.

(**
  Similarly, if we must use a resource [Zero] times, then we cannot use it
  [One] time, so [Zero] is not a [Subusage] of [One].
*)

Lemma not_Subusage_Zero_One :
  ~ Subusage Zero One.
Proof.
  now inversion 1.
Qed.

(**
  If we must use a resource [Many] (i.e. 1 or more) times, we are not allowed
  to use it 0 times, which is required for a resource that is expected to be
  used [Few] times. Hence [Many] is not a [Subusage] of [Few].
*)

Lemma not_Subusage_Many_Few :
  ~ Subusage Many Few.
Proof.
  now inversion 1.
Qed.

(**
  Similarly: if we must use a resource [Few] (i.e. 0 or 1) times, then we
  cannot use it more than once, which is required of a resource that is
  expected to be used [Many] times, so [Few] is not a [Subusage] of [Many]
*)

Lemma not_Subusage_Few_Many :
  ~ Subusage Few Many.
Proof.
  now inversion 1.
Qed.

(** [Subusage] is a decidable partial order. *)

#[export] Instance PreOrder_Subusage :
  PreOrder Subusage.
Proof.
  split; red.
  - easy.
  - now do 2 inversion 1.
Qed.

#[export] Instance Antisymmetric_Subusage :
  Antisymmetric _ eq Subusage.
Proof.
  now do 2 inversion 1.
Qed.

#[refine, export] Instance Decidable_Subusage :
  forall r s : Quantity,
    Decidable (Subusage r s) :=
{
  Decidable_witness :=
    match r, s with
    | Any , _    => true
    | Many, One  => true
    | Few , One  => true
    | Few , Zero => true
    | _   , _    => decide (r = s)
    end;
}.
Proof.
  now destruct r, s; cbn.
Defined.

(** * Semiring structure

  Quantities form an ordered commutative semiring with no zero divisors and
  with the additional property that if the result of addition is [Zero], then
  so are the arguments.

  We define quantity addition and multiplication below and spend the rest of
  this section proving that the above sentence is indeed true.
*)

(** ** Addition

  Because quantities are a very crude way of counting, addition is very simple.
  Let's assume we have a quantity <<r>> (of some resource, perhaps):
  - When we add [Zero], then we still have <<r>>.
  - When <<r>> is not [Zero] and we add [One] or [Many], then we have [Many].
    Yes, quantity arithmetic is this crude!
  - In all other cases, the result is [Any].
*)

Definition add (r s : Quantity) : Quantity :=
match r, s with
| Zero, s    => s
| r   , Zero => r
| One , _    => Many
| _   , One  => Many
| Many, _    => Many
| _   , Many => Many
| _, _       => Any
end.

(** [Zero] is the identity element of [add]. *)

Lemma add_Zero_l :
  forall r : Quantity,
    add Zero r = r.
Proof.
  easy.
Qed.

Lemma add_Zero_r :
  forall r : Quantity,
    add r Zero = r.
Proof.
  now intros []; cbn.
Qed.

(**
  [Many] is the absorbing element of [add], i.e. adding [Many] to anything
  results in [Many].
*)

Lemma add_Many_l :
  forall r : Quantity,
    add Many r = Many.
Proof.
  now intros []; cbn.
Qed.

Lemma add_Many_r :
  forall r : Quantity,
    add r Many = Many.
Proof.
  now intros []; cbn.
Qed.

(** [add] is associative and commutative. *)

Lemma add_comm :
  forall r s : Quantity,
    add r s = add s r.
Proof.
  now intros [] []; cbn.
Qed.

Lemma add_assoc :
  forall r s t : Quantity,
    add (add r s) t = add r (add s t).
Proof.
  now intros [] [] []; cbn; easy.
Qed.

(**
  When the result of [add] is [Zero], both arguments also are [Zero]. This
  means that there are no "negative" quantities, so quantities are, in some
  sense, more like natural numbers than like integers.
*)

Lemma add_Zero_inv :
  forall r s : Quantity,
    add r s = Zero -> r = Zero /\ s = Zero.
Proof.
  now intros [] []; cbn.
Qed.

(** [add] preserves [Subusage] in both arguments. *)

Lemma Subusage_add :
  forall r1 r2 s1 s2 : Quantity,
    Subusage r1 r2 -> Subusage s1 s2 -> Subusage (add r1 s1) (add r2 s2).
Proof.
  intros r1 r2 s1 s2 H1 H2.
  transitivity (add r2 s1).
  - now destruct r2, s1; inversion H1; subst; cbn.
  - now destruct r2, s2; inversion H2; subst; cbn.
Qed.

(** *** Alternative definition of addition

  When defining addition, besides the [Zero] cases, we highlighted the cases
  when the result is [Many] and then said that in all other cases the result
  is [Any].

  We could have given an alternative definition, which highlights the cases
  when the result is [Any], and then says that in all other cases the result
  is [Many]. Both definitions are equivalent. However, we believe the original
  definition is more intuitive.
*)

Definition add' (r s : Quantity) : Quantity :=
match r, s with
| Zero, _    => s
| _   , Zero => r
| Few , Few  => Any
| Few , Any  => Any
| Any , Few  => Any
| Any , Any  => Any
| _   , _    => Many
end.

Lemma add'_spec :
  forall r s : Quantity,
    add' r s = add r s.
Proof.
  now intros [] [].
Qed.

(** ** Multiplication

  Multiplication of quantities, like addition, is rather unsophisticated:
  - Multiplying by [Zero] gives [Zero], like for ordinary numbers
  - Multiplying by [One] doesn't change the result
  - [Few] times [Few] is [Few] and [Many] times [Many] is [Many]
  - In all other cases, the result is [Any]
*)

Definition mul (r s : Quantity) : Quantity :=
match r, s with
| Zero, _    => Zero
| One , _    => s
| _   , Zero => Zero
| _   , One  => r
| Few , Few  => Few
| Many, Many => Many
| _   , _    => Any
end.

(** [One] is the identity element of [mul]. *)

Lemma mul_One_l :
  forall r : Quantity,
    mul One r = r.
Proof.
  easy.
Qed.

Lemma mul_One_r :
  forall r : Quantity,
    mul r One = r.
Proof.
  now intros []; cbn.
Qed.

(** [Zero] is the absorbing element of [mul]. *)

Lemma mul_Zero_l :
  forall r : Quantity,
    mul Zero r = Zero.
Proof.
  easy.
Qed.

Lemma mul_Zero_r :
  forall r : Quantity,
    mul r Zero = Zero.
Proof.
  now intros []; cbn.
Qed.

(** [mul] is associative and commutative. *)

Lemma mul_comm :
  forall r s : Quantity,
    mul r s = mul s r.
Proof.
  now intros [] []; cbn.
Qed.

Lemma mul_assoc :
  forall r s t : Quantity,
    mul (mul r s) t = mul r (mul s t).
Proof.
  now intros [] [] []; cbn.
Qed.

(**
  When the result of [mul] is [Zero], one of the arguments must also be [Zero].
  In this way quantities are similar to ordinary numbers.
*)

Lemma mul_Zero_inv :
  forall r s : Quantity,
    mul r s = Zero -> r = Zero \/ s = Zero.
Proof.
  now intros [] []; cbn; inversion 1; intuition.
Qed.

(** [mul] preserves [Subusage] in both arguments. *)

Lemma Subusage_mul :
  forall r1 r2 s1 s2 : Quantity,
    Subusage r1 r2 -> Subusage s1 s2 -> Subusage (mul r1 s1) (mul r2 s2).
Proof.
  intros r1 r2 s1 s2 H1 H2.
  transitivity (mul r2 s1).
  - now destruct r2, s1; inversion H1; subst; cbn.
  - now destruct r2, s2; inversion H2; subst; cbn.
Qed.

(** ** Distributivity laws *)

(** [mul] distributes over [add] on both sides. *)

Lemma mul_add_l :
  forall r s t : Quantity,
    mul r (add s t) = add (mul r s) (mul r t).
Proof.
  now intros [] [] []; cbn.
Qed.

Lemma mul_add_r :
  forall r s t : Quantity,
    mul (add r s) t = add (mul r t) (mul s t).
Proof.
  now intros [] [] []; cbn.
Qed.

(** * Structure of the subusage ordering

  In this section we'll study the [Subusage] ordering in a bit more depth.
  Our goal will be to define the infimum and supremum operations, prove their
  specifications and find a nice intuitive characterization.

  The key to finding this intuitive characterization will be to change
  perspective. Until now we have though about quantities as a crude kind
  of arithmetic. But we can view them differently: quantities are traits
  (i.e. interfaces) that a resource type may have (i.e. implement) or not.
  Well, at least that's the case for the non-zero quantities - zero is special
  in this view and is not a trait, but rather information that a resource has
  been used up.
*)

(** ** Infimum *)

Definition inf (r s : Quantity) : Quantity :=
match r, s with
| Any , _    => Any
| _   , Any  => Any
| Many, Few  => Any
| Many, Zero => Any
| Many, _    => Many
| Few , Many => Any
| Few , _    => Few
| One , Zero => Few
| One , _    => s
| Zero, One  => Few
| Zero, Many => Any
| Zero, _    => s
end.

Definition inf' (r s : Quantity) : Quantity :=
match r, s with
| Zero, One  => Few
| Zero, Many => Any
| Zero, _    => s
| One , Zero => Few
| Many, Zero => Any
| _   , Zero => r
| _   , _    => mul r s
end.

Lemma inf'_spec :
  forall r s : Quantity,
    inf' r s = inf r s.
Proof.
  now intros [] [].
Qed.

(**
  [inf] is associative, commutative and idempotent.
  [Any] is its absorbing element.
*)

Lemma inf_Any_l :
  forall r : Quantity,
    inf Any r = Any.
Proof.
  easy.
Qed.

Lemma inf_Any_r :
  forall r : Quantity,
    inf r Any = Any.
Proof.
  now intros []; cbn.
Qed.

Lemma inf_idem :
  forall r : Quantity,
    inf r r = r.
Proof.
  now intros []; cbn.
Qed.

Lemma inf_comm :
  forall r s : Quantity,
    inf r s = inf s r.
Proof.
  now intros [] []; cbn.
Qed.

Lemma inf_assoc :
  forall r s t : Quantity,
    inf (inf r s) t = inf r (inf s t).
Proof.
  now intros [] [] []; cbn.
Qed.

(** [inf] truly is the infimum in the [Subusage] ordering. *)

Lemma Subusage_inf_l_l :
  forall r s : Quantity,
    Subusage (inf r s) r.
Proof.
  now intros [] []; cbn.
Qed.

Lemma Subusage_inf_l_r :
  forall r s : Quantity,
    Subusage (inf r s) s.
Proof.
  now intros [] []; cbn.
Qed.

Lemma Subusage_inf_r :
  forall q r s : Quantity,
    Subusage q r -> Subusage q s -> Subusage q (inf r s).
Proof.
  now do 2 inversion 1; only 1: destruct s; cbn.
Qed.

Lemma inf_spec :
  forall r s rs : Quantity,
    inf r s = rs
      <->
    Subusage rs r /\
    Subusage rs s /\
    forall q : Quantity, Subusage q r -> Subusage q s -> Subusage q rs.
Proof.
  split.
  - intros <-.
    split; [| split].
    + now apply Subusage_inf_l_l.
    + now apply Subusage_inf_l_r.
    + now intros; apply Subusage_inf_r.
  - intros (Htr & Hts & Huniq).
    apply Antisymmetric_Subusage.
    + apply Huniq.
      * now apply Subusage_inf_l_l.
      * now apply Subusage_inf_l_r.
    + now apply Subusage_inf_r.
Qed.

(** [inf] preserves [Subusage] in both arguments. *)

Lemma Subusage_inf_inf :
  forall r1 r2 s1 s2 : Quantity,
    Subusage r1 r2 -> Subusage s1 s2 -> Subusage (inf r1 s1) (inf r2 s2).
Proof.
  intros r1 r2 s1 s2 Hr Hs.
  transitivity (inf r2 s1).
  - now destruct s1; inversion Hr; subst; cbn.
  - now destruct r2; inversion Hs; subst; cbn.
Qed.

(** The algebraic and order structures are related in the usual way. *)

Lemma Subusage_iff_inf_eq :
  forall r s : Quantity,
    Subusage r s <-> inf r s = r.
Proof.
  now intros [] []; cbn.
Qed.

(** ** Complement

  But before we delve into infima and suprema, let's stop for a moment to
  define an operation called 

*)

Definition complement (r : Quantity) : Quantity :=
match r with
| Zero => Zero
| One  => Any
| Few  => Many
| Many => Few
| Any  => One
end.

Lemma complement_complement :
  forall r : Quantity,
    complement (complement r) = r.
Proof.
  now intros []; cbn.
Qed.

Lemma Subusage_complement :
  forall r s : Quantity,
    Subusage r s -> s = Zero \/ Subusage (complement s) (complement r).
Proof.
  now intros r []; inversion 1; cbn; firstorder.
Qed.

(** ** Supremum *)

Definition sup (r s : Quantity) : option Quantity :=
match r, s with
| Any , _    => Some s
| _   , Any  => Some r
| Many, Zero => None
| Many, Few  => Some One
| Many, _    => Some s
| Few , Many => Some One
| Few , _    => Some s
| One , Zero => None
| One , _    => Some One
| Zero, Few  => Some Zero
| Zero, Zero => Some Zero
| Zero, _    => None
end.



Lemma sup_is_complement :
  forall r s rs : Quantity,
    sup r s = Some rs ->
      rs = complement (mul (complement r) (complement s)).
Proof.
  now intros [] [] rs; inversion 1; subst; cbn.
Qed.

Lemma sup_complement :
  forall r s rs : Quantity,
    sup (complement r) (complement s) = Some rs ->
      rs = complement (mul r s).
Proof.
  now intros [] [] rs; inversion 1; subst; cbn.
Qed.

(**
  [sup] is commutative, idempotent and its identity element is [Any].
  When all subexpressions are defined, [sup] is also associative.
*)

Lemma sup_Any_l :
  forall r : Quantity,
    sup Any r = Some r.
Proof.
  easy.
Qed.

Lemma sup_Any_r :
  forall r : Quantity,
    sup r Any = Some r.
Proof.
  now intros []; cbn.
Qed.

Lemma sup_idem :
  forall r : Quantity,
    sup r r = Some r.
Proof.
  now intros []; cbn.
Qed.

Lemma sup_comm :
  forall r s : Quantity,
    sup r s = sup s r.
Proof.
  now intros [] []; cbn.
Qed.

Lemma sup_assoc :
  forall r s t rs st : Quantity,
    sup r s = Some rs -> sup s t = Some st ->
      sup rs t = sup r st.
Proof.
  now intros [] [] [] rs st; do 2 inversion 1; cbn.
Qed.

(** When [sup] is defined, it truly is the supremum in the [Subusage] ordering. *)

Lemma Subusage_sup_r_l :
  forall r s rs : Quantity,
    sup r s = Some rs ->
      Subusage r rs.
Proof.
  now intros [] [] rs; inversion 1; cbn.
Qed.

Lemma Subusage_sup_r_r :
  forall r s rs : Quantity,
    sup r s = Some rs ->
      Subusage s rs.
Proof.
  now intros [] [] rs; inversion 1; cbn.
Qed.

Lemma Subusage_sup_l :
  forall r s t rs : Quantity,
    sup r s = Some rs ->
      Subusage r t -> Subusage s t -> Subusage rs t.
Proof.
  now intros [] [] t; do 3 inversion 1; subst; cbn.
Qed.

Lemma sup_spec :
  forall r s rs : Quantity,
    sup r s = Some rs
      <->
    Subusage r rs /\
    Subusage s rs /\
    forall t : Quantity, Subusage r t -> Subusage s t -> Subusage rs t.
Proof.
  split.
  - intros Hsup.
    split; [| split].
    + now apply Subusage_sup_r_l in Hsup.
    + now apply Subusage_sup_r_r in Hsup.
    + now intros; apply Subusage_sup_l with r s.
  - intros (Htr & Hts & Huniq).
    now destruct r, s; cbn;
      inversion Htr; subst; try congruence;
      inversion Hts; subst; try congruence;
      match goal with
      | H : forall _, Subusage _ _ -> Subusage _ _ -> Subusage One _ |- _ =>
        specialize (H Zero ltac:(easy)); inversion H
      | H : forall _, Subusage _ _ -> Subusage _ _ -> Subusage _ _ |- _ =>
        specialize (H Any  ltac:(easy) ltac:(easy)) +
        specialize (H Many ltac:(easy) ltac:(easy)) +
        specialize (H Few  ltac:(easy) ltac:(easy)) +
        specialize (H One  ltac:(easy) ltac:(easy)) +
        specialize (H Zero ltac:(easy));
          now inversion H
      end.
Qed.

(** When two quantities have a supremum, smaller quantities also do. *)

Lemma sup_defined_Subusage :
  forall r1 r2 s r2s : Quantity,
    sup r2 s = Some r2s -> Subusage r1 r2 ->
      exists r1s : Quantity, sup r1 s = Some r1s.
Proof.
  now intros r1 [] []; cbn; do 2 inversion 1; subst; cbn; eauto.
Qed.

(** [sup] preserves [Subusage] in both arguments. *)

Lemma Subusage_sup_sup :
  forall r1 r2 s1 s2 r1s1 r2s2 : Quantity,
    sup r1 s1 = Some r1s1 -> sup r2 s2 = Some r2s2 ->
      Subusage r1 r2 -> Subusage s1 s2 -> Subusage r1s1 r2s2.
Proof.
  intros r1 r2 s1 s2 r1s1 r2s2 H1 H2 Hr Hs.
  destruct (sup_defined_Subusage r1 r2 s2 _ H2 Hr) as [r1s2 H].
  transitivity r1s2.
  - now destruct r1, s1, s2; inversion H1; inversion H2; inversion H; cbn.
  - now destruct r1, r2, s2; inversion H1; inversion H2; inversion H; cbn.
Qed.

(** The algebraic and order structures are related in the usual way. *)

Lemma Subusage_iff_sup_eq :
  forall r s : Quantity,
    Subusage r s <-> sup r s = Some s.
Proof.
  now intros [] []; cbn.
Qed.

(** ** Absorbption and distributivity laws *)

(** Absorption laws for [sup]. *)

Lemma sup_inf_l :
  forall r s : Quantity,
    sup (inf r s) s = Some s.
Proof.
  now intros [] []; cbn.
Qed.

Lemma sup_inf_r :
  forall r s : Quantity,
    sup r (inf r s) = Some r.
Proof.
  now intros [] []; cbn.
Qed.

(** Absorption laws for [inf]. *)

Lemma inf_sup_l :
  forall r s rs : Quantity,
    sup r s = Some rs ->
      inf rs s = s.
Proof.
  now intros [] [] rs; inversion 1; subst; cbn.
Qed.

Lemma inf_sup_r :
  forall r s rs : Quantity,
    sup r s = Some rs ->
      inf r rs = r.
Proof.
  now intros [] [] rs; inversion 1; subst; cbn.
Qed.

(** Distributivity laws. *)

Lemma sup_inf_inf_l :
  forall r s t st,
    sup s t = Some st ->
      sup (inf r s) (inf r t) = Some (inf r st).
Proof.
  now intros [] [] []; cbn; inversion 1; subst; cbn.
Qed.

Lemma sup_inf_inf_r :
  forall r s t rs,
    sup r s = Some rs ->
      sup (inf r t) (inf s t) = Some (inf rs t).
Proof.
  now intros [] [] []; cbn; inversion 1; subst; cbn.
Qed.

(** * Subtraction *)

Definition sub (r s : Quantity) : option Quantity :=
match r, s with
| Any , _    => Some Any
| _   , Zero => Some r
| Zero, _    => None
| One , One  => Some Zero
| One , _    => None
| Few , One  => Some Zero
| Few , Few  => Some Zero
| Few , _    => None
| Many, One  => Some Any
| Many, Few  => Some Many
| Many, Many => Some Any
| Many, Any  => Some Many
end.

Lemma sub_spec_ex :
  forall r s rs : Quantity,
    sub r s = Some rs ->
      Subusage r (add rs s).
Proof.
  now intros [] [] rs; inversion 1; subst; cbn.
Qed.

Lemma sub_spec_uniq :
  forall r s rs : Quantity,
    sub r s = Some rs ->
      forall t : Quantity, Subusage r (add t s) -> Subusage rs t.
Proof.
  now intros [] [] rs; inversion 1; intros []; inversion 1; subst; cbn.
Qed.

Lemma sub_spec :
  forall r s rs : Quantity,
    sub r s = Some rs
      <->
    Subusage r (add rs s) /\
    forall t : Quantity, Subusage r (add t s) -> Subusage rs t.
Proof.
  split.
  - split.
    + now apply sub_spec_ex.
    + now apply sub_spec_uniq.
  - intros [Hex Huniq].
    now destruct r, s, rs; cbn in *; try easy;
      match goal with
      | H : forall _, Subusage _ _ -> Subusage _ _ |- _ =>
        specialize (H Any  ltac:(easy)) +
        specialize (H Many ltac:(easy)) +
        specialize (H One  ltac:(easy)) +
        specialize (H Zero ltac:(easy));
          now inversion H
      end.
Qed.

Lemma Subusage_sub_Zero :
  forall r rr : Quantity,
    sub r r = Some rr ->
      Subusage rr Zero.
Proof.
  now intros [] rr; inversion 1.
Qed.

(** * Miscellaneous orderings *)

(** ** Subtraction order

  [SubtractionOrder] is a decidable total preorder that arises from subtraction,
  i.e. <<r <= s>> if and only if <<s - r>> is defined.

  We define it explicitly as <<Zero <= One <= Few <= Many <= Any <= Many>>.

  Note that according to this order, [Many] and [Any] are equivalent, therefore
  it is not antisymmetric and thus not a partial order.
*)

Inductive SubtractionOrder : Quantity -> Quantity -> Prop :=
| SubtractionOrder_refl    : forall r : Quantity, SubtractionOrder r r
| SubtractionOrder_Zero_l  : forall r : Quantity, SubtractionOrder Zero r
| SubtractionOrder_Many_r  : forall r : Quantity, SubtractionOrder r Many
| SubtractionOrder_Any_r   : forall r : Quantity, SubtractionOrder r Any
| SubtractionOrder_One_Few : SubtractionOrder One Few.

#[export] Hint Constructors SubtractionOrder : core.

Lemma SubtractionOrder_spec :
  forall r s : Quantity,
    SubtractionOrder r s <-> sub s r <> None.
Proof.
  now intros [] []; cbn.
Qed.

#[export] Instance PreOrder_SubtractionOrder :
  PreOrder SubtractionOrder.
Proof.
  split; red.
  - easy.
  - now do 2 inversion 1.
Qed.

Lemma Total_SubtractionOrder :
  forall r s : Quantity,
    SubtractionOrder r s \/ SubtractionOrder s r.
Proof.
  now intros [] []; cbn; firstorder.
Qed.

#[refine, export] Instance Decidable_SubtractionOrder :
  forall r s : Quantity,
    Decidable (SubtractionOrder r s) :=
{
  Decidable_witness :=
    match r, s with
    | Zero, _    => true
    | _   , Many => true
    | _   , Any  => true
    | One , Few  => true
    | _   , _    => decide (r = s)
    end;
}.
Proof.
  now destruct r, s; cbn.
Defined.

(** ** Decrementation order

  [DecrementationOrder] is a decidable transitive relation (which is not
  reflexive, hence not an actual "order") that arises from decrementation,
  i.e. <<r <= s>> if and only if <<r = s - One>>.

  We define it explicitly as:
  - <<Zero <= One>>
  - <<Zero <= Few>>
  - <<Any <= Many>>
  - <<Any <= Any>>
*)

Inductive DecrementationOrder : Quantity -> Quantity -> Prop :=
| DecrementationOrder_Zero_One : DecrementationOrder Zero One
| DecrementationOrder_Zero_Few : DecrementationOrder Zero Few
| DecrementationOrder_Any_Many : DecrementationOrder Any Many
| DecrementationOrder_Any_Any  : DecrementationOrder Any Any.

#[export] Hint Constructors DecrementationOrder : core.

Lemma DecrementationOrder_spec :
  forall r s : Quantity,
    DecrementationOrder r s <-> sub s One = Some r.
Proof.
  now intros [] []; cbn.
Qed.

#[export] Instance Transitive_DecrementationOrder :
  Transitive DecrementationOrder.
Proof.
  now do 2 inversion 1; subst.
Qed.

#[refine, export] Instance Decidable_DecrementationOrder :
  forall r s : Quantity,
    Decidable (DecrementationOrder r s) :=
{
  Decidable_witness :=
    match r, s with
    | Zero, One  => true
    | Zero, Few  => true
    | Any , Many => true
    | Any , Any  => true
    | _   , _    => false
    end;
}.
Proof.
  now destruct r, s; cbn.
Defined.

(** ** Arithmetic order

  [ArithmeticOrder] is a decidable total order that orders quantities
  by how big (in some sense) they are. The idea is as follows:

  We define it explicitly as: <<Zero <= One <= Few <= Many <= Any>>.

*)

Inductive ArithmeticOrder : Quantity -> Quantity -> Prop :=
| ArithmeticOrder_refl     : forall r : Quantity, ArithmeticOrder r r
| ArithmeticOrder_Zero_l   : forall r : Quantity, ArithmeticOrder Zero r
| ArithmeticOrder_Any_r    : forall r : Quantity, ArithmeticOrder r Any
| ArithmeticOrder_One_Few  : ArithmeticOrder One Few
| ArithmeticOrder_One_Many : ArithmeticOrder One Many
| ArithmeticOrder_Few_Many : ArithmeticOrder Few Many.

#[export] Hint Constructors ArithmeticOrder : core.

#[export] Instance PreOrder_ArithmeticOrder :
  PreOrder ArithmeticOrder.
Proof.
  split; red.
  - easy.
  - now do 2 inversion 1; subst.
Qed.

#[export] Instance Antisymmetric_ArithmeticOrder :
  Antisymmetric _ eq ArithmeticOrder.
Proof.
  now do 2 inversion 1; subst.
Qed.

Lemma Total_ArithmeticOrder :
  forall r s : Quantity,
    ArithmeticOrder r s \/ ArithmeticOrder s r.
Proof.
  now intros [] []; cbn; firstorder.
Qed.

#[refine, export] Instance Decidable_ArithmeticOrder :
  forall r s : Quantity,
    Decidable (ArithmeticOrder r s) :=
{
  Decidable_witness :=
    match r, s with
    | Zero, _    => true
    | _   , Any  => true
    | One , Few  => true
    | One , Many => true
    | Few , Many => true
    | _   , _    => decide (r = s)
    end;
}.
Proof.
  now destruct r, s; cbn.
Defined.

(** ** Trait order *)

Inductive TraitOrder : Quantity -> Quantity -> Prop :=
| TraitOrder_refl     : forall r : Quantity, TraitOrder r r
| TraitOrder_Any_l    : forall r : Quantity, TraitOrder Any r
| TraitOrder_Zero_r   : forall r : Quantity, TraitOrder r Zero
| TraitOrder_Few_One  : TraitOrder Few One
| TraitOrder_Many_One : TraitOrder Many One
| TraitOrder_One_Zero : TraitOrder One Zero.

#[export] Hint Constructors TraitOrder : core.

#[export] Instance PreOrder_TraitOrder :
  PreOrder TraitOrder.
Proof.
  split; red.
  - easy.
  - now do 2 inversion 1; subst.
Qed.

#[export] Instance Antisymmetric_TraitOrder :
  Antisymmetric _ eq TraitOrder.
Proof.
  now do 2 inversion 1; subst.
Qed.

#[refine, export] Instance Decidable_TraitOrder :
  forall r s : Quantity,
    Decidable (TraitOrder r s) :=
{
  Decidable_witness :=
    match r, s with
    | Any , _    => true
    | _   , Zero => true
    | Few , One  => true
    | Many, One  => true
    | _   , _    => decide (r = s)
    end;
}.
Proof.
  now destruct r, s; cbn.
Defined.

Lemma TraitOrder_complement :
  forall r s : Quantity,
    TraitOrder r s -> s = Zero \/ TraitOrder (complement s) (complement r).
Proof.
  now intros r []; inversion 1; cbn; firstorder.
Qed.

(** ** Relationships between orders *)

Lemma TraitOrder_Subusage :
  forall r s : Quantity,
    Subusage r s -> TraitOrder r s.
Proof.
  now inversion 1.
Qed.

Lemma SubtractionOrder_ArithmeticOrder :
  forall r s : Quantity,
    ArithmeticOrder r s -> SubtractionOrder r s.
Proof.
  now inversion 1.
Qed.

Lemma SubtractionOrder_DecrementationOrder :
  forall r s : Quantity,
    DecrementationOrder r s -> SubtractionOrder r s.
Proof.
  now inversion 1.
Qed.

(** ** Alternative definition of [sup] *)

Definition sup' (r s : Quantity) : option Quantity :=
match r, s with
| Zero, One  => None
| Zero, Many => None
| One , Zero => None
| Many, Zero => None
| _   , _    => Some (complement (mul (complement r) (complement s)))
end.

Lemma sup'_spec :
  forall r s : Quantity,
    sup' r s = sup r s.
Proof.
  now intros [] []; cbn.
Qed.

(** * Trait-checking division *)

Definition div (r s : Quantity) : option Quantity :=
match r, s with
| Zero, _    => Some Zero
| _   , Zero => None
| Any , r    => Some (complement r)
| _   , _    => if decide (TraitOrder s r) then Some One else Some r
end.

Definition div' (r s : Quantity) : option Quantity :=
match r, s with
| Zero, _    => Some Zero
| _   , Zero => None
| Any , r    => Some (complement r)
| _   , _    => if decide (Subusage s r) then Some One else Some r
end.

Definition div'' (r s : Quantity) : option Quantity :=
match r, s with
| Zero, _    => Some Zero
| _   , Zero => None
| Any , r    => Some (complement r)
| One , _    => Some One
| Few , Any  => Some One
| Few , Few  => Some One
| Many, Any  => Some One
| Many, Many => Some One
| _   , _    => Some r
end.

Lemma div'_spec :
  forall r s : Quantity,
    div' r s = div r s.
Proof.
  now intros [] []; cbn.
Qed.

Lemma div_spec :
  forall r s rs : Quantity,
    div r s = Some rs
      <->
    TraitOrder (mul rs s) r /\
    forall t : Quantity, TraitOrder (mul t s) r -> TraitOrder t rs.
Proof.
  split.
  - split.
    + now destruct r, s; inversion H; subst; cbn.
    + now destruct r, s, t; inversion H; subst; cbn in *.
  - intros [Hex Huniq].
    now destruct r, s, rs; cbn in *; try easy;
      try match goal with
      | H : forall _, TraitOrder _ _ -> TraitOrder _ _ |- _ =>
        specialize (H Many ltac:(easy)) +
        specialize (H Few  ltac:(easy)) +
        specialize (H Zero ltac:(easy));
          now inversion H
      end.
Qed.

(** * Division with remainder *)

Definition divmod (r s : Quantity) : Quantity * Quantity :=
match r, s with
| _   , Zero => (Any , r)
| _   , One  => (r   , Zero)
| Zero, _    => (Zero, Zero)
| One , _    => (Zero, One)
| Any , _    => (Any , Zero)
| Few , Few  => (Few , Zero)
| Few , _    => (Zero, Few)
| Many, Few  => (Any , One)
| Many, Many => (Many, Zero)
| Many, Any  => (Any , One)
end.

Lemma divmod_Zero_r :
  forall r : Quantity,
    divmod r Zero = (Any, r).
Proof.
  now intros []; cbn.
Qed.

Lemma divmod_One_r :
  forall r : Quantity,
    divmod r One = (r, Zero).
Proof.
  now intros []; cbn.
Qed.

Lemma divmod_spec :
  forall r s a b : Quantity,
    divmod r s = (a, b) ->
      r = add (mul a s) b.
Proof.
  now intros [] [] a b [= <- <-]; cbn.
Qed.

Lemma SubtractionOrder_divmod_1 :
  forall r s a b : Quantity,
    divmod r s = (a, b) ->
    forall a' b' : Quantity,
      r = add (mul a' s) b' -> SubtractionOrder a' a.
Proof.
  now intros [] [] a b [= <- <-] [] []; cbn.
Qed.

Lemma SubtractionOrder_divmod_2 :
  forall r s a b : Quantity,
    divmod r s = (a, b) ->
    forall a' b' : Quantity,
      r = add (mul a' s) b' -> SubtractionOrder b b'.
Proof.
  now intros [] [] a b [= <- <-] [] []; cbn.
Qed.

Lemma SubtractionOrder_divmod_2' :
  forall r s a b : Quantity,
    divmod r s = (a, b) ->
    forall a' b' : Quantity,
      r = add (mul a' s) b' ->
        SubtractionOrder a' a /\ SubtractionOrder b b'.
Proof.
   now intros [] [] a b [= <- <-] [] []; cbn; firstorder.
Qed.

Lemma divmod_spec' :
  forall r s a b : Quantity,
    divmod r s = (a, b)
      <->
    r = add (mul a s) b /\
    forall a' b' : Quantity,
      r = add (mul a' s) b' ->
        SubtractionOrder a' a /\ SubtractionOrder b b'.
Proof.
  split.
  - split; [| split].
    + now apply divmod_spec.
    + now eapply SubtractionOrder_divmod_1; eauto.
    + now eapply SubtractionOrder_divmod_2; eauto.
  - intros [-> H].
    destruct s.
    + specialize (H Any b).
      rewrite !mul_Zero_r, add_Zero_l in H.
      specialize (H eq_refl).
      rewrite mul_Zero_r, add_Zero_l.
      rewrite divmod_Zero_r.
      destruct H.
Abort.