(** * Quantity *)

Require Export
  Bool
  Coq.Classes.RelationClasses
  Coq.Classes.DecidableClass.

(**
  [Quantity] is the type of quantities. Quantities express a crude measure of
  resource usage:
  - [Zero] means <<0>> uses
  - [One] means <<1>> use
  - [Few] means <<0>> or <<1>> use
  - [Many] means <<1>> or more uses
  - [Any] means <<0>> or more uses
*)

Inductive Quantity : Type :=
| Zero
| One
| Few
| Many
| Any.

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

(** * Subusage ordering *)

(** A picture is worth a thousand words: *)

(*
    0     1
     \   / \
      \ /   \
       ?     +
        \   /
         \ /
          *
*)
Inductive Subusage : Quantity -> Quantity -> Prop :=
| Subusage_refl     : forall r : Quantity, Subusage r r
| Subusage_Any_l    : forall r : Quantity, Subusage Any r
| Subusage_Many_One : Subusage Many One
| Subusage_Few_One  : Subusage Few One
| Subusage_Few_Zero : Subusage Few Zero.

#[export] Hint Constructors Subusage : core.

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
    destruct r, s; cbn;
      inversion Htr; subst; try congruence;
      inversion Hts; subst; try congruence;
      try match goal with
      | Huniq : forall _, _ -> _ -> Subusage One _ |- _ =>
          now cut (Subusage One Zero); [inversion 1 | apply Huniq]
      | Huniq : forall _, _ -> _ -> Subusage One _ |- _ =>
          now cut (Subusage One Many); [inversion 1 | apply Huniq]
      | Huniq : forall _, _ -> _ -> Subusage Zero _ |- _ =>
          now cut (Subusage Zero One); [inversion 1 | apply Huniq]
      end.
    now f_equal; apply Antisymmetric_Subusage; [| apply Huniq].
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

(** ** [inf] and [sup] *)

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

(** * Ordered semiring structure *)

(** ** Addition *)

Definition add (r s : Quantity) : Quantity :=
match r, s with
| Zero, _    => s
| _   , Zero => r
| Few , Few  => Any
| Few , Any  => Any
| Any , Few  => Any
| Any , Any  => Any
| _   , _    => Many
end.

(**
  [add] is associative and commutative.
  [Zero] is its identity and [Many] is its absorbing element.
*)

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

(** When the result of [add] is [Zero], both arguments also are [Zero]. *)

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

(** ** Multiplication *)

Definition mul (r s : Quantity) : Quantity :=
match r, s with
| Zero, _    => Zero
| _   , Zero => Zero
| One , _    => s
| _   , One  => r
| Few , Few  => Few
| Many, Many => Many
| _   , _    => Any
end.

(**
  [mul] is associative and commutative.
  [One] is its identity and [Zero] is its absorbing element.
*)

Lemma mul_One_l :
  forall r : Quantity,
    mul One r = r.
Proof.
  now intros []; cbn.
Qed.

Lemma mul_One_r :
  forall r : Quantity,
    mul r One = r.
Proof.
  now intros []; cbn.
Qed.

Lemma mul_Zero_l :
  forall r : Quantity,
    mul Zero r = Zero.
Proof.
  now intros []; cbn.
Qed.

Lemma mul_Zero_r :
  forall r : Quantity,
    mul r Zero = Zero.
Proof.
  now intros []; cbn.
Qed.

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

(** When the result of [mul] is [Zero], one of the arguments also is [Zero]. *)

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

(** ** [add] and [mul] *)

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
    | One , Zero => false
    | One , _    => true
    | _   , Many => true
    | _   , Any  => true
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
    | Any , Any  => true
    | Any , Many => true
    | Zero, One  => true
    | Zero, Few  => true
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

#[export] Instance Reflexive_ArithmeticOrder :
  Reflexive ArithmeticOrder.
Proof.
  easy.
Qed.

#[export] Instance Transitive_ArithmeticOrder :
  Transitive ArithmeticOrder.
Proof.
  now do 2 inversion 1; subst.
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
    | One , Zero => false
    | One , _    => true
    | Few , Zero => false
    | Few , One  => false
    | Few , _    => true
    | Any , Many => false
    | _   , Many => true
    | _   , Any  => true
    | _   , _    => decide (r = s)
    end;
}.
Proof.
  now destruct r, s; cbn.
Defined.

(** * Trait-checking division *)

Definition div (r s : Quantity) : option Quantity :=
match r, s with
| Zero, _    => Some Zero
| _   , Zero => None
| One , _    => Some One
| Any , _    => Some s
| Few , One  => Some Few
| Few , Many => Some Few
| Few , _    => Some One
| Many, One  => Some Many
| Many, Few  => Some Many
| Many, _    => Some One
end.

(** * Another division *)
