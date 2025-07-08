(** * Quantities *)
Require Import Bool Coq.Classes.RelationClasses.

Inductive Qty : Type :=
| Zero
| One
| Few
| Many
| Any.

Definition qty_eq_dec (r s : Qty) : bool :=
match r, s with
| Zero, Zero => true
| One , One  => true
| Few , Few  => true
| Many, Many => true
| Any , Any  => true
| _   , _    => false
end.

Lemma qty_eq_dec_spec :
  forall r s : Qty,
    reflect (r = s) (qty_eq_dec r s).
Proof.
  now intros [] []; cbn; constructor;
    match goal with
    | |- _ = _ => reflexivity
    | |- _ <> _ => inversion 1
    end.
Qed.

(** * Subusage ordering *)

Inductive subusage : Qty -> Qty -> Prop :=
| subusage_refl : forall r : Qty, subusage r r
| subusage_Any_l : forall r : Qty, subusage Any r
| subusage_Many_One : subusage Many One
| subusage_Few_One : subusage Few One
| subusage_Few_Zero : subusage Few Zero.

#[export] Instance Reflexive_subusage :
  Reflexive subusage.
Proof.
  now constructor.
Qed.

#[export] Instance Transitive_subusage :
  Transitive subusage.
Proof.
  now intros r s t []; inversion 1; constructor.
Qed.

#[export] Instance Antisymmetric_subusage :
  Antisymmetric _ eq subusage.
Proof.
  now intros r s []; inversion 1.
Qed.

Definition subusageb (r s : Qty) : bool :=
match r, s with
| Any , _    => true
| Many, One  => true
| Few , One  => true
| Few , Zero => true
| _   , _    => qty_eq_dec r s
end.

Lemma subusageb_spec :
  forall r s : Qty,
    reflect (subusage r s) (subusageb r s).
Proof.
  now intros [] []; cbn; constructor;
    match goal with
    | |- ~ _ => inversion 1
    | _ => constructor
    end.
Qed.

Inductive subusage' : Qty -> Qty -> Prop :=
| subusage'_refl : forall r : Qty, subusage' r r
| subusage'_Any_l : forall r : Qty, subusage' Any r
| subusage'_One_r : forall r : Qty, r <> Zero -> subusage' r One
| subusage'_Few_Zero : subusage' Few Zero.

Lemma subusage'_spec :
  forall r s : Qty,
    subusage' r s <-> subusage r s.
Proof.
  split.
  - inversion 1; subst; try constructor.
    now destruct r; [congruence | constructor..].
  - now inversion 1; subst; constructor; congruence.
Qed.

(** * Addition *)

Definition add (r s : Qty) : Qty :=
match r, s with
| Zero, _    => s
| _   , Zero => r
| Few , Few  => Any
| Few , Any  => Any
| Any , Few  => Any
| Any , Any  => Any
| _   , _    => Many
end.

Lemma add_assoc :
  forall r s t : Qty,
    add (add r s) t = add r (add s t).
Proof.
  now intros [] [] []; cbn; easy.
Qed.

Lemma add_comm :
  forall r s : Qty,
    add r s = add s r.
Proof.
  now intros [] []; cbn.
Qed.

Lemma add_Zero_l :
  forall r : Qty,
    add Zero r = r.
Proof.
  easy.
Qed.

Lemma add_Zero_r :
  forall r : Qty,
    add r Zero = r.
Proof.
  now intros [].
Qed.

Lemma add_Many_l :
  forall r : Qty,
    add Many r = Many.
Proof.
  now intros []; cbn.
Qed.

Lemma add_Many_r :
  forall r : Qty,
    add r Many = Many.
Proof.
  now intros []; cbn.
Qed.

Lemma add_Zero_inv :
  forall r s : Qty,
    add r s = Zero -> r = Zero /\ s = Zero.
Proof.
  now intros [] []; cbn.
Qed.

#[export] Hint Rewrite add_Zero_l add_Zero_r add_Many_l add_Many_r : qty.

Lemma subusage_add_l :
  forall r1 r2 s : Qty,
    subusage r1 r2 -> subusage (add r1 s) (add r2 s).
Proof.
  intros r1 r2 []; inversion 1; subst; cbn; try constructor.
  - now destruct r2; constructor.
  - now destruct r2; constructor.
Qed.

Lemma subusage'_add_l :
  forall r1 r2 s : Qty,
    subusage' r1 r2 -> subusage' (add r1 s) (add r2 s).
Proof.
  inversion 1; subst.
  - now constructor.
  - now destruct r2, s; cbn; constructor; congruence.
  - now destruct r1, s; cbn; try constructor; congruence.
  - now destruct s; cbn; constructor.
Qed.

Lemma subusage_add_r :
  forall r s1 s2 : Qty,
    subusage s1 s2 -> subusage (add r s1) (add r s2).
Proof.
  intros [] s1 s2; inversion 1; subst; cbn; try constructor.
  - now destruct s2; cbn; constructor.
  - now destruct s2; cbn; constructor.
Qed.

Lemma subusage_add :
  forall r1 r2 s1 s2 : Qty,
    subusage r1 r2 -> subusage s1 s2 -> subusage (add r1 s1) (add r2 s2).
Proof.
  intros.
  transitivity (add r2 s1).
  - now apply subusage_add_l.
  - now apply subusage_add_r.
Qed.

(** * Multiplication *)

Definition mul (r s : Qty) : Qty :=
match r, s with
| Zero, _    => Zero
| _   , Zero => Zero
| One , _    => s
| _   , One  => r
| Few , Few  => Few
| Many, Many => Many
| _   , _    => Any
end.

Lemma mul_assoc :
  forall r s t : Qty,
    mul (mul r s) t = mul r (mul s t).
Proof.
  now intros [] [] []; cbn; easy.
Qed.

Lemma mul_comm :
  forall r s : Qty,
    mul r s = mul s r.
Proof.
  now intros [] []; cbn.
Qed.

Lemma mul_One_l :
  forall r : Qty,
    mul One r = r.
Proof.
  now intros [].
Qed.

Lemma mul_One_r :
  forall r : Qty,
    mul r One = r.
Proof.
  now intros [].
Qed.

Lemma mul_Zero_l :
  forall r : Qty,
    mul Zero r = Zero.
Proof.
  now intros [].
Qed.

Lemma mul_Zero_r :
  forall r : Qty,
    mul r Zero = Zero.
Proof.
  now intros [].
Qed.

Lemma mul_add_l :
  forall r s t : Qty,
    mul r (add s t) = add (mul r s) (mul r t).
Proof.
  now intros [] [] []; cbn.
Qed.

Lemma mul_add_r :
  forall r s t : Qty,
    mul (add r s) t = add (mul r t) (mul s t).
Proof.
  now intros [] [] []; cbn.
Qed.

Lemma mul_Zero_inv :
  forall r s : Qty,
    mul r s = Zero -> r = Zero \/ s = Zero.
Proof.
  now intros [] []; cbn; inversion 1; auto.
Qed.

Lemma subusage_mul_l :
  forall r1 r2 s : Qty,
    subusage r1 r2 -> subusage (mul r1 s) (mul r2 s).
Proof.
  intros r1 r2 []; inversion 1; subst; cbn; try constructor.
  rewrite mul_Zero_r.
  now constructor.
Qed.

Lemma subusage_mul_r :
  forall r s1 s2 : Qty,
    subusage s1 s2 -> subusage (mul r s1) (mul r s2).
Proof.
  intros [] s1 s2; inversion 1; subst; cbn; try constructor.
Qed.

Lemma subusage_mul :
  forall r1 r2 s1 s2 : Qty,
    subusage r1 r2 -> subusage s1 s2 -> subusage (mul r1 s1) (mul r2 s2).
Proof.
  intros.
  transitivity (mul r2 s1).
  - now apply subusage_mul_l.
  - now apply subusage_mul_r.
Qed.

(** * Greatest lower bound *)

Definition glb (r s : Qty) : Qty :=
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

Lemma glb_Any_l :
  forall r : Qty,
    glb Any r = Any.
Proof.
  easy.
Qed.

Lemma glb_Any_r :
  forall r : Qty,
    glb r Any = Any.
Proof.
  now intros []; cbn.
Qed.

Lemma glb_idem :
  forall r : Qty,
    glb r r = r.
Proof.
  now intros []; cbn.
Qed.

Lemma glb_comm :
  forall r s : Qty,
    glb r s = glb s r.
Proof.
  now intros [] []; cbn.
Qed.

Lemma glb_assoc :
  forall r s t : Qty,
    glb (glb r s) t = glb r (glb s t).
Proof.
  now intros [] [] []; cbn.
Qed.

Lemma subusage_glb_glb_l :
  forall r1 r2 s : Qty,
    subusage r1 r2 -> subusage (glb r1 s) (glb r2 s).
Proof.
  now intros [] [] []; cbn; inversion 1; constructor.
Qed.

Lemma subusage_glb_glb_r :
  forall r s1 s2 : Qty,
    subusage s1 s2 -> subusage (glb r s1) (glb r s2).
Proof.
  now intros [] [] []; cbn; inversion 1; constructor.
Qed.

Lemma subusage_glb_glb :
  forall r1 r2 s1 s2 : Qty,
    subusage r1 r2 -> subusage s1 s2 -> subusage (glb r1 s1) (glb r2 s2).
Proof.
  intros.
  transitivity (glb r2 s1).
  - now apply subusage_glb_glb_l.
  - now apply subusage_glb_glb_r.
Qed.

Lemma subusage_glb_l_l :
  forall r s : Qty,
    subusage (glb r s) r.
Proof.
  now intros [] []; cbn; constructor.
Qed.

Lemma subusage_glb_l_r :
  forall r s : Qty,
    subusage (glb r s) s.
Proof.
  now intros [] []; cbn; constructor.
Qed.

Lemma subusage_glb_r :
  forall r s t : Qty,
    subusage r s -> subusage r t -> subusage r (glb s t).
Proof.
  now intros [] [] []; do 2 inversion 1; subst; cbn; constructor.
Qed.

Lemma glb_spec :
  forall r s rs : Qty,
    glb r s = rs
      <->
    subusage rs r /\
    subusage rs s /\
    forall t : Qty, subusage t r -> subusage t s -> subusage t rs.
Proof.
  split.
  - intros <-.
    repeat split.
    + now apply subusage_glb_l_l.
    + now apply subusage_glb_l_r.
    + now intros; apply subusage_glb_r.
  - intros (Htr & Hts & Huniq).
    apply Antisymmetric_subusage.
    + apply Huniq.
      * now apply subusage_glb_l_l.
      * now apply subusage_glb_l_r.
    + now apply subusage_glb_r.
Qed.

Lemma subusageb_glb :
  forall r s : Qty,
    subusageb r s = true <-> glb r s = r.
Proof.
  now intros [] []; cbn; firstorder congruence.
Qed.

(** * Least upper bound *)

Definition lub (r s : Qty) : option Qty :=
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

Lemma lub_Any_l :
  forall r : Qty,
    lub Any r = Some r.
Proof.
  easy.
Qed.

Lemma lub_Any_r :
  forall r : Qty,
    lub r Any = Some r.
Proof.
  now intros []; cbn.
Qed.

Lemma lub_idem :
  forall r : Qty,
    lub r r = Some r.
Proof.
  now intros []; cbn.
Qed.

Lemma lub_comm :
  forall r s : Qty,
    lub r s = lub s r.
Proof.
  now intros [] []; cbn.
Qed.

Lemma lub_assoc :
  forall r s t rs st : Qty,
    lub r s = Some rs -> lub s t = Some st ->
      lub rs t = lub r st.
Proof.
  now intros [] [] [] rs st; cbn; do 2 inversion 1; cbn.
Qed.

Lemma subusage_lub_lub_l :
  forall r1 r2 s r1s r2s : Qty,
    lub r1 s = Some r1s -> lub r2 s = Some r2s ->
      subusage r1 r2 -> subusage r1s r2s.
Proof.
  now intros [] [] []; cbn; do 3 inversion 1; constructor.
Qed.

Lemma subusage_lub_lub_r :
  forall r s1 s2 rs1 rs2 : Qty,
    lub r s1 = Some rs1 -> lub r s2 = Some rs2 ->
      subusage s1 s2 -> subusage rs1 rs2.
Proof.
  now intros [] [] []; cbn; do 3 inversion 1; constructor.
Qed.

Lemma lub_defined_subusage :
  forall r1 r2 s r2s : Qty,
    lub r2 s = Some r2s -> subusage r1 r2 ->
      exists r1s : Qty, lub r1 s = Some r1s.
Proof.
  now intros r1 [] []; cbn; do 2 inversion 1; subst; cbn; eauto.
Qed.

Lemma subusage_lub_lub :
  forall r1 r2 s1 s2 r1s1 r2s2 : Qty,
    lub r1 s1 = Some r1s1 -> lub r2 s2 = Some r2s2 ->
      subusage r1 r2 -> subusage s1 s2 -> subusage r1s1 r2s2.
Proof.
  intros * H1 H2 Hr Hs.
  destruct (lub_defined_subusage r1 r2 s2 _ H2 Hr) as [r1s2 H].
  transitivity r1s2.
  - now eapply subusage_lub_lub_r; eauto.
  - now eapply subusage_lub_lub_l; eauto.
Qed.

Lemma subusage_lub_r_l :
  forall r s rs : Qty,
    lub r s = Some rs ->
      subusage r rs.
Proof.
  now intros [] [] rs; inversion 1; cbn; constructor.
Qed.

Lemma subusage_lub_r_r :
  forall r s rs : Qty,
    lub r s = Some rs ->
      subusage s rs.
Proof.
  now intros [] [] rs; inversion 1; cbn; constructor.
Qed.

Lemma subusage_lub_l :
  forall r s t rs : Qty,
    lub r s = Some rs ->
      subusage r t -> subusage s t -> subusage rs t.
Proof.
  now intros [] [] []; do 3 inversion 1; subst; cbn; constructor.
Qed.

Lemma lub_spec :
  forall r s rs : Qty,
    lub r s = Some rs
      <->
    subusage r rs /\
    subusage s rs /\
    forall t : Qty, subusage r t -> subusage s t -> subusage rs t.
Proof.
  split.
  - intros Hlub; repeat split.
    + now apply subusage_lub_r_l in Hlub.
    + now apply subusage_lub_r_r in Hlub.
    + now intros; apply subusage_lub_l with r s.
  - intros (Htr & Hts & Huniq).
    destruct r, s; cbn; inversion Htr; inversion Hts; subst; try congruence;
      try match goal with
      | H : forall _, _ -> _ -> subusage One _ |- _ =>
        now cut (subusage One Zero); [inversion 1 | apply H; constructor]
      | H : forall _, _ -> _ -> subusage One _ |- _ =>
        now cut (subusage One Many); [inversion 1 | apply H; constructor]
      | H : forall _, _ -> _ -> subusage Zero _ |- _ =>
        now cut (subusage Zero One); [inversion 1 | apply H; constructor]
      end.
    f_equal.
    apply Antisymmetric_subusage; [easy |].
    now apply Huniq; constructor.
Qed.

Lemma subusageb_lub :
  forall r s : Qty,
    subusageb r s = true <-> lub r s = Some s.
Proof.
  now intros [] []; cbn; firstorder congruence.
Qed.

Lemma lub_glb_l :
  forall r s : Qty,
    lub (glb r s) s = Some s.
Proof.
  now intros [] []; cbn.
Qed.

Lemma lub_glb_r :
  forall r s : Qty,
    lub r (glb r s) = Some r.
Proof.
  now intros [] []; cbn.
Qed.

Lemma glb_lub_r :
  forall r s rs : Qty,
    lub r s = Some rs ->
      glb rs s = s.
Proof.
  now intros [] [] rs; cbn; inversion 1; subst; cbn.
Qed.

(** * Subtraction *)

Definition sub (r s : Qty) : option Qty :=
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
  forall r s rs : Qty,
    sub r s = Some rs ->
      subusage r (add rs s).
Proof.
  now intros [] [] rs; cbn; inversion 1; subst; cbn; constructor.
Qed.

Lemma sub_spec_uniq :
  forall r s rs : Qty,
    sub r s = Some rs ->
      forall t : Qty, subusage r (add t s) -> subusage rs t.
Proof.
  now intros [] [] rs; inversion 1; intros []; inversion 1; subst; cbn; constructor.
Qed.

Lemma subusage_sub_Zero :
  forall r rr : Qty,
    sub r r = Some rr ->
      subusage rr Zero.
Proof.
  now intros [] rr; inversion 1; constructor.
Qed.

(** * Miscellaneous orderings *)

Inductive SubtractionOrder : Qty -> Qty -> Prop :=
| SubtractionOrder_refl    : forall r : Qty, SubtractionOrder r r
| SubtractionOrder_Zero_l  : forall r : Qty, SubtractionOrder Zero r
| SubtractionOrder_Many_r  : forall r : Qty, SubtractionOrder r Many
| SubtractionOrder_Any_r   : forall r : Qty, SubtractionOrder r Any
| SubtractionOrder_One_Few : SubtractionOrder One Few.

Lemma SubtractionOrder_spec :
  forall r s : Qty,
    SubtractionOrder r s <-> sub s r <> None.
Proof.
  now intros [] []; cbn; (split; [inversion 1 |]); congruence + constructor.
Qed.

Inductive DecrementationOrder : Qty -> Qty -> Prop :=
| DecrementationOrder_Zero_One : DecrementationOrder Zero One
| DecrementationOrder_Zero_Few : DecrementationOrder Zero Few
| DecrementationOrder_Any_Many : DecrementationOrder Any Many
| DecrementationOrder_Any_Any : DecrementationOrder Any Any.

Lemma DecrementationOrder_spec :
  forall r s : Qty,
    DecrementationOrder r s <-> sub s One = Some r.
Proof.
  intros [] []; cbn; (split; [inversion 1 |]); congruence + constructor.
Qed.

Inductive ArithmeticOrder : Qty -> Qty -> Prop :=
| ArithmeticOrder_refl     : forall r : Qty, ArithmeticOrder r r
| ArithmeticOrder_Zero_l   : forall r : Qty, ArithmeticOrder Zero r
| ArithmeticOrder_Any_r    : forall r : Qty, ArithmeticOrder r Any
| ArithmeticOrder_One_Few  : ArithmeticOrder One Few
| ArithmeticOrder_One_Many : ArithmeticOrder One Many
| ArithmeticOrder_Few_Many : ArithmeticOrder Few Many.

(** * Trait-checking division *)

Definition div (r s : Qty) : option Qty :=
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
