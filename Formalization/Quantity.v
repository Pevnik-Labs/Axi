Require Import Bool.

Inductive Qty : Type :=
| Zero
| One
| Few
| Many
| Any.

Definition subusageb (r s : Qty) : bool :=
match r, s with
| Any , _    => true
| Many, Any  => false
| Many, Few  => false
| Many, Zero => false
| Many, _    => true
| Few , Any  => false
| Few , Many => false
| Few , _    => true
| One , One  => true
| One , _    => false
| Zero, Zero => true
| Zero, _    => false
end.

Module try1.

Inductive subusage : Qty -> Qty -> Prop :=
| subusage_refl : forall r : Qty, subusage r r
| subusage_Any_l : forall r : Qty, subusage Any r
| subusage_One_r : forall r : Qty, r <> Zero -> subusage r One
| subusage_Few_Zero : subusage Few Zero.

Lemma subusage_refl' :
  forall r : Qty,
    subusage r r.
Proof.
  now constructor.
Qed.

Lemma subusage_trans :
  forall r s t : Qty,
    subusage r s -> subusage s t -> subusage r t.
Proof.
  now intros r s t []; inversion 1; constructor. (* 12 cases *)
Qed.

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

End try1.

Module try2.

Inductive subusage : Qty -> Qty -> Prop :=
| subusage_refl : forall r : Qty, subusage r r
| subusage_Any_l : forall r : Qty, subusage Any r
| subusage_Many_One : subusage Many One
| subusage_Few_One : subusage Few One
| subusage_Few_Zero : subusage Few Zero.

Lemma subusage_refl' :
  forall r : Qty,
    subusage r r.
Proof.
  now constructor.
Qed.

Lemma subusage_trans :
  forall r s t : Qty,
    subusage r s -> subusage s t -> subusage r t.
Proof.
  now intros r s t []; inversion 1; constructor. (* 13 cases *)
Qed.

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

End try2.

Module try3.

Inductive subusage_step : Qty -> Qty -> Prop :=
| subusage_step_Any_Many : subusage_step Any Many
| subusage_step_Any_Few  : subusage_step Any Few
| subusage_step_Many_One : subusage_step Many One
| subusage_step_Few_One  : subusage_step Few One
| subusage_step_Few_Zero : subusage_step Few Zero.

Inductive subusage : Qty -> Qty -> Prop :=
| subusage_refl : forall r : Qty, subusage r r
| subusage_once : forall r s : Qty, subusage_step r s -> subusage r s
| subusage_twice : forall r s t : Qty, subusage_step r s -> subusage_step s t -> subusage r t.

Lemma subusage_refl' :
  forall r : Qty,
    subusage r r.
Proof.
  now constructor.
Qed.

Lemma subusage_trans :
  forall r s t : Qty,
    subusage r s -> subusage s t -> subusage r t.
Proof.
  intros r s t []; inversion 1; subst.
Abort.

Lemma subusageb_spec :
  forall r s : Qty,
    reflect (subusage r s) (subusageb r s).
Proof.
  intros [] []; cbn; constructor;
    match goal with
    | |- ~ _ => inversion 1
    | _ => constructor
    end.
Abort.

End try3.

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

Lemma add_Zero_inv :
  forall r s : Qty,
    add r s = Zero -> r = Zero /\ s = Zero.
Proof.
  now intros [] []; cbn.
Qed.

Lemma mul_Zero_inv :
  forall r s : Qty,
    mul r s = Zero -> r = Zero \/ s = Zero.
Proof.
  now intros [] []; cbn; inversion 1; auto.
Qed.