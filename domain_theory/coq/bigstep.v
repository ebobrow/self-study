Require Export pcf typing.
Require Import ssreflect.

Inductive value {n} : exp n -> Prop :=
  | VZero : value Zero
  | VSucc : forall v, value v -> value (Succ v)
  | VTrue : value tt
  | VFalse : value ff
  | VFn : forall t m, value (Fn t m).

Inductive bigstep : forall n, ty -> exp n -> exp n -> Prop :=
  | SVal : forall v t, value v -> has_type null v t -> bigstep 0 t v v
  | SSucc : forall n m v, bigstep n Nat m v -> bigstep n Nat (Succ m) (Succ v)
  | SPred : forall n m v, bigstep n Nat m (Succ v) -> bigstep n Nat (Pred m) v
  | SZero1 : forall n m, bigstep n Nat m Zero -> bigstep n Bool (IsZero m) tt
  | SZero2 : forall n m v, bigstep n Nat m (Succ v) -> bigstep n Bool (IsZero m) ff
  | SIf1 : forall n m1 m2 m3 v t,
      bigstep n Bool m1 tt ->
      bigstep n t m2 v ->
      bigstep n t (If m1 m2 m3) v
  | SIf2 : forall n m1 m2 m3 v t,
      bigstep n Bool m1 ff ->
      bigstep n t m3 v ->
      bigstep n t (If m1 m2 m3) v
  | SCbn : forall n m1 m2 m1' v t t',
      bigstep n (Arr t t') m1 (Fn t m1') ->
      bigstep n t' (subst_exp (m2..) m1') v ->
      bigstep n t' (App m1 m2) v
  | SFix : forall n m v t,
      bigstep n t (App m (Fix m)) v ->
      bigstep n t (Fix m) v.

Hint Constructors bigstep : core.

Lemma eval_deterministic : forall n m t v v',
  bigstep n t m v ->
  bigstep n t m v' ->
  v = v'.
Proof.
Admitted. (* oh boy *)
