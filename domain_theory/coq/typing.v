Require Export pcf.
Require Import ssreflect.

Definition context n := fin n -> ty.

Inductive has_type {n} (ctx : context n) : exp n -> ty -> Prop :=
  | TZero : has_type ctx Zero Nat
  | TSucc : forall m, has_type ctx m Nat -> has_type ctx (Succ m) Nat
  | TPred : forall m, has_type ctx m Nat -> has_type ctx (Pred m) Nat
  | TIsZero : forall m, has_type ctx m Nat -> has_type ctx (IsZero m) Bool
  | TTrue : has_type ctx tt Bool
  | TFalse : has_type ctx ff Bool
  | TIf : forall m1 m2 m3 t,
      has_type ctx m1 Bool ->
      has_type ctx m2 t ->
      has_type ctx m3 t ->
      has_type ctx (If m1 m2 m3) t
  | TVar : forall x, has_type ctx (var_exp x) (ctx x)
  | TFn : forall t t' m, has_type (t .: ctx) m t' -> has_type ctx (Fn t m) t'
  | FApp : forall m1 m2 t t',
      has_type ctx m1 (Arr t t') ->
      has_type ctx m2 t ->
      has_type ctx (App m1 m2) t'
  | TFix : forall m t, has_type ctx m (Arr t t) -> has_type ctx (Fix m) t.

Hint Constructors has_type : core.

Lemma typing_consistent : forall n ctx (m : exp n) t t',
  has_type ctx m t -> has_type ctx m t' -> t = t'.
Proof.
  move=>n ctx m t + Hty. elim: Hty;
    try (move=>> H; by inversion H);
    try (move=>> _ _ ? H; by inversion H).
  - move=>> _ _ _ _ _ ? ? H. inversion H. auto.
  - move=>> _ ? ? H. inversion H. auto.
  - move=>> _ Harr _ _ ? H. inversion H. apply Harr in H2. by inversion H2.
  - move=>> _ Harr ? H. inversion H. apply Harr in H1. by inversion H1.
Qed.

Lemma sub_extend : forall n (ctx : context n) m m' t t',
  has_type ctx m t ->
  has_type (t .: ctx) m' t' ->
  has_type ctx (@subst_exp (S n) n (m..) m') t'.
Proof.
Admitted. (* Something funky with the induction here *)
