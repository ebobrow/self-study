Require Import stlc fintype.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition context n := fin n -> ty.

(* TODO: why is notation like `.:` not working? *)
Inductive has_ty {n} : context n -> tm n -> ty -> Prop :=
  | TVar : forall c x, has_ty c (var_tm x) (c x)
  | TLam : forall c t x T1 T2,
      has_ty (scons T1 c) t T2 -> has_ty c (Lam x t) (Fun T1 T2)
  | TApp : forall t1 t2 c T1 T2,
      has_ty c t2 T1 -> has_ty c t1 (Fun T1 T2) -> has_ty c (App t1 t2) T2.
