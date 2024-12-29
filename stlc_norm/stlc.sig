tm : Type
ty : Type

T : tm
F : tm
If : tm -> tm -> tm -> tm
Lam : ty -> (tm -> tm) -> tm
App : tm -> tm -> tm

Fun : ty -> ty -> ty
Bool : ty
