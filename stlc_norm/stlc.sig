tm : Type
ty : Type

Lam : ty -> (bind tm in tm) -> tm
App : tm -> tm -> tm

Fun : ty -> ty -> ty
Unit : ty
