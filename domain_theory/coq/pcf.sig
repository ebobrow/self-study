ty : Type
exp : Type

Nat : ty
Bool : ty
Arr : ty -> ty -> ty

Zero : exp
Succ : exp -> exp
Pred : exp -> exp
tt : exp
ff : exp
IsZero : exp -> exp
If : exp -> exp -> exp -> exp
Fn : ty -> (exp -> exp) -> exp
App : exp -> exp -> exp
Fix : exp -> exp
