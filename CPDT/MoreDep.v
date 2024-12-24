Require Import List.
Require Import Nat.
Require Import Cpdt.MoreSpecif.
Require Import Cpdt.CpdtTactics.
(* Set Implicit Arguments. *)

(* Section plist. *)
(*   Variable A : Set. *)
(*   Variable P : A -> Prop. *)

(*   Inductive plist : nat -> Set := *)
(*     | PNil : plist O *)
(*     | PConsUnsat : forall n, A -> plist n -> plist n *)
(*     | PConsSat : forall n a, P a -> plist n -> plist (S n). *)
(* End plist. *)
(* Inductive plist { A : Set } { P : A -> Prop } : nat -> Set := *)
(*   | PNil : plist O *)
(*   | PConsUnsat : forall n, A -> plist n -> plist n *)
(*   | PConsSat : forall n a, P a -> plist n -> plist (S n). *)

Definition big (n : nat) : Prop := n > 5.
Lemma ten_big : big 10.
Proof. repeat constructor. Qed.
Lemma nine_big : big 9.
Proof. repeat constructor. Qed.
Lemma eight_big : big 8.
Proof. repeat constructor. Qed.
(* Eval compute in PConsSat _ _ _ _ ten_big (PConsUnsat _ _ _ 1 (PNil _ _)). *)
(* Eval compute in PConsSat _ _ ten_big (PConsUnsat _ 1 PNil). *)

Inductive plist { A : Set } { P : A -> Prop } : nat -> Set :=
  | PNil : plist O
  | PConsUnsat { n : nat } : A -> plist n -> plist n
  | PConsSat { n : nat } : forall a, P a -> plist n -> plist (S n).
Eval compute in PConsSat _ ten_big (PConsUnsat 1 PNil).
Eval compute in PConsUnsat 10 (PConsUnsat 1 PNil).

Fixpoint plist_concat { A : Set } { P : A -> Prop } { n1 n2 }
  (p1 : @plist A P n1) (p2 : @plist A P n2) : @plist A P (n1 + n2) :=
  match p1 with
  | PNil => p2
  | PConsUnsat h t => PConsUnsat h (plist_concat t p2)
  | PConsSat h pf t => PConsSat h pf (plist_concat t p2)
  end.

Definition p1 := PConsSat _ ten_big (PConsUnsat 1 PNil).
Definition p2 := PConsSat _ nine_big (PConsUnsat 4 (PConsSat _ eight_big (PConsUnsat 2 PNil))).
Eval compute in plist_concat p1 p2.

Fixpoint plistOut {A P n} (p : @plist A P n) : list A :=
  match p with
  | PNil => nil
  | PConsUnsat h t => h :: plistOut t
  | PConsSat h _ t => h :: plistOut t
  end.
Eval compute in plistOut (plist_concat p1 p2).

Definition prop_dec { A : Set} (P : A -> Prop) := forall a, { P a } + { ~ P a }.
Fixpoint numSat { A : Set } { P : A -> Prop } (ls : list A) (dec : prop_dec P) : nat :=
  match ls with
  | nil => 0
  | h :: t => let numT := numSat t dec in
      if dec h then 1 + numT else numT
  end.

Fixpoint plistIn { A : Set } { P : A -> Prop } (ls : list A) (dec : prop_dec P) :
  @plist A P (numSat ls dec) :=
  match ls with
  | nil => PNil
  | h :: t => match dec h as sat return plist (if sat then S (numSat t dec) else numSat t dec) with
              | left pf => PConsSat h pf (plistIn t dec)
              | right _ => PConsUnsat h (plistIn t dec)
              end
  end.

Local Open Scope specif_scope.
Definition big_dec : forall n, {big n} + {~ big n}.
Proof.
  intros. destruct (5 <? n) eqn:E;
  match goal with
  | [ E: _ = true |- _ ] => apply PeanoNat.Nat.ltb_lt in E
  | [ E: _ = false |- _ ] => apply PeanoNat.Nat.ltb_nlt in E
  end; auto.
Defined.
Eval compute in plistIn (10 :: 2 :: 5 :: 8 :: nil) big_dec.

Lemma out_in {A : Set} {P : A -> Prop} : forall ls dec, @plistOut A P _ (plistIn ls dec) = ls.
Proof.
  induction ls.
  - reflexivity.
  - intros. destruct (dec a) eqn:E; crush.
Qed.

Fixpoint grab {A P n} (ls : @plist A P (S n)) : sig P :=
  match ls in plist n' return match n' with
                              | O => unit
                              | S _ => sig P
                              end with
  | PNil => tt
  | PConsSat x pf _ => exist _ x pf
  | @PConsUnsat _ _ O _ _ => tt
  | PConsUnsat _ ls' => grab ls'
  end.
Eval compute in grab (plistIn (2 :: 5 :: 8 :: nil) big_dec).
