Require Import ssreflect ssrfun ssrbool (* eqtype ssrnat div seq *).
(* Require Import path choice fintype tuple finfun finset. *)

(* Set Implicit Arguments. *)
Unset Strict Implicit.
Import Prenex Implicits.

Section Tauto.
  Variables A B C : Prop.

  Lemma tauto1 : A -> A.
  Proof. done. Qed.

  Lemma tauto2 : (A -> B) -> (B -> C) -> A -> C.
  Proof.
    (* Is there a way to do this without having to name Hab? *)
    by move=> Hab ? /Hab.
    (* move=> Hab Hbc Ha. apply: Hbc. by apply: Hab. *)
  Qed.

  Lemma tauto3 : A /\ B <-> B /\ A.
  Proof.
    (* is there a ssr-ism for `split`? *)
    split; by move=> [? ?].
  Qed.
End Tauto.

Section MoreBasics.
  Variables A B C : Prop.
  Variable P : nat -> Prop.

  Lemma foo1 : ~(exists x, P x) -> forall x, ~P x.
  Proof.
    rewrite /not.
    move=> H x Hx. apply: H.
    by exists x.
  Qed.

  Lemma foo2 : (exists x, A -> P x) -> (forall x, ~P x) -> ~A.
  Proof.
    rewrite/not.
    move=> [x Hx] /(_ x) H2 a. apply: H2. apply: Hx => //.
  Qed.
End MoreBasics.

Lemma forall_dist {T} : forall (P Q : T -> Prop), ((forall x, P x -> Q x) -> ((forall y, P y) -> forall z, Q z)).
Proof.
  move=> ? ? H1 *. by apply: H1.
Qed.

Inductive my_ex A (S : A -> Prop) : Prop := my_ex_intro x of S x.
Goal forall A (S : A -> Prop), my_ex A S <-> exists y, S y.
Proof.
  move=> A S. split.
  - case=> x. exists x => //.
  - case=> x H. apply (my_ex_intro _ _ x) => //.
Qed.

Lemma imp_trans4 P Q R S : (P -> Q) -> (Q -> R) -> (R -> S) -> P -> S.
Proof.
  move=>H1 H2 H3.
  by move/H1/H2/H3.
Qed.

Goal forall P Q R, P -> (P -> Q -> R) -> Q -> R.
Proof.
  move=> P Q R p.
  by move/(_ p).
Qed.
