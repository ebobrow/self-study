Require Import ssreflect ssrbool ssrfun.
From mathcomp Require Import finmap order eqtype choice.
Import Order.Theory.
Require Import Coq.Lists.List.
From HB Require Import structures.
From mathcomp Require Import tuple seq.

Open Scope order_scope.
Open Scope type_scope.
Open Scope fmap_scope.
Open Scope fset_scope.

Definition monotone {t} { D E : porderType t } (f : (D -> E)) : Prop :=
  forall d d', is_true (d <= d') -> is_true (f d <= f d').

Lemma const_mono : forall t D E e, @monotone t D E (fun _ => e).
Proof.
  unfold monotone. move=> *. apply lexx.
Qed.

Module tuplePOrder.
  Section tuplePOrder.
    Variable d : Order.disp_t.
    Variable T : porderType d.
    Variable n : nat.

    Definition cmp (x y : n.-tuple T) (op : T -> T -> bool) :=
      all (fun s => let: (h1, h2) := s in op h1 h2) (zip x y).
    Definition le (f g : n.-tuple T) := cmp f g <=%O.
    Definition lt (f g : n.-tuple T) := cmp f g <%O.

    Lemma lt_def : forall x y, lt x y = (y != x) && (le x y). Admitted.
    Lemma refl : reflexive le. Admitted.
    Lemma anti : antisymmetric le. Admitted.
    Lemma trans : transitive le. Admitted.

    HB.instance Definition what :=
      Order.isPOrder.Build d (n.-tuple T) lt_def refl anti trans.
  End tuplePOrder.
End tuplePOrder.

HB.instance Definition _ (d : Order.disp_t) (n : nat) (T : porderType d)
  : Order.isPOrder d (n.-tuple T) := tuplePOrder.what d T n.

Definition comp {n d} {T : porderType d} := {fmap n.-tuple T -> n.-tuple T}.

(* TODO: we want domain, not POrder--define domain first *)
(* Define chain: totally ordered subset *)
(* What is going on with subPOrder? *)
(* Then have `HB.structure Definition Domain (d : disp_t) :=
  { T of POrder d T & isChainComplete d T }. *)
Module compPOrder.
  Section compPOrder.
    Variable d : Order.disp_t.
    Variable D : choiceType.
    Variable E : porderType d.
    Variable n : nat.

    Definition cmp (f g : {fmap D -> E}) (op : E -> E -> bool) :=
      (fix F dom :=
        match dom with
        | nil => true
        | x :: dom' => match f.[?x], g.[?x] with
                       | None, _ => true
                       | Some _, None => false
                       | Some fx, Some gx => op fx gx
                       end && F dom'
        end) (enum_fset (domf f)).
    Definition le (f g : {fmap D -> E}) := cmp f g <=%O.
    Definition lt (f g : {fmap D -> E}) := cmp f g <%O.

    Lemma lt_def : forall x y, lt x y = (y != x) && (le x y). Admitted.
    Lemma refl : reflexive le. Admitted.
    Lemma anti : antisymmetric le. Admitted.
    Lemma trans : transitive le. Admitted.

    HB.instance Definition what :=
      Order.isPOrder.Build d {fmap D -> E} lt_def refl anti trans.
  End compPOrder.
End compPOrder.

HB.instance Definition _ (d : Order.disp_t) (n : nat) (D : choiceType) (E : porderType d)
  : Order.isPOrder d {fmap D -> E} := compPOrder.what d D E n.

(* Denotation of a while loop is w such that w = f w *)
From mathcomp Require Import fintype finset.
Definition fdom {n d} {T : finPOrderType d} (b : n.-tuple T -> bool) (c : @comp n d T) (w : @comp n d T)
  : {fset n.-tuple T} :=
  [fset s : n.-tuple T | ~~ b s || (match c.[?s] with
                                    | None => false
                                    | Some s' => s' \in w
                                    end)].
Definition f {n d} {T : finPOrderType d} (b : n.-tuple T -> bool) (c : comp)
  : comp -> comp := fun w => [fmap s : fdom b c w => if b (fsval s)
                                                   then match c.[? fsval s] with
                                                        | Some s' => match w.[? s'] with
                                                                     | Some s'' => s''
                                                                     | None => s' (* unreachable *)
                                                                     end
                                                        | None => fsval s (* unreachable *)
                                                        end
                                                    else fsval s].
Lemma f_mono {n d} {T : finPOrderType d} : forall b c,
  monotone (@f n d T b c).
