Require Export stlc.
Require Import ssreflect.

(* Set Implicit Arguments. *)
(* Unset Strict Implicit. *)
(* Unset Printing Implicit Defensive. *)

Definition context n := fin n -> ty.

Definition empty_ctx : context 0 :=
  fun x => match x with end.

Inductive value {n} : tm n -> Prop :=
  | VTrue : value T
  | VFalse : value F
  | VLam : forall typ t, value (Lam typ t).

Inductive has_ty {n} (ctx : context n) : tm n -> ty -> Prop :=
  | TVar : forall x, has_ty ctx (var_tm x) (ctx x)
  | TLam : forall t x T1 T2,
      has_ty (T1 .: ctx) t T2 -> has_ty ctx (Lam x t) (Fun T1 T2)
  | TApp : forall t1 t2 T1 T2,
      has_ty ctx t2 T1 -> has_ty ctx t1 (Fun T1 T2) -> has_ty ctx (App t1 t2) T2
  | TTrue : has_ty ctx T Bool
  | TFalse : has_ty ctx F Bool
  | TIf : forall t1 t2 t3 typ,
      has_ty ctx t1 Bool ->
      has_ty ctx t2 typ ->
      has_ty ctx t3 typ ->
      has_ty ctx (If t1 t2 t3) typ.

Hint Constructors has_ty : core.

Inductive big_step {n} : tm n -> tm n -> Prop :=
  | FunDone : forall type t, big_step (Lam type t) (Lam type t)
  | TDone : big_step T T
  | FDone : big_step F F
  | ST_App : forall e1 e2 e v v' type,
      big_step e1 (Lam type e) ->
      big_step e2 v ->
      big_step (subst_tm (v..) e) v' ->
      big_step (App e1 e2) v'
  | ST_IfT : forall e1 e2 e3 v,
      big_step e1 T ->
      big_step e2 v ->
      big_step (If e1 e2 e3) v
  | ST_IfF : forall e1 e2 e3 v,
      big_step e1 F ->
      big_step e3 v ->
      big_step (If e1 e2 e3) v.

Hint Constructors big_step : core.

Example test : big_step (App (Lam Bool ((@var_tm 1) var_zero)) T) T.
Proof. eauto. Qed.

Definition norm {n} (t : tm n) := exists t', big_step t t'.

Fixpoint N (type : ty) (t : tm 0) : Prop :=
  has_ty empty_ctx t type /\ norm t /\
  match type with
  | Bool => True
  | Fun t1 t2 => forall t', N t1 t' -> N t2 (App t t')
  end.

Lemma N_impl_norm : forall t type, N type t -> norm t.
Proof.
  move=> t type. elim: type => [_ _ _ _|] [_ [? _]] //.
Qed.

Lemma N_impl_type : forall t typ, N typ t -> has_ty empty_ctx t typ.
Proof.
  move=> t typ. by elim: typ => [? _ ? _|] [H _].
Qed.

Definition sub n m := fin n -> tm m.
Definition sub_ok_in {n} (sub : sub n 0) (ctx : context n) :=
  forall i, N (ctx i) (sub i).

Definition good_ren {n m} (ren : fin n -> fin m) (ctx : context n) ctx' :=
  forall i, ctx i = ctx' (ren i).
Definition good_sub {n m} (sub : sub n m) ctx ctx' :=
  forall i, has_ty ctx' (sub i) (ctx i).

Lemma good_ren_cons {n m} (ren : fin n -> fin m) ctx ctx' typ :
  good_ren ren ctx ctx' ->
  good_ren (up_ren ren) (typ .: ctx) (typ .: ctx').
Proof.
  rewrite /good_ren. move=> ?. by case.
Qed.

Lemma renaming {n} : forall e typ ctx m ctx' (ren : fin n -> fin m),
  has_ty ctx e typ ->
  good_ren ren ctx ctx' ->
  has_ty ctx' (ren_tm ren e) typ.
Proof.
  move=> e typ ctx + + + Hty. induction Hty; try (intros; asimpl; eauto).
  - rewrite /good_ren in H. by rewrite H.
  - asimpl. econstructor. eauto using good_ren_cons.
Qed.

Lemma weakening {n} : forall (t : tm n) typ typ' ctx,
  has_ty ctx t typ ->
  has_ty (typ' .: ctx) (ren_tm shift t) typ.
Proof.
  intros. eapply renaming; eauto. by unfold good_ren.
Qed.

Lemma good_sub_cons {n m} (sub : sub n m) ctx ctx' typ :
  good_sub sub ctx ctx' ->
  good_sub (up_tm sub) (typ .: ctx) (typ .: ctx').
Proof.
  unfold good_sub. intros. destruct i.
  - by apply weakening.
  - constructor.
Qed.

Lemma sub_ok_impl_good {n} : forall (s : sub n 0) ctx,
  sub_ok_in s ctx -> good_sub s ctx empty_ctx.
Proof.
  rewrite /sub_ok_in/good_sub. auto using N_impl_type.
Qed.

Lemma sub_ok_cons {n} : forall (s : sub n 0) ctx (t : tm 0) typ,
  sub_ok_in s ctx ->
  N typ t ->
  sub_ok_in (t .: s) (typ .: ctx).
Proof.
  rewrite /sub_ok_in. move=>> ? ? i. by case: i.
Qed.

Lemma morphing : forall n e m ctx ctx' (sub : sub n m) typ,
  has_ty ctx e typ ->
  good_sub sub ctx ctx' ->
  has_ty ctx' (subst_tm sub e) typ.
Proof.
  induction e; simpl; move=>> H; inversion H; eauto using good_sub_cons.
Qed.

Lemma preservation {n} : forall (t t' : tm n) typ ctx,
  big_step t t' ->
  has_ty ctx t typ ->
  has_ty ctx t' typ.
Proof.
  move=> t t' + + Hstep. induction Hstep => typ ctx Hty; inversion Hty; auto.
  apply IHHstep3. apply IHHstep1 in H3. inversion H3; subst.
  eapply morphing.
  + eassumption.
  + rewrite /good_sub. induction i; [constructor|auto].
Qed.

Lemma big_step_to_val {n} : forall (t v : tm n), big_step t v -> value v.
Proof.
  Hint Constructors value : core.
  induction 1; auto.
Qed.

Lemma N_backpreservation : forall typ t v,
  big_step t v ->
  N typ v ->
  N typ t.
Admitted.

Lemma N_preservation : forall typ t v,
  big_step t v ->
  N typ t ->
  N typ v.
Admitted.

Lemma canonical_forms_bool : forall v,
  value v ->
  has_ty empty_ctx v Bool ->
  (v = T \/ v = F).
Proof.
  intros. inversion H; auto.
  - subst. inversion H0.
Qed.

Lemma fundamental_lemma : forall ctx (t : tm 0) typ sub,
  has_ty ctx t typ ->
  sub_ok_in sub ctx ->
  N typ (subst_tm sub t).
Proof.
  move=> ctx t typ sub Hty.
  induction Hty.
  - done.
  - move=> Hsub. repeat split.
    + eauto using morphing, sub_ok_impl_good.
    + exists (subst_tm sub (Lam x t)). by simpl.
    + move=> t' /[dup] /N_impl_norm Hnorm HN. destruct Hnorm as [v Hv].
      assert (sub_ok_in (v .: sub) (T1 .: ctx)); eauto using sub_ok_cons, N_preservation.
      * apply IHHty in H. move: H => /[dup] /N_impl_norm Hnormt HNt. destruct Hnormt as [v' Hv'].
        -- simpl. apply N_backpreservation with (v := v').
           ++ econstructor; eauto. asimpl => //.
           ++ eapply N_preservation; eauto.
  - simpl. intros. apply IHHty2; [|apply IHHty1]; assumption.
  - by repeat split; try exists T.
  - by repeat split; try exists F.
  - move=> /[dup] Hsub Hsub'. simpl. apply IHHty1 in Hsub. destruct Hsub as [Hty [[v Hv] _]].
    move: Hv => /[dup] Hv Hv2. apply big_step_to_val in Hv. apply canonical_forms_bool in Hv.
    + case: Hv => Hv; subst; [apply IHHty2 in Hsub'|apply IHHty3 in Hsub'];
      move: Hsub' => /[dup] /N_impl_norm Hnorm HN; destruct Hnorm as [v' Hv'];
        eapply N_backpreservation; eauto;
        eapply N_preservation; eauto.
    + by apply (preservation (subst_tm sub t1)).
Qed.
