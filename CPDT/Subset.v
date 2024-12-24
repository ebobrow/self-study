Require Import Nat.
Require Import Lia.
Require Import PeanoNat.
Require Import Cpdt.CpdtTactics.

Definition le_dep : forall n m, {n <= m} + {n > m}.
Proof.
  intros. destruct (n <=? m) eqn:E.
  - apply Nat.leb_le in E. auto.
  - apply Nat.leb_gt in E. auto.
Defined.
Print le_dep.

Definition le_dep' : forall n m, {n <= m} + {n > m}.
Proof.
  refine (fix F (n m : nat) :=
    match n, m with
    | O, O => left _ _
    | O, S _ => left _ _
    | S _, O => right _ _
    | S n', S m' => if (F n' m') then left _ _ else right _ _
    end); lia.
Defined.
Print le_dep'.

(* ----------------------- *)
Notation "'Yes'" := (left _ _).
Notation "'No'" := (right _ _).
Notation "'Reduce' x" := (if x then Yes else No) (at level 50).
Notation "x || y" := (if x then Yes else Reduce y) (at level 50, left associativity).

Definition var := nat.
Inductive prop : Set :=
  | PVar : var -> prop
  | PNeg : prop -> prop
  | PConj : prop -> prop -> prop
  | PDisj : prop -> prop -> prop.

Fixpoint propDenote (truth : var -> bool) (p : prop) : Prop :=
  match p with
  | PVar v => if truth v then True else False
  | PNeg p' => ~ propDenote truth p'
  | PConj p1 p2 => propDenote truth p1 /\ propDenote truth p2
  | PDisj p1 p2 => propDenote truth p1 \/ propDenote truth p2
  end.

Definition bool_true_dec : forall b, { b = true } + { b = true -> False }.
Proof.
  refine (fun b => match b with
                   | true => Yes
                   | false => No
                   end); crush.
Defined.

Definition decide : forall (truth : var -> bool) (p : prop), {propDenote truth p} + {~ propDenote truth p}.
Proof.
  refine (fix F (truth : var -> bool) (p : prop) :=
    match p with
    | PVar v => Reduce bool_true_dec (truth v)
    | PNeg p' => if F truth p' then No else Yes
    | PConj p1 p2 => if F truth p1 then Reduce F truth p2 else No
    | PDisj p1 p2 => if F truth p1 then Yes else Reduce F truth p2
    end); crush. destruct (truth v); auto.
Defined.

Notation "[ e ]" := (exist _ e _).
Definition negate : forall p : prop, {p' : prop | forall truth, propDenote truth p <-> ~ propDenote truth p'}.
Proof.
  refine (fun x => [(fix F (p : prop) :=
    match p with
    | PVar v => PNeg (PVar v)
    | PNeg p' => p'
    | PConj p1 p2 => PDisj (F p1) (F p2)
    | PDisj p1 p2 => PConj (F p1) (F p2)
    end) x]). intros. destruct (decide truth x); induction x; crush.
Defined.
