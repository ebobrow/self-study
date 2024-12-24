(* bad *)
Ltac deSome :=
  match goal with
  | [ H : Some _ = Some _ |- _ ] => injection H; clear H; intros; subst; deSome
  | _ => reflexivity
  end.

(* good *)
Ltac deSome' :=
  repeat match goal with
  | [ H : Some _ = Some _ |- _ ] => injection H; clear H; intros; subst
  end; reflexivity.

(* ---------------------------------------- *)

Ltac enumLists n k :=
  match n with
  | O => k (@nil bool)
  | S ?n' => enumLists n' ltac:(fun l => k l)
  | S ?n' => enumLists n' ltac:(fun l => k (true :: l))
  | S ?n' => enumLists n' ltac:(fun l => k (false :: l))
  end.

Ltac falsify' n :=
  match goal with
  | [ H : _ |- _ ] =>
      match type of H with
      | forall x : ?T, _ =>
          match type of T with
          | Set => enumLists n ltac:(fun l => specialize H with (x := l); falsify' n)
          | _ => specialize H with (x := bool); falsify' n
          end
      | _ => discriminate
      end
  end.

Ltac falsify n :=
  match goal with
  | [ |- ?P ] => assert (~ P) by
      let H := fresh "H" in
        unfold not; intro H; falsify' n
  end.

Theorem test1 : forall A (ls1 ls2 : list A), ls1 ++ ls2 = ls2 ++ ls1.
Proof. falsify 1. Abort.
Theorem test2 : forall A (ls1 ls2 : list A), length (ls1 ++ ls2) = length ls1 - length ls2.
Proof. falsify 1. Abort.
Theorem test3 : forall A (ls : list A), length (rev ls) - 3 = 0.
Proof. falsify 4. Abort.
