Set Implicit Arguments.

(* weird tree that only has data at leaves *)
Inductive tree (A : Type) :=
  | Node : tree A -> tree A -> tree A
  | Leaf : A -> tree A.

Section htree.
  Variable A : Type.
  Variable B : A -> Type.

  Inductive htree : tree A -> Type :=
    | HNode : forall (t1 t2 : tree A), htree t1 -> htree t2 -> htree (Node t1 t2)
    | HLeaf : forall (x : A), B x -> htree (Leaf x).

  Variable elm : A.

  Inductive path : tree A -> Type :=
    | PLeaf : path (Leaf elm)
    | PLeft : forall t1 t2, path t1 -> path (Node t1 t2)
    | PRight : forall t1 t2, path t2 -> path (Node t1 t2).

  Fixpoint tget t (ht : htree t) : path t -> B elm :=
    match ht with
    | HLeaf x => fun p =>
        match p in path t return match t with
                                 | Leaf a => B a -> B elm
                                 | Node _ _ => unit
                                 end with
        | PLeaf => fun x => x
        | PLeft _ _ => tt
        | PRight _ _ => tt
        end x
    | HNode l r => fun p =>
        match p in path t return match t with
                                 | Leaf _ => unit
                                 | Node t1 t2 => (path t1 -> B elm) ->
                                                 (path t2 -> B elm) -> B elm
                                 end with
        | PLeaf => tt
        | PLeft _ p' => fun getl _ => getl p'
        | PRight _ p' => fun _ getr => getr p'
        end (tget l) (tget r)
    end.
End htree.
Arguments HNode [A B t1 t2] _ _.
Arguments HLeaf [A B x] _.
Arguments PLeft [A elm t1 t2] _.
Arguments PRight [A elm t1 t2] _.
Arguments path [A elm] _.

Definition t : tree Set := Node (Leaf nat) (Leaf bool).
Definition ht : htree (fun T : Set => T) t := HNode (HLeaf 5) (HLeaf true).
Definition p : path t := PRight (PLeaf bool).
Eval simpl in tget ht p.

(* TODO: get a fresh look at this *)
(* Fixpoint htmap2 {t f} (ht1 ht2 : htree f t) (binop : htree (fun T => T -> T -> f T) t) : htree f t := *)
(*   match ht1 with *)
(*   | HLeaf x1 => match ht2, binop in htree _ t, htree _ t return match t with *)
(*                                                             | Leaf _ => _ *)
(*                                                             | Node _ _ => unit *)
(*                                                             end with *)
(*                 | HLeaf x2, HLeaf bin, _ => HLeaf (bin x1 x2) *)
(*                 | _, _, _ => tt *)
(*                 end *)
(*   | HNode l1 r1 => match ht2, binop in htree _ t, htree _ t return match t with *)
(*                                                                    | Leaf _ => unit *)
(*                                                                    | Node _ _ => _ *)
(*                                                                    end with *)
(*                    | HNode l2 r2, HNode lb rb, _ => HNode (htmap2 l1 l2 lb) (htmap2 r1 r2 rb) *)
(*                    | _, _, _ => tt *)
(*                    end *)
(*   end. *)
