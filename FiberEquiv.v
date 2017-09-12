(*
Furthermore, we prove that each fiber of the new index map is equivalent
to the equality in a fiber of the original index map.

Specifically, with a and b having index i,
the fiber of a = b is equivalent to the path space ax = bx in the fiber of i.
*)

From IWTypes Require Import IWType.
From IWTypes Require Import CharacterizeIWEquality.

Definition fib {A B} (f : A -> B) (b : B) := {a : A & f a = b}.

Module Import inner.
Section inner.
Context {S : spec} (I : impl S).

(*
Since we are working with an arbitrary implementation, we don't have
judgemental matching. The below destruct_type gives some of that back.
*)
Definition deconstruct_type i (a : carrier I i)
  := {a' : {x : Data S & children_for I x * (index x = i)} &
      eq_rect _ _ (sup I _ (fst (projT2 a'))) i (snd (projT2 a')) = a}.
Definition deconstruct
  : forall i a, deconstruct_type i a
  := induct I deconstruct_type
     (fun x children _ => existT _ (existT _ x (children, eq_refl)) eq_refl).
Definition deconstruct_computes
  : forall x children,
    deconstruct _ (sup I x children) =
    existT _ (existT _ x (children, eq_refl)) eq_refl
  := induct_computes I _ _.
Definition deconstruct_contract
  : forall i a (d : deconstruct_type i a),
    deconstruct i a = d
  := fun i a '(existT _ (existT _ x' (children', px)) p) =>
     match p with eq_refl => match px with eq_refl =>
       deconstruct_computes x' children'
     end end.
(*
To prove something for all destructions of (sup I x children), it is enough
to prove it for (x, children) with reflexive paths.
This is basically the judgemental computation rule.
*)
Definition deconstruct_type_rect x children
  (P : deconstruct_type (index x) (sup I x children) -> Type)
  (IS : P (existT _ (existT _ x (children, eq_refl)) eq_refl))
  : forall d, P d
  := fun d => eq_rect _ P IS d (eq_trans
       (eq_sym (deconstruct_computes x children))
       (deconstruct_contract _ _ d)).
Definition deconstruct_type_rect_computes x children P IS
  : deconstruct_type_rect x children P IS
    (existT _ (existT _ x (children, eq_refl)) eq_refl) =
    IS
  := f_equal _ (eq_trans_sym_inv_l (deconstruct_computes x children)).

(* Take a node with index i and make an element of the fiber of i. *)
Definition data_from_deconstruct i a
  : deconstruct_type i a -> fib (@index S) i
  := fun '(existT _ (existT _ x (_, p)) _) => existT _ x p.

(* Define the forward and reverse functions, and prove they are inverses. *)
Definition fib_to_eq_rect
  (P : forall i a b, deconstruct_type i a -> deconstruct_type i b ->
       fib (@index (Seq I)) (existT _ i (a, b)) -> Type)
  (IS : forall x children1 children2,
        P (index x) (sup I x children1) (sup I x children2)
        (existT _ (existT _ x (children1, eq_refl)) eq_refl)
        (existT _ (existT _ x (children2, eq_refl)) eq_refl)
        (existT _ (existT _ x (children1, children2)) eq_refl))
  : forall i a b da db fx, P i a b da db fx
  := fun i a b da db '(existT _ dat index_eq) =>
     match dat
     return forall index_eq da db, P i a b da db (existT _ dat index_eq)
     with existT _ x (children1, children2) => fun index_eq =>
       match index_eq in (_ = existT _ i (a, b))
       return
         forall da db,
         P i a b da db (existT _ (existT _ x (children1, children2)) index_eq)
       with eq_refl =>
         (deconstruct_type_rect x children1 _
         (deconstruct_type_rect x children2 _
          (IS x children1 children2)))
       end
     end index_eq da db.
Definition fib_to_eq_rect_computes P IS x children1 children2
  (da := existT _ (existT _ x (children1, eq_refl)) eq_refl
   : deconstruct_type _ (sup I x children1))
  (db := existT _ (existT _ x (children2, eq_refl)) eq_refl)
  (fx := existT _ (existT _ x (children1, children2)) eq_refl)
  : fib_to_eq_rect P IS _ (sup I x children1) (sup I x children2) da db fx =
    IS x children1 children2
  := eq_trans (x:=fib_to_eq_rect P IS _ _ _ da db fx)
       (f_equal (fun f => f db)
        (deconstruct_type_rect_computes x children1 _ _))
       (deconstruct_type_rect_computes x children2 _ _).
Definition fib_to_eq_parametrized
  : forall i (a b : carrier I i) da db,
    fib (@index (Seq I)) (existT _ i (a, b)) ->
    data_from_deconstruct i a da = data_from_deconstruct i b db
    :> fib (@index S) i
  := fib_to_eq_rect _ (fun x children1 children2 => eq_refl).

Definition eq_to_fib_rect
  (P : forall i a b da db,
       data_from_deconstruct i a da = data_from_deconstruct i b db -> Type)
  (IS : forall x children1 children2,
        P (index x) (sup I x children1) (sup I x children2)
        (existT _ (existT _ x (children1, eq_refl)) eq_refl)
        (existT _ (existT _ x (children2, eq_refl)) eq_refl)
        eq_refl)
  : forall i a b da db data_eq, P i a b da db data_eq
  := fun i a b da db =>
     match da, db with
     existT _ (existT _ x (children1, px)) pa,
     existT _ (existT _ y (children2, py)) pb =>
     match pa, pb with eq_refl, eq_refl =>
     fun data_eq : existT _ x px = existT _ y py =>
     match data_eq in (_ = existT _ y py)
     return
       forall children2,
       let da := existT _ (existT _ x (children1, px)) eq_refl in
       let db := existT _ (existT _ y (children2, py)) eq_refl in
       P _ _ _ da db data_eq
     with eq_refl => fun children2 =>
     match px in (_ = i)
     return
       let da := existT _ (existT _ x (children1, px)) eq_refl in
       let db := existT _ (existT _ x (children2, px)) eq_refl in
       P _ _ _ da db eq_refl
     with eq_refl => IS x children1 children2
     end end children2 end end.
Definition eq_to_fib_parametrized
  : forall i a b da db,
    data_from_deconstruct i a da = data_from_deconstruct i b db ->
    fib (@index (Seq I)) (existT _ i (a, b))
  := eq_to_fib_rect
     (fun i a b _ _ _ => fib (@index (Seq I)) (existT _ i (a, b)))
     (fun x children1 children2 =>
      existT _ (existT _ x (children1, children2)) eq_refl).

Definition eq_to_fib_to_eq_id_parametrized
  : forall i a b da db data_eq,
    fib_to_eq_parametrized i a b da db
    (eq_to_fib_parametrized i a b da db data_eq) =
    data_eq
  := eq_to_fib_rect _
     (fun x children1 children2 =>
      fib_to_eq_rect_computes _ _ x children1 children2).

Definition fib_to_eq_to_fib_id_parametrized
  : forall i a b da db fx,
    eq_to_fib_parametrized i a b da db
    (fib_to_eq_parametrized i a b da db fx) =
    fx
  := fib_to_eq_rect _
     (fun x children1 children2 =>
      (f_equal (eq_to_fib_parametrized _ _ _ _ _)
       (fib_to_eq_rect_computes _ _ x children1 children2))).
End inner.
End inner.

(* By specializing the above, we get the desired inverses. *)
Section fibers.
Context {S : spec} (I : impl S).

Definition data_part : forall i, carrier I i -> fib (@index S) i
  := fun i a => data_from_deconstruct I i a (deconstruct I i a).

Definition fib_to_eq i (a b : carrier I i)
  : fib (@index (Seq I)) (existT _ i (a, b)) ->
    data_part i a = data_part i b :> fib (@index S) i
  := fib_to_eq_parametrized I i a b _ _.

Definition eq_to_fib i (a b : carrier I i)
  : data_part i a = data_part i b :> fib (@index S) i ->
    fib (@index (Seq I)) (existT _ i (a, b))
  := eq_to_fib_parametrized I i a b _ _.

Definition fib_to_eq_to_fib_id i a b
  : forall fx, eq_to_fib i a b (fib_to_eq i a b fx) = fx
  := fib_to_eq_to_fib_id_parametrized I i a b _ _.

Definition eq_to_fib_to_eq_id i a b
  : forall data_eq, fib_to_eq i a b (eq_to_fib i a b data_eq) = data_eq
  := eq_to_fib_to_eq_id_parametrized I i a b _ _.
End fibers.
