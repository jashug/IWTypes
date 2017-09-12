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
Context {S : spec} {I : impl S} (satSI : sat S I).

(*
Since we are working with an arbitrary implementation, we don't have
judgemental matching. The below destruct_type gives some of that back.
*)
Definition deconstruct_type i (a : carrier I i)
  := {a' : {x : Data S & children_for I x * (index x = i)} &
      eq_rect _ _ (sup I _ (fst (projT2 a'))) i (snd (projT2 a')) = a}.
Definition deconstruct
  : forall i a, deconstruct_type i a
  := induct satSI deconstruct_type
     (fun x children _ => existT _ (existT _ x (children, eq_refl)) eq_refl).
Definition deconstruct_computes
  : forall x children,
    deconstruct _ (sup I x children) =
    existT _ (existT _ x (children, eq_refl)) eq_refl
  := induct_computes satSI _ _.
Definition deconstruct_contract
  : forall i a (d : deconstruct_type i a),
    deconstruct i a = d
  := fun i a '(existT _ (existT _ x' (children', px)) p) =>
     match p with eq_refl => match px with eq_refl =>
       deconstruct_computes x' children'
     end end.

(* Take a node with index i and make an element of the fiber of i. *)
Definition data_from_deconstruct i a
  : deconstruct_type i a -> fib (@index S) i
  := fun '(existT _ (existT _ x (_, p)) _) => existT _ x p.
Definition data_part : forall i, carrier I i -> fib (@index S) i
  := fun i a => data_from_deconstruct i a (deconstruct i a).
Definition data_part_computes x children
  : data_part _ (sup I x children) = existT _ x eq_refl
  := f_equal (data_from_deconstruct _ _) (deconstruct_computes x children).
Definition data_part_unique x children
  : forall dx,
    data_from_deconstruct _ (sup I x children) dx =
    data_part _ (sup I x children)
  := fun '(existT _ (existT _ x' (children', pi')) p') =>
     match p' in (_ = a) return _ = data_part _ a
     with eq_refl =>
       match pi' return existT _ x' pi' = data_part _ (eq_rect _ _ _ _ pi')
       with eq_refl => eq_sym (data_part_computes x' children') end
     end.
Definition data_part_computes' x children dx
  : data_from_deconstruct _ (sup I x children) dx = existT _ x eq_refl
  := eq_trans (data_part_unique x children dx) (data_part_computes x children).
Definition simplify_data_part_computes x children1 children2
  : eq_trans
    (eq_trans
     (eq_sym (data_part_computes x children1))
     (data_part_computes x children1))
    (eq_sym (eq_trans
     (eq_sym (data_part_computes x children2))
     (data_part_computes x children2)))
     =
    eq_refl
  := f_equal2 (fun p1 p2 => eq_trans p1 (eq_sym p2))
     (eq_trans_sym_inv_l _) (eq_trans_sym_inv_l _).

(* Define the forward and reverse functions, and prove they are inverses. *)
Definition fib_to_eq_rect
  (P : forall i a b, deconstruct_type i a -> deconstruct_type i b ->
       fib (@index (Seq I)) (existT _ i (a, b)) -> Type)
  (IS : forall x children1 children2 da db,
        P (index x) (sup I x children1) (sup I x children2) da db
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
         fun da db => IS x children1 children2 da db
       end
     end index_eq da db.
Definition fib_to_eq_parametrized
  : forall i (a b : carrier I i) da db,
    fib (@index (Seq I)) (existT _ i (a, b)) ->
    data_from_deconstruct i a da = data_from_deconstruct i b db
    :> fib (@index S) i
  := fib_to_eq_rect _
     (fun x children1 children2 da db => eq_trans
      (data_part_computes' x children1 da)
      (eq_sym (data_part_computes' x children2 db))).

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
      simplify_data_part_computes x children1 children2).

Definition deconstruct_type_rect x children
  (P : deconstruct_type (index x) (sup I x children) -> Type)
  (IS : P (existT _ (existT _ x (children, eq_refl)) eq_refl))
  : forall d, P d
  := fun d => eq_rect _ P IS d (eq_trans
       (eq_sym (deconstruct_computes x children))
       (deconstruct_contract _ _ d)).

Definition fib_to_eq_to_fib_id_parametrized
  : forall i a b da db fx,
    eq_to_fib_parametrized i a b da db
    (fib_to_eq_parametrized i a b da db fx) =
    fx
  := fib_to_eq_rect _
     (fun x children1 children2 =>
      (deconstruct_type_rect x children1 (fun da => forall db, _)
       (deconstruct_type_rect x children2 (fun db => _)
        (f_equal (fun p => _ p)
         (simplify_data_part_computes x children1 children2))))).
End inner.
End inner.

(* By specializing the above, we get the desired inverses. *)
Section fibers.
Context {S : spec} {I : impl S} (satSI : sat S I).

Definition fib_to_eq i (a b : carrier I i)
  : fib (@index (Seq I)) (existT _ i (a, b)) ->
    data_part satSI i a = data_part satSI i b :> fib (@index S) i
  := fib_to_eq_parametrized satSI i a b _ _.

Definition eq_to_fib i (a b : carrier I i)
  : data_part satSI i a = data_part satSI i b :> fib (@index S) i ->
    fib (@index (Seq I)) (existT _ i (a, b))
  := eq_to_fib_parametrized (I:=I) i a b _ _.

Definition fib_to_eq_to_fib_id i a b
  : forall fx, eq_to_fib i a b (fib_to_eq i a b fx) = fx
  := fib_to_eq_to_fib_id_parametrized satSI i a b _ _.

Definition eq_to_fib_to_eq_id i a b
  : forall data_eq, fib_to_eq i a b (eq_to_fib i a b data_eq) = data_eq
  := eq_to_fib_to_eq_id_parametrized satSI i a b _ _.
End fibers.
