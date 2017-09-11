(*
We present a characterization of the equality in an Indexed W type
as an Indexed W type of the same shape.
(assuming function extensionality)

That is, a path between (sup x children1) and (sup y children2) is
a path p between x and y,
and a path between each pair of children, lying over p.

I am not aware of this result in any of the literature,
but I believe it is an interesting result.
In particular, I was surprised not to find it in the HoTT book.
*)

From IWTypes Require Import IWType.
From IWTypes Require Import FunctionExtensionality.

(* We aren't working with nat, and we want to use the * notation for pairs. *)
Close Scope nat_scope.

Section IWEquality.
Context {FunExt : FunExt}.
Context {S : spec}.

(* Postulate an implementation I of S *)
Context {I : impl S} (satSI : sat S I).

(* Define the type of children of a node labeled by x *)
Definition children_for (x : Data S) := forall c, carrier I (child_index x c).

(* We claim that equality in T satisfies the following spec: *)
Definition Seq : spec := {|
  Data := {xy : Data S * Data S &
    children_for (fst xy) * children_for (snd xy) * (fst xy = snd xy)};
  Children := fun '(existT _ (_, y) _) => Children y;
  Index := {i : Index S & carrier I i * carrier I i};
  index := fun '(existT _ (x, y) (children1, children2, p)) =>
    existT _ (index y)
    (sup I y (eq_rect x children_for children1 y p), sup I y children2);
  child_index := fun '(existT _ (x, y) (children1, children2, p)) c =>
    existT _ _ ((eq_rect x children_for children1 y p) c, children2 c);
|}.

(* This is the type family we claim satisfies the above spec *)
Definition eq_type : Index Seq -> Type
  := fun '(existT _ i (a, b)) => a = b.
(* Introduction rule, easy by funext *)
Definition eq_sup
  : forall dat : Data Seq, (forall c, eq_type (child_index dat c)) ->
    eq_type (index dat)
  := fun '(existT _ (x, y) (children1, children2, p)) children_eq =>
     f_equal (sup I y) (funext children_eq).
Definition Ieq : impl Seq := Build_impl Seq eq_type eq_sup.

(* Now we prove that we have the induction rule, and that it computes. *)
Section induct.
Context
  (P : forall iab, eq_type iab -> Type)
  (IS : forall dat children_eq, (forall c, P _ (children_eq c)) ->
        P (index dat) (eq_sup dat children_eq)).

(* First we show that P holds for reflexivity *)
Definition eq_induct_refl : forall i a, P (existT _ i (a, a)) eq_refl
  := induct satSI (fun i a => P (existT _ i (a, a)) eq_refl)
     (fun x children refl_children_P => eq_rect
      (funext (fun c => eq_refl))
      (fun p' =>
       P (existT _ (index x) (sup I x children, sup I x children))
       (f_equal (sup I x) p'))
      (IS (existT _ (x, x) (children, children, eq_refl)) (fun c => eq_refl)
       refl_children_P)
      eq_refl
      (funext_comp eq_refl)).

(* Then we use path induction to generalize. *)
Definition eq_induct
  : forall iab p, P iab p
  := fun '(existT _ i (a, b)) (p : a = b) => match p in (_ = b)
     return P (existT _ i (a, b)) p with
     | eq_refl => eq_induct_refl i a
     end.

(* Finally, we show that the induction above computes as expected. *)

(* First eq_induct_refl: *)
Definition eq_induct_refl_computes
  x y children1 (p : x = y)
  : let children1' := eq_rect x children_for children1 y p in
    eq_induct_refl (index y) (sup I y children1') =
    eq_rect (funext (fun c => eq_refl)) _
      (IS (existT _ (x, y) (children1, children1', p)) (fun c => eq_refl)
       (fun c => eq_induct_refl _ (children1' c)))
      eq_refl (funext_comp eq_refl)
  := match p in (_ = y) with eq_refl => induct_computes satSI _ _ _ _ end.

(* Then in general *)
Definition eq_induct_computes
  : forall dat children_eq,
    eq_induct (index dat) (eq_sup dat children_eq) =
    IS dat children_eq (fun c => eq_induct _ (children_eq c))
  := fun '(existT _ (x, y) (children1, children2, p)) =>
     let children1' := eq_rect x children_for children1 y p in
     fun children_eq : forall c, children1' c = children2 c =>
     eq_trans (eq_trans
     (match funext children_eq
      as p' in (_ = children2)
      return
        match f_equal (sup I y) p' as p'' in (_ = b)
        return P (existT _ (index y) (sup I y children1', b)) p''
        with eq_refl => eq_induct_refl (index y) (sup I y children1') end
        =
        eq_rect (funext (happly p'))
        (fun p'' => P (existT _ _ (_, _)) (f_equal (sup I y) p''))
        (IS (existT _ (x, y) (children1, children2, p)) (happly p')
         (fun c => eq_induct (existT _ _ (_, _)) (happly p' c)))
        p' (funext_comp p')
        :> P (existT _ (index y) (sup I y children1', sup I y children2))
           (f_equal (sup I y) p')
      with eq_refl => eq_induct_refl_computes x y children1 p
      end)
     (f_equal (eq_rect _ _ _ _) (funext_adjoint children_eq)))
     (match funext_app children_eq as children_p in (_ = children_eq')
      return
        eq_rect _ _ _ _ (f_equal funext children_p) =
        IS (existT _ (x, y) (children1, children2, p)) children_eq'
        (fun c => eq_induct (existT _ _ (_, _)) (children_eq' c))
      with eq_refl => eq_refl end).
End induct.

(* Thus the equality is an inductive family: *)
Definition eq_sat : sat Seq Ieq
  := Build_sat Seq Ieq eq_induct eq_induct_computes.

End IWEquality.
Arguments children_for {S} I x.
Arguments Seq {S} I.
Arguments eq_type {S} I.
Arguments eq_sup {FunExt S I} dat children.
Arguments Ieq {FunExt S} I.