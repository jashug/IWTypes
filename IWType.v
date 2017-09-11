(*
We define an Indexed W type by five pieces of data.
First, we have two pieces that are the same as regular W types:
Data : Type
  The type of data carried by each node, traditionally A
Children : Data -> Type
  The children of a node with data x are named by (Children x).
  Traditionally B.
Then we specify the indices:
Index : Type
  The type of indices
index : Data -> Index
  A node with data x has is labeled (index x)
child_index : forall x : Data, Children x -> Index
  Child c : Children x is labeled (child_index x c)

The Indexed W type is then a type family carrier : Index -> Type,
along with a constructor
sup : forall x : Data, (forall c : Children x, carrier (child_index x c)) ->
      carrier (index x)
.

We then require sup to satisfy an appropriate dependent induction principle.

Note that regular W types are a subset of Indexed W types, obtained by
setting Index = unit.
*)

From IWTypes Require Import FunctionExtensionality.

Record spec := {
  Data : Type;
  Children : Data -> Type;
  Index : Type;
  index : Data -> Index;
  child_index : forall x, Children x -> Index;
}.
Arguments Data S : rename.
Arguments Children {S} x : rename.
Arguments Index S : rename.
Arguments index {S} x : rename.
Arguments child_index {S} x c : rename.

Record impl {S : spec} := {
  carrier : Index S -> Type;
  sup :
    forall x : Data S,
    (forall (c : Children x), carrier (child_index x c)) ->
    carrier (index x);
}.
Arguments impl S : clear implicits.

Record sat {S : spec} {I : impl S} := {
  induct :
    forall (P : forall i, carrier I i -> Type),
    (forall x children, (forall c, P _ (children c)) ->
     P _ (sup I x children)) ->
    forall i m, P i m;
  induct_computes :
    forall P IS,
    forall x children,
    induct P IS _ (sup I x children) =
    IS x children (fun c => induct P IS _ (children c));
}.
Arguments sat S I : clear implicits.

Module unique.
Section unique.
(* We prove that the implementation of a spec is unique up to equivalence. *)

Context {FunExt : FunExt}.
Context {S} {I1 I2} (sat1 : sat S I1) (sat2 : sat S I2).

Definition I1_to_I2 : forall i, carrier I1 i -> carrier I2 i
  := induct sat1
     (fun i _ => carrier I2 i)
     (fun x children IH => sup I2 x IH).

Definition I2_to_I1 : forall i, carrier I2 i -> carrier I1 i
  := induct sat2
     (fun i _ => carrier I1 i)
     (fun x children IH => sup I1 x IH).

Definition I1_to_I2_sup
  : forall x children,
    I1_to_I2 _ (sup I1 x children) =
    sup I2 x (fun c => I1_to_I2 _ (children c))
  := induct_computes sat1 _ _.

Definition I2_to_I1_sup
  : forall x children,
    I2_to_I1 _ (sup I2 x children) =
    sup I1 x (fun c => I2_to_I1 _ (children c))
  := induct_computes sat2 _ _.

Definition I1_to_I2_to_I1_id
  : forall i m, I2_to_I1 i (I1_to_I2 i m) = m
  := induct sat1
     (fun i m => I2_to_I1 i (I1_to_I2 i m) = m)
     (fun x children IH => eq_trans (eq_trans
      (f_equal (I2_to_I1 _) (I1_to_I2_sup _ _))
      (I2_to_I1_sup _ _))
      (f_equal (sup I1 x) (funext IH))).

(* The reverse holds by symmetry, so the two implementations are equivalent. *)

End unique.
End unique.

Module concrete.
Section concrete.
(* We prove that every spec has an implementation. *)

Context (S : spec).

Inductive IW : Index S -> Type
  := IWsup :
       forall (x : Data S) (children : forall c, IW (child_index x c)),
       IW (index x).

Definition IWinduct
  (P : forall i, IW i -> Type)
  (IS :
    forall x children, (forall c, P _ (children c)) ->
    P _ (IWsup x children))
  : forall i m, P i m
  := fix induct i (m : IW i) : P i m := match m with
     | IWsup x children => IS x children (fun c => induct _ (children c))
     end.
Definition IWcomputes P IS x children
  : IWinduct P IS _ (IWsup x children) =
    IS x children (fun c => IWinduct P IS _ (children c))
  := eq_refl.
Definition Wsat : sat S {| carrier := IW; sup := IWsup |}
  := Build_sat S {| carrier := IW; sup := IWsup |} IWinduct IWcomputes.

(*
With the above module unique,
this shows that every spec has a unique implementation.
With univalence, you should have that {I : impl S & sat S I} is contractable,
assuming that coherence of induct_computes doesn't mess things up.
*)

End concrete.
End concrete.
