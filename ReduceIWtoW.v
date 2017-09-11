(*
We present a reduction from Indexed W types to W types.
The main idea is to take a W type that forgets all the index information,
and then recursively define well_formed m i predicate which witnesses
that m has index i.
We then show that the sigma type combining the two satisfies the expected
induction principle, and so is equivalent to any other implementation.

I found this construction (typecheck unindexed trees) in
Indexed Containers by Thorsten Altenkirch and Peter Morris
http://www.cs.nott.ac.uk/~psztxa/publ/ICont.pdf,
which references
* M. Abbott, T. Altenkirch, and N. Ghani. Containers - constructing
 strictly positive types. Theoretical Computer Science,
 342:327, September 2005. Applied Semantics: Selected Topics.
* N. Gambino and M. Hyland. Wellfounded trees and dependent
 polynomial functors. In S. Berardi, M. Coppo, and
 F. Damiani, editors, types for Proofs and Programs (TYPES 2003),
 Lecture Notes in Computer Science, 2004
as previous examples of the technique.
*)

From IWTypes Require Import IWType.
From IWTypes Require Import FunctionExtensionality.
From IWTypes Require SigmaEta.

(*
Define the W type inductively.
As with IW types, we have uniqueness, so WLOG we use this one,
which has nice judgemental equalities.
*)
Inductive W (Data : Type) (Children : Data -> Type) :=
  sup : forall x : Data, (Children x -> W Data Children) -> W Data Children.
Arguments sup {Data Children} x children.

Section IW_to_W.
Context {FunExt : FunExt}.

(* We want to build a type that satisfies this spec. *)
Context (S : spec).

(* This is our approximation to S that forgets index information. *)
Definition tree := W (Data S) (@Children S).

(* We define, recursively, a well_formed predicate that represents a proof
   that m has index i. *)
Fixpoint well_formed (i : Index S) (m : tree) : Type
  := match m with
     | sup x children =>
       (index x = i) *
       (forall c, well_formed (child_index x c) (children c))
     end.

(* Define our implementation of S *)
Definition carrier' i := sigT (well_formed i).
Definition sup' (x : Data S) (children : forall c, carrier' (child_index x c))
  : carrier' (index x)
  := existT (well_formed (index x))
     (sup x (fun c => projT1 (children c)))
     (eq_refl, fun c => projT2 (children c)).
Definition I' : impl S := Build_impl S carrier' sup'.

(* Define the induction principle and show it computes. *)
Section induct'.
Context
  (P : forall i, carrier' i -> Type)
  (IS : forall x children, (forall c, P _ (children c)) ->
    P _ (sup' x children)).

(* The induction is structural on the unindexed W type. *)
Fixpoint induct'_pre i m
  : forall (m_ix_i : well_formed i m), P i (existT _ m m_ix_i)
  := match m with
     | sup x children => fun '(p, IH) => match p in (_ = i)
       return P i (existT _ (sup x children) (p, IH))
       with eq_refl => IS x
         (fun c => existT _ (children c) (IH c))
         (fun c => induct'_pre _ (children c) (IH c))
       end
     end.

(*
Note that because of the match on m, we lose one level of judgemental equality.
If we were working in a type theory with
 - W types with judgemental dependent eliminators AND
 - Sigma type with judgemental eta
Then it appears that we can build Indexed W types
with judgemental dependent eliminators
*)
Definition induct' : forall i m, P i m
  := fun i '(existT _ m m_ix_i) => induct'_pre i m m_ix_i.

(*
We need function extensionality to compensate for the lack of
judgemental eta for sigma.
*)
Definition induct_computes' x children
  : induct' _ (sup' x children) =
    IS x children (fun c => induct' _ (children c))
  := SigmaEta.sigma_eta_family_funext _
     (fun p1 p2 =>
      P _ (existT _ (sup x p1) (eq_refl, p2)))
     (fun children => IS x children (fun c => induct' _ (children c)))
     children.
End induct'.

(*
Thus we have constructed an implementation of the Indexed W type S
from the non-indexed W type tree.
*)
Definition sat' : sat S I'
  := Build_sat S I' induct' induct_computes'.

End IW_to_W.