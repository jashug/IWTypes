(*
For some properties, if they hold for all the fibers of the index map,
then they hold for the Indexed W type.
We assume function extensionality throughout.

We work with the concrete inductive implementation IW, since
it has nice judgemental equalities. Since all implementations are equivalent,
the results hold for any implementation.

We show below that being a subsingleton / mere proposition is such a property.

We also show below that, assuming we can lift decisions over the children
(if the children are finitely enumerable, this is possible)
that decidability of equality is another such property.

Since we showed that the fibers of the index map of the equality family are
equivalent to equality in a fiber of the index map, we have by recursion
that all positive h-levels are also inherited.

In the case of non-indexed W types, the Index type is unit, so the unique
fiber is equivalent to the Data set, and this result coincides with
the result by Danielsson:
https://homotopytypetheory.org/2012/09/21/positive-h-levels-are-closed-under-w/
*)

From IWTypes Require Import IWType.
From IWTypes Require Import FunctionExtensionality.
From IWTypes Require Eqdep_dec.
Import IWType.concrete.

(* We aren't working with nat, and we want to use the + notation for types. *)
Close Scope nat_scope.

Definition fib {A B} (f : A -> B) (b : B) := {a : A & f a = b}.

Definition isProp A := forall x y : A, x = y.

Definition isProp_inherited {FunExt : FunExt} (S : spec)
  (fibers_prop : forall i, isProp (fib (@index S) i))
  : forall i, isProp (IW S i)
  := fix isProp i a : forall b, a = b := match a with
     | IWsup x children1 => fun (b : IW S (index x)) =>
       let children_contract children2 : children1 = children2
        := funext (fun c => isProp _ (children1 c) (children2 c)) in
       match b in (IW _ i)
       return
         forall iy : i = index x,
         IWsup x children1 =
         eq_rect i (IW S) b (index x) iy
       with IWsup y children2 => fun iy : index y = index x =>
         match fibers_prop (index x) (existT _ x eq_refl) (existT _ y iy)
         in (_ = existT _ y iy)
         return
           forall children2,
           IWsup x children1 =
           eq_rect (index y) _ (IWsup y children2) (index x) iy
         with eq_refl => fun children2 =>
           f_equal (IWsup x) (children_contract children2)
         end children2
       end eq_refl
     end.

Definition decidable (A : Type) := A + (A -> False).
Definition decidable_eq (A : Type) := forall x y : A, decidable (x = y).

(* If Children x is finitely enumerable, we have liftP. *)
Definition decidable_eq_inherited {FunExt : FunExt} (S : spec)
  (liftP : forall (x : Data S) (P : Children x -> Type),
   (forall c, decidable (P c)) -> decidable (forall c, P c))
  (fibers_dec : forall i, decidable_eq (fib (@index S) i))
  : forall i, decidable_eq (IW S i)
  := let children_for (x : Data S) := forall c, IW S (child_index x c) in
     let getfib {i} (a : IW S i) : fib (@index S) i
      := match a with IWsup x _ => existT _ x eq_refl end in
     let getfib_computes x y children p
      : getfib (eq_rect (index y) (IW S) (IWsup y children) (index x) p) =
        existT _ y p
      := match p
         return getfib (eq_rect _ _ (IWsup y children) _ p) = existT _ y p
         with eq_refl => eq_refl end in
     let getfib_plus {i} (a : IW S i)
      : {f : fib (@index S) i & children_for (projT1 f)}
      := match a with IWsup x children =>
         existT _ (existT _ x eq_refl) children end in
     let children_eq (x : Data S) children1 children2
      : IWsup x children1 = IWsup x children2 -> children1 = children2
      := fun aeqb => Eqdep_dec.inj_right_pair_on
         _ (fibers_dec _ (existT _ x eq_refl))
         (fun f => children_for (projT1 f))
         _ _ (f_equal getfib_plus aeqb) in
     fix decide_eq i a : forall b, decidable (a = b) := match a with
     | IWsup x children1 => fun (b : IW S (index x)) =>
       let decide_children children2 : decidable (children1 = children2)
        := match liftP x (fun c => children1 c = children2 c)
                 (fun c => decide_eq _ (children1 c) (children2 c))
           with
           | inl agree => inl (funext agree)
           | inr disagree => inr (fun agree => disagree (happly agree))
           end in
       match b in (IW _ i)
       return
         forall iy : i = index x,
         decidable (
           IWsup x children1 =
           eq_rect i (IW S) b (index x) iy
         )
       with IWsup y children2 => fun iy : index y = index x =>
         match fibers_dec (index x) (existT _ x eq_refl) (existT _ y iy)
         with
         | inl fiber_eq => match fiber_eq in (_ = existT _ y iy)
           return
             forall children2,
             decidable (
               IWsup x children1 =
               eq_rect (index y) (IW S) (IWsup y children2) (index x) iy
             )
           with eq_refl => fun children2 =>
             match decide_children children2 with
             | inl children_eq => inl (f_equal (IWsup x) children_eq)
             | inr children_neq => inr (fun aeqb => children_neq
               (children_eq x children1 children2 aeqb))
             end
           end children2
         | inr fiber_neq => inr
           (fun aeqb
              : IWsup x children1 = eq_rect _ _ (IWsup y children2) _ iy =>
            fiber_neq (eq_trans
             (f_equal getfib aeqb)
             (getfib_computes x y children2 iy)))
         end
       end eq_refl
     end.


