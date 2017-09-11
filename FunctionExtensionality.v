(*
Proof that strong function extensionality follows
from naive function extensionality.

We create a typeclass carrying a proof of naive functionality,
and provide a version of function extensionality that is an
adjoint equivalence with the cannonical happly.

To use, simply provide an instance of FunExt in the context.
*)

From IWTypes Require Adjointification.

Class FunExt := funext_raw
  : forall {A B} (f g : forall a : A, B a), (forall a, f a = g a) -> f = g.

Section funext.
Context {FunExt : FunExt}.
Context {A} {B : A -> Type}.
Implicit Types f g : forall a, B a.

Definition happly {f g} (feq : f = g) : forall a, f a = g a
  := match feq in (_ = g) return forall a, f a = g a
     with eq_refl => fun a => eq_refl end.

Definition funext {f g} (hom : forall a, f a = g a) : f = g
  := eq_trans (eq_sym (funext_raw f f (happly eq_refl))) (funext_raw f g hom).

Definition funext_comp {f g} (feq : f = g)
  : funext (happly feq) = feq
  := match feq return funext (happly feq) = feq
     with eq_refl => eq_trans_sym_inv_l (funext_raw f f (happly eq_refl)) end.
End funext.

Section funext_app.
Context {FunExt : FunExt}.
Context {A} {B : A -> Type}.
Implicit Types f g : forall a, B a.

Definition funext_contract {f g} (hom : forall a, f a = g a)
  : existT _ f (fun a => eq_refl) = existT _ g hom
  := f_equal
     (fun r => existT (fun g => forall a, f a = g a)
        (fun a => projT1 (r a)) (fun a => projT2 (r a)))
     (funext (fun a =>
      match hom a as homa in (_ = ga)
      return existT _ (f a) eq_refl = existT _ ga homa
      with eq_refl => eq_refl end)).

Definition funext_app {f g}
  : forall (hom : forall a, f a = g a), happly (funext hom) = hom
  := Adjointification.fg_id' happly funext funext_comp
     (fun hom => match funext_contract hom in (_ = existT _ g hom)
      return happly (funext hom) = hom
      with eq_refl => f_equal happly (funext_comp eq_refl) end).

Definition happly_adjoint {f g}
  : forall feq : f = g,
    funext_app (happly feq) = f_equal happly (funext_comp feq)
  := Adjointification.f_adjoint _ _ _ _.

Definition funext_adjoint {f g}
  : forall hom : forall a, f a = g a,
    funext_comp (funext hom) = f_equal funext (funext_app hom)
  := Adjointification.g_adjoint _ _ _ _.
End funext_app.
