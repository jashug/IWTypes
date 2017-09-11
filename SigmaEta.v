(*
Coq does not have judgemental sigma eta conversion.
Assuming function extensionality, we develop eta conversion
inside a function, as part of a term whose type is judgementally
the same before and after the eta expansion.

This was surprisingly hard to prove.
*)

From IWTypes Require Import FunctionExtensionality.

Section sigma_eta.
Context {FunExt : FunExt}.

Definition sigma_eta_eq {A} (P : A -> Type) (x : sigT P)
  : x = existT P (projT1 x) (projT2 x)
  := match x with existT _ p1 p2 => eq_refl end.

Context {A B} (P : forall a : A, B a -> Type).

Definition sigma_eta_family f (a : A) : sigT (P a)
  := existT _ (projT1 (f a)) (projT2 (f a)).
Definition sigma_eta_family_eq f : f = sigma_eta_family f
  := funext (fun a => sigma_eta_eq (P a) (f a)).

Context (C : forall (p1 : forall a, B a), (forall a, P a (p1 a)) -> Type).
Definition Cf f := C (fun a => projT1 (f a)) (fun a => projT2 (f a)).
Context (make_C : forall f, Cf f).

Definition sigma_eta_family_funext f
  : make_C (sigma_eta_family f) = make_C f
  := let lemma
      : eq_rect (Cf (sigma_eta_family f)) (fun T => T)
          (make_C (sigma_eta_family f)) (Cf f)
          (f_equal Cf (eq_trans
           (eq_sym (sigma_eta_family_eq f))
           (sigma_eta_family_eq f))) =
        make_C f
      := match eq_sym (sigma_eta_family_eq f) as p in (_ = f')
         return
           eq_rect (Cf (sigma_eta_family f)) (fun T => T)
             (make_C (sigma_eta_family f)) (Cf f')
             (f_equal Cf (eq_trans p (sigma_eta_family_eq f'))) =
           make_C f'
         with eq_refl => f_equal
           (fun p2  =>
            eq_rect _ (fun T => T) _ _ (f_equal Cf (eq_trans eq_refl p2)))
           (funext_comp eq_refl)
         end in
     let cancel_paths {A} {a b : A} (p : a = b)
      : eq_trans (eq_sym p) p = eq_refl
      := match p in (_ = b) return eq_trans (eq_sym p) p = eq_refl
         with eq_refl => eq_refl end in
     match cancel_paths (sigma_eta_family_eq f) in (_ = p)
     return eq_rect _ (fun T => T) _ _ (f_equal Cf p) = _
     with eq_refl => lemma end.
End sigma_eta.