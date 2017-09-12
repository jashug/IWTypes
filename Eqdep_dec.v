(* Based on Coq's Eqdep_dec module, but for Type. *)
Section Eqdep_dec.
Context {A : Type} (x : A) (A_dec : forall y : A, (x = y) + (x = y -> False)).

Let comp (y y' : A) (eq1 : x = y) (eq2 : x = y') : y = y'
 := eq_ind x (fun a : A => a = y') eq2 y eq1.

Definition trans_sym_eq (y : A) (u : x = y) : comp y y u u = eq_refl
  := match u with eq_refl => eq_refl end.

Let nu y : x = y -> x = y
 := fun xeqy =>
    match A_dec y with
    | inl xeqy' => xeqy'
    | inr xneqy => False_rect _ (xneqy xeqy)
    end.

Let nu_constant y (u v : x = y) : nu y u = nu y v
 := match A_dec y as d
    return
      match d with inl xeqy => xeqy | inr xneqy => False_rect _ (xneqy u) end
       =
      match d with inl xeqy => xeqy | inr xneqy => False_rect _ (xneqy v) end
    with
    | inl xeqy => eq_refl
    | inr xneqy => False_rect _ (xneqy u)
    end.

Let nu_inv y (v : x = y) : x = y
 := comp x y (nu x eq_refl) v.

Let proj (P : A -> Type) (exP : sigT P) (def : P x) : P x :=
  match exP with
    | existT _ x' prf =>
      match A_dec x' with
        | inl eqprf => eq_rect x' P prf x (eq_sym eqprf)
        | _ => def
      end
  end.

Definition nu_left_inv_on (y : A) (u : x = y) : nu_inv y (nu y u) = u
  := match u with eq_refl => trans_sym_eq x (nu x eq_refl) end.

Definition eq_proofs_unicity_on (y : A) (p1 p2 : x = y) : p1 = p2
  := eq_ind (nu_inv y (nu y p1)) (fun p3 : x = y => p3 = p2)
       (eq_ind (nu_inv y (nu y p2)) (fun p3 : x = y => nu_inv y (nu y p1) = p3)
          (eq_ind (nu y p1) (fun e : x = y => nu_inv y (nu y p1) = nu_inv y e)
             eq_refl (nu y p2) (nu_constant y p1 p2)) p2
          (nu_left_inv_on y p2)) p1 (nu_left_inv_on y p1).

Definition K_dec_on (P : x = x -> Type) (H : P eq_refl) (p : x = x) : P p
  := eq_rect eq_refl P H p (eq_proofs_unicity_on x eq_refl p).

Definition inj_right_pair_on (P : A -> Type) (y y' : P x)
  (H : existT P x y = existT P x y') : y = y'
  := let H0 : proj P (existT P x y) y = proj P (existT P x y') y
      := f_equal (fun px => proj P px y) H in
     match A_dec x as d
     return
       match d with inl xeqx => eq_rect x P y x (eq_sym xeqx) | inr _ => y end =
       match d with inl xeqx => eq_rect x P y' x (eq_sym xeqx) | inr _ => y end
       -> y = y'
     with
     | inl xeqx => K_dec_on
       (fun xeqx => eq_rect x P y x xeqx = eq_rect x P y' x xeqx -> y = y')
       (fun H0 => H0) (eq_sym xeqx)
     | inr xneqx => False_ind _ (xneqx eq_refl)
     end H0.
End Eqdep_dec.