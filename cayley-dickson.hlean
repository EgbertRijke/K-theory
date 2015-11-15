/-
Copyright (c) 2015 Ulrik Buchholtz and Egbert Rijke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ulrik Buchholtz, Egbert Rijke

Cayley-Dickson construction on the level of spheres.
-/

import algebra.group homotopy.join cubical.square

open eq

-- TODO: move this to algebra hierarchy in hott std lib
namespace algebra

structure has_star [class] (A : Type) :=
(star : A → A)

reserve postfix `*` : (max+1)
postfix `*` := has_star.star

structure h_space [class] (A : Type) extends has_mul A, has_one A :=
(one_mul : ∀a, mul one a = a) (mul_one : ∀a, mul a one = a)

end algebra

namespace bool

  definition biff (a b : bool) :=
  bool.rec_on a (bnot b) b

end bool

namespace join
section
  parameters {A B : Type}

  open pushout

  protected definition rec {P : join A B → Type} (Pinl : Π(x : A), P (inl x))
    (Pinr : Π(y : B), P (inr y)) (Pglue : Π(x : A)(y : B), Pinl x =[jglue x y] Pinr y)
      (z : join A B) : P z :=
  pushout.rec Pinl Pinr (prod.rec Pglue) z

  theorem rec_glue {P : join A B → Type} (Pinl : Π(x : A), P (inl x))
    (Pinr : Π(y : B), P (inr y)) (Pglue : Π(x : A)(y : B), Pinl x =[jglue x y] Pinr y)
      (x : A) (y : B) : apdo (rec Pinl Pinr Pglue) (jglue x y) = Pglue x y :=
  !quotient.rec_eq_of_rel

  protected definition elim {P : Type} (Pinl : A → P) (Pinr : B → P)
    (Pglue : Π(x : A)(y : B), Pinl x = Pinr y) (z : join A B) : P :=
  rec Pinl Pinr (λx y, pathover_of_eq (Pglue x y)) z

  theorem elim_glue {P : Type} (Pinl : A → P) (Pinr : B → P)
    (Pglue : Π(x : A)(y : B), Pinl x = Pinr y) (x : A) (y : B)
    : ap (elim Pinl Pinr Pglue) (jglue x y) = Pglue x y :=
  begin
    apply equiv.eq_of_fn_eq_fn_inv !(pathover_constant (jglue x y)),
    rewrite [▸*,-apdo_eq_pathover_of_eq_ap,↑join.elim],
    apply rec_glue
  end

end
end join

open algebra

namespace homotopy

structure cayley_dickson [class] (A : Type)
  extends h_space A, has_neg A, has_star A :=
(one_star : star one = one)
(neg_neg : ∀a, neg (neg a) = a)
(star_star : ∀a, star (star a) = a)
(star_mul : ∀a b, star (mul a b) = mul (star b) (star a))

/- possible further laws:
   neg_mul : ∀a b, mul (neg a) b = neg (mul a b)
   neg_star : ∀a, star (neg a) = neg (star a)
   norm : ∀a, mul (star a) a = one   -- this expresses that A is nicely normed
   …
-/

section
  variable {A : Type}

  theorem one_mul [s : h_space A] (a : A) : 1 * a = a := !h_space.one_mul

  theorem mul_one [s : h_space A] (a : A) : a * 1 = a := !h_space.mul_one

  theorem one_star [s : cayley_dickson A] : @eq A (1*) 1 := !cayley_dickson.one_star

  theorem star_one_mul (A : Type) [H : cayley_dickson A] (a : A)
    : 1* * a = a :=
  calc
    1* * a = 1 * a : by rewrite [one_star]
       ... = a     : one_mul
  
end

section
  open bool

  definition cayley_dickson_bool [instance] : cayley_dickson bool :=
  ⦃ cayley_dickson, one := tt, mul := biff, neg := bnot, star := function.id,
    one_mul := bool.rec idp idp, mul_one := bool.rec idp idp,
    neg_neg := bool.rec idp idp, star_star := λa, idp,
    one_star := idp, star_mul := bool.rec (bool.rec idp idp) (bool.rec idp idp) ⦄

end

section
  parameter A : Type
  parameter [H : cayley_dickson A]
  include A
  include H

  open cayley_dickson
  open join
  open prod
  open pushout

  definition carrier : Type := join A A

  definition one [instance] : has_one carrier :=
  ⦃ has_one, one := (inl 1) ⦄

  definition neg [instance] : has_neg carrier :=
  ⦃ has_neg, neg := join.elim (λa, inl (-a)) (λb, inr (-b)) (λa b, jglue (-a) (-b)) ⦄

  definition star [instance] : has_star carrier :=
  ⦃ has_star, star := join.elim (λa, inl (a*)) (λb, inr (-b)) (λa b, jglue (a*) (-b)) ⦄

  /-
    in the algebraic form, the Cayley-Dickson multiplication has:

      (a,b)(c,d) = (a * c - d * b*, a* * d + c * b)

    here we do the spherical form where one of the coordinates is zero.
  -/
  open eq.ops
  definition mul [instance] : has_mul carrier :=
  ⦃ has_mul,
    mul := join.elim
     (λa, join.elim
       (λc, inl (a * c))
       (λd, inr (a* * d))
       (λc d, jglue (a * c) (a* * d)))
     (λb, join.elim
       (λc, inr (c * b))
       (λd, inl (- d * b*))
       (λc d, by apply (jglue (- d * b*) (c * b))⁻¹))
     (λa b, 
     begin
       apply eq_of_homotopy,
       fapply join.rec,
       { intro c, apply jglue (a * c) (c * b) },
       { intro d, apply (jglue (- d * b*) (a* * d))⁻¹ },
       { intros c d, apply eq_pathover,
         krewrite [join.elim_glue,join.elim_glue],
         exact sorry }
     end
     ) ⦄

  definition cd_one_mul : ∀a : carrier, 1 * a = a :=
  begin
    fapply join.rec,
    { intro a, apply ap inl, exact one_mul a },
    { intro b, apply ap inr, exact star_one_mul A b },
    { intros a b, apply eq_pathover, exact sorry },
  end

  definition cd_mul_one : ∀a : carrier, a * 1 = a :=
  begin
    fapply join.rec,
    { intro a, apply ap inl, exact mul_one a },
    { intro b, apply ap inr, exact one_mul b },
    { intros a b, apply eq_pathover, exact sorry }
  end

end

end homotopy

