/-
Copyright (c) 2015 Ulrik Buchholtz and Egbert Rijke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ulrik Buchholtz, Egbert Rijke

Cayley-Dickson construction on the level of spheres.
-/

import algebra.group homotopy.join

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

open algebra

namespace homotopy

structure cayley_dickson [class] (A : Type)
  extends h_space A, has_neg A, has_star A :=
(neg_neg : ∀a, neg (neg a) = a)
(star_star : ∀a, star (star a) = a)
(star_one : star one = one)
(star_mul : ∀a b, star (mul a b) = mul (star b) (star a))

section
  open bool

  definition cayley_dickson_bool [instance] : cayley_dickson bool :=
  ⦃ cayley_dickson, one := tt, mul := biff, neg := bnot, star := function.id,
    one_mul := bool.rec idp idp, mul_one := bool.rec idp idp,
    neg_neg := bool.rec idp idp, star_star := bool.rec idp idp,
    star_one := idp, star_mul := bool.rec (bool.rec idp idp) (bool.rec idp idp) ⦄

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
  has_one.mk (inl 1)

  definition neg : carrier → carrier :=
  pushout.elim (λa, inl (- a)) (λa, inr (- a)) (λz, jglue (- pr1 z) (- pr2 z))

end

end homotopy

