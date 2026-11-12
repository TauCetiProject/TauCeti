/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MonoidAlgebra.Basic

/-!
# Transport of a monoid algebra along a monoid isomorphism

An isomorphism of monoids `e : G ≃* H` induces the algebra isomorphism
`MonoidAlgebra.domCongr R A e : A[G] ≃ₐ[R] A[H]`, which moves the coefficient at `g` to `e g`.
It touches only the index of each coefficient, so it commutes with any map of the coefficients.

## Main results

* `MonoidAlgebra.mapAlgHom_domCongr`: mapping the coefficients along an algebra homomorphism
  commutes with transport along a monoid isomorphism.
-/

public section

namespace MonoidAlgebra

/-- Mapping the coefficients of a monoid algebra along an algebra homomorphism commutes with
transport along an isomorphism of monoids. -/
theorem mapAlgHom_domCongr {R A B G H : Type*} [CommSemiring R] [Semiring A] [Semiring B]
    [Algebra R A] [Algebra R B] [Monoid G] [Monoid H] (f : A →ₐ[R] B) (e : G ≃* H)
    (x : MonoidAlgebra A G) :
    mapAlgHom H f (domCongr R A e x) = domCongr R B e (mapAlgHom G f x) := by
  induction x using induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | single g r => simp

end MonoidAlgebra
