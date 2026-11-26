/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.AlgebraMap

/-!
# Natural operations on the affine line are polynomial

Let `H` be a commutative `R`-algebra, so that `A ↦ (H →ₐ[R] A)` is the functor of points of
`Spec H`. A family of maps `op A : (H →ₐ[R] A) → A → A`, natural in the commutative `R`-algebra
`A`, is a morphism `Spec H × 𝔸¹ → 𝔸¹`, so by the Yoneda lemma it is given by a polynomial with
coefficients in `H`: the value of the operation at the universal point, the inclusion of the
constants `H → H[X]`, and the universal element `X`. A point `g` sends `a` to the evaluation of
that polynomial, with coefficients pushed along `g`, at `a`.

Evaluation along the universal point itself is composition of polynomials.

## Main results

* `Polynomial.comp_eq_aevalTower`: composition is evaluation along the inclusion of constants.
* `Polynomial.eq_aevalTower_of_naturality`: a natural operation on the affine line is evaluation
  of the polynomial obtained at the universal point and the universal element.
-/

public section

namespace Polynomial

universe u v

variable {R : Type u} {H : Type v} [CommSemiring R] [CommSemiring H] [Algebra R H]

/-- Composition of polynomials is evaluation along the inclusion of the constants
`H → H[X]`, viewed as an `R`-algebra homomorphism. -/
theorem comp_eq_aevalTower (p q : H[X]) :
    p.comp q = aevalTower (IsScalarTower.toAlgHom R H H[X]) q p := by
  have h : (aeval q).restrictScalars R = aevalTower (IsScalarTower.toAlgHom R H H[X]) q :=
    algHom_ext' (AlgHom.ext fun c => by simp) (by simp)
  rw [comp_eq_aeval, ← h, AlgHom.restrictScalars_apply]

/-- **Yoneda for natural operations on the affine line.** A family of operations
`op A : (H →ₐ[R] A) → A → A`, natural in the commutative `R`-algebra `A`, is determined by the
polynomial obtained by applying the operation at the universal point `H → H[X]` to `X`: a point
`g` sends `a` to the evaluation of that polynomial, with coefficients pushed along `g`, at `a`. -/
theorem eq_aevalTower_of_naturality
    (op : ∀ (A : Type v) [CommSemiring A] [Algebra R A], (H →ₐ[R] A) → A → A)
    (op_map : ∀ (A B : Type v) [CommSemiring A] [Algebra R A] [CommSemiring B] [Algebra R B]
      (φ : A →ₐ[R] B) (g : H →ₐ[R] A) (a : A), φ (op A g a) = op B (φ.comp g) (φ a))
    (A : Type v) [CommSemiring A] [Algebra R A] (g : H →ₐ[R] A) (a : A) :
    op A g a = aevalTower g a (op H[X] (IsScalarTower.toAlgHom R H H[X]) X) := by
  rw [op_map H[X] A (aevalTower g a), aevalTower_comp_toAlgHom, aevalTower_X]

end Polynomial
