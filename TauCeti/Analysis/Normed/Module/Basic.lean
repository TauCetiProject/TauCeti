/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps

/-!
# The integer cast into a normed ring

In a seminormed ring in which `ℤ` acts isometrically and `‖1‖ = 1`, such as `ℝ` or `ℂ`, the
cast `Int.castRingHom R` preserves norms. This makes lemmas stated for a `RingHomIsometric`
ring homomorphism, such as `Polynomial.supNorm_map`, apply to integer polynomials.

Over a seminormed ring `R`, which need not be a field, an `R`-bilinear map `β` with
`‖β x y‖ ≤ C * ‖x‖ * ‖y‖` is jointly continuous (`LinearMap.continuous₂_of_bound`), and
so is a scalar action with `‖r • m‖ ≤ C * ‖r‖ * ‖m‖` (`TauCeti.continuousSMul_of_norm_smul_le`).
-/

public section

/-- The cast from `ℤ` is norm-preserving in a normed ring in which `ℤ` acts isometrically and
`‖1‖ = 1`, such as `ℝ` or `ℂ`. -/
instance RingHomIsometric.intCastRingHom {R : Type*} [SeminormedRing R]
    [NormSMulClass ℤ R] [NormOneClass R] : RingHomIsometric (Int.castRingHom R) where
  norm_map {n} := by simp [norm_intCast_eq_abs_mul_norm_one, Int.norm_eq_abs]

open scoped NNReal

section BoundedBilinear

variable {R : Type*} [SeminormedCommRing R]

/-- An `R`-bilinear map bounded by `C * ‖x‖ * ‖y‖` is jointly continuous. -/
theorem LinearMap.continuous₂_of_bound {X Y Z : Type*} [SeminormedAddCommGroup X]
    [Module R X] [SeminormedAddCommGroup Y] [Module R Y] [SeminormedAddCommGroup Z] [Module R Z]
    (β : X →ₗ[R] Y →ₗ[R] Z) (C : ℝ) (hβ : ∀ x y, ‖β x y‖ ≤ C * ‖x‖ * ‖y‖) :
    Continuous fun p : X × Y ↦ β p.1 p.2 :=
  IsBoundedBilinearMap.continuous (𝕜 := R)
    { add_left := fun x₁ x₂ y ↦ by simp
      smul_left := fun c x y ↦ by simp
      add_right := fun x y₁ y₂ ↦ by simp
      smul_right := fun c x y ↦ by simp
      bound := ⟨max C 1, by positivity, fun x y ↦
        (hβ x y).trans (by gcongr; exact le_max_left _ _)⟩ }

/-- A scalar action bounded by `C * ‖r‖ * ‖m‖` is continuous. -/
theorem TauCeti.continuousSMul_of_norm_smul_le {M : Type*} [SeminormedAddCommGroup M]
    [Module R M]
    (h : ∃ C : ℝ≥0, ∀ (r : R) (m : M), ‖r • m‖ ≤ C * ‖r‖ * ‖m‖) : ContinuousSMul R M :=
  h.elim fun C hC ↦ ⟨(LinearMap.lsmul R M).continuous₂_of_bound C hC⟩

end BoundedBilinear

end
