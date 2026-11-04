/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.LinearAlgebra.BilinearMap

/-!
# The integer cast into a normed ring

In a seminormed ring in which `ℤ` acts isometrically and `‖1‖ = 1`, such as `ℝ` or `ℂ`, the
cast `Int.castRingHom R` preserves norms. This makes lemmas stated for a `RingHomIsometric`
ring homomorphism, such as `Polynomial.supNorm_map`, apply to integer polynomials.

Over a seminormed ring `R`, which need not be a field, an `R`-bilinear map `β` with
`‖β x y‖ ≤ C * ‖x‖ * ‖y‖` is jointly continuous (`LinearMap.continuous_of_norm_apply_le`), and
so is a scalar action with `‖r • m‖ ≤ C * ‖r‖ * ‖m‖` (`continuousSMul_of_norm_smul_le`).
-/

public section

/-- The cast from `ℤ` is norm-preserving in a normed ring in which `ℤ` acts isometrically and
`‖1‖ = 1`, such as `ℝ` or `ℂ`. -/
instance RingHomIsometric.intCastRingHom {R : Type*} [SeminormedRing R]
    [NormSMulClass ℤ R] [NormOneClass R] : RingHomIsometric (Int.castRingHom R) where
  norm_map {n} := by simp [norm_intCast_eq_abs_mul_norm_one, Int.norm_eq_abs]

open Filter Topology

open scoped NNReal

section BoundedBilinear

variable {R : Type*} [SeminormedCommRing R]

/-- An `R`-bilinear map bounded by `C * ‖x‖ * ‖y‖` is jointly continuous. -/
theorem LinearMap.continuous_of_norm_apply_le {X Y Z : Type*} [SeminormedAddCommGroup X]
    [Module R X] [SeminormedAddCommGroup Y] [Module R Y] [SeminormedAddCommGroup Z] [Module R Z]
    (β : X →ₗ[R] Y →ₗ[R] Z) (C : ℝ) (hβ : ∀ x y, ‖β x y‖ ≤ C * ‖x‖ * ‖y‖) :
    Continuous fun p : X × Y ↦ β p.1 p.2 := by
  refine continuous_iff_continuousAt.2 fun p ↦ ?_
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  -- `β x y - β x₀ y₀ = β (x - x₀) y + β x₀ (y - y₀)`
  have hg : Tendsto (fun q : X × Y ↦ C * ‖q.1 - p.1‖ * ‖q.2‖ + C * ‖p.1‖ * ‖q.2 - p.2‖) (𝓝 p)
      (𝓝 0) := by
    simpa using ((by fun_prop : Continuous fun q : X × Y ↦
      C * ‖q.1 - p.1‖ * ‖q.2‖ + C * ‖p.1‖ * ‖q.2 - p.2‖).tendsto p)
  refine squeeze_zero (fun _ ↦ norm_nonneg _) (fun q ↦ ?_) hg
  have hsplit : β q.1 q.2 - β p.1 p.2 = β (q.1 - p.1) q.2 + β p.1 (q.2 - p.2) := by
    simp only [map_sub, LinearMap.sub_apply]
    abel
  rw [hsplit]
  exact (norm_add_le _ _).trans (add_le_add (hβ _ _) (hβ _ _))

/-- A scalar action bounded by `C * ‖r‖ * ‖m‖` is continuous. -/
theorem continuousSMul_of_norm_smul_le {M : Type*} [SeminormedAddCommGroup M] [Module R M]
    (h : ∃ C : ℝ≥0, ∀ (r : R) (m : M), ‖r • m‖ ≤ C * ‖r‖ * ‖m‖) : ContinuousSMul R M :=
  h.elim fun C hC ↦ ⟨(LinearMap.lsmul R M).continuous_of_norm_apply_le C hC⟩

end BoundedBilinear

end
