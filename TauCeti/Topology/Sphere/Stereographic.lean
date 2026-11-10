/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Geometry.Manifold.Instances.Sphere

/-!
# Compact subsets of a punctured sphere lie in a stereographic ball

Let `K` be a compact subset of the unit sphere `Sⁿ` of a real inner product space of dimension
`n + 1`, missing a point `w`. Reading `Sⁿ \ {w}` in the stereographic chart from `w`, the image of
`K` is bounded, so `K` lies in the image of a large coordinate ball. Rescaling, `K` lies in the
image of the open unit ball of any real normed space `E` of dimension `n` under a continuous
injection `E → Sⁿ` missing `w`.

## Main results

* `TauCeti.exists_continuous_injective_subset_image_ball`: a compact subset of the sphere missing
  `w` lies in the image of the open unit ball under a continuous injection `E → Sⁿ` missing `w`.
-/

public section

open Function Metric Module Set

namespace TauCeti

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- A compact subset `K` of the unit sphere `Sⁿ` of a real inner product space of dimension
`n + 1` missing a point `w` lies in the image of the open unit ball of `E`, `dim E = n`, under a
continuous injection `E → Sⁿ` missing `w`: a large ball in the stereographic chart from `w`. -/
theorem exists_continuous_injective_subset_image_ball
    (hEF : finrank ℝ F = finrank ℝ E + 1) {K : Set (sphere (0 : F) 1)} (hK : IsCompact K)
    {w : sphere (0 : F) 1} (hwK : w ∉ K) :
    ∃ ψ : E → sphere (0 : F) 1, Continuous ψ ∧ Injective ψ ∧ (∀ v, ψ v ≠ w) ∧
      K ⊆ ψ '' ball 0 1 := by
  have : Fact (finrank ℝ F = finrank ℝ E + 1) := ⟨hEF⟩
  set φs := stereographic' (finrank ℝ E) w
  have hsymm : Continuous φs.symm :=
    continuousOn_univ.1 (stereographic'_target (n := finrank ℝ E) w ▸ φs.continuousOn_symm)
  let L : E ≃L[ℝ] EuclideanSpace ℝ (Fin (finrank ℝ E)) :=
    ContinuousLinearEquiv.ofFinrankEq (by simp)
  have hKs : K ⊆ φs.source := fun x hx ↦ by
    rw [stereographic'_source (n := finrank ℝ E)]
    rintro rfl
    exact hwK hx
  -- `K` lies in the coordinate ball of radius `R`.
  obtain ⟨R, hR, hKR⟩ := ((hK.image_of_continuousOn (φs.continuousOn.mono hKs)).image
    L.symm.continuous).isBounded.subset_ball_lt 0 0
  refine ⟨fun v ↦ φs.symm (L (R • v)), hsymm.comp (L.continuous.comp (continuous_const_smul R)),
    fun v v' h ↦ smul_right_injective E hR.ne'
      (L.injective (φs.symm.injOn (by simp [φs]) (by simp [φs]) h)), fun v ↦ ?_,
    fun x hx ↦ ⟨R⁻¹ • L.symm (φs x), ?_, ?_⟩⟩
  · have := φs.map_target (x := L (R • v)) (by simp [φs])
    rwa [stereographic'_source (n := finrank ℝ E)] at this
  · have h := hKR ⟨φs x, ⟨x, hx, rfl⟩, rfl⟩
    rw [mem_ball_zero_iff] at h ⊢
    rwa [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hR, inv_mul_lt_iff₀ hR, mul_one]
  · simp only [smul_inv_smul₀ hR.ne', ContinuousLinearEquiv.apply_symm_apply,
      φs.left_inv (hKs hx)]


end TauCeti
