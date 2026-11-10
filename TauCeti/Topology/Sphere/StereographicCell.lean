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
# Compact subsets of a sphere lie in stereographic open cells

Let `K` be a compact subset of the unit sphere `Sⁿ` of a real inner product space of dimension
`n + 1`, missing a point `z`, and let `E` be a real normed space of dimension `n`. The inverse
stereographic projection from `z`, precomposed with a linear isomorphism and a dilation of `E`, is
a continuous injection `ψ : E → Sⁿ` whose image misses `z` and whose open unit cell `ψ(ball 0 1)`
contains `K`. M. Brown uses such a cell in his proof that the inverse sets of a map of `Sⁿ` onto
itself with two inverse sets are cellular.

## Main results

* `TauCeti.exists_injective_subset_image_ball_sphere`: a compact subset of the sphere missing `z`
  lies in the open cell of a continuous injection of `E` into the sphere whose image misses `z`.

## References

* M. Brown, *A proof of the generalized Schoenflies theorem*, Bull. Amer. Math. Soc. 66 (1960),
  74–76, Theorem 4.
-/

public section

open Function Metric Module Set

namespace TauCeti

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- A compact subset `K` of the unit sphere `Sⁿ` missing a point `z` lies in the open cell of an
injection of `E`, `dim E = n`, whose image misses `z`: the inverse stereographic projection from
`z`, precomposed with a linear isomorphism and a dilation of `E`. -/
theorem exists_injective_subset_image_ball_sphere
    (hEF : finrank ℝ F = finrank ℝ E + 1) {K : Set (sphere (0 : F) 1)} (hK : IsCompact K)
    {z : sphere (0 : F) 1} (hz : z ∉ K) :
    ∃ ψ : E → sphere (0 : F) 1, Continuous ψ ∧ Injective ψ ∧ z ∉ range ψ ∧
      K ⊆ ψ '' ball 0 1 := by
  have : Fact (finrank ℝ F = finrank ℝ E + 1) := ⟨hEF⟩
  set φ := stereographic' (finrank ℝ E) z
  have htgt : φ.target = univ := stereographic'_target z
  have hKs : K ⊆ φ.source := fun w hw ↦ by
    rw [stereographic'_source]
    exact fun h : w = z ↦ hz (h ▸ hw)
  let L : E ≃L[ℝ] EuclideanSpace ℝ (Fin (finrank ℝ E)) :=
    ContinuousLinearEquiv.ofFinrankEq (by simp)
  -- The image of `K` in `E` lies in a ball of radius `R`.
  obtain ⟨R, hR, hKR⟩ := ((hK.image_of_continuousOn (φ.continuousOn.mono hKs)).image
    L.symm.continuous).isBounded.subset_ball_lt 0 0
  refine ⟨fun x ↦ φ.symm (L (R • x)),
    φ.continuousOn_symm.comp_continuous (by fun_prop) fun x ↦ htgt ▸ mem_univ _,
    fun x x' h ↦ smul_right_injective E hR.ne' <| L.injective <|
      φ.symm.injOn (by simp [htgt]) (by simp [htgt]) h, ?_, fun w hw ↦ ?_⟩
  · rintro ⟨x, hx⟩
    have := φ.map_target (htgt ▸ mem_univ (L (R • x)))
    rw [stereographic'_source] at this
    exact this hx
  · refine ⟨R⁻¹ • L.symm (φ w), ?_, ?_⟩
    · have := hKR ⟨φ w, ⟨w, hw, rfl⟩, rfl⟩
      rw [mem_ball_zero_iff] at this ⊢
      rw [norm_smul, norm_inv, Real.norm_of_nonneg hR.le, inv_mul_lt_one₀ hR]
      exact this
    · simp [smul_smul, hR.ne', φ.left_inv (hKs hw)]

end TauCeti
