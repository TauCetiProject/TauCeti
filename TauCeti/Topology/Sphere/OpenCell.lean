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
# A compact subset of a sphere missing a point lies in an open cell

Let `C` be a compact subset of the unit sphere `Sⁿ` of a real inner product space of dimension
`n + 1`, and let `z ∉ C`. Rescaling the stereographic chart from `z` so that its unit ball contains
the bounded image of `C` gives a continuous injection `e` of a real normed space of dimension `n`
into `Sⁿ \ {z}` such that the image of the open unit ball is open and contains `C`
(`TauCeti.exists_subset_image_ball_sphere`). The image of the closed unit ball is then a closed
cell of `Sⁿ` missing `z` whose interior contains `C`; M. Brown's proof of the generalized
Schoenflies theorem uses such a cell in the proof of its Theorem 4.

## Main results

* `TauCeti.exists_subset_image_ball_sphere`: a compact subset of `Sⁿ` missing a point lies in the
  image of the open unit ball under a continuous injection of `ℝⁿ` into the complement of that
  point, and that image is open.

## References

* M. Brown, *A proof of the generalized Schoenflies theorem*, Bull. Amer. Math. Soc. 66 (1960),
  74–76, Theorem 4.
-/

public section

open Function Metric Module Set

namespace TauCeti

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **A compact subset of a sphere missing a point lies in an open cell.** If `C` is a compact
subset of the unit sphere `Sⁿ` of a real inner product space of dimension `n + 1` and `z ∉ C`, then
there is a continuous injection `e` of a real normed space `E` of dimension `n` into `Sⁿ \ {z}`
such that the image of the open unit ball is open and contains `C`. It is the stereographic chart
from `z`, rescaled so that its closed unit ball contains `C` in its interior. -/
theorem exists_subset_image_ball_sphere [FiniteDimensional ℝ E]
    (hEF : finrank ℝ F = finrank ℝ E + 1) {C : Set (sphere (0 : F) 1)} (hC : IsCompact C)
    {z : sphere (0 : F) 1} (hz : z ∉ C) :
    ∃ e : E → sphere (0 : F) 1, Continuous e ∧ Injective e ∧ (∀ v, e v ≠ z) ∧
      IsOpen (e '' ball 0 1) ∧ C ⊆ e '' ball 0 1 := by
  have : FiniteDimensional ℝ F := .of_finrank_pos (by omega)
  have : Fact (finrank ℝ F = finrank ℝ E + 1) := ⟨hEF⟩
  set φ := stereographic' (finrank ℝ E) z
  have hφs : φ.source = {z}ᶜ := stereographic'_source z
  have hφt : φ.target = univ := stereographic'_target z
  set L := ContinuousLinearEquiv.ofFinrankEq (𝕜 := ℝ) (E := E)
    (F := EuclideanSpace ℝ (Fin (finrank ℝ E))) (finrank_euclideanSpace_fin.symm)
  have hCφ : C ⊆ φ.source := by
    rw [hφs]
    rintro x hx (rfl : x = z)
    exact hz hx
  -- `C` lies in the image of the open ball of radius `R` under `φ⁻¹ ∘ L`.
  obtain ⟨B, hB⟩ := hC.exists_bound_of_continuousOn
    (L.symm.continuous.comp_continuousOn (φ.continuousOn.mono hCφ))
  set R := max B 0 + 1
  have hR : 0 < R := by positivity
  have hsymm : Continuous φ.symm := continuousOn_univ.1 (hφt ▸ φ.continuousOn_symm)
  refine ⟨fun v ↦ φ.symm (L (R • v)), hsymm.comp (by fun_prop), fun v w h ↦
    smul_right_injective E hR.ne' (L.injective (φ.symm.injOn (by simp [hφt]) (by simp [hφt]) h)),
    fun v ↦ ?_, ?_, fun x hx ↦ ⟨R⁻¹ • L.symm (φ x), ?_, ?_⟩⟩
  · have h := φ.map_target (x := L (R • v)) (by simp [hφt])
    rwa [hφs, mem_compl_singleton_iff] at h
  · rw [← image_image φ.symm, ← image_image L]
    exact φ.symm.isOpen_image_of_subset_source
      (L.toHomeomorph.isOpenMap _ (isOpenMap_smul₀ hR.ne' _ isOpen_ball)) (by simp [hφt])
  · rw [mem_ball_zero_iff, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hR,
      inv_mul_lt_iff₀ hR, mul_one]
    exact (hB x hx).trans_lt (by simp [R]; linarith [le_max_left B 0])
  · simp [smul_smul, hR.ne', φ.left_inv (hCφ hx)]

end TauCeti
