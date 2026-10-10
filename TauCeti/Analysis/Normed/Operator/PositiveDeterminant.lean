/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Matrix.PositiveDeterminant
public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Smooth paths of orientation-preserving linear maps

Transport the smooth positive-determinant matrix path through a finite basis. The resulting
family of continuous linear maps starts at the identity, ends at the given map, and remains
invertible for every real parameter. It supplies linear isotopies fixing the origin.

Reference: M. Hirsch, *Differential Topology*, Chapter 4, §6, Theorem 6.6.
-/

public section

open scoped ContDiff Matrix.Norms.Elementwise

namespace ContinuousLinearMap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- A real continuous linear map of positive determinant admits a smooth path from the identity
through linear maps of positive determinant, on the whole real parameter line. -/
theorem exists_contDiff_det_pos (L : E →L[ℝ] E) (hL : 0 < L.det) :
    ∃ γ : ℝ → E →L[ℝ] E, ContDiff ℝ ∞ γ ∧ γ 0 = ContinuousLinearMap.id ℝ E ∧
      γ 1 = L ∧ ∀ t, 0 < (γ t).det := by
  classical
  let b := Module.finBasis ℝ E
  let T := ((Matrix.toLin b b).trans LinearMap.toContinuousLinearMap).toContinuousLinearEquiv
  -- Compute the locally constructed transport through the chosen finite basis.
  have hT (A) : T A = LinearMap.toContinuousLinearMap (Matrix.toLin b b A) := rfl
  have hdet (A : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ) :
      (T A).det = A.det := by
    simp only [hT, LinearMap.det_toContinuousLinearMap, LinearMap.det_toLin]
  obtain ⟨δ, hδ, hδ0, hδ1, hδdet⟩ :=
    Matrix.exists_contDiff_det_pos (T.symm L) (by simpa only [← hdet, T.apply_symm_apply] using hL)
  refine ⟨fun t => T (δ t), T.contDiff.comp hδ, ?_, ?_, ?_⟩
  · simp only [hδ0, hT, Matrix.toLin_one]
    rfl
  · simp only [hδ1, T.apply_symm_apply]
  · intro t
    rw [hdet]
    exact hδdet t

end ContinuousLinearMap
