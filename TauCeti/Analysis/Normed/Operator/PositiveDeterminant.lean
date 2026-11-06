/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.PositiveDeterminant
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

omit [FiniteDimensional ℝ E] in
/-- `det (A + t • id) → det A` as `t → 0`. -/
theorem tendsto_det_add_smul_id (A : E →L[ℝ] E) :
    Filter.Tendsto (fun t : ℝ => (A + t • ContinuousLinearMap.id ℝ E).det) (nhds 0)
      (nhds A.det) := by
  have : Continuous fun t : ℝ => (A + t • ContinuousLinearMap.id ℝ E).det :=
    ContinuousLinearMap.continuous_det.comp
      (continuous_const.add (continuous_id.smul continuous_const))
  simpa using this.tendsto 0

omit [FiniteDimensional ℝ E] in
/-- If `a < det A`, there is `-(κ / 2) < t < 0` with `a < det (A + t)`. -/
theorem exists_det_add_smul_id_gt {A : E →L[ℝ] E} {a κ : ℝ} (hlt : a < A.det)
    (hκ : 0 < κ) :
    ∃ t : ℝ, (a < (A + t • ContinuousLinearMap.id ℝ E).det ∧ -(κ / 2) < t) ∧ t < 0 :=
  (((((tendsto_det_add_smul_id A).eventually (lt_mem_nhds hlt)).and
    (lt_mem_nhds (by linarith))).filter_mono nhdsWithin_le_nhds).and
    (self_mem_nhdsWithin (s := Set.Iio (0 : ℝ)))).exists

end ContinuousLinearMap
