/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Operator.LinearIsometry
public import Mathlib.LinearAlgebra.Determinant
import TauCeti.LinearAlgebra.Determinant.Basic

/-!
# Linear isometries of rank-one spaces and their determinants

On a free module of rank one, every endomorphism is multiplication by its determinant. So a linear
isometry of such a space is the identity when its determinant is `1`, and negation when its
determinant is `-1`. Over the reals, the determinant of a linear isometry of a one-dimensional
space has absolute value `1`, so these are the only two linear isometries.

## Main results

* `LinearIsometryEquiv.eq_refl_of_det_eq_one`, `LinearIsometryEquiv.eq_neg_of_det_eq_neg_one`: on
  a free module of rank one, these are the linear isometries of determinant `1` and `-1`.
* `LinearIsometryEquiv.eq_refl_or_eq_neg`: the only linear isometries of a one-dimensional real
  normed space are the identity and negation.
-/

public section

namespace LinearIsometryEquiv

section FinrankOne

variable {R E : Type*} [CommRing R] [SeminormedAddCommGroup E] [Module R E] [Module.Free R E]
  (hE : Module.finrank R E = 1) {e : E ≃ₗᵢ[R] E}
include hE

/-- A linear isometry of determinant `1` of a free module of rank one is the identity. -/
theorem eq_refl_of_det_eq_one (he : LinearMap.det e.toLinearMap = 1) : e = .refl R E :=
  ext fun x ↦ (LinearMap.apply_eq_det_smul_of_finrank_eq_one hE e.toLinearMap x).trans <| by
    rw [he, one_smul, coe_refl, id_eq]

/-- A linear isometry of determinant `-1` of a free module of rank one is negation. -/
theorem eq_neg_of_det_eq_neg_one (he : LinearMap.det e.toLinearMap = -1) : e = .neg R :=
  ext fun x ↦ (LinearMap.apply_eq_det_smul_of_finrank_eq_one hE e.toLinearMap x).trans <| by
    rw [he, neg_one_smul, coe_neg]

end FinrankOne

/-- The only linear isometries of a one-dimensional real normed space are the identity and
negation. -/
theorem eq_refl_or_eq_neg {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (hE : Module.finrank ℝ E = 1) (e : E ≃ₗᵢ[ℝ] E) : e = .refl ℝ E ∨ e = .neg ℝ := by
  have : Nontrivial E := Module.nontrivial_of_finrank_eq_succ hE
  obtain ⟨x, hx⟩ := exists_ne (0 : E)
  -- `e` is multiplication by its determinant, which therefore has absolute value `1`.
  have h : ‖LinearMap.det e.toLinearMap • x‖ = ‖x‖ := by
    rw [← LinearMap.apply_eq_det_smul_of_finrank_eq_one hE]
    exact e.norm_map x
  rw [norm_smul, mul_eq_right₀ (norm_ne_zero_iff.mpr hx), Real.norm_eq_abs,
    abs_eq zero_le_one] at h
  exact h.imp (eq_refl_of_det_eq_one hE) (eq_neg_of_det_eq_neg_one hE)

end LinearIsometryEquiv
