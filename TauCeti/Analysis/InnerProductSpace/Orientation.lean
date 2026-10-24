/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Orientation
public import Mathlib.Analysis.Normed.Module.Alternating.Basic
public import TauCeti.Analysis.Normed.Module.Alternating.TopDegree

/-!
# Continuous oriented volume forms

This file packages Mathlib's oriented volume form as a continuous alternating map.  The
construction is shared by the manifold Riemannian volume form and the planar complex area form.
-/

public section

noncomputable section

namespace Orientation

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
  [Fact (Module.finrank ℝ E = n)]

/-- Mathlib's oriented volume form, equipped with its norm bound as a continuous map. -/
def volumeFormL (o : Orientation ℝ E (Fin n)) : E [⋀^Fin n]→L[ℝ] ℝ :=
  o.volumeForm.mkContinuous 1 fun v ↦ by
    simpa only [Real.norm_eq_abs, one_mul] using o.abs_volumeForm_apply_le v

/-- Evaluation of `volumeFormL` is the underlying oriented volume form. -/
@[simp]
theorem volumeFormL_apply (o : Orientation ℝ E (Fin n)) (v : Fin n → E) :
    o.volumeFormL v = o.volumeForm v := (rfl)

/-- `volumeFormL` evaluates to one on a positively oriented orthonormal basis. -/
theorem volumeFormL_robust (o : Orientation ℝ E (Fin n))
    (b : OrthonormalBasis (Fin n) ℝ E) (hb : b.toBasis.orientation = o) :
    o.volumeFormL b = 1 := by
  rw [volumeFormL_apply, o.volumeForm_robust b hb]
  exact b.toBasis.det_self

/-- The volume form has absolute value one on every orthonormal basis. -/
theorem abs_volumeFormL_apply_of_orthonormal (o : Orientation ℝ E (Fin n))
    (b : OrthonormalBasis (Fin n) ℝ E) :
    |o.volumeFormL b| = 1 := by
  rw [volumeFormL_apply]
  exact o.abs_volumeForm_apply_of_orthonormal b

/-- The volume form is negative on an oppositely oriented orthonormal basis. -/
theorem volumeFormL_robust_neg (o : Orientation ℝ E (Fin n))
    (b : OrthonormalBasis (Fin n) ℝ E) (hb : b.toBasis.orientation ≠ o) :
    o.volumeFormL b = -1 := by
  rw [volumeFormL_apply, o.volumeForm_robust_neg b hb, neg_apply]
  simpa only [OrthonormalBasis.coe_toBasis] using congrArg Neg.neg b.toBasis.det_self

/-- A top form taking value one on an oriented orthonormal basis is the volume form. -/
theorem eq_volumeFormL_of_apply_orthonormal (o : Orientation ℝ E (Fin n))
    (ω : E [⋀^Fin n]→L[ℝ] ℝ) (b : OrthonormalBasis (Fin n) ℝ E)
    (hb : b.toBasis.orientation = o) (hω : ω b = 1) :
    ω = o.volumeFormL := by
  have hω' : ω b.toBasis = 1 := by simpa using hω
  ext v
  rw [ContinuousAlternatingMap.apply_eq_det_mul ω b.toBasis, hω', mul_one,
    volumeFormL_apply, o.volumeForm_robust b hb]

end Orientation
