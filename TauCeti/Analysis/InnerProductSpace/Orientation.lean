/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Orientation
public import Mathlib.Analysis.Normed.Module.Alternating.Basic

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
theorem volumeFormL_apply (o : Orientation ℝ E (Fin n)) (v : Fin n → E) :
    o.volumeFormL v = o.volumeForm v := (rfl)

/-- `volumeFormL` evaluates to one on a positively oriented orthonormal basis. -/
theorem volumeFormL_robust (o : Orientation ℝ E (Fin n))
    (b : OrthonormalBasis (Fin n) ℝ E) (hb : b.toBasis.orientation = o) :
    o.volumeFormL b = 1 := by
  rw [volumeFormL_apply, o.volumeForm_robust b hb]
  exact b.toBasis.det_self

end Orientation
