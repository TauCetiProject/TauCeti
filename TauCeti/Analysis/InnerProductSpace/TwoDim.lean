/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.TwoDim
public import TauCeti.Analysis.InnerProductSpace.Orientation

/-!
# The continuous volume form on the complex plane

The continuous oriented volume form is normalized on the standard complex basis `(1, I)`. On a
pair of vectors it is the area form `dx ∧ dy`, `(v, w) ↦ Im (conj v * w)`.
-/

public section

open ComplexConjugate

noncomputable section

namespace Complex

attribute [local instance] Complex.finrank_real_complex_fact

/-- The normalized complex volume form evaluates to one on the basis `(1, I)`. -/
theorem orientation_volumeFormL_one_I :
    Complex.orientation.volumeFormL ![1, I] = 1 := by
  simpa [coe_basisOneI] using
    Complex.orientation.volumeFormL_apply_orthonormal Complex.orthonormalBasisOneI rfl

/-- The continuous volume form of `ℂ` is the area form `dx ∧ dy`: on a pair of vectors `(v, w)` it
is `Im (conj v * w)`. -/
theorem orientation_volumeFormL_apply (v : Fin 2 → ℂ) :
    Complex.orientation.volumeFormL v = (conj (v 0) * v 1).im := by
  rw [Orientation.volumeFormL_apply, ← Complex.areaForm, Orientation.areaForm_to_volumeForm]
  congr 1
  ext i
  fin_cases i <;> rfl

end Complex
