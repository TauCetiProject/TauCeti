/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Alternating.Basic
public import Mathlib.Analysis.Complex.Basic

/-!
# Coefficients of real one-forms on the complex plane

`ContinuousAlternatingMap.apply_const_complex` evaluates a real one-form on a complex vector
using its coefficients on the real basis `(1, I)`. It identifies differential-form line
integrands with their coordinate expressions.
-/

public section

namespace ContinuousAlternatingMap

/-- A real one-form on the complex plane evaluates on a vector using its coefficients on
the real basis `(1, I)`. -/
theorem apply_const_complex {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (α : ℂ [⋀^Fin 1]→L[ℝ] F) (v : ℂ) :
    α (fun _ ↦ v) = v.re • α (fun _ ↦ 1) + v.im • α (fun _ ↦ Complex.I) := by
  have hv : v = v.re • (1 : ℂ) + v.im • Complex.I := by
    simp [Complex.real_smul]
  simpa only [map_add, map_smul, ofSubsingleton_symm_apply_apply] using
    congrArg ((ofSubsingleton ℝ ℂ F (0 : Fin 1)).symm α) hv

end ContinuousAlternatingMap
