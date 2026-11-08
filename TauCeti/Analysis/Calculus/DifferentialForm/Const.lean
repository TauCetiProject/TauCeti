/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.DifferentialForm.Basic
import TauCeti.Analysis.Calculus.DifferentialForm.Basic

/-!
# The exterior derivative of a constant differential form

A differential form on a normed space which does not depend on the base point has exterior
derivative identically zero, within any set. This complements the linearity lemmas of
`Mathlib/Analysis/Calculus/DifferentialForm/Basic.lean`, which cover the `0`-form case only
(`extDerivWithin_constOfIsEmpty`), and is what makes constant two-forms on a vector space closed.

A constant two-form `ω` is moreover exact: for any covector `a` and base point `x₀`, the affine
one-form `y ↦ a + ½ ι_{y - x₀} ω` has exterior derivative `ω`
(`ContinuousAlternatingMap.extDeriv_const_add_smul_curryLeft_sub`).

## Main declarations

* `ContinuousAlternatingMap.extDerivWithin_const` and `ContinuousAlternatingMap.extDeriv_const`:
  the exterior derivative of a constant form vanishes.
* `ContinuousAlternatingMap.extDeriv_const_add_smul_curryLeft_sub`: an affine primitive of a
  constant two-form.
-/

public section

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {n : ℕ}

namespace ContinuousAlternatingMap

/-- The exterior derivative within a set of a constant differential form vanishes. -/
@[simp]
theorem extDerivWithin_const (ω : E [⋀^Fin n]→L[𝕜] F) (s : Set E) :
    extDerivWithin (fun _ ↦ ω) s = 0 := by
  ext1 x
  simp [extDerivWithin, ← alternatizeUncurryFinCLM_apply]

/-- The exterior derivative of a constant differential form vanishes. -/
@[simp]
theorem extDeriv_const (ω : E [⋀^Fin n]→L[𝕜] F) : extDeriv (fun _ ↦ ω) = 0 := by
  rw [← extDerivWithin_univ, extDerivWithin_const]

/-- A constant two-form `ω` is the exterior derivative of the affine one-form
`y ↦ a + ½ ι_{y - x₀} ω`, for every covector `a` and base point `x₀`. -/
theorem extDeriv_const_add_smul_curryLeft_sub [CharZero 𝕜] (ω : E [⋀^Fin 2]→L[𝕜] F)
    (a : E [⋀^Fin 1]→L[𝕜] F) (x₀ x : E) :
    extDeriv (fun y ↦ a + (2⁻¹ : 𝕜) • ω.curryLeft (y - x₀)) x = ω := by
  have hfd : HasFDerivAt (fun y ↦ a + (2⁻¹ : 𝕜) • ω.curryLeft (y - x₀))
      ((2⁻¹ : 𝕜) • ω.curryLeft) x := by
    simpa using ((ω.curryLeft.hasFDerivAt.comp x ((hasFDerivAt_id x).sub_const x₀)).const_smul
      (2⁻¹ : 𝕜)).const_add a
  ext m
  have hm : m = ![m 0, m 1] := by
    funext i
    fin_cases i <;> rfl
  have hswap : ω ![m 1, m 0] = -ω ![m 0, m 1] := by
    simpa using ω.map_swap ![m 0, m 1] (i := 0) (j := 1) Fin.zero_ne_one
  rw [hm, TauCeti.extDeriv_apply_pair, hfd.fderiv]
  simp only [FunLike.coe_smul, Pi.smul_apply, smul_apply, curryLeft_apply_apply,
    ← Matrix.vec_single_eq_const, hswap, smul_neg, sub_neg_eq_add, ← add_smul]
  rw [← two_mul, mul_inv_cancel₀ two_ne_zero, one_smul]

end ContinuousAlternatingMap

end
