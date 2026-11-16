/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic

/-!
# Conjugate-linear real forms on the plane

In the real coordinates `(a, b)` of `z = a + i b`, multiplication by `i` is the rotation
`(a, b) ↦ (-b, a)`. A real linear form `η : ℝ × ℝ → ℂ` is conjugate linear for it,
`η (-b, a) = -i η (a, b)`, exactly when it is `η (1, 0)` times the conjugate coordinate
`(a, b) ↦ a - i b`, the composition of `Complex.conjCLE` with `Complex.equivRealProdCLM.symm`
(`Complex.forall_apply_neg_snd_fst_eq_iff`). These forms are the `(0,1)`-forms of the plane.
-/

public section

open ComplexConjugate

namespace Complex

/-- The conjugate coordinate `(a, b) ↦ a - i b` on `ℝ × ℝ`. -/
theorem conjCLE_comp_equivRealProdCLM_symm_apply (v : ℝ × ℝ) :
    (conjCLE.toContinuousLinearMap ∘L equivRealProdCLM.symm.toContinuousLinearMap) v =
      v.1 - v.2 * I := by
  simp [equivRealProdCLM_symm_apply, sub_eq_add_neg]

/-- A real linear form `η` on `ℝ × ℝ` satisfies `η (-b, a) = -i η (a, b)` exactly when it is
`η (1, 0)` times the conjugate coordinate `(a, b) ↦ a - i b`. -/
theorem forall_apply_neg_snd_fst_eq_iff (η : ℝ × ℝ →L[ℝ] ℂ) :
    (∀ v : ℝ × ℝ, η (-v.2, v.1) = -(I • η v)) ↔
      η = η (1, 0) • (conjCLE.toContinuousLinearMap ∘L
        equivRealProdCLM.symm.toContinuousLinearMap) := by
  constructor
  · intro h
    -- `η (0, 1) = η (-0, 1) = -i η (1, 0)`, and `η` is determined by its values on `(1, 0)` and
    -- `(0, 1)`.
    have ht : η (0, 1) = -(I * η (1, 0)) := by simpa using h (1, 0)
    refine ContinuousLinearMap.ext fun v ↦ ?_
    have hv : v = v.1 • ((1, 0) : ℝ × ℝ) + v.2 • ((0, 1) : ℝ × ℝ) := by ext <;> simp
    rw [smul_apply, conjCLE_comp_equivRealProdCLM_symm_apply, hv, map_add,
      map_smul, map_smul, ht]
    simp [real_smul]
    ring
  · intro h v
    rw [h]
    simp only [smul_apply, conjCLE_comp_equivRealProdCLM_symm_apply, smul_eq_mul, ofReal_neg]
    linear_combination -(η (1, 0) * v.2) * I_mul_I

end Complex
