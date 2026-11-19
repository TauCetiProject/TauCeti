/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Unbundled.IsPowMulUnique
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# The absolute values of `ℂ` extending `|·|`

An absolute value of `ℂ` that restricts to the usual absolute value on `ℝ` is the norm
(`AbsoluteValue.eq_norm_of_apply_ofReal`). Such an absolute value is a multiplicative
`ℝ`-algebra norm on the algebraic extension `ℂ` of the complete field `ℝ`, so it agrees with the
norm by Mathlib's uniqueness of multiplicative algebra norms, `MulAlgebraNorm.unique`. This is the
uniqueness statement behind the isometric Gelfand–Mazur theorem
`NormedAlgebra.Real.exists_algHom_complex_isometry`.

## Main results

* `AbsoluteValue.eq_norm_of_apply_ofReal`: an absolute value of `ℂ` that restricts to `|·|` on
  `ℝ` is the norm.

## References

* E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press
  (2006), §1.2 (Ostrowski's theorem).
-/

public section

namespace AbsoluteValue

/-- An absolute value of `ℂ` that restricts to the usual absolute value on `ℝ` is the norm. -/
theorem eq_norm_of_apply_ofReal (f : AbsoluteValue ℂ ℝ) (h : ∀ r : ℝ, f r = |r|) :
    ⇑f = norm := by
  let g : MulAlgebraNorm ℝ ℂ :=
    { MulRingNorm.mulRingNormEquivAbsoluteValue.symm f with
      smul' r z := by
        simp only [MulRingNorm.mulRingNormEquivAbsoluteValue_symm_apply,
          AddGroupSeminorm.toFun_eq_coe, MulRingSeminorm.toFun_eq_coe,
          MulRingNorm.toMulRingSeminorm_apply, MulRingNorm.ofAbsoluteValue_toFun,
          MulHom.toFun_eq_coe, AbsoluteValue.coe_toMulHom]
        rw [Algebra.smul_def, map_mul, Complex.coe_algebraMap, h, Real.norm_eq_abs] }
  exact congrArg DFunLike.coe (MulAlgebraNorm.unique g (NormedAlgebra.toMulAlgebraNorm ℝ ℂ))

end AbsoluteValue
