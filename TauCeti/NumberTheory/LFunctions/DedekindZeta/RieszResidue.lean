/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ArithmeticDirichletSeries.Riesz.Residue
public import TauCeti.NumberTheory.LFunctions.DedekindZeta.TrivialZeros
import TauCeti.Analysis.SpecialFunctions.Gamma.LeadingCoefficient
import TauCeti.NumberTheory.LFunctions.Data.DedekindZeta

/-!
# The origin and trivial-zero terms of the Dedekind zeta Riesz formula

The origin contributes an affine function of `log y` with slope the unit rank. At `1 - n`,
`n ≥ 2`, the contribution comes from the `r₂` complex places and, when `n` is odd, the `r₁` real
places. The two ladders of negative integers give the decaying terms in the explicit formula.
-/

public section

open Complex NumberField.InfinitePlace TauCeti.Contour

namespace TauCeti.LFunctions

variable (K : Type*) [Field K] [NumberField K]

/-- At the origin, the first Riesz kernel for Dedekind zeta contributes an affine function of
`log y` with slope the unit rank and intercept the finite part of `ζ′_K/ζ_K` plus the unit rank. -/
theorem residue_rieszRemainderMellin_dedekindZetaC_zero {y : ℂ} (hy : y ≠ 0) :
    residue (fun s ↦ rieszRemainderMellin (dedekindZetaC K) s * y ^ s) 0 =
      logDerivFinitePart (dedekindZetaC K) 0 +
        ((nrRealPlaces K : ℂ) + nrComplexPlaces K - 1) * (1 + log y) := by
  have horder : meromorphicOrderAt (dedekindZetaC K) 0 =
      ((nrRealPlaces K : ℤ) + nrComplexPlaces K - 1 : ℤ) := by
    have h := meromorphicOrderAt_Gammaℝ_pow_mul_Gammaℂ_pow_one_sub_nat
      (nrRealPlaces K) (nrComplexPlaces K) (n := 1) le_rfl
    rw [Nat.cast_one, sub_self, ite_eq_right Nat.not_even_one] at h
    rw [← dedekindZetaData_continuedL, (dedekindZetaData K).meromorphicOrderAt_continuedL
      (dedekindZetaData_hasMeromorphicContinuation K).meromorphic, dedekindZetaData_completed,
      meromorphicOrderAt_completedDedekindZeta_zero, funext (dedekindZetaData_gammaFactor K), h,
      sub_neg_eq_add, ← WithTop.coe_add]
    congr 1
  rw [(meromorphic_dedekindZetaC K).residue_rieszRemainderMellin_mul_cpow_zero horder hy]
  push_cast
  norm_num

/-- At `1 - n < 0`, the first Riesz kernel for Dedekind zeta contributes the archimedean zero
multiplicity times `y ^ (1 - n) / ((1 - n) * n)`. The formula includes the zero contribution
when no Gamma factor has a pole there. -/
theorem residue_rieszRemainderMellin_dedekindZetaC_one_sub_nat {n : ℕ} (hn : 2 ≤ n) (y : ℂ) :
    residue (fun s ↦ rieszRemainderMellin (dedekindZetaC K) s * y ^ s) (1 - n) =
      ((if Even n then nrComplexPlaces K else nrRealPlaces K + nrComplexPlaces K : ℕ) : ℂ) *
        y ^ ((1 : ℂ) - n) / ((1 - n) * n) := by
  have h₀ : (1 : ℂ) - n ≠ 0 :=
    sub_ne_zero.mpr (Nat.cast_ne_one.mpr (Nat.ne_of_gt (Nat.lt_of_succ_le hn))).symm
  have hy : AnalyticAt ℂ (fun s : ℂ ↦ y ^ s) (1 - n) := by
    by_cases hy : y = 0
    · subst y
      refine analyticAt_const.congr (f := fun _ : ℂ ↦ (0 : ℂ)) ?_
      filter_upwards [eventually_ne_nhds h₀] with s hs
      exact (zero_cpow hs).symm
    · exact Differentiable.analyticAt (fun _ ↦ differentiableAt_id.const_cpow (.inl hy)) _
  rw [(meromorphic_dedekindZetaC K).residue_rieszRemainderMellin_mul h₀
    (meromorphicOrderAt_dedekindZetaC_one_sub_nat K hn) hy, sub_sub_cancel]
  by_cases h : Even n <;> simp [h]

end TauCeti.LFunctions
