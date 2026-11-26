/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LFunctions.DedekindZeta.Completed
import TauCeti.Analysis.SpecialFunctions.Gamma.LeadingCoefficient
import TauCeti.NumberTheory.ArithmeticDirichletSeries.EulerProduct.Analytic
import TauCeti.NumberTheory.LFunctions.Data.DedekindZeta

/-!
# Trivial zeros of the Dedekind zeta function

On the open left half-plane the completed zeta function is nonvanishing by the functional
equation. Thus only the reciprocal Gamma factors contribute to the order of the uncompleted
function there. This gives the multiplicities in the trivial-zero terms of explicit formulas.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII, §5.
-/

public section

open Complex NumberField.InfinitePlace

namespace TauCeti.LFunctions

variable (K : Type*) [Field K] [NumberField K]

/-- The functional equation and Euler product exclude zeros of the completion in `Re s < 0`. -/
theorem completedDedekindZeta_ne_zero_of_re_neg {s : ℂ} (hs : s.re < 0) :
    completedDedekindZeta K s ≠ 0 := by
  have h : 1 < (1 - s).re := by simpa using sub_lt_sub_left hs (1 : ℝ)
  have hd : ((|NumberField.discr K| : ℤ) : ℂ) ≠ 0 := by
    exact_mod_cast abs_ne_zero.mpr (NumberField.discr_ne_zero K)
  rw [← completedDedekindZeta_one_sub K s, completedDedekindZeta_eq_mul_dedekindZeta K h]
  have hpos := zero_lt_one.trans h
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (cpow_ne_zero_iff.mpr (.inl hd))
    (pow_ne_zero _ (Gammaℝ_ne_zero_of_re_pos hpos)))
      (pow_ne_zero _ (Gammaℂ_ne_zero_of_re_pos hpos))) (dedekindZeta_ne_zero_of_one_lt_re h)

/-- On the left half-plane, the multiplicities of the zeros of Dedekind zeta come entirely from
its reciprocal Gamma factors. -/
theorem meromorphicOrderAt_dedekindZetaC_of_re_neg {s : ℂ} (hs : s.re < 0) :
    meromorphicOrderAt (dedekindZetaC K) s =
      meromorphicOrderAt (fun z ↦ (Gammaℝ z)⁻¹ ^ nrRealPlaces K *
        (Gammaℂ z)⁻¹ ^ nrComplexPlaces K) s := by
  have hn (t : ℂ) (ht : 0 ≤ t.re) : s ≠ t := fun he ↦ hs.not_ge (he ▸ ht)
  have ha := analyticAt_completedDedekindZeta K (hn 0 (by simp)) (hn 1 (by simp))
  rw [← dedekindZetaData_continuedL, (dedekindZetaData K).meromorphicOrderAt_continuedL
    (dedekindZetaData_hasMeromorphicContinuation K).meromorphic, dedekindZetaData_completed,
    ha.meromorphicOrderAt_eq,
    analyticOrderAt_eq_zero.mpr (.inr (completedDedekindZeta_ne_zero_of_re_neg K hs))]
  simp only [ENat.map_zero, Nat.cast_zero, WithTop.coe_zero, zero_sub,
    ← (dedekindZetaData K).meromorphicOrderAt_invGammaFactor]
  congr 1
  funext z
  rw [AnalyticLFunctionData.invGammaFactor_def, dedekindZetaData_gammaFactor,
    mul_inv_rev, ← inv_pow, ← inv_pow, mul_comm]

/-- At `1 - n` for `n ≥ 2`, the order of Dedekind zeta is the number of complex places,
plus the number of real places when `n` is odd. -/
theorem meromorphicOrderAt_dedekindZetaC_one_sub_nat {n : ℕ} (hn : 2 ≤ n) :
    meromorphicOrderAt (dedekindZetaC K) (1 - n) =
      (((if Even n then 0 else nrRealPlaces K) + nrComplexPlaces K : ℕ) : ℤ) := by
  have hr : ((1 : ℂ) - n).re < 0 := by simpa [sub_re] using Nat.lt_of_succ_le hn
  rw [meromorphicOrderAt_dedekindZetaC_of_re_neg K hr,
    (analyticAt_inv_Gammaℝ_pow_mul_inv_Gammaℂ_pow _ _ _).meromorphicOrderAt_eq,
    analyticOrderAt_inv_Gammaℝ_pow_mul_inv_Gammaℂ_pow_one_sub _ _ (by omega : 1 ≤ n),
    ENat.map_natCast]

end TauCeti.LFunctions
