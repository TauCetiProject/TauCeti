/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LFunctions.DedekindZeta.Completed
import TauCeti.Analysis.SpecialFunctions.Gamma.LeadingCoefficient
import TauCeti.NumberTheory.ArithmeticDirichletSeries.EulerProduct.Analytic

/-!
# Trivial zeros of the Dedekind zeta function

On the open left half-plane the completed zeta function is nonvanishing by the functional
equation. Thus only the reciprocal Gamma factors contribute to the order of the uncompleted
function there. At the origin one must also subtract the order of the pole of the completion.
These orders give the multiplicities in the trivial-zero and origin terms of explicit formulas.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII, §5.
-/

public section

open Complex Filter NumberField.InfinitePlace Set
open scoped Topology

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

/-- The order of the uncompleted zeta function is the order of the completion plus that of the
reciprocal Gamma factors. This equality includes the poles of the completion at `0` and `1`. -/
theorem meromorphicOrderAt_dedekindZetaC_eq_add (s : ℂ) :
    meromorphicOrderAt (dedekindZetaC K) s =
      meromorphicOrderAt (completedDedekindZeta K) s +
        meromorphicOrderAt (fun z ↦ (Gammaℝ z)⁻¹ ^ nrRealPlaces K *
          (Gammaℂ z)⁻¹ ^ nrComplexPlaces K) s := by
  let D (z : ℂ) := ((|NumberField.discr K| : ℤ) : ℂ) ^ (-z / 2)
  let G (z : ℂ) := (Gammaℝ z)⁻¹ ^ nrRealPlaces K * (Gammaℂ z)⁻¹ ^ nrComplexPlaces K
  have hd : 0 < ((|NumberField.discr K| : ℤ) : ℝ) := by
    exact_mod_cast abs_pos.mpr (NumberField.discr_ne_zero K)
  have hD : AnalyticAt ℂ D s :=
    analyticAt_const.cpow (by fun_prop) (by
      rw [← ofReal_intCast]
      exact ofReal_mem_slitPlane.mpr hd)
  have hD₀ : D s ≠ 0 := cpow_ne_zero_iff.mpr (.inl (by
    rw [← ofReal_intCast]
    exact ofReal_ne_zero.mpr hd.ne'))
  have hG : AnalyticAt ℂ G s := by
    simpa only [G, inv_pow] using
      analyticAt_inv_Gammaℝ_pow_mul_inv_Gammaℂ_pow (nrRealPlaces K) (nrComplexPlaces K) s
  have heq : dedekindZetaC K =ᶠ[𝓝[≠] s] D * (completedDedekindZeta K * G) := by
    have hne (a : ℂ) : ∀ᶠ z in 𝓝[≠] s, z ≠ a := by
      by_cases h : s = a
      · subst a
        exact self_mem_nhdsWithin
      · exact (eventually_ne_nhds h).filter_mono nhdsWithin_le_nhds
    filter_upwards [hne 0, hne 1] with z hz₀ hz₁
    rw [dedekindZetaC_eq_mul_completedDedekindZeta K hz₀ hz₁]
    simp only [Pi.mul_apply, G, D]
    ring
  rw [meromorphicOrderAt_congr heq, meromorphicOrderAt_mul_of_ne_zero hD hD₀,
    meromorphicOrderAt_mul (meromorphic_completedDedekindZeta K s) hG.meromorphicAt]

/-- On the left half-plane, the multiplicities of the zeros of Dedekind zeta come entirely from
its reciprocal Gamma factors. -/
theorem meromorphicOrderAt_dedekindZetaC_of_re_neg {s : ℂ} (hs : s.re < 0) :
    meromorphicOrderAt (dedekindZetaC K) s =
      meromorphicOrderAt (fun z ↦ (Gammaℝ z)⁻¹ ^ nrRealPlaces K *
        (Gammaℂ z)⁻¹ ^ nrComplexPlaces K) s := by
  have hn (t : ℂ) (ht : 0 ≤ t.re) : s ≠ t := fun he ↦ hs.not_ge (he ▸ ht)
  have ha := analyticAt_completedDedekindZeta K (hn 0 (by simp)) (hn 1 (by simp))
  rw [meromorphicOrderAt_dedekindZetaC_eq_add, ha.meromorphicOrderAt_eq,
    analyticOrderAt_eq_zero.mpr (.inr (completedDedekindZeta_ne_zero_of_re_neg K hs))]
  simp

/-- The order of Dedekind zeta at the origin is the unit rank `r₁ + r₂ - 1`. -/
theorem meromorphicOrderAt_dedekindZetaC_zero :
    meromorphicOrderAt (dedekindZetaC K) 0 =
      ((nrRealPlaces K : ℤ) + nrComplexPlaces K - 1 : ℤ) := by
  have h := analyticOrderAt_inv_Gammaℝ_pow_mul_inv_Gammaℂ_pow_one_sub
    (nrRealPlaces K) (nrComplexPlaces K) (n := 1) le_rfl
  rw [Nat.cast_one, sub_self, ite_eq_right Nat.not_even_one] at h
  rw [meromorphicOrderAt_dedekindZetaC_eq_add, meromorphicOrderAt_completedDedekindZeta_zero,
    (analyticAt_inv_Gammaℝ_pow_mul_inv_Gammaℂ_pow _ _ _).meromorphicOrderAt_eq, h,
    ENat.map_natCast]
  norm_cast

end TauCeti.LFunctions
