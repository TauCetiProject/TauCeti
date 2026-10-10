/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Grönwall's inequality in integral form

Mathlib's Grönwall inequality (`le_gronwallBound_of_liminf_deriv_right_le`) bounds a function by
a bound on its derivative. Energy estimates for evolution equations instead produce a bound on a
function by an integral of itself: a continuous `φ` with `φ t ≤ c + K ∫ₐᵗ φ` on `[a, b]`, for
some `K ≥ 0`. This file proves that such a `φ` satisfies `φ t ≤ c exp (K (t - a))`
(`TauCeti.le_mul_exp_of_le_add_mul_integral`).

The proof applies the differential form to the primitive `Ψ t = ∫ₐᵗ φ`, whose derivative `φ` is
at most `c + K Ψ`, and then uses `K ≥ 0` to pass from the bound on `Ψ` back to `φ`. Without
`K ≥ 0` the statement is false: a very negative stretch of `φ` makes `c + K ∫ₐᵗ φ` large.

## References

* T. H. Gronwall, *Note on the derivatives with respect to a parameter of the solutions of a
  system of differential equations*, Ann. of Math. **20** (1919), 292–296.
* L. C. Evans, *Partial Differential Equations*, 2nd ed., Appendix B.2.
-/

public section

open Set Filter Real MeasureTheory
open scoped Topology

namespace TauCeti

/-- **Grönwall's inequality, integral form.** If `φ` is continuous on `[a, b]`, `0 ≤ K` and
`φ t ≤ c + K ∫ₐᵗ φ` for every `t ∈ [a, b]`, then `φ t ≤ c exp (K (t - a))` on `[a, b]`. -/
theorem le_mul_exp_of_le_add_mul_integral {φ : ℝ → ℝ} {a b c K : ℝ}
    (hφ : ContinuousOn φ (Icc a b)) (hK : 0 ≤ K)
    (h : ∀ t ∈ Icc a b, φ t ≤ c + K * ∫ s in a..t, φ s) :
    ∀ t ∈ Icc a b, φ t ≤ c * exp (K * (t - a)) := by
  intro t ht
  have hab : a ≤ b := ht.1.trans ht.2
  have hint : IntegrableOn φ (Icc a b) := hφ.integrableOn_Icc
  -- The primitive `Ψ` satisfies `Ψ a = 0` and `Ψ' = φ ≤ c + K Ψ` from the right on `[a, b)`.
  have hΨ : ContinuousOn (fun t ↦ ∫ s in a..t, φ s) (Icc a b) := by
    have := intervalIntegral.continuousOn_primitive_interval (μ := volume)
      (by rwa [uIcc_of_le hab] : IntegrableOn φ (uIcc a b))
    rwa [uIcc_of_le hab] at this
  have hderiv (x : ℝ) (hx : x ∈ Ico a b) :
      HasDerivWithinAt (fun t ↦ ∫ s in a..t, φ s) (φ x) (Ici x) x := by
    have hmem : Icc a b ∈ 𝓝[>] x := Icc_mem_nhdsGT_of_mem hx
    have hsub : uIcc a x ⊆ Icc a b := by
      rw [uIcc_of_le hx.1]
      exact Icc_subset_Icc_right hx.2.le
    refine intervalIntegral.integral_hasDerivWithinAt_right (hint.mono_set hsub).intervalIntegrable
      ?_ ((hφ x (Ico_subset_Icc_self hx)).mono_of_mem_nhdsWithin hmem)
    exact (hφ.stronglyMeasurableAtFilter_nhdsWithin measurableSet_Icc x).filter_mono
      (nhdsWithin_le_of_mem hmem)
  have hgr := le_gronwallBound_of_liminf_deriv_right_le (δ := 0) (K := K) (ε := c) hΨ
    (fun x hx r hr ↦ (hderiv x hx).liminf_right_slope_le hr) (by simp)
    (fun x hx ↦ by linarith [h x (Ico_subset_Icc_self hx)]) t ht
  -- Hence `φ t ≤ c + K Ψ t ≤ c + K gronwallBound 0 K c (t - a) = c exp (K (t - a))`.
  calc φ t ≤ c + K * ∫ s in a..t, φ s := h t ht
    _ ≤ c + K * gronwallBound 0 K c (t - a) := by gcongr
    _ = c * exp (K * (t - a)) := by
        rcases hK.eq_or_lt with rfl | hK
        · simp
        · rw [gronwallBound_of_K_ne_0 hK.ne']
          field_simp
          ring

end TauCeti
