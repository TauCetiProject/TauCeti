/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Measure.ResolventTransform.Basic
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-!
# Atoms from the resolvent transform

For a finite measure on the real line, multiplying the imaginary part of its resolvent
transform by `η` and approaching `a` vertically from above recovers the mass of `{a}`.
This detects atoms, including atoms at endpoints when using Stieltjes inversion.

We use Mathlib's `MeasureTheory.resolventTransform`, with sign `(x - z)⁻¹`, not
`(z - x)⁻¹`. No moment assumptions are needed.

## References

* Anderson, Guionnet and Zeitouni, *An Introduction to Random Matrices*, §2.4.1,
  for the Stieltjes transform and its inversion (Theorem 2.4.3).
-/

public section

noncomputable section

open MeasureTheory Filter Complex
open scoped Topology

namespace Real

/-- The rescaled Poisson kernels converge pointwise to the indicator of the singleton
at their center as the height tends to zero from above. -/
theorem tendsto_sq_div_sq_add_sq_indicator (a x : ℝ) :
    Tendsto (fun η : ℝ => η ^ 2 / ((x - a) ^ 2 + η ^ 2)) (𝓝[>] 0)
      (𝓝 (Set.indicator {a} (fun _ : ℝ => (1 : ℝ)) x)) := by
  by_cases hx : x = a
  · subst x
    simp only [Set.indicator_of_mem (Set.mem_singleton a), sub_self, zero_pow,
      ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_add]
    apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin] with η hη
    exact (div_self (pow_ne_zero 2 (ne_of_gt hη))).symm
  · have hxa : x ∉ ({a} : Set ℝ) := by simpa using hx
    rw [Set.indicator_of_notMem hxa]
    have hden : (x - a) ^ 2 + (0 : ℝ) ^ 2 ≠ 0 := by
      simpa using pow_ne_zero 2 (sub_ne_zero.mpr hx)
    have ht : Tendsto (fun η : ℝ => η) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
    simpa only [zero_pow (by decide : 2 ≠ 0), zero_div] using!
      (ht.pow 2).div (tendsto_const_nhds.add (ht.pow 2)) hden

end Real

namespace MeasureTheory

variable {μ : Measure ℝ} [IsFiniteMeasure μ]

/-- The rescaled imaginary transform is an integral of kernels taking values in `[0,1]`. -/
theorem mul_im_resolventTransform {a η : ℝ} :
    η * (resolventTransform μ ((a : ℂ) + η * I)).im =
      ∫ x, η ^ 2 / ((x - a) ^ 2 + η ^ 2) ∂μ := by
  rw [im_resolventTransform, ← integral_const_mul]
  congr 1
  ext x
  simp [sq, mul_div_assoc]

/-- **Atom recovery for the Stieltjes transform.** Approaching `a` vertically from the upper
half-plane, `η Im m(a + iη)` tends to the mass of `{a}`. The mass is real-valued since `μ`
is finite. -/
theorem tendsto_mul_im_resolventTransform (a : ℝ) :
    Tendsto (fun η : ℝ => η * (resolventTransform μ ((a : ℂ) + η * I)).im)
      (𝓝[>] 0) (𝓝 (μ.real {a})) := by
  have hlim : Tendsto (fun η : ℝ => ∫ x, η ^ 2 / ((x - a) ^ 2 + η ^ 2) ∂μ)
      (𝓝[>] 0) (𝓝 (∫ x, Set.indicator {a} (fun _ : ℝ => (1 : ℝ)) x ∂μ)) := by
    apply tendsto_integral_filter_of_dominated_convergence (fun _ => (1 : ℝ))
    · exact Eventually.of_forall fun η =>
        (by fun_prop : Measurable (fun x : ℝ => η ^ 2 / ((x - a) ^ 2 + η ^ 2))).aestronglyMeasurable
    · filter_upwards [self_mem_nhdsWithin] with η hη
      have hpos : 0 < η := hη
      exact ae_of_all _ fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        exact (div_le_one (by positivity : 0 < (x - a) ^ 2 + η ^ 2)).2
          (by nlinarith [sq_nonneg (x - a)])
    · exact integrable_const 1
    · exact ae_of_all _ (Real.tendsto_sq_div_sq_add_sq_indicator a)
  have heq : (∫ x, Set.indicator {a} (fun _ : ℝ => (1 : ℝ)) x ∂μ) = μ.real {a} := by
    exact integral_indicator_one (measurableSet_singleton a)
  rw [heq] at hlim
  simpa only [mul_im_resolventTransform] using hlim

end MeasureTheory
