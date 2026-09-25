/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Stieltjes
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import TauCeti.Order.Northcott

/-!
# Stieltjes functions from Northcott summatory functions

The inclusive summatory function `A(x) = ∑_{N i ≤ x} w i` of a nonnegative real weight is
continuous from the right and defines a Stieltjes function. Its measure is the weighted sum of
point masses `∑ i, w i • δ_{N i}`. Integrals over `(a, b]` against this measure are finite
weighted sums over the indices whose `N`-value lies in that interval.

## Main definitions

* `TauCeti.summatoryStieltjes`: the summatory function as a `StieltjesFunction ℝ`.

## Main results

* `TauCeti.measure_summatoryStieltjes`: the measure is `∑ i, w i • δ_{N i}`.
* `TauCeti.restrict_Ioc_measure_summatoryStieltjes`: its restriction to `(a, b]` is a finite sum.
* `TauCeti.setIntegral_Ioc_summatoryStieltjes`: integrals are summatory increments.
* `TauCeti.setIntegral_Ioc_summatoryStieltjes_of_lt`: the form from a cutoff below all `N`-values.

## References

* G. Tenenbaum, *Introduction to Analytic and Probabilistic Number Theory*, Chapter I.0.
-/

public section

namespace TauCeti

open MeasureTheory Set Filter
open scoped Topology

variable {ι : Type*} (N : ι → ℕ) [Northcott N]

/-! ### The Stieltjes function and its measure -/

/-- The summatory function `x ↦ ∑_{N i ≤ x} w i` of a nonnegative real weight, as a Stieltjes
function. -/
noncomputable def summatoryStieltjes {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i) : StieltjesFunction ℝ where
  toFun := summatory N w
  mono' := summatory_mono N hw
  right_continuous' := continuousWithinAt_summatory_Ici N w

/-- The Stieltjes function `summatoryStieltjes N hw` evaluates to the summatory function. -/
@[simp]
theorem summatoryStieltjes_apply {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i) (x : ℝ) :
    summatoryStieltjes N hw x = summatory N w x := (rfl)

/-- **The Stieltjes measure of a summatory function** is the sum over the carrier of the point
masses at the `N`-values, weighted by `w`. -/
theorem measure_summatoryStieltjes {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i) :
    (summatoryStieltjes N hw).measure =
      Measure.sum fun i ↦ ENNReal.ofReal (w i) • Measure.dirac (N i : ℝ) := by
  refine Measure.ext_of_Ioc _ _ fun a b hab ↦ ?_
  rw [StieltjesFunction.measure_Ioc, summatoryStieltjes_apply, summatoryStieltjes_apply,
    summatory_sub_summatory_eq_sum_filter N w hab.le,
    ENNReal.ofReal_sum_of_nonneg fun i _ ↦ hw i, Measure.sum_apply _ measurableSet_Ioc]
  simp only [Measure.smul_apply, Measure.dirac_apply' _ measurableSet_Ioc, smul_eq_mul]
  have hmem (i : ι) : i ∈ {j ∈ normLE N b | a < N j} ↔ (N i : ℝ) ∈ Ioc a b := by
    simp only [Finset.mem_filter, mem_normLE, mem_Ioc, and_comm]
  rw [tsum_eq_sum (s := {j ∈ normLE N b | a < N j}) fun i hi ↦ ?_]
  · refine Finset.sum_congr rfl fun i hi ↦ ?_
    rw [indicator_of_mem ((hmem i).mp hi), Pi.one_apply, mul_one]
  · rw [indicator_of_notMem (fun h ↦ hi ((hmem i).mpr h)), mul_zero]

/-- On the interval `(a, b]` the Stieltjes measure of a summatory function is the finite sum of
the weighted point masses of the indices whose `N`-value lies in `(a, b]`. -/
theorem restrict_Ioc_measure_summatoryStieltjes {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i) (a b : ℝ) :
    (summatoryStieltjes N hw).measure.restrict (Ioc a b) =
      ∑ i ∈ {j ∈ normLE N b | a < N j}, ENNReal.ofReal (w i) • Measure.dirac (N i : ℝ) := by
  ext s hs
  rw [Measure.restrict_apply hs, measure_summatoryStieltjes,
    Measure.sum_apply _ (hs.inter measurableSet_Ioc), Measure.finsetSum_apply]
  simp only [Measure.smul_apply, Measure.dirac_apply' _ (hs.inter measurableSet_Ioc),
    Measure.dirac_apply' _ hs, smul_eq_mul]
  have hmem (i : ι) : i ∈ {j ∈ normLE N b | a < N j} ↔ (N i : ℝ) ∈ Ioc a b := by
    simp only [Finset.mem_filter, mem_normLE, mem_Ioc, and_comm]
  rw [tsum_eq_sum (s := {j ∈ normLE N b | a < N j}) fun i hi ↦ ?_]
  · refine Finset.sum_congr rfl fun i hi ↦ ?_
    by_cases his : (N i : ℝ) ∈ s
    · rw [indicator_of_mem (mem_inter his ((hmem i).mp hi)), indicator_of_mem his]
    · rw [indicator_of_notMem (fun h ↦ his h.1), indicator_of_notMem his]
  · rw [indicator_of_notMem (fun h ↦ hi ((hmem i).mpr h.2)), mul_zero]

/-! ### Integrals against the Stieltjes measure -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- **Sums as Stieltjes integrals.** For `a ≤ b`, integrating `g` over `(a, b]` against the
Stieltjes measure `dA` of `A = summatory N w` gives `∑_{a < N i ≤ b} w i • g (N i)`, written as
the increment between `a` and `b` of the summatory function of `i ↦ w i • g (N i)`. -/
theorem setIntegral_Ioc_summatoryStieltjes {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i) (g : ℝ → E)
    {a b : ℝ} (hab : a ≤ b) :
    ∫ t in Ioc a b, g t ∂(summatoryStieltjes N hw).measure =
      summatory N (fun i ↦ w i • g (N i)) b - summatory N (fun i ↦ w i • g (N i)) a := by
  rw [restrict_Ioc_measure_summatoryStieltjes, summatory_sub_summatory_eq_sum_filter N _ hab,
    integral_finsetSum_measure fun i _ ↦
      (integrable_dirac enorm_lt_top).smul_measure ENNReal.ofReal_ne_top]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal (hw i)]

/-- Sums as Stieltjes integrals from a cutoff `a` below every `N`-value: then
`∫_{(a, x]} g dA = ∑_{N i ≤ x} w i • g (N i)` for every real `x`. -/
theorem setIntegral_Ioc_summatoryStieltjes_of_lt {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i) (g : ℝ → E)
    {a : ℝ} (hN : ∀ i, a < N i) (x : ℝ) :
    ∫ t in Ioc a x, g t ∂(summatoryStieltjes N hw).measure =
      summatory N (fun i ↦ w i • g (N i)) x := by
  have hzero {y : ℝ} (hy : y ≤ a) : normLE N y = ∅ :=
    Finset.eq_empty_of_forall_notMem fun i hi ↦
      (hy.trans_lt (hN i)).not_ge ((mem_normLE N).mp hi)
  rcases le_or_gt a x with hax | hxa
  · rw [setIntegral_Ioc_summatoryStieltjes N hw g hax, summatory_apply N _ a, hzero le_rfl,
      Finset.sum_empty, sub_zero]
  · rw [Ioc_eq_empty_of_le hxa.le, Measure.restrict_empty, integral_zero_measure,
      summatory_apply, hzero hxa.le, Finset.sum_empty]

end TauCeti
