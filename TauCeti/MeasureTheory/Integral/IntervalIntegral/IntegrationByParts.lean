/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
# Substituting `u = x²` and `u = c / x` in an interval integral

On an interval of nonnegative reals the map `x ↦ x²` is monotone with derivative `2 x ≥ 0`, so
Mathlib's change of variables `intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg` applies
to any integrand `g`, with no continuity or integrability hypothesis on `g`:
`∫ x in a..b, g (x²) * (2 x) = ∫ u in a²..b², g u`.

Similarly, on any interval not containing `0`, the map `t ↦ c / t` is monotone or antitone with
derivative `-c / t²`, giving both the interval-integrability equivalence and the substitution
identity `∫ t in a..b, (c / t²) • f (c / t) = ∫ u in (c / b)..(c / a), f u` with no continuity
or integrability assumption on `f`.

## Main declarations

* `TauCeti.intervalIntegral.integral_comp_sq_mul`
* `TauCeti.intervalIntegral.intervalIntegrable_div_sq_smul_comp_div_iff`
* `TauCeti.intervalIntegral.integral_div_sq_smul_comp_div`
-/

public section

open MeasureTheory Set

namespace TauCeti

namespace intervalIntegral

/-- **Substituting `u = x²`.** For `0 ≤ a` and `0 ≤ b`,
`∫ x in a..b, g (x²) * (2 x) = ∫ u in a²..b², g u` for every `g : ℝ → ℝ`. -/
theorem integral_comp_sq_mul {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (g : ℝ → ℝ) :
    ∫ x in a..b, g (x ^ 2) * (2 * x) = ∫ u in a ^ 2..b ^ 2, g u :=
  _root_.intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg (f := fun x => x ^ 2)
    (by fun_prop) (fun x _ => by simpa using hasDerivAt_pow 2 x) fun x hx => by
      linarith [(le_min ha hb).trans_lt hx.1]

private theorem continuousOn_const_div_of_notMem {a b c : ℝ} (h0 : (0 : ℝ) ∉ uIcc a b) :
    ContinuousOn (fun t : ℝ ↦ c / t) (uIcc a b) :=
  continuousOn_const.div continuousOn_id fun _ ht h ↦ h0 (h ▸ ht)

private theorem hasDerivAt_const_div_of_mem_Ioo {a b c : ℝ} (h0 : (0 : ℝ) ∉ uIcc a b) :
    ∀ t ∈ Ioo (min a b) (max a b), HasDerivAt (fun t : ℝ ↦ c / t) (-c / t ^ 2) t := by
  intro t ht
  have ht0 : t ≠ 0 := fun h ↦ h0 (h ▸ Ioo_subset_Icc_self ht)
  refine ((hasDerivAt_const t c).div (hasDerivAt_id' t) ht0).congr_deriv ?_
  ring

/-- **Substitution `u = c / t` for interval integrability.** Whenever `0 ∉ uIcc a b`,
`(c / t ^ 2) • f (c / t)` is interval integrable on `a..b` if and only if `f` is interval
integrable on `(c / b)..(c / a)`. -/
theorem intervalIntegrable_div_sq_smul_comp_div_iff {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {a b c : ℝ} (h0 : (0 : ℝ) ∉ uIcc a b) (f : ℝ → E) :
    IntervalIntegrable (fun t ↦ (c / t ^ 2) • f (c / t)) volume a b ↔
      IntervalIntegrable f volume (c / b) (c / a) := by
  have hcont := continuousOn_const_div_of_notMem (c := c) h0
  have hderiv := hasDerivAt_const_div_of_mem_Ioo (c := c) h0
  have hneg :
      (IntervalIntegrable (fun t ↦ (-c / t ^ 2) • (f ∘ fun t ↦ c / t) t) volume a b ↔
          IntervalIntegrable (fun t ↦ (c / t ^ 2) • f (c / t)) volume a b) := by
    have heq : (fun t ↦ (-c / t ^ 2) • (f ∘ fun t ↦ c / t) t) =
        fun t ↦ -((c / t ^ 2) • f (c / t)) := funext fun t ↦ by
      simp [neg_div, neg_smul]
    rw [heq]
    exact ⟨fun h ↦ h.neg.congr fun t _ ↦ by simp, fun h ↦ h.neg⟩
  rw [← hneg]
  rcases le_total 0 c with hc | hc
  · rw [_root_.intervalIntegral.integrable_deriv_smul_comp_iff_of_deriv_nonpos hcont hderiv
        fun t _ ↦ div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hc) (sq_nonneg t),
      IntervalIntegrable.symm_iff]
  · rw [_root_.intervalIntegral.integrable_deriv_smul_comp_iff_of_deriv_nonneg hcont hderiv
        fun t _ ↦ div_nonneg (neg_nonneg.mpr hc) (sq_nonneg t),
      IntervalIntegrable.symm_iff]

/-- **Substituting `u = c / t`.** Whenever `0 ∉ uIcc a b`,
`∫ t in a..b, (c / t ^ 2) • f (c / t) = ∫ u in (c / b)..(c / a), f u` for every
`f : ℝ → E`, with no continuity or integrability hypothesis on `f`. -/
theorem integral_div_sq_smul_comp_div {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {a b c : ℝ} (h0 : (0 : ℝ) ∉ uIcc a b) (f : ℝ → E) :
    ∫ t in a..b, (c / t ^ 2) • f (c / t) = ∫ u in c / b..c / a, f u := by
  have hcont := continuousOn_const_div_of_notMem (c := c) h0
  have hderiv := hasDerivAt_const_div_of_mem_Ioo (c := c) h0
  have hneg :
      ∫ t in a..b, (-c / t ^ 2) • (f ∘ fun t ↦ c / t) t =
        -∫ t in a..b, (c / t ^ 2) • f (c / t) := by
    have heq : (fun t ↦ (-c / t ^ 2) • (f ∘ fun t ↦ c / t) t) =
        fun t ↦ -((c / t ^ 2) • f (c / t)) := funext fun t ↦ by
      simp [neg_div, neg_smul]
    rw [heq, _root_.intervalIntegral.integral_neg]
  rcases le_total 0 c with hc | hc
  · have h := _root_.intervalIntegral.integral_deriv_smul_comp_of_deriv_nonpos (g := f)
      hcont hderiv fun t _ ↦ div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hc) (sq_nonneg t)
    rw [hneg, _root_.intervalIntegral.integral_symm (c / b) (c / a)] at h
    exact neg_injective h
  · have h := _root_.intervalIntegral.integral_deriv_smul_comp_of_deriv_nonneg (g := f)
      hcont hderiv fun t _ ↦ div_nonneg (neg_nonneg.mpr hc) (sq_nonneg t)
    rw [hneg, _root_.intervalIntegral.integral_symm (c / b) (c / a)] at h
    exact neg_injective h

end intervalIntegral

end TauCeti
