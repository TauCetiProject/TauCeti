/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Hypoexponential.PDF
import TauCeti.Probability.Distributions.Gamma.Pi
import TauCeti.Probability.Distributions.Gamma.PDF

/-!
# Strict positivity of hypoexponential densities

The density of a nonempty sum of independent positive-rate exponential variables is strictly
positive at every positive point, even when rates coincide. More precisely, if `R` bounds all
rates from above, the density dominates the Erlang density of the same number of summands and
rate `R`, multiplied by `∏ i, r i / R`.

This comparison first holds for the product exponential measures and survives the sum
pushforward. Continuity on the positive half-line upgrades the resulting almost-everywhere
density bound to a pointwise one. Thus strict positivity does not depend on the signs of the
partial-fraction coefficients.

## References

* S. M. Ross, *Introduction to Probability Models*, 12th ed., Academic Press (2019), Chapter 5.
-/

public section

noncomputable section

open Finset MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal Nat

namespace TauCeti.Probability

variable {ι : Type*} [Fintype ι] {r : ι → ℝ} {R x : ℝ}

/-- A positive multiple of the common-rate Erlang law is bounded by the hypoexponential law
when the common rate bounds all the individual rates from above. -/
theorem smul_gammaMeasure_le_hypoexponentialMeasure [Nonempty ι]
    (hr : ∀ i, 0 < r i) (hR : ∀ i, r i ≤ R) :
    ENNReal.ofReal (∏ i, r i / R) • gammaMeasure (Fintype.card ι) R ≤
      hypoexponentialMeasure r := by
  have hRpos : 0 < R := (hr (Classical.arbitrary ι)).trans_le (hR _)
  have hfactor (i : ι) (y : ℝ) :
      ENNReal.ofReal (r i / R) * gammaPDF 1 R y ≤ gammaPDF 1 (r i) y := by
    rcases le_or_gt 0 y with hy | hy
    · simp only [gammaPDF_eq, ite_eq_left hy, rpow_one, Gamma_one, div_one, sub_self,
        rpow_zero, mul_one]
      rw [← ENNReal.ofReal_mul (div_nonneg (hr i).le hRpos.le)]
      apply ENNReal.ofReal_le_ofReal
      calc
        r i / R * (R * exp (-(R * y))) = r i * exp (-(R * y)) := by field_simp
        _ ≤ r i * exp (-(r i * y)) :=
          mul_le_mul_of_nonneg_left (exp_le_exp.2 (neg_le_neg (mul_le_mul_of_nonneg_right
            (hR i) hy))) (hr i).le
    · simp [gammaPDF_of_neg hy]
  have hpi :
      ENNReal.ofReal (∏ i, r i / R) • (Measure.pi fun _ : ι ↦ gammaMeasure 1 R) ≤
        Measure.pi fun i ↦ gammaMeasure 1 (r i) := by
    rw [pi_gammaMeasure_eq_withDensity, pi_gammaMeasure_eq_withDensity,
      ← withDensity_smul' _ _ ENNReal.ofReal_ne_top]
    apply withDensity_mono
    filter_upwards [] with y
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [ENNReal.ofReal_prod_of_nonneg (fun i _ ↦ (div_pos (hr i) hRpos).le),
      ← prod_mul_distrib]
    exact prod_le_prod fun i _ ↦ hfactor i (y i)
  have hmap := Measure.map_mono hpi (by fun_prop : Measurable fun y : ι → ℝ ↦ ∑ i, y i)
  rw [Measure.map_smul _ (by fun_prop)] at hmap
  rw [hypoexponentialMeasure_eq_map hr]
  simpa only [map_sum_pi_gammaMeasure (fun _ ↦ one_pos) hRpos,
    sum_const, card_univ, nsmul_eq_mul, mul_one, expMeasure] using hmap

/-- The common-rate Erlang lower bound for a hypoexponential density holds at every positive
point, including for repeated rates. -/
theorem mul_gammaPDFReal_le_hypoexponentialPDFReal [Nonempty ι]
    (hr : ∀ i, 0 < r i) (hR : ∀ i, r i ≤ R) (hx : 0 < x) :
    (∏ i, r i / R) * gammaPDFReal (Fintype.card ι) R x ≤ hypoexponentialPDFReal r x := by
  have hc : 0 ≤ ∏ i, r i / R := prod_nonneg fun i _ ↦
    (div_pos (hr i) ((hr (Classical.arbitrary ι)).trans_le (hR _))).le
  have hmeas := smul_gammaMeasure_le_hypoexponentialMeasure hr hR
  rw [gammaMeasure, hypoexponentialMeasure_eq_withDensity hr,
    ← withDensity_smul _ (measurable_gammaPDF _ _)] at hmeas
  have hae : (fun y ↦ ENNReal.ofReal (∏ i, r i / R) *
      gammaPDF (Fintype.card ι) R y) ≤ᵐ[volume] hypoexponentialPDF r := by
    apply ae_le_of_forall_setLIntegral_le_of_sigmaFinite
      ((measurable_gammaPDF _ _).const_mul _)
    intro s hs _
    simpa only [withDensity_apply _ hs, Pi.smul_apply, smul_eq_mul] using hmeas s
  have haeReal : (fun y ↦ (∏ i, r i / R) * gammaPDFReal (Fintype.card ι) R y) ≤ᵐ[volume]
      hypoexponentialPDFReal r := by
    filter_upwards [hae] with y hy
    rw [gammaPDF, ← ENNReal.ofReal_mul hc, hypoexponentialPDF_eq_ofReal] at hy
    exact (ENNReal.ofReal_le_ofReal_iff (hypoexponentialPDFReal_nonneg r y)).1 hy
  -- Both formulas are continuous on the open half-line; use the existing a.e.-equality API
  -- on their maximum to upgrade the a.e. inequality.
  have hleft : ContinuousOn (fun y ↦ (∏ i, r i / R) *
      gammaPDFReal (Fintype.card ι) R y) (Ioi 0) :=
    (continuousOn_gammaPDFReal (Fintype.card ι) R).const_mul _
  have hright := continuousOn_hypoexponentialPDFReal r
  have heq := Measure.eqOn_open_of_ae_eq
    (ae_restrict_of_ae (haeReal.mono fun y hy ↦ max_eq_right hy))
    isOpen_Ioi (hleft.sup hright) hright hx
  exact (max_eq_right_iff).1 heq

/-- The density of a nonempty valid hypoexponential law is strictly positive on `(0, ∞)`. -/
theorem hypoexponentialPDFReal_pos [Nonempty ι] (hr : ∀ i, 0 < r i) (hx : 0 < x) :
    0 < hypoexponentialPDFReal r x := by
  have hR : ∀ i, r i ≤ ∑ j, r j := fun i ↦
    single_le_sum (fun j _ ↦ (hr j).le) (mem_univ i)
  have hRpos : 0 < ∑ i, r i := sum_pos (fun i _ ↦ hr i) univ_nonempty
  exact (mul_pos (prod_pos fun i _ ↦ div_pos (hr i) hRpos)
    (gammaPDFReal_pos (Nat.cast_pos.2 Fintype.card_pos) hRpos hx)).trans_le
      (mul_gammaPDFReal_le_hypoexponentialPDFReal hr hR hx)

/-- For a nonempty family, positivity of the real density characterizes valid rates and
positive arguments. -/
@[simp]
theorem hypoexponentialPDFReal_pos_iff [Nonempty ι] :
    0 < hypoexponentialPDFReal r x ↔ (∀ i, 0 < r i) ∧ 0 < x := by
  by_cases hr : ∀ i, 0 < r i
  · by_cases hx : 0 < x
    · exact iff_of_true (hypoexponentialPDFReal_pos hr hx) ⟨hr, hx⟩
    · simp [hr, hx, hypoexponentialPDFReal_of_nonpos r (not_lt.1 hx)]
  · simp [hr]

end TauCeti.Probability
