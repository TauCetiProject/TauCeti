/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Renewal.Equation
public import TauCeti.Probability.Renewal.LocalBound

/-!
# Constant local renewal limits

The renewal tail identity can be written as an integral, against the interarrival law,
of the renewal mass in a backward window. The coefficient of any constant local limit
equals the inverse extended mean: dominated convergence identifies it for finite mean, while
Fatou's lemma forces it to vanish for infinite mean. The local renewal bound supplies
the domination, with no moment assumptions beyond the finite mean in that case.

These results identify the coefficient after local limits have been shown to be constant;
they do not assert existence of local limits.

The backward window is open on the left and closed on the right. This retains arrivals
at the observation time and treats zero increments without discarding their clusters.

## References

* W. Feller, *An Introduction to Probability Theory and Its Applications*, volume II,
  second edition (1971), Chapter XI, identification of the constant in renewal limits.
-/

public section

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

namespace MeasureTheory.Measure

variable (F : Measure ℝ≥0) [IsProbabilityMeasure F]

private theorem eq_inv_mean_of_tendsto_backwardWindow
    (hF : F {0} < 1) {t : ℕ → ℝ≥0} {c : ℝ≥0∞}
    (hconv : ∀ u : ℝ≥0, Tendsto
      (fun n ↦ F.renewalMeasure {s | s ≤ t n ∧ t n < s + u}) atTop (𝓝 (c * u))) :
    c = (∫⁻ u, (u : ℝ≥0∞) ∂F)⁻¹ := by
  let W (n : ℕ) (u : ℝ≥0) := F.renewalMeasure {s | s ≤ t n ∧ t n < s + u}
  have hW (n : ℕ) : Measurable (W n) :=
    Monotone.measurable fun u v huv ↦ measure_mono fun s hs ↦
      ⟨hs.1, hs.2.trans_le (add_le_add_right huv s)⟩
  by_cases hmean : (∫⁻ u, (u : ℝ≥0∞) ∂F) = ∞
  · -- Fatou alone suffices when the mean is infinite.
    have hfatou : c * (∫⁻ u, (u : ℝ≥0∞) ∂F) ≤ 1 := by
      rw [← lintegral_const_mul c measurable_coe_nnreal_ennreal]
      calc
        _ = ∫⁻ u, liminf (fun n ↦ W n u) atTop ∂F := by
          apply lintegral_congr
          intro u
          exact (hconv u).liminf_eq.symm
        _ ≤ liminf (fun n ↦ ∫⁻ u, W n u ∂F) atTop := lintegral_liminf_le hW
        _ = 1 := by
          simp only [W, F.lintegral_renewalMeasure_backwardWindow hF, liminf_const]
    rw [hmean, ENNReal.inv_top]
    by_contra hc
    simp [hmean, hc] at hfatou
  · -- The local renewal bound gives a finite-mean integrable envelope.
    have hbound (n : ℕ) (u : ℝ≥0) : W n u ≤ F.renewalMeasure (Iic u) := by
      apply le_trans (measure_mono ?_) (F.renewalMeasure_Icc_add_le (t n - u) u)
      intro s hs
      exact ⟨tsub_le_iff_right.mpr (by simpa [add_comm] using hs.2.le),
        hs.1.trans (le_tsub_add : t n ≤ t n - u + u)⟩
    have hdom := tendsto_lintegral_of_dominated_convergence
      (fun u ↦ F.renewalMeasure (Iic u)) hW
      (fun n ↦ ae_of_all _ (hbound n)) (F.lintegral_renewalMeasure_Iic_lt_top hF hmean).ne
      (ae_of_all _ hconv)
    simp only [W, F.lintegral_renewalMeasure_backwardWindow hF] at hdom
    have hone : c * (∫⁻ u, (u : ℝ≥0∞) ∂F) = 1 := by
      rw [← lintegral_const_mul c measurable_coe_nnreal_ennreal]
      exact tendsto_nhds_unique hdom tendsto_const_nhds
    exact ENNReal.eq_inv_of_mul_eq_one_left hone

/-- If `F {0} < 1`, `t n → ∞`, and `U((t n - u, t n]) → c * u` for every `u`, then
`c` is the inverse extended mean `(∫⁻ u, u ∂F)⁻¹`. The statement applies along subsequences
and needs neither a nonlattice nor a finite-mean assumption. In particular `c = 0` for
infinite mean. -/
theorem eq_inv_mean_of_tendsto_renewalMeasure_Ioc
    (hF : F {0} < 1) {t : ℕ → ℝ≥0} (ht : Tendsto t atTop atTop) {c : ℝ≥0∞}
    (hlim : ∀ u : ℝ≥0, Tendsto
      (fun n ↦ F.renewalMeasure (Ioc (t n - u) (t n))) atTop (𝓝 (c * u))) :
    c = (∫⁻ u, (u : ℝ≥0∞) ∂F)⁻¹ := by
  refine F.eq_inv_mean_of_tendsto_backwardWindow hF (t := t) ?_
  intro u
  apply (hlim u).congr'
  filter_upwards [ht.eventually (eventually_ge_atTop u)] with n hn
  congr 1
  ext s
  simp only [mem_ofPred_eq, mem_Ioc]
  have hiff : t n - u < s ↔ t n < s + u := by
    rw [tsub_lt_iff_left hn]
    simp [add_comm]
  exact and_comm.trans (and_congr_right fun _ ↦ hiff)

end MeasureTheory.Measure
