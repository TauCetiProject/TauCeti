/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Renewal.Countdown.Convergence
public import TauCeti.Probability.Renewal.Lattice.Mass
public import TauCeti.Probability.Renewal.Lattice.Renewal
public import TauCeti.Probability.Renewal.GapMean

/-!
# The lattice Blackwell renewal theorem

At greatest lattice span `a`, successive increments of the renewal function converge to
`a` times the reciprocal extended mean gap. Infinite mean gives limit zero. Zero increments
are allowed: conditioning them away changes both the renewal mass and the positive-gap mean,
and the two normalization factors cancel.

The proof uses convergence of the irreducible aperiodic countdown chain on its natural state
space. The singleton-mass limit is also exposed, since it identifies the renewal density at
individual lattice locations, including for laws with an atom at zero.

## References

* William Feller, *An Introduction to Probability Theory and Its Applications*, vol. II,
  second edition (1971), Chapter XI, the arithmetic renewal theorem.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology

namespace MeasureTheory.Measure

variable {F : Measure ℝ≥0} [IsProbabilityMeasure F] {a : ℝ≥0}

/-- **Lattice renewal density theorem.** At greatest span, the real mass of the renewal
measure at `n * a` tends to `a` times the reciprocal extended interarrival mean.
Zero gaps and infinite means are included. -/
theorem IsLatticeSpan.tendsto_renewalMeasure_real_mul (ha : F.IsLatticeSpan a)
    (hF : F {0} < 1) (hmax : IsGreatest {b | F.IsLatticeSpan b} a) :
    Tendsto (fun n : ℕ => F.renewalMeasure.real {(n : ℝ≥0) * a}) atTop
      (𝓝 ((a : ℝ) * ((∫⁻ t, (t : ℝ≥0∞) ∂F)⁻¹).toReal)) := by
  let ν := F[|{0}ᶜ].map (fun x ↦ ⌊x / a⌋₊)
  have := isProbabilityMeasure_cond_compl_singleton hF.ne
  have hν : ν {0} = 0 := by
    simp [ν, ha.map_floor_div_cond_compl_zero_apply_singleton]
  have hgcd : Nat.setGcd {n | 0 < ν {n}} = 1 :=
    ha.isGreatest_iff_setGcd_map_floor_div_cond_eq_one.mp hmax
  have hmean : (∫⁻ n, (n : ℝ≥0∞) ∂ν) =
      (∫⁻ t, (t : ℝ≥0∞) ∂F) / ((a : ℝ≥0∞) * (1 - F {0})) := by
    rw [← prob_compl_eq_one_sub (measurableSet_singleton 0)]
    apply F.lintegral_natCast_map_floor_div_cond ha.pos.ne'
    filter_upwards [ha.ae_mem_range] with t ⟨n, hn⟩
    exact ⟨n, hn.symm⟩
  have hq : 1 - F {0} ≠ 0 := (tsub_pos_iff_lt.mpr hF).ne'
  have hqfin : 1 - F {0} ≠ ∞ := ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self
  have hden : (a : ℝ≥0∞) * (1 - F {0}) ≠ 0 :=
    mul_ne_zero (ENNReal.coe_ne_zero.mpr ha.pos.ne') hq
  have hdenfin : (a : ℝ≥0∞) * (1 - F {0}) ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.coe_ne_top hqfin
  have hrate : (1 - F {0})⁻¹ * (∫⁻ n, (n : ℝ≥0∞) ∂ν)⁻¹ =
      (a : ℝ≥0∞) * (∫⁻ t, (t : ℝ≥0∞) ∂F)⁻¹ := by
    rw [hmean, ENNReal.inv_div (Or.inl hdenfin) (Or.inl hden), div_eq_mul_inv]
    calc
      _ = (a : ℝ≥0∞) * ((1 - F {0})⁻¹ * (1 - F {0})) *
          (∫⁻ t, (t : ℝ≥0∞) ∂F)⁻¹ := by ring
      _ = _ := by rw [ENNReal.inv_mul_cancel hq hqfin, mul_one]
  have hlim := (ν.tendsto_countdownKernel_map_pred_pow_zero hν hgcd).const_mul
    ((1 - F {0})⁻¹).toReal
  have hmass (n : ℕ) : F.renewalMeasure.real {(n : ℝ≥0) * a} =
      ((1 - F {0})⁻¹).toReal * (((ν.map Nat.pred).countdownKernel ^ n) 0).real {0} := by
    rw [measureReal_def, ha.renewalMeasure_apply_mul_eq_countdownKernel_pow hF,
      ENNReal.toReal_mul]
    rfl
  have hrateReal : ((1 - F {0})⁻¹).toReal * (∫⁻ n, (n : ℝ≥0∞) ∂ν)⁻¹.toReal =
      (a : ℝ) * (∫⁻ t, (t : ℝ≥0∞) ∂F)⁻¹.toReal := by
    rw [← ENNReal.toReal_mul, hrate, ENNReal.toReal_mul, ENNReal.coe_toReal]
  simpa only [← hmass, hrateReal] using hlim

/-- **Lattice Blackwell theorem.** At greatest span `a`, the increase in expected renewal
count from `n * a` to `(n + 1) * a` tends to `a / μ`, with reciprocal taken in `ℝ≥0∞`.
The initial artificial arrival is excluded from the renewal function, while genuine
zero-time arrivals are retained. Infinite mean gives limit zero. -/
theorem IsLatticeSpan.tendsto_renewalFunction_succ_mul_sub (ha : F.IsLatticeSpan a)
    (hF : F {0} < 1) (hmax : IsGreatest {b | F.IsLatticeSpan b} a) :
    Tendsto (fun n : ℕ => (F.renewalFunction ((n + 1 : ℕ) * a)).toReal -
      (F.renewalFunction ((n : ℝ≥0) * a)).toReal) atTop
      (𝓝 ((a : ℝ) * ((∫⁻ t, (t : ℝ≥0∞) ∂F)⁻¹).toReal)) := by
  let := F.isLocallyFiniteMeasure_renewalMeasure hF
  simpa only [ha.toReal_renewalFunction_succ_mul_sub, Function.comp_def] using
    (ha.tendsto_renewalMeasure_real_mul hF hmax).comp (tendsto_add_atTop_nat 1)

end MeasureTheory.Measure
