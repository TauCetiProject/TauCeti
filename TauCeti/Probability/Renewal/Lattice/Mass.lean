/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Renewal.Lattice.Gap
public import TauCeti.Probability.Renewal.Countdown.Mass
public import TauCeti.Probability.Renewal.PositiveIncrements

/-!
# Lattice renewal masses and the countdown chain

At a lattice time `n * a`, the renewal mass is the return probability of the countdown
chain for positive gaps in integer units, divided by the probability of a positive gap.
The factor accounts for zero-increment clusters, including the cluster at time zero.
The identity requires neither greatest span nor finite mean. It connects lattice renewal
limits with convergence of transition probabilities of the countdown chain.

## References

* William Feller, *An Introduction to Probability Theory and Its Applications*, vol. II,
  second edition (1971), Chapter XI.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace MeasureTheory.Measure

variable {μ : Measure ℝ≥0} {a : ℝ≥0}

/-- Dividing a lattice law by its span transports each lattice renewal atom to the
corresponding integer renewal atom. -/
theorem IsLatticeSpan.renewalMeasure_apply_mul [SFinite μ]
    (ha : μ.IsLatticeSpan a) (n : ℕ) :
    μ.renewalMeasure {(n : ℝ≥0) * a} =
      (μ.map (fun x ↦ ⌊x / a⌋₊)).renewalMeasure {n} := by
  let ν := μ.map (fun x ↦ ⌊x / a⌋₊)
  have hmap : ν.renewalMeasure.map (fun k : ℕ ↦ (k : ℝ≥0) * a) = μ.renewalMeasure := by
    have hf : ⇑(multiplesHom ℝ≥0 a) = (fun k : ℕ ↦ (k : ℝ≥0) * a) := by
      ext k
      simp [nsmul_eq_mul]
    have h := map_renewalMeasure ν (multiplesHom ℝ≥0 a) (measurable_of_countable _)
    simpa only [hf, ν, ha.map_mul_map_floor_div] using h
  rw [← hmap, map_apply (measurable_of_countable _) (measurableSet_singleton _)]
  congr 1
  ext k
  simp [mul_left_inj' ha.pos.ne']

/-- The lattice renewal mass is the countdown return probability divided by the chance
of a positive gap. Zero-increment clusters are retained, also at time zero. The reset law
is the conditional positive gap in lattice units, minus one. -/
theorem IsLatticeSpan.renewalMeasure_apply_mul_eq_countdownKernel_pow [IsProbabilityMeasure μ]
    (ha : μ.IsLatticeSpan a) (hμ : μ {0} < 1) (n : ℕ) :
    μ.renewalMeasure {(n : ℝ≥0) * a} = (1 - μ {0})⁻¹ *
      (((μ[|{0}ᶜ].map (fun x ↦ ⌊x / a⌋₊)).map Nat.pred).countdownKernel ^ n) 0 {0} := by
  have := isProbabilityMeasure_cond_compl_singleton hμ.ne
  have hzero : (μ[|{0}ᶜ].map (fun x ↦ ⌊x / a⌋₊)) {0} = 0 := by
    simp [ha.map_floor_div_cond_compl_zero_apply_singleton]
  rw [renewalMeasure_eq_inv_smul_cond_compl_zero hμ, smul_apply, smul_eq_mul,
    prob_compl_eq_one_sub (measurableSet_singleton 0),
    (ha.cond {0}ᶜ).renewalMeasure_apply_mul,
    renewalMeasure_apply_singleton_eq_countdownKernel_pow _ hzero]

end MeasureTheory.Measure
