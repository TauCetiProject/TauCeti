/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Probability.CDF
public import TauCeti.Data.Fin.Tuple.OrderStatistic
import TauCeti.MeasureTheory.Measure.PiWithDensity
import TauCeti.Probability.Cdf
import TauCeti.Probability.Distributions.Beta.Cdf
import TauCeti.Probability.Distributions.Beta.NatShape
import TauCeti.Probability.Distributions.OrderStatistic.Basic
import TauCeti.Probability.Distributions.OrderStatistic.Joint
import TauCeti.Probability.Quantile

/-!
# Densities of order statistics

Let `μ` be a probability law on `ℝ` with density `g` with respect to Lebesgue measure, and sort
an iid sample of size `n` from `μ`. The vector of order statistics then has density
`n! ∏ i, g (x i)` on the strictly increasing tuples and zero elsewhere, and the `j`-th order
statistic (counted from `0`) has density

`n! / (j! (n - j - 1)!) F(x) ^ j (1 - F(x)) ^ (n - j - 1) g(x)`,

where `F = cdf μ`.

The joint density combines the chamber formula
`TauCeti.Probability.map_orderStatistics_pi` with the product of densities
`TauCeti.pi_withDensity₀`. The marginal density compares distribution functions: the
distribution function of the `j`-th order statistic is the beta distribution function with
shapes `j + 1` and `n - j` evaluated at `F`, and the probability integral transform
`MeasureTheory.Measure.cdf_map_eq_volume_restrict` moves the polynomial beta density back
along `F`.

## Main results

* `TauCeti.Probability.map_orderStatistics_pi_eq_withDensity` — the joint density;
* `TauCeti.Probability.map_orderStatistic_pi_eq_withDensity` — the marginal density.

## References

* G. Casella and R. L. Berger, *Statistical Inference*, 2nd ed., Duxbury, 2002, Thm 5.4.4,
  p. 186 (the marginal density), and p. 187 (the joint density).

The proofs are adapted from the lean-CKSD project (<https://github.com/bjbraams/lean-CKSD>),
file `CKSD/Inference/Families.lean`.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace TauCeti.Probability

variable {n : ℕ} {μ : Measure ℝ} [IsProbabilityMeasure μ] {g : ℝ → ℝ≥0∞}

/-- **Joint density of the order statistics.** If `μ` has density `g` with respect to Lebesgue
measure, the vector of order statistics of an iid sample of size `n` from `μ` has density
`n! ∏ i, g (x i)` on the strictly increasing tuples and zero elsewhere. -/
theorem map_orderStatistics_pi_eq_withDensity (hg : AEMeasurable g)
    (hμ : μ = volume.withDensity g) :
    (Measure.pi fun _ : Fin n => μ).map (fun x i => orderStatistic i x) =
      volume.withDensity ({x : Fin n → ℝ | StrictMono x}.indicator
        fun x => n.factorial * ∏ i, g (x i)) := by
  have : NullSingletonClass μ := by rw [hμ]; infer_instance
  have : SigmaFinite (volume.withDensity g) := by rw [← hμ]; infer_instance
  have hC : MeasurableSet {x : Fin n → ℝ | StrictMono x} := measurableSet_setOf_strictMono
  rw [map_orderStatistics_pi, hμ, pi_withDensity₀ (fun _ => volume) fun _ => hg, ← volume_pi,
    restrict_withDensity hC, ← withDensity_indicator hC, ← Nat.cast_smul_eq_nsmul ℝ≥0∞,
    ← withDensity_smul' _ _ (ENNReal.natCast_ne_top _)]
  congr 1
  funext x
  simp only [Pi.smul_apply, smul_eq_mul, indicator_mul_right]

/-- **Marginal density of an order statistic.** If `μ` has density `g` with respect to Lebesgue
measure and `F = cdf μ`, the `j`-th order statistic (counted from `0`) of an iid sample of size
`n` from `μ` has density `n! / (j! (n - j - 1)!) F(x) ^ j (1 - F(x)) ^ (n - j - 1) g(x)`. -/
theorem map_orderStatistic_pi_eq_withDensity (j : Fin n) (hg : AEMeasurable g)
    (hμ : μ = volume.withDensity g) :
    (Measure.pi fun _ : Fin n => μ).map (orderStatistic j) =
      volume.withDensity fun x => ENNReal.ofReal
        (n.factorial / (j.val.factorial * (n - j.val - 1).factorial) *
          cdf μ x ^ j.val * (1 - cdf μ x) ^ (n - j.val - 1)) * g x := by
  have : NullSingletonClass μ := by rw [hμ]; infer_instance
  set F : ℝ → ℝ := ⇑(cdf μ)
  set c : ℝ := n.factorial / (j.val.factorial * (n - j.val - 1).factorial)
  have hFm : Measurable F := (cdf μ).mono.measurable
  have hhm : Measurable fun u : ℝ => c * u ^ j.val * (1 - u) ^ (n - j.val - 1) := by fun_prop
  have ha : (0 : ℝ) < (j : ℝ) + 1 := by positivity
  have hb : (0 : ℝ) < (n : ℝ) - j := by
    have : (j.val : ℝ) < n := by exact_mod_cast j.isLt
    linarith
  have hbeta : betaMeasure ((j : ℝ) + 1) ((n : ℝ) - j) =
      (volume.restrict (Icc (0 : ℝ) 1)).withDensity fun u => ENNReal.ofReal
        (c * u ^ j.val * (1 - u) ^ (n - j.val - 1)) := by
    have hk : (n : ℝ) - j = ((n - j.val - 1 : ℕ) : ℝ) + 1 := by
      rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; push_cast; ring
    have hnm : j.val + (n - j.val - 1) + 1 = n := by omega
    rw [hk, betaMeasure_natCast_add_one_eq_withDensity, hnm]
  have := isProbabilityMeasureBeta ha hb
  -- the right side is `μ` reweighted by the beta density composed with `F`
  have hrhs : (volume.withDensity fun x => ENNReal.ofReal
        (c * F x ^ j.val * (1 - F x) ^ (n - j.val - 1)) * g x) =
      μ.withDensity fun x => ENNReal.ofReal (c * F x ^ j.val * (1 - F x) ^ (n - j.val - 1)) := by
    have hA : Measurable fun x => ENNReal.ofReal (c * F x ^ j.val * (1 - F x) ^ (n - j.val - 1)) :=
      (hhm.comp hFm).ennreal_ofReal
    rw [hμ, ← withDensity_mul₀ hg hA.aemeasurable]
    congr 1
    funext x
    exact mul_comm _ _
  rw [hrhs]
  refine Measure.ext_of_Iic _ _ fun t => ?_
  rw [← ofReal_cdf, cdf_map_orderStatistic_pi_eq_regularizedIncompleteBeta,
    ← cdf_betaMeasure_eq ha hb, ofReal_cdf, hbeta, ← Measure.cdf_map_eq_volume_restrict μ,
    withDensity_apply _ measurableSet_Iic, setLIntegral_map measurableSet_Iic (by fun_prop) hFm,
    withDensity_apply _ measurableSet_Iic]
  exact setLIntegral_congr (Measure.preimage_cdf_Iic_cdf_ae_eq_Iic μ t)

end TauCeti.Probability
