/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Statistics.Experiments.Density
public import TauCeti.Probability.Distributions.OrderStatistic.Basic
import TauCeti.Probability.Distributions.OrderStatistic.Joint
import TauCeti.Probability.Distributions.Beta.Basic
import TauCeti.MeasureTheory.Measure.PiWithDensity

/-!
# Densities of order statistics

The sorted vector has density `n!` times the product of the sampling densities on the
strictly increasing chamber. An individual order statistic of an atomless law has an explicit
density relative to the sampling law. The density is a polynomial in the sampling cdf, obtained
by transporting the beta law along the quantile. Multiplying by the sampling density gives the
corresponding density relative to the original reference measure.

## References

* G. Casella and R. L. Berger, *Statistical Inference*, 2nd ed., §5.4.
-/

public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace TauCeti

variable {n : ℕ} {P ν : Measure ℝ} {f : ℝ → ℝ}

/-- An atomless i.i.d. sample with real density `f` has sorted density
`n! ∏ i, f (x i)` on the strictly increasing chamber, and zero elsewhere. -/
theorem hasDensity_map_orderStatistics_pi [IsProbabilityMeasure P] [NullSingletonClass P]
    [SigmaFinite ν] (hf : HasDensity P ν f) :
    HasDensity ((Measure.pi fun _ : Fin n ↦ P).map (fun x i ↦ orderStatistic i x))
      (Measure.pi fun _ : Fin n ↦ ν)
      ({x | StrictMono x}.indicator (fun x ↦ (n.factorial : ℝ) * ∏ i, f (x i))) := by
  classical
  let ρ := Measure.pi fun _ : Fin n ↦ ν
  let g : (Fin n → ℝ) → ℝ := fun x ↦ ∏ i, f (x i)
  have hg : Measurable g := Finset.measurable_fun_prod _ fun i _ ↦
    hf.measurable.comp (measurable_pi_apply i)
  have hcoord : ∀ᵐ x ∂ρ, ∀ i, 0 ≤ f (x i) :=
    ae_all_iff.2 fun i ↦ (Measure.quasiMeasurePreserving_eval (fun _ : Fin n ↦ ν) i).ae hf.ae_nonneg
  have hmono : MeasurableSet {x : Fin n → ℝ | StrictMono x} := measurableSet_setOf_strictMono
  have hpi : (Measure.pi fun _ : Fin n ↦ P) = ρ.withDensity (fun x ↦ ENNReal.ofReal (g x)) := by
    have : IsProbabilityMeasure (ν.withDensity fun x ↦ ENNReal.ofReal (f x)) :=
      hf.eq_withDensity ▸ inferInstanceAs (IsProbabilityMeasure P)
    rw [hf.eq_withDensity, pi_withDensity _ (fun _ ↦ hf.measurable.ennreal_ofReal)]
    apply withDensity_congr_ae
    filter_upwards [hcoord] with x hx
    exact (ENNReal.ofReal_prod_of_nonneg fun i _ ↦ hx i).symm
  refine ⟨(measurable_const.mul hg).indicator hmono, ?_, ?_⟩
  · filter_upwards [hcoord] with x hx
    exact indicator_nonneg (fun _ _ ↦ mul_nonneg (Nat.cast_nonneg _) (Finset.prod_nonneg
      fun i _ ↦ hx i)) x
  rw [Probability.map_orderStatistics_pi, hpi, restrict_withDensity hmono,
    ← withDensity_indicator hmono, ← Nat.cast_smul_eq_nsmul ℝ≥0∞,
    ← withDensity_smul _ (hg.ennreal_ofReal.indicator hmono)]
  congr 1
  funext x
  by_cases hx : StrictMono x <;>
    simp [Set.indicator, hx, Pi.smul_apply, smul_eq_mul, ENNReal.ofReal_mul, g]

private theorem orderStatistic_weight_nonneg (k : Fin n) {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) :
    0 ≤ (n.factorial : ℝ) / ((k : ℕ).factorial * (n - k - 1).factorial) *
      u ^ (k : ℕ) * (1 - u) ^ (n - k - 1) :=
  mul_nonneg (mul_nonneg (by positivity) (pow_nonneg hu.1 _)) (pow_nonneg (sub_nonneg.2 hu.2) _)

/-- At an interior probability level the beta density for the `k`-th order statistic
is a polynomial with a factorial coefficient. -/
private theorem betaPDF_orderStatistic_eq (k : Fin n) {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) :
    betaPDF ((k : ℕ) + 1) (n - (k : ℕ)) u =
      ENNReal.ofReal ((n.factorial : ℝ) / ((k : ℕ).factorial * (n - k - 1).factorial) *
        u ^ (k : ℕ) * (1 - u) ^ (n - k - 1)) := by
  have hk : (k : ℕ) < n := k.isLt
  have hcast : (n : ℝ) - (k : ℕ) = ((n - k - 1 : ℕ) : ℝ) + 1 := calc
    _ = ((n - (k : ℕ) : ℕ) : ℝ) := (Nat.cast_sub hk.le).symm
    _ = _ := by
      rw [← Nat.cast_succ]
      congr 1
      omega
  have hsum : ((k : ℝ) + 1) + ((n : ℝ) - k) = (n : ℝ) + 1 := by ring
  rw [betaPDF_of_pos_lt_one hu.1 hu.2]
  have hβ : beta ((k : ℕ) + 1) (n - (k : ℕ)) =
      ((k : ℕ).factorial : ℝ) * (n - k - 1).factorial / n.factorial := by
    rw [beta, hsum, hcast, Real.Gamma_nat_eq_factorial, Real.Gamma_nat_eq_factorial,
      Real.Gamma_nat_eq_factorial]
  rw [hβ, one_div_div, add_sub_cancel_right, hcast, add_sub_cancel_right,
    Real.rpow_natCast, Real.rpow_natCast]

/-- For an atomless real sampling law, the `k`-th order statistic has density
`n! / (k! (n-k-1)!) * F^k * (1-F)^(n-k-1)` relative to the sampling law with cdf `F`.
Here `k` is zero based. -/
theorem hasDensity_map_orderStatistic_pi_self [IsProbabilityMeasure P] [NullSingletonClass P]
    (k : Fin n) :
    HasDensity ((Measure.pi fun _ : Fin n ↦ P).map (orderStatistic k)) P
      (fun x ↦ (n.factorial : ℝ) / ((k : ℕ).factorial * (n - k - 1).factorial) *
        cdf P x ^ (k : ℕ) * (1 - cdf P x) ^ (n - k - 1)) := by
  let w : ℝ → ℝ := fun u ↦ (n.factorial : ℝ) / ((k : ℕ).factorial * (n - k - 1).factorial) *
    u ^ (k : ℕ) * (1 - u) ^ (n - k - 1)
  have hF : Measurable (cdf P) := (cdf P).mono.measurable
  have hw : Measurable w := by fun_prop
  refine ⟨hw.comp hF, Filter.Eventually.of_forall (fun x ↦ ?_), ?_⟩
  · exact orderStatistic_weight_nonneg k ⟨cdf_nonneg P x, cdf_le_one P x⟩
  rw [Probability.map_orderStatistic_pi_eq_map_betaMeasure_quantile]
  let U := volume.restrict (Ioo (0 : ℝ) 1)
  have hU : U.map P.quantile = P := P.map_quantile_volume_Ioo
  have hweight : betaMeasure ((k : ℕ) + 1) (n - (k : ℕ)) =
      U.withDensity (fun u ↦ ENNReal.ofReal (w (cdf P (P.quantile u)))) := by
    rw [Probability.betaMeasure_eq_withDensity_restrict_Ioo]
    apply withDensity_congr_ae
    filter_upwards [ae_restrict_mem (μ := volume) (measurableSet_Ioo (a := (0 : ℝ)) (b := 1))]
      with u hu
    rw [P.cdf_quantile_of_noAtoms hu.1 hu.2]
    exact betaPDF_orderStatistic_eq k hu
  rw [hweight]
  calc
    _ = (U.map P.quantile).withDensity (fun x ↦ ENNReal.ofReal (w (cdf P x))) :=
      Measure.map_withDensity_comp P.measurable_quantile (hw.comp hF).ennreal_ofReal
    _ = _ := congrArg (fun μ ↦ μ.withDensity (fun x ↦ ENNReal.ofReal (w (cdf P x)))) hU

/-- The marginal density of the `k`-th order statistic from a law with density `f` is
the beta weight in the sampling cdf times `f`, relative to the original reference measure. -/
theorem hasDensity_map_orderStatistic_pi [IsProbabilityMeasure P] [NullSingletonClass P]
    (hf : HasDensity P ν f) (k : Fin n) :
    HasDensity ((Measure.pi fun _ : Fin n ↦ P).map (orderStatistic k)) ν
      (fun x ↦ (n.factorial : ℝ) / ((k : ℕ).factorial * (n - k - 1).factorial) *
        cdf P x ^ (k : ℕ) * (1 - cdf P x) ^ (n - k - 1) * f x) := by
  let w : ℝ → ℝ := fun x ↦ (n.factorial : ℝ) / ((k : ℕ).factorial * (n - k - 1).factorial) *
    cdf P x ^ (k : ℕ) * (1 - cdf P x) ^ (n - k - 1)
  have hw := hasDensity_map_orderStatistic_pi_self (P := P) k
  have hw_meas : Measurable w := hw.measurable
  have hw_nonneg (x : ℝ) : 0 ≤ w x :=
    orderStatistic_weight_nonneg k ⟨cdf_nonneg P x, cdf_le_one P x⟩
  refine ⟨hw_meas.mul hf.measurable, hf.ae_nonneg.mono (fun x hx ↦ mul_nonneg (hw_nonneg x) hx), ?_⟩
  calc
    _ = P.withDensity (fun x ↦ ENNReal.ofReal (w x)) := hw.eq_withDensity
    _ = (ν.withDensity (fun x ↦ ENNReal.ofReal (f x))).withDensity
        (fun x ↦ ENNReal.ofReal (w x)) :=
      congrArg (fun μ ↦ μ.withDensity (fun x ↦ ENNReal.ofReal (w x))) hf.eq_withDensity
    _ = _ := by
      rw [← withDensity_mul _ hf.measurable.ennreal_ofReal hw_meas.ennreal_ofReal]
      congr 1
      funext x
      rw [Pi.mul_apply, ENNReal.ofReal_mul (hw_nonneg x), mul_comm]

end TauCeti
