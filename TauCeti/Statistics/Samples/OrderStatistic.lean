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

/-!
# Densities of order statistics

The sorted vector has density `n!` times the product of the sampling densities on the
strictly increasing chamber. An individual order statistic of an atomless real law has an explicit
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

variable {n : ℕ}

/-- An atomless i.i.d. sample with real density `f` has sorted density
`n! ∏ i, f (x i)` on the strictly increasing chamber, and zero elsewhere. -/
theorem hasDensity_map_orderStatistics_pi {α : Type*} [LinearOrder α] [TopologicalSpace α]
    [OrderClosedTopology α] [SecondCountableTopology α] [MeasurableSpace α] [BorelSpace α]
    {P ν : Measure α} {f : α → ℝ} [IsProbabilityMeasure P] [NullSingletonClass P]
    [SigmaFinite ν] (hf : HasDensity P ν f) :
    HasDensity ((Measure.pi fun _ : Fin n ↦ P).map (fun x i ↦ orderStatistic i x))
      (Measure.pi fun _ : Fin n ↦ ν)
      ({x | StrictMono x}.indicator (fun x ↦ (n.factorial : ℝ) * ∏ i, f (x i))) := by
  classical
  have hprod := HasDensity.pi fun _ : Fin n ↦ hf
  have hmono : MeasurableSet {x : Fin n → α | StrictMono x} := measurableSet_setOf_strictMono
  refine ⟨(measurable_const.mul hprod.measurable).indicator hmono, ?_, ?_⟩
  · filter_upwards [hprod.ae_nonneg] with x hx
    exact indicator_nonneg (fun _ _ ↦ mul_nonneg (Nat.cast_nonneg _) hx) x
  rw [Probability.map_orderStatistics_pi, hprod.eq_withDensity, restrict_withDensity hmono,
    ← withDensity_indicator hmono, ← Nat.cast_smul_eq_nsmul ℝ≥0∞,
    ← withDensity_smul _ (hprod.measurable.ennreal_ofReal.indicator hmono)]
  congr 1
  funext x
  by_cases hx : StrictMono x <;>
    simp [Set.indicator, hx, Pi.smul_apply, smul_eq_mul, ENNReal.ofReal_mul]

variable {P ν : Measure ℝ} {f : ℝ → ℝ}

private theorem orderStatistic_weight_nonneg (k : Fin n) {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) :
    0 ≤ (n.factorial : ℝ) / ((k : ℕ).factorial * (n - k - 1).factorial) *
      u ^ (k : ℕ) * (1 - u) ^ (n - k - 1) :=
  mul_nonneg (mul_nonneg (by positivity) (pow_nonneg hu.1 _)) (pow_nonneg (sub_nonneg.2 hu.2) _)

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
    have hk := k.isLt
    have hshape : (n : ℝ) - (k : ℕ) = ((n - k - 1 : ℕ) : ℝ) + 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ n - (k : ℕ)), Nat.cast_sub hk.le, Nat.cast_one]
      ring
    have hsize : (k : ℕ) + (n - k - 1) + 1 = n := by omega
    filter_upwards [ae_restrict_mem (μ := volume) (measurableSet_Ioo (a := (0 : ℝ)) (b := 1))]
      with u hu
    rw [P.cdf_quantile_of_noAtoms hu.1 hu.2, hshape, Probability.betaPDF_nat_add_one_eq hu,
      hsize]
  rw [hweight]
  calc
    _ = (U.map P.quantile).withDensity (fun x ↦ ENNReal.ofReal (w (cdf P x))) :=
      Measure.map_withDensity_comp P.measurable_quantile.aemeasurable
        (hw.comp hF).ennreal_ofReal.aemeasurable
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
