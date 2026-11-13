/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Measure.NNReal
public import TauCeti.Probability.Renewal.ArrivalMeasure
public import TauCeti.Probability.Renewal.Exponential.Process
public import TauCeti.Probability.PointProcess.Poisson.Construction
import TauCeti.Probability.PointProcess.Poisson.Count
import TauCeti.Probability.PointProcess.Poisson.IntegerValued
import TauCeti.Probability.RandomMeasure.Cumulative

/-!
# Exponential renewal arrivals form a Poisson random measure

The random measure placing one occurrence at each positive-index arrival of independent
exponential waiting times has the homogeneous Poisson random-measure law. This identifies
the entire measure-valued law, not only individual interval counts or the intensity.
It holds on arbitrary measurable sample spaces and retains the existing arrival-measure
representative on exceptional explosive paths. No points are placed at the artificial
initial arrival at zero.

These results connect renewal arrivals to the `Measure.poissonLaw` and
`IsPoissonRandomMeasure` interfaces, including independent counts on disjoint measurable
sets and Laplace functionals. Waiting times take values in `ℝ≥0`; their coercions to `ℝ`
have law `expMeasure r`, and the arrival-measure intensity is `r • nnvolume`.
The count-path counterpart is `identDistrib_renewalCountNat_of_hasLaw_poissonMeasure`;
`identDistrib_measure_iff_Iic` supplies the corresponding cumulative-measure uniqueness.

## References

* G. Last and M. Penrose, *Lectures on the Poisson Process*, Cambridge University Press,
  2018, Chapter 7 (exponential waiting times and homogeneous Poisson processes).
* W. Feller, *An Introduction to Probability Theory and Its Applications*, vol. II,
  second edition (1971), Chapter I, §4.
-/

public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace TauCeti.Probability

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {T : ℕ → Ω → ℝ≥0} {r : ℝ≥0}

private theorem identDistrib_renewalArrivalMeasure_of_expMeasure
    {Ω' : Type*} [MeasurableSpace Ω'] {Q : Measure Ω'} {M : Ω' → Measure ℝ≥0}
    (hT : ∀ n, Measurable (T n)) (hindep : iIndepFun T P)
    (hlaw : ∀ n, HasLaw (fun ω ↦ (T n ω : ℝ)) (expMeasure r) P)
    (hM : IsPoissonRandomMeasure Q M ((r : ℝ≥0∞) • nnvolume)) :
    IdentDistrib (renewalArrivalMeasure T) M P Q := by
  have : IsLocallyFiniteMeasure ((r : ℝ≥0∞) • nnvolume) :=
    nnvolume.isLocallyFiniteMeasure_smul ENNReal.coe_ne_top
  have hzero : ∀ᵐ ω ∂Q, M ω {0} = 0 := by
    have hz := hM.hasLaw (A := {0}) (measurableSet_singleton 0) (by simp)
    have hz' : HasLaw (fun ω ↦ M ω {0}) (Measure.dirac 0) Q := by simpa using hz
    exact hz'.ae_eq_of_dirac
  have hfinite : ∀ᵐ ω ∂Q, ∀ t, M ω (Iic t) ≠ ∞ :=
    hM.ae_isLocallyFiniteMeasure.mono fun _ _ _ ↦ measure_Iic_lt_top.ne
  -- Recover every cumulative mass on one event, using integer-valued realizations.
  have hcounts : (fun ω t ↦ (⌊(M ω (Ioc 0 t)).toNNReal⌋₊ : ℝ≥0∞)) =ᵐ[Q]
      (fun ω t ↦ M ω (Iic t)) := by
    filter_upwards [hM.ae_isIntegerValued, hfinite, hzero] with ω hint hfin hz
    funext t
    have hmass : M ω (Ioc 0 t) = M ω (Iic t) := by
      rw [← Icc_sdiff_left, measure_sdiff_null hz, ← bot_eq_zero, Icc_bot]
    obtain ⟨n, hn⟩ := hint.exists_eq_natCast measurableSet_Iic (lt_top_iff_ne_top.2 (hfin t))
    simp [hmass, hn]
  have hrenew : (fun ω t ↦ renewalArrivalMeasure T ω (Iic t)) =ᵐ[P]
      (fun ω t ↦ (renewalCountNat T t ω : ℝ≥0∞)) := by
    filter_upwards [ae_tendsto_arrival_atTop_of_expMeasure hindep hlaw] with ω hω
    funext t
    rw [renewalArrivalMeasure_Iic, natCast_renewalCountNat hω]
  -- The independent-increment comparison identifies the entire natural count path.
  have hpath := identDistrib_renewalCountNat_of_hasLaw_poissonMeasure hT hindep hlaw
    hM.hasIndepIncrements_nat_count hM.measurable_nat_count
    (ae_of_all _ fun ω ↦ by simp) hM.ae_monotone_nat_count
    (fun _ _ hst ↦ hM.hasLaw_nat_count_sub_smul_nnvolume hst)
  have hcast := hpath.comp (u := fun w : ℝ≥0 → ℕ ↦ fun t ↦ (w t : ℝ≥0∞))
    (measurable_pi_iff.2 fun t ↦ Measurable.of_discrete.comp (measurable_pi_apply t))
  apply (identDistrib_measure_iff_Iic (measurable_renewalArrivalMeasure hT).aemeasurable
    hM.measurable.aemeasurable ?_ hfinite).2
  · refine ⟨hcast.aemeasurable_fst.congr hrenew.symm,
      hcast.aemeasurable_snd.congr hcounts, ?_⟩
    rw [Measure.map_congr hrenew, ← Measure.map_congr hcounts]
    exact hcast.map_eq
  · filter_upwards [hrenew] with ω hω
    exact fun t ↦ by rw [congrFun hω t]; exact ENNReal.natCast_ne_top _

/-- The entire arrival measure of independent exponential waiting times has the
homogeneous Poisson sampling law. The artificial arrival at zero is excluded.
Independence forces `P` to be a probability measure; together with the law hypotheses,
this forces the rate to be positive, since `expMeasure 0 = 0`. -/
theorem hasLaw_renewalArrivalMeasure_poissonLaw_of_expMeasure
    (hT : ∀ n, Measurable (T n)) (hindep : iIndepFun T P)
    (hlaw : ∀ n, HasLaw (fun ω ↦ (T n ω : ℝ)) (expMeasure r) P) :
    HasLaw (renewalArrivalMeasure T) (r • nnvolume).poissonLaw P := by
  exact (identDistrib_renewalArrivalMeasure_of_expMeasure hT hindep hlaw
    (by simpa only [Measure.coe_nnreal_smul] using
      isPoissonRandomMeasure_poissonLaw (r • nnvolume))).symm.hasLaw HasLaw.id

/-- Independent exponential waiting times generate a homogeneous Poisson random measure.
In particular, counts on arbitrary disjoint measurable sets are independent, not only counts
on consecutive time intervals. No regularity of the sample space is required. -/
theorem isPoissonRandomMeasure_renewalArrivalMeasure_of_expMeasure
    (hT : ∀ n, Measurable (T n)) (hindep : iIndepFun T P)
    (hlaw : ∀ n, HasLaw (fun ω ↦ (T n ω : ℝ)) (expMeasure r) P) :
    IsPoissonRandomMeasure P (renewalArrivalMeasure T) ((r : ℝ≥0∞) • nnvolume) := by
  rw [Measure.coe_nnreal_smul]
  exact (isPoissonRandomMeasure_poissonLaw (r • nnvolume)).of_identDistrib
    (measurable_renewalArrivalMeasure hT)
    (identDistrib_renewalArrivalMeasure_of_expMeasure hT hindep hlaw
      (by simpa only [Measure.coe_nnreal_smul] using
        isPoissonRandomMeasure_poissonLaw (r • nnvolume))).symm

end TauCeti.Probability
