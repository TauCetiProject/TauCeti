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
import TauCeti.Probability.PointProcess.Poisson.Law
import TauCeti.Probability.PointProcess.Poisson.Temporal

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
The count-path counterpart is `identDistrib_renewalCountNat_of_hasLaw_poissonMeasure`.

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

/-- Independent exponential waiting times generate a homogeneous Poisson random measure.
In particular, counts on arbitrary disjoint measurable sets are independent, not only counts
on consecutive time intervals. No regularity of the sample space is required. -/
theorem isPoissonRandomMeasure_renewalArrivalMeasure_of_expMeasure
    (hT : ∀ n, Measurable (T n)) (hindep : iIndepFun T P)
    (hlaw : ∀ n, HasLaw (fun ω ↦ (T n ω : ℝ)) (expMeasure r) P) :
    IsPoissonRandomMeasure P (renewalArrivalMeasure T) ((r : ℝ≥0∞) • nnvolume) := by
  have hrenew : ∀ᵐ ω ∂P, ∀ t,
      renewalArrivalMeasure T ω (Iic t) = (renewalCountNat T t ω : ℝ≥0∞) := by
    filter_upwards [ae_tendsto_arrival_atTop_of_expMeasure hindep hlaw] with ω hω t
    rw [renewalArrivalMeasure_Iic, natCast_renewalCountNat hω]
  apply (isPoissonRandomMeasure_smul_nnvolume_iff_count_increments
    (measurable_renewalArrivalMeasure hT) hrenew).2
  refine ⟨?_, hasIndepIncrements_renewalCountNat_of_expMeasure hT hindep hlaw, ?_⟩
  · have h := hasLaw_renewalCountNat_poissonMeasure hindep hlaw 0
    simp only [mul_zero, poissonMeasure_zero] at h
    exact h.ae_eq_of_dirac
  · intro s t hst
    simpa only [add_tsub_cancel_of_le hst] using
      hasLaw_renewalCountNat_sub_poissonMeasure hT hindep hlaw s (t - s)

/-- The entire arrival measure of independent exponential waiting times has the
homogeneous Poisson sampling law. The artificial arrival at zero is excluded.
Independence forces `P` to be a probability measure; together with the law hypotheses,
this forces the rate to be positive, since `expMeasure 0 = 0`. -/
theorem hasLaw_renewalArrivalMeasure_poissonLaw_of_expMeasure
    (hT : ∀ n, Measurable (T n)) (hindep : iIndepFun T P)
    (hlaw : ∀ n, HasLaw (fun ω ↦ (T n ω : ℝ)) (expMeasure r) P) :
    HasLaw (renewalArrivalMeasure T) (r • nnvolume).poissonLaw P := by
  exact ((Measure.isPoissonRandomMeasure_poissonLaw (r • nnvolume)).identDistrib
    (by simpa only [Measure.coe_nnreal_smul] using
      isPoissonRandomMeasure_renewalArrivalMeasure_of_expMeasure hT hindep hlaw)).hasLaw HasLaw.id

end TauCeti.Probability
