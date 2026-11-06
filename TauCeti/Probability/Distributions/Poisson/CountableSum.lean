/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Poisson.Sum
public import TauCeti.Probability.Distributions.Poisson.SizeBias
public import Mathlib.Probability.Independence.InfinitePi
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

/-!
# Countable sums of independent Poisson counts

Independent Poisson counts with summable rates have a Poisson total. Almost surely only
finitely many summands are nonzero, so the natural-valued total agrees with the extended
nonnegative sum. The extended formulation is useful for countable superpositions of random
measures: it does not silently assign zero to a divergent series.

The finite-support conclusion requires only the marginal laws, not independence. The law
of the total follows from the finite-sum law and bounded convergence of probability
generating functions. Countable index types, empty families and zero rates are included.

## References

* Günter Last and Mathew Penrose, *Lectures on the Poisson Process*, Cambridge University
  Press, 2018, Chapter 3, on countable superposition of Poisson counts.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal

namespace TauCeti.Probability

variable {ι Ω : Type*} [Countable ι] [MeasurableSpace Ω]
  {P : Measure Ω} {X : ι → Ω → ℕ} {r : ι → ℝ≥0}

/-- With summable Poisson rates, almost surely only finitely many counts are nonzero.
Independence is not needed for this assertion. -/
theorem ae_finite_support_of_hasLaw_poissonMeasure
    (hlaw : ∀ i, HasLaw (X i) (poissonMeasure (r i)) P) (hr : Summable r) :
    ∀ᵐ ω ∂P, (Function.support fun i => X i ω).Finite := by
  have hm (i : ι) : AEMeasurable (fun ω => (X i ω : ℝ≥0∞)) P :=
    (measurable_of_countable _).comp_aemeasurable (hlaw i).aemeasurable
  have hmean : ∫⁻ ω, ∑' i, (X i ω : ℝ≥0∞) ∂P = (∑' i, r i : ℝ≥0) := by
    rw [lintegral_tsum hm]
    simp_rw [(hlaw _).lintegral_comp (measurable_of_countable _).aemeasurable,
      lintegral_natCast_poissonMeasure]
    exact ENNReal.tsum_coe_eq hr.hasSum
  filter_upwards [ae_lt_top' (AEMeasurable.tsum hm) (by rw [hmean]; simp)] with ω hω
  refine (ENNReal.finite_const_le_of_tsum_ne_top hω.ne one_ne_zero).subset ?_
  intro i hi
  exact_mod_cast Nat.one_le_iff_ne_zero.2 hi

end TauCeti.Probability

namespace ProbabilityTheory

variable {ι Ω : Type*} [Countable ι] [MeasurableSpace Ω]
  {P : Measure Ω} {X : ι → Ω → ℕ} {r : ι → ℝ≥0}

/-- A countable independent family of Poisson counts with summable rates has Poisson total.
The natural-number sum is almost surely a finite sum, including for an empty family. -/
theorem iIndepFun.hasLaw_tsum_poissonMeasure (hindep : iIndepFun X P)
    (hlaw : ∀ i, HasLaw (X i) (poissonMeasure (r i)) P) (hr : Summable r) :
    HasLaw (fun ω => ∑' i, X i ω) (poissonMeasure (∑' i, r i)) P := by
  classical
  have := hindep.isProbabilityMeasure
  have hm : AEMeasurable (fun ω => ∑' i, X i ω) P :=
    AEMeasurable.tsum fun i => (hlaw i).aemeasurable
  refine ⟨hm, TauCeti.Probability.measure_eq_of_pgf_eqOn fun z hz => ?_⟩
  rw [TauCeti.Probability.pgf_map hm]
  have habs : |z| ≤ 1 := (abs_lt.2 hz).le
  have hlim : Tendsto (fun s : Finset ι => ∫ ω, z ^ (∑ i ∈ s, X i ω) ∂P)
      (SummationFilter.unconditional ι).filter (nhds (∫ ω, z ^ (∑' i, X i ω) ∂P)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun _ => (1 : ℝ))
      (Eventually.of_forall fun s => ?_) (Eventually.of_forall fun s => ?_)
      (integrable_const 1) ?_
    · exact (measurable_of_countable _).comp_aemeasurable
        (Finset.aemeasurable_fun_sum _ fun i _ => (hlaw i).aemeasurable)
        |>.aestronglyMeasurable
    · exact ae_of_all _ fun ω => by simpa only [Real.norm_eq_abs, abs_pow] using
        (pow_le_one₀ (n := ∑ i ∈ s, X i ω) (abs_nonneg z) habs)
    · filter_upwards [TauCeti.Probability.ae_finite_support_of_hasLaw_poissonMeasure hlaw hr]
        with ω hω
      exact (continuous_of_discreteTopology (f := fun n : ℕ => z ^ n)).continuousAt.tendsto.comp
        (summable_of_hasFiniteSupport hω).hasSum
  have hfinite (s : Finset ι) : (∫ ω, z ^ (∑ i ∈ s, X i ω) ∂P) =
      Real.exp ((∑ i ∈ s, (r i : ℝ)) * (z - 1)) := by
    have h := TauCeti.Probability.HasLaw.pgf_eq
      (hindep.hasLaw_sum_poissonMeasure (s := s) fun i _ => hlaw i) z
    rw [TauCeti.Probability.pgf_poissonMeasure] at h
    simpa only [TauCeti.Probability.pgf_def, NNReal.coe_sum] using h
  simp_rw [hfinite] at hlim
  have hrate : Tendsto (fun s : Finset ι => ∑ i ∈ s, (r i : ℝ))
      (SummationFilter.unconditional ι).filter
      (nhds ((∑' i, r i : ℝ≥0) : ℝ)) := by
    simpa only [Function.comp_def, NNReal.coe_sum] using
      NNReal.continuous_coe.continuousAt.tendsto.comp hr.hasSum
  have htarget := Real.continuous_exp.continuousAt.tendsto.comp
    (hrate.mul_const (z - 1))
  rw [TauCeti.Probability.pgf_poissonMeasure, TauCeti.Probability.pgf_def]
  exact tendsto_nhds_unique hlim htarget

/-- The extended sum of independent Poisson counts has the cast Poisson law. This form
retains the value infinity before the almost-sure finiteness conclusion is used. -/
theorem iIndepFun.hasLaw_tsum_natCast_poissonMeasure (hindep : iIndepFun X P)
    (hlaw : ∀ i, HasLaw (X i) (poissonMeasure (r i)) P) (hr : Summable r) :
    HasLaw (fun ω => ∑' i, (X i ω : ℝ≥0∞))
      ((poissonMeasure (∑' i, r i)).map (Nat.cast : ℕ → ℝ≥0∞)) P := by
  have h := (hasLaw_map (P := poissonMeasure (∑' i, r i))
    (measurable_of_countable (Nat.cast : ℕ → ℝ≥0∞)).aemeasurable).comp
      (hindep.hasLaw_tsum_poissonMeasure hlaw hr)
  apply h.congr
  filter_upwards [TauCeti.Probability.ae_finite_support_of_hasLaw_poissonMeasure hlaw hr]
    with ω hω
  simp only [Function.comp_apply]
  rw [tsum_eq_sum (s := hω.toFinset) (by simp),
    tsum_eq_sum (s := hω.toFinset) (by simp)]
  simp

end ProbabilityTheory

namespace TauCeti.Probability

/-- The total of the canonical countable independent Poisson family has Poisson law,
with the sum taken in the extended nonnegative reals. In particular the total is finite
almost surely, even if infinitely many rates are positive. -/
theorem map_tsum_infinitePi_poissonMeasure {ι : Type*} [Countable ι]
    {r : ι → ℝ≥0} (hr : Summable r) :
    (Measure.infinitePi (fun i => poissonMeasure (r i))).map
      (fun x : ι → ℕ => ∑' i, (x i : ℝ≥0∞)) =
        (poissonMeasure (∑' i, r i)).map (Nat.cast : ℕ → ℝ≥0∞) := by
  have hind : iIndepFun (fun i (x : ι → ℕ) => x i)
      (Measure.infinitePi (fun i => poissonMeasure (r i))) :=
    iIndepFun_infinitePi (X := fun _ => (id : ℕ → ℕ)) fun _ => measurable_id
  exact (hind.hasLaw_tsum_natCast_poissonMeasure
    (fun i => (measurePreserving_eval_infinitePi
      (fun i => poissonMeasure (r i)) i).hasLaw) hr).map_eq

end TauCeti.Probability
