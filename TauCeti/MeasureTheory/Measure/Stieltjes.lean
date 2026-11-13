/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Stieltjes
public import Mathlib.MeasureTheory.Measure.Real
public import TauCeti.MeasureTheory.Measure.Interval
public import TauCeti.MeasureTheory.Measure.Measurability
import TauCeti.MeasureTheory.Integral.Bochner.Cumulative

/-!
# Stieltjes measures, cumulative functions and measurable families

A measure on the real line need not be finite to have a real-valued cumulative function:
it suffices that every interval `(-∞, t]` has finite mass. This file bundles that cumulative
function as a `StieltjesFunction` and proves that its Stieltjes measure is the original measure.
In particular this applies to locally finite measures supported on the nonnegative half-line,
without normalizing them to probability measures.

On the nonnegative half-line, the cumulative mass of a Stieltjes measure is the increment
of its Stieltjes function from zero. For continuous Stieltjes functions, pathwise locally
integrable functions have continuous accumulated integrals.

For a family of Stieltjes functions, measurability of evaluations implies measurability of the
associated measures, without normalization or a uniform bound on their masses. On a bounded
interval only evaluations within that interval need be measurable; this is useful for random
Stieltjes measures adapted to a filtration. These results extend the probability-CDF
measurability criterion of Rémy Degenne in
`Mathlib.Probability.Kernel.Disintegration.MeasurableStieltjes` by restricting to finite intervals.
-/

public section

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace StieltjesFunction

/-- The cumulative mass of a Stieltjes measure on the half-line is its increment from zero. -/
@[simp]
theorem measure_Iic_nnreal (f : StieltjesFunction ℝ≥0) (t : ℝ≥0) :
    f.measure (Iic t) = ENNReal.ofReal (f t - f 0) := by
  apply f.measure_Iic
  rw [atBot_eq_pure_of_isBot (isBot_bot : IsBot (0 : ℝ≥0))]
  exact tendsto_pure_nhds _ _

end StieltjesFunction

namespace MeasureTheory.Measure

variable (μ : Measure ℝ) (hμ : ∀ t, μ (Iic t) ≠ ∞)

/-- The cumulative function of a measure with finite left tails, bundled as a Stieltjes
function. Unlike a probability cdf, it need not be bounded above. -/
def cumulativeStieltjes : StieltjesFunction ℝ where
  toFun t := μ.real (Iic t)
  mono' _ _ hab := measureReal_mono (Iic_subset_Iic.mpr hab) (hμ _)
  right_continuous' t := by
    have hlim := tendsto_measure_Iic_nhdsGT (μ := μ) ⟨t + 1, lt_add_one t, hμ _⟩
    rw [← continuousWithinAt_Ioi_iff_Ici]
    exact (ENNReal.tendsto_toReal (hμ t)).comp hlim

@[simp]
theorem cumulativeStieltjes_apply (t : ℝ) : μ.cumulativeStieltjes hμ t = μ.real (Iic t) :=
  (rfl)

/-- Recover a measure with finite left tails from its cumulative Stieltjes function. -/
@[simp]
theorem measure_cumulativeStieltjes : (μ.cumulativeStieltjes hμ).measure = μ := by
  refine (μ.cumulativeStieltjes hμ).measure.ext_of_Ioc' μ
    (fun _ _ _ ↦ by simp) ?_
  intro a b hab
  have hdiff : μ.real (Ioc a b) = μ.real (Iic b) - μ.real (Iic a) := by
    rw [← Iic_sdiff_Iic,
      measureReal_sdiff (Iic_subset_Iic.mpr hab.le) measurableSet_Iic (hμ b)]
  rw [StieltjesFunction.measure_Ioc, cumulativeStieltjes_apply, cumulativeStieltjes_apply,
    ← hdiff, ofReal_measureReal (measure_ne_top_of_subset Ioc_subset_Iic_self (hμ b))]

end MeasureTheory.Measure

namespace StieltjesFunction

variable {Ω R : Type*} {mΩ : MeasurableSpace Ω}
  [LinearOrder R] [TopologicalSpace R] [OrderTopology R] [CompactIccSpace R]
  [MeasurableSpace R] [BorelSpace R] [SecondCountableTopology R] [DenselyOrdered R]

/-- The Stieltjes measure of a continuous Stieltjes function vanishes on singletons. -/
theorem nullSingletonClass_measure_of_continuous (f : StieltjesFunction R)
    (hf : Continuous f) : NullSingletonClass f.measure :=
  ⟨fun t ↦ by
    rw [f.measure_singleton, hf.continuousAt.continuousWithinAt.leftLim_eq, sub_self,
      ENNReal.ofReal_zero]⟩

/-- Integration of a locally integrable Banach-valued function against a Stieltjes function
continuous on `(a,∞)` has a continuous accumulated integral. Jumps at or before `a` are allowed;
no bound on the total mass or integrability beyond each finite horizon is required. -/
theorem continuous_setIntegral_Ioc {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : StieltjesFunction R) (a : R) (hf : ContinuousOn f (Ioi a)) {H : R → E}
    (hH : ∀ T, IntegrableOn H (Ioc a T) f.measure) :
    Continuous (fun t ↦ ∫ u in Ioc a t, H u ∂f.measure) := by
  have : NullSingletonClass (f.measure.restrict (Ioi a)) := ⟨fun t ↦ by
    rw [Measure.restrict_apply (measurableSet_singleton t)]
    by_cases ht : t ∈ Ioi a
    · rw [singleton_inter_of_mem ht, f.measure_singleton,
        (isOpen_Ioi.continuousOn_iff.mp hf ht).continuousWithinAt.leftLim_eq,
        sub_self, ENNReal.ofReal_zero]
    · rw [singleton_inter_of_notMem ht, measure_empty]⟩
  have hi : ∀ T, IntegrableOn H (Ioc a T) (f.measure.restrict (Ioi a)) := by
    intro T
    simpa only [IntegrableOn, Measure.restrict_restrict_of_subset Ioc_subset_Ioi_self] using hH T
  simpa only [Measure.restrict_restrict_of_subset Ioc_subset_Ioi_self] using
    MeasureTheory.continuous_integral_Ioc hi

/-- The Stieltjes measure restricted to `(a,b]` is a measurable family if evaluations inside
`[a,b]` are measurable. No uniform bound on the random interval mass is required. -/
theorem measurable_restrict_measure_Ioc {f : Ω → StieltjesFunction R} {a b : R}
    (hf : ∀ t ∈ Icc a b, Measurable fun ω ↦ f ω t) :
    Measurable fun ω ↦ (f ω).measure.restrict (Ioc a b) := by
  by_cases hab : a ≤ b
  · let μ : Ω → Measure R := fun ω ↦ (f ω).measure.restrict (Ioc a b)
    have : ∀ ω, IsFiniteMeasure (μ ω) := fun ω ↦ by
      constructor
      simp [μ, measure_Ioc]
    refine Measurable.measure_of_isPiSystem
      (BorelSpace.measurable_eq.trans (borel_eq_generateFrom_Iic R)) isPiSystem_Iic ?_ ?_
    · rintro _ ⟨c, rfl⟩
      simp only [Measure.restrict_apply measurableSet_Iic, inter_comm (Iic c),
        Ioc_inter_Iic]
      by_cases hac : a ≤ min b c
      · simp only [measure_Ioc]
        simpa only [Pi.sub_apply] using
          ((hf _ ⟨hac, min_le_left _ _⟩).sub (hf a ⟨le_rfl, hab⟩)).ennreal_ofReal
      · simp only [Ioc_eq_empty (not_lt.mpr (le_of_not_ge hac)), measure_empty]
        exact measurable_const
    · simpa only [μ, Measure.restrict_apply_univ, measure_Ioc, Pi.sub_apply] using
        ((hf b ⟨hab, le_rfl⟩).sub (hf a ⟨le_rfl, hab⟩)).ennreal_ofReal
  · simp only [Ioc_eq_empty (not_lt.mpr (le_of_not_ge hab)), Measure.restrict_empty]
    exact measurable_const

/-- Measurable evaluations give a measurable family of locally finite Stieltjes measures.
Unlike the probability-CDF criterion, this requires neither limits at infinity nor finite
total mass. -/
theorem measurable_measure_of_measurable_eval {f : Ω → StieltjesFunction ℝ}
    (hf : ∀ t, Measurable fun ω ↦ f ω t) : Measurable fun ω ↦ (f ω).measure := by
  refine Measurable.measure_of_isPiSystem_of_iUnion
    (B := fun n : ℕ ↦ Ioc (-(n + 1 : ℝ)) (n + 1))
    (BorelSpace.measurable_eq.trans (borel_eq_generateFrom_Ioc ℝ))
    (isPiSystem_Ioc id id) ?_ ?_ ?_ ?_
  · intro n
    exact ⟨_, _, by have := Nat.cast_nonneg (α := ℝ) n; linarith, rfl⟩
  · ext x
    simp only [mem_iUnion, mem_Ioc, mem_univ, iff_true]
    obtain ⟨n, hn⟩ := exists_nat_gt |x|
    exact ⟨n, by have := neg_abs_le x; linarith, by have := le_abs_self x; linarith⟩
  · intro ω n
    simp only [measure_Ioc, ENNReal.ofReal_ne_top, ne_eq, not_false_eq_true]
  · rintro _ ⟨a, b, _, rfl⟩
    simpa only [measure_Ioc, Pi.sub_apply] using ((hf b).sub (hf a)).ennreal_ofReal

end StieltjesFunction
