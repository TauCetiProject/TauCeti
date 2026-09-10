/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
public import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Space
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

/-!
# Wasserstein convergence implies weak convergence

Convergence in any `p`-Wasserstein distance with `1 ≤ p` is stronger than weak convergence of
probability measures. This file proves that implication through the Lévy--Prokhorov metric.

The quantitative input is the classical coupling estimate: if a coupling has expected displacement
less than `ε²`, then its marginals are at Lévy--Prokhorov distance at most `ε`. Markov's
inequality bounds the mass of pairs whose displacement exceeds the thickening radius. Monotonicity
of `eLpNorm` then lets the same estimate consume a `p`-Wasserstein bound for every `1 ≤ p`,
including `p = ∞`.

On a separable Borel pseudometric space, the Lévy--Prokhorov metric induces the weak topology.
Consequently, the inclusions of both finite-moment Wasserstein spaces and arbitrary anchored
finite-distance components into `ProbabilityMeasure` are continuous.

## Main statements

* `TauCeti.levyProkhorovEDist_le_of_wassersteinEDist_lt_mul_self` — a quantitative comparison
  between the two extended distances;
* `TauCeti.WassersteinSpace.continuous_toProbabilityMeasure` — Wasserstein convergence of
  finite-moment laws implies weak convergence;
* `TauCeti.WassersteinComponent.continuous_toProbabilityMeasure` — the same implication on an
  arbitrary finite-distance component.

## References

* C. Villani, *Optimal Transport: Old and New*, Grundlehren 338, Springer 2009, Chapter 6.
* P. Billingsley, *Convergence of Probability Measures*, Wiley, 1999, Chapter 1.
-/

public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace TauCeti

universe u

section Comparison

variable {X : Type u} [PseudoEMetricSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
  {p ε : ℝ≥0∞} {μ ν : Measure X} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

/-- If the `p`-Wasserstein distance is strictly below `ε²`, then the Lévy--Prokhorov
extended distance is at most `ε`, for `1 ≤ p`.

The square is not asserted to be an optimal modulus. It is the direct consequence of Markov's
inequality needed to compare the Wasserstein and weak topologies. -/
theorem levyProkhorovEDist_le_of_wassersteinEDist_lt_mul_self
    (hd : Measurable fun z : X × X ↦ edist z.1 z.2) (hp : 1 ≤ p)
    (h : wassersteinEDist p μ ν < ε * ε) :
    levyProkhorovEDist μ ν ≤ ε := by
  obtain ⟨π, hπ, hπε⟩ := wassersteinEDist_lt_iff.mp h
  let : IsProbabilityMeasure π := hπ.isProbabilityMeasure
  have hint : ∫⁻ z, edist z.1 z.2 ∂π < ε * ε := by
    calc
      ∫⁻ z, edist z.1 z.2 ∂π
          = eLpNorm (fun z : X × X ↦ edist z.1 z.2) 1 π := by
              rw [eLpNorm_one_eq_lintegral_enorm]
              simp
      _ ≤ eLpNorm (fun z : X × X ↦ edist z.1 z.2) p π :=
        eLpNorm_le_eLpNorm_of_exponent_le hp hd.aestronglyMeasurable
      _ < ε * ε := hπε
  refine levyProkhorovEDist_le_of_forall_le μ ν ε fun δ B hεδ hδtop hB ↦ ?_
  have hδ0 : δ ≠ 0 := (pos_of_gt (lt_of_le_of_lt (bot_le : 0 ≤ ε) hεδ)).ne'
  have hδtop' : δ ≠ ∞ := hδtop.ne
  have hεδsq : ε * ε < δ * δ := ENNReal.mul_lt_mul hεδ hεδ
  have hbad : π {z : X × X | δ ≤ edist z.1 z.2} ≤ δ := by
    refine (meas_ge_le_lintegral_div hd.aemeasurable hδ0 hδtop').trans ?_
    exact (ENNReal.div_lt_iff (Or.inl hδ0) (Or.inl hδtop')).2
      (hint.trans hεδsq) |>.le
  have hsubset : B ×ˢ univ ⊆
      univ ×ˢ Metric.thickening δ.toReal B ∪ {z : X × X | δ ≤ edist z.1 z.2} := by
    intro z hz
    by_cases hzt : z.2 ∈ Metric.thickening δ.toReal B
    · exact Or.inl ⟨Set.mem_univ _, hzt⟩
    · refine Or.inr ?_
      simp only [mem_ofPred_eq]
      apply le_of_not_gt
      intro hdist
      apply hzt
      rw [Metric.mem_thickening_iff_exists_edist_lt]
      refine ⟨z.1, hz.1, ?_⟩
      rwa [edist_comm, ENNReal.ofReal_toReal hδtop']
  calc
    μ B = π (B ×ˢ univ) := (hπ.measure_prod_univ hB).symm
    _ ≤ π (univ ×ˢ Metric.thickening δ.toReal B ∪
        {z : X × X | δ ≤ edist z.1 z.2}) := measure_mono hsubset
    _ ≤ π (univ ×ˢ Metric.thickening δ.toReal B) +
        π {z : X × X | δ ≤ edist z.1 z.2} := measure_union_le _ _
    _ = ν (Metric.thickening δ.toReal B) +
        π {z : X × X | δ ≤ edist z.1 z.2} := by
          rw [hπ.measure_univ_prod Metric.isOpen_thickening.measurableSet]
    _ ≤ ν (Metric.thickening δ.toReal B) + δ := add_le_add_right hbad _

end Comparison

section Continuous

variable {X : Type u} {p : ℝ≥0∞} [PseudoMetricSpace X] [MeasurableSpace X]
  [BorelSpace X] [SecondCountableTopology X]
  [StandardBorelSpace X] [Fact (1 ≤ p)]

omit [StandardBorelSpace X] in
private theorem continuous_toProbabilityMeasure_of_edist_eq
    {Y : Type*} [PseudoMetricSpace Y] (toProbabilityMeasure : Y → ProbabilityMeasure X)
    (hedist : ∀ μ ν, edist μ ν = wassersteinEDist p
      (toProbabilityMeasure μ : Measure X) (toProbabilityMeasure ν : Measure X)) :
    Continuous toProbabilityMeasure := by
  let f : Y → LevyProkhorov (ProbabilityMeasure X) :=
    fun μ ↦ LevyProkhorov.ofMeasure (toProbabilityMeasure μ)
  have hf : Continuous f := Metric.continuous_iff.mpr fun μ ε hε ↦ by
    refine ⟨(ε / 2) ^ 2, sq_pos_of_pos (half_pos hε), fun ν hν ↦ ?_⟩
    have hW : wassersteinEDist p (toProbabilityMeasure ν : Measure X)
        (toProbabilityMeasure μ : Measure X) <
        ENNReal.ofReal (ε / 2) * ENNReal.ofReal (ε / 2) := by
      rw [← ENNReal.ofReal_mul (half_pos hε).le]
      rw [← hedist ν μ, edist_dist,
        ENNReal.ofReal_lt_ofReal_iff (mul_pos (half_pos hε) (half_pos hε))]
      simpa only [pow_two] using hν
    have hLP := levyProkhorovEDist_le_of_wassersteinEDist_lt_mul_self
      measurable_edist Fact.out hW
    rw [LevyProkhorov.dist_probabilityMeasure_def, levyProkhorovDist]
    exact (ENNReal.toReal_mono (by finiteness) hLP).trans_lt <| by
      simpa only [ENNReal.toReal_ofReal (half_pos hε).le] using half_lt_self hε
  exact LevyProkhorov.continuous_toMeasure_probabilityMeasure.comp hf

namespace WassersteinSpace

/-- The inclusion of the finite-moment `p`-Wasserstein space into probability measures is
continuous when the codomain carries its weak topology. -/
theorem continuous_toProbabilityMeasure :
    Continuous (toProbabilityMeasure : WassersteinSpace p X → ProbabilityMeasure X) :=
  continuous_toProbabilityMeasure_of_edist_eq toProbabilityMeasure edist_def

end WassersteinSpace

namespace WassersteinComponent

variable {μ₀ : ProbabilityMeasure X}

/-- The inclusion of an anchored finite-distance `p`-Wasserstein component into probability
measures is continuous when the codomain carries its weak topology. -/
theorem continuous_toProbabilityMeasure :
    Continuous (toProbabilityMeasure : WassersteinComponent p μ₀ → ProbabilityMeasure X) :=
  continuous_toProbabilityMeasure_of_edist_eq toProbabilityMeasure edist_def

end WassersteinComponent

end Continuous

end TauCeti
