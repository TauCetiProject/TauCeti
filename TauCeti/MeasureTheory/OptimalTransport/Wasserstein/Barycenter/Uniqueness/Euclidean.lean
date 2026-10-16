/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.OptimalTransport.Brenier
public import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Barycenter.Uniqueness.Basic

/-!
# Uniqueness of quadratic Euclidean barycenters

On a finite-dimensional real inner product space, Brenier's theorem
(`TauCeti.IsOptimalCoupling.exists_eq_graphPlan_of_absolutelyContinuous`) shows that every optimal
plan for the cost `edist ^ 2` out of a law absolutely continuous with respect to an additive Haar
measure, such as Lebesgue measure on `ℝⁿ`, into a law at finite `W₂` distance from it, is induced
by a map. Between laws of `P₂(E)` the distance is always finite, so this is the hypothesis of the
general uniqueness result `TauCeti.WassersteinSpace.subsingleton_frechetBarycenters`. It gives the
uniqueness half of Agueh and Carlier's theorem for finitely many input laws, one of them
absolutely continuous with a positive weight, and its population version, for laws `P` giving
positive mass to absolutely continuous measures.

## Main statements

* `TauCeti.WassersteinSpace.subsingleton_frechetBarycenters_two` and
  `TauCeti.WassersteinSpace.subsingleton_frechetBarycenters_two_sum_smul_dirac` — there is at most
  one quadratic Wasserstein barycenter when the law of the input laws gives positive mass to
  absolutely continuous laws, in particular for finitely many input laws one of which is
  absolutely continuous and has a positive weight.

## References

* M. Agueh and G. Carlier, *Barycenters in the Wasserstein space*, SIAM J. Math. Anal. 43
  (2011), 904--924, for uniqueness of finite quadratic barycenters.
* T. Le Gouic and J.-M. Loubes, *Existence and consistency of Wasserstein barycenters*,
  Probab. Theory Related Fields 168 (2017), 901--917, for the population version.
* F. Santambrogio, *Optimal Transport for Applied Mathematicians*, Birkhäuser 2015, Chapter 7,
  for uniqueness of barycenters through strict convexity of `ν ↦ W₂(μ, ν) ^ 2`.
-/

public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {ρ : Measure E} [ρ.IsAddHaarMeasure]

namespace WassersteinSpace

/-- **Uniqueness of quadratic Wasserstein barycenters.** On a finite-dimensional real inner
product space, a law `P` on `P₂(E)` that gives positive mass to the laws absolutely continuous
with respect to an additive Haar measure has at most one quadratic Fréchet barycenter in
`P₂(E)`. -/
theorem subsingleton_frechetBarycenters_two {P : Measure (WassersteinSpace 2 E)}
    (hP : P {m : WassersteinSpace 2 E | ((m : ProbabilityMeasure E) : Measure E) ≪ ρ} ≠ 0) :
    (frechetBarycenters 2 P).Subsingleton := by
  refine subsingleton_frechetBarycenters ENNReal.ofNat_ne_top fun h ↦
    hP (measure_mono_null ?_ h)
  intro m (hm : _ ≪ ρ) ν π hπ
  rw [ENNReal.toReal_ofNat] at hπ
  obtain ⟨T, hT, hπT⟩ := hπ.exists_eq_graphPlan_of_absolutelyContinuous hm
    (wassersteinEDist_ne_top measurable_edist m ν)
  exact ⟨T, hT.aemeasurable, hπT⟩

/-- **Uniqueness of quadratic Wasserstein barycenters of finitely many laws** (Agueh–Carlier). On
a finite-dimensional real inner product space, if one of finitely many laws `μ i` of `P₂(E)` is
absolutely continuous with respect to an additive Haar measure and has a nonzero weight, then the
law `∑ i, w i • δ_{μ i}` has at most one quadratic Fréchet barycenter in `P₂(E)`. -/
theorem subsingleton_frechetBarycenters_two_sum_smul_dirac {ι : Type*} [Fintype ι]
    {w : ι → ℝ≥0} {μ : ι → WassersteinSpace 2 E} {j : ι} (hj : w j ≠ 0)
    (hμj : ((μ j : ProbabilityMeasure E) : Measure E) ≪ ρ) :
    (frechetBarycenters 2 (∑ i, w i • Measure.dirac (μ i))).Subsingleton := by
  set S := {m : WassersteinSpace 2 E | ((m : ProbabilityMeasure E) : Measure E) ≪ ρ}
  refine subsingleton_frechetBarycenters_two (ρ := ρ) (ne_of_gt ?_)
  have hjS : μ j ∈ S := by simpa only [S, Set.mem_ofPred_eq] using hμj
  calc (0 : ℝ≥0∞) < w j := ENNReal.coe_pos.2 (pos_iff_ne_zero.2 hj)
    _ = (w j • Measure.dirac (μ j)) S := by simp [Measure.dirac_apply_of_mem hjS]
    _ ≤ ∑ i, (w i • Measure.dirac (μ i)) S :=
        Finset.single_le_sum (f := fun i ↦ (w i • Measure.dirac (μ i)) S)
          (fun _ _ ↦ bot_le) (Finset.mem_univ j)
    _ = (∑ i, w i • Measure.dirac (μ i)) S := by rw [Measure.coe_finsetSum, Finset.sum_apply]

end WassersteinSpace

end TauCeti
