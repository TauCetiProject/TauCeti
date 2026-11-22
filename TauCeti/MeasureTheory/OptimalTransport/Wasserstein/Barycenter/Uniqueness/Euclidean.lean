/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.OptimalTransport.Brenier.Basic
public import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Barycenter.Uniqueness.Basic
import TauCeti.MeasureTheory.Measure.Dirac

/-!
# Uniqueness of quadratic Euclidean barycenters

On a finite-dimensional real inner product space `E`, Brenier's theorem for `c - c`-regular sources
(`TauCeti.IsOptimalCoupling.exists_eq_graphPlan_of_isCCRegular`) shows that every optimal plan for
the cost `edist ^ 2` out of a `c - c`-regular law, into a law at finite `W₂` distance from it, is
induced by a measurable map. Between laws of `P₂(E)` the distance is always finite, so this
discharges the hypothesis of the general uniqueness theorem
`TauCeti.WassersteinSpace.subsingleton_frechetBarycenters`.

Consequently, a law `P` on `P₂(E)` has at most one quadratic Fréchet barycenter whenever it gives
positive mass to `c - c`-regular laws. Via `TauCeti.Analysis.Convex.CCHypersurface.Regular`, this
covers laws vanishing on Lipschitz graphs over hyperplanes, laws vanishing on Borel sets with
`dimH A + 1 ≤ finrank ℝ E` or small sets (`dimH A ≤ finrank ℝ E - 1`, Agueh–Carlier
Proposition 3.5), and laws absolutely continuous with respect to an additive Haar measure.
Specializing `P` to `∑ i, w i • δ_{μ i}` gives the finite barycenter uniqueness theorem of Agueh
and Carlier.

## Main statements

* `TauCeti.WassersteinSpace.subsingleton_frechetBarycenters_two` — population uniqueness of
  quadratic Wasserstein barycenters when `P` gives positive mass to `c - c`-regular laws;
* `TauCeti.WassersteinSpace.subsingleton_frechetBarycenters_two_sum_smul_dirac` — finite barycenter
  uniqueness when one positively weighted input law is `c - c`-regular.

## References

* M. Agueh and G. Carlier, *Barycenters in the Wasserstein space*, SIAM J. Math. Anal. 43
  (2011), 904--924, Proposition 3.5, for uniqueness of finite quadratic barycenters.
* T. Le Gouic and J.-M. Loubes, *Existence and consistency of Wasserstein barycenters*,
  Probab. Theory Related Fields 168 (2017), 901--917, for the population version.
* F. Santambrogio, *Optimal Transport for Applied Mathematicians*, Birkhäuser 2015, Chapter 7,
  for uniqueness of barycenters through strict convexity of `ν ↦ W₂(μ, ν) ^ 2`.
-/

public section

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

namespace WassersteinSpace

/-- **Uniqueness of quadratic Wasserstein barycenters.** On a finite-dimensional real inner
product space, a law `P` on `P₂(E)` that gives positive mass to `c - c`-regular laws (for
instance, laws vanishing on small sets or absolutely continuous with respect to an additive Haar
measure) has at most one quadratic Fréchet barycenter in `P₂(E)`. -/
theorem subsingleton_frechetBarycenters_two {P : Measure (WassersteinSpace 2 E)}
    (hP : P {m : WassersteinSpace 2 E |
      IsCCRegular ((m : ProbabilityMeasure E) : Measure E)} ≠ 0) :
    (frechetBarycenters 2 P).Subsingleton := by
  refine subsingleton_frechetBarycenters ENNReal.ofNat_ne_top (mt (measure_mono_null ?_) hP)
  intro m (hm : IsCCRegular _) ν π hπ
  rw [ENNReal.toReal_ofNat] at hπ
  obtain ⟨T, hT, hπT⟩ := hπ.exists_eq_graphPlan_of_isCCRegular hm
    (wassersteinEDist_ne_top measurable_edist m ν)
  exact ⟨T, hT.aemeasurable, hπT⟩

/-- **Uniqueness of quadratic Wasserstein barycenters of finitely many laws** (Agueh–Carlier). On
a finite-dimensional real inner product space, if one of finitely many laws `μ i` of `P₂(E)` is
`c - c`-regular and has a nonzero weight, then the law `∑ i, w i • δ_{μ i}` has at most one
quadratic Fréchet barycenter in `P₂(E)`. -/
theorem subsingleton_frechetBarycenters_two_sum_smul_dirac {ι : Type*} [Fintype ι]
    {w : ι → ℝ≥0} {μ : ι → WassersteinSpace 2 E} {j : ι} (hj : w j ≠ 0)
    (hμj : IsCCRegular ((μ j : ProbabilityMeasure E) : Measure E)) :
    (frechetBarycenters 2 (∑ i, w i • Measure.dirac (μ i))).Subsingleton :=
  subsingleton_frechetBarycenters_two
    (sum_smul_dirac_apply_ne_zero_of_mem (Finset.mem_univ j) hj hμj)

end WassersteinSpace

end TauCeti
