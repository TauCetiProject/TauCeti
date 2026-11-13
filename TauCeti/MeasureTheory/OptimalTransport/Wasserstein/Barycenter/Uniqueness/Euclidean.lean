/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Measure.Haar.Hausdorff
public import TauCeti.MeasureTheory.OptimalTransport.Brenier.SmallSet
public import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Barycenter.Uniqueness.Basic
import TauCeti.MeasureTheory.Measure.Dirac

/-!
# Uniqueness of quadratic Euclidean barycenters

On a finite-dimensional real inner product space `E`, Brenier's theorem for sources vanishing on
Lipschitz hypersurfaces (`TauCeti.IsOptimalCoupling.exists_eq_graphPlan_of_null_lipschitz_graphs`)
shows that every optimal plan for the cost `edist ^ 2` out of such a law, into a law at finite `W₂`
distance from it, is induced by a measurable map. Between laws of `P₂(E)` the distance is always
finite, so this discharges the hypothesis of the general uniqueness theorem
`TauCeti.WassersteinSpace.subsingleton_frechetBarycenters`.

Consequently, a law `P` on `P₂(E)` has at most one quadratic Fréchet barycenter whenever it gives
positive mass to laws vanishing on Lipschitz graphs over hyperplanes—in particular whenever it gives
positive mass to laws vanishing on Borel sets with `dimH A + 1 ≤ finrank ℝ E`, on small sets
(`dimH A ≤ finrank ℝ E - 1`, Agueh–Carlier Proposition 3.5), or to laws absolutely continuous with
respect to an additive Haar measure. Specializing `P` to `∑ i, w i • δ_{μ i}` gives the finite
barycenter uniqueness theorem of Agueh and Carlier under each of these conditions.

## Main statements

* `TauCeti.WassersteinSpace.subsingleton_frechetBarycenters_two_of_null_lipschitz_graphs`,
  `TauCeti.WassersteinSpace.subsingleton_frechetBarycenters_two_of_dimH_add_one_le`,
  `TauCeti.WassersteinSpace.subsingleton_frechetBarycenters_two_of_dimH_le`, and
  `TauCeti.WassersteinSpace.subsingleton_frechetBarycenters_two` — population uniqueness of
  quadratic Wasserstein barycenters;
* `WassersteinSpace.subsingleton_frechetBarycenters_two_sum_smul_dirac_of_null_lipschitz_graphs`,
  `TauCeti.WassersteinSpace.subsingleton_frechetBarycenters_two_sum_smul_dirac_of_dimH_add_one_le`,
  `TauCeti.WassersteinSpace.subsingleton_frechetBarycenters_two_sum_smul_dirac_of_dimH_le`, and
  `TauCeti.WassersteinSpace.subsingleton_frechetBarycenters_two_sum_smul_dirac` — finite
  barycenter uniqueness when one positively weighted input law vanishes on Lipschitz hypersurfaces,
  on small sets, or is absolutely continuous.

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

open MeasureTheory Module Set
open scoped ENNReal NNReal

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

namespace WassersteinSpace

/-- **Uniqueness of quadratic Wasserstein barycenters under null Lipschitz hypersurfaces.** On a
finite-dimensional real inner product space `E`, a law `P` on `P₂(E)` that gives positive mass to
the laws vanishing on globally Lipschitz graphs over hyperplanes has at most one quadratic Fréchet
barycenter in `P₂(E)`. -/
theorem subsingleton_frechetBarycenters_two_of_null_lipschitz_graphs
    {P : Measure (WassersteinSpace 2 E)}
    (hP : P {m : WassersteinSpace 2 E | ∀ (v : E), ‖v‖ = 1 → ∀ (K : ℝ≥0) (g : (ℝ ∙ v)ᗮ → ℝ),
      LipschitzWith K g →
        ((m : ProbabilityMeasure E) : Measure E)
          (range fun w : (ℝ ∙ v)ᗮ => (w : E) + g w • v) = 0} ≠ 0) :
    (frechetBarycenters 2 P).Subsingleton := by
  refine subsingleton_frechetBarycenters ENNReal.ofNat_ne_top (mt (measure_mono_null ?_) hP)
  intro m hm ν π hπ
  rw [ENNReal.toReal_ofNat] at hπ
  obtain ⟨T, hT, hπT⟩ := hπ.exists_eq_graphPlan_of_null_lipschitz_graphs hm
    (wassersteinEDist_ne_top measurable_edist m ν)
  exact ⟨T, hT.aemeasurable, hπT⟩

/-- **Uniqueness of quadratic Wasserstein barycenters under `dimH A + 1 ≤ finrank ℝ E`.** This
hypothesis holds in every finite dimension, including `0`. -/
theorem subsingleton_frechetBarycenters_two_of_dimH_add_one_le
    {P : Measure (WassersteinSpace 2 E)}
    (hP : P {m : WassersteinSpace 2 E | ∀ A, MeasurableSet A →
      dimH A + 1 ≤ (finrank ℝ E : ℝ≥0∞) →
        ((m : ProbabilityMeasure E) : Measure E) A = 0} ≠ 0) :
    (frechetBarycenters 2 P).Subsingleton := by
  refine subsingleton_frechetBarycenters_two_of_null_lipschitz_graphs
    (mt (measure_mono_null ?_) hP)
  intro m hm _ hv _ _ hg
  exact measure_range_add_smul_eq_zero_of_dimH_add_one_le hm hv hg

/-- **Uniqueness of quadratic Wasserstein barycenters under vanishing on small sets
(`dimH A ≤ finrank ℝ E - 1`).** -/
theorem subsingleton_frechetBarycenters_two_of_dimH_le
    {P : Measure (WassersteinSpace 2 E)}
    (hP : P {m : WassersteinSpace 2 E | ∀ A, MeasurableSet A →
      dimH A ≤ ((finrank ℝ E - 1 : ℕ) : ℝ≥0∞) →
        ((m : ProbabilityMeasure E) : Measure E) A = 0} ≠ 0) :
    (frechetBarycenters 2 P).Subsingleton := by
  refine subsingleton_frechetBarycenters_two_of_dimH_add_one_le
    (mt (measure_mono_null ?_) hP)
  intro m hm _ hA hdim
  exact measure_eq_zero_of_dimH_add_one_le_of_forall_dimH_le hm hA hdim

/-- **Uniqueness of quadratic Wasserstein barycenters.** On a finite-dimensional real inner
product space, a law `P` on `P₂(E)` that gives positive mass to the laws absolutely continuous
with respect to an additive Haar measure has at most one quadratic Fréchet barycenter in
`P₂(E)`. -/
theorem subsingleton_frechetBarycenters_two {ρ : Measure E} [ρ.IsAddHaarMeasure]
    {P : Measure (WassersteinSpace 2 E)}
    (hP : P {m : WassersteinSpace 2 E | ((m : ProbabilityMeasure E) : Measure E) ≪ ρ} ≠ 0) :
    (frechetBarycenters 2 P).Subsingleton := by
  refine subsingleton_frechetBarycenters_two_of_dimH_add_one_le
    (mt (measure_mono_null ?_) hP)
  intro m hm _ _ hdim
  exact hm (ρ.addHaar_eq_zero_of_dimH_add_one_le_finrank hdim)

/-- **Uniqueness of quadratic Wasserstein barycenters of finitely many laws** when one positively
weighted input law vanishes on Lipschitz graphs over hyperplanes. -/
theorem subsingleton_frechetBarycenters_two_sum_smul_dirac_of_null_lipschitz_graphs
    {ι : Type*} [Fintype ι] {w : ι → ℝ≥0} {μ : ι → WassersteinSpace 2 E} {j : ι} (hj : w j ≠ 0)
    (hμj : ∀ (v : E), ‖v‖ = 1 → ∀ (K : ℝ≥0) (g : (ℝ ∙ v)ᗮ → ℝ), LipschitzWith K g →
      ((μ j : ProbabilityMeasure E) : Measure E)
        (range fun w : (ℝ ∙ v)ᗮ => (w : E) + g w • v) = 0) :
    (frechetBarycenters 2 (∑ i, w i • Measure.dirac (μ i))).Subsingleton :=
  subsingleton_frechetBarycenters_two_of_null_lipschitz_graphs
    (sum_smul_dirac_apply_ne_zero_of_mem (Finset.mem_univ j) hj hμj)

/-- **Uniqueness of quadratic Wasserstein barycenters of finitely many laws** when one positively
weighted input law vanishes on Borel sets with `dimH A + 1 ≤ finrank ℝ E`. -/
theorem subsingleton_frechetBarycenters_two_sum_smul_dirac_of_dimH_add_one_le
    {ι : Type*} [Fintype ι] {w : ι → ℝ≥0} {μ : ι → WassersteinSpace 2 E} {j : ι} (hj : w j ≠ 0)
    (hμj : ∀ A, MeasurableSet A → dimH A + 1 ≤ (finrank ℝ E : ℝ≥0∞) →
      ((μ j : ProbabilityMeasure E) : Measure E) A = 0) :
    (frechetBarycenters 2 (∑ i, w i • Measure.dirac (μ i))).Subsingleton :=
  subsingleton_frechetBarycenters_two_of_dimH_add_one_le
    (sum_smul_dirac_apply_ne_zero_of_mem (Finset.mem_univ j) hj hμj)

/-- **Uniqueness of quadratic Wasserstein barycenters of finitely many laws** (Agueh–Carlier,
Proposition 3.5) when one positively weighted input law vanishes on small sets
(`dimH A ≤ finrank ℝ E - 1`). -/
theorem subsingleton_frechetBarycenters_two_sum_smul_dirac_of_dimH_le
    {ι : Type*} [Fintype ι] {w : ι → ℝ≥0} {μ : ι → WassersteinSpace 2 E} {j : ι} (hj : w j ≠ 0)
    (hμj : ∀ A, MeasurableSet A → dimH A ≤ ((finrank ℝ E - 1 : ℕ) : ℝ≥0∞) →
      ((μ j : ProbabilityMeasure E) : Measure E) A = 0) :
    (frechetBarycenters 2 (∑ i, w i • Measure.dirac (μ i))).Subsingleton :=
  subsingleton_frechetBarycenters_two_of_dimH_le
    (sum_smul_dirac_apply_ne_zero_of_mem (Finset.mem_univ j) hj hμj)

/-- **Uniqueness of quadratic Wasserstein barycenters of finitely many laws** (Agueh–Carlier). On
a finite-dimensional real inner product space, if one of finitely many laws `μ i` of `P₂(E)` is
absolutely continuous with respect to an additive Haar measure and has a nonzero weight, then the
law `∑ i, w i • δ_{μ i}` has at most one quadratic Fréchet barycenter in `P₂(E)`. -/
theorem subsingleton_frechetBarycenters_two_sum_smul_dirac {ρ : Measure E} [ρ.IsAddHaarMeasure]
    {ι : Type*} [Fintype ι] {w : ι → ℝ≥0} {μ : ι → WassersteinSpace 2 E} {j : ι} (hj : w j ≠ 0)
    (hμj : ((μ j : ProbabilityMeasure E) : Measure E) ≪ ρ) :
    (frechetBarycenters 2 (∑ i, w i • Measure.dirac (μ i))).Subsingleton :=
  subsingleton_frechetBarycenters_two (ρ := ρ)
    (sum_smul_dirac_apply_ne_zero_of_mem (Finset.mem_univ j) hj hμj)

end WassersteinSpace

end TauCeti
