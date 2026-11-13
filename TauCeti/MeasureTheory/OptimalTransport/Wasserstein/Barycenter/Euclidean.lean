/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Barycenter.Uniqueness.Euclidean
public import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.PopulationBarycenter
import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.FrechetMean

/-!
# Existence and uniqueness of quadratic Euclidean Wasserstein barycenters

Let `E` be a finite-dimensional real inner product space. Because `E` is proper, the existence
theorems of Agueh–Carlier and Le Gouic–Loubes
(`TauCeti.WassersteinSpace.exists_isFrechetBarycenter_sum_smul_dirac` and
`TauCeti.WassersteinSpace.exists_isFrechetBarycenter`) provide quadratic Fréchet barycenters in
`P₂(E)` for every finitely supported probability law `∑ i, w i • δ_{μ i}` and, more generally, for
every probability law `P` on `P₂(E)` of finite second moment. Combining existence with the Brenier
uniqueness theorems of
`TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Barycenter.Uniqueness.Euclidean` yields
existence and uniqueness whenever positive mass is given to laws vanishing on Lipschitz graphs over
hyperplanes, on Borel sets with `dimH A + 1 ≤ finrank ℝ E`, on small sets
(`dimH A ≤ finrank ℝ E - 1`), or on laws absolutely continuous with respect to an additive Haar
measure.

For finitely many probability laws `μ i` on `E` of finite second moment with weights summing to
`1`, any probability measure `ν` minimizing the weighted quadratic cost
`ν ↦ ∑ i, w i * W₂(ν, μ i) ^ 2` over all of `ProbabilityMeasure E` costs no more than `μ j`, hence
automatically has finite second moment
(`TauCeti.hasFiniteMoment_of_sum_mul_wassersteinEDist_rpow_ne_top`) and belongs to `P₂(E)`.
Conversely, a Fréchet barycenter in `P₂(E)` minimizes the weighted cost over all probability laws
(`TauCeti.WassersteinSpace.isMinOn_sum_mul_wassersteinEDist_rpow_of_isFrechetBarycenter`). This
yields Agueh and Carlier's existence and uniqueness theorem over `ProbabilityMeasure E` and its
specialization `TauCeti.existsUnique_isMinOn_sum_wassersteinEDist_sq_of_dimH_le` on
`EuclideanSpace ℝ (Fin n)`.

## Main statements

* `TauCeti.WassersteinSpace.existsUnique_isFrechetBarycenter_two_of_null_lipschitz_graphs`,
  `TauCeti.WassersteinSpace.existsUnique_isFrechetBarycenter_two_of_dimH_add_one_le`,
  `TauCeti.WassersteinSpace.existsUnique_isFrechetBarycenter_two_of_dimH_le`, and
  `TauCeti.WassersteinSpace.existsUnique_isFrechetBarycenter_two` — existence and uniqueness of
  population quadratic Wasserstein barycenters in `P₂(E)`;
* `WassersteinSpace.existsUnique_isFrechetBarycenter_two_sum_smul_dirac_of_null_lipschitz_graphs`,
  `TauCeti.WassersteinSpace.existsUnique_isFrechetBarycenter_two_sum_smul_dirac_of_dimH_add_one_le`,
  `TauCeti.WassersteinSpace.existsUnique_isFrechetBarycenter_two_sum_smul_dirac_of_dimH_le`, and
  `TauCeti.WassersteinSpace.existsUnique_isFrechetBarycenter_two_sum_smul_dirac` — existence and
  uniqueness of finite quadratic barycenters in `P₂(E)`;
* `TauCeti.existsUnique_isMinOn_sum_mul_wassersteinEDist_sq_of_null_lipschitz_graphs`,
  `TauCeti.existsUnique_isMinOn_sum_mul_wassersteinEDist_sq_of_dimH_add_one_le`,
  `TauCeti.existsUnique_isMinOn_sum_mul_wassersteinEDist_sq_of_dimH_le`, and
  `TauCeti.existsUnique_isMinOn_sum_mul_wassersteinEDist_sq_of_absolutelyContinuous` — existence and
  uniqueness of minimizers over `ProbabilityMeasure E`;
* `TauCeti.existsUnique_isMinOn_sum_wassersteinEDist_sq_of_dimH_le` — **Agueh–Carlier existence and
  uniqueness of quadratic barycenters** on `EuclideanSpace ℝ (Fin n)`.

## References

* M. Agueh and G. Carlier, *Barycenters in the Wasserstein space*, SIAM J. Math. Anal. 43 (2011),
  904–924, Proposition 2.3, Definition 3.2, and Proposition 3.5.
* T. Le Gouic and J.-M. Loubes, *Existence and consistency of Wasserstein barycenters*,
  Probab. Theory Related Fields 168 (2017), 901–917.
-/

public section

noncomputable section

open MeasureTheory Module Set
open scoped ENNReal NNReal

namespace TauCeti

section GeneralInnerProduct

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

namespace WassersteinSpace

/-- **Existence and uniqueness of population quadratic Wasserstein barycenters** when `P` gives
positive mass to laws vanishing on Lipschitz graphs over hyperplanes. -/
theorem existsUnique_isFrechetBarycenter_two_of_null_lipschitz_graphs
    (P : Measure (WassersteinSpace 2 E)) [IsProbabilityMeasure P] (hP2 : HasFiniteMoment 2 P)
    (hP : P {m : WassersteinSpace 2 E | ∀ (v : E), ‖v‖ = 1 → ∀ (K : ℝ≥0) (g : (ℝ ∙ v)ᗮ → ℝ),
      LipschitzWith K g →
        ((m : ProbabilityMeasure E) : Measure E)
          (range fun w : (ℝ ∙ v)ᗮ => (w : E) + g w • v) = 0} ≠ 0) :
    ∃! ν : WassersteinSpace 2 E, IsFrechetBarycenter 2 P ν := by
  have : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨one_le_two⟩
  obtain ⟨ν, hν⟩ := exists_isFrechetBarycenter ENNReal.ofNat_ne_top P hP2
  exact ⟨ν, hν, fun ν' hν' =>
    subsingleton_frechetBarycenters_two_of_null_lipschitz_graphs hP
      (mem_frechetBarycenters.mpr hν') (mem_frechetBarycenters.mpr hν)⟩

/-- **Existence and uniqueness of population quadratic Wasserstein barycenters** when `P` gives
positive mass to laws vanishing on Borel sets with `dimH A + 1 ≤ finrank ℝ E`. -/
theorem existsUnique_isFrechetBarycenter_two_of_dimH_add_one_le
    (P : Measure (WassersteinSpace 2 E)) [IsProbabilityMeasure P] (hP2 : HasFiniteMoment 2 P)
    (hP : P {m : WassersteinSpace 2 E | ∀ A, MeasurableSet A →
      dimH A + 1 ≤ (finrank ℝ E : ℝ≥0∞) →
        ((m : ProbabilityMeasure E) : Measure E) A = 0} ≠ 0) :
    ∃! ν : WassersteinSpace 2 E, IsFrechetBarycenter 2 P ν :=
  existsUnique_isFrechetBarycenter_two_of_null_lipschitz_graphs P hP2
    (mt (measure_mono_null fun _ hm _ hv _ _ hg =>
      measure_range_add_smul_eq_zero_of_dimH_add_one_le hm hv hg) hP)

/-- **Existence and uniqueness of population quadratic Wasserstein barycenters** when `P` gives
positive mass to laws vanishing on small sets (`dimH A ≤ finrank ℝ E - 1`). -/
theorem existsUnique_isFrechetBarycenter_two_of_dimH_le
    (P : Measure (WassersteinSpace 2 E)) [IsProbabilityMeasure P] (hP2 : HasFiniteMoment 2 P)
    (hP : P {m : WassersteinSpace 2 E | ∀ A, MeasurableSet A →
      dimH A ≤ ((finrank ℝ E - 1 : ℕ) : ℝ≥0∞) →
        ((m : ProbabilityMeasure E) : Measure E) A = 0} ≠ 0) :
    ∃! ν : WassersteinSpace 2 E, IsFrechetBarycenter 2 P ν :=
  existsUnique_isFrechetBarycenter_two_of_dimH_add_one_le P hP2
    (mt (measure_mono_null fun _ hm _ hA hdim =>
      measure_eq_zero_of_dimH_add_one_le_of_forall_dimH_le hm hA hdim) hP)

/-- **Existence and uniqueness of population quadratic Wasserstein barycenters** (Le Gouic–Loubes)
when `P` gives positive mass to laws absolutely continuous with respect to an additive Haar
measure. -/
theorem existsUnique_isFrechetBarycenter_two {ρ : Measure E} [ρ.IsAddHaarMeasure]
    (P : Measure (WassersteinSpace 2 E)) [IsProbabilityMeasure P] (hP2 : HasFiniteMoment 2 P)
    (hP : P {m : WassersteinSpace 2 E | ((m : ProbabilityMeasure E) : Measure E) ≪ ρ} ≠ 0) :
    ∃! ν : WassersteinSpace 2 E, IsFrechetBarycenter 2 P ν := by
  refine existsUnique_isFrechetBarycenter_two_of_dimH_add_one_le P hP2
    (mt (measure_mono_null ?_) hP)
  exact fun _ hm _ _ hdim => hm (ρ.addHaar_eq_zero_of_dimH_add_one_le_finrank hdim)

/-- **Existence and uniqueness of finite quadratic Wasserstein barycenters in `P₂(E)`** when one
positively weighted input law vanishes on Lipschitz graphs over hyperplanes. -/
theorem existsUnique_isFrechetBarycenter_two_sum_smul_dirac_of_null_lipschitz_graphs
    {ι : Type*} [Fintype ι] {w : ι → ℝ≥0} (hw : ∑ i, w i = 1) (μ : ι → WassersteinSpace 2 E)
    {j : ι} (hj : w j ≠ 0)
    (hμj : ∀ (v : E), ‖v‖ = 1 → ∀ (K : ℝ≥0) (g : (ℝ ∙ v)ᗮ → ℝ), LipschitzWith K g →
      ((μ j : ProbabilityMeasure E) : Measure E)
        (range fun w : (ℝ ∙ v)ᗮ => (w : E) + g w • v) = 0) :
    ∃! ν : WassersteinSpace 2 E, IsFrechetBarycenter 2 (∑ i, w i • Measure.dirac (μ i)) ν := by
  have : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨one_le_two⟩
  obtain ⟨ν, hν⟩ := exists_isFrechetBarycenter_sum_smul_dirac ENNReal.ofNat_ne_top hw μ
  exact ⟨ν, hν, fun ν' hν' =>
    subsingleton_frechetBarycenters_two_sum_smul_dirac_of_null_lipschitz_graphs hj hμj
      (mem_frechetBarycenters.mpr hν') (mem_frechetBarycenters.mpr hν)⟩

/-- **Existence and uniqueness of finite quadratic Wasserstein barycenters in `P₂(E)`** when one
positively weighted input law vanishes on Borel sets with `dimH A + 1 ≤ finrank ℝ E`. -/
theorem existsUnique_isFrechetBarycenter_two_sum_smul_dirac_of_dimH_add_one_le
    {ι : Type*} [Fintype ι] {w : ι → ℝ≥0} (hw : ∑ i, w i = 1) (μ : ι → WassersteinSpace 2 E)
    {j : ι} (hj : w j ≠ 0)
    (hμj : ∀ A, MeasurableSet A → dimH A + 1 ≤ (finrank ℝ E : ℝ≥0∞) →
      ((μ j : ProbabilityMeasure E) : Measure E) A = 0) :
    ∃! ν : WassersteinSpace 2 E, IsFrechetBarycenter 2 (∑ i, w i • Measure.dirac (μ i)) ν :=
  existsUnique_isFrechetBarycenter_two_sum_smul_dirac_of_null_lipschitz_graphs hw μ hj
    fun _ hv _ _ hg => measure_range_add_smul_eq_zero_of_dimH_add_one_le hμj hv hg

/-- **Existence and uniqueness of finite quadratic Wasserstein barycenters in `P₂(E)`**
(Agueh–Carlier) when one positively weighted input law vanishes on small sets
(`dimH A ≤ finrank ℝ E - 1`). -/
theorem existsUnique_isFrechetBarycenter_two_sum_smul_dirac_of_dimH_le
    {ι : Type*} [Fintype ι] {w : ι → ℝ≥0} (hw : ∑ i, w i = 1) (μ : ι → WassersteinSpace 2 E)
    {j : ι} (hj : w j ≠ 0)
    (hμj : ∀ A, MeasurableSet A → dimH A ≤ ((finrank ℝ E - 1 : ℕ) : ℝ≥0∞) →
      ((μ j : ProbabilityMeasure E) : Measure E) A = 0) :
    ∃! ν : WassersteinSpace 2 E, IsFrechetBarycenter 2 (∑ i, w i • Measure.dirac (μ i)) ν :=
  existsUnique_isFrechetBarycenter_two_sum_smul_dirac_of_dimH_add_one_le hw μ hj
    fun _ hA hdim => measure_eq_zero_of_dimH_add_one_le_of_forall_dimH_le hμj hA hdim

/-- **Existence and uniqueness of finite quadratic Wasserstein barycenters in `P₂(E)`**
(Agueh–Carlier) when one positively weighted input law is absolutely continuous with respect to an
additive Haar measure. -/
theorem existsUnique_isFrechetBarycenter_two_sum_smul_dirac {ρ : Measure E} [ρ.IsAddHaarMeasure]
    {ι : Type*} [Fintype ι] {w : ι → ℝ≥0} (hw : ∑ i, w i = 1) (μ : ι → WassersteinSpace 2 E)
    {j : ι} (hj : w j ≠ 0)
    (hμj : ((μ j : ProbabilityMeasure E) : Measure E) ≪ ρ) :
    ∃! ν : WassersteinSpace 2 E, IsFrechetBarycenter 2 (∑ i, w i • Measure.dirac (μ i)) ν :=
  existsUnique_isFrechetBarycenter_two_sum_smul_dirac_of_dimH_add_one_le hw μ hj
    fun _ _ hdim => hμj (ρ.addHaar_eq_zero_of_dimH_add_one_le_finrank hdim)

end WassersteinSpace

/-- **Existence and uniqueness of quadratic barycenters over `ProbabilityMeasure E`** when one
positively weighted input law vanishes on globally Lipschitz graphs over hyperplanes. -/
theorem existsUnique_isMinOn_sum_mul_wassersteinEDist_sq_of_null_lipschitz_graphs
    {ι : Type*} [Fintype ι] (w : ι → ℝ≥0) (hw : ∑ i, w i = 1) (μ : ι → Measure E)
    [∀ i, IsProbabilityMeasure (μ i)] (hμ : ∀ i, HasFiniteMoment 2 (μ i))
    {j : ι} (hj : w j ≠ 0)
    (hμj : ∀ (v : E), ‖v‖ = 1 → ∀ (K : ℝ≥0) (g : (ℝ ∙ v)ᗮ → ℝ), LipschitzWith K g →
      μ j (range fun w : (ℝ ∙ v)ᗮ => (w : E) + g w • v) = 0) :
    ∃! ν : ProbabilityMeasure E,
      IsMinOn (fun ν : ProbabilityMeasure E =>
        ∑ i, (w i : ℝ≥0∞) * wassersteinEDist 2 (ν : Measure E) (μ i) ^ 2) univ ν := by
  have : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨one_le_two⟩
  let μW : ι → WassersteinSpace 2 E := fun i => WassersteinSpace.mk ⟨μ i, inferInstance⟩ (hμ i)
  have hcoe (i : ι) : ((μW i : ProbabilityMeasure E) : Measure E) = μ i :=
    congrArg ProbabilityMeasure.toMeasure (WassersteinSpace.coe_mk _ _)
  have h := WassersteinSpace.existsUnique_isMinOn_sum_mul_wassersteinEDist_rpow_of_existsUnique
    (p := 2) ENNReal.ofNat_ne_top (μ := μW) hj
    (WassersteinSpace.existsUnique_isFrechetBarycenter_two_sum_smul_dirac_of_null_lipschitz_graphs
      hw μW hj (by simpa only [hcoe] using hμj))
  simpa only [hcoe, ENNReal.toReal_ofNat, ENNReal.rpow_ofNat] using h

/-- **Existence and uniqueness of quadratic barycenters over `ProbabilityMeasure E`** when one
positively weighted input law vanishes on Borel sets with `dimH A + 1 ≤ finrank ℝ E`. This form
remains non-vacuous when `finrank ℝ E = 0`. -/
theorem existsUnique_isMinOn_sum_mul_wassersteinEDist_sq_of_dimH_add_one_le
    {ι : Type*} [Fintype ι] (w : ι → ℝ≥0) (hw : ∑ i, w i = 1) (μ : ι → Measure E)
    [∀ i, IsProbabilityMeasure (μ i)] (hμ : ∀ i, HasFiniteMoment 2 (μ i))
    {j : ι} (hj : w j ≠ 0)
    (hsmall : ∀ A, MeasurableSet A → dimH A + 1 ≤ (finrank ℝ E : ℝ≥0∞) → μ j A = 0) :
    ∃! ν : ProbabilityMeasure E,
      IsMinOn (fun ν : ProbabilityMeasure E =>
        ∑ i, (w i : ℝ≥0∞) * wassersteinEDist 2 (ν : Measure E) (μ i) ^ 2) univ ν :=
  existsUnique_isMinOn_sum_mul_wassersteinEDist_sq_of_null_lipschitz_graphs w hw μ hμ hj
    fun _ hv _ _ hg => measure_range_add_smul_eq_zero_of_dimH_add_one_le hsmall hv hg

/-- **Existence and uniqueness of quadratic barycenters over `ProbabilityMeasure E`**
(Agueh–Carlier) when one positively weighted input law vanishes on small sets
(`dimH A ≤ finrank ℝ E - 1`). -/
theorem existsUnique_isMinOn_sum_mul_wassersteinEDist_sq_of_dimH_le
    {ι : Type*} [Fintype ι] (w : ι → ℝ≥0) (hw : ∑ i, w i = 1) (μ : ι → Measure E)
    [∀ i, IsProbabilityMeasure (μ i)] (hμ : ∀ i, HasFiniteMoment 2 (μ i))
    {j : ι} (hj : w j ≠ 0)
    (hsmall : ∀ A, MeasurableSet A → dimH A ≤ ((finrank ℝ E - 1 : ℕ) : ℝ≥0∞) → μ j A = 0) :
    ∃! ν : ProbabilityMeasure E,
      IsMinOn (fun ν : ProbabilityMeasure E =>
        ∑ i, (w i : ℝ≥0∞) * wassersteinEDist 2 (ν : Measure E) (μ i) ^ 2) univ ν :=
  existsUnique_isMinOn_sum_mul_wassersteinEDist_sq_of_dimH_add_one_le w hw μ hμ hj
    fun _ hA hdim => measure_eq_zero_of_dimH_add_one_le_of_forall_dimH_le hsmall hA hdim

/-- **Existence and uniqueness of quadratic barycenters over `ProbabilityMeasure E`**
(Agueh–Carlier) when one positively weighted input law is absolutely continuous with respect to an
additive Haar measure. -/
theorem existsUnique_isMinOn_sum_mul_wassersteinEDist_sq_of_absolutelyContinuous
    {ρ : Measure E} [ρ.IsAddHaarMeasure]
    {ι : Type*} [Fintype ι] (w : ι → ℝ≥0) (hw : ∑ i, w i = 1) (μ : ι → Measure E)
    [∀ i, IsProbabilityMeasure (μ i)] (hμ : ∀ i, HasFiniteMoment 2 (μ i))
    {j : ι} (hj : w j ≠ 0) (hμj : μ j ≪ ρ) :
    ∃! ν : ProbabilityMeasure E,
      IsMinOn (fun ν : ProbabilityMeasure E =>
        ∑ i, (w i : ℝ≥0∞) * wassersteinEDist 2 (ν : Measure E) (μ i) ^ 2) univ ν :=
  existsUnique_isMinOn_sum_mul_wassersteinEDist_sq_of_dimH_add_one_le w hw μ hμ hj
    fun _ _ hdim => hμj (ρ.addHaar_eq_zero_of_dimH_add_one_le_finrank hdim)

end GeneralInnerProduct

/-- **Agueh–Carlier existence and uniqueness of quadratic barycenters** (Agueh–Carlier 2011,
Proposition 2.3, Definition 3.2 and Proposition 3.5). For finitely many laws `μ i` of finite
second moment on `ℝⁿ` and weights `w i ≥ 0` summing to one, suppose that one input `μ j` of
positive weight vanishes on small sets: `μ j A = 0` for every Borel `A` of Hausdorff dimension at
most `n - 1`. Then exactly one probability measure minimizes `ν ↦ ∑ i, w i W₂(ν, μ i)²`.
For `n = 0` the truncated `n - 1` is `0`, the hypothesis `hsmall` is unsatisfiable, and the
statement is vacuous; see
`TauCeti.existsUnique_isMinOn_sum_mul_wassersteinEDist_sq_of_dimH_add_one_le` for the
dimension-zero-compatible formulation `dimH A + 1 ≤ finrank ℝ E`. -/
theorem existsUnique_isMinOn_sum_wassersteinEDist_sq_of_dimH_le {n : ℕ} {ι : Type*} [Fintype ι]
    (w : ι → ℝ≥0) (hw : ∑ i, w i = 1) (μ : ι → Measure (EuclideanSpace ℝ (Fin n)))
    [∀ i, IsProbabilityMeasure (μ i)] (hμ : ∀ i, HasFiniteMoment 2 (μ i))
    {j : ι} (hj : w j ≠ 0)
    (hsmall : ∀ A, MeasurableSet A → dimH A ≤ ((n - 1 : ℕ) : ℝ≥0∞) → μ j A = 0) :
    ∃! ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)),
      IsMinOn (fun ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)) =>
        ∑ i, (w i : ℝ≥0∞) * wassersteinEDist 2 (ν : Measure _) (μ i) ^ 2) univ ν :=
  existsUnique_isMinOn_sum_mul_wassersteinEDist_sq_of_dimH_le
    (E := EuclideanSpace ℝ (Fin n)) w hw μ hμ hj fun A hA hdim =>
      hsmall A hA (by simpa only [finrank_euclideanSpace_fin] using hdim)

end TauCeti
