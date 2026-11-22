/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Distributions.Beta
public import TauCeti.Probability.Distributions.Dirichlet.Density

/-!
# Two-category Dirichlet laws and the Beta distribution

When a finite index type `ι` has a single index away from `i₀` (`[Unique {i // i ≠ i₀}]`), the
simplex chart `TauCeti.Probability.dirichletChart` at `i₀` is parameterized by one real coordinate,
the chart region `TauCeti.Probability.dirichletChartRegion` is `Set.Ioo 0 1` in that coordinate
(`TauCeti.Probability.mem_dirichletChartRegion_iff_of_unique`), and
`TauCeti.Probability.dirichletChartPDFReal` agrees with `ProbabilityTheory.betaPDFReal` with first
shape `a default` and second shape `a i₀`. Because division on `ℝ` satisfies `1 / (x / y) = y / x`
unconditionally, the chart-density identities hold for every real parameter vector `a : ι → ℝ`. On
`Fin 2`, dropping coordinate `1` gives `betaPDFReal (a 0) (a 1)` while dropping coordinate `0`
exchanges the two shapes.

At positive concentration parameters, `dirichletMeasure a` is therefore the image of
`betaMeasure (a default) (a i₀)` under `u ↦ dirichletChart i₀ (fun _ ↦ u)` (on `Fin 2` at `i₀ = 1`,
the embedding `u ↦ (u, 1 - u)`). Outside the positive range the measure identity does not extend:
`dirichletMeasure` is zero whenever a parameter is nonpositive, whereas `betaMeasure` remains
nonzero whenever `ProbabilityTheory.beta` is positive (for instance at `a = ![-3 / 2, 2]`).

## Main results

* `TauCeti.Probability.dirichletChartPDFReal_of_unique` and
  `TauCeti.Probability.dirichletChartPDF_of_unique` — when `{i // i ≠ i₀}` is a singleton, the
  Dirichlet chart density at `i₀` equals the Beta density `betaPDFReal (a default) (a i₀)`
  (respectively `betaPDF`), specialized to `Fin 2` in
  `TauCeti.Probability.dirichletChartPDFReal_one_fin_two` and
  `TauCeti.Probability.dirichletChartPDFReal_zero_fin_two`;
* `TauCeti.Probability.dirichletMeasure_eq_map_betaMeasure_of_unique`,
  `TauCeti.Probability.dirichletMeasure_fin_two_eq_map_betaMeasure`,
  `ProbabilityTheory.HasLaw.dirichletChart_betaMeasure_of_unique`, and
  `ProbabilityTheory.HasLaw.pair_one_sub_betaMeasure` — at positive concentrations, a two-category
  Dirichlet law is the simplex pushforward of the corresponding Beta law.

## References

* N. L. Johnson, S. Kotz, N. Balakrishnan, *Continuous Multivariate Distributions*, vol. 1,
  2nd ed., Wiley, 2000, Chapter 49.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set

namespace TauCeti.Probability

/-! ### Simplex chart densities and Beta pushforward with one retained coordinate -/

section Unique

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- When `{i // i ≠ i₀}` has a unique index, the real Dirichlet chart density at `i₀` equals the
real Beta density with shapes `a default` and `a i₀`, for every real parameter vector `a`. -/
theorem dirichletChartPDFReal_of_unique (a : ι → ℝ) (i₀ : ι) [Unique {i // i ≠ i₀}]
    (x : {i // i ≠ i₀} → ℝ) :
    dirichletChartPDFReal a i₀ x =
      betaPDFReal (a (default : {i // i ≠ i₀})) (a i₀) (x default) := by
  by_cases hx : x ∈ dirichletChartRegion i₀
  · have hx' : 0 < x default ∧ x default < 1 :=
      mem_Ioo.mp (mem_dirichletChartRegion_iff_of_unique.mp hx)
    simp only [dirichletChartPDFReal_of_mem a hx, betaPDFReal, ite_eq_left hx',
      Fintype.sum_eq_add_sum_subtype_ne a i₀, Fintype.prod_eq_mul_prod_subtype_ne _ i₀,
      Fintype.sum_unique, Fintype.prod_unique, ProbabilityTheory.beta, one_div_div]
    rw [add_comm (a i₀), mul_comm (Real.Gamma (a i₀))]
  · have hx' : ¬(0 < x default ∧ x default < 1) :=
      fun h ↦ hx (mem_dirichletChartRegion_iff_of_unique.mpr (mem_Ioo.mpr h))
    rw [dirichletChartPDFReal_of_notMem a hx, betaPDFReal, ite_eq_right hx']

/-- When `{i // i ≠ i₀}` has a unique index, the extended nonnegative Dirichlet chart density at
`i₀` equals `betaPDF (a default) (a i₀)`, for every real parameter vector `a`. -/
theorem dirichletChartPDF_of_unique (a : ι → ℝ) (i₀ : ι) [Unique {i // i ≠ i₀}]
    (x : {i // i ≠ i₀} → ℝ) :
    dirichletChartPDF a i₀ x =
      betaPDF (a (default : {i // i ≠ i₀})) (a i₀) (x default) := by
  rw [dirichletChartPDF_eq_ofReal, betaPDF, dirichletChartPDFReal_of_unique]

/-- When `{i // i ≠ i₀}` has a unique index and `a` is positive, `dirichletMeasure a` is the image
of `betaMeasure (a default) (a i₀)` under `u ↦ dirichletChart i₀ (fun _ ↦ u)`. -/
theorem dirichletMeasure_eq_map_betaMeasure_of_unique {a : ι → ℝ} (ha : ∀ i, 0 < a i)
    (i₀ : ι) [Unique {i // i ≠ i₀}] :
    dirichletMeasure a =
      (betaMeasure (a (default : {i // i ≠ i₀})) (a i₀)).map
        (fun u ↦ dirichletChart i₀ (fun _ ↦ u)) := by
  let e : ({i // i ≠ i₀} → ℝ) ≃ᵐ ℝ := MeasurableEquiv.funUnique {i // i ≠ i₀} ℝ
  have hvol : (volume : Measure ℝ).map e.symm = (volume : Measure ({i // i ≠ i₀} → ℝ)) := by
    refine ((volume_preserving_funUnique {i // i ≠ i₀} ℝ).symm e).map_eq.trans ?_
    congr 2
    exact Subsingleton.elim _ _
  have hdens : (betaMeasure (a (default : {i // i ≠ i₀})) (a i₀)).map e.symm =
      (volume : Measure ({i // i ≠ i₀} → ℝ)).withDensity (dirichletChartPDF a i₀) := by
    rw [betaMeasure, e.symm.map_withDensity, hvol]
    congr 1
    funext x
    simp [e, dirichletChartPDF_of_unique]
  have hcomp : dirichletChart i₀ ∘ e.symm = fun u ↦ dirichletChart i₀ (fun _ ↦ u) :=
    funext fun u ↦ congrArg (dirichletChart i₀) (funext fun j ↦ by simp [e])
  rw [dirichletMeasure_eq_map_withDensity_dirichletChartPDF ha i₀, ← hdens,
    Measure.map_map measurable_dirichletChart e.symm.measurable, hcomp]

end Unique

/-! ### Specialization to `Fin 2` -/

/-- On `Fin 2`, the real Dirichlet chart density at dropped coordinate `1` equals the real Beta
density of shapes `a 0` and `a 1`, for every real parameter vector `a`. -/
theorem dirichletChartPDFReal_one_fin_two (a : Fin 2 → ℝ) (x : {i : Fin 2 // i ≠ 1} → ℝ) :
    dirichletChartPDFReal a 1 x = betaPDFReal (a 0) (a 1) (x ⟨0, by decide⟩) := by
  let _ : Unique {i : Fin 2 // i ≠ 1} := ⟨⟨⟨0, by decide⟩⟩, by decide⟩
  exact dirichletChartPDFReal_of_unique a 1 x

/-- On `Fin 2`, the extended nonnegative Dirichlet chart density at dropped coordinate `1` equals
`betaPDF (a 0) (a 1)`, for every real parameter vector `a`. -/
theorem dirichletChartPDF_one_fin_two (a : Fin 2 → ℝ) (x : {i : Fin 2 // i ≠ 1} → ℝ) :
    dirichletChartPDF a 1 x = betaPDF (a 0) (a 1) (x ⟨0, by decide⟩) := by
  let _ : Unique {i : Fin 2 // i ≠ 1} := ⟨⟨⟨0, by decide⟩⟩, by decide⟩
  exact dirichletChartPDF_of_unique a 1 x

/-- On `Fin 2`, the real Dirichlet chart density at dropped coordinate `0` equals the real Beta
density of reversed shapes `a 1` and `a 0`, for every real parameter vector `a`. -/
theorem dirichletChartPDFReal_zero_fin_two (a : Fin 2 → ℝ) (x : {i : Fin 2 // i ≠ 0} → ℝ) :
    dirichletChartPDFReal a 0 x = betaPDFReal (a 1) (a 0) (x ⟨1, by decide⟩) := by
  let _ : Unique {i : Fin 2 // i ≠ 0} := ⟨⟨⟨1, by decide⟩⟩, by decide⟩
  exact dirichletChartPDFReal_of_unique a 0 x

/-- On `Fin 2`, the extended nonnegative Dirichlet chart density at dropped coordinate `0` equals
`betaPDF (a 1) (a 0)`, for every real parameter vector `a`. -/
theorem dirichletChartPDF_zero_fin_two (a : Fin 2 → ℝ) (x : {i : Fin 2 // i ≠ 0} → ℝ) :
    dirichletChartPDF a 0 x = betaPDF (a 1) (a 0) (x ⟨1, by decide⟩) := by
  let _ : Unique {i : Fin 2 // i ≠ 0} := ⟨⟨⟨1, by decide⟩⟩, by decide⟩
  exact dirichletChartPDF_of_unique a 0 x

/-- At positive concentration parameters, the `Fin 2` Dirichlet law is the image of
`betaMeasure (a 0) (a 1)` under the simplex parameterization `u ↦ (u, 1 - u)`. -/
theorem dirichletMeasure_fin_two_eq_map_betaMeasure {a : Fin 2 → ℝ} (ha : ∀ i, 0 < a i) :
    dirichletMeasure a =
      (betaMeasure (a 0) (a 1)).map
        (fun u ↦ (EuclideanSpace.equiv (Fin 2) ℝ).symm ![u, 1 - u]) := by
  let _ : Unique {i : Fin 2 // i ≠ 1} := ⟨⟨⟨0, by decide⟩⟩, by decide⟩
  rw [dirichletMeasure_eq_map_betaMeasure_of_unique ha (1 : Fin 2)]
  congr 1
  funext u
  exact dirichletChart_one_fin_two (fun _ ↦ u)

end TauCeti.Probability

namespace ProbabilityTheory

open TauCeti.Probability

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- When `{i // i ≠ i₀}` has a unique index, embedding a Beta random variable `U` with positive
shapes `a default` and `a i₀` through `dirichletChart i₀` produces `dirichletMeasure a`. -/
theorem HasLaw.dirichletChart_betaMeasure_of_unique {ι : Type*} [Fintype ι] [DecidableEq ι]
    {U : Ω → ℝ} {a : ι → ℝ} {i₀ : ι} [Unique {i // i ≠ i₀}]
    (hU : HasLaw U (betaMeasure (a (default : {i // i ≠ i₀})) (a i₀)) P) (ha : ∀ i, 0 < a i) :
    HasLaw (fun ω ↦ dirichletChart i₀ (fun _ ↦ U ω)) (dirichletMeasure a) P := by
  have hmap : HasLaw (fun u : ℝ ↦ dirichletChart i₀ (fun _ ↦ u)) (dirichletMeasure a)
      (betaMeasure (a (default : {i // i ≠ i₀})) (a i₀)) :=
    ⟨(by fun_prop : Measurable _).aemeasurable,
      (dirichletMeasure_eq_map_betaMeasure_of_unique ha i₀).symm⟩
  exact hmap.fun_comp hU

/-- Embedding a Beta random variable `U` with positive shapes `a` and `b` as `(U, 1 - U)` produces
`dirichletMeasure ![a, b]`. -/
theorem HasLaw.pair_one_sub_betaMeasure {U : Ω → ℝ} {a b : ℝ}
    (hU : HasLaw U (betaMeasure a b) P) (ha : 0 < a) (hb : 0 < b) :
    HasLaw (fun ω ↦ (EuclideanSpace.equiv (Fin 2) ℝ).symm ![U ω, 1 - U ω])
      (dirichletMeasure ![a, b]) P := by
  let _ : Unique {i : Fin 2 // i ≠ 1} := ⟨⟨⟨0, by decide⟩⟩, by decide⟩
  have hab : ∀ i : Fin 2, 0 < ![a, b] i := Fin.forall_fin_two.2 ⟨ha, hb⟩
  simpa only [dirichletChart_one_fin_two] using
    hU.dirichletChart_betaMeasure_of_unique (a := ![a, b]) (i₀ := 1) hab

end ProbabilityTheory
