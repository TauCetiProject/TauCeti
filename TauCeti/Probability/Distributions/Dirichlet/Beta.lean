/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Distributions.Beta
public import TauCeti.Probability.Distributions.Dirichlet.Factorization

/-!
# Two-category Dirichlet laws and the Gamma–Beta reduction

When a finite index type `ι` has a single index away from `i₀` (`[Unique {i // i ≠ i₀}]`), the
simplex chart `TauCeti.Probability.dirichletChart` at `i₀` is parameterized by one real coordinate,
the chart region `TauCeti.Probability.dirichletChartRegion` is `Set.Ioo 0 1` in that coordinate,
and `TauCeti.Probability.dirichletChartPDFReal` agrees with `ProbabilityTheory.betaPDFReal` with
first shape `a default` and second shape `a i₀`. Because division on `ℝ` satisfies
`1 / (x / y) = y / x` unconditionally, the chart-density identities hold for every real parameter
vector `a : ι → ℝ`. On `Fin 2`, dropping coordinate `1` gives `betaPDFReal (a 0) (a 1)` while
dropping coordinate `0` exchanges the two shapes.

At positive concentration parameters, `dirichletMeasure a` is therefore the image of
`betaMeasure (a default) (a i₀)` under `u ↦ dirichletChart i₀ (fun _ ↦ u)` (on `Fin 2` at `i₀ = 1`,
the embedding `u ↦ (u, 1 - u)`). Outside the positive range the measure identity does not extend:
`dirichletMeasure` is zero whenever a parameter is nonpositive, whereas `betaMeasure` remains
nonzero whenever `ProbabilityTheory.beta` is positive (for instance at `a = ![-3 / 2, 2]`).

Evaluating the normalized vector at the retained coordinate reduces the two-category
Gamma–Dirichlet factorization `TauCeti.Probability.map_dirichletNormalize_sum_pi_gammaMeasure` to
the Gamma–Beta joint law of the coordinate ratio and total. On `ℝ × ℝ`,
`MeasurableEquiv.finTwoArrow` gives the corresponding binary-product and
`ProbabilityTheory.IndepFun` forms of the two-category Gamma–Dirichlet factorization.

## Main results

* `TauCeti.Probability.dirichletChartPDFReal_of_unique` and
  `TauCeti.Probability.dirichletChartPDF_of_unique` — when `{i // i ≠ i₀}` is a singleton, the
  Dirichlet chart density at `i₀` equals the Beta density `betaPDFReal (a default) (a i₀)`
  (respectively `betaPDF`), specialized to `Fin 2` in
  `TauCeti.Probability.dirichletChartPDFReal_one_fin_two` and
  `TauCeti.Probability.dirichletChartPDFReal_zero_fin_two`;
* `TauCeti.Probability.dirichletMeasure_eq_map_betaMeasure_of_unique`,
  `TauCeti.Probability.dirichletMeasure_fin_two_eq_map_betaMeasure`, and
  `ProbabilityTheory.HasLaw.dirichletMeasure_of_unique` — at positive concentrations, a two-category
  Dirichlet law is the simplex pushforward of the corresponding Beta law;
* `TauCeti.Probability.map_eval_one_dirichletMeasure_fin_two` — the second coordinate of a `Fin 2`
  Dirichlet law has law `betaMeasure (a 1) (a 0)`;
* `TauCeti.Probability.map_div_add_sum_pi_gammaMeasure_of_unique`,
  `TauCeti.Probability.map_div_add_pi_gammaMeasure_of_unique`,
  `TauCeti.Probability.map_div_add_sum_pi_gammaMeasure_fin_two`, and
  `TauCeti.Probability.map_div_add_pi_gammaMeasure_fin_two` — the two-category Gamma–Dirichlet
  factorization reduces to the Gamma–Beta joint and marginal ratio laws;
* `TauCeti.Probability.map_dirichletNormalize_add_prod_gammaMeasure`,
  `TauCeti.Probability.map_dirichletNormalize_prod_gammaMeasure`, and their
  `ProbabilityTheory.IndepFun` companions — the binary-product Gamma–Dirichlet factorization.

## References

* N. L. Johnson, S. Kotz, N. Balakrishnan, *Continuous Multivariate Distributions*, vol. 1,
  2nd ed., Wiley, 2000, Chapter 49.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set

namespace TauCeti.Probability

/-! ### Simplex charts with a single retained coordinate -/

section Unique

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- When `{i // i ≠ i₀}` has a unique index, membership in `dirichletChartRegion i₀` means that
the unique retained coordinate lies in `Ioo 0 1`. -/
theorem mem_dirichletChartRegion_of_unique_iff {i₀ : ι} [Unique {i // i ≠ i₀}]
    {x : {i // i ≠ i₀} → ℝ} :
    x ∈ dirichletChartRegion i₀ ↔ x default ∈ Ioo 0 1 := by
  rw [mem_dirichletChartRegion_iff, Unique.forall_iff, Fintype.sum_unique]
  rfl

/-- When `{i // i ≠ i₀}` has a unique index, the real Dirichlet chart density at `i₀` equals the
real Beta density with shapes `a default` and `a i₀`, for every real parameter vector `a`. -/
theorem dirichletChartPDFReal_of_unique (a : ι → ℝ) (i₀ : ι) [Unique {i // i ≠ i₀}]
    (x : {i // i ≠ i₀} → ℝ) :
    dirichletChartPDFReal a i₀ x =
      betaPDFReal (a (default : {i // i ≠ i₀})) (a i₀) (x default) := by
  by_cases hx : x ∈ dirichletChartRegion i₀
  · have hx' : 0 < x default ∧ x default < 1 := mem_dirichletChartRegion_of_unique_iff.mp hx
    rw [dirichletChartPDFReal_of_mem a hx, betaPDFReal, ite_eq_left hx',
      Fintype.sum_eq_add_sum_subtype_ne a i₀, Fintype.prod_eq_mul_prod_subtype_ne _ i₀,
      Fintype.sum_unique, Fintype.prod_unique, Fintype.prod_unique, Fintype.sum_unique,
      ProbabilityTheory.beta, one_div_div, add_comm (a i₀), mul_comm (Real.Gamma (a i₀))]
  · have hx' : ¬(0 < x default ∧ x default < 1) :=
      fun h ↦ hx (mem_dirichletChartRegion_of_unique_iff.mpr h)
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
    exact (dirichletChartPDF_of_unique a i₀ x).symm
  rw [dirichletMeasure_eq_map_withDensity_dirichletChartPDF ha i₀, ← hdens,
    Measure.map_map measurable_dirichletChart e.symm.measurable]
  rfl

omit [DecidableEq ι] in
/-- When `{i // i ≠ i₀}` has a unique index, for independent Gamma coordinates at a common positive
rate, the ratio of the retained coordinate to the total and the total itself have the product of a
Beta law and a Gamma law. -/
theorem map_div_add_sum_pi_gammaMeasure_of_unique {a : ι → ℝ} {r : ℝ}
    (ha : ∀ i, 0 < a i) (hr : 0 < r) (i₀ : ι) [Unique {i // i ≠ i₀}] :
    (Measure.pi fun i ↦ gammaMeasure (a i) r).map
        (fun x ↦ (x (default : {i // i ≠ i₀}) / (x (default : {i // i ≠ i₀}) + x i₀),
          x (default : {i // i ≠ i₀}) + x i₀)) =
      (betaMeasure (a (default : {i // i ≠ i₀})) (a i₀)).prod
        (gammaMeasure (a (default : {i // i ≠ i₀}) + a i₀) r) := by
  classical
  have _ : Nonempty ι := ⟨i₀⟩
  let j₀ : {i // i ≠ i₀} := default
  have hsum (y : ι → ℝ) : ∑ i, y i = y j₀ + y i₀ := by
    rw [Fintype.sum_eq_add_sum_subtype_ne y i₀, Fintype.sum_unique, add_comm]
  let _ := isProbabilityMeasure_gammaMeasure (add_pos (ha j₀) (ha i₀)) hr
  have h := congrArg (Measure.map (Prod.map (fun p : EuclideanSpace ℝ ι ↦ p j₀) id))
    (map_dirichletNormalize_sum_pi_gammaMeasure ha hr)
  rw [Measure.map_map (by fun_prop) (by fun_prop), hsum a,
    ← Measure.map_prod_map _ _ (by fun_prop) measurable_id, Measure.map_id,
    dirichletMeasure_eq_map_betaMeasure_of_unique ha i₀,
    Measure.map_map (by fun_prop) (by fun_prop)] at h
  have hid : ((fun p : EuclideanSpace ℝ ι ↦ p j₀) ∘ fun u ↦ dirichletChart i₀ (fun _ ↦ u)) = id :=
    funext fun u ↦ dirichletChart_apply_coe i₀ (fun _ ↦ u) j₀
  rw [hid, Measure.map_id] at h
  simpa only [Function.comp_def, Prod.map_apply, id_eq, dirichletNormalize_apply, hsum] using h

omit [DecidableEq ι] in
/-- When `{i // i ≠ i₀}` has a unique index, for independent Gamma coordinates at a common positive
rate, the ratio of the retained coordinate to the total has law `betaMeasure (a default) (a i₀)`. -/
theorem map_div_add_pi_gammaMeasure_of_unique {a : ι → ℝ} {r : ℝ}
    (ha : ∀ i, 0 < a i) (hr : 0 < r) (i₀ : ι) [Unique {i // i ≠ i₀}] :
    (Measure.pi fun i ↦ gammaMeasure (a i) r).map
        (fun x ↦ x (default : {i // i ≠ i₀}) / (x (default : {i // i ≠ i₀}) + x i₀)) =
      betaMeasure (a (default : {i // i ≠ i₀})) (a i₀) := by
  let j₀ : {i // i ≠ i₀} := default
  let _ := isProbabilityMeasure_gammaMeasure (add_pos (ha j₀) (ha i₀)) hr
  have h := congrArg (Measure.map Prod.fst) (map_div_add_sum_pi_gammaMeasure_of_unique ha hr i₀)
  rw [Measure.map_map measurable_fst (by fun_prop)] at h
  simpa only [Function.comp_def, Measure.map_fst_prod, measure_univ, one_smul] using h

end Unique

/-! ### Specialization to `Fin 2` -/

/-- Dropping coordinate `1` on `Fin 2` embeds the retained coordinate `x ⟨0, _⟩` into the simplex
hyperplane as `(x ⟨0, _⟩, 1 - x ⟨0, _⟩)`. -/
theorem dirichletChart_one_fin_two (x : {i : Fin 2 // i ≠ 1} → ℝ) :
    dirichletChart (1 : Fin 2) x =
      (EuclideanSpace.equiv (Fin 2) ℝ).symm ![x ⟨0, by decide⟩, 1 - x ⟨0, by decide⟩] := by
  let _ : Unique {i : Fin 2 // i ≠ 1} := ⟨⟨⟨0, by decide⟩⟩, by decide⟩
  ext i
  fin_cases i <;> simp
  rfl

/-- Dropping coordinate `0` on `Fin 2` embeds the retained coordinate `x ⟨1, _⟩` into the simplex
hyperplane as `(1 - x ⟨1, _⟩, x ⟨1, _⟩)`. -/
theorem dirichletChart_zero_fin_two (x : {i : Fin 2 // i ≠ 0} → ℝ) :
    dirichletChart (0 : Fin 2) x =
      (EuclideanSpace.equiv (Fin 2) ℝ).symm ![1 - x ⟨1, by decide⟩, x ⟨1, by decide⟩] := by
  let _ : Unique {i : Fin 2 // i ≠ 0} := ⟨⟨⟨1, by decide⟩⟩, by decide⟩
  ext i
  fin_cases i <;> simp
  rfl

/-- At dropped coordinate `1` on `Fin 2`, the chart region is `Ioo 0 1` in coordinate `0`. -/
theorem mem_dirichletChartRegion_one_fin_two_iff {x : {i : Fin 2 // i ≠ 1} → ℝ} :
    x ∈ dirichletChartRegion (1 : Fin 2) ↔ x ⟨0, by decide⟩ ∈ Ioo 0 1 := by
  let _ : Unique {i : Fin 2 // i ≠ 1} := ⟨⟨⟨0, by decide⟩⟩, by decide⟩
  exact mem_dirichletChartRegion_of_unique_iff

/-- At dropped coordinate `0` on `Fin 2`, the chart region is `Ioo 0 1` in coordinate `1`. -/
theorem mem_dirichletChartRegion_zero_fin_two_iff {x : {i : Fin 2 // i ≠ 0} → ℝ} :
    x ∈ dirichletChartRegion (0 : Fin 2) ↔ x ⟨1, by decide⟩ ∈ Ioo 0 1 := by
  let _ : Unique {i : Fin 2 // i ≠ 0} := ⟨⟨⟨1, by decide⟩⟩, by decide⟩
  exact mem_dirichletChartRegion_of_unique_iff

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

/-- The second coordinate of a `Fin 2` Dirichlet law with positive concentration parameters has law
`betaMeasure (a 1) (a 0)`. -/
theorem map_eval_one_dirichletMeasure_fin_two {a : Fin 2 → ℝ} (ha : ∀ i, 0 < a i) :
    (dirichletMeasure a).map (fun x ↦ x 1) = betaMeasure (a 1) (a 0) := by
  let _ : Unique {i : Fin 2 // i ≠ 0} := ⟨⟨⟨1, by decide⟩⟩, by decide⟩
  rw [dirichletMeasure_eq_map_betaMeasure_of_unique ha (0 : Fin 2),
    Measure.map_map (by fun_prop) (by fun_prop)]
  have hid : ((fun x : EuclideanSpace ℝ (Fin 2) ↦ x 1) ∘
      fun v ↦ dirichletChart (0 : Fin 2) (fun _ ↦ v)) = id :=
    funext fun v ↦ dirichletChart_apply_of_ne (0 : Fin 2) (fun _ ↦ v) (by decide)
  rw [hid, Measure.map_id]
  rfl

/-! ### Two-category Gamma–Dirichlet and Gamma–Beta factorizations -/

/-- For two independent Gamma coordinates on `Fin 2` with positive shapes and a common positive
rate, the ratio of the first coordinate to their sum and the sum itself have the product law
`betaMeasure (a 0) (a 1) ⊗ gammaMeasure (a 0 + a 1) r`. -/
theorem map_div_add_sum_pi_gammaMeasure_fin_two {a : Fin 2 → ℝ} {r : ℝ}
    (ha : ∀ i, 0 < a i) (hr : 0 < r) :
    (Measure.pi fun i : Fin 2 ↦ gammaMeasure (a i) r).map
        (fun x ↦ (x 0 / (x 0 + x 1), x 0 + x 1)) =
      (betaMeasure (a 0) (a 1)).prod (gammaMeasure (a 0 + a 1) r) := by
  let _ : Unique {i : Fin 2 // i ≠ 1} := ⟨⟨⟨0, by decide⟩⟩, by decide⟩
  exact map_div_add_sum_pi_gammaMeasure_of_unique ha hr (1 : Fin 2)

/-- For two independent Gamma coordinates on `Fin 2` with positive shapes and a common positive
rate, the ratio of the first coordinate to their sum has law `betaMeasure (a 0) (a 1)`. -/
theorem map_div_add_pi_gammaMeasure_fin_two {a : Fin 2 → ℝ} {r : ℝ}
    (ha : ∀ i, 0 < a i) (hr : 0 < r) :
    (Measure.pi fun i : Fin 2 ↦ gammaMeasure (a i) r).map
        (fun x ↦ x 0 / (x 0 + x 1)) =
      betaMeasure (a 0) (a 1) := by
  let _ : Unique {i : Fin 2 // i ≠ 1} := ⟨⟨⟨0, by decide⟩⟩, by decide⟩
  exact map_div_add_pi_gammaMeasure_of_unique ha hr (1 : Fin 2)

/-- For a binary product of Gamma laws with positive shapes and a common positive rate, normalizing
the pair and taking its sum produces the product of `dirichletMeasure ![a, b]` and
`gammaMeasure (a + b) r`. -/
theorem map_dirichletNormalize_add_prod_gammaMeasure {a b r : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hr : 0 < r) :
    ((gammaMeasure a r).prod (gammaMeasure b r)).map
        (fun z ↦ (dirichletNormalize ![z.1, z.2], z.1 + z.2)) =
      (dirichletMeasure ![a, b]).prod (gammaMeasure (a + b) r) := by
  let _ := isProbabilityMeasure_gammaMeasure ha hr
  let _ := isProbabilityMeasure_gammaMeasure hb hr
  have hab : ∀ i : Fin 2, 0 < ![a, b] i := Fin.forall_fin_two.2 ⟨ha, hb⟩
  have hvec : Measure.pi ![gammaMeasure a r, gammaMeasure b r] =
      Measure.pi fun i : Fin 2 ↦ gammaMeasure (![a, b] i) r := by
    congr 1
    funext i
    fin_cases i <;> rfl
  have hmp := measurePreserving_finTwoArrow_vec (gammaMeasure a r) (gammaMeasure b r)
  rw [← hmp.map_eq, hvec, Measure.map_map (by fun_prop) MeasurableEquiv.finTwoArrow.measurable]
  convert map_dirichletNormalize_sum_pi_gammaMeasure hab hr using 2
  · funext x
    have hx : ![x 0, x 1] = x := List.ofFn_inj.mp rfl
    simp [MeasurableEquiv.finTwoArrow, Fin.sum_univ_two, hx]
  · simp [Fin.sum_univ_two]

/-- Normalizing a pair drawn from the product of two Gamma laws with positive shapes and a common
positive rate produces `dirichletMeasure ![a, b]`. -/
theorem map_dirichletNormalize_prod_gammaMeasure {a b r : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hr : 0 < r) :
    ((gammaMeasure a r).prod (gammaMeasure b r)).map
        (fun z ↦ dirichletNormalize ![z.1, z.2]) =
      dirichletMeasure ![a, b] := by
  let _ := isProbabilityMeasure_gammaMeasure (add_pos ha hb) hr
  have h := congrArg (Measure.map Prod.fst) (map_dirichletNormalize_add_prod_gammaMeasure ha hb hr)
  rw [Measure.map_map measurable_fst (by fun_prop)] at h
  simpa only [Function.comp_def, Measure.map_fst_prod, measure_univ, one_smul] using h

end TauCeti.Probability

namespace ProbabilityTheory

open TauCeti.Probability

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- When `{i // i ≠ i₀}` has a unique index, embedding a Beta random variable `U` with positive
shapes `a default` and `a i₀` through `dirichletChart i₀` produces `dirichletMeasure a`. -/
theorem HasLaw.dirichletMeasure_of_unique {ι : Type*} [Fintype ι] [DecidableEq ι]
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
theorem HasLaw.dirichletMeasure_fin_two {U : Ω → ℝ} {a b : ℝ}
    (hU : HasLaw U (betaMeasure a b) P) (ha : 0 < a) (hb : 0 < b) :
    HasLaw (fun ω ↦ (EuclideanSpace.equiv (Fin 2) ℝ).symm ![U ω, 1 - U ω])
      (dirichletMeasure ![a, b]) P := by
  let _ : Unique {i : Fin 2 // i ≠ 1} := ⟨⟨⟨0, by decide⟩⟩, by decide⟩
  have hab : ∀ i : Fin 2, 0 < ![a, b] i := Fin.forall_fin_two.2 ⟨ha, hb⟩
  simpa only [dirichletChart_one_fin_two] using
    hU.dirichletMeasure_of_unique (a := ![a, b]) (i₀ := 1) hab

/-- For two independent Gamma random variables with positive shapes and a common positive rate,
their normalized vector and their sum have the joint Dirichlet–Gamma product law. -/
theorem IndepFun.hasLaw_dirichletNormalize_add_prod_gammaMeasure {X Y : Ω → ℝ} {a b r : ℝ}
    (hXY : IndepFun X Y P) (hX : HasLaw X (gammaMeasure a r) P)
    (hY : HasLaw Y (gammaMeasure b r) P) (ha : 0 < a) (hb : 0 < b) (hr : 0 < r) :
    HasLaw (fun ω ↦ (dirichletNormalize ![X ω, Y ω], X ω + Y ω))
      ((dirichletMeasure ![a, b]).prod (gammaMeasure (a + b) r)) P := by
  let _ := isProbabilityMeasure_gammaMeasure ha hr
  let _ := isProbabilityMeasure_gammaMeasure hb hr
  let _ : IsProbabilityMeasure P := hX.isProbabilityMeasure
  have hmap : HasLaw (fun z : ℝ × ℝ ↦ (dirichletNormalize ![z.1, z.2], z.1 + z.2))
      ((dirichletMeasure ![a, b]).prod (gammaMeasure (a + b) r))
      ((gammaMeasure a r).prod (gammaMeasure b r)) :=
    ⟨(by fun_prop : Measurable _).aemeasurable,
      map_dirichletNormalize_add_prod_gammaMeasure ha hb hr⟩
  exact hmap.fun_comp (hXY.hasLaw_prod hX hY)

/-- Normalizing two independent Gamma random variables with positive shapes and a common positive
rate gives `dirichletMeasure ![a, b]`. -/
theorem IndepFun.hasLaw_dirichletNormalize_gammaMeasure {X Y : Ω → ℝ} {a b r : ℝ}
    (hXY : IndepFun X Y P) (hX : HasLaw X (gammaMeasure a r) P)
    (hY : HasLaw Y (gammaMeasure b r) P) (ha : 0 < a) (hb : 0 < b) (hr : 0 < r) :
    HasLaw (fun ω ↦ dirichletNormalize ![X ω, Y ω]) (dirichletMeasure ![a, b]) P := by
  let _ := isProbabilityMeasure_gammaMeasure ha hr
  let _ := isProbabilityMeasure_gammaMeasure hb hr
  let _ : IsProbabilityMeasure P := hX.isProbabilityMeasure
  have hmap : HasLaw (fun z : ℝ × ℝ ↦ dirichletNormalize ![z.1, z.2])
      (dirichletMeasure ![a, b]) ((gammaMeasure a r).prod (gammaMeasure b r)) :=
    ⟨(by fun_prop : Measurable _).aemeasurable,
      map_dirichletNormalize_prod_gammaMeasure ha hb hr⟩
  exact hmap.fun_comp (hXY.hasLaw_prod hX hY)

/-- The normalized vector of two independent Gamma random variables with positive shapes and a
common positive rate is independent of their sum. -/
theorem IndepFun.indepFun_dirichletNormalize_add_of_hasLaw_gammaMeasure {X Y : Ω → ℝ} {a b r : ℝ}
    (hXY : IndepFun X Y P) (hX : HasLaw X (gammaMeasure a r) P)
    (hY : HasLaw Y (gammaMeasure b r) P) (ha : 0 < a) (hb : 0 < b) (hr : 0 < r) :
    IndepFun (fun ω ↦ dirichletNormalize ![X ω, Y ω]) (fun ω ↦ X ω + Y ω) P := by
  have hab : ∀ i : Fin 2, 0 < ![a, b] i := Fin.forall_fin_two.2 ⟨ha, hb⟩
  let _ := isProbabilityMeasure_gammaMeasure ha hr
  let _ := isProbabilityMeasure_dirichletMeasure hab
  let _ := isProbabilityMeasure_gammaMeasure (add_pos ha hb) hr
  let _ : IsProbabilityMeasure P := hX.isProbabilityMeasure
  have hjoint := hXY.hasLaw_dirichletNormalize_add_prod_gammaMeasure hX hY ha hb hr
  have hnorm := hXY.hasLaw_dirichletNormalize_gammaMeasure hX hY ha hb hr
  have hsum : HasLaw (fun ω ↦ X ω + Y ω) (gammaMeasure (a + b) r) P := by
    have hsnd : HasLaw Prod.snd (gammaMeasure (a + b) r)
        ((dirichletMeasure ![a, b]).prod (gammaMeasure (a + b) r)) :=
      MeasureTheory.measurePreserving_snd.hasLaw
    simpa only [Function.comp_def] using hsnd.fun_comp hjoint
  exact (indepFun_iff_hasLaw_prodMk_prod hnorm hsum).2 hjoint

end ProbabilityTheory
