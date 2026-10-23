/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Hyperexponential.Basic
import TauCeti.Geometry.Convex.ConvexSpace.Defs
import TauCeti.Probability.Distributions.Gamma.Basic

/-!
# Operations on hyperexponential laws

Hyperexponential mixtures can be regrouped by adding the weights of components with equal
rates. The regrouping identity also covers reindexing and insertion or deletion of zero-weight
components, and holds even when an active rate is invalid. Positive scaling divides the rates.

An independent categorical variable and a rate-one exponential variable construct the mixture:
divide the exponential variable by the rate selected by the category. Zero-weight categories
may have arbitrary rates, since they are selected with probability zero.

The constructions use `map_categoricalMeasure`, `hyperexponentialMeasure_eq_bind`, and
`gammaMeasure_map_const_mul` (specialized to exponential laws).

## References

* S. Asmussen, *Applied Probability and Queues*, 2nd ed., Springer (2003), Chapter III, §4.
-/

public section

noncomputable section

open Convexity MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace TauCeti.Probability

variable {ι κ : Type*} [Fintype ι] [Fintype κ]
variable {p : StdSimplex ℝ≥0 ι} {r : ι → ℝ}

/-- Regrouping components adds their weights. Rates need agree only on active components;
neither surjectivity of the grouping map nor positivity of the rates is required.
For an injective grouping map this inserts zero-weight components, with arbitrary rates. -/
theorem hyperexponentialMeasure_map (f : ι → κ) {s : κ → ℝ}
    (h : ∀ i, 0 < p.weights i → r i = s (f i)) :
    hyperexponentialMeasure (p.map f) s = hyperexponentialMeasure p r := by
  classical
  let : MeasurableSpace ι := ⊤
  let : MeasurableSpace κ := ⊤
  have hvalid : (∀ j, 0 < (p.map f).weights j → 0 < s j) ↔
      ∀ i, 0 < p.weights i → 0 < r i := by
    simp only [StdSimplex.weights_map_apply, Finset.sum_pos_iff, Finset.mem_filter,
      Finset.mem_univ, true_and]
    constructor
    · intro hs i hi
      rw [h i hi]
      exact hs (f i) ⟨i, rfl, hi⟩
    · rintro hr j ⟨i, rfl, hi⟩
      rw [← h i hi]
      exact hr i hi
  by_cases hr : ∀ i, 0 < p.weights i → 0 < r i
  · rw [hyperexponentialMeasure_eq_bind (hvalid.mpr hr), ← map_categoricalMeasure,
      Measure.bind_map (by fun_prop) (measurable_of_finite _).aemeasurable,
      ← hyperexponentialMeasure_eq_bind (fun i hi ↦ by rw [← h i hi]; exact hr i hi)]
    exact hyperexponentialMeasure_congr (fun i hi ↦ (h i hi).symm)
  · rw [hyperexponentialMeasure_of_not_pos hr,
      hyperexponentialMeasure_of_not_pos (mt hvalid.mp hr)]

/-- Relabeling a hyperexponential mixture along an equivalence preserves its law. -/
@[simp]
theorem hyperexponentialMeasure_reindex (p : StdSimplex ℝ≥0 ι) (r : ι → ℝ) (e : ι ≃ κ) :
    hyperexponentialMeasure (p.map e) (r ∘ e.symm) = hyperexponentialMeasure p r := by
  exact hyperexponentialMeasure_map e (fun i _ ↦ by simp)

/-- Multiplication by a positive constant divides every active rate by that constant.
The identity also holds on the invalid zero-measure branch. -/
@[simp]
theorem map_mul_hyperexponentialMeasure {c : ℝ} (hc : 0 < c) :
    (hyperexponentialMeasure p r).map (c * ·) =
      hyperexponentialMeasure p (fun i ↦ r i / c) := by
  by_cases hr : ∀ i, 0 < p.weights i → 0 < r i
  · rw [hyperexponentialMeasure_of_pos hr,
      hyperexponentialMeasure_of_pos (fun i hi ↦ div_pos (hr i hi) hc),
      Measure.map_finset_sum (by fun_prop)]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : p.weights i = 0
    · simp [hi]
    · rw [Measure.map_smul _ (by fun_prop)]
      congr 1
      simpa only [expMeasure] using
        gammaMeasure_map_const_mul one_pos (hr i (pos_iff_ne_zero.mpr hi)) hc
  · have hscale : ¬ ∀ i, 0 < p.weights i → 0 < r i / c := by
      simpa only [div_pos_iff_of_pos_right hc] using hr
    simp [hyperexponentialMeasure_of_not_pos hr,
      hyperexponentialMeasure_of_not_pos hscale]

section Construction

variable [MeasurableSpace ι] [MeasurableSingletonClass ι]

/-- Select a rate categorically and divide an independent rate-one exponential by it.
Inactive rates may be zero or negative. -/
@[simp]
theorem map_div_prod_categoricalMeasure_expMeasure
    (hr : ∀ i, 0 < p.weights i → 0 < r i) :
    ((categoricalMeasure p).prod (expMeasure 1)).map (fun z ↦ z.2 / r z.1) =
      hyperexponentialMeasure p r := by
  let _ := isProbabilityMeasure_expMeasure one_pos
  have hmeas : Measurable (fun z : ι × ℝ ↦ z.2 / r z.1) :=
    measurable_snd.div ((measurable_of_finite r).comp measurable_fst)
  rw [Measure.prod_eq_of_sfinite,
    Measure.map_bind Measurable.map_prodMk_left.aemeasurable hmeas.aemeasurable,
    hyperexponentialMeasure_eq_bind hr]
  apply Measure.bind_congr_right
  apply ae_iff_of_countable.mpr
  intro i hi
  have hri : 0 < r i := hr i (pos_iff_ne_zero.mpr (by simpa using hi))
  dsimp only
  rw [Measure.map_map hmeas measurable_prodMk_left]
  have hscale := gammaMeasure_map_const_mul one_pos one_pos (inv_pos.mpr hri)
  simpa only [Function.comp_def, expMeasure, one_div, inv_inv, div_eq_mul_inv,
    mul_comm, mul_one] using hscale

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
variable {I : Ω → ι} {E : Ω → ℝ}

/-- Independent categorical and rate-one exponential variables construct a hyperexponential
variable by dividing the exponential by the selected rate. -/
theorem hasLaw_hyperexponentialMeasure_of_indepFun
    (hr : ∀ i, 0 < p.weights i → 0 < r i)
    (hI : HasLaw I (categoricalMeasure p) P) (hE : HasLaw E (expMeasure 1) P)
    (hindep : IndepFun I E P) :
    HasLaw (fun ω ↦ E ω / r (I ω)) (hyperexponentialMeasure p r) P := by
  let _ := hI.isProbabilityMeasure
  have hmeas : Measurable (fun z : ι × ℝ ↦ z.2 / r z.1) :=
    measurable_snd.div ((measurable_of_finite r).comp measurable_fst)
  have hlaw := (hasLaw_map hmeas.aemeasurable).comp (hindep.hasLaw_prod hI hE)
  rw [map_div_prod_categoricalMeasure_expMeasure hr] at hlaw
  exact hlaw

end Construction

/-- Scaling a hyperexponential variable by a positive constant divides its rates. -/
theorem hasLaw_mul_hyperexponentialMeasure {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {X : Ω → ℝ} {c : ℝ}
    (hX : HasLaw X (hyperexponentialMeasure p r) P) (hc : 0 < c) :
    HasLaw (fun ω ↦ c * X ω) (hyperexponentialMeasure p (fun i ↦ r i / c)) P := by
  have hlaw := (hasLaw_map (measurable_const_mul c).aemeasurable).comp hX
  rwa [map_mul_hyperexponentialMeasure hc] at hlaw

end TauCeti.Probability
