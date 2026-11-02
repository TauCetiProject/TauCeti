/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Dirichlet.Basic
public import TauCeti.Probability.Distributions.Gamma.Beta
public import TauCeti.Probability.Distributions.Gamma.Sum

/-!
# Block marginals of the Dirichlet distribution

A Dirichlet vector is a vector of independent unit-rate Gamma variables divided by its own total.
The total of a block `s` of its coordinates is therefore the total of the corresponding Gamma
variables divided by the sum of that total and the total of the remaining, independent, Gamma
variables.  Both totals are again Gamma with the summed shapes, so the Gamma--Beta change of
variables identifies the block total as a Beta variable whose first parameter is the total
concentration of the block and whose second parameter is the total concentration of its
complement.

Both the block and its complement must be nonempty for the two Beta parameters to be positive.  A
single coordinate is the case `s = {i}`, which needs at least two indices; the remaining case of a
one-element index type, where the Dirichlet law is a Dirac mass, is
`TauCeti.Probability.dirichletMeasure_eq_dirac_of_card_eq_one`.

## Main results

* `TauCeti.Probability.map_sum_dirichletMeasure` — the total of a block of coordinates is a Beta
  law.
* `TauCeti.Probability.map_eval_dirichletMeasure` — a coordinate marginal is a Beta law.
* `TauCeti.Probability.map_eval_zero_dirichletMeasure_fin_two` — the two-parameter case, where the
  first coordinate carries the Beta law of the two concentration parameters themselves.

## References

* N. L. Johnson, S. Kotz, N. Balakrishnan, *Continuous Multivariate Distributions*, vol. 1,
  2nd ed., Wiley, 2000, Chapter 49.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory

namespace TauCeti

namespace Probability

variable {ι : Type*} [Fintype ι]

/-- Under a positive concentration vector, the total of a block of Dirichlet coordinates is the
total of the corresponding Gamma variables divided by the total of all of them. -/
private theorem map_sum_dirichletMeasure_eq [Nonempty ι] {a : ι → ℝ} (ha : ∀ i, 0 < a i)
    (s : Finset ι) :
    (dirichletMeasure a).map (fun x ↦ ∑ i ∈ s, x i) =
      (Measure.pi fun j ↦ gammaMeasure (a j) 1).map fun x ↦ (∑ i ∈ s, x i) / ∑ j, x j := by
  rw [dirichletMeasure_of_pos ha, Measure.map_map (by fun_prop) measurable_dirichletNormalize]
  simp only [Function.comp_def, dirichletNormalize_apply, ← Finset.sum_div]

/-- Under a Dirichlet law with positive concentration parameters, the total of a block of
coordinates has the Beta law whose first parameter is the total concentration of the block and
whose second parameter is the total concentration of the complementary block. -/
theorem map_sum_dirichletMeasure [DecidableEq ι] {a : ι → ℝ} (ha : ∀ i, 0 < a i) {s : Finset ι}
    (hs : s.Nonempty) (hsc : sᶜ.Nonempty) :
    (dirichletMeasure a).map (fun x ↦ ∑ i ∈ s, x i) =
      betaMeasure (∑ i ∈ s, a i) (∑ i ∈ sᶜ, a i) := by
  have : Nonempty ι := ⟨hs.choose⟩
  have _ : ∀ j, IsProbabilityMeasure (gammaMeasure (a j) 1) :=
    fun j ↦ isProbabilityMeasure_gammaMeasure (ha j) one_pos
  have hlaw : ∀ j, HasLaw (fun x : ι → ℝ ↦ x j) (gammaMeasure (a j) 1)
      (Measure.pi fun k ↦ gammaMeasure (a k) 1) :=
    fun j ↦ (measurePreserving_eval (fun k ↦ gammaMeasure (a k) 1) j).hasLaw
  have hindep : iIndepFun (fun (j : ι) (x : ι → ℝ) ↦ x j)
      (Measure.pi fun k ↦ gammaMeasure (a k) 1) :=
    iIndepFun_pi (X := fun _ ↦ id) fun _ ↦ aemeasurable_id
  have hspos : 0 < ∑ i ∈ s, a i := Finset.sum_pos (fun j _ ↦ ha j) hs
  have hscpos : 0 < ∑ i ∈ sᶜ, a i := Finset.sum_pos (fun j _ ↦ ha j) hsc
  have hblock : HasLaw (fun x : ι → ℝ ↦ ∑ i ∈ s, x i) (gammaMeasure (∑ i ∈ s, a i) 1)
      (Measure.pi fun k ↦ gammaMeasure (a k) 1) :=
    hindep.hasLaw_sum_gammaMeasure one_pos hs (fun j _ ↦ ha j) fun j _ ↦ hlaw j
  have hrest : HasLaw (fun x : ι → ℝ ↦ ∑ i ∈ sᶜ, x i) (gammaMeasure (∑ i ∈ sᶜ, a i) 1)
      (Measure.pi fun k ↦ gammaMeasure (a k) 1) :=
    hindep.hasLaw_sum_gammaMeasure one_pos hsc (fun j _ ↦ ha j) fun j _ ↦ hlaw j
  have hpair : IndepFun (fun x : ι → ℝ ↦ ∑ i ∈ s, x i) (fun x ↦ ∑ i ∈ sᶜ, x i)
      (Measure.pi fun k ↦ gammaMeasure (a k) 1) := by
    have h := (hindep.indepFun_finset s sᶜ disjoint_compl_right fun j ↦ measurable_pi_apply j).comp
      (Finset.measurable_sum (f := fun (i : s) (y : s → ℝ) ↦ y i) Finset.univ
        fun i _ ↦ measurable_pi_apply i)
      (Finset.measurable_sum (f := fun (i : ↥sᶜ) (y : ↥sᶜ → ℝ) ↦ y i) Finset.univ
        fun i _ ↦ measurable_pi_apply i)
    simpa only [Function.comp_def, Finset.sum_coe_sort] using h
  have hbeta := hasLaw_div_add_gammaMeasure_of_indepFun hspos hscpos one_pos hpair hblock hrest
  rw [map_sum_dirichletMeasure_eq ha s, ← hbeta.map_eq]
  refine Measure.map_congr (.of_forall fun x ↦ ?_)
  exact congrArg ((∑ i ∈ s, x i) / ·) (Finset.sum_add_sum_compl s x).symm

/-- Under a Dirichlet law with positive concentration parameters, a coordinate has the Beta law
whose first parameter is that coordinate's concentration parameter and whose second parameter is
the total of the remaining ones. -/
theorem map_eval_dirichletMeasure [DecidableEq ι] [Nontrivial ι] {a : ι → ℝ} (ha : ∀ i, 0 < a i)
    (i : ι) :
    (dirichletMeasure a).map (fun x ↦ x i) =
      betaMeasure (a i) (∑ j with j ≠ i, a j) := by
  have hsc : ({i} : Finset ι)ᶜ.Nonempty := by
    obtain ⟨j, hj⟩ := exists_ne i
    exact ⟨j, by simpa using hj⟩
  have h := map_sum_dirichletMeasure ha (s := {i}) ⟨i, Finset.mem_singleton_self i⟩ hsc
  simpa only [Finset.sum_singleton, Finset.compl_singleton, Finset.filter_ne'] using h

/-- The `Fin 2` Dirichlet law has the Beta law of the same two parameters as its first
coordinate. -/
theorem map_eval_zero_dirichletMeasure_fin_two {a : Fin 2 → ℝ} (ha : ∀ i, 0 < a i) :
    (dirichletMeasure a).map (fun x ↦ x 0) = betaMeasure (a 0) (a 1) := by
  have herase : Finset.univ.erase (0 : Fin 2) = {1} := by decide
  rw [map_eval_dirichletMeasure ha 0, Finset.filter_ne', herase, Finset.sum_singleton]

end Probability

end TauCeti
