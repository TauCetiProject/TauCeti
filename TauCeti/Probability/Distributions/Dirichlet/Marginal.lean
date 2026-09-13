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
# Coordinate marginals of the Dirichlet distribution

A Dirichlet vector is a vector of independent unit-rate Gamma variables divided by its own total.
Its `i`th coordinate is therefore one Gamma variable divided by the sum of itself and the total of
the remaining, independent, Gamma variables.  That total is again Gamma with the summed shape, so
the Gamma--Beta change of variables identifies the coordinate as a Beta variable whose first
parameter is `a i` and whose second parameter is the total of the other concentration parameters.

Two indices are needed for the second Beta parameter to be positive.  The remaining case of a
one-element index type, where the Dirichlet law is a Dirac mass, is
`TauCeti.Probability.dirichletMeasure_eq_dirac_of_card_eq_one`.

## Main results

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

/-- Under a positive concentration vector, a Dirichlet coordinate is the ratio of its own Gamma
variable to the total of all of them. -/
private theorem map_eval_dirichletMeasure_eq [Nonempty ι] {a : ι → ℝ} (ha : ∀ i, 0 < a i)
    (i : ι) :
    (dirichletMeasure a).map (fun x ↦ x i) =
      (Measure.pi fun j ↦ gammaMeasure (a j) 1).map (fun x ↦ x i / ∑ j, x j) := by
  rw [dirichletMeasure_of_pos ha, Measure.map_map (by fun_prop) measurable_dirichletNormalize]
  simp only [Function.comp_def, dirichletNormalize_apply]

/-- Under a Dirichlet law with positive concentration parameters, a coordinate has the Beta law
whose first parameter is that coordinate's concentration parameter and whose second parameter is
the total of the remaining ones. -/
theorem map_eval_dirichletMeasure [DecidableEq ι] [Nontrivial ι] {a : ι → ℝ} (ha : ∀ i, 0 < a i)
    (i : ι) :
    (dirichletMeasure a).map (fun x ↦ x i) =
      betaMeasure (a i) (∑ j with j ≠ i, a j) := by
  rw [Finset.filter_ne']
  have _ : ∀ j, IsProbabilityMeasure (gammaMeasure (a j) 1) :=
    fun j ↦ isProbabilityMeasure_gammaMeasure (ha j) one_pos
  have hlaw : ∀ j, HasLaw (fun x : ι → ℝ ↦ x j) (gammaMeasure (a j) 1)
      (Measure.pi fun k ↦ gammaMeasure (a k) 1) :=
    fun j ↦ (measurePreserving_eval (fun k ↦ gammaMeasure (a k) 1) j).hasLaw
  have hindep : iIndepFun (fun (j : ι) (x : ι → ℝ) ↦ x j)
      (Measure.pi fun k ↦ gammaMeasure (a k) 1) :=
    iIndepFun_pi (X := fun _ ↦ id) fun _ ↦ aemeasurable_id
  have hs : (Finset.univ.erase i).Nonempty := by
    obtain ⟨j, hj⟩ := exists_ne i
    exact ⟨j, Finset.mem_erase.2 ⟨hj, Finset.mem_univ j⟩⟩
  have hspos : 0 < ∑ j ∈ Finset.univ.erase i, a j := Finset.sum_pos (fun j _ ↦ ha j) hs
  have hrest : HasLaw (fun x : ι → ℝ ↦ ∑ j ∈ Finset.univ.erase i, x j)
      (gammaMeasure (∑ j ∈ Finset.univ.erase i, a j) 1)
      (Measure.pi fun k ↦ gammaMeasure (a k) 1) :=
    iIndepFun.hasLaw_sum_gammaMeasure hindep one_pos hs (fun j _ ↦ ha j) fun j _ ↦ hlaw j
  have hpair : IndepFun (fun x : ι → ℝ ↦ x i) (fun x ↦ ∑ j ∈ Finset.univ.erase i, x j)
      (Measure.pi fun k ↦ gammaMeasure (a k) 1) := by
    have hsplit : (∑ j ∈ Finset.univ.erase i, fun x : ι → ℝ ↦ x j) =
        fun x ↦ ∑ j ∈ Finset.univ.erase i, x j :=
      funext fun x ↦ Finset.sum_apply x _ _
    have h := (hindep.indepFun_finsetSum_of_notMem₀ (fun j ↦ (hlaw j).aemeasurable)
      (Finset.notMem_erase i Finset.univ)).symm
    rwa [hsplit] at h
  have hbeta := hasLaw_div_add_gammaMeasure_of_indepFun (ha i) hspos one_pos hpair (hlaw i) hrest
  rw [map_eval_dirichletMeasure_eq ha i, ← hbeta.map_eq]
  refine Measure.map_congr (.of_forall fun x ↦ ?_)
  exact congrArg (x i / ·) (Finset.add_sum_erase _ _ (Finset.mem_univ i)).symm

/-- The `Fin 2` Dirichlet law has the Beta law of the same two parameters as its first
coordinate. -/
theorem map_eval_zero_dirichletMeasure_fin_two {a : Fin 2 → ℝ} (ha : ∀ i, 0 < a i) :
    (dirichletMeasure a).map (fun x ↦ x 0) = betaMeasure (a 0) (a 1) := by
  have herase : Finset.univ.erase (0 : Fin 2) = {1} := by decide
  rw [map_eval_dirichletMeasure ha 0, Finset.filter_ne', herase, Finset.sum_singleton]

end Probability

end TauCeti
