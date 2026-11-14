/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.WithLp
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import TauCeti.Probability.Distributions.LogisticNormal.Basic

/-!
# The logistic chart as a smooth equivalence onto the open simplex

The logistic chart `logisticNormalChart r` sends log ratios `z` to the normalized exponentials
`(e^{z'ᵢ} / ∑ⱼ e^{z'ⱼ})ᵢ`, where `z'` extends `z` by `z'ᵣ = 0`. Its inverse on the strictly
positive simplex is the additive log-ratio map `x ↦ (log (xᵢ / xᵣ))_{i ≠ r}`.

This file shows that the two maps are smooth inverse charts: the logistic chart is smooth of
every order (including analytic) on the whole log-ratio space, the additive log-ratio map is
smooth of every order on the open set of vectors with nonzero coordinates, which contains the open
simplex, and together they form a homeomorphism from the log-ratio space onto the open simplex
`{x | (∀ i, 0 < x i) ∧ ∑ i, x i = 1}`. Both smoothness statements are in the ambient Euclidean
space, so they apply to the simplex as a subset of its affine hyperplane.

## Main declarations

* `TauCeti.Probability.contDiff_logisticNormalChart`: the logistic chart is smooth.
* `TauCeti.Probability.contDiffOn_logisticNormalLogRatio`: the additive log-ratio map is smooth
  on vectors with nonzero coordinates.
* `TauCeti.Probability.logisticNormalChartHomeomorph`: the logistic chart as a homeomorphism onto
  the open simplex, with the additive log-ratio map as inverse.

## References

* J. Aitchison and S. M. Shen, *Logistic-normal distributions: Some properties and uses*,
  Biometrika 67(2), 261–272, 1980.
-/

public section

noncomputable section

open Set

namespace TauCeti.Probability

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The logistic chart is smooth.** It is `C^n` for every `n`, including real-analytic. -/
@[fun_prop]
theorem contDiff_logisticNormalChart (r : ι) {n : WithTop ℕ∞} :
    ContDiff ℝ n (logisticNormalChart r) := by
  have hD : ∀ z : EuclideanSpace ℝ {i // i ≠ r}, 1 + ∑ j, Real.exp (z j) ≠ 0 :=
    fun z ↦ by positivity
  have hden : ContDiff ℝ n fun z : EuclideanSpace ℝ {i // i ≠ r} ↦ 1 + ∑ j, Real.exp (z j) :=
    contDiff_const.add (ContDiff.sum fun j _ ↦ Real.contDiff_exp.comp (contDiff_piLp_apply _))
  refine contDiff_piLp' _ fun i ↦ ?_
  simp_rw [logisticNormalChart_apply, Equiv.funSplitAt_symm_apply]
  split_ifs with hi
  · exact contDiff_const.div hden hD
  · exact (Real.contDiff_exp.comp (contDiff_piLp_apply _)).div hden hD

/-- The additive log-ratio map is smooth of every order, including real-analytic, at every
vector whose coordinates are all nonzero. -/
theorem contDiffAt_logisticNormalLogRatio (r : ι) {n : WithTop ℕ∞} {x : EuclideanSpace ℝ ι}
    (hx : ∀ i, x i ≠ 0) : ContDiffAt ℝ n (logisticNormalLogRatio r) x := by
  have hcoord (i : ι) : ContDiffAt ℝ n (fun y : EuclideanSpace ℝ ι ↦ y i) x :=
    contDiffAt_piLp_apply 2
  refine contDiffAt_piLp' _ fun j ↦ ?_
  simp only [logisticNormalLogRatio_apply]
  exact ((hcoord j).div (hcoord r) (hx r)).log (div_ne_zero (hx j) (hx r))

/-- **The additive log-ratio map is smooth** of every order, including real-analytic, on the
vectors whose coordinates are all nonzero. This open set contains the open simplex. -/
theorem contDiffOn_logisticNormalLogRatio (r : ι) {n : WithTop ℕ∞} :
    ContDiffOn ℝ n (logisticNormalLogRatio r) {x : EuclideanSpace ℝ ι | ∀ i, x i ≠ 0} :=
  fun _ hx ↦ (contDiffAt_logisticNormalLogRatio r hx).contDiffWithinAt

/-- **The logistic chart as a homeomorphism onto the open simplex.** The forward map is
`logisticNormalChart r` and the inverse is the additive log-ratio map `logisticNormalLogRatio r`;
both are smooth in the ambient Euclidean space by `contDiff_logisticNormalChart` and
`contDiffOn_logisticNormalLogRatio`. -/
def logisticNormalChartHomeomorph (r : ι) :
    EuclideanSpace ℝ {i // i ≠ r} ≃ₜ
      {x : EuclideanSpace ℝ ι // (∀ i, 0 < x i) ∧ ∑ i, x i = 1} where
  toFun z := ⟨logisticNormalChart r z, logisticNormalChart_pos r z, sum_logisticNormalChart r z⟩
  invFun x := logisticNormalLogRatio r x
  left_inv := logisticNormalLogRatio_chart r
  right_inv x := Subtype.ext (logisticNormalChart_logRatio r x.2.1 x.2.2)
  continuous_toFun := (continuous_logisticNormalChart r).subtype_mk _
  continuous_invFun := by
    refine (contDiffOn_logisticNormalLogRatio r (n := 0)).continuousOn.comp_continuous
      continuous_subtype_val fun x ↦ ?_
    exact fun i ↦ (x.2.1 i).ne'

/-- The logistic-chart homeomorphism is the logistic chart. -/
@[simp]
theorem coe_logisticNormalChartHomeomorph_apply (r : ι) (z : EuclideanSpace ℝ {i // i ≠ r}) :
    (logisticNormalChartHomeomorph r z : EuclideanSpace ℝ ι) = logisticNormalChart r z := (rfl)

/-- The inverse of the logistic-chart homeomorphism takes additive log ratios. -/
@[simp]
theorem logisticNormalChartHomeomorph_symm_apply (r : ι)
    (x : {x : EuclideanSpace ℝ ι // (∀ i, 0 < x i) ∧ ∑ i, x i = 1}) :
    (logisticNormalChartHomeomorph r).symm x = logisticNormalLogRatio r x := (rfl)

end TauCeti.Probability
