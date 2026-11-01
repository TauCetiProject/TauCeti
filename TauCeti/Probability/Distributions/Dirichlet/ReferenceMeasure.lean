/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.Dirichlet.Density
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Reference measure on the simplex hyperplane

Deleting any one coordinate identifies the hyperplane of vectors with coordinate sum one
with a product of real lines. The resulting pushforward of product Lebesgue measure does
not depend on the deleted coordinate. Thus densities on this hyperplane, such as those of
Dirichlet and logistic-normal laws, can be compared across reference categories.

`dirichletChartChange` is the transition between deleted-coordinate charts. After reindexing
by the transposition of two distinct reference categories, its derivative is the identity
matrix with one row replaced by minus one. Keeping the reference gives the identity map.
Its absolute determinant is one, so the transition preserves product volume. The statements
include a single category, where the coordinate
space has dimension zero and the reference measure is a point mass.

## References

* J. Aitchison and S. M. Shen, *Logistic-normal distributions: Some properties and uses*,
  Biometrika 67(2), 261–272, 1980.
-/

public section

noncomputable section

open MeasureTheory Set

namespace TauCeti.Probability

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Change the deleted coordinate from `r` to `s` on the simplex hyperplane. -/
def dirichletChartChange (r s : ι) (x : {i // i ≠ r} → ℝ) : {i // i ≠ s} → ℝ :=
  fun j ↦ dirichletChart r x j

/-- A chart transition reads the retained coordinates of the reconstructed point. -/
@[simp]
theorem dirichletChartChange_apply (r s : ι) (x : {i // i ≠ r} → ℝ)
    (j : {i // i ≠ s}) : dirichletChartChange r s x j = dirichletChart r x j := (rfl)

/-- Reconstructing after a chart transition gives the same point of the hyperplane. -/
@[simp]
theorem dirichletChart_dirichletChartChange (r s : ι) (x : {i // i ≠ r} → ℝ) :
    dirichletChart s (dirichletChartChange r s x) = dirichletChart r x :=
  (dirichletChart_eq_self_iff s _).2 (sum_dirichletChart r x)

/-- Keeping the reference coordinate gives the identity transition. -/
@[simp]
theorem dirichletChartChange_self (r : ι) (x : {i // i ≠ r} → ℝ) :
    dirichletChartChange r r x = x := by
  ext j
  simp

/-- Successive changes of deleted coordinate compose. In particular, reversing a transition
is its inverse. -/
@[simp]
theorem dirichletChartChange_dirichletChartChange (r s t : ι) (x : {i // i ≠ r} → ℝ) :
    dirichletChartChange s t (dirichletChartChange r s x) = dirichletChartChange r t x := by
  ext j
  simp

/-- Chart transitions are continuous on the whole coordinate space. -/
@[fun_prop]
theorem continuous_dirichletChartChange (r s : ι) : Continuous (dirichletChartChange r s) := by
  unfold dirichletChartChange
  fun_prop

/-- Chart transitions are measurable. -/
@[fun_prop]
theorem measurable_dirichletChartChange (r s : ι) : Measurable (dirichletChartChange r s) :=
  (continuous_dirichletChartChange r s).measurable

private theorem dirichletChart_swap_eq_affine (r s : ι) :
    ∃ (L : ({i // i ≠ r} → ℝ) →L[ℝ] ({i // i ≠ r} → ℝ))
      (c : {i // i ≠ r} → ℝ),
      (fun (x : {i // i ≠ r} → ℝ) (j : {i // i ≠ r}) ↦
        dirichletChart r x (Equiv.swap r s j)) = (fun x ↦ c + L x) ∧
      |LinearMap.det L.toLinearMap| = 1 := by
  by_cases hrs : s = r
  · subst s
    refine ⟨ContinuousLinearMap.id ℝ _, 0, ?_, by simp⟩
    ext x j
    simp
  let k : {i // i ≠ r} := ⟨s, hrs⟩
  let M : Matrix {i // i ≠ r} {i // i ≠ r} ℝ :=
    (1 : Matrix {i // i ≠ r} {i // i ≠ r} ℝ).updateRow k (-1)
  have hdet : M.det = -1 := by
    have hrow : (∑ j : {i // i ≠ r}, (-1 : ℝ) • (1 : Matrix {i // i ≠ r} {i // i ≠ r} ℝ) j) =
        (-1 : {i // i ≠ r} → ℝ) := by
      ext j
      simp [Finset.sum_apply, Matrix.one_apply]
    simpa only [Pi.neg_apply, Pi.one_apply, hrow, Matrix.det_one, smul_eq_mul, mul_one] using
      Matrix.det_updateRow_sum (1 : Matrix {i // i ≠ r} {i // i ≠ r} ℝ) k (-1)
  let L := (Matrix.toLin' M).toContinuousLinearMap
  have hL (x : {i // i ≠ r} → ℝ) : L x = Function.update x k (-∑ j, x j) := by
    simp [L, M, Matrix.toLin'_apply, Matrix.updateRow_mulVec, neg_dotProduct, one_dotProduct]
  refine ⟨L, Pi.single k 1, ?_, ?_⟩
  · ext x j
    by_cases hjs : (j : ι) = s
    · have hj : j = k := Subtype.ext hjs
      subst j
      simp [hL, k, sub_eq_add_neg]
    · have hj : j ≠ k := fun h ↦ hjs (congrArg Subtype.val h)
      simp [Equiv.swap_apply_of_ne_of_ne j.property hjs, hL, hj]
  · simp [L, LinearMap.det_toLin', hdet]

/-- The absolute Jacobian of a deleted-coordinate chart transition is one. The target
coordinates are reindexed by swapping the reference categories, so the derivative is an
endomorphism of the source coordinate space. -/
theorem abs_det_fderiv_dirichletChart_swap (r s : ι) (x : {i // i ≠ r} → ℝ) :
    |(fderiv ℝ (fun (y : {i // i ≠ r} → ℝ) (j : {i // i ≠ r}) ↦
      dirichletChart r y (Equiv.swap r s j)) x).toLinearMap.det| = 1 := by
  obtain ⟨L, c, hf, hdet⟩ := dirichletChart_swap_eq_affine r s
  rw [hf, (L.hasFDerivAt.const_add c).fderiv]
  exact hdet

/-- Changing the deleted coordinate preserves product Lebesgue measure. -/
theorem measurePreserving_dirichletChartChange (r s : ι) :
    MeasurePreserving (dirichletChartChange r s) volume volume := by
  obtain ⟨L, c, hf, hdet⟩ := dirichletChart_swap_eq_affine r s
  have hL : MeasurePreserving L volume volume := by
    refine ⟨L.continuous.measurable, ?_⟩
    have hne : LinearMap.det L.toLinearMap ≠ 0 := by
      intro h
      simp [h] at hdet
    simpa [abs_inv, hdet] using
      Real.map_linearMap_volume_pi_eq_smul_volume_pi (f := L.toLinearMap) hne
  have hswap : MeasurePreserving
      (fun (x : {i // i ≠ r} → ℝ) (j : {i // i ≠ r}) ↦
        dirichletChart r x (Equiv.swap r s j)) volume volume := by
    rw [hf]
    exact (measurePreserving_add_left volume c).comp hL
  let e : {i // i ≠ r} ≃ {i // i ≠ s} :=
    (Equiv.swap r s).subtypeEquiv (fun i ↦ by
      have h : (Equiv.swap r s) i ≠ (Equiv.swap r s) r ↔ i ≠ r :=
        (Equiv.swap r s).injective.ne_iff
      simpa only [Equiv.swap_apply_left] using h.symm)
  have he := volume_measurePreserving_piCongrLeft (fun _ : {i // i ≠ s} ↦ ℝ) e
  convert he.comp hswap using 1
  ext x j
  obtain ⟨j, rfl⟩ := e.surjective j
  rw [dirichletChartChange_apply]
  simpa only [Function.comp_apply, e, Equiv.subtypeEquiv_apply] using
    (MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ ↦ ℝ) e
      (fun j ↦ dirichletChart r x (Equiv.swap r s j)) j).symm

/-- The reference measure on the sum-one hyperplane is independent of the deleted
coordinate, with the normalization inherited from product volume. -/
theorem map_dirichletChart_volume_eq (r s : ι) :
    (volume : Measure ({i // i ≠ r} → ℝ)).map (dirichletChart r) =
      (volume : Measure ({i // i ≠ s} → ℝ)).map (dirichletChart s) := by
  rw [← (measurePreserving_dirichletChartChange r s).map_eq,
    Measure.map_map measurable_dirichletChart (measurable_dirichletChartChange r s)]
  simp only [Function.comp_def, dirichletChart_dirichletChartChange]

end TauCeti.Probability
