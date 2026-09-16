/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Dirichlet.Basic

import Mathlib.MeasureTheory.Function.Jacobian

/-!
# Simplex coordinates for the Dirichlet distribution

Fixing one coordinate `i₀`, a point of the open simplex is described by its other coordinates;
the missing coordinate is one minus their sum.  Adjoining a positive scale gives coordinates for
the positive orthant: the inverse map multiplies every simplex coordinate by the scale.  Its
Jacobian is the scale to the power `|ι| - 1`.

This is the geometric change of variables underlying the lower-dimensional density of the
Dirichlet distribution.  The definitions here keep the displayed simplex chart separate from the
ambient Euclidean space, so a later density statement cannot accidentally claim absolute
continuity with respect to ambient volume.

## Main definitions and results

* `TauCeti.Probability.dirichletChart` is the open coordinate region of the simplex;
* `TauCeti.Probability.dirichletChartReconstruct` restores the omitted coordinate;
* `TauCeti.Probability.dirichletGammaCoordinates` adjoins a scale and maps to the positive
  orthant;
* `TauCeti.Probability.dirichletGammaCoordinates_image` identifies its image;
* `TauCeti.Probability.det_fderivDirichletGammaCoordinates` computes its Jacobian determinant;
* `TauCeti.Probability.map_dirichletGammaCoordinates_withDensity` gives the resulting
  change-of-variables identity for Lebesgue measure.

## References

* N. L. Johnson, S. Kotz, N. Balakrishnan, *Continuous Multivariate Distributions*, vol. 1,
  2nd ed., Wiley, 2000, Chapter 49.
-/

public section

noncomputable section

open Finset MeasureTheory Set
open scoped BigOperators

namespace TauCeti

namespace Probability

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The coordinate type of the simplex chart obtained by omitting `i₀`. -/
abbrev DirichletChartIndex (i₀ : ι) := {i : ι // i ≠ i₀}

/-- The open simplex in the chart which omits coordinate `i₀`. -/
def dirichletChart (i₀ : ι) : Set (DirichletChartIndex i₀ → ℝ) :=
  {x | (∀ i, 0 < x i) ∧ ∑ i, x i < 1}

/-- Reconstruct a simplex point from all coordinates except `i₀`, setting its `i₀`
coordinate to one minus the sum of the displayed coordinates. -/
def dirichletChartReconstruct (i₀ : ι) (x : DirichletChartIndex i₀ → ℝ) :
    EuclideanSpace ℝ ι :=
  (EuclideanSpace.equiv ι ℝ).symm fun i ↦
    if h : i = i₀ then 1 - ∑ j, x j else x ⟨i, h⟩

@[simp]
theorem dirichletChartReconstruct_apply_eq (i₀ : ι) (x : DirichletChartIndex i₀ → ℝ) :
    dirichletChartReconstruct i₀ x i₀ = 1 - ∑ j, x j := by
  simp [dirichletChartReconstruct]

@[simp]
theorem dirichletChartReconstruct_apply_ne (i₀ : ι)
    (x : DirichletChartIndex i₀ → ℝ) {i : ι} (hi : i ≠ i₀) :
    dirichletChartReconstruct i₀ x i = x ⟨i, hi⟩ := by
  simp [dirichletChartReconstruct, hi]

/-- Every reconstructed chart point has coordinate sum one. -/
@[simp]
theorem sum_dirichletChartReconstruct (i₀ : ι) (x : DirichletChartIndex i₀ → ℝ) :
    ∑ i, dirichletChartReconstruct i₀ x i = 1 := by
  rw [← univ.add_sum_erase _ (mem_univ i₀), dirichletChartReconstruct_apply_eq]
  have hsum : ∑ i ∈ univ.erase i₀, dirichletChartReconstruct i₀ x i = ∑ j, x j := by
    calc
      ∑ i ∈ univ.erase i₀, dirichletChartReconstruct i₀ x i =
          ∑ j : DirichletChartIndex i₀, dirichletChartReconstruct i₀ x j :=
        sum_subtype (univ.erase i₀) (by simp) _
      _ = ∑ j, x j := sum_congr rfl fun j _ ↦ dirichletChartReconstruct_apply_ne i₀ x j.2
  rw [hsum]
  ring

/-- A point in the open chart reconstructs to a point with strictly positive coordinates. -/
theorem dirichletChartReconstruct_pos {i₀ : ι} {x : DirichletChartIndex i₀ → ℝ}
    (hx : x ∈ dirichletChart i₀) (i : ι) : 0 < dirichletChartReconstruct i₀ x i := by
  by_cases hi : i = i₀
  · subst i
    rw [dirichletChartReconstruct_apply_eq]
    exact sub_pos.mpr hx.2
  · rw [dirichletChartReconstruct_apply_ne i₀ x hi]
    exact hx.1 ⟨i, hi⟩

/-- Store a chart point and its scale in a single `ι`-indexed vector, using the omitted coordinate
to hold the scale. -/
def dirichletChartWithScale (i₀ : ι) : Set (ι → ℝ) :=
  {z | 0 < z i₀ ∧ (∀ i, i ≠ i₀ → 0 < z i) ∧ ∑ i : DirichletChartIndex i₀, z i < 1}

/-- Multiply the simplex point encoded by `z` by the positive scale stored in coordinate `i₀`. -/
def dirichletGammaCoordinates (i₀ : ι) (z : ι → ℝ) : ι → ℝ := fun i ↦
  if i = i₀ then z i₀ * (1 - ∑ j : DirichletChartIndex i₀, z j) else z i₀ * z i

/-- The inverse coordinates on the positive orthant: the total is stored at `i₀`, and every
other coordinate is divided by that total. -/
def dirichletGammaCoordinatesInv (i₀ : ι) (y : ι → ℝ) : ι → ℝ := fun i ↦
  if i = i₀ then ∑ j, y j else y i / ∑ j, y j

/-- The positive orthant in finite product coordinates. -/
def dirichletPositiveOrthant : Set (ι → ℝ) := {y | ∀ i, 0 < y i}

theorem measurableSet_dirichletChart (i₀ : ι) : MeasurableSet (dirichletChart i₀) := by
  unfold dirichletChart
  measurability

theorem measurableSet_dirichletChartWithScale (i₀ : ι) :
    MeasurableSet (dirichletChartWithScale i₀) := by
  unfold dirichletChartWithScale
  measurability

omit [Fintype ι] [DecidableEq ι] in
theorem measurableSet_dirichletPositiveOrthant [Finite ι] :
    MeasurableSet (dirichletPositiveOrthant : Set (ι → ℝ)) := by
  let _ := Fintype.ofFinite ι
  unfold dirichletPositiveOrthant
  measurability

@[fun_prop]
theorem measurable_dirichletGammaCoordinates (i₀ : ι) :
    Measurable (dirichletGammaCoordinates i₀) := by
  refine measurable_pi_iff.mpr fun i ↦ ?_
  by_cases hi : i = i₀
  · simp only [dirichletGammaCoordinates, hi, ite_true]
    fun_prop
  · simp only [dirichletGammaCoordinates, hi, ite_false]
    fun_prop

@[fun_prop]
theorem measurable_dirichletGammaCoordinatesInv (i₀ : ι) :
    Measurable (dirichletGammaCoordinatesInv i₀) := by
  refine measurable_pi_iff.mpr fun i ↦ ?_
  by_cases hi : i = i₀
  · simp only [dirichletGammaCoordinatesInv, hi, ite_true]
    fun_prop
  · simp only [dirichletGammaCoordinatesInv, hi, ite_false]
    fun_prop

/-- The chart-and-scale map sends its natural domain into the positive orthant. -/
theorem dirichletGammaCoordinates_mem_positiveOrthant {i₀ : ι} {z : ι → ℝ}
    (hz : z ∈ dirichletChartWithScale i₀) :
    dirichletGammaCoordinates i₀ z ∈ dirichletPositiveOrthant := by
  intro i
  rw [dirichletGammaCoordinates]
  split_ifs with hi
  · exact mul_pos hz.1 (sub_pos.mpr hz.2.2)
  · exact mul_pos hz.1 (hz.2.1 i hi)

/-- Positive orthant coordinates map back into the chart-and-scale domain. -/
theorem dirichletGammaCoordinatesInv_mem_chartWithScale {i₀ : ι} {y : ι → ℝ}
    (hy : y ∈ dirichletPositiveOrthant) :
    dirichletGammaCoordinatesInv i₀ y ∈ dirichletChartWithScale i₀ := by
  let _ : Nonempty ι := ⟨i₀⟩
  have hsum : 0 < ∑ i, y i := Finset.sum_pos (fun i _ ↦ hy i) univ_nonempty
  refine ⟨by simp [dirichletGammaCoordinatesInv, hsum], ?_, ?_⟩
  · intro i hi
    simp only [dirichletGammaCoordinatesInv, ite_eq_right hi]
    exact div_pos (hy i) hsum
  · have heq : ∑ i : DirichletChartIndex i₀, dirichletGammaCoordinatesInv i₀ y i =
        ∑ i : DirichletChartIndex i₀, y i / ∑ j, y j := by
      apply sum_congr rfl
      intro i _
      rw [dirichletGammaCoordinatesInv, ite_eq_right i.2]
    rw [heq, ← sum_div,
      ← sum_subtype (p := fun i ↦ i ≠ i₀) (univ.erase i₀) (by simp) y,
      div_lt_one hsum]
    calc
      ∑ i ∈ univ.erase i₀, y i < y i₀ + ∑ i ∈ univ.erase i₀, y i :=
        lt_add_of_pos_left _ (hy i₀)
      _ = ∑ i, y i := univ.add_sum_erase y (mem_univ i₀)

/-- The inverse-coordinate map is a left inverse on the chart-and-scale domain. -/
theorem dirichletGammaCoordinatesInv_apply_coordinates {i₀ : ι} {z : ι → ℝ}
    (hz : z ∈ dirichletChartWithScale i₀) :
    dirichletGammaCoordinatesInv i₀ (dirichletGammaCoordinates i₀ z) = z := by
  have hsum : ∑ i, dirichletGammaCoordinates i₀ z i = z i₀ := by
    rw [← univ.add_sum_erase _ (mem_univ i₀)]
    simp only [dirichletGammaCoordinates, ite_eq_left]
    have hrest : ∑ i ∈ univ.erase i₀, (if i = i₀ then
        z i₀ * (1 - ∑ j : DirichletChartIndex i₀, z j) else z i₀ * z i) =
        z i₀ * ∑ j : DirichletChartIndex i₀, z j := by
      calc
        _ = ∑ i ∈ univ.erase i₀, z i₀ * z i := by
          apply sum_congr rfl
          intro i hi
          rw [ite_eq_right (mem_erase.mp hi).1]
        _ = z i₀ * ∑ j : DirichletChartIndex i₀, z j := by
          rw [← mul_sum,
            sum_subtype (p := fun i ↦ i ≠ i₀) (univ.erase i₀) (by simp) z]
    rw [hrest]
    ring
  funext i
  rw [dirichletGammaCoordinatesInv]
  split_ifs with hi
  · simp [hi, hsum]
  · rw [dirichletGammaCoordinates, ite_eq_right hi, hsum]
    exact mul_div_cancel_left₀ (z i) hz.1.ne'

/-- The chart-and-scale map is a left inverse on the positive orthant. -/
theorem dirichletGammaCoordinates_apply_inv {i₀ : ι} {y : ι → ℝ}
    (hy : y ∈ dirichletPositiveOrthant) :
    dirichletGammaCoordinates i₀ (dirichletGammaCoordinatesInv i₀ y) = y := by
  let _ : Nonempty ι := ⟨i₀⟩
  have hsum : 0 < ∑ i, y i := Finset.sum_pos (fun i _ ↦ hy i) univ_nonempty
  funext i
  rw [dirichletGammaCoordinates]
  split_ifs with hi
  · subst i
    have hrest : ∑ j : DirichletChartIndex i₀, dirichletGammaCoordinatesInv i₀ y j =
        (∑ j ∈ univ.erase i₀, y j) / ∑ k, y k := by
      calc
        _ = ∑ j : DirichletChartIndex i₀, y j / ∑ k, y k := by
          apply sum_congr rfl
          intro j _
          rw [dirichletGammaCoordinatesInv, ite_eq_right j.2]
        _ = _ := by
          rw [← sum_div,
            ← sum_subtype (p := fun i ↦ i ≠ i₀) (univ.erase i₀) (by simp) y]
    rw [show dirichletGammaCoordinatesInv i₀ y i₀ = ∑ k, y k by
      simp [dirichletGammaCoordinatesInv], hrest]
    field_simp
    rw [← univ.add_sum_erase _ (mem_univ i₀)]
    ring
  · rw [dirichletGammaCoordinatesInv, ite_eq_left rfl,
      dirichletGammaCoordinatesInv, ite_eq_right hi]
    field_simp

/-- The chart-and-scale coordinate map is injective on its natural domain. -/
theorem dirichletGammaCoordinates_injOn (i₀ : ι) :
    Set.InjOn (dirichletGammaCoordinates i₀) (dirichletChartWithScale i₀) := by
  intro z hz w hw hzw
  rw [← dirichletGammaCoordinatesInv_apply_coordinates hz,
    ← dirichletGammaCoordinatesInv_apply_coordinates hw, hzw]

/-- The image of the chart-and-scale domain is exactly the positive orthant. -/
theorem dirichletGammaCoordinates_image (i₀ : ι) :
    dirichletGammaCoordinates i₀ '' dirichletChartWithScale i₀ =
      (dirichletPositiveOrthant : Set (ι → ℝ)) := by
  apply Set.Subset.antisymm
  · rintro _ ⟨z, hz, rfl⟩
    exact dirichletGammaCoordinates_mem_positiveOrthant hz
  · intro y hy
    exact ⟨dirichletGammaCoordinatesInv i₀ y,
      dirichletGammaCoordinatesInv_mem_chartWithScale hy,
      dirichletGammaCoordinates_apply_inv hy⟩

/-! ### The Jacobian -/

/-- The derivative of the chart-and-scale map. -/
def fderivDirichletGammaCoordinates (i₀ : ι) (z : ι → ℝ) :
    (ι → ℝ) →L[ℝ] (ι → ℝ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun h i ↦ if i = i₀ then
        (1 - ∑ j : DirichletChartIndex i₀, z j) * h i₀ -
          z i₀ * ∑ j : DirichletChartIndex i₀, h j
        else z i * h i₀ + z i₀ * h i
      map_add' := fun h k ↦ by
        ext i
        by_cases hi : i = i₀
        · simp [hi, Finset.sum_add_distrib]
          ring
        · simp [hi]
          ring
      map_smul' := fun c h ↦ by
        ext i
        by_cases hi : i = i₀
        · simp only [Pi.smul_apply, smul_eq_mul, ite_eq_left hi]
          rw [← Finset.mul_sum]
          simp only [RingHom.id_apply]
          ring
        · simp [hi]
          ring }

@[simp]
theorem fderivDirichletGammaCoordinates_apply (i₀ : ι) (z h : ι → ℝ) (i : ι) :
    fderivDirichletGammaCoordinates i₀ z h i = if i = i₀ then
      (1 - ∑ j : DirichletChartIndex i₀, z j) * h i₀ -
        z i₀ * ∑ j : DirichletChartIndex i₀, h j
      else z i * h i₀ + z i₀ * h i := by
  simp [fderivDirichletGammaCoordinates]

/-- The chart-and-scale coordinate change is differentiable, with the displayed derivative. -/
theorem hasFDerivAt_dirichletGammaCoordinates (i₀ : ι) (z : ι → ℝ) :
    HasFDerivAt (dirichletGammaCoordinates i₀)
      (fderivDirichletGammaCoordinates i₀ z) z := by
  rw [hasFDerivAt_pi']
  intro i
  by_cases hi : i = i₀
  · subst i
    have hsum : HasFDerivAt (fun y : ι → ℝ ↦ ∑ j : DirichletChartIndex i₀, y j)
        (∑ j : DirichletChartIndex i₀,
          (ContinuousLinearMap.proj (R := ℝ) (j : ι) : (ι → ℝ) →L[ℝ] ℝ)) z :=
      by
        simpa using HasFDerivAt.fun_sum
          (u := (Finset.univ : Finset (DirichletChartIndex i₀)))
          (A := fun j (y : ι → ℝ) ↦ y (j : ι))
          (A' := fun j ↦
            (ContinuousLinearMap.proj (R := ℝ) (j : ι) : (ι → ℝ) →L[ℝ] ℝ))
          fun j _ ↦ hasFDerivAt_apply (j : ι) z
    have hcalc := (hasFDerivAt_apply i₀ z).fun_mul
      ((hasFDerivAt_const (x := z) (c := (1 : ℝ))).sub hsum)
    rw [show (fun y : ι → ℝ ↦ dirichletGammaCoordinates i₀ y i₀) =
        fun y ↦ y i₀ * (1 - ∑ j : DirichletChartIndex i₀, y j) by
      funext y
      simp [dirichletGammaCoordinates]]
    have hderiv : (ContinuousLinearMap.proj (R := ℝ) i₀).comp
        (fderivDirichletGammaCoordinates i₀ z) =
        z i₀ • (0 - ∑ j : DirichletChartIndex i₀,
          ContinuousLinearMap.proj (R := ℝ) (j : ι)) +
        (1 - ∑ j : DirichletChartIndex i₀, z j) •
          ContinuousLinearMap.proj (R := ℝ) i₀ := by
      ext h
      simp only [ContinuousLinearMap.coe_comp, Function.comp_apply,
        ContinuousLinearMap.proj_apply, fderivDirichletGammaCoordinates_apply, ite_eq_left,
        add_apply, smul_apply, smul_eq_mul]
      have hneg : ((0 - ∑ j : DirichletChartIndex i₀,
          ContinuousLinearMap.proj (R := ℝ) (j : ι)) :
          (ι → ℝ) →L[ℝ] ℝ) h =
          -∑ j : DirichletChartIndex i₀, h j := by
        rw [sub_apply, zero_apply, zero_sub]
        congr 1
        simp
      rw [hneg]
      ring
    rw [hderiv]
    exact hcalc
  · have hleft : HasFDerivAt (fun y : ι → ℝ ↦ y i₀)
        (ContinuousLinearMap.proj (R := ℝ) i₀) z := hasFDerivAt_apply i₀ z
    have hright : HasFDerivAt (fun y : ι → ℝ ↦ y i)
        (ContinuousLinearMap.proj (R := ℝ) i) z := hasFDerivAt_apply i z
    have hcalc := hleft.fun_mul hright
    rw [show (fun y : ι → ℝ ↦ dirichletGammaCoordinates i₀ y i) =
        fun y ↦ y i₀ * y i by
      funext y
      simp [dirichletGammaCoordinates, hi]]
    have hderiv : (ContinuousLinearMap.proj (R := ℝ) i).comp
        (fderivDirichletGammaCoordinates i₀ z) =
        z i₀ • ContinuousLinearMap.proj (R := ℝ) i +
          z i • ContinuousLinearMap.proj (R := ℝ) i₀ := by
      ext h
      simp only [ContinuousLinearMap.coe_comp, Function.comp_apply,
        ContinuousLinearMap.proj_apply, fderivDirichletGammaCoordinates_apply, ite_eq_right hi,
        add_apply, smul_apply, smul_eq_mul]
      ring
    rw [hderiv]
    exact hcalc

private theorem toMatrix_fderivDirichletGammaCoordinates (i₀ : ι) (z : ι → ℝ) (i k : ι) :
    LinearMap.toMatrix (Pi.basisFun ℝ ι) (Pi.basisFun ℝ ι)
        (fderivDirichletGammaCoordinates i₀ z) i k =
      if i = i₀ then
        if k = i₀ then 1 - ∑ j : DirichletChartIndex i₀, z j else -z i₀
      else if k = i₀ then z i else if k = i then z i₀ else 0 := by
  rw [LinearMap.toMatrix_apply, Pi.basisFun_repr, Pi.basisFun_apply,
    ContinuousLinearMap.coe_coe, fderivDirichletGammaCoordinates_apply]
  by_cases hi : i = i₀
  · subst i
    by_cases hk : k = i₀
    · subst k
      have hsum : ∑ j : DirichletChartIndex i₀,
          (Pi.single i₀ (1 : ℝ) : ι → ℝ) (j : ι) = 0 := by
        apply Finset.sum_eq_zero
        intro j _
        rw [Pi.single_eq_of_ne j.2]
      rw [Pi.single_eq_same, hsum]
      simp
    · have hsum : ∑ j : DirichletChartIndex i₀,
          (Pi.single k (1 : ℝ) : ι → ℝ) (j : ι) = 1 := by
        rw [Finset.sum_eq_single ⟨k, hk⟩]
        · exact Pi.single_eq_same k 1
        · intro b _ hb
          rw [Pi.single_eq_of_ne]
          exact fun h ↦ hb (Subtype.ext h)
        · simp
      rw [Pi.single_eq_of_ne (Ne.symm hk), hsum]
      simp [hk]
  · by_cases hk₀ : k = i₀
    · subst k
      simp [hi]
    · by_cases hki : k = i
      · subst k
        simp [hi]
      · simp [hi, hk₀, hki]

private theorem sum_rows_toMatrix_fderivDirichletGammaCoordinates (i₀ : ι) (z : ι → ℝ)
    (k : ι) :
    ∑ i, LinearMap.toMatrix (Pi.basisFun ℝ ι) (Pi.basisFun ℝ ι)
        (fderivDirichletGammaCoordinates i₀ z) i k = if k = i₀ then 1 else 0 := by
  rw [← univ.add_sum_erase _ (mem_univ i₀),
    toMatrix_fderivDirichletGammaCoordinates]
  simp only [ite_eq_left]
  by_cases hk : k = i₀
  · subst k
    simp only [ite_eq_left]
    have hrest : ∑ i ∈ univ.erase i₀, z i = ∑ j : DirichletChartIndex i₀, z j :=
      sum_subtype (p := fun i ↦ i ≠ i₀) (univ.erase i₀) (by simp) z
    have htail : ∑ i ∈ univ.erase i₀,
        LinearMap.toMatrix (Pi.basisFun ℝ ι) (Pi.basisFun ℝ ι)
          (fderivDirichletGammaCoordinates i₀ z) i i₀ = ∑ i ∈ univ.erase i₀, z i := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [toMatrix_fderivDirichletGammaCoordinates]
      simp [(mem_erase.mp hi).1]
    rw [htail, hrest]
    ring
  · rw [ite_eq_right hk]
    have hk_mem : k ∈ univ.erase i₀ := by simp [hk]
    have htail : ∑ i ∈ univ.erase i₀,
        LinearMap.toMatrix (Pi.basisFun ℝ ι) (Pi.basisFun ℝ ι)
          (fderivDirichletGammaCoordinates i₀ z) i k = z i₀ := by
      rw [Finset.sum_eq_single k]
      · rw [toMatrix_fderivDirichletGammaCoordinates]
        simp [hk]
      · intro i hi hik
        have hi₀ : i ≠ i₀ := (mem_erase.mp hi).1
        rw [toMatrix_fderivDirichletGammaCoordinates]
        simp [hi₀, hk, Ne.symm hik]
      · intro hnot
        exact (hnot hk_mem).elim
    rw [htail]
    simp [hk]

/-- **The Jacobian determinant of the simplex chart with scale.** The scale coordinate contributes
one factor for every displayed simplex coordinate. -/
theorem det_fderivDirichletGammaCoordinates (i₀ : ι) (z : ι → ℝ) :
    (fderivDirichletGammaCoordinates i₀ z).det =
      (z i₀) ^ Fintype.card (DirichletChartIndex i₀) := by
  let M := LinearMap.toMatrix (Pi.basisFun ℝ ι) (Pi.basisFun ℝ ι)
    (fderivDirichletGammaCoordinates i₀ z)
  let A := M.updateRow i₀ (∑ i, M i)
  have hA (i k : ι) : A i k = if i = i₀ then
      (if k = i₀ then 1 else 0)
      else if k = i₀ then z i else if k = i then z i₀ else 0 := by
    change M.updateRow i₀ (∑ i, M i) i k = _
    rw [Matrix.updateRow_apply]
    by_cases hi : i = i₀
    · rw [ite_eq_left hi, ite_eq_left hi]
      calc
        (∑ i, M i) k = ∑ i, M i k := by
          simpa using Finset.sum_apply k Finset.univ M
        _ = if k = i₀ then 1 else 0 := by
          simpa only [M] using sum_rows_toMatrix_fderivDirichletGammaCoordinates i₀ z k
    · rw [ite_eq_right hi, ite_eq_right hi]
      simpa only [M, ite_eq_right hi] using
        toMatrix_fderivDirichletGammaCoordinates i₀ z i k
  have hdet : A.det = M.det := by
    have hrows : (∑ i, M i) = ∑ i, (1 : ℝ) • M i := by simp
    change (M.updateRow i₀ (∑ i, M i)).det = M.det
    rw [hrows, Matrix.det_updateRow_sum]
    simp
  rw [ContinuousLinearMap.det, ← LinearMap.det_toMatrix (Pi.basisFun ℝ ι)]
  change M.det = _
  rw [← hdet, Matrix.det_apply']
  rw [Finset.sum_eq_single 1]
  · simp only [Equiv.Perm.sign_one, Units.val_one, Int.cast_one, Equiv.Perm.one_apply,
      one_mul]
    rw [show ∏ i, A i i = ∏ i, (if i = i₀ then 1 else z i₀) by
      apply Finset.prod_congr rfl
      intro i _
      rw [hA i i]
      by_cases hi : i = i₀ <;> simp [hi]]
    let _ : Fintype {i : ι // i ≠ i₀} :=
      inferInstanceAs (Fintype (DirichletChartIndex i₀))
    calc
      ∏ i, (if i = i₀ then 1 else z i₀) = ∏ _i : DirichletChartIndex i₀, z i₀ := by
        rw [← Finset.prod_erase_mul _ _ (mem_univ i₀)]
        simp only [ite_eq_left, mul_one]
        rw [prod_congr rfl fun i hi ↦ ite_eq_right (mem_erase.mp hi).1,
          prod_subtype (p := fun i ↦ i ≠ i₀) (univ.erase i₀) (by simp)
            (fun _ ↦ z i₀)]
      _ = (z i₀) ^ Fintype.card (DirichletChartIndex i₀) := by
        exact (Finset.prod_const (s := (Finset.univ : Finset (DirichletChartIndex i₀)))
          (z i₀)).trans (by rw [Finset.card_univ])
  · intro σ _ hσ
    have hprod : ∏ i, A (σ i) i = 0 := by
      by_cases hfix : σ i₀ = i₀
      · obtain ⟨i, hi⟩ := not_forall.1 (mt Equiv.ext hσ)
        have hi₀ : i ≠ i₀ := by
          intro h
          subst i
          exact hi hfix
        have hσi₀ : σ i ≠ i₀ := by
          intro h
          exact hi₀ (σ.injective (h.trans hfix.symm))
        apply Finset.prod_eq_zero (mem_univ i)
        rw [hA (σ i) i]
        have hi' : i ≠ σ i := fun h ↦ hi h.symm
        rw [ite_eq_right hσi₀, ite_eq_right hi₀, ite_eq_right hi']
      · let i := σ.symm i₀
        have hσi : σ i = i₀ := σ.apply_symm_apply i₀
        have hi₀ : i ≠ i₀ := by
          intro h
          apply hfix
          simpa [h] using hσi
        apply Finset.prod_eq_zero (mem_univ i)
        rw [hA (σ i) i]
        rw [ite_eq_left hσi, ite_eq_right hi₀]
    rw [hprod, mul_zero]
  · simp

/-- On the positive-scale chart, the absolute Jacobian is the positive scale to the number of
displayed simplex coordinates. -/
theorem abs_det_fderivDirichletGammaCoordinates {i₀ : ι} {z : ι → ℝ}
    (hz : z ∈ dirichletChartWithScale i₀) :
    |(fderivDirichletGammaCoordinates i₀ z).det| =
      (z i₀) ^ Fintype.card (DirichletChartIndex i₀) := by
  rw [det_fderivDirichletGammaCoordinates, abs_of_pos (pow_pos hz.1 _)]

/-- The Jacobian formula for the simplex-and-scale coordinate change, expressed as an equality of
restricted Lebesgue measures. -/
theorem map_dirichletGammaCoordinates_withDensity (i₀ : ι) :
    Measure.map (dirichletGammaCoordinates i₀)
        ((volume.restrict (dirichletChartWithScale i₀)).withDensity fun z ↦
          ENNReal.ofReal ((z i₀) ^ Fintype.card (DirichletChartIndex i₀))) =
      volume.restrict dirichletPositiveOrthant := by
  let _ : Measure.IsAddHaarMeasure (volume : Measure (ι → ℝ)) :=
    isAddHaarMeasure_volume_pi ι
  have heq : (fun z : ι → ℝ ↦
      ENNReal.ofReal ((z i₀) ^ Fintype.card (DirichletChartIndex i₀)))
      =ᵐ[volume.restrict (dirichletChartWithScale i₀)] fun z ↦
        ENNReal.ofReal |(fderivDirichletGammaCoordinates i₀ z).det| := by
    filter_upwards [ae_restrict_mem (measurableSet_dirichletChartWithScale i₀)] with z hz
    rw [abs_det_fderivDirichletGammaCoordinates hz]
  rw [withDensity_congr_ae heq, ← dirichletGammaCoordinates_image]
  exact map_withDensity_abs_det_fderiv_eq_addHaar volume
    (measurableSet_dirichletChartWithScale i₀).nullMeasurableSet
    (fun z _ ↦ (hasFDerivAt_dirichletGammaCoordinates i₀ z).hasFDerivWithinAt)
    (dirichletGammaCoordinates_injOn i₀)

end Probability

end TauCeti
