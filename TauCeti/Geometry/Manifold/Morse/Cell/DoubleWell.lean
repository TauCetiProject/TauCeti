/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Disk.Neg
public import TauCeti.Geometry.Manifold.Morse.Cell.Strict

/-!
# The Morse cell of the double well

The double well `f(x) = (x² - 1)²` on `ℝ` has minima at `±1` and a nondegenerate maximum at `0`,
of value `1` and index `1`. Since `f = 1 - (x √(2 - x²))²`, the maps `x ↦ ± x √(2 - x²)` on
`(-1, 1)` are normal-form charts at `0` (`TauCeti.doubleWellChart` and
`TauCeti.doubleWellChartNeg`), in which `f = 1 - y²`. With `ε = 1/2`, their targets contain the
closed ball of radius `√ε`, so each of them attaches a `1`-cell to the lower sublevel
`{f ≤ 1/2} = [-a, -b] ∪ [b, a]`, where `b = √(1 - 1/√2)` and `a = √(1 + 1/√2)`.

This file computes the two cells and compares them, as a test of the cell-attachment API.

* The attaching maps `α± : S⁰ → {f ≤ 1/2}` are `α±(s) = ± s b`
  (`TauCeti.coe_morseAttachingMap_doubleWellChart` and
  `TauCeti.coe_morseAttachingMap_doubleWellChartNeg`).
* They are not homotopic (`TauCeti.not_homotopic_morseAttachingMap_doubleWellChart`): at `s = 1`
  their values `b` and `-b` lie in different components of `{f ≤ 1/2}`. So the choice of chart
  matters for the attaching map itself, with its source labelled.
* They differ by the reflection `r = -id` of the disc, strictly: `α₋ = α₊ ∘ r` on `S⁰`, and
  likewise for the characteristic maps. Hence the two attachments are homeomorphic relative to the
  lower sublevel, compatibly with the handle-to-cell comparisons
  (`TauCeti.exists_iso_morseCellAttachment_doubleWell`).

## References

* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  Theorem 3.2, Remark 3.3 and Lemma 3.6.
-/

public section

noncomputable section

open Set Metric CategoryTheory

namespace TauCeti

/-- The double well `x ↦ (x² - 1)²`. -/
def doubleWell (x : ℝ) : ℝ :=
  (x ^ 2 - 1) ^ 2

theorem doubleWell_apply (x : ℝ) : doubleWell x = (x ^ 2 - 1) ^ 2 :=
  (rfl)

/-! ### The normal-form coordinate `x ↦ x √(2 - x²)` and its inverse -/

/-- The normal-form coordinate `x ↦ x √(2 - x²)` of the double well at `0`. -/
private def wellCoord (x : ℝ) : ℝ :=
  x * √(2 - x ^ 2)

/-- The inverse `y ↦ y / √(1 + √(1 - y²))` of `wellCoord` on `(-1, 1)`. -/
private def wellCoordInv (y : ℝ) : ℝ :=
  y / √(1 + √(1 - y ^ 2))

private theorem continuous_wellCoord : Continuous wellCoord := by
  unfold wellCoord; fun_prop

private theorem continuous_wellCoordInv : Continuous wellCoordInv :=
  continuous_id.div (by fun_prop) fun y ↦ (Real.sqrt_pos.2 (by positivity)).ne'

private theorem wellCoord_sq {x : ℝ} (hx : x ^ 2 ≤ 2) :
    wellCoord x ^ 2 = 1 - (1 - x ^ 2) ^ 2 := by
  rw [wellCoord, mul_pow, Real.sq_sqrt (by linarith)]
  ring

private theorem sq_lt_one_of_mem_Ioo {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) : x ^ 2 < 1 := by
  rw [sq_lt_one_iff_abs_lt_one, abs_lt]
  exact hx

private theorem mem_Ioo_of_sq_lt_one {x : ℝ} (hx : x ^ 2 < 1) : x ∈ Ioo (-1 : ℝ) 1 :=
  abs_lt.1 ((sq_lt_one_iff_abs_lt_one x).1 hx)

private theorem wellCoord_mem_Ioo {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    wellCoord x ∈ Ioo (-1 : ℝ) 1 := by
  have hx2 := sq_lt_one_of_mem_Ioo hx
  refine mem_Ioo_of_sq_lt_one ?_
  rw [wellCoord_sq (by linarith)]
  have h1 : 0 < 1 - x ^ 2 := by linarith
  have : 0 < (1 - x ^ 2) ^ 2 := by positivity
  linarith

/-- The square of `wellCoordInv y` is `1 - √(1 - y²)`. -/
private theorem wellCoordInv_sq {y : ℝ} (hy : y ^ 2 ≤ 1) :
    wellCoordInv y ^ 2 = 1 - √(1 - y ^ 2) := by
  have hs := Real.sq_sqrt (show 0 ≤ 1 - y ^ 2 by linarith)
  have hd : 0 < 1 + √(1 - y ^ 2) := by positivity
  rw [wellCoordInv, div_pow, Real.sq_sqrt hd.le, div_eq_iff hd.ne']
  nlinarith

private theorem wellCoordInv_mem_Ioo {y : ℝ} (hy : y ∈ Ioo (-1 : ℝ) 1) :
    wellCoordInv y ∈ Ioo (-1 : ℝ) 1 := by
  have hy2 := sq_lt_one_of_mem_Ioo hy
  refine mem_Ioo_of_sq_lt_one ?_
  rw [wellCoordInv_sq hy2.le]
  have : 0 < √(1 - y ^ 2) := Real.sqrt_pos.2 (by linarith)
  linarith

private theorem wellCoordInv_wellCoord {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    wellCoordInv (wellCoord x) = x := by
  have hx2 := sq_lt_one_of_mem_Ioo hx
  have h1 : √(1 - wellCoord x ^ 2) = 1 - x ^ 2 := by
    rw [wellCoord_sq (by linarith), sub_sub_cancel, Real.sqrt_sq (by linarith)]
  have h2 : 0 < √(2 - x ^ 2) := Real.sqrt_pos.2 (by linarith)
  rw [wellCoordInv, h1, show 1 + (1 - x ^ 2) = 2 - x ^ 2 by ring, wellCoord,
    mul_div_assoc, div_self h2.ne', mul_one]

private theorem wellCoord_wellCoordInv {y : ℝ} (hy : y ∈ Ioo (-1 : ℝ) 1) :
    wellCoord (wellCoordInv y) = y := by
  have hy2 := sq_lt_one_of_mem_Ioo hy
  have hd : 0 < √(1 + √(1 - y ^ 2)) := Real.sqrt_pos.2 (by positivity)
  have h : 2 - wellCoordInv y ^ 2 = 1 + √(1 - y ^ 2) := by
    rw [wellCoordInv_sq hy2.le]
    ring
  rw [wellCoord, h, wellCoordInv, div_mul_cancel₀ _ hd.ne']

/-- At the point `a s` with `a = √(1/2)` and `s = ±1`, the inverse coordinate is `s √(1 - 1/√2)`. -/
private theorem wellCoordInv_sqrt_half_mul {s : ℝ} (hs : s ^ 2 = 1) :
    wellCoordInv (√(1 / 2) * s) = s * √(1 - 1 / √2) := by
  set a := √(1 / 2) with ha
  have ha0 : 0 < a := Real.sqrt_pos.2 (by norm_num)
  have ha2 : a ^ 2 = 1 / 2 := Real.sq_sqrt (by norm_num)
  have hinv : 1 / √2 = a := by
    rw [ha, Real.sqrt_div' _ (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_one]
  have hsq : √(1 - (a * s) ^ 2) = a := by
    rw [mul_pow, hs, mul_one, ha2, ha]
    norm_num
  have hd : 0 < √(1 + a) := Real.sqrt_pos.2 (by linarith)
  have hb : √(1 - a) = a / √(1 + a) := by
    rw [Real.sqrt_eq_iff_mul_self_eq_of_pos (div_pos ha0 hd), div_mul_div_comm,
      Real.mul_self_sqrt (show (0 : ℝ) ≤ 1 + a by linarith), div_eq_iff (by positivity)]
    nlinarith
  rw [wellCoordInv, hsq, hinv, hb]
  ring

/-! ### The two charts -/

/-- The normal-form chart `x ↦ x √(2 - x²)` of the double well at `0`, from `(-1, 1)` onto the
open unit ball of `ℝ¹`. In it, `doubleWell = 1 - y²`
(`TauCeti.doubleWell_eq_sum_doubleWellChart`). -/
def doubleWellChart : OpenPartialHomeomorph ℝ (EuclideanSpace ℝ (Fin 1)) where
  toFun x := WithLp.toLp 2 fun _ ↦ wellCoord x
  invFun y := wellCoordInv (y 0)
  source := Ioo (-1) 1
  target := {y | y 0 ∈ Ioo (-1) 1}
  map_source' _ hx := wellCoord_mem_Ioo hx
  map_target' _ hy := wellCoordInv_mem_Ioo hy
  left_inv' _ hx := wellCoordInv_wellCoord hx
  right_inv' y hy := by
    ext j
    rw [Subsingleton.elim j 0]
    exact wellCoord_wellCoordInv hy
  open_source := isOpen_Ioo
  open_target := isOpen_Ioo.preimage (PiLp.continuous_apply 2 _ 0)
  continuousOn_toFun := (PiLp.continuous_toLp 2 _ |>.comp
    (continuous_pi fun _ ↦ continuous_wellCoord)).continuousOn
  continuousOn_invFun := (continuous_wellCoordInv.comp (PiLp.continuous_apply 2 _ 0)).continuousOn

@[simp]
theorem doubleWellChart_source : doubleWellChart.source = Ioo (-1) 1 :=
  (rfl)

@[simp]
theorem doubleWellChart_target : doubleWellChart.target = {y | y 0 ∈ Ioo (-1) 1} :=
  (rfl)

@[simp]
theorem doubleWellChart_apply (x : ℝ) (j : Fin 1) : doubleWellChart x j = x * √(2 - x ^ 2) :=
  (rfl)

private theorem doubleWellChart_symm_apply (y : EuclideanSpace ℝ (Fin 1)) :
    doubleWellChart.symm y = wellCoordInv (y 0) :=
  (rfl)

/-- The reflected normal-form chart `x ↦ -x √(2 - x²)` of the double well at `0`. -/
def doubleWellChartNeg : OpenPartialHomeomorph ℝ (EuclideanSpace ℝ (Fin 1)) :=
  doubleWellChart.trans (Homeomorph.neg (EuclideanSpace ℝ (Fin 1))).toOpenPartialHomeomorph

@[simp]
theorem doubleWellChartNeg_source : doubleWellChartNeg.source = Ioo (-1) 1 := by
  simp [doubleWellChartNeg]

@[simp]
theorem doubleWellChartNeg_apply (x : ℝ) (j : Fin 1) :
    doubleWellChartNeg x j = -(x * √(2 - x ^ 2)) :=
  (rfl)

private theorem doubleWellChartNeg_symm_apply (y : EuclideanSpace ℝ (Fin 1)) :
    doubleWellChartNeg.symm y = wellCoordInv (-y 0) :=
  (rfl)

/-- In the chart `TauCeti.doubleWellChart`, the double well is `1 - y²`, in the form of the
normal-form hypothesis of the cell-attachment API with index `1`. -/
theorem doubleWell_eq_sum_doubleWellChart :
    ∀ x ∈ doubleWellChart.source,
      doubleWell x = 1 + ∑ j : Fin 1, (if j.val < 1 then -1 else 1) * doubleWellChart x j ^ 2 := by
  intro x hx
  have hx2 := sq_lt_one_of_mem_Ioo hx
  have h := wellCoord_sq (x := x) (by linarith)
  simp only [Fin.sum_univ_one, Fin.val_zero, zero_lt_one, ite_true, doubleWellChart_apply,
    doubleWell_apply]
  rw [wellCoord] at h
  linarith

/-- In the chart `TauCeti.doubleWellChartNeg`, the double well is `1 - y²`. -/
theorem doubleWell_eq_sum_doubleWellChartNeg :
    ∀ x ∈ doubleWellChartNeg.source,
      doubleWell x =
        1 + ∑ j : Fin 1, (if j.val < 1 then -1 else 1) * doubleWellChartNeg x j ^ 2 := by
  intro x hx
  rw [doubleWellChartNeg_source] at hx
  have h := doubleWell_eq_sum_doubleWellChart x hx
  simp only [Fin.sum_univ_one, doubleWellChart_apply, doubleWellChartNeg_apply, neg_sq] at h ⊢
  exact h

private theorem abs_apply_zero_le_norm (y : EuclideanSpace ℝ (Fin 1)) : |y 0| ≤ ‖y‖ := by
  simpa [Real.norm_eq_abs] using PiLp.norm_apply_le y 0

private theorem sqrt_half_lt_one : √(1 / 2 : ℝ) < 1 := by
  rw [Real.sqrt_lt' one_pos]
  norm_num

/-- The target of `TauCeti.doubleWellChart` contains the closed ball of radius `√(1/2)`, so the
chart carries the cell of width `ε = 1/2`. -/
theorem closedBall_subset_doubleWellChart_target :
    closedBall 0 √(1 / 2) ⊆ doubleWellChart.target := fun y hy ↦ by
  have h := (abs_apply_zero_le_norm y).trans (mem_closedBall_zero_iff.1 hy)
  exact abs_lt.1 (h.trans_lt sqrt_half_lt_one)

/-- The target of `TauCeti.doubleWellChartNeg` contains the closed ball of radius `√(1/2)`. -/
theorem closedBall_subset_doubleWellChartNeg_target :
    closedBall 0 √(1 / 2) ⊆ doubleWellChartNeg.target := fun y hy ↦ by
  have h := (abs_apply_zero_le_norm y).trans (mem_closedBall_zero_iff.1 hy)
  have h' := abs_lt.1 (h.trans_lt sqrt_half_lt_one)
  rw [doubleWellChartNeg, OpenPartialHomeomorph.trans_target]
  refine ⟨mem_univ _, ?_⟩
  have hneg : -1 < -y 0 ∧ -y 0 < 1 := ⟨by linarith, by linarith⟩
  simpa using hneg

/-! ### The cells and their comparison -/

/-- The point `y` of the unit sphere `S⁰ ⊆ ℝ¹` has `y₀² = 1`. -/
private theorem sq_apply_zero_of_mem_diskBoundary (s : TopCat.diskBoundary.{0} 1) :
    s.down.1 0 ^ 2 = 1 := by
  have h := (abs_apply_zero_le_norm s.down.1).antisymm ?_
  · rw [mem_sphere_zero_iff_norm.1 s.down.2] at h
    rw [← sq_abs, h, one_pow]
  · rw [EuclideanSpace.norm_eq, Fin.sum_univ_one, Real.norm_eq_abs, Real.sqrt_sq_eq_abs, abs_abs]

private theorem morseCellMap_apply_zero (w : EuclideanSpace ℝ (Fin 1)) :
    (√(1 / 2) • LinearIsometry.piLpExtendByZero 2 ℝ ℝ (Fin.castLEEmb (le_refl 1)) w) 0 =
      √(1 / 2) * w 0 := by
  simp

/-- The attaching map of the cell of `TauCeti.doubleWellChart` is `s ↦ s √(1 - 1/√2)`. -/
theorem coe_morseAttachingMap_doubleWellChart (s : TopCat.diskBoundary.{0} 1) :
    (doubleWellChart.morseAttachingMap (le_refl 1) (by norm_num : (0 : ℝ) ≤ 1 / 2)
        closedBall_subset_doubleWellChart_target doubleWell_eq_sum_doubleWellChart s : ℝ) =
      s.down.1 0 * √(1 - 1 / √2) := by
  rw [OpenPartialHomeomorph.coe_morseAttachingMap_apply, OpenPartialHomeomorph.morseCellMap_def,
    doubleWellChart_symm_apply, morseCellMap_apply_zero,
    wellCoordInv_sqrt_half_mul (sq_apply_zero_of_mem_diskBoundary s)]

/-- The attaching map of the cell of `TauCeti.doubleWellChartNeg` is `s ↦ -s √(1 - 1/√2)`. -/
theorem coe_morseAttachingMap_doubleWellChartNeg (s : TopCat.diskBoundary.{0} 1) :
    (doubleWellChartNeg.morseAttachingMap (le_refl 1) (by norm_num : (0 : ℝ) ≤ 1 / 2)
        closedBall_subset_doubleWellChartNeg_target doubleWell_eq_sum_doubleWellChartNeg s : ℝ) =
      -s.down.1 0 * √(1 - 1 / √2) := by
  rw [OpenPartialHomeomorph.coe_morseAttachingMap_apply, OpenPartialHomeomorph.morseCellMap_def,
    doubleWellChartNeg_symm_apply, morseCellMap_apply_zero, ← mul_neg,
    wellCoordInv_sqrt_half_mul (by rw [neg_sq]; exact sq_apply_zero_of_mem_diskBoundary s)]

/-- **The two attaching maps are not homotopic.** At the point `1` of `S⁰` the attaching maps of
the cells of `TauCeti.doubleWellChart` and `TauCeti.doubleWellChartNeg` take the values
`√(1 - 1/√2)` and `-√(1 - 1/√2)`, which lie in different components of the lower sublevel
`{doubleWell ≤ 1/2}`, since `doubleWell 0 = 1`. -/
theorem not_homotopic_morseAttachingMap_doubleWellChart :
    ¬ (doubleWellChart.morseAttachingMap (le_refl 1) (by norm_num : (0 : ℝ) ≤ 1 / 2)
        closedBall_subset_doubleWellChart_target doubleWell_eq_sum_doubleWellChart).hom.Homotopic
      (doubleWellChartNeg.morseAttachingMap (le_refl 1) (by norm_num : (0 : ℝ) ≤ 1 / 2)
        closedBall_subset_doubleWellChartNeg_target doubleWell_eq_sum_doubleWellChartNeg).hom := by
  rintro ⟨H⟩
  -- The point `1` of `S⁰`.
  let s : TopCat.diskBoundary.{0} 1 := ULift.up ⟨WithLp.toLp 2 fun _ ↦ 1, by
    rw [mem_sphere_zero_iff_norm, EuclideanSpace.norm_eq, Fin.sum_univ_one]
    simp⟩
  have hb : 0 < √(1 - 1 / √2) := Real.sqrt_pos.2 (by
    rw [sub_pos, div_lt_one (Real.sqrt_pos.2 two_pos)]
    exact Real.lt_sqrt_of_sq_lt (by norm_num))
  have hcont : Continuous fun t ↦ (H (t, s) : ℝ) :=
    continuous_subtype_val.comp (H.continuous.comp (continuous_id.prodMk continuous_const))
  have h0 : (H (0, s) : ℝ) = √(1 - 1 / √2) := by
    rw [ContinuousMap.Homotopy.apply_zero, coe_morseAttachingMap_doubleWellChart]
    simp [s]
  have h1 : (H (1, s) : ℝ) = -√(1 - 1 / √2) := by
    rw [ContinuousMap.Homotopy.apply_one, coe_morseAttachingMap_doubleWellChartNeg]
    simp only [s, neg_mul, one_mul]
  obtain ⟨t, ht⟩ := intermediate_value_univ 1 0 hcont
    (show (0 : ℝ) ∈ Icc _ _ from ⟨by rw [h1]; linarith, by rw [h0]; linarith⟩)
  have hle : doubleWell (H (t, s) : ℝ) ≤ 1 - 1 / 2 := (H (t, s)).2
  rw [show (H (t, s) : ℝ) = 0 from ht, doubleWell_apply] at hle
  norm_num at hle

/-- The attaching maps differ strictly by the antipodal map of `S⁰`: `α₋ = α₊ ∘ r`. -/
theorem morseAttachingMap_doubleWellChartNeg :
    doubleWellChartNeg.morseAttachingMap (le_refl 1) (by norm_num : (0 : ℝ) ≤ 1 / 2)
        closedBall_subset_doubleWellChartNeg_target doubleWell_eq_sum_doubleWellChartNeg =
      diskBoundaryNeg 1 ≫ doubleWellChart.morseAttachingMap (le_refl 1)
        (by norm_num : (0 : ℝ) ≤ 1 / 2) closedBall_subset_doubleWellChart_target
        doubleWell_eq_sum_doubleWellChart := by
  ext s
  rw [ConcreteCategory.comp_apply, coe_morseAttachingMap_doubleWellChartNeg,
    coe_morseAttachingMap_doubleWellChart, diskBoundaryNeg_apply_down, coe_neg_sphere,
    PiLp.neg_apply]

/-- The characteristic maps differ strictly by the reflection `r = -id` of `D¹`: `χ₋ = χ₊ ∘ r`. -/
theorem morseCharacteristicMap_doubleWellChartNeg :
    doubleWellChartNeg.morseCharacteristicMap (le_refl 1) (by norm_num : (0 : ℝ) ≤ 1 / 2)
        closedBall_subset_doubleWellChartNeg_target doubleWell_eq_sum_doubleWellChartNeg =
      (TopCat.diskNegIso 1).hom ≫ doubleWellChart.morseCharacteristicMap (le_refl 1)
        (by norm_num : (0 : ℝ) ≤ 1 / 2) closedBall_subset_doubleWellChart_target
        doubleWell_eq_sum_doubleWellChart := by
  ext w
  rw [ConcreteCategory.comp_apply, OpenPartialHomeomorph.coe_morseCharacteristicMap_apply,
    OpenPartialHomeomorph.coe_morseCharacteristicMap_apply, OpenPartialHomeomorph.morseCellMap_def,
    OpenPartialHomeomorph.morseCellMap_def, doubleWellChartNeg_symm_apply,
    doubleWellChart_symm_apply, morseCellMap_apply_zero, morseCellMap_apply_zero,
    TopCat.coe_diskNegIso_hom_apply_down, PiLp.neg_apply, mul_neg]

/-- **The two attachments are homeomorphic relative to the lower sublevel.** The attachments of
the cells of `TauCeti.doubleWellChartNeg` and `TauCeti.doubleWellChart` to `{doubleWell ≤ 1/2}`
are homeomorphic by a homeomorphism which is the identity on the lower sublevel (it is the
reflection `r = -id` on the cell) and which intertwines the handle-to-cell comparisons into
`{doubleWell ≤ 3/2}`. -/
theorem exists_iso_morseCellAttachment_doubleWell :
    ∃ e : morseCellAttachment (ι := Unit) (fun _ ↦ doubleWellChartNeg) (fun _ ↦ 1)
        (fun _ ↦ le_refl 1) (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (fun _ ↦ closedBall_subset_doubleWellChartNeg_target)
        (fun _ ↦ doubleWell_eq_sum_doubleWellChartNeg) ≅
      morseCellAttachment (ι := Unit) (fun _ ↦ doubleWellChart) (fun _ ↦ 1) (fun _ ↦ le_refl 1)
        (by norm_num : (0 : ℝ) ≤ 1 / 2) (fun _ ↦ closedBall_subset_doubleWellChart_target)
        (fun _ ↦ doubleWell_eq_sum_doubleWellChart),
      morseCellAttachmentIncl _ _ _ _ _ _ ≫ e.hom = morseCellAttachmentIncl _ _ _ _ _ _ ∧
        e.hom ≫ morseCellComparison _ _ _ _ _ _ = morseCellComparison _ _ _ _ _ _ :=
  ⟨morseCellAttachmentIso _ _ _ _ _ _ _ _ _ (fun _ ↦ TopCat.diskNegIso 1)
      (fun _ ↦ TopCat.diskBoundaryNegIso 1)
      (fun _ ↦ by rw [TopCat.diskBoundaryNegIso_hom]
                  exact TopCat.diskBoundaryNeg_comp_diskBoundaryInclusion 1)
      (fun _ ↦ by rw [TopCat.diskBoundaryNegIso_hom]; exact morseAttachingMap_doubleWellChartNeg),
    morseCellAttachmentIncl_comp_morseCellAttachmentIso_hom ..,
    morseCellAttachmentIso_hom_comp_morseCellComparison _ _ _ _ _ _ _ _ _ _ _ _ _
      fun _ ↦ morseCharacteristicMap_doubleWellChartNeg⟩

end TauCeti
