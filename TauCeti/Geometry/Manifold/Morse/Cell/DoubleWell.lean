/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Disk
public import TauCeti.Geometry.Manifold.Morse.Cell.Comparison
public import Mathlib.Topology.Homotopy.Basic

/-!
# The cell of the double well and its two charts

The double well `f x = (x² - 1)²` on `ℝ` has a nondegenerate local maximum at `0`, of index `1`,
with value `c = 1`. Since `f x = 1 - x² (2 - x²)`, the coordinate `y = x √(2 - x²)` is a normal-form
chart `f = 1 - y²` on `(-1, 1)` (`TauCeti.doubleWellChart`), and so is its negative `-y`
(`TauCeti.negDoubleWellChart`). Passing the level `c = 1` with `ε = 1/2` attaches a `1`-cell to
the lower sublevel `M_{1/2} = {f ≤ 1/2}`, which is the union of the two intervals
`1 - 1/√2 ≤ x² ≤ 1 + 1/√2`, one on each side of `0`.

The cells of the two charts are attached along the maps `α_± : S⁰ → M_{1/2}`,
`α_±(s) = ± s √(1 - 1/√2)` (`TauCeti.coe_doubleWellChart_morseAttachingMap`,
`TauCeti.coe_negDoubleWellChart_morseAttachingMap`), where `S⁰ = {-1, 1}` is the boundary of the
disc `D¹ = [-1, 1]`. For each `s`, the points `α_+(s)` and `α_-(s)` lie in different connected
components of `M_{1/2}`, on opposite sides of the maximum `0` where `f = 1`; so `α_+` and `α_-`
are not homotopic as maps out of the labelled sphere `S⁰`
(`TauCeti.not_homotopic_doubleWellChart_morseAttachingMap`). The attaching map of one chart
depends on the choice of chart, and only its class up to automorphisms of the disc is intrinsic.
Here the two maps differ strictly by the reflection `r = -id` of `D¹`, `α_- = α_+ ∘ r`
(`TauCeti.negDoubleWellChart_morseAttachingMap`), and the map that is the identity on `M_{1/2}`
and `r` on the disc is a homeomorphism between the two attachments
`M_{1/2} ∪_{α_-} D¹ ≅ M_{1/2} ∪_{α_+} D¹`
(`TauCeti.exists_negDoubleWellChart_morseCellAttachment_iso`), an instance of
`TauCeti.morseCellAttachmentIsoOfAttachingMap`.

## Main definitions

* `TauCeti.doubleWellChart`, `TauCeti.negDoubleWellChart`: the normal-form charts
  `x ↦ ± x √(2 - x²)` of the double well on `(-1, 1)`.

## Main results

* `TauCeti.coe_doubleWellChart_morseAttachingMap`,
  `TauCeti.coe_negDoubleWellChart_morseAttachingMap`: `α_±(s) = ± s √(1 - 1/√2)`.
* `TauCeti.negDoubleWellChart_morseAttachingMap_notMem_connectedComponent`: `α_+(s)` and `α_-(s)`
  lie in different components of `M_{1/2}`.
* `TauCeti.not_homotopic_doubleWellChart_morseAttachingMap`: `α_+` and `α_-` are not homotopic.
* `TauCeti.negDoubleWellChart_morseAttachingMap`: `α_- = α_+ ∘ r` for `r = -id`.
* `TauCeti.exists_negDoubleWellChart_morseCellAttachment_iso`: the two attachments are homeomorphic
  relative to `M_{1/2}`.

## References

* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  Theorem 3.2, Remark 3.3 and Lemma 3.6.
-/

public section

noncomputable section

open Set Metric Topology CategoryTheory
open LinearIsometry (piLpExtendByZero piLpExtendByZero_castLEEmb_refl)

namespace TauCeti

/-! ### The normal-form coordinate -/

/-- The coordinate `x ↦ x √(2 - x²)` on `(-1, 1)`, with inverse `y ↦ y / √(1 + √(1 - y²))`. -/
private def doubleWellCoord : OpenPartialHomeomorph ℝ ℝ where
  toFun x := x * √(2 - x ^ 2)
  invFun y := y / √(1 + √(1 - y ^ 2))
  source := Ioo (-1) 1
  target := Ioo (-1) 1
  map_source' x hx := by
    have hx2 : x ^ 2 < 1 := by simpa [sq_lt_one_iff_abs_lt_one, abs_lt] using hx
    rw [mem_Ioo, ← abs_lt]
    refine abs_lt_of_sq_lt_sq ?_ zero_le_one
    rw [mul_pow, Real.sq_sqrt (by nlinarith)]
    nlinarith [sq_nonneg (1 - x ^ 2), mul_pos (sub_pos.2 hx2) (sub_pos.2 hx2)]
  map_target' y hy := by
    have hy2 : y ^ 2 < 1 := by simpa [sq_lt_one_iff_abs_lt_one, abs_lt] using hy
    have hs := Real.sqrt_pos.2 (sub_pos.2 hy2)
    have hs2 := Real.sq_sqrt (sub_pos.2 hy2).le
    rw [mem_Ioo, ← abs_lt]
    refine abs_lt_of_sq_lt_sq ?_ zero_le_one
    rw [div_pow, Real.sq_sqrt (by positivity), one_pow, div_lt_one (by positivity)]
    nlinarith
  left_inv' x hx := by
    have hx2 : x ^ 2 < 1 := by simpa [sq_lt_one_iff_abs_lt_one, abs_lt] using hx
    have h2 : 0 < 2 - x ^ 2 := by linarith
    have h1 : 1 - (x * √(2 - x ^ 2)) ^ 2 = (1 - x ^ 2) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt h2.le]
      ring
    rw [h1, Real.sqrt_sq (by linarith), show 1 + (1 - x ^ 2) = 2 - x ^ 2 by ring,
      mul_div_cancel_right₀ _ (Real.sqrt_pos.2 h2).ne']
  right_inv' y hy := by
    have hy2 : y ^ 2 < 1 := by simpa [sq_lt_one_iff_abs_lt_one, abs_lt] using hy
    have hs := Real.sqrt_nonneg (1 - y ^ 2)
    have hs2 := Real.sq_sqrt (sub_pos.2 hy2).le
    have ht : 0 < √(1 + √(1 - y ^ 2)) := Real.sqrt_pos.2 (by positivity)
    have hx : 2 - (y / √(1 + √(1 - y ^ 2))) ^ 2 = 1 + √(1 - y ^ 2) := by
      rw [div_pow, Real.sq_sqrt (by positivity)]
      field_simp
      nlinarith
    rw [hx, div_mul_cancel₀ _ ht.ne']
  open_source := isOpen_Ioo
  open_target := isOpen_Ioo
  continuousOn_toFun := by fun_prop
  continuousOn_invFun := by
    refine Continuous.continuousOn (continuous_id.div (by fun_prop) fun y ↦ ?_)
    exact (Real.sqrt_pos.2 (by positivity)).ne'

private theorem doubleWellCoord_symm_apply (y : ℝ) :
    doubleWellCoord.symm y = y / √(1 + √(1 - y ^ 2)) :=
  (rfl)

/-- The value of the inverse coordinate at `σ / √2`, for a sign `σ`. -/
private theorem doubleWellCoord_symm_mul_sqrt {σ : ℝ} (hσ : σ ^ 2 = 1) :
    doubleWellCoord.symm (σ * √(1 / 2)) = σ * √(1 - 1 / √2) := by
  have h2 : (0 : ℝ) < √2 := by positivity
  have hsq : √(1 / 2 : ℝ) = 1 / √2 := by rw [Real.sqrt_div' _ zero_le_two, Real.sqrt_one]
  rw [doubleWellCoord_symm_apply, mul_pow, hσ, one_mul, Real.sq_sqrt (by norm_num), mul_div_assoc,
    ← Real.sqrt_div' _ (by positivity)]
  congr 2
  rw [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num, hsq]
  field_simp
  nlinarith [Real.sq_sqrt (zero_le_two : (0 : ℝ) ≤ 2)]

/-! ### The two charts -/

/-- The normal-form chart `x ↦ x √(2 - x²)` of the double well `f x = (x² - 1)²` at its local
maximum `0`, on `(-1, 1)` with values in `ℝ¹`. In it, `f = 1 - y²`
(`TauCeti.doubleWellChart_normalForm`). -/
def doubleWellChart : OpenPartialHomeomorph ℝ (EuclideanSpace ℝ (Fin 1)) :=
  doubleWellCoord.trans
    (PiLp.equivOfUnique 2 ℝ fun _ : Fin 1 ↦ ℝ).symm.toHomeomorph.toOpenPartialHomeomorph

/-- The negative `x ↦ -x √(2 - x²)` of `TauCeti.doubleWellChart`, again a normal-form chart of the
double well at `0` (`TauCeti.negDoubleWellChart_normalForm`). -/
def negDoubleWellChart : OpenPartialHomeomorph ℝ (EuclideanSpace ℝ (Fin 1)) :=
  doubleWellChart.trans (Homeomorph.neg _).toOpenPartialHomeomorph

@[simp]
theorem doubleWellChart_source : doubleWellChart.source = Ioo (-1) 1 := by
  simp [doubleWellChart, doubleWellCoord]

@[simp]
theorem negDoubleWellChart_source : negDoubleWellChart.source = Ioo (-1) 1 := by
  simp [negDoubleWellChart]

@[simp]
theorem doubleWellChart_apply (x : ℝ) (j : Fin 1) : doubleWellChart x j = x * √(2 - x ^ 2) :=
  (rfl)

@[simp]
theorem negDoubleWellChart_apply (x : ℝ) (j : Fin 1) :
    negDoubleWellChart x j = -(x * √(2 - x ^ 2)) :=
  (rfl)

theorem doubleWellChart_symm_apply (y : EuclideanSpace ℝ (Fin 1)) :
    doubleWellChart.symm y = y 0 / √(1 + √(1 - y 0 ^ 2)) :=
  (rfl)

theorem negDoubleWellChart_symm_apply (y : EuclideanSpace ℝ (Fin 1)) :
    negDoubleWellChart.symm y = doubleWellChart.symm (-y) :=
  (rfl)

/-- The target of `TauCeti.doubleWellChart` is the interval `(-1, 1)` of `ℝ¹`. -/
@[simp]
theorem mem_doubleWellChart_target {y : EuclideanSpace ℝ (Fin 1)} :
    y ∈ doubleWellChart.target ↔ -1 < y 0 ∧ y 0 < 1 := by
  simp [doubleWellChart, doubleWellCoord]

/-- The target of `TauCeti.negDoubleWellChart` is the interval `(-1, 1)` of `ℝ¹`. -/
@[simp]
theorem mem_negDoubleWellChart_target {y : EuclideanSpace ℝ (Fin 1)} :
    y ∈ negDoubleWellChart.target ↔ -1 < y 0 ∧ y 0 < 1 := by
  simp only [negDoubleWellChart, OpenPartialHomeomorph.trans_target,
    Homeomorph.toOpenPartialHomeomorph_target, Homeomorph.toOpenPartialHomeomorph_symm_apply,
    univ_inter, mem_preimage, Homeomorph.symm_neg, Homeomorph.coe_neg, mem_doubleWellChart_target,
    PiLp.neg_apply]
  constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith

/-- The target of `TauCeti.doubleWellChart` contains the closed ball of radius `√(1/2)`. -/
theorem closedBall_subset_doubleWellChart_target :
    closedBall 0 √(1 / 2) ⊆ doubleWellChart.target := by
  intro y hy
  have hle : |y 0| ≤ √(1 / 2) := by
    simpa using (PiLp.norm_apply_le y 0).trans (mem_closedBall_zero_iff.1 hy)
  have hlt : √(1 / 2 : ℝ) < 1 := by
    rw [Real.sqrt_lt' zero_lt_one]
    norm_num
  exact mem_doubleWellChart_target.2 (abs_lt.1 (hle.trans_lt hlt))

/-- The target of `TauCeti.negDoubleWellChart` contains the closed ball of radius `√(1/2)`. -/
theorem closedBall_subset_negDoubleWellChart_target :
    closedBall 0 √(1 / 2) ⊆ negDoubleWellChart.target := fun _ hy ↦
  mem_negDoubleWellChart_target.2
    (mem_doubleWellChart_target.1 (closedBall_subset_doubleWellChart_target hy))

/-- In `TauCeti.doubleWellChart` the double well has the normal form `f = 1 - y²` of index `1`. -/
theorem doubleWellChart_normalForm : ∀ x ∈ doubleWellChart.source,
    (x ^ 2 - 1) ^ 2 =
      1 + ∑ j : Fin 1, (if j.val < 1 then -1 else 1) * doubleWellChart x j ^ 2 := by
  intro x hx
  rw [doubleWellChart_source, mem_Ioo] at hx
  simp only [Fin.sum_univ_one, Fin.val_zero, zero_lt_one, ↓reduceIte, doubleWellChart_apply,
    mul_pow, Real.sq_sqrt (show 0 ≤ 2 - x ^ 2 by nlinarith)]
  ring

/-- In `TauCeti.negDoubleWellChart` the double well has the normal form `f = 1 - y²` of index
`1`. -/
theorem negDoubleWellChart_normalForm : ∀ x ∈ negDoubleWellChart.source,
    (x ^ 2 - 1) ^ 2 =
      1 + ∑ j : Fin 1, (if j.val < 1 then -1 else 1) * negDoubleWellChart x j ^ 2 := by
  intro x hx
  simpa [neg_sq] using doubleWellChart_normalForm x (by simpa using hx)

/-! ### The attaching maps -/

/-- The attaching map `α_+ : S⁰ → M_{1/2}` of the cell of `TauCeti.doubleWellChart` is
`s ↦ s √(1 - 1/√2)`. -/
theorem coe_doubleWellChart_morseAttachingMap (s : TopCat.diskBoundary.{0} 1) :
    (doubleWellChart.morseAttachingMap le_rfl (by norm_num : (0 : ℝ) ≤ 1 / 2)
        closedBall_subset_doubleWellChart_target doubleWellChart_normalForm s : ℝ) =
      ((s : ULift.{0} (sphere (0 : EuclideanSpace ℝ (Fin 1)) 1)).down :
        EuclideanSpace ℝ (Fin 1)) 0 * √(1 - 1 / √2) := by
  rw [OpenPartialHomeomorph.coe_morseAttachingMap_apply,
    OpenPartialHomeomorph.morseCellMap_def, doubleWellChart_symm_apply,
    piLpExtendByZero_castLEEmb_refl, PiLp.smul_apply, smul_eq_mul, mul_comm √(1 / 2),
    ← doubleWellCoord_symm_mul_sqrt (sq_diskBoundary_one_apply_zero s), doubleWellCoord_symm_apply]

/-- The attaching map `α_- : S⁰ → M_{1/2}` of the cell of `TauCeti.negDoubleWellChart` is
`s ↦ -s √(1 - 1/√2)`. -/
theorem coe_negDoubleWellChart_morseAttachingMap (s : TopCat.diskBoundary.{0} 1) :
    (negDoubleWellChart.morseAttachingMap le_rfl (by norm_num : (0 : ℝ) ≤ 1 / 2)
        closedBall_subset_negDoubleWellChart_target negDoubleWellChart_normalForm s : ℝ) =
      -(((s : ULift.{0} (sphere (0 : EuclideanSpace ℝ (Fin 1)) 1)).down :
        EuclideanSpace ℝ (Fin 1)) 0 * √(1 - 1 / √2)) := by
  have hs : (-((s : ULift.{0} (sphere (0 : EuclideanSpace ℝ (Fin 1)) 1)).down :
      EuclideanSpace ℝ (Fin 1)) 0) ^ 2 = 1 := by
    rw [neg_sq, sq_diskBoundary_one_apply_zero]
  rw [OpenPartialHomeomorph.coe_morseAttachingMap_apply,
    OpenPartialHomeomorph.morseCellMap_def, negDoubleWellChart_symm_apply,
    doubleWellChart_symm_apply, PiLp.neg_apply, piLpExtendByZero_castLEEmb_refl, PiLp.smul_apply,
    smul_eq_mul, mul_comm √(1 / 2), ← neg_mul, ← neg_mul, ← doubleWellCoord_symm_mul_sqrt hs,
    doubleWellCoord_symm_apply]

/-- The attaching maps of the two charts differ strictly by the reflection `r = -id` of `D¹`:
`α_- = α_+ ∘ r`. -/
theorem negDoubleWellChart_morseAttachingMap :
    negDoubleWellChart.morseAttachingMap le_rfl (by norm_num : (0 : ℝ) ≤ 1 / 2)
        closedBall_subset_negDoubleWellChart_target negDoubleWellChart_normalForm =
      diskBoundaryNeg 1 ≫ doubleWellChart.morseAttachingMap le_rfl (by norm_num)
        closedBall_subset_doubleWellChart_target doubleWellChart_normalForm := by
  ext s
  rw [ConcreteCategory.comp_apply, coe_negDoubleWellChart_morseAttachingMap,
    coe_doubleWellChart_morseAttachingMap, diskBoundaryNeg_apply_down]
  simp [neg_mul]

/-- For each `s ∈ S⁰`, the points `α_+(s)` and `α_-(s)` lie in different connected components of
the lower sublevel `M_{1/2} = {f ≤ 1/2}`: they lie on opposite sides of `0`, where `f = 1`. -/
theorem negDoubleWellChart_morseAttachingMap_notMem_connectedComponent
    (s : TopCat.diskBoundary.{0} 1) :
    negDoubleWellChart.morseAttachingMap le_rfl (by norm_num : (0 : ℝ) ≤ 1 / 2)
        closedBall_subset_negDoubleWellChart_target negDoubleWellChart_normalForm s ∉
      connectedComponent (doubleWellChart.morseAttachingMap le_rfl (by norm_num)
        closedBall_subset_doubleWellChart_target doubleWellChart_normalForm s) := by
  intro hmem
  set p := doubleWellChart.morseAttachingMap le_rfl (by norm_num : (0 : ℝ) ≤ 1 / 2)
    closedBall_subset_doubleWellChart_target doubleWellChart_normalForm s
  set q := negDoubleWellChart.morseAttachingMap le_rfl (by norm_num : (0 : ℝ) ≤ 1 / 2)
    closedBall_subset_negDoubleWellChart_target negDoubleWellChart_normalForm s
  have hpq : (q : ℝ) = -(p : ℝ) := by
    rw [coe_negDoubleWellChart_morseAttachingMap, coe_doubleWellChart_morseAttachingMap]
  -- The image of the component in `ℝ` is an interval containing `p` and `-p`, hence `0`.
  have hconn : _root_.IsPreconnected ((↑) '' connectedComponent p : Set ℝ) :=
    isPreconnected_connectedComponent.image _ continuous_subtype_val.continuousOn
  have h0 : (0 : ℝ) ∈ (↑) '' connectedComponent p := by
    rcases le_total (p : ℝ) 0 with h | h
    · exact hconn.Icc_subset (mem_image_of_mem _ mem_connectedComponent)
        (mem_image_of_mem _ hmem) ⟨h, by rw [hpq]; linarith⟩
    · exact hconn.Icc_subset (mem_image_of_mem _ hmem)
        (mem_image_of_mem _ mem_connectedComponent) ⟨by rw [hpq]; linarith, h⟩
  obtain ⟨x, -, hx⟩ := h0
  have hfx : ((x : ℝ) ^ 2 - 1) ^ 2 ≤ 1 - 1 / 2 := x.2
  rw [hx] at hfx
  norm_num at hfx

/-- **The attaching maps of the two charts are not homotopic** as maps `S⁰ → M_{1/2}` of the
labelled sphere: a homotopy would move `α_+(s)` to `α_-(s)` within a connected component of
`M_{1/2}`. -/
theorem not_homotopic_doubleWellChart_morseAttachingMap :
    ¬ ContinuousMap.Homotopic
      (doubleWellChart.morseAttachingMap le_rfl (by norm_num : (0 : ℝ) ≤ 1 / 2)
        closedBall_subset_doubleWellChart_target doubleWellChart_normalForm).hom
      (negDoubleWellChart.morseAttachingMap le_rfl (by norm_num : (0 : ℝ) ≤ 1 / 2)
        closedBall_subset_negDoubleWellChart_target negDoubleWellChart_normalForm).hom := by
  rintro ⟨H⟩
  let s : TopCat.diskBoundary.{0} 1 :=
    ULift.up ⟨EuclideanSpace.single 0 1, by simp⟩
  refine negDoubleWellChart_morseAttachingMap_notMem_connectedComponent s ?_
  have hpath : _root_.IsPreconnected (range fun t ↦ H (t, s)) :=
    isPreconnected_range (H.continuous.comp (Continuous.prodMk_left s))
  exact hpath.subset_connectedComponent ⟨0, H.apply_zero s⟩ ⟨1, H.apply_one s⟩

/-! ### The two attachments -/

/-- **The attachments of the two charts are homeomorphic relative to the lower sublevel.** The map
`M_{1/2} ∪_{α_-} D¹ → M_{1/2} ∪_{α_+} D¹` which is the identity on `M_{1/2}` and the reflection
`r = -id` on the disc is a homeomorphism, because `α_- = α_+ ∘ r` holds strictly. -/
theorem exists_negDoubleWellChart_morseCellAttachment_iso :
    ∃ e : morseCellAttachment (fun _ : PUnit.{1} ↦ negDoubleWellChart) (fun _ ↦ 1)
        (fun _ ↦ le_rfl) (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (fun _ ↦ closedBall_subset_negDoubleWellChart_target)
        (fun _ ↦ negDoubleWellChart_normalForm) ≅
      morseCellAttachment (fun _ : PUnit.{1} ↦ doubleWellChart) (fun _ ↦ 1) (fun _ ↦ le_rfl)
        (by norm_num : (0 : ℝ) ≤ 1 / 2) (fun _ ↦ closedBall_subset_doubleWellChart_target)
        (fun _ ↦ doubleWellChart_normalForm),
      morseCellAttachmentIncl (fun _ ↦ negDoubleWellChart) (fun _ ↦ 1) _ _ _ _ ≫ e.hom =
          morseCellAttachmentIncl (fun _ ↦ doubleWellChart) (fun _ ↦ 1) _ _ _ _ ∧
        ∀ i, morseCellAttachmentCell (fun _ ↦ negDoubleWellChart) (fun _ ↦ 1) _ _ _ _ i ≫ e.hom =
          (diskNeg 1).hom ≫
            morseCellAttachmentCell (fun _ ↦ doubleWellChart) (fun _ ↦ 1) _ _ _ _ i := by
  exact ⟨morseCellAttachmentIsoOfAttachingMap _ _ _ _ _ _ _ _ _ (fun _ ↦ diskNeg 1)
      (fun _ ↦ diskBoundaryNegIso 1)
      (fun _ ↦ by rw [diskBoundaryNegIso_hom]; exact diskBoundaryNeg_comp_diskBoundaryInclusion 1)
      (fun _ ↦ by rw [diskBoundaryNegIso_hom]; exact negDoubleWellChart_morseAttachingMap),
    by simp, fun _ ↦ by simp⟩

end TauCeti
