/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Cell.Strict
public import TauCeti.Geometry.Manifold.Morse.CriticalPoints

/-!
# Morse cells of the double-well function

The double-well function `f(x) = (x² - 1)²` on `ℝ` has minima at `±1`, at the level `0`, and a
local maximum at `0`, at the level `1`. This file works out the cell attached at that maximum
for the width `ε = 1/2`, in two different normal-form charts, as a concrete test of the attaching
maps `OpenPartialHomeomorph.morseAttachingMap` and the cell attachments
`TauCeti.morseCellAttachment`.

In the charts `ψ± : x ↦ ±x √(2 - x²)` of `(-1, 1)` the function reads `f = 1 - y²`, so `0` is a
critical point of index `1`. The width `ε = 1/2` is admissible: the band `f⁻¹[1/2, 3/2]` is
compact (`TauCeti.isCompact_doubleWell_preimage_Icc`), its only critical point is `0`
(`TauCeti.criticalPoints_doubleWell_inter_preimage_Icc`), and both chart targets contain the
closed ball of radius `√(1/2)`. The attaching maps `α± : S⁰ → {f ≤ 1/2}` of the two charts are

`α±(s) = ±s √(1 - 1/√2)`.

The lower sublevel `{f ≤ 1/2}` consists of two intervals, one on each side of the omitted point
`0`, and `α₊(1)`, `α₋(1)` lie in different ones. So `α₊` and `α₋` are not homotopic with their
labelled source fixed, even though the two charts present the same critical point. They differ
instead by the reflection `r = -id` of the disc, strictly: `α₋ = α₊ ∘ r`. Hence the identity on
`{f ≤ 1/2}` together with `r` on the disc is a homeomorphism between the two cell attachments,
relative to the lower sublevel (`TauCeti.morseCellAttachmentIso`). The characteristic maps
are strictly related by the same reflection, `χ₋ = χ₊ ∘ r`, so this homeomorphism also
intertwines the handle-to-cell comparisons into `{f ≤ 3/2}`. The comparison of cell
attachments in different charts must therefore allow a reparametrization of the disc: the
attaching map alone is not determined up to homotopy by the critical point.

## Main results

* `TauCeti.coe_morseAttachingMap_doubleWellChart_apply`,
  `TauCeti.coe_morseAttachingMap_doubleWellNegChart_apply`: the attaching maps
  `α±(s) = ±s √(1 - 1/√2)`.
* `TauCeti.not_homotopic_morseAttachingMap_doubleWellChart_doubleWellNegChart`: `α₊` and `α₋`
  are not homotopic.
* `TauCeti.morseAttachingMap_doubleWellNegChart`: `α₋ = α₊ ∘ r` for the reflection `r = -id`.
* `TauCeti.morseCharacteristicMap_doubleWellNegChart`: `χ₋ = χ₊ ∘ r`.
* `TauCeti.exists_iso_morseCellAttachment_doubleWellNegChart_doubleWellChart`: the two cell
  attachments are homeomorphic relative to `{f ≤ 1/2}`, by the identity and `r`, compatibly with
  the handle-to-cell comparisons.
* `TauCeti.criticalPoints_doubleWell`, `TauCeti.isCompact_doubleWell_preimage_Icc` and
  `TauCeti.criticalPoints_doubleWell_inter_preimage_Icc`: the width `ε = 1/2` is admissible.

## References

* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  Theorem 3.2 and Lemma 3.6.
-/

public section

noncomputable section

open Set Metric CategoryTheory
open scoped Manifold

namespace TauCeti

/-- The double-well function `x ↦ (x² - 1)²` on `ℝ`. -/
def doubleWell (x : ℝ) : ℝ := (x ^ 2 - 1) ^ 2

/-- `TauCeti.doubleWell x` is `(x² - 1)²`. -/
theorem doubleWell_def (x : ℝ) : doubleWell x = (x ^ 2 - 1) ^ 2 := (rfl)

private theorem sqrt_one_sub_sq_mul (x : ℝ) (hx : x ∈ Ioo (-1 : ℝ) 1) :
    √(1 - (x * √(2 - x ^ 2)) ^ 2) = 1 - x ^ 2 := by
  have hx2 : x ^ 2 < 1 := by nlinarith [hx.1, hx.2]
  have h : 1 - (x * √(2 - x ^ 2)) ^ 2 = (1 - x ^ 2) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by nlinarith)]
    ring
  rw [h]
  exact Real.sqrt_sq (by linarith)

/-- The coordinate `y = x √(2 - x²)` on `(-1, 1)`, in which `doubleWell = 1 - y²`. It is a
homeomorphism of `(-1, 1)` onto itself with inverse `y ↦ y / √(1 + √(1 - y²))`. -/
def doubleWellCoord : OpenPartialHomeomorph ℝ ℝ where
  toFun x := x * √(2 - x ^ 2)
  invFun y := y / √(1 + √(1 - y ^ 2))
  source := Ioo (-1) 1
  target := Ioo (-1) 1
  map_source' x hx := by
    have hx2 : x ^ 2 < 1 := by nlinarith [hx.1, hx.2]
    have h0 : 0 ≤ 2 - x ^ 2 := by nlinarith
    have : (x * √(2 - x ^ 2)) ^ 2 < 1 := by
      rw [mul_pow, Real.sq_sqrt h0]; nlinarith
    rw [mem_Ioo, ← abs_lt, ← sq_lt_one_iff_abs_lt_one]; exact this
  map_target' y hy := by
    have hy2 : y ^ 2 < 1 := by nlinarith [hy.1, hy.2]
    have hs : 0 < 1 + √(1 - y ^ 2) := by positivity
    rw [mem_Ioo, ← abs_lt, ← sq_lt_one_iff_abs_lt_one, div_pow, Real.sq_sqrt hs.le,
      div_lt_one hs]
    nlinarith [Real.sqrt_nonneg (1 - y ^ 2)]
  left_inv' x hx := by
    have hx2 : x ^ 2 < 1 := by nlinarith [hx.1, hx.2]
    have h : 1 + √(1 - (x * √(2 - x ^ 2)) ^ 2) = 2 - x ^ 2 := by
      rw [sqrt_one_sub_sq_mul x hx]
      ring
    have h0 : √(2 - x ^ 2) ≠ 0 := (Real.sqrt_pos.2 (by linarith)).ne'
    rw [h]
    field_simp
  right_inv' y hy := by
    have hy2 : y ^ 2 < 1 := by nlinarith [hy.1, hy.2]
    have hs : 0 < 1 + √(1 - y ^ 2) := by positivity
    have hsq : √(1 - y ^ 2) ^ 2 = 1 - y ^ 2 := Real.sq_sqrt (by linarith)
    rw [div_pow, Real.sq_sqrt hs.le]
    have : 2 - y ^ 2 / (1 + √(1 - y ^ 2)) = 1 + √(1 - y ^ 2) := by
      field_simp
      nlinarith
    rw [this, div_mul_cancel₀ _ (Real.sqrt_pos.2 hs).ne']
  open_source := isOpen_Ioo
  open_target := isOpen_Ioo
  continuousOn_toFun := by fun_prop
  continuousOn_invFun := (continuous_id.div (by fun_prop) fun y ↦
    (Real.sqrt_pos.2 (by positivity)).ne').continuousOn

@[simp]
theorem doubleWellCoord_apply (x : ℝ) : doubleWellCoord x = x * √(2 - x ^ 2) := (rfl)

@[simp]
theorem doubleWellCoord_symm_apply (y : ℝ) :
    doubleWellCoord.symm y = y / √(1 + √(1 - y ^ 2)) := (rfl)

@[simp]
theorem doubleWellCoord_source : doubleWellCoord.source = Ioo (-1) 1 := (rfl)

@[simp]
theorem doubleWellCoord_target : doubleWellCoord.target = Ioo (-1) 1 := (rfl)

/-- The normal-form chart `ψ₊ : x ↦ x √(2 - x²)` of the double-well function at its local maximum
`0`, from `(-1, 1)` onto the open unit ball of `ℝ¹ = EuclideanSpace ℝ (Fin 1)`. In it
`doubleWell = 1 - y²` (`TauCeti.doubleWell_eq_one_add_sum_doubleWellChart`), so `0` is a critical
point of index `1` at the level `1`. -/
def doubleWellChart : OpenPartialHomeomorph ℝ (EuclideanSpace ℝ (Fin 1)) :=
  doubleWellCoord.transHomeomorph (PiLp.equivOfUnique 2 ℝ fun _ : Fin 1 ↦ ℝ).symm.toHomeomorph

@[simp]
theorem doubleWellChart_apply (x : ℝ) (j : Fin 1) :
    doubleWellChart x j = x * √(2 - x ^ 2) := (rfl)

@[simp]
theorem doubleWellChart_source : doubleWellChart.source = Ioo (-1) 1 := (rfl)

/-- The chart `ψ₊` maps `(-1, 1)` onto the open unit ball of `ℝ¹`. -/
@[simp]
theorem doubleWellChart_target : doubleWellChart.target = ball 0 1 := by
  ext y
  simp [doubleWellChart, EuclideanSpace.norm_eq, Real.sqrt_sq_eq_abs, abs_lt]

/-- The inverse of `ψ₊` is the inverse of `TauCeti.doubleWellCoord` on the coordinate. -/
@[simp]
theorem doubleWellChart_symm_apply (y : EuclideanSpace ℝ (Fin 1)) :
    doubleWellChart.symm y = doubleWellCoord.symm (y 0) := (rfl)

/-- The double-well function reads `1 - y²` in the chart `ψ₊`. -/
theorem doubleWell_eq_one_add_sum_doubleWellChart :
    ∀ x ∈ doubleWellChart.source, doubleWell x =
      1 + ∑ j : Fin 1, (if j.val < 1 then -1 else 1) * doubleWellChart x j ^ 2 := by
  intro x hx
  rw [doubleWellChart_source, mem_Ioo] at hx
  have h0 : 0 ≤ 2 - x ^ 2 := by nlinarith
  simp only [Fin.sum_univ_one, doubleWellChart_apply, Fin.val_zero, zero_lt_one, ite_true,
    mul_pow, Real.sq_sqrt h0, doubleWell_def]
  ring

/-- The target of `ψ₊` contains the closed ball of radius `√(1/2)`, so the width `ε = 1/2` fits the
chart. -/
theorem closedBall_subset_doubleWellChart_target :
    closedBall 0 √(1 / 2) ⊆ doubleWellChart.target := by
  rw [doubleWellChart_target]
  refine closedBall_subset_ball ?_
  rw [Real.sqrt_lt' one_pos]
  norm_num

/-- The opposite normal-form chart `ψ₋ : x ↦ -x √(2 - x²)` of the double-well function at `0`,
the chart `ψ₊` followed by the reflection of `ℝ¹`. -/
def doubleWellNegChart : OpenPartialHomeomorph ℝ (EuclideanSpace ℝ (Fin 1)) :=
  doubleWellChart.transHomeomorph (LinearIsometryEquiv.neg ℝ).toHomeomorph

@[simp]
theorem doubleWellNegChart_apply (x : ℝ) (j : Fin 1) :
    doubleWellNegChart x j = -(x * √(2 - x ^ 2)) := (rfl)

@[simp]
theorem doubleWellNegChart_source : doubleWellNegChart.source = Ioo (-1) 1 := (rfl)

/-- The chart `ψ₋` maps `(-1, 1)` onto the open unit ball of `ℝ¹`. -/
@[simp]
theorem doubleWellNegChart_target : doubleWellNegChart.target = ball 0 1 := by
  ext y
  simp [doubleWellNegChart, doubleWellChart_target]

/-- The inverse of `ψ₋` is the inverse of `TauCeti.doubleWellCoord` on the negated coordinate. -/
@[simp]
theorem doubleWellNegChart_symm_apply (y : EuclideanSpace ℝ (Fin 1)) :
    doubleWellNegChart.symm y = doubleWellCoord.symm (-y 0) := (rfl)

/-- The double-well function reads `1 - y²` in the chart `ψ₋`. -/
theorem doubleWell_eq_one_add_sum_doubleWellNegChart :
    ∀ x ∈ doubleWellNegChart.source, doubleWell x =
      1 + ∑ j : Fin 1, (if j.val < 1 then -1 else 1) * doubleWellNegChart x j ^ 2 := by
  intro x hx
  simpa only [doubleWellNegChart_apply, doubleWellChart_apply, neg_sq] using
    doubleWell_eq_one_add_sum_doubleWellChart x hx

/-- The target of `ψ₋` contains the closed ball of radius `√(1/2)`. -/
theorem closedBall_subset_doubleWellNegChart_target :
    closedBall 0 √(1 / 2) ⊆ doubleWellNegChart.target :=
  doubleWellNegChart_target ▸ doubleWellChart_target ▸ closedBall_subset_doubleWellChart_target

private theorem doubleWellCoord_symm_mul_sqrt {t : ℝ} (ht : t ^ 2 = 1) :
    doubleWellCoord.symm (t * √(1 / 2)) = t * √(1 - 1 / √2) := by
  have hs : √(1 / 2) = 1 / √2 := by
    rw [Real.sqrt_div' 1 zero_le_two, Real.sqrt_one]
  have h2 : √2 ^ 2 = 2 := Real.sq_sqrt zero_le_two
  have h2pos : 0 < √2 := by positivity
  have hinner : √(1 - (t * √(1 / 2)) ^ 2) = 1 / √2 := by
    rw [mul_pow, ht, one_mul, Real.sq_sqrt (by norm_num), ← hs]
    norm_num
  have hq0 : 0 ≤ 1 - 1 / √2 := by
    rw [sub_nonneg, div_le_one h2pos]
    nlinarith
  have hq : (1 - 1 / √2) * (1 + 1 / √2) = 1 / 2 := by
    field_simp
    nlinarith
  have hprod : √(1 - 1 / √2) * √(1 + 1 / √2) = 1 / √2 := by
    rw [← Real.sqrt_mul hq0, hq, hs]
  rw [doubleWellCoord_symm_apply, hinner, div_eq_iff (by positivity), mul_assoc, hprod, hs]

private theorem smul_piLpExtendByZero_apply_zero (ε : ℝ) (w : EuclideanSpace ℝ (Fin 1)) :
    (√ε • LinearIsometry.piLpExtendByZero 2 ℝ ℝ (Fin.castLEEmb le_rfl) w) 0 = √ε * w 0 := by
  rw [PiLp.smul_apply, LinearIsometry.piLpExtendByZero_castLEEmb_apply]
  simp

/-- The cell parametrization of `ψ₊` is `w ↦ ψ₊⁻¹(√ε w)`. -/
theorem morseCellMap_doubleWellChart (ε : ℝ) (w : EuclideanSpace ℝ (Fin 1)) :
    doubleWellChart.morseCellMap le_rfl ε w = doubleWellCoord.symm (√ε * w 0) := by
  rw [OpenPartialHomeomorph.morseCellMap_def, doubleWellChart_symm_apply,
    smul_piLpExtendByZero_apply_zero]

/-- The cell parametrization of `ψ₋` is `w ↦ ψ₊⁻¹(-√ε w)`. -/
theorem morseCellMap_doubleWellNegChart (ε : ℝ) (w : EuclideanSpace ℝ (Fin 1)) :
    doubleWellNegChart.morseCellMap le_rfl ε w = doubleWellCoord.symm (-(√ε * w 0)) := by
  rw [OpenPartialHomeomorph.morseCellMap_def, doubleWellNegChart_symm_apply,
    smul_piLpExtendByZero_apply_zero]

/-- The attaching map `α₊ : S⁰ → {doubleWell ≤ 1/2}` of the chart `ψ₊` at the level `c = 1` with
width `ε = 1/2` is `α₊(s) = s √(1 - 1/√2)`. -/
@[simp]
theorem coe_morseAttachingMap_doubleWellChart_apply (s : TopCat.diskBoundary.{0} 1) :
    (doubleWellChart.morseAttachingMap le_rfl one_half_pos.le
      closedBall_subset_doubleWellChart_target doubleWell_eq_one_add_sum_doubleWellChart s : ℝ) =
      (s.down : EuclideanSpace ℝ (Fin 1)) 0 * √(1 - 1 / √2) := by
  rw [OpenPartialHomeomorph.coe_morseAttachingMap_apply, morseCellMap_doubleWellChart, mul_comm,
    doubleWellCoord_symm_mul_sqrt (sq_diskBoundary_one_eq_one s)]

/-- The attaching map `α₋ : S⁰ → {doubleWell ≤ 1/2}` of the chart `ψ₋` at the level `c = 1` with
width `ε = 1/2` is `α₋(s) = -s √(1 - 1/√2)`. -/
@[simp]
theorem coe_morseAttachingMap_doubleWellNegChart_apply (s : TopCat.diskBoundary.{0} 1) :
    (doubleWellNegChart.morseAttachingMap le_rfl one_half_pos.le
      closedBall_subset_doubleWellNegChart_target doubleWell_eq_one_add_sum_doubleWellNegChart
      s : ℝ) = -((s.down : EuclideanSpace ℝ (Fin 1)) 0 * √(1 - 1 / √2)) := by
  rw [OpenPartialHomeomorph.coe_morseAttachingMap_apply, morseCellMap_doubleWellNegChart,
    mul_comm, ← neg_mul, doubleWellCoord_symm_mul_sqrt (by rw [neg_sq, sq_diskBoundary_one_eq_one]),
    neg_mul]

/-- The two attaching maps `α₊` and `α₋` are not homotopic as maps `S⁰ → {doubleWell ≤ 1/2}` with
their labelled source fixed. Their values `±√(1 - 1/√2)` at `s = 1` lie on either side of the
point `0`, which the sublevel omits. -/
theorem not_homotopic_morseAttachingMap_doubleWellChart_doubleWellNegChart :
    ¬ (doubleWellChart.morseAttachingMap le_rfl one_half_pos.le
        closedBall_subset_doubleWellChart_target
        doubleWell_eq_one_add_sum_doubleWellChart).hom.Homotopic
      (doubleWellNegChart.morseAttachingMap le_rfl one_half_pos.le
        closedBall_subset_doubleWellNegChart_target
        doubleWell_eq_one_add_sum_doubleWellNegChart).hom := by
  rintro ⟨H⟩
  let s₁ : TopCat.diskBoundary.{0} 1 := ULift.up ⟨EuclideanSpace.single 0 1, by simp⟩
  have hs₁ : (s₁.down : EuclideanSpace ℝ (Fin 1)) 0 = 1 := by simp [s₁]
  have ha : 0 < √(1 - 1 / √2) := Real.sqrt_pos.2 <| sub_pos.2 <|
    (div_lt_one (by positivity)).2 (Real.lt_sqrt zero_le_one |>.2 (by norm_num))
  let γ : unitInterval → ℝ := fun t ↦ (H (t, s₁) : ℝ)
  have hγ : Continuous γ := continuous_subtype_val.comp (H.continuous.comp (by fun_prop))
  have h0 : γ 0 = √(1 - 1 / √2) := by
    simp only [γ, ContinuousMap.Homotopy.apply_zero]
    rw [coe_morseAttachingMap_doubleWellChart_apply, hs₁, one_mul]
  have h1 : γ 1 = -√(1 - 1 / √2) := by
    simp only [γ, ContinuousMap.Homotopy.apply_one]
    rw [coe_morseAttachingMap_doubleWellNegChart_apply, hs₁, one_mul]
  have h01 : (0 : ℝ) ∈ Icc (γ 1) (γ 0) := by
    rw [h0, h1]
    exact ⟨by linarith, ha.le⟩
  obtain ⟨t, ht⟩ := intermediate_value_univ 1 0 hγ h01
  -- The value of the homotopy at `(t, s₁)` lies in the sublevel `{doubleWell ≤ 1/2}`.
  have hmem : doubleWell (H (t, s₁) : ℝ) ≤ 1 - 1 / 2 := (H (t, s₁)).2
  have ht0 : (H (t, s₁) : ℝ) = 0 := ht
  rw [ht0, doubleWell_def] at hmem
  norm_num at hmem

/-- The attaching maps of the two charts differ strictly by the reflection `r = -id` of the disc:
`α₋ = α₊ ∘ r` on `S⁰`. -/
theorem morseAttachingMap_doubleWellNegChart :
    doubleWellNegChart.morseAttachingMap le_rfl one_half_pos.le
        closedBall_subset_doubleWellNegChart_target
        doubleWell_eq_one_add_sum_doubleWellNegChart =
      diskBoundaryNeg 1 ≫ doubleWellChart.morseAttachingMap le_rfl one_half_pos.le
        closedBall_subset_doubleWellChart_target doubleWell_eq_one_add_sum_doubleWellChart := by
  ext s
  rw [ConcreteCategory.comp_apply, coe_morseAttachingMap_doubleWellNegChart_apply,
    coe_morseAttachingMap_doubleWellChart_apply, diskBoundaryNeg_apply_down]
  simp [neg_mul]

/-- The characteristic maps of the two charts differ strictly by the reflection `r = -id` of the
disc: `χ₋ = χ₊ ∘ r` on `D¹`. -/
theorem morseCharacteristicMap_doubleWellNegChart :
    doubleWellNegChart.morseCharacteristicMap le_rfl one_half_pos.le
        closedBall_subset_doubleWellNegChart_target
        doubleWell_eq_one_add_sum_doubleWellNegChart =
      (LinearIsometryEquiv.neg ℝ).diskIso.hom ≫ doubleWellChart.morseCharacteristicMap le_rfl
        one_half_pos.le closedBall_subset_doubleWellChart_target
        doubleWell_eq_one_add_sum_doubleWellChart := by
  ext w
  rw [ConcreteCategory.comp_apply, OpenPartialHomeomorph.coe_morseCharacteristicMap_apply,
    OpenPartialHomeomorph.coe_morseCharacteristicMap_apply, morseCellMap_doubleWellNegChart,
    morseCellMap_doubleWellChart, LinearIsometryEquiv.coe_diskIso_hom_apply_down]
  simp

/-- Since `α₋ = α₊ ∘ r` strictly, the map which is the identity on `{doubleWell ≤ 1/2}` and the
reflection `r = -id` on the disc is a homeomorphism between the two cell attachments
`{doubleWell ≤ 1/2} ∪_{α₋} D¹ ≅ {doubleWell ≤ 1/2} ∪_{α₊} D¹`, relative to the lower sublevel.
Since also `χ₋ = χ₊ ∘ r`, it intertwines the handle-to-cell comparisons into
`{doubleWell ≤ 3/2}`. -/
theorem exists_iso_morseCellAttachment_doubleWellNegChart_doubleWellChart :
    ∃ Φ : morseCellAttachment (fun _ : Unit ↦ doubleWellNegChart) (fun _ ↦ 1) (fun _ ↦ le_rfl)
        one_half_pos.le (fun _ ↦ closedBall_subset_doubleWellNegChart_target)
        (fun _ ↦ doubleWell_eq_one_add_sum_doubleWellNegChart) ≅
      morseCellAttachment (fun _ : Unit ↦ doubleWellChart) (fun _ ↦ 1) (fun _ ↦ le_rfl)
        one_half_pos.le (fun _ ↦ closedBall_subset_doubleWellChart_target)
        (fun _ ↦ doubleWell_eq_one_add_sum_doubleWellChart),
      morseCellAttachmentIncl (fun _ : Unit ↦ doubleWellNegChart) (fun _ ↦ 1) (fun _ ↦ le_rfl)
          one_half_pos.le (fun _ ↦ closedBall_subset_doubleWellNegChart_target)
          (fun _ ↦ doubleWell_eq_one_add_sum_doubleWellNegChart) ≫ Φ.hom =
        morseCellAttachmentIncl (fun _ : Unit ↦ doubleWellChart) (fun _ ↦ 1) (fun _ ↦ le_rfl)
          one_half_pos.le (fun _ ↦ closedBall_subset_doubleWellChart_target)
          (fun _ ↦ doubleWell_eq_one_add_sum_doubleWellChart) ∧
      morseCellAttachmentCell (fun _ : Unit ↦ doubleWellNegChart) (fun _ ↦ 1) (fun _ ↦ le_rfl)
          one_half_pos.le (fun _ ↦ closedBall_subset_doubleWellNegChart_target)
          (fun _ ↦ doubleWell_eq_one_add_sum_doubleWellNegChart) () ≫ Φ.hom =
        (LinearIsometryEquiv.neg ℝ).diskIso.hom ≫
          morseCellAttachmentCell (fun _ : Unit ↦ doubleWellChart) (fun _ ↦ 1) (fun _ ↦ le_rfl)
            one_half_pos.le (fun _ ↦ closedBall_subset_doubleWellChart_target)
            (fun _ ↦ doubleWell_eq_one_add_sum_doubleWellChart) () ∧
      Φ.hom ≫ morseCellComparison (fun _ : Unit ↦ doubleWellChart) (fun _ ↦ 1) (fun _ ↦ le_rfl)
          one_half_pos.le (fun _ ↦ closedBall_subset_doubleWellChart_target)
          (fun _ ↦ doubleWell_eq_one_add_sum_doubleWellChart) =
        morseCellComparison (fun _ : Unit ↦ doubleWellNegChart) (fun _ ↦ 1) (fun _ ↦ le_rfl)
          one_half_pos.le (fun _ ↦ closedBall_subset_doubleWellNegChart_target)
          (fun _ ↦ doubleWell_eq_one_add_sum_doubleWellNegChart) := by
  have hα : ∀ _ : Unit, doubleWellNegChart.morseAttachingMap le_rfl one_half_pos.le
        closedBall_subset_doubleWellNegChart_target
        doubleWell_eq_one_add_sum_doubleWellNegChart =
      (LinearIsometryEquiv.neg ℝ).diskBoundaryIso.hom ≫ doubleWellChart.morseAttachingMap le_rfl
        one_half_pos.le closedBall_subset_doubleWellChart_target
        doubleWell_eq_one_add_sum_doubleWellChart := fun _ ↦ by
    rw [LinearIsometryEquiv.diskBoundaryIso_neg_hom, morseAttachingMap_doubleWellNegChart]
  exact ⟨morseCellAttachmentIso _ _ _ _ _ _ _ _ _ (fun _ ↦ (LinearIsometryEquiv.neg ℝ).diskIso)
    (fun _ ↦ (LinearIsometryEquiv.neg ℝ).diskBoundaryIso)
    (fun _ ↦ LinearIsometryEquiv.diskBoundaryIso_hom_comp_diskBoundaryInclusion _) hα,
    by simp, by simp, morseCellAttachmentIso_hom_comp_morseCellComparison _ _ _ _ _ _ _ _ _ _ _ _ _
      fun _ ↦ morseCharacteristicMap_doubleWellNegChart⟩

/-! ### Admissibility of the width `ε = 1/2` -/

/-- The derivative of the double-well function is `4x(x² - 1)`. -/
theorem hasDerivAt_doubleWell (x : ℝ) : HasDerivAt doubleWell (4 * x * (x ^ 2 - 1)) x := by
  have h := ((hasDerivAt_pow 2 x).sub_const 1).pow 2
  convert h using 1
  · exact funext doubleWell_def
  · push_cast
    ring

/-- The critical points of the double-well function are the minima `±1` and the local maximum
`0`. -/
theorem criticalPoints_doubleWell : criticalPoints 𝓘(ℝ) doubleWell = {-1, 0, 1} := by
  ext x
  have hfac : 4 * x * (x ^ 2 - 1) = 4 * (x * ((x + 1) * (x - 1))) := by ring
  rw [mem_criticalPoints_iff_fderiv_eq_zero, (hasDerivAt_doubleWell x).hasFDerivAt.fderiv,
    ← ContinuousLinearMap.toSpanSingleton_zero, ContinuousLinearMap.toSpanSingleton_inj, hfac]
  simp [add_eq_zero_iff_eq_neg, sub_eq_zero]
  tauto

/-- The band `doubleWell⁻¹[1/2, 3/2]` around the critical level `1` is compact. -/
theorem isCompact_doubleWell_preimage_Icc :
    IsCompact (doubleWell ⁻¹' Icc (1 - 1 / 2) (1 + 1 / 2)) := by
  refine (isCompact_Icc (a := -2) (b := 2)).of_isClosed_subset
    (isClosed_Icc.preimage (by unfold doubleWell; fun_prop)) fun x hx ↦ ?_
  rw [mem_preimage, mem_Icc, doubleWell_def] at hx
  have h : x ^ 2 - 1 ≤ 2 := by nlinarith [hx.2]
  constructor <;> nlinarith

/-- The only critical point of the double-well function in the band `doubleWell⁻¹[1/2, 3/2]` is the
local maximum `0`, at the level `1`. -/
theorem criticalPoints_doubleWell_inter_preimage_Icc :
    criticalPoints 𝓘(ℝ) doubleWell ∩ doubleWell ⁻¹' Icc (1 - 1 / 2) (1 + 1 / 2) = {0} := by
  rw [criticalPoints_doubleWell]
  ext x
  simp only [mem_inter_iff, mem_insert_iff, mem_singleton_iff, mem_preimage, mem_Icc]
  constructor
  · rintro ⟨rfl | rfl | rfl, h⟩
    · norm_num [doubleWell_def] at h
    · rfl
    · norm_num [doubleWell_def] at h
  · rintro rfl
    norm_num [doubleWell_def]

end TauCeti
