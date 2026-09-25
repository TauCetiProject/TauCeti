/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.ThricePuncturedSphere.PeripheralLoops
public import TauCeti.Topology.Homotopy.Path
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

/-!
# The peripheral element at infinity is a loop around infinity

The peripheral element `periphInf` of `π₁(ℂ ∖ {0, 1}, 1/2)` is *defined* as
`(periph1 * periph0)⁻¹`, so that the three peripheral elements have product one. This file proves
that it is what its name says: the class of a loop around the third puncture `∞`.

Let `δ` be the circle `|z| = 3`, traversed counterclockwise once from the point
`p₊ = 1/2 + (√35/2)·i`, and let `α₊` be the vertical segment from the basepoint `1/2` up to `p₊`.
The circle `δ` separates the punctures `0` and `1` from `∞`, and the main theorem is

  `α₊ · δ · α₊.symm ≃ γ0 · γ1`

as paths in `ℂ ∖ {0, 1}`, where `γ0` and `γ1` are the peripheral loops around `0` and `1`.
Consequently `periph1 * periph0` is the class of `α₊ · δ · α₊.symm`, and `periphInf` is the class of
the circle `|z| = 3` traversed **clockwise** in the affine coordinate `z`, transported to the
basepoint along `α₊`. In the chart `w = 1/z` at `∞` the same circle runs counterclockwise.

The proof cuts both loops into pieces lying in the closed upper half-plane `im z ≥ 0` or the closed
lower half-plane `im z ≤ 0` of `ℂ ∖ {0, 1}`. Each of these is star-convex (about `i` and `−i`), so
simply connected, and the two punctures lie on its boundary line. The cut points are the points
`−3` and `3` of the big circle, joined along the real axis to the points `−1/2` and `3/2` of the
small circles; the connecting segments lie in both half-planes, and cancel in the final
concatenation.

## Main declarations

* `TauCeti.ThricePuncturedSphere.pPlus`: the point `1/2 + (√35/2)·i` of the circle `|z| = 3`.
* `TauCeti.ThricePuncturedSphere.αPlus`: the vertical segment from `1/2` to `pPlus`.
* `TauCeti.ThricePuncturedSphere.δ`: the circle `|z| = 3`, counterclockwise from `pPlus`, with
  `norm_coe_δ`.
* `TauCeti.ThricePuncturedSphere.αPlus_trans_δ_trans_symm_homotopic_γ0_trans_γ1`:
  `α₊ · δ · α₊.symm ≃ γ0 · γ1`.
* `TauCeti.ThricePuncturedSphere.periph1_mul_periph0_eq_fromPath`,
  `TauCeti.ThricePuncturedSphere.periphInf_eq_fromPath`: `periph1 * periph0` is the class of
  `α₊ · δ · α₊.symm`, and `periphInf` is the class of `α₊ · δ.symm · α₊.symm`.

## References

* E. Girondo and G. González-Diez, *Introduction to Compact Riemann Surfaces and Dessins
  d'Enfants*, London Mathematical Society Student Texts 79, Cambridge University Press, 2012,
  pp. 125–126 (the loops around `0`, `1` and `∞` of the thrice-punctured sphere).
-/

public section

open Set Real Complex

namespace TauCeti

namespace ThricePuncturedSphere

/-! ### The circle `|z| = 3` and the segment joining it to the basepoint -/

/-- The point `p₊ = 1/2 + (√35/2)·i`, where the circle `|z| = 3` meets the line `re z = 1/2` in the
upper half-plane. -/
noncomputable def pPlus : ThricePuncturedSphere :=
  ⟨1 / 2 + √35 / 2 * I, fun h ↦ by simpa using congrArg re h, fun h ↦ by
    have := congrArg re h
    norm_num at this⟩

@[simp]
theorem coe_pPlus : (pPlus : ℂ) = 1 / 2 + √35 / 2 * I :=
  (rfl)

/-- The vertical segment `α₊` from the basepoint `1/2` up to `p₊ = 1/2 + (√35/2)·i`. -/
noncomputable def αPlus : Path basePt pPlus where
  toFun t := ⟨1 / 2 + (t * (√35 / 2) : ℝ) * I, fun h ↦ by simpa using congrArg re h, fun h ↦ by
    have := congrArg re h
    norm_num at this⟩
  continuous_toFun := by fun_prop
  source' := Subtype.ext (by simp)
  target' := Subtype.ext (by simp)

@[simp]
theorem coe_αPlus (t : unitInterval) : (αPlus t : ℂ) = 1 / 2 + (t * (√35 / 2) : ℝ) * I :=
  (rfl)

/-- The angle `arccos (1/6)` of `p₊ = 3·exp(i·arccos(1/6))`. -/
local notation "θ₀" => arccos (1 / 6)

private theorem θ₀_pos : 0 < θ₀ := arccos_pos.2 (by norm_num)

private theorem θ₀_lt_pi : θ₀ < π :=
  (arccos_lt_pi_div_two.2 (by norm_num)).trans (by linarith [pi_pos])

private theorem cos_θ₀ : Real.cos θ₀ = 1 / 6 :=
  Real.cos_arccos (by norm_num) (by norm_num)

private theorem sin_θ₀ : Real.sin θ₀ = √35 / 6 := by
  rw [sin_arccos, show (1 : ℝ) - (1 / 6) ^ 2 = 35 / 6 ^ 2 by norm_num,
    Real.sqrt_div' _ (by positivity), Real.sqrt_sq (by norm_num)]

private theorem circleMap_θ₀ : circleMap 0 3 θ₀ = 1 / 2 + √35 / 2 * I := by
  have hc := cos_θ₀
  have hs := sin_θ₀
  apply Complex.ext <;>
    simp [circleMap, exp_ofReal_mul_I_re, exp_ofReal_mul_I_im] at hc hs ⊢ <;> linarith

private theorem circleMap_θ₀_add_two_pi : circleMap 0 3 (θ₀ + 2 * π) = 1 / 2 + √35 / 2 * I := by
  rw [(periodic_circleMap 0 3) θ₀, circleMap_θ₀]

/-- The circle `|z| = 3`, traversed counterclockwise once from `p₊`:
`t ↦ 3·exp(i(arccos(1/6) + 2πt))`, where `p₊ = 3·exp(i·arccos(1/6))`. It separates the punctures
`0` and `1` from `∞`. -/
noncomputable def δ : Path pPlus pPlus where
  toFun t := ⟨circleMap 0 3 (θ₀ + 2 * π * t), by
    have hnorm : ‖circleMap 0 3 (θ₀ + 2 * π * t)‖ = 3 := by simp [norm_circleMap_zero]
    constructor <;> rintro h <;> rw [h] at hnorm <;> norm_num at hnorm⟩
  continuous_toFun := by fun_prop
  source' := Subtype.ext (by simpa using circleMap_θ₀)
  target' := Subtype.ext (by simpa using circleMap_θ₀_add_two_pi)

@[simp]
theorem coe_δ (t : unitInterval) : (δ t : ℂ) = circleMap 0 3 (arccos (1 / 6) + 2 * π * t) :=
  (rfl)

/-- The loop `δ` lies on the circle of radius `3` about `0`, which bounds a punctured disc about
`∞` containing neither `0` nor `1`. -/
theorem norm_coe_δ (t : unitInterval) : ‖(δ t : ℂ)‖ = 3 := by
  simp [norm_circleMap_zero]

/-! ### The closed upper and lower half-planes -/

/-- The closed half-plane `0 ≤ ε · im z` of `ℂ`, with the punctures `0` and `1` removed from its
boundary line, is star-convex about `ε · i`. -/
private theorem starConvex_setOf_mul_im {ε : ℝ} (hε : ε ≠ 0) :
    StarConvex ℝ (ε * I) {w : ℂ | (w ≠ 0 ∧ w ≠ 1) ∧ 0 ≤ ε * w.im} := by
  rintro w ⟨⟨hw₀, hw₁⟩, hw⟩ a b ha hb hab
  have him : (a • (ε * I) + b • w).im = a * ε + b * w.im := by simp
  -- a point of the segment on the real axis is its endpoint `w`
  have key {c : ℂ} (hc : c.im = 0) (h : a • (ε * I) + b • w = c) : w = c := by
    have hsum : a * ε ^ 2 + b * (ε * w.im) = 0 := by
      have := congrArg (fun z : ℂ ↦ ε * z.im) h
      simp only [him, hc, mul_zero] at this
      linear_combination this
    have ha₀ : a * ε ^ 2 = 0 := by nlinarith [mul_nonneg hb hw, mul_nonneg ha (sq_nonneg ε)]
    have ha₀' : a = 0 := by simpa [hε] using ha₀
    obtain rfl : b = 1 := by linarith
    simpa [ha₀'] using h
  refine ⟨⟨fun h ↦ hw₀ (key (by simp) h), fun h ↦ hw₁ (key (by simp) h)⟩, ?_⟩
  rw [him]
  nlinarith [mul_nonneg hb hw, mul_nonneg ha (sq_nonneg ε)]

/-- The closed half-plane `0 ≤ ε · im z` of the thrice-punctured sphere is simply connected. -/
private theorem isSimplyConnected_setOf_mul_im {ε : ℝ} (hε : ε ≠ 0) :
    IsSimplyConnected {z : ThricePuncturedSphere | 0 ≤ ε * (z : ℂ).im} := by
  rw [← isOpenEmbedding_coe.isEmbedding.isSimplyConnected_image]
  have himage : ((↑) : ThricePuncturedSphere → ℂ) '' {z | 0 ≤ ε * (z : ℂ).im} =
      {w : ℂ | (w ≠ 0 ∧ w ≠ 1) ∧ 0 ≤ ε * w.im} := by
    ext w
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨z.2, hz⟩
    · rintro ⟨hw, hw'⟩
      exact ⟨⟨w, hw⟩, hw', rfl⟩
  rw [himage]
  have hmem : (ε * I : ℂ) ∈ {w : ℂ | (w ≠ 0 ∧ w ≠ 1) ∧ 0 ≤ ε * w.im} := by
    refine ⟨⟨by simpa using hε, fun h ↦ hε (by simpa using congrArg im h)⟩, ?_⟩
    simpa using mul_self_nonneg ε
  have := (starConvex_setOf_mul_im hε).contractibleSpace ⟨_, hmem⟩
  exact SimplyConnectedSpace.ofContractible _

/-! ### The cut points -/

/-- The time `1/2`, at which `γ0` passes through `−1/2` and `γ1` through `3/2`. -/
private noncomputable def tHalf : unitInterval := ⟨1 / 2, by norm_num, by norm_num⟩

/-- The time `(π − θ₀)/(2π)`, at which `δ` passes through `−3`. -/
private noncomputable def tNeg : unitInterval :=
  ⟨(π - θ₀) / (2 * π), div_nonneg (by linarith [θ₀_lt_pi]) (by positivity),
    (div_le_one (by positivity)).2 (by linarith [θ₀_pos, pi_pos])⟩

/-- The time `(2π − θ₀)/(2π)`, at which `δ` passes through `3`. -/
private noncomputable def tPos : unitInterval :=
  ⟨(2 * π - θ₀) / (2 * π), div_nonneg (by linarith [θ₀_lt_pi, pi_pos]) (by positivity),
    (div_le_one (by positivity)).2 (by linarith [θ₀_pos])⟩

private theorem tNeg_le_tPos : tNeg ≤ tPos := by
  rw [← Subtype.coe_le_coe]
  exact div_le_div_of_nonneg_right (by linarith [pi_pos]) (by positivity)

private theorem two_pi_mul_tHalf : 2 * π * (tHalf : ℝ) = π := by
  simp only [tHalf]
  ring

private theorem θ₀_add_two_pi_mul_tNeg : θ₀ + 2 * π * (tNeg : ℝ) = π := by
  simp only [tNeg]
  field_simp
  ring

private theorem θ₀_add_two_pi_mul_tPos : θ₀ + 2 * π * (tPos : ℝ) = 2 * π := by
  simp only [tPos]
  field_simp
  ring

private theorem coe_γ0_tHalf : (γ0 tHalf : ℂ) = -(1 / 2 : ℝ) := by
  rw [coe_γ0, two_pi_mul_tHalf]
  simp [circleMap]

private theorem coe_γ1_tHalf : (γ1 tHalf : ℂ) = (3 / 2 : ℝ) := by
  rw [coe_γ1, two_pi_mul_tHalf]
  simp [circleMap]
  norm_num

private theorem coe_δ_tNeg : (δ tNeg : ℂ) = (-3 : ℝ) := by
  rw [coe_δ, θ₀_add_two_pi_mul_tNeg]
  simp [circleMap]

private theorem coe_δ_tPos : (δ tPos : ℂ) = (3 : ℝ) := by
  rw [coe_δ, θ₀_add_two_pi_mul_tPos]
  simp [circleMap]

/-- The segment of the real axis from `−1/2 = γ0 (1/2)` to `−3 = δ tNeg`. -/
private noncomputable def segNeg : Path (γ0 tHalf) (δ tNeg) where
  toFun t := ⟨(-(1 / 2 + 5 / 2 * t : ℝ) : ℂ), fun h ↦ by
    have := congrArg re h
    simp at this
    linarith [t.2.1], fun h ↦ by
    have := congrArg re h
    simp at this
    linarith [t.2.1]⟩
  continuous_toFun := by fun_prop
  source' := Subtype.ext (by rw [coe_γ0_tHalf]; simp)
  target' := Subtype.ext (by rw [coe_δ_tNeg]; norm_num)

/-- The segment of the real axis from `3/2 = γ1 (1/2)` to `3 = δ tPos`. -/
private noncomputable def segPos : Path (γ1 tHalf) (δ tPos) where
  toFun t := ⟨((3 / 2 + 3 / 2 * t : ℝ) : ℂ), fun h ↦ by
    have := congrArg re h
    simp at this
    linarith [t.2.1], fun h ↦ by
    have := congrArg re h
    simp at this
    linarith [t.2.1]⟩
  continuous_toFun := by fun_prop
  source' := Subtype.ext (by rw [coe_γ1_tHalf]; simp)
  target' := Subtype.ext (by rw [coe_δ_tPos]; norm_num)

/-! ### The pieces and the half-planes containing them -/

private theorem isSimplyConnected_upper :
    IsSimplyConnected {z : ThricePuncturedSphere | 0 ≤ (z : ℂ).im} := by
  simpa using isSimplyConnected_setOf_mul_im one_ne_zero

private theorem isSimplyConnected_lower :
    IsSimplyConnected {z : ThricePuncturedSphere | (z : ℂ).im ≤ 0} := by
  simpa using isSimplyConnected_setOf_mul_im (neg_ne_zero.2 one_ne_zero)

private theorem sin_nonpos_of_pi_le {x : ℝ} (h₁ : π ≤ x) (h₂ : x ≤ 2 * π) : Real.sin x ≤ 0 := by
  rw [← Real.sin_sub_two_pi]
  exact sin_nonpos_of_nonpos_of_neg_pi_le (by linarith) (by linarith)

private theorem im_coe_δ (t : unitInterval) : (δ t : ℂ).im = 3 * Real.sin (θ₀ + 2 * π * t) := by
  simp only [coe_δ, circleMap, zero_add, im_ofReal_mul, exp_ofReal_mul_I_im]

private theorem im_coe_γ0 (t : unitInterval) : (γ0 t : ℂ).im = 1 / 2 * Real.sin (2 * π * t) := by
  simp only [coe_γ0, circleMap, zero_add, im_ofReal_mul, exp_ofReal_mul_I_im]

private theorem im_coe_γ1 (t : unitInterval) : (γ1 t : ℂ).im = -(1 / 2) * Real.sin (2 * π * t) := by
  simp only [coe_γ1, circleMap, add_im, one_im, zero_add, im_ofReal_mul, exp_ofReal_mul_I_im]

/-- The arc of `δ` from `p₊` counterclockwise to `−3`, in the upper half-plane. -/
private noncomputable def δ₁ : Path pPlus (δ tNeg) := (δ.subpath 0 tNeg).cast δ.source.symm rfl

/-- The arc of `δ` from `−3` counterclockwise to `3`, in the lower half-plane. -/
private noncomputable def δ₂ : Path (δ tNeg) (δ tPos) := δ.subpath tNeg tPos

/-- The arc of `δ` from `3` counterclockwise to `p₊`, in the upper half-plane. -/
private noncomputable def δ₃ : Path (δ tPos) pPlus := (δ.subpath tPos 1).cast rfl δ.target.symm

/-- The upper half of `γ0`, from `1/2` to `−1/2`. -/
private noncomputable def γ0₁ : Path basePt (γ0 tHalf) :=
  (γ0.subpath 0 tHalf).cast γ0.source.symm rfl

/-- The lower half of `γ0`, from `−1/2` to `1/2`. -/
private noncomputable def γ0₂ : Path (γ0 tHalf) basePt :=
  (γ0.subpath tHalf 1).cast rfl γ0.target.symm

/-- The lower half of `γ1`, from `1/2` to `3/2`. -/
private noncomputable def γ1₁ : Path basePt (γ1 tHalf) :=
  (γ1.subpath 0 tHalf).cast γ1.source.symm rfl

/-- The upper half of `γ1`, from `3/2` to `1/2`. -/
private noncomputable def γ1₂ : Path (γ1 tHalf) basePt :=
  (γ1.subpath tHalf 1).cast rfl γ1.target.symm

private theorem mk_δ : Path.Homotopic.Quotient.mk δ =
    (Path.Homotopic.Quotient.mk δ₁).trans
      ((Path.Homotopic.Quotient.mk δ₂).trans (Path.Homotopic.Quotient.mk δ₃)) := by
  have h₂₃ := Path.Homotopic.Quotient.subpath_cast_trans δ tNeg tPos 1 rfl rfl δ.target.symm
  have h₁₂₃ := Path.Homotopic.Quotient.subpath_cast_trans δ 0 tNeg 1 δ.source.symm rfl
    δ.target.symm
  rw [Path.cast_rfl_rfl] at h₂₃
  rw [δ₁, δ₂, δ₃, h₂₃, h₁₂₃]
  simp

private theorem mk_γ0 : Path.Homotopic.Quotient.mk γ0 =
    (Path.Homotopic.Quotient.mk γ0₁).trans (Path.Homotopic.Quotient.mk γ0₂) := by
  rw [γ0₁, γ0₂, Path.Homotopic.Quotient.subpath_cast_trans]
  simp

private theorem mk_γ1 : Path.Homotopic.Quotient.mk γ1 =
    (Path.Homotopic.Quotient.mk γ1₁).trans (Path.Homotopic.Quotient.mk γ1₂) := by
  rw [γ1₁, γ1₂, Path.Homotopic.Quotient.subpath_cast_trans]
  simp

private theorem range_αPlus : range αPlus ⊆ {z | 0 ≤ (z : ℂ).im} := by
  rintro _ ⟨t, rfl⟩
  simpa using mul_nonneg t.2.1 (by positivity : (0 : ℝ) ≤ √35 / 2)

private theorem range_segNeg : range segNeg ⊆ {z | (z : ℂ).im = 0} := by
  rintro _ ⟨t, rfl⟩
  simp [segNeg]

private theorem range_segPos : range segPos ⊆ {z | (z : ℂ).im = 0} := by
  rintro _ ⟨t, rfl⟩
  simp [segPos]

private theorem range_δ₁ : range δ₁ ⊆ {z | 0 ≤ (z : ℂ).im} := by
  refine (Path.range_subpath_of_le δ 0 tNeg unitInterval.nonneg').trans_subset ?_
  rintro _ ⟨t, ⟨-, ht⟩, rfl⟩
  have h := mul_le_mul_of_nonneg_left (show (t : ℝ) ≤ tNeg from ht) (by positivity : 0 ≤ 2 * π)
  rw [mem_ofPred_eq, im_coe_δ]
  exact mul_nonneg (by norm_num) (sin_nonneg_of_nonneg_of_le_pi
    (by nlinarith [θ₀_pos, t.2.1, pi_pos]) (by linarith [θ₀_add_two_pi_mul_tNeg]))

private theorem range_δ₂ : range δ₂ ⊆ {z | (z : ℂ).im ≤ 0} := by
  refine (Path.range_subpath_of_le _ _ _ tNeg_le_tPos).trans_subset ?_
  rintro _ ⟨t, ⟨ht₁, ht₂⟩, rfl⟩
  have h₁ := mul_le_mul_of_nonneg_left (show (tNeg : ℝ) ≤ t from ht₁) (by positivity : 0 ≤ 2 * π)
  have h₂ := mul_le_mul_of_nonneg_left (show (t : ℝ) ≤ tPos from ht₂) (by positivity : 0 ≤ 2 * π)
  rw [mem_ofPred_eq, im_coe_δ]
  exact mul_nonpos_of_nonneg_of_nonpos (by norm_num) (sin_nonpos_of_pi_le
    (by linarith [θ₀_add_two_pi_mul_tNeg]) (by linarith [θ₀_add_two_pi_mul_tPos]))

private theorem range_δ₃ : range δ₃ ⊆ {z | 0 ≤ (z : ℂ).im} := by
  refine (Path.range_subpath_of_le δ tPos 1 unitInterval.le_one').trans_subset ?_
  rintro _ ⟨t, ⟨ht, -⟩, rfl⟩
  have h₁ := mul_le_mul_of_nonneg_left (show (tPos : ℝ) ≤ t from ht) (by positivity : 0 ≤ 2 * π)
  have h₂ := mul_le_mul_of_nonneg_left t.2.2 (by positivity : 0 ≤ 2 * π)
  rw [mem_ofPred_eq, im_coe_δ, ← Real.sin_sub_two_pi]
  exact mul_nonneg (by norm_num) (sin_nonneg_of_nonneg_of_le_pi
    (by linarith [θ₀_add_two_pi_mul_tPos]) (by linarith [θ₀_lt_pi]))

private theorem range_γ0₁ : range γ0₁ ⊆ {z | 0 ≤ (z : ℂ).im} := by
  refine (Path.range_subpath_of_le _ _ _ unitInterval.nonneg').trans_subset ?_
  rintro _ ⟨t, ⟨-, ht⟩, rfl⟩
  have h := mul_le_mul_of_nonneg_left (show (t : ℝ) ≤ tHalf from ht) (by positivity : 0 ≤ 2 * π)
  rw [mem_ofPred_eq, im_coe_γ0]
  exact mul_nonneg (by norm_num) (sin_nonneg_of_nonneg_of_le_pi
    (by nlinarith [t.2.1, pi_pos]) (by linarith [two_pi_mul_tHalf]))

private theorem range_γ0₂ : range γ0₂ ⊆ {z | (z : ℂ).im ≤ 0} := by
  refine (Path.range_subpath_of_le _ _ _ unitInterval.le_one').trans_subset ?_
  rintro _ ⟨t, ⟨ht, -⟩, rfl⟩
  have h₁ := mul_le_mul_of_nonneg_left (show (tHalf : ℝ) ≤ t from ht) (by positivity : 0 ≤ 2 * π)
  have h₂ := mul_le_mul_of_nonneg_left t.2.2 (by positivity : 0 ≤ 2 * π)
  rw [mem_ofPred_eq, im_coe_γ0]
  exact mul_nonpos_of_nonneg_of_nonpos (by norm_num) (sin_nonpos_of_pi_le
    (by linarith [two_pi_mul_tHalf]) (by linarith))

private theorem range_γ1₁ : range γ1₁ ⊆ {z | (z : ℂ).im ≤ 0} := by
  refine (Path.range_subpath_of_le _ _ _ unitInterval.nonneg').trans_subset ?_
  rintro _ ⟨t, ⟨-, ht⟩, rfl⟩
  have h := mul_le_mul_of_nonneg_left (show (t : ℝ) ≤ tHalf from ht) (by positivity : 0 ≤ 2 * π)
  rw [mem_ofPred_eq, im_coe_γ1]
  exact mul_nonpos_of_nonpos_of_nonneg (by norm_num) (sin_nonneg_of_nonneg_of_le_pi
    (by nlinarith [t.2.1, pi_pos]) (by linarith [two_pi_mul_tHalf]))

private theorem range_γ1₂ : range γ1₂ ⊆ {z | 0 ≤ (z : ℂ).im} := by
  refine (Path.range_subpath_of_le _ _ _ unitInterval.le_one').trans_subset ?_
  rintro _ ⟨t, ⟨ht, -⟩, rfl⟩
  have h₁ := mul_le_mul_of_nonneg_left (show (tHalf : ℝ) ≤ t from ht) (by positivity : 0 ≤ 2 * π)
  have h₂ := mul_le_mul_of_nonneg_left t.2.2 (by positivity : 0 ≤ 2 * π)
  rw [mem_ofPred_eq, im_coe_γ1]
  exact mul_nonneg_of_nonpos_of_nonpos (by norm_num) (sin_nonpos_of_pi_le
    (by linarith [two_pi_mul_tHalf]) (by linarith))

/-! ### The loop at infinity -/

/-- **The big circle is the product of the two small ones.** The circle `|z| = 3`, traversed
counterclockwise and transported to the basepoint `1/2` along the vertical segment `α₊`, is
homotopic in `ℂ ∖ {0, 1}` to the loop `γ0` around `0` followed by the loop `γ1` around `1`. -/
theorem αPlus_trans_δ_trans_symm_homotopic_γ0_trans_γ1 :
    ((αPlus.trans δ).trans αPlus.symm).Homotopic (γ0.trans γ1) := by
  have homotopic_of_range_subset {V : Set ThricePuncturedSphere} (hV : IsSimplyConnected V)
      {x y : ThricePuncturedSphere} {p q : Path x y} (hp : range p ⊆ V) (hq : range q ⊆ V) :
      p.Homotopic q :=
    let ⟨K, _⟩ := Path.exists_homotopy_forall_mem_of_isSimplyConnected hV
      (range_subset_iff.1 hp) (range_subset_iff.1 hq)
    ⟨K⟩
  have hreal {S : Set ThricePuncturedSphere} (hS : S ⊆ {z | (z : ℂ).im = 0}) :
      S ⊆ {z | 0 ≤ (z : ℂ).im} ∧ S ⊆ {z | (z : ℂ).im ≤ 0} :=
    ⟨hS.trans fun _ h ↦ h.symm.le, hS.trans fun _ h ↦ h.le⟩
  -- the three pairs of pieces, each pair in a common closed half-plane
  have hA : (αPlus.trans δ₁).Homotopic (γ0₁.trans segNeg) :=
    homotopic_of_range_subset isSimplyConnected_upper
      (by rw [Path.trans_range]; exact union_subset range_αPlus range_δ₁)
      (by rw [Path.trans_range]; exact union_subset range_γ0₁ (hreal range_segNeg).1)
  have hB : δ₂.Homotopic (segNeg.symm.trans (γ0₂.trans (γ1₁.trans segPos))) :=
    homotopic_of_range_subset isSimplyConnected_lower range_δ₂
      (by
        simp only [Path.trans_range, Path.symm_range]
        exact union_subset (hreal range_segNeg).2 <| union_subset range_γ0₂ <|
          union_subset range_γ1₁ (hreal range_segPos).2)
  have hC : (δ₃.trans αPlus.symm).Homotopic (segPos.symm.trans γ1₂) :=
    homotopic_of_range_subset isSimplyConnected_upper
      (by
        rw [Path.trans_range, Path.symm_range]
        exact union_subset range_δ₃ range_αPlus)
      (by
        rw [Path.trans_range, Path.symm_range]
        exact union_subset (hreal range_segPos).1 range_γ1₂)
  -- assemble the pieces in the fundamental groupoid; the connecting segments cancel
  rw [← Path.Homotopic.Quotient.eq] at hA hB hC ⊢
  simp only [Path.Homotopic.Quotient.mk_trans, Path.Homotopic.Quotient.mk_symm] at hA hB hC ⊢
  rw [mk_δ, mk_γ0, mk_γ1]
  grind

/-- `periph1 * periph0`, the class of `γ0` followed by `γ1`, is the class of the circle `|z| = 3`
traversed counterclockwise and transported to the basepoint along `α₊`. -/
theorem periph1_mul_periph0_eq_fromPath :
    periph1 * periph0 = FundamentalGroup.fromPath ⟦(αPlus.trans δ).trans αPlus.symm⟧ := by
  rw [periph1_def, periph0_def, FundamentalGroup.mul_def]
  exact (Path.Homotopic.Quotient.eq.2 αPlus_trans_δ_trans_symm_homotopic_γ0_trans_γ1).symm

/-- **The peripheral element at infinity is the loop around infinity.** `periphInf` is the class of
the circle `|z| = 3` traversed clockwise in the affine coordinate `z`, transported to the basepoint
along `α₊`. In the chart `w = 1/z` at `∞` this circle runs counterclockwise about `w = 0`. -/
theorem periphInf_eq_fromPath :
    periphInf = FundamentalGroup.fromPath ⟦(αPlus.trans δ.symm).trans αPlus.symm⟧ := by
  rw [periphInf_def, periph1_mul_periph0_eq_fromPath, FundamentalGroup.inv_def]
  have h : ((αPlus.trans δ).trans αPlus.symm).symm.Homotopic
      ((αPlus.trans δ.symm).trans αPlus.symm) := by
    rw [Path.trans_symm, Path.trans_symm, Path.symm_symm]
    exact (Path.Homotopic.trans_assoc _ _ _).symm
  -- the class of the reversed loop is the inverse class by definition (`mk_symm` is `rfl`)
  exact Path.Homotopic.Quotient.eq.2 h

end ThricePuncturedSphere

end TauCeti
