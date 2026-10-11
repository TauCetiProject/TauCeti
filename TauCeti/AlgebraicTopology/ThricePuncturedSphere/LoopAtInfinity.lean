/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.ThricePuncturedSphere.Anharmonic
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

The anharmonic self-homeomorphism `z ↦ z / (z − 1)` of `ℂ ∖ {0, 1}` fixes the puncture `0` and
exchanges `1` with `∞`, so it gives a second description of `periphInf`: the image of the loop `γ1`
around `1`. The map moves the basepoint `1/2` to `−1`; transporting back along the path `α₋₁` from
`−1` to `1/2` through the closed upper half-plane, it induces an automorphism `mob1InfMulAut` of
`π₁(ℂ ∖ {0, 1}, 1/2)`, and

  `mob1InfMulAut periph0 = periph0`,  `mob1InfMulAut periph1 = periphInf`.

These values are what identify pulling covers back along `z ↦ z / (z − 1)` with the exchange of
the branch points `1` and `∞` on permutation triples.

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
* `TauCeti.ThricePuncturedSphere.αMob1Inf`: the path from `−1` to `1/2` through the upper
  half-plane, with `range_αMob1Inf_subset`.
* `TauCeti.ThricePuncturedSphere.mob1InfMulAut`: the automorphism of `π₁(ℂ ∖ {0, 1}, 1/2)` induced
  by `z ↦ z / (z − 1)` and `α₋₁`, with `mob1InfMulAut_periph0`, `mob1InfMulAut_periph1` and
  `mob1InfMulAut_periphInf`, and the values `mob1InfMulAut_symm_periph0` and
  `mob1InfMulAut_symm_periph1` of its inverse.

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

private theorem θ₀_lt_pi : θ₀ < π := arccos_lt_pi.2 (by norm_num)

private theorem cos_θ₀ : Real.cos θ₀ = 1 / 6 :=
  Real.cos_arccos (by norm_num) (by norm_num)

private theorem sin_θ₀ : Real.sin θ₀ = √35 / 6 := by
  have h : (1 : ℝ) - (1 / 6) ^ 2 = 35 / 6 ^ 2 := by norm_num
  rw [sin_arccos, h,
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
-- `coe_δ` and `norm_circleMap_zero` already simplify this statement; marking it `@[simp]`
-- would fail the simpNF linter.
theorem norm_coe_δ (t : unitInterval) : ‖(δ t : ℂ)‖ = 3 := by
  simp

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
      {w : ℂ | (w ≠ 0 ∧ w ≠ 1) ∧ 0 ≤ ε * w.im} :=
    Subtype.image_preimage_coe {w : ℂ | w ≠ 0 ∧ w ≠ 1} {w | 0 ≤ ε * w.im}
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

/-- The segment of the real axis between two real points `z = a` and `w = b` of `ℂ ∖ {0, 1}`
lying on the same side of `0` and on the same side of `1`. -/
private noncomputable def realSegment (z w : ThricePuncturedSphere) (a b : ℝ) (hz : (z : ℂ) = a)
    (hw : (w : ℂ) = b) (h₀ : 0 < a * b) (h₁ : 0 < (a - 1) * (b - 1)) : Path z w where
  toFun t := ⟨((1 - t) * a + t * b : ℝ),
    -- a convex combination of two reals of the same sign is not zero, by convexity of the
    -- open half-lines `Ioi 0` and `Iio 0`
    have hne {a b : ℝ} (hab : 0 < a * b) : (1 - t) * a + t * b ≠ 0 := by
      rcases mul_pos_iff.1 hab with ⟨ha, hb⟩ | ⟨ha, hb⟩
      · exact (convex_Ioi 0 ha hb (sub_nonneg.2 t.2.2) t.2.1 (sub_add_cancel 1 _)).ne'
      · exact (convex_Iio 0 ha hb (sub_nonneg.2 t.2.2) t.2.1 (sub_add_cancel 1 _)).ne
    ⟨fun h ↦ hne h₀ (by exact_mod_cast h), fun h ↦ hne h₁ (by
      have : ((1 - t) * a + t * b : ℝ) = 1 := by exact_mod_cast h
      linear_combination this)⟩⟩
  continuous_toFun := by fun_prop
  source' := Subtype.ext (by simp [hz])
  target' := Subtype.ext (by simp [hw])

private theorem range_realSegment_subset (z w : ThricePuncturedSphere) (a b : ℝ) (hz : (z : ℂ) = a)
    (hw : (w : ℂ) = b) (h₀ : 0 < a * b) (h₁ : 0 < (a - 1) * (b - 1)) :
    range (realSegment z w a b hz hw h₀ h₁) ⊆ {z | (z : ℂ).im = 0} := by
  rintro _ ⟨t, rfl⟩
  simp [realSegment]

/-- The segment of the real axis from `−1/2 = γ0 (1/2)` to `−3 = δ tNeg`. -/
private noncomputable def segNeg : Path (γ0 tHalf) (δ tNeg) :=
  realSegment _ _ (-(1 / 2)) (-3) (by rw [coe_γ0_tHalf, ofReal_neg]) coe_δ_tNeg (by norm_num)
    (by norm_num)

/-- The segment of the real axis from `3/2 = γ1 (1/2)` to `3 = δ tPos`. -/
private noncomputable def segPos : Path (γ1 tHalf) (δ tPos) :=
  realSegment _ _ (3 / 2) 3 coe_γ1_tHalf coe_δ_tPos (by norm_num) (by norm_num)

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
  rw [coe_δ, circleMap_zero_im]

private theorem im_coe_γ0 (t : unitInterval) : (γ0 t : ℂ).im = 1 / 2 * Real.sin (2 * π * t) := by
  rw [coe_γ0, circleMap_zero_im]

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

private theorem range_αPlus_subset : range αPlus ⊆ {z | 0 ≤ (z : ℂ).im} := by
  rintro _ ⟨t, rfl⟩
  simpa using mul_nonneg t.2.1 (by positivity : (0 : ℝ) ≤ √35 / 2)

/-- A subpath of a path whose imaginary part is `r * sin (a + 2 * π * u)` stays in the region
where the imaginary part satisfies `P`, as soon as `r * sin θ` does on the corresponding interval
of angles. -/
private theorem _root_.Path.range_subpath_subset_of_im {x y : ThricePuncturedSphere}
    (p : Path x y) {r a : ℝ}
    (hp : ∀ u : unitInterval, (p u : ℂ).im = r * Real.sin (a + 2 * π * u))
    {s t : unitInterval} (hst : s ≤ t) {P : ℝ → Prop}
    (h : ∀ θ, a + 2 * π * s ≤ θ → θ ≤ a + 2 * π * t → P (r * Real.sin θ)) :
    range (p.subpath s t) ⊆ {z | P (z : ℂ).im} := by
  rw [Path.range_subpath_of_le _ _ _ hst]
  rintro _ ⟨u, ⟨h₁, h₂⟩, rfl⟩
  rw [mem_ofPred_eq, hp]
  exact h _ (by gcongr) (by gcongr)

private theorem range_δ₁_subset : range δ₁ ⊆ {z | 0 ≤ (z : ℂ).im} :=
  δ.range_subpath_subset_of_im im_coe_δ unitInterval.nonneg' (P := (0 ≤ ·)) fun _ h₁ h₂ ↦
    mul_nonneg (by norm_num) (sin_nonneg_of_nonneg_of_le_pi (by simp at h₁; linarith [θ₀_pos])
      (by linarith [θ₀_add_two_pi_mul_tNeg]))

private theorem range_δ₂_subset : range δ₂ ⊆ {z | (z : ℂ).im ≤ 0} :=
  δ.range_subpath_subset_of_im im_coe_δ tNeg_le_tPos (P := (· ≤ 0)) fun _ h₁ h₂ ↦
    mul_nonpos_of_nonneg_of_nonpos (by norm_num) (sin_nonpos_of_pi_le
      (by linarith [θ₀_add_two_pi_mul_tNeg]) (by linarith [θ₀_add_two_pi_mul_tPos]))

private theorem range_δ₃_subset : range δ₃ ⊆ {z | 0 ≤ (z : ℂ).im} :=
  δ.range_subpath_subset_of_im im_coe_δ unitInterval.le_one' (P := (0 ≤ ·)) fun _ h₁ h₂ ↦ by
    rw [← Real.sin_sub_two_pi]
    exact mul_nonneg (by norm_num) (sin_nonneg_of_nonneg_of_le_pi
      (by linarith [θ₀_add_two_pi_mul_tPos]) (by simp at h₂; linarith [θ₀_lt_pi]))

private theorem range_γ0₁_subset : range γ0₁ ⊆ {z | 0 ≤ (z : ℂ).im} :=
  γ0.range_subpath_subset_of_im (a := 0) (fun u ↦ by rw [im_coe_γ0, zero_add])
    unitInterval.nonneg' (P := (0 ≤ ·)) fun _ h₁ h₂ ↦
    mul_nonneg (by norm_num) (sin_nonneg_of_nonneg_of_le_pi
      (by simpa using h₁) (by linarith [two_pi_mul_tHalf]))

private theorem range_γ0₂_subset : range γ0₂ ⊆ {z | (z : ℂ).im ≤ 0} :=
  γ0.range_subpath_subset_of_im (a := 0) (fun u ↦ by rw [im_coe_γ0, zero_add])
    unitInterval.le_one' (P := (· ≤ 0)) fun _ h₁ h₂ ↦
    mul_nonpos_of_nonneg_of_nonpos (by norm_num) (sin_nonpos_of_pi_le
      (by linarith [two_pi_mul_tHalf]) (by simpa using h₂))

private theorem range_γ1₁_subset : range γ1₁ ⊆ {z | (z : ℂ).im ≤ 0} :=
  γ1.range_subpath_subset_of_im (a := 0) (fun u ↦ by rw [im_coe_γ1, zero_add])
    unitInterval.nonneg' (P := (· ≤ 0)) fun _ h₁ h₂ ↦
    mul_nonpos_of_nonpos_of_nonneg (by norm_num) (sin_nonneg_of_nonneg_of_le_pi
      (by simpa using h₁) (by linarith [two_pi_mul_tHalf]))

private theorem range_γ1₂_subset : range γ1₂ ⊆ {z | 0 ≤ (z : ℂ).im} :=
  γ1.range_subpath_subset_of_im (a := 0) (fun u ↦ by rw [im_coe_γ1, zero_add])
    unitInterval.le_one' (P := (0 ≤ ·)) fun _ h₁ h₂ ↦
    mul_nonneg_of_nonpos_of_nonpos (by norm_num) (sin_nonpos_of_pi_le
      (by linarith [two_pi_mul_tHalf]) (by simpa using h₂))

/-- A subset of the real axis lies in both closed half-planes. -/
private theorem subset_halfPlanes_of_real {S : Set ThricePuncturedSphere}
    (hS : S ⊆ {z | (z : ℂ).im = 0}) :
    S ⊆ {z | 0 ≤ (z : ℂ).im} ∧ S ⊆ {z | (z : ℂ).im ≤ 0} :=
  ⟨hS.trans fun _ h ↦ h.symm.le, hS.trans fun _ h ↦ h.le⟩

/-! ### The loop at infinity -/

/-- **The big circle is the product of the two small ones.** The circle `|z| = 3`, traversed
counterclockwise and transported to the basepoint `1/2` along the vertical segment `α₊`, is
homotopic in `ℂ ∖ {0, 1}` to the loop `γ0` around `0` followed by the loop `γ1` around `1`. -/
theorem αPlus_trans_δ_trans_symm_homotopic_γ0_trans_γ1 :
    ((αPlus.trans δ).trans αPlus.symm).Homotopic (γ0.trans γ1) := by
  -- the three pairs of pieces, each pair in a common closed half-plane
  have hA : (αPlus.trans δ₁).Homotopic (γ0₁.trans segNeg) :=
    isPathHomotopyTrivial_def.mp isSimplyConnected_upper.isPathHomotopyTrivial _ _
      (by rw [Path.trans_range]; exact union_subset range_αPlus_subset range_δ₁_subset)
      (by
        rw [Path.trans_range]
        exact union_subset range_γ0₁_subset
          (subset_halfPlanes_of_real (range_realSegment_subset ..)).1)
  have hB : δ₂.Homotopic (segNeg.symm.trans (γ0₂.trans (γ1₁.trans segPos))) :=
    isPathHomotopyTrivial_def.mp isSimplyConnected_lower.isPathHomotopyTrivial _ _ range_δ₂_subset
      (by
        simp only [Path.trans_range, Path.symm_range]
        exact union_subset (subset_halfPlanes_of_real (range_realSegment_subset ..)).2 <|
          union_subset range_γ0₂_subset <|
            union_subset range_γ1₁_subset
              (subset_halfPlanes_of_real (range_realSegment_subset ..)).2)
  have hC : (δ₃.trans αPlus.symm).Homotopic (segPos.symm.trans γ1₂) :=
    isPathHomotopyTrivial_def.mp isSimplyConnected_upper.isPathHomotopyTrivial _ _
      (by
        rw [Path.trans_range, Path.symm_range]
        exact union_subset range_δ₃_subset range_αPlus_subset)
      (by
        rw [Path.trans_range, Path.symm_range]
        exact union_subset (subset_halfPlanes_of_real (range_realSegment_subset ..)).1
          range_γ1₂_subset)
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

/-! ### The anharmonic map exchanging `1` and `∞`

The self-homeomorphism `mob1Inf : z ↦ z / (z − 1)` fixes the puncture `0`, exchanges the punctures
`1` and `∞`, and moves the basepoint `1/2` to `−1`. It has real coefficients and reverses the sign
of the imaginary part, so it exchanges the closed upper and lower half-planes, and the half-plane
decomposition of the previous section computes the images of the peripheral loops as well. -/

/-- `z ↦ z / (z − 1)` reverses the sign of the imaginary part. -/
private theorem im_coe_mob1Inf (z : ThricePuncturedSphere) :
    (mob1Inf z : ℂ).im = -(z : ℂ).im / normSq ((z : ℂ) - 1) := by
  rw [coe_mob1Inf, div_im, sub_re, sub_im, one_re, one_im, sub_zero]
  ring

private theorem im_coe_mob1Inf_nonpos {z : ThricePuncturedSphere} (hz : 0 ≤ (z : ℂ).im) :
    (mob1Inf z : ℂ).im ≤ 0 := by
  rw [im_coe_mob1Inf]
  exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.2 hz) (normSq_nonneg _)

private theorem im_coe_mob1Inf_nonneg {z : ThricePuncturedSphere} (hz : (z : ℂ).im ≤ 0) :
    0 ≤ (mob1Inf z : ℂ).im := by
  rw [im_coe_mob1Inf]
  exact div_nonneg (neg_nonneg.2 hz) (normSq_nonneg _)

private theorem coe_mob1Inf_γ0_tHalf : (mob1Inf (γ0 tHalf) : ℂ) = (1 / 3 : ℝ) := by
  rw [coe_mob1Inf, coe_γ0_tHalf]
  push_cast
  norm_num

private theorem coe_mob1Inf_γ1_tHalf : (mob1Inf (γ1 tHalf) : ℂ) = (3 : ℝ) := by
  rw [coe_mob1Inf, coe_γ1_tHalf]
  push_cast
  norm_num

/-- The segment of the real axis from `−1 = mob1Inf (1/2)` to `−1/2 = γ0 (1/2)`. -/
private noncomputable def segLeft : Path (mob1Inf basePt) (γ0 tHalf) :=
  realSegment _ _ (-1) (-(1 / 2)) (by rw [coe_mob1Inf_basePt]; norm_num)
    (by rw [coe_γ0_tHalf, ofReal_neg])
    (by norm_num) (by norm_num)

/-- The segment of the real axis from `1/3 = mob1Inf (−1/2)` to the basepoint `1/2`. -/
private noncomputable def segMid : Path (mob1Inf (γ0 tHalf)) basePt :=
  realSegment _ _ (1 / 3) (1 / 2) coe_mob1Inf_γ0_tHalf (by rw [coe_basePt]; norm_num)
    (by norm_num) (by norm_num)

/-- The segment of the real axis from `3/2 = γ1 (1/2)` to `3 = mob1Inf (3/2)`. -/
private noncomputable def segRight : Path (γ1 tHalf) (mob1Inf (γ1 tHalf)) :=
  realSegment _ _ (3 / 2) 3 coe_γ1_tHalf coe_mob1Inf_γ1_tHalf (by norm_num) (by norm_num)

/-- The path `α₋₁` from `−1 = mob1Inf (1/2)` to the basepoint `1/2` through the closed upper
half-plane: along the real axis to `−1/2`, then along the upper half of the circle `|z| = 1/2`
(`range_αMob1Inf_subset`). Any two such paths are homotopic, the closed upper half-plane of
`ℂ ∖ {0, 1}` being simply connected. -/
noncomputable def αMob1Inf : Path (mob1Inf basePt) basePt :=
  segLeft.trans γ0₁.symm

/-- The path `α₋₁` runs in the closed upper half-plane. -/
theorem range_αMob1Inf_subset : range αMob1Inf ⊆ {z | 0 ≤ (z : ℂ).im} := by
  rw [αMob1Inf, Path.trans_range, Path.symm_range]
  exact union_subset (subset_halfPlanes_of_real (range_realSegment_subset ..)).1 range_γ0₁_subset

/-- The automorphism of `π₁(ℂ ∖ {0, 1}, 1/2)` induced by `z ↦ z / (z − 1)`: the isomorphism onto
`π₁(ℂ ∖ {0, 1}, −1)` induced by the map, followed by the change of basepoint back to `1/2` along
`α₋₁`. It sends the class of a loop `γ` to the class of `α₋₁⁻¹ ⬝ (mob1Inf ∘ γ) ⬝ α₋₁`. -/
noncomputable def mob1InfMulAut : MulAut (FundamentalGroup ThricePuncturedSphere basePt) :=
  (FundamentalGroup.homeomorphMulEquiv mob1Inf basePt).trans
    (FundamentalGroup.fundamentalGroupMulEquivOfPath αMob1Inf)

/-- `mob1InfMulAut` is the isomorphism induced by `z ↦ z / (z − 1)` followed by the change of
basepoint along `α₋₁`. -/
theorem mob1InfMulAut_def :
    mob1InfMulAut = (FundamentalGroup.homeomorphMulEquiv mob1Inf basePt).trans
      (FundamentalGroup.fundamentalGroupMulEquivOfPath αMob1Inf) :=
  (rfl)

/-- The value of `mob1InfMulAut` on the class of a loop. -/
private theorem mob1InfMulAut_fromPath (γ : Path basePt basePt) :
    mob1InfMulAut (FundamentalGroup.fromPath (.mk γ)) =
      (Path.Homotopic.Quotient.mk αMob1Inf.symm).trans
        ((Path.Homotopic.Quotient.mk (γ.map mob1Inf.continuous)).trans
          (Path.Homotopic.Quotient.mk αMob1Inf)) := by
  simp [mob1InfMulAut_def, FundamentalGroup.fundamentalGroupMulEquivOfPath_apply]
  -- `FundamentalGroup.fromPath` is an abbreviation for the identity, which blocks rewriting with
  -- `Path.Homotopic.Quotient.mk_map`; that lemma holds by `rfl`
  rfl

/-- The class of the image of a loop under `z ↦ z / (z − 1)` is the product of the classes of the
images of its two halves at the time `1/2`. -/
private theorem mk_map_mob1Inf {γ : Path basePt basePt} {p : Path basePt (γ tHalf)}
    {q : Path (γ tHalf) basePt}
    (h : Path.Homotopic.Quotient.mk γ =
      (Path.Homotopic.Quotient.mk p).trans (Path.Homotopic.Quotient.mk q)) :
    Path.Homotopic.Quotient.mk (γ.map mob1Inf.continuous) =
      (Path.Homotopic.Quotient.mk (p.map mob1Inf.continuous)).trans
        (Path.Homotopic.Quotient.mk (q.map mob1Inf.continuous)) := by
  rw [← Path.Homotopic.Quotient.mk_trans, ← Path.map_trans, Path.Homotopic.Quotient.eq]
  exact (Path.Homotopic.Quotient.eq.1 (h.trans (Path.Homotopic.Quotient.mk_trans _ _).symm)).map
    ⟨mob1Inf, mob1Inf.continuous⟩

/-- **`z ↦ z / (z − 1)` fixes the peripheral element at `0`.** -/
@[simp]
theorem mob1InfMulAut_periph0 : mob1InfMulAut periph0 = periph0 := by
  -- The image of `γ0` is the circle `|z + 1/3| = 2/3`, through `−1` and `1/3`. Its lower half,
  -- from `−1` to `1/3`, and its upper half, back to `−1`, are homotopic in the closed lower and
  -- upper half-planes to paths made of the halves of `γ0` and segments of the real axis.
  have hL : (γ0₁.map mob1Inf.continuous).Homotopic ((segLeft.trans γ0₂).trans segMid.symm) :=
    isPathHomotopyTrivial_def.mp isSimplyConnected_lower.isPathHomotopyTrivial _ _
      (by
        rintro _ ⟨t, rfl⟩
        exact im_coe_mob1Inf_nonpos (range_γ0₁_subset ⟨t, rfl⟩))
      (by
        simp only [Path.trans_range, Path.symm_range]
        exact union_subset (union_subset (subset_halfPlanes_of_real (range_realSegment_subset ..)).2
          range_γ0₂_subset) (subset_halfPlanes_of_real (range_realSegment_subset ..)).2)
  have hU : (γ0₂.map mob1Inf.continuous).Homotopic ((segMid.trans γ0₁).trans segLeft.symm) :=
    isPathHomotopyTrivial_def.mp isSimplyConnected_upper.isPathHomotopyTrivial _ _
      (by
        rintro _ ⟨t, rfl⟩
        exact im_coe_mob1Inf_nonneg (range_γ0₂_subset ⟨t, rfl⟩))
      (by
        simp only [Path.trans_range, Path.symm_range]
        exact union_subset (union_subset (subset_halfPlanes_of_real (range_realSegment_subset ..)).1
          range_γ0₁_subset) (subset_halfPlanes_of_real (range_realSegment_subset ..)).1)
  rw [← Path.Homotopic.Quotient.eq] at hL hU
  -- `periph0` is by definition the class of `γ0`
  have h0 : periph0 = FundamentalGroup.fromPath (.mk γ0) := periph0_def
  rw [h0, mob1InfMulAut_fromPath, mk_map_mob1Inf mk_γ0, hL, hU]
  simp only [mk_γ0, αMob1Inf, Path.trans_symm, Path.symm_symm, Path.Homotopic.Quotient.mk_trans,
    Path.Homotopic.Quotient.mk_symm]
  grind

/-- **`z ↦ z / (z − 1)` carries the peripheral element at `1` to the peripheral element at `∞`.**
The image of the loop `γ1` around `1` is a loop around `∞`, and transported back to the basepoint
along `α₋₁` its class is `periphInf`. -/
@[simp]
theorem mob1InfMulAut_periph1 : mob1InfMulAut periph1 = periphInf := by
  -- The image of `γ1` is the circle `|z − 1| = 2`, run clockwise from `−1`. Its upper half, from
  -- `−1` to `3`, and its lower half, back to `−1`, are homotopic in the closed upper and lower
  -- half-planes to paths made of the halves of `γ0` and `γ1` and segments of the real axis.
  have hU : (γ1₁.map mob1Inf.continuous).Homotopic
      (((segLeft.trans γ0₁.symm).trans γ1₂.symm).trans segRight) :=
    isPathHomotopyTrivial_def.mp isSimplyConnected_upper.isPathHomotopyTrivial _ _
      (by
        rintro _ ⟨t, rfl⟩
        exact im_coe_mob1Inf_nonneg (range_γ1₁_subset ⟨t, rfl⟩))
      (by
        simp only [Path.trans_range, Path.symm_range]
        exact union_subset (union_subset (union_subset
          (subset_halfPlanes_of_real (range_realSegment_subset ..)).1 range_γ0₁_subset)
            range_γ1₂_subset)
          (subset_halfPlanes_of_real (range_realSegment_subset ..)).1)
  have hL : (γ1₂.map mob1Inf.continuous).Homotopic
      (((segRight.symm.trans γ1₁.symm).trans γ0₂.symm).trans segLeft.symm) :=
    isPathHomotopyTrivial_def.mp isSimplyConnected_lower.isPathHomotopyTrivial _ _
      (by
        rintro _ ⟨t, rfl⟩
        exact im_coe_mob1Inf_nonpos (range_γ1₂_subset ⟨t, rfl⟩))
      (by
        simp only [Path.trans_range, Path.symm_range]
        exact union_subset (union_subset (union_subset
          (subset_halfPlanes_of_real (range_realSegment_subset ..)).2 range_γ1₁_subset)
            range_γ0₂_subset)
          (subset_halfPlanes_of_real (range_realSegment_subset ..)).2)
  rw [← Path.Homotopic.Quotient.eq] at hL hU
  -- `periph0` and `periph1` are by definition the classes of `γ0` and `γ1`
  have h0 : periph0 = FundamentalGroup.fromPath (.mk γ0) := periph0_def
  have h1 : periph1 = FundamentalGroup.fromPath (.mk γ1) := periph1_def
  -- check `mob1InfMulAut periph1 * (periph1 * periph0) = 1`, which involves no inverse of a product
  rw [periphInf_def, eq_inv_iff_mul_eq_one, h1, h0, mob1InfMulAut_fromPath,
    FundamentalGroup.mul_def, FundamentalGroup.mul_def, FundamentalGroup.one_def,
    mk_map_mob1Inf mk_γ1, hL, hU]
  -- the word cancels letter by letter once it is reassociated to the right
  have hcancel {x y z : ThricePuncturedSphere} (p : Path.Homotopic.Quotient x y)
      (q : Path.Homotopic.Quotient x z) : p.trans (p.symm.trans q) = q := by
    rw [← Path.Homotopic.Quotient.trans_assoc, Path.Homotopic.Quotient.trans_symm,
      Path.Homotopic.Quotient.refl_trans]
  have hcancel' {x y z : ThricePuncturedSphere} (p : Path.Homotopic.Quotient x y)
      (q : Path.Homotopic.Quotient y z) : p.symm.trans (p.trans q) = q := by
    rw [← Path.Homotopic.Quotient.trans_assoc, Path.Homotopic.Quotient.symm_trans,
      Path.Homotopic.Quotient.refl_trans]
  simp only [mk_γ0, mk_γ1, αMob1Inf, Path.trans_symm, Path.symm_symm,
    Path.Homotopic.Quotient.mk_trans, Path.Homotopic.Quotient.mk_symm,
    Path.Homotopic.Quotient.trans_assoc, hcancel, hcancel', Path.Homotopic.Quotient.trans_symm]

/-- `z ↦ z / (z − 1)` carries the peripheral element at `∞` to the conjugate
`periph0⁻¹ * periph1 * periph0` of the peripheral element at `1`. -/
@[simp]
theorem mob1InfMulAut_periphInf :
    mob1InfMulAut periphInf = periph0⁻¹ * periph1 * periph0 := by
  rw [periphInf_def, map_inv, map_mul, mob1InfMulAut_periph0, mob1InfMulAut_periph1,
    periphInf_def]
  group

/-- The inverse of `mob1InfMulAut` fixes `periph0`. -/
@[simp]
theorem mob1InfMulAut_symm_periph0 : mob1InfMulAut.symm periph0 = periph0 := by
  rw [MulEquiv.symm_apply_eq, mob1InfMulAut_periph0]

/-- The inverse of `mob1InfMulAut` carries `periph1` to `periph1⁻¹ * periphInf * periph1`, the
second component of the branch-point operation exchanging `1` and `∞`. -/
@[simp]
theorem mob1InfMulAut_symm_periph1 :
    mob1InfMulAut.symm periph1 = periph1⁻¹ * periphInf * periph1 := by
  rw [MulEquiv.symm_apply_eq, map_mul, map_mul, map_inv, mob1InfMulAut_periph1,
    mob1InfMulAut_periphInf, periphInf_def]
  group

end ThricePuncturedSphere

end TauCeti
