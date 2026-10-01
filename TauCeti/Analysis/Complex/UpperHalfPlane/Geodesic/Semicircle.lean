/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.UpperHalfPlane.Geodesic.Angle
public import TauCeti.Analysis.Complex.UpperHalfPlane.Geodesic.Between
public import TauCeti.Analysis.Complex.UpperHalfPlane.HalfPlane
public import TauCeti.Analysis.Complex.UpperHalfPlane.PSL.Translation

/-!
# The geodesic through two points as a semicircle

This file makes the classical description of the geodesics of `ℍ` quantitative, for the geodesic
`geodesicBetween P Q` from `P` to `Q`. The affine map `toPoint P : z ↦ P.im * z + P.re` sends `I`
to `P`, so `geodesicBetween P Q` is `toPoint P` followed by a rotation of the imaginary axis
(`exists_geodesicBetween_eq_toPoint_mul_rotation`); the half-planes of a rotated axis are given
by an explicit quadratic form (`mem_rightHalfPlane_rotation_iff`).

When `P.re ≠ Q.re`, the geodesic through `P` and `Q` is the semicircle centred at
`circleCenter P Q` on the real axis (`mem_range_geodesicLine_geodesicBetween_iff_of_re_ne`), its
right half-plane is the inside of that disc when `Q` is to the right of `P` and the outside when
`Q` is to the left (`mem_rightHalfPlane_geodesicBetween_iff_of_re_lt`,
`mem_rightHalfPlane_geodesicBetween_iff_of_lt_re`), and its velocity at `P` is tangent to the
semicircle, oriented clockwise exactly when `Q` is to the right of `P`
(`exists_velocity_geodesicBetween_zero_eq`). When `P.re = Q.re` the geodesic is the vertical line
through `P` (`geodesicBetween_eq_toPoint_of_re_eq`,
`mem_rightHalfPlane_geodesicBetween_iff_of_re_eq`,
`exists_velocity_geodesicBetween_zero_eq_of_re_eq`).

Source: Katok, *Fuchsian groups, geodesic flows…*, Clay Math. Proc. 8 (2008), §3 Theorem 3.1
(p. 10): the geodesics in `ℍ` are the semicircles and the rays orthogonal to the real axis.
-/

public section

noncomputable section

open Matrix.ProjectiveSpecialLinearGroup UpperHalfPlane
open scoped MatrixGroups Pointwise Real

namespace TauCeti.UpperHalfPlane

open Matrix.SpecialLinearGroup (rotation dilation)

/-! ### The half-planes of a rotated axis, explicitly -/

/-- The real part after the inverse rotation by `θ`, as a quadratic form in the point: the
numerator vanishes exactly on the rotated imaginary axis. -/
theorem re_rotation_inv_smul (θ : ℝ) (w : ℍ) :
    (((↑(rotation θ) : PSL(2, ℝ))⁻¹ • w : ℍ)).re =
      (Real.sin θ * Real.cos θ * (Complex.normSq (w : ℂ) - 1) +
          (Real.cos θ ^ 2 - Real.sin θ ^ 2) * w.re) /
        Complex.normSq ((Real.sin θ : ℂ) * w + Real.cos θ) := by
  rw [← QuotientGroup.mk_inv, Matrix.SpecialLinearGroup.rotation_inv, UpperHalfPlane.pslMk_smul,
    ← UpperHalfPlane.coe_re, UpperHalfPlane.coe_specialLinearGroup_apply]
  simp only [Matrix.SpecialLinearGroup.coe_rotation, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    Algebra.algebraMap_self_apply, Real.cos_neg, Real.sin_neg, neg_neg, Complex.ofReal_neg]
  rw [Complex.div_re, ← add_div]
  congr 1
  simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.neg_re,
    Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im, Complex.normSq_apply,
    UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
  ring

/-- The denominator of `re_rotation_inv_smul` is positive. -/
theorem normSq_sin_mul_add_cos_pos (θ : ℝ) (w : ℍ) :
    0 < Complex.normSq ((Real.sin θ : ℂ) * w + Real.cos θ) := by
  refine Complex.normSq_pos.2 fun h ↦ ?_
  rw [UpperHalfPlane.ofReal_mul_add_eq_zero_iff] at h
  nlinarith [Real.sin_sq_add_cos_sq θ, h.1, h.2]

/-- Membership in the right half-plane of a rotated axis, as a quadratic inequality. -/
theorem mem_rightHalfPlane_rotation_iff (θ : ℝ) (w : ℍ) :
    w ∈ rightHalfPlane (↑(rotation θ)) ↔
      0 < Real.sin θ * Real.cos θ * (Complex.normSq (w : ℂ) - 1) +
        (Real.cos θ ^ 2 - Real.sin θ ^ 2) * w.re := by
  rw [mem_rightHalfPlane_iff, re_rotation_inv_smul, div_pos_iff_of_pos_right
    (normSq_sin_mul_add_cos_pos θ w)]

/-- The real part of a point of the rotated axis, at height `y` before rotating. -/
theorem re_rotation_smul_mk (θ y : ℝ) (hy : 0 < y) :
    (rotation θ • UpperHalfPlane.mk ⟨0, y⟩ hy).re =
      Real.sin θ * Real.cos θ * (1 - y ^ 2) /
        Complex.normSq ((Real.cos θ : ℂ) - Complex.I * y * Real.sin θ) := by
  rw [← UpperHalfPlane.coe_re, UpperHalfPlane.coe_specialLinearGroup_apply]
  simp only [Matrix.SpecialLinearGroup.coe_rotation, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    Algebra.algebraMap_self_apply, Complex.ofReal_neg]
  have h : (⟨0, y⟩ : ℂ) = Complex.I * y := by simp [Complex.ext_iff]
  rw [h, Complex.div_re, ← add_div]
  have hden : (-(Real.sin θ : ℂ)) * (Complex.I * y) + Real.cos θ =
      (Real.cos θ : ℂ) - Complex.I * y * Real.sin θ := by ring
  rw [hden]
  congr 1
  simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.sub_re,
    Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
  ring

/-! ### Moving `I` to a given point -/

/-- The affine map `z ↦ P.im * z + P.re`, an element of `PSL(2, ℝ)` sending `I` to `P`. -/
def toPoint (P : ℍ) : PSL(2, ℝ) := upperRightHom P.re * ↑(dilation (Real.log P.im))

/-- `toPoint P` acts on `ℍ` as `z ↦ P.im * z + P.re`. -/
theorem coe_toPoint_smul (P z : ℍ) : ((toPoint P • z : ℍ) : ℂ) = P.im * z + P.re := by
  rw [toPoint, mul_smul, UpperHalfPlane.pslMk_smul, upperRightHom_smul, UpperHalfPlane.coe_vadd,
    coe_dilation_smul, Real.exp_log P.im_pos, add_comm]

@[simp]
theorem toPoint_smul_I (P : ℍ) : toPoint P • UpperHalfPlane.I = P := by
  apply UpperHalfPlane.coe_injective
  rw [coe_toPoint_smul, UpperHalfPlane.coe_I]
  apply Complex.ext <;> simp

/-- The inverse of `toPoint P` acts on `ℍ` as `z ↦ (z - P.re) / P.im`. -/
theorem coe_toPoint_inv_smul (P z : ℍ) :
    (((toPoint P)⁻¹ • z : ℍ) : ℂ) = ((z : ℂ) - P.re) / P.im := by
  have h := coe_toPoint_smul P ((toPoint P)⁻¹ • z)
  rw [smul_inv_smul] at h
  rw [eq_div_iff (by exact_mod_cast P.im_pos.ne')]
  linear_combination -h

/-- The centre on the real axis of the semicircle through `P` and `Q`, when `P.re ≠ Q.re`. -/
def circleCenter (P Q : ℍ) : ℝ :=
  (Complex.normSq (Q : ℂ) - Complex.normSq (P : ℂ)) / (2 * (Q.re - P.re))

-- The body of `circleCenter` is not `@[expose]`d; downstream modules rewrite with this equation.
/-- The centre of the semicircle through `P` and `Q`, as a formula. -/
theorem circleCenter_def (P Q : ℍ) :
    circleCenter P Q = (Complex.normSq (Q : ℂ) - Complex.normSq (P : ℂ)) / (2 * (Q.re - P.re)) := by
  rfl

/-- The derivative of the affine map `toPoint P` is `P.im`. -/
theorem smulDeriv_toPoint (P z : ℍ) : smulDeriv (toPoint P) z = P.im := by
  rw [toPoint, smulDeriv_mul, smulDeriv_upperRightHom, smulDeriv_dilation, Real.exp_log P.im_pos,
    one_mul]

/-- The real part of the normalised point `(toPoint P)⁻¹ • z`. -/
theorem re_toPoint_inv_smul (P z : ℍ) : ((toPoint P)⁻¹ • z : ℍ).re = (z.re - P.re) / P.im := by
  rw [← UpperHalfPlane.coe_re, coe_toPoint_inv_smul, div_eq_mul_inv, ← Complex.ofReal_inv,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, Complex.sub_re,
    Complex.ofReal_re, UpperHalfPlane.coe_re, div_eq_mul_inv]

/-- The norm-square of the normalised point `(toPoint P)⁻¹ • z`. -/
theorem normSq_toPoint_inv_smul (P z : ℍ) :
    Complex.normSq (((toPoint P)⁻¹ • z : ℍ) : ℂ) = Complex.normSq ((z : ℂ) - P.re) / P.im ^ 2 := by
  rw [coe_toPoint_inv_smul, map_div₀, Complex.normSq_ofReal, sq]

/-- The geodesic from `P` to `Q` is the normalising map of `P` followed by a rotation of the
imaginary axis. -/
theorem exists_geodesicBetween_eq_toPoint_mul_rotation {P Q : ℍ} (hPQ : P ≠ Q) :
    ∃ θ : ℝ, geodesicBetween P Q = toPoint P * ↑(rotation θ) ∧
      UpperHalfPlane.I ≠ (toPoint P)⁻¹ • Q ∧
        geodesicBetween UpperHalfPlane.I ((toPoint P)⁻¹ • Q) = ↑(rotation θ) := by
  have hne : UpperHalfPlane.I ≠ (toPoint P)⁻¹ • Q := by
    intro h
    apply hPQ
    rw [← toPoint_smul_I P, h, smul_inv_smul]
  obtain ⟨θ, hθ⟩ := exists_geodesicBetween_I_eq_rotation ((toPoint P)⁻¹ • Q)
  refine ⟨θ, ?_, hne, hθ⟩
  rw [← hθ, ← geodesicBetween_smul (toPoint P) hne, toPoint_smul_I, smul_inv_smul]

private theorem pos_mul_iff_of_pos_mul {a b X : ℝ} (h : 0 < a * b) : 0 < a * X ↔ 0 < b * X := by
  rcases mul_pos_iff.1 h with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · rw [mul_pos_iff_of_pos_left ha, mul_pos_iff_of_pos_left hb]
  · rw [← neg_mul_neg a X, ← neg_mul_neg b X, mul_pos_iff_of_pos_left (neg_pos.2 ha),
      mul_pos_iff_of_pos_left (neg_pos.2 hb)]

/-- The semicircle case: the geodesic from `P` to `Q` is `toPoint P` followed by a rotation
by an angle `θ`, whose sign is opposite to that of `Q.re - P.re`, and the centre of the
semicircle through `P` and `Q` is `P.re - cos 2θ / sin 2θ · P.im`. -/
theorem exists_rotation_of_re_ne {P Q : ℍ} (hPQ : P.re ≠ Q.re) :
    ∃ θ : ℝ, geodesicBetween P Q = toPoint P * ↑(rotation θ) ∧
      0 < Real.sin θ * Real.cos θ * (P.re - Q.re) ∧
        circleCenter P Q = P.re -
          (Real.cos θ ^ 2 - Real.sin θ ^ 2) * P.im / (2 * (Real.sin θ * Real.cos θ)) := by
  obtain ⟨θ, hgb, hne, hθ⟩ :=
    exists_geodesicBetween_eq_toPoint_mul_rotation (fun h ↦ hPQ (h ▸ rfl) : P ≠ Q)
  set Q' : ℍ := (toPoint P)⁻¹ • Q with hQ'
  set α := Real.sin θ * Real.cos θ with hα
  set β := Real.cos θ ^ 2 - Real.sin θ ^ 2 with hβ
  have hQ're : Q'.re = (Q.re - P.re) / P.im := re_toPoint_inv_smul P Q
  have hQ'n : Complex.normSq (Q' : ℂ) = Complex.normSq ((Q : ℂ) - P.re) / P.im ^ 2 :=
    normSq_toPoint_inv_smul P Q
  -- `Q'` lies on the rotated axis: the quadratic form vanishes at it
  have hd : Q' = rotation θ • UpperHalfPlane.mk ⟨0, Real.exp (dist UpperHalfPlane.I Q')⟩
      (Real.exp_pos _) := by
    have h := geodesicLine_geodesicBetween_dist UpperHalfPlane.I Q'
    rw [hθ, geodesicLine_def, UpperHalfPlane.pslMk_smul] at h
    exact h.symm
  have hE1 : α * (Complex.normSq (Q' : ℂ) - 1) + β * Q'.re = 0 := by
    have h0 : (((↑(rotation θ) : PSL(2, ℝ))⁻¹ • Q' : ℍ)).re = 0 := by
      rw [hd, ← UpperHalfPlane.pslMk_smul, inv_smul_smul]
      rfl
    rw [re_rotation_inv_smul, div_eq_zero_iff] at h0
    exact h0.resolve_right (normSq_sin_mul_add_cos_pos θ Q').ne'
  -- the sign of `α` is opposite to the sign of `Q.re - P.re`
  have hE2 : 0 < α * (P.re - Q.re) := by
    have hs : 0 < dist UpperHalfPlane.I Q' := dist_pos.2 hne
    have hre := re_rotation_smul_mk θ (Real.exp (dist UpperHalfPlane.I Q')) (Real.exp_pos _)
    rw [← hd, hQ're, ← hα] at hre
    have hy : 1 < Real.exp (dist UpperHalfPlane.I Q') ^ 2 := by
      have := Real.one_lt_exp_iff.2 hs
      nlinarith
    have hN : 0 < Complex.normSq ((Real.cos θ : ℂ) -
        Complex.I * Real.exp (dist UpperHalfPlane.I Q') * Real.sin θ) := by
      refine Complex.normSq_pos.2 fun h ↦ ?_
      have h1 := congrArg Complex.re h
      have h2 := congrArg Complex.im h
      simp only [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.I_re,
        Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, Complex.zero_re,
        Complex.zero_im] at h1 h2
      ring_nf at h1 h2
      nlinarith [Real.sin_sq_add_cos_sq θ, Real.exp_pos (dist UpperHalfPlane.I Q'), h1, h2]
    have hα0 : α ≠ 0 := by
      intro h0
      rw [h0, zero_mul, zero_div, div_eq_zero_iff] at hre
      rcases hre with hre | hre
      · exact hPQ (by linarith)
      · exact P.im_pos.ne' hre
    have hprod : α * ((Q.re - P.re) / P.im) < 0 := by
      rw [hre, mul_div_assoc', div_neg_iff]
      right
      exact ⟨by nlinarith [sq_pos_of_ne_zero hα0], hN⟩
    have : α * (Q.re - P.re) < 0 := by
      rw [mul_div_assoc'] at hprod
      exact (div_neg_iff.1 hprod).resolve_left (fun h ↦ (P.im_pos.not_gt h.2)) |>.1
    linarith
  have hα0 : α ≠ 0 := fun h ↦ by simp [h] at hE2
  -- identify the centre
  have hP := P.im_pos.ne'
  have hQP : Q.re - P.re ≠ 0 := sub_ne_zero.2 (Ne.symm hPQ)
  have hE1' : α * ((Q.re - P.re) ^ 2 + Q.im ^ 2 - P.im ^ 2) + β * P.im * (Q.re - P.re) = 0 := by
    rw [hQ're, hQ'n, Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.ofReal_re,
      Complex.ofReal_im, sub_zero, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im] at hE1
    field_simp at hE1
    linear_combination hE1
  have hcc : circleCenter P Q * (2 * (Q.re - P.re)) =
      Q.re ^ 2 + Q.im ^ 2 - (P.re ^ 2 + P.im ^ 2) := by
    rw [circleCenter, div_mul_cancel₀ _ (mul_ne_zero two_ne_zero hQP), Complex.normSq_apply,
      Complex.normSq_apply, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im, UpperHalfPlane.coe_re,
      UpperHalfPlane.coe_im]
    ring
  have hc : circleCenter P Q = P.re - β * P.im / (2 * α) := by
    have h2 : 2 * α * (Q.re - P.re) * (β * P.im / (2 * α)) = (Q.re - P.re) * (β * P.im) := by
      field_simp
    refine mul_left_cancel₀ (mul_ne_zero (mul_ne_zero two_ne_zero hα0) hQP) ?_
    rw [mul_sub (2 * α * (Q.re - P.re)) P.re, h2]
    linear_combination α * hcc + hE1'
  exact ⟨θ, hgb, hE2, hc⟩

/-- The semicircle case: after applying the inverse of the geodesic from `P` to `Q`, the real
part of a point is a positive multiple of `(P.re - Q.re) · (|z - c|² - |P - c|²)`, where `c` is
the centre of the semicircle through `P` and `Q`. -/
theorem exists_re_inv_geodesicBetween_smul_eq {P Q : ℍ} (hPQ : P.re ≠ Q.re) (z : ℍ) :
    ∃ κ : ℝ, 0 < κ ∧ ((geodesicBetween P Q)⁻¹ • z : ℍ).re =
      κ * ((P.re - Q.re) * (Complex.normSq ((z : ℂ) - circleCenter P Q) -
        Complex.normSq ((P : ℂ) - circleCenter P Q))) := by
  obtain ⟨θ, hgb, hE2, hc⟩ := exists_rotation_of_re_ne hPQ
  set α := Real.sin θ * Real.cos θ with hα
  set β := Real.cos θ ^ 2 - Real.sin θ ^ 2 with hβ
  have hP := P.im_pos.ne'
  have hα0 : α ≠ 0 := fun h ↦ by simp [h] at hE2
  have hQP : P.re - Q.re ≠ 0 := sub_ne_zero.2 hPQ
  rw [hgb, mul_inv_rev, mul_smul, re_rotation_inv_smul, re_toPoint_inv_smul,
    normSq_toPoint_inv_smul]
  set N := Complex.normSq ((Real.sin θ : ℂ) * (((toPoint P)⁻¹ • z : ℍ) : ℂ) + Real.cos θ)
    with hN
  have hN0 : 0 < N := normSq_sin_mul_add_cos_pos θ _
  have key : α * (Complex.normSq ((z : ℂ) - P.re) / P.im ^ 2 - 1) + β * ((z.re - P.re) / P.im) =
      (α / P.im ^ 2) * (Complex.normSq ((z : ℂ) - circleCenter P Q) -
        Complex.normSq ((P : ℂ) - circleCenter P Q)) := by
    rw [hc]
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.ofReal_re,
      Complex.ofReal_im, sub_zero, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
    field_simp
    ring
  rw [key]
  refine ⟨α * (P.re - Q.re) / (P.im ^ 2 * N * (P.re - Q.re) ^ 2),
    div_pos hE2 (by positivity), ?_⟩
  field_simp

/-- The semicircle case of the description of the half-planes of `geodesicBetween P Q`: the
right half-plane is the inside of the disc through `P` and `Q` centred on the real axis when
`Q` is to the right of `P`, and the outside when it is to the left. -/
theorem mem_rightHalfPlane_geodesicBetween_iff_of_re_ne {P Q : ℍ} (hPQ : P.re ≠ Q.re) (z : ℍ) :
    z ∈ rightHalfPlane (geodesicBetween P Q) ↔
      0 < (P.re - Q.re) * (Complex.normSq ((z : ℂ) - circleCenter P Q) -
        Complex.normSq ((P : ℂ) - circleCenter P Q)) := by
  obtain ⟨κ, hκ, h⟩ := exists_re_inv_geodesicBetween_smul_eq hPQ z
  rw [mem_rightHalfPlane_iff, h, mul_pos_iff_of_pos_left hκ]

/-- The left half-plane of the geodesic from `P` to `Q`, in the semicircle case. -/
theorem mem_leftHalfPlane_geodesicBetween_iff_of_re_ne {P Q : ℍ} (hPQ : P.re ≠ Q.re) (z : ℍ) :
    z ∈ leftHalfPlane (geodesicBetween P Q) ↔
      (P.re - Q.re) * (Complex.normSq ((z : ℂ) - circleCenter P Q) -
        Complex.normSq ((P : ℂ) - circleCenter P Q)) < 0 := by
  obtain ⟨κ, hκ, h⟩ := exists_re_inv_geodesicBetween_smul_eq hPQ z
  rw [mem_leftHalfPlane_iff, h]
  exact ⟨fun h ↦ neg_of_mul_neg_right h hκ.le, fun h ↦ mul_neg_of_pos_of_neg hκ h⟩

/-- The geodesic through `P` and `Q`, as a set, is the semicircle through them centred on the
real axis. -/
theorem mem_range_geodesicLine_geodesicBetween_iff_of_re_ne {P Q : ℍ} (hPQ : P.re ≠ Q.re)
    (z : ℍ) :
    z ∈ Set.range (geodesicLine (geodesicBetween P Q)) ↔
      Complex.normSq ((z : ℂ) - circleCenter P Q) =
        Complex.normSq ((P : ℂ) - circleCenter P Q) := by
  obtain ⟨κ, hκ, h⟩ := exists_re_inv_geodesicBetween_smul_eq hPQ z
  rw [mem_range_geodesicLine_iff, h, mul_eq_zero, mul_eq_zero, sub_eq_zero, sub_eq_zero]
  simp [hκ.ne', hPQ]

/-- The centre of the semicircle through two points does not depend on their order. -/
theorem circleCenter_comm (P Q : ℍ) : circleCenter Q P = circleCenter P Q := by
  rw [circleCenter, circleCenter, ← neg_sub (Complex.normSq (Q : ℂ)), ← neg_sub Q.re, mul_neg,
    neg_div_neg_eq]

/-- Both endpoints lie on the semicircle: they are equidistant from its centre. -/
theorem normSq_sub_circleCenter {P Q : ℍ} (hPQ : P.re ≠ Q.re) :
    Complex.normSq ((Q : ℂ) - circleCenter P Q) = Complex.normSq ((P : ℂ) - circleCenter P Q) := by
  have hQP : Q.re - P.re ≠ 0 := sub_ne_zero.2 (Ne.symm hPQ)
  have hcc : circleCenter P Q * (2 * (Q.re - P.re)) =
      Complex.normSq (Q : ℂ) - Complex.normSq (P : ℂ) := by
    rw [circleCenter, div_mul_cancel₀ _ (mul_ne_zero two_ne_zero hQP)]
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.ofReal_re,
    Complex.ofReal_im, sub_zero, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im] at hcc ⊢
  linear_combination -hcc

/-- The geodesic from `P` to a point `Q` to its right runs clockwise along the semicircle through
them, so its right half-plane is the inside of the disc. -/
theorem mem_rightHalfPlane_geodesicBetween_iff_of_re_lt {P Q : ℍ} (hPQ : P.re < Q.re) (z : ℍ) :
    z ∈ rightHalfPlane (geodesicBetween P Q) ↔
      Complex.normSq ((z : ℂ) - circleCenter P Q) <
        Complex.normSq ((P : ℂ) - circleCenter P Q) := by
  rw [mem_rightHalfPlane_geodesicBetween_iff_of_re_ne hPQ.ne, ← neg_mul_neg, neg_sub, neg_sub,
    mul_pos_iff_of_pos_left (sub_pos.2 hPQ), sub_pos]

/-- The geodesic from `P` to a point `Q` to its left runs counterclockwise along the semicircle
through them, so its right half-plane is the outside of the disc. -/
theorem mem_rightHalfPlane_geodesicBetween_iff_of_lt_re {P Q : ℍ} (hPQ : Q.re < P.re) (z : ℍ) :
    z ∈ rightHalfPlane (geodesicBetween P Q) ↔
      Complex.normSq ((P : ℂ) - circleCenter P Q) <
        Complex.normSq ((z : ℂ) - circleCenter P Q) := by
  rw [mem_rightHalfPlane_geodesicBetween_iff_of_re_ne hPQ.ne',
    mul_pos_iff_of_pos_left (sub_pos.2 hPQ), sub_pos]

/-- The geodesic from `P` up to a point `Q` above it is the vertical line through `P`. -/
theorem geodesicBetween_eq_toPoint_of_re_eq {P Q : ℍ} (h : P.re = Q.re) (hPQ : P.im < Q.im) :
    geodesicBetween P Q = toPoint P := by
  symm
  refine eq_geodesicBetween_of_geodesicLine_eq (fun hne ↦ hPQ.ne (hne ▸ rfl)) ?_ ?_
  · rw [geodesicLine_zero, toPoint_smul_I]
  · rw [geodesicLine_def]
    apply UpperHalfPlane.coe_injective
    rw [coe_toPoint_smul, UpperHalfPlane.coe_mk, UpperHalfPlane.dist_of_re_eq h, Real.dist_eq,
      abs_of_neg (sub_neg.2 (Real.log_lt_log P.im_pos hPQ)), neg_sub, Real.exp_sub,
      Real.exp_log Q.im_pos, Real.exp_log P.im_pos]
    apply Complex.ext
    · simp [h]
    · simp
      field_simp

/-- The geodesic from `P` up to a point `Q` above it is a vertical line; its right half-plane is
the side of larger real part. -/
theorem mem_rightHalfPlane_geodesicBetween_iff_of_re_eq {P Q : ℍ} (h : P.re = Q.re)
    (hPQ : P.im < Q.im) (z : ℍ) :
    z ∈ rightHalfPlane (geodesicBetween P Q) ↔ P.re < z.re := by
  rw [geodesicBetween_eq_toPoint_of_re_eq h hPQ, mem_rightHalfPlane_iff, re_toPoint_inv_smul,
    div_pos_iff_of_pos_right P.im_pos, sub_pos]

/-- The velocity at `P` of the geodesic from `P` to `Q` is tangent to the semicircle through
them, with the clockwise orientation exactly when `Q` is to the right of `P`. -/
theorem exists_velocity_geodesicBetween_zero_eq {P Q : ℍ} (hPQ : P.re ≠ Q.re) :
    ∃ μ : ℝ, μ * (Q.re - P.re) < 0 ∧
      velocity (geodesicBetween P Q) 0 = μ * (Complex.I * ((P : ℂ) - circleCenter P Q)) := by
  obtain ⟨θ, hgb, hE2, hc⟩ := exists_rotation_of_re_ne hPQ
  have hα0 : Real.sin θ * Real.cos θ ≠ 0 := fun h ↦ by simp [h] at hE2
  refine ⟨2 * (Real.sin θ * Real.cos θ), ?_, ?_⟩
  · have h : 2 * (Real.sin θ * Real.cos θ) * (Q.re - P.re) =
        -2 * (Real.sin θ * Real.cos θ * (P.re - Q.re)) := by ring
    linarith
  · rw [hgb, velocity_mul, geodesicLine_zero, UpperHalfPlane.pslMk_smul, rotation_smul_I,
      smulDeriv_toPoint, velocity_rotation_zero, hc, ← UpperHalfPlane.re_add_im P]
    have he : Complex.exp (2 * θ * Complex.I) =
        ((Real.cos θ : ℂ) + Real.sin θ * Complex.I) ^ 2 := by
      have h2θ : (2 * θ * Complex.I : ℂ) = θ * Complex.I + θ * Complex.I := by ring
      rw [h2θ, Complex.exp_add, Complex.exp_mul_I, sq, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    rw [he]
    obtain ⟨hs, hcθ⟩ := mul_ne_zero_iff.1 hα0
    apply Complex.ext
    · simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.sub_re,
        Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, sq]
      field_simp
      ring
    · simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.sub_re,
        Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, sq]
      field_simp
      ring

/-- The velocity at `P` of the vertical geodesic from `P` to `Q` points up exactly when `Q` is
above `P`. -/
theorem exists_velocity_geodesicBetween_zero_eq_of_re_eq {P Q : ℍ} (h : P.re = Q.re)
    (hPQ : P ≠ Q) :
    ∃ μ : ℝ, 0 < μ ∧ velocity (geodesicBetween P Q) 0 = (μ * (Q.im - P.im)) * Complex.I := by
  rcases lt_trichotomy P.im Q.im with hlt | heq | hgt
  · refine ⟨P.im / (Q.im - P.im), div_pos P.im_pos (sub_pos.2 hlt), ?_⟩
    rw [geodesicBetween_eq_toPoint_of_re_eq h hlt, velocity_def, smulDeriv_toPoint, Real.exp_zero,
      Complex.ofReal_one, mul_one, ← Complex.ofReal_sub, ← Complex.ofReal_mul,
      div_mul_cancel₀ _ (sub_pos.2 hlt).ne']
  · exact absurd (UpperHalfPlane.ext (Complex.ext h heq)) hPQ
  · have hne : P.im - Q.im ≠ 0 := (sub_pos.2 hgt).ne'
    refine ⟨Q.im * Real.exp (dist Q P) / (P.im - Q.im), by positivity, ?_⟩
    rw [geodesicBetween_swap hPQ.symm, geodesicBetween_eq_toPoint_of_re_eq h.symm hgt,
      velocity_mul_pslS, neg_zero, velocity_mul_dilation, add_zero, velocity_def,
      smulDeriv_toPoint]
    have hμ : Q.im * Real.exp (dist Q P) / (P.im - Q.im) * (Q.im - P.im) =
        -(Q.im * Real.exp (dist Q P)) := by
      field_simp
      ring
    rw [← Complex.ofReal_sub, ← Complex.ofReal_mul, hμ]
    push_cast
    ring

end TauCeti.UpperHalfPlane
