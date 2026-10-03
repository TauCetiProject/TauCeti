/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.UpperHalfPlane.Geodesic.FromTo
public import TauCeti.Analysis.Complex.UpperHalfPlane.Geodesic.InteriorAngle
public import TauCeti.Analysis.Complex.UpperHalfPlane.PSL.Affine
import TauCeti.Analysis.Complex.UpperHalfPlane.Geodesic.Orientation
import TauCeti.Analysis.Complex.UpperHalfPlane.Geodesic.Semicircle
import TauCeti.Analysis.Complex.UpperHalfPlane.PSL.Translation

/-!
# Rays to points of `ℍ ∪ ∂ℍ` and angles at a vertex

`rayToward A p` is the geodesic line leaving `A ∈ ℍ` at parameter `0` towards a point `p` of
`ℍ ∪ ∂ℍ`: `geodesicBetween A B` for `p = B ∈ ℍ`, and for an ideal point `ξ` the unique geodesic
line with `A` at parameter `0` and forward endpoint `ξ`. The angle at a vertex `p` of `ℍ ∪ ∂ℍ`
between the directions to `q` and `r` (`vertexAngle p q r`) is the angle between the two rays
when `p ∈ ℍ`, and `0` at an ideal vertex (Walkden §7.1: geodesics meet `∂ℍ` at right angles). On
three points of `ℍ` it is `UpperHalfPlane.interiorAngle` (`vertexAngle_inl_inl_inl`).

When the vertex is a point `w` of the semicircle of centre `m` and radius `ρ` (or one of its two
ideal endpoints), the angle between the upward vertical through `w` and the semicircle is an
arccosine of `(Re w - m) / ρ` (`vertexAngle_infty_of_re_lt`, `vertexAngle_infty_of_lt_re`), and
at a vertex where two semicircles meet with the upward vertical inside the angle, the angle is
the sum of the angles to the vertical (`vertexAngle_eq_add_of_mem_circles`). These are the angles
of a hyperbolic triangle with an ideal vertex at `∞`, in the normal form of Walkden's and Katok's
proofs of the Gauss–Bonnet formula.

## Main declarations

* `TauCeti.UpperHalfPlane.rayToward A p`: the geodesic ray from `A ∈ ℍ` towards `p ∈ ℍ ∪ ∂ℍ`.
* `TauCeti.UpperHalfPlane.rayToward_inr_infty`, `TauCeti.UpperHalfPlane.isGeodesicFromTo_rayToward`,
  `TauCeti.UpperHalfPlane.rayToward_smul`: the ray towards `∞` is the upward vertical; a ray runs
  from its base point to its target; rays are equivariant.
* `TauCeti.UpperHalfPlane.IsGeodesicFromTo.re_toComplex_lt_iff`,
  `TauCeti.UpperHalfPlane.IsGeodesicFromTo.normSq_geodesicLine_sub`: a geodesic line through two
  points of a semicircle centred on the real axis lies on it, and passes its points in order.
* `UpperHalfPlane.vertexAngle p q r`: the angle at a vertex of `ℍ ∪ ∂ℍ`.
* `UpperHalfPlane.vertexAngle_infty_of_re_lt`, `UpperHalfPlane.vertexAngle_infty_of_lt_re`: the
  angles at the two finite vertices of a triangle with an ideal vertex at `∞`.
* `UpperHalfPlane.vertexAngle_eq_add_of_mem_circles`: an angle split by the upward vertical.

## Source

Walkden, *Hyperbolic geometry* (MATH32051 lecture notes, Manchester 2019), §7.1 (the unique geodesic
through two points of `ℍ ∪ ∂ℍ`; the angle at an ideal vertex is zero) and the proof of Theorem 7.2.1
(the angles of a triangle with a vertex at `∞`, with the other two vertices on a semicircle, read
off as `π - α` and `β` at the endpoints of the radius vectors); Katok, *Fuchsian groups, geodesic
flows…*, Clay Math. Proc. 10 (2010), §5, proof of Theorem 5.4 (Figure 5.2: the angles at the two
finite vertices are the angles between the radius vectors and the real axis, "as angles with
mutually perpendicular sides"), and §13, proof of Siegel's theorem (the angle between consecutive
sides is the sum `ωₖ = βₖ + γₖ₊₁` of the angles they make with the vertical through their common
vertex).
-/

public section

noncomputable section

open UpperHalfPlane
open scoped MatrixGroups Pointwise OnePoint Real

namespace TauCeti.UpperHalfPlane

open Matrix.ProjectiveSpecialLinearGroup (upperRightHom upperRightHom_smul_infty)
open Matrix.SpecialLinearGroup (dilation)

/-! ### Rays -/

/-- The affine map `toPoint A`, `z ↦ Re A + Im A · z`, fixes the ideal point `∞`. -/
@[simp]
theorem toPoint_smul_infty (A : ℍ) : toPoint A • (∞ : OnePoint ℝ) = ∞ := by
  -- `toPoint A` is the translation by `Re A` after the dilation by `Im A`, by faithfulness
  have h : toPoint A = upperRightHom A.re * ↑(dilation (Real.log A.im)) := by
    refine FaithfulSMul.eq_of_smul_eq_smul fun z ↦ UpperHalfPlane.coe_injective ?_
    rw [coe_toPoint_smul, mul_smul, UpperHalfPlane.pslMk_smul, upperRightHom_smul,
      UpperHalfPlane.coe_vadd, coe_dilation_smul, Real.exp_log A.im_pos, add_comm]
  rw [h, mul_smul, dilation_smul_infty, upperRightHom_smul_infty]

/-- The geodesic line leaving `A` at parameter `0` towards the point `p` of `ℍ ∪ ∂ℍ`:
`geodesicBetween A B` for `p = B ∈ ℍ`, and for an ideal point `ξ` the geodesic line with `A` at
parameter `0` and forward endpoint `ξ`. -/
def rayToward (A : ℍ) (p : ℍ ⊕ OnePoint ℝ) : PSL(2, ℝ) :=
  Sum.elim (geodesicBetween A) (fun ξ ↦ (exists_geodesicLine_zero_eq_and_smul_infty_eq A ξ).choose)
    p

@[simp]
theorem rayToward_inl (A B : ℍ) : rayToward A (.inl B) = geodesicBetween A B := by
  rfl

/-- A ray starts at its base point. -/
@[simp]
theorem geodesicLine_rayToward_zero (A : ℍ) (p : ℍ ⊕ OnePoint ℝ) :
    geodesicLine (rayToward A p) 0 = A := by
  rcases p with B | ξ
  · exact geodesicLine_geodesicBetween_zero A B
  · exact (exists_geodesicLine_zero_eq_and_smul_infty_eq A ξ).choose_spec.1

/-- A ray towards an ideal point has it as forward endpoint. -/
@[simp]
theorem rayToward_inr_smul_infty (A : ℍ) (ξ : OnePoint ℝ) :
    rayToward A (.inr ξ) • (∞ : OnePoint ℝ) = ξ :=
  (exists_geodesicLine_zero_eq_and_smul_infty_eq A ξ).choose_spec.2

/-- The ray from `A` towards `∞` is the upward vertical through `A`. -/
theorem rayToward_inr_infty (A : ℍ) : rayToward A (.inr ∞) = toPoint A :=
  eq_of_geodesicLine_zero_eq_of_smul_infty_eq
    (by rw [geodesicLine_rayToward_zero, geodesicLine_zero, toPoint_smul_I])
    (by rw [rayToward_inr_smul_infty, toPoint_smul_infty])

/-- The upward vertical through `A` keeps the real part of `A`. -/
@[simp]
theorem re_geodesicLine_toPoint (A : ℍ) (t : ℝ) : (geodesicLine (toPoint A) t).re = A.re := by
  rw [← coe_re, ← mul_one (toPoint A), ← smul_geodesicLine, coe_toPoint_smul,
    geodesicLine_one_apply]
  simp only [Complex.add_re, Complex.re_ofReal_mul, Complex.ofReal_re, mul_zero, zero_add]

/-- The upward vertical through `A` reaches height `Im A · exp t` at parameter `t`. -/
@[simp]
theorem im_geodesicLine_toPoint (A : ℍ) (t : ℝ) :
    (geodesicLine (toPoint A) t).im = A.im * Real.exp t := by
  rw [← coe_im, ← mul_one (toPoint A), ← smul_geodesicLine, coe_toPoint_smul,
    geodesicLine_one_apply]
  simp only [Complex.add_im, Complex.im_ofReal_mul, Complex.ofReal_im, add_zero]

/-- A ray from `A` towards `p ≠ A` runs from `A` to `p`. -/
theorem isGeodesicFromTo_rayToward {A : ℍ} {p : ℍ ⊕ OnePoint ℝ} (hAp : .inl A ≠ p) :
    IsGeodesicFromTo (rayToward A p) (.inl A) p := by
  rcases p with B | ξ
  · exact isGeodesicFromTo_geodesicBetween fun h ↦ hAp (congrArg _ h)
  · exact isGeodesicFromTo_inl_inr.2
      ⟨⟨0, geodesicLine_rayToward_zero A _⟩, rayToward_inr_smul_infty A ξ⟩

/-- Rays transform naturally under the action. -/
theorem rayToward_smul (h : PSL(2, ℝ)) {A : ℍ} {p : ℍ ⊕ OnePoint ℝ} (hAp : .inl A ≠ p) :
    rayToward (h • A) (h • p) = h * rayToward A p := by
  rcases p with B | ξ
  · rw [Sum.smul_inl, rayToward_inl, rayToward_inl,
      geodesicBetween_smul h fun hAB ↦ hAp (congrArg _ hAB)]
  · rw [Sum.smul_inr]
    refine eq_of_geodesicLine_zero_eq_of_smul_infty_eq ?_ ?_
    · rw [geodesicLine_rayToward_zero, ← smul_geodesicLine, geodesicLine_rayToward_zero]
    · rw [rayToward_inr_smul_infty, mul_smul, rayToward_inr_smul_infty]

/-- A ray is the geodesic from its base point to its point at parameter `1`. -/
theorem rayToward_eq_geodesicBetween (A : ℍ) (p : ℍ ⊕ OnePoint ℝ) :
    rayToward A p = geodesicBetween A (geodesicLine (rayToward A p) 1) := by
  have h₀ := geodesicLine_rayToward_zero A p
  have hne : A ≠ geodesicLine (rayToward A p) 1 := fun h ↦
    zero_ne_one (geodesicLine_injective _ (h₀.trans h))
  have hd : dist A (geodesicLine (rayToward A p) 1) = 1 := by
    simpa [h₀] using dist_geodesicLine (rayToward A p) 0 1
  exact eq_geodesicBetween_of_geodesicLine_eq hne h₀ (by rw [hd])

/-! ### Geodesic lines through two points of a semicircle -/

/-- A geodesic line running from `p` to `q` and to `r` (none of them `∞`), where `p` and `q` have
distinct real parts, reaches `r` on the same side of `p` as `q`. -/
theorem IsGeodesicFromTo.re_toComplex_lt_iff {g : PSL(2, ℝ)} {p q r : ℍ ⊕ OnePoint ℝ}
    (hpq : IsGeodesicFromTo g p q) (hpr : IsGeodesicFromTo g p r) (hp : p ≠ .inr ∞)
    (hq : q ≠ .inr ∞) (hre : (toComplex p).re ≠ (toComplex q).re) :
    (toComplex p).re < (toComplex r).re ↔ (toComplex p).re < (toComplex q).re := by
  have hp₀ := hpq.sideForm_toComplex_left hp
  have hq₀ := hpq.sideForm_toComplex_right hq
  -- neither endpoint of the line is `∞`: the line would be vertical, with `Re p = Re q`
  have h₀ : g • ((0 : ℝ) : OnePoint ℝ) ≠ ∞ := fun h₀ ↦ by
    obtain ⟨e, he⟩ := OnePoint.ne_infty_iff_exists.1 fun h₁ : g • (∞ : OnePoint ℝ) = ∞ ↦
      OnePoint.coe_ne_infty (0 : ℝ) (MulAction.injective g (h₀.trans h₁.symm))
    rw [sideForm_eq_of_smul_zero_eq_infty h₀ he.symm] at hp₀ hq₀
    exact hre (by linarith)
  have h₁ : g • (∞ : OnePoint ℝ) ≠ ∞ := fun h₁ ↦ by
    obtain ⟨e, he⟩ := OnePoint.ne_infty_iff_exists.1 fun h₀ : g • ((0 : ℝ) : OnePoint ℝ) = ∞ ↦
      OnePoint.coe_ne_infty (0 : ℝ) (MulAction.injective g (h₀.trans h₁.symm))
    rw [sideForm_eq_of_smul_infty_eq_infty he.symm h₁] at hp₀ hq₀
    exact hre (by linarith)
  obtain ⟨e₀, he₀⟩ := OnePoint.ne_infty_iff_exists.1 h₀
  obtain ⟨e₁, he₁⟩ := OnePoint.ne_infty_iff_exists.1 h₁
  have hne : e₀ ≠ e₁ := fun h ↦ OnePoint.coe_ne_infty (0 : ℝ)
    (MulAction.injective g (he₀.symm.trans ((congrArg _ h).trans he₁)))
  -- `∞` lies strictly on one side of the line; orient the line so that it is on the left
  rcases hne.lt_or_gt with h | h
  · have hinf := (infty_mem_boundaryLeftHalfPlane_iff he₀.symm he₁.symm).2 h
    exact iff_of_true (hpr.re_toComplex_lt hinf) (hpq.re_toComplex_lt hinf)
  · have hinf : (∞ : OnePoint ℝ) ∈ boundaryLeftHalfPlane (g * pslS) :=
      (infty_mem_boundaryLeftHalfPlane_iff (by rw [mul_smul, pslS_smul_zero, he₁])
        (by rw [mul_smul, pslS_smul_infty, he₀])).2 h
    exact iff_of_false (isGeodesicFromTo_mul_pslS_iff.2 hpr |>.re_toComplex_lt hinf).not_gt
      (isGeodesicFromTo_mul_pslS_iff.2 hpq |>.re_toComplex_lt hinf).not_gt

/-- A geodesic line running between two points (other than `∞`) of a circle centred on the real
axis, with distinct real parts, lies on that circle. -/
theorem IsGeodesicFromTo.normSq_geodesicLine_sub {g : PSL(2, ℝ)} {p q : ℍ ⊕ OnePoint ℝ} {m r : ℝ}
    (hg : IsGeodesicFromTo g p q) (hp : p ≠ .inr ∞) (hq : q ≠ .inr ∞)
    (hpm : Complex.normSq (toComplex p - m) = r) (hqm : Complex.normSq (toComplex q - m) = r)
    (hre : (toComplex p).re ≠ (toComplex q).re) (t : ℝ) :
    Complex.normSq ((geodesicLine g t : ℂ) - m) = r := by
  obtain ⟨α, hα, hs⟩ := exists_sideForm_eq_mul_normSq_sub (hg.sideForm_toComplex_left hp)
    (hg.sideForm_toComplex_right hq) hpm hqm hre
  have h := (mem_range_geodesicLine_iff_sideForm_eq_zero g _).1 ⟨t, rfl⟩
  rw [hs, mul_eq_zero, sub_eq_zero] at h
  exact h.resolve_left hα

end TauCeti.UpperHalfPlane

namespace UpperHalfPlane

open TauCeti.UpperHalfPlane

/-! ### The angle at a vertex of `ℍ ∪ ∂ℍ` -/

/-- The angle at the vertex `p` of `ℍ ∪ ∂ℍ` between the directions to `q` and `r`: the angle
between the rays towards `q` and `r` when `p ∈ ℍ`, and `0` when `p` is an ideal point. -/
def vertexAngle (p q r : ℍ ⊕ OnePoint ℝ) : ℝ :=
  Sum.elim (fun A ↦ geodesicAngle (rayToward A q) (rayToward A r)) (fun _ ↦ 0) p

-- The body of `vertexAngle` is not `@[expose]`d, so downstream modules rewrite with this.
/-- The angle at a vertex of `ℍ`, unfolded. -/
theorem vertexAngle_inl (A : ℍ) (q r : ℍ ⊕ OnePoint ℝ) :
    vertexAngle (.inl A) q r = geodesicAngle (rayToward A q) (rayToward A r) := by
  rfl

/-- The angle at an ideal vertex is `0`. -/
@[simp]
theorem vertexAngle_inr (ξ : OnePoint ℝ) (q r : ℍ ⊕ OnePoint ℝ) :
    vertexAngle (.inr ξ) q r = 0 := by
  rfl

/-- On three points of `ℍ`, the angle at a vertex is the interior angle. -/
@[simp]
theorem vertexAngle_inl_inl_inl (A B C : ℍ) :
    vertexAngle (.inl A) (.inl B) (.inl C) = interiorAngle A B C := by
  rw [vertexAngle_inl, rayToward_inl, rayToward_inl, interiorAngle_def]

/-- The angle at a vertex does not depend on the order of the other two points. -/
theorem vertexAngle_comm (p q r : ℍ ⊕ OnePoint ℝ) : vertexAngle p r q = vertexAngle p q r := by
  rcases p with A | ξ
  · rw [vertexAngle_inl, vertexAngle_inl, geodesicAngle_comm]
  · rw [vertexAngle_inr, vertexAngle_inr]

/-- Angles at a vertex are nonnegative. -/
theorem vertexAngle_nonneg (p q r : ℍ ⊕ OnePoint ℝ) : 0 ≤ vertexAngle p q r := by
  rcases p with A | ξ
  · exact vertexAngle_inl A q r ▸ geodesicAngle_nonneg _ _
  · exact (vertexAngle_inr ξ q r).ge

/-- Angles at a vertex are at most `π`. -/
theorem vertexAngle_le_pi (p q r : ℍ ⊕ OnePoint ℝ) : vertexAngle p q r ≤ π := by
  rcases p with A | ξ
  · exact vertexAngle_inl A q r ▸ geodesicAngle_le_pi _ _
  · exact (vertexAngle_inr ξ q r).trans_le Real.pi_pos.le

/-- The angle at a vertex of `ℍ` towards two points of `ℍ ∪ ∂ℍ` is the interior angle towards
the points of the two rays at parameter `1`. -/
theorem vertexAngle_inl_eq_interiorAngle (A : ℍ) (q r : ℍ ⊕ OnePoint ℝ) :
    vertexAngle (.inl A) q r =
      interiorAngle A (geodesicLine (rayToward A q) 1) (geodesicLine (rayToward A r) 1) := by
  rw [vertexAngle_inl, interiorAngle_def, ← rayToward_eq_geodesicBetween,
    ← rayToward_eq_geodesicBetween]

/-- Angles at a vertex are invariant under the action. -/
theorem vertexAngle_smul (h : PSL(2, ℝ)) {p q r : ℍ ⊕ OnePoint ℝ} (hpq : p ≠ q) (hpr : p ≠ r) :
    vertexAngle (h • p) (h • q) (h • r) = vertexAngle p q r := by
  rcases p with A | ξ
  · rw [Sum.smul_inl, vertexAngle_inl, vertexAngle_inl, rayToward_smul h hpq,
      rayToward_smul h hpr, geodesicAngle_mul _ _ _ (by
        rw [geodesicLine_rayToward_zero, geodesicLine_rayToward_zero])]
  · rw [Sum.smul_inr, vertexAngle_inr, vertexAngle_inr]

/-! ### Angles with the upward vertical -/

/-- A point at squared distance `ρ ^ 2` from `m`, with `0 < ρ`, is at distance `ρ`. -/
private theorem norm_sub_eq_of_normSq {z : ℂ} {m ρ : ℝ} (hρ : 0 < ρ)
    (h : Complex.normSq (z - m) = ρ ^ 2) : ‖z - m‖ = ρ := by
  rwa [Complex.normSq_eq_norm_sq, pow_left_inj₀ (norm_nonneg _) hρ.le two_ne_zero] at h

/-- The angle between `I` and `I * w`, for `w` in the upper half-plane, is the argument of `w`. -/
private theorem angle_I_I_mul {w : ℂ} (hw : 0 < w.im) :
    InnerProductGeometry.angle Complex.I (Complex.I * w) = Real.arccos (w.re / ‖w‖) := by
  have h := Complex.angle_mul_left Complex.I_ne_zero 1 w
  rw [mul_one] at h
  rw [h, Complex.angle_one_left (fun h0 ↦ by simp [h0] at hw), Complex.arg_of_im_pos hw,
    abs_of_nonneg (Real.arccos_nonneg _)]

/-- An ideal point `x` of the circle of centre `m` and radius `ρ`, to the left of a point `w` of
the closed upper half-plane on that circle, is its left endpoint `m - ρ`. -/
private theorem eq_coe_sub_of_normSq_eq_of_lt {x m ρ : ℝ} {w : ℂ} (hρ : 0 < ρ)
    (hx : Complex.normSq ((x : ℂ) - m) = ρ ^ 2) (hw : Complex.normSq (w - m) = ρ ^ 2)
    (hxw : (x : ℂ).re < w.re) : x = m - ρ := by
  rw [← Complex.ofReal_sub, Complex.normSq_ofReal] at hx
  rw [Complex.normSq_apply] at hw
  simp only [Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im,
    sub_zero] at hw hxw
  have hlt : x - m < ρ := by nlinarith [mul_self_nonneg w.im]
  have h : (x - m + ρ) * (x - m - ρ) = 0 := by linear_combination hx
  linarith [(mul_eq_zero.1 h).resolve_right (sub_ne_zero.2 hlt.ne)]

/-- An ideal point `x` of the circle of centre `m` and radius `ρ`, to the right of a point `w` of
the closed upper half-plane on that circle, is its right endpoint `m + ρ`. -/
private theorem eq_coe_add_of_normSq_eq_of_lt {x m ρ : ℝ} {w : ℂ} (hρ : 0 < ρ)
    (hx : Complex.normSq ((x : ℂ) - m) = ρ ^ 2) (hw : Complex.normSq (w - m) = ρ ^ 2)
    (hwx : w.re < (x : ℂ).re) : x = m + ρ := by
  rw [← Complex.ofReal_sub, Complex.normSq_ofReal] at hx
  rw [Complex.normSq_apply] at hw
  simp only [Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im,
    sub_zero] at hw hwx
  have hlt : -ρ < x - m := by nlinarith [mul_self_nonneg w.im]
  have h : (x - m + ρ) * (x - m - ρ) = 0 := by linear_combination hx
  linarith [(mul_eq_zero.1 h).resolve_left (by linarith)]

/-- **The radical line of two circles.** Let `a` lie on two circles centred on the real axis,
of centres `m₁`, `m₂` and radii `ρ₁`, `ρ₂`, and let `w` lie on the first circle, to the left of
`a` and strictly outside the second. Then every point `z` of the first circle to the left of `a` is
strictly outside the second: on the first circle, `|z - m₂|² - ρ₂²` is an affine function of
`Re z`, vanishing at `a`. -/
private theorem lt_normSq_sub_of_normSq_eq {a w z : ℂ} {m₁ ρ₁ m₂ ρ₂ : ℝ}
    (ha₁ : Complex.normSq (a - m₁) = ρ₁ ^ 2) (ha₂ : Complex.normSq (a - m₂) = ρ₂ ^ 2)
    (hw₁ : Complex.normSq (w - m₁) = ρ₁ ^ 2) (hw₂ : ρ₂ ^ 2 < Complex.normSq (w - m₂))
    (hz₁ : Complex.normSq (z - m₁) = ρ₁ ^ 2) (hwa : w.re < a.re) (hza : z.re < a.re) :
    ρ₂ ^ 2 < Complex.normSq (z - m₂) := by
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.ofReal_re,
    Complex.ofReal_im, sub_zero] at ha₁ ha₂ hw₁ hw₂ hz₁ ⊢
  have hz : (z.re - m₂) * (z.re - m₂) + z.im * z.im - ρ₂ ^ 2 = 2 * (m₁ - m₂) * (z.re - a.re) := by
    linear_combination hz₁ - ha₁ + ha₂
  have hw : (w.re - m₂) * (w.re - m₂) + w.im * w.im - ρ₂ ^ 2 = 2 * (m₁ - m₂) * (w.re - a.re) := by
    linear_combination hw₁ - ha₁ + ha₂
  have hm : 2 * (m₁ - m₂) < 0 :=
    neg_of_mul_pos_left (hw ▸ sub_pos.2 hw₂) (sub_neg.2 hwa).le
  linarith [mul_pos_of_neg_of_neg hm (sub_neg.2 hza)]

/-- On a circle of centre `m` through `A ∈ ℍ` and a point `q` (other than `∞`) of different real
part, the point of the ray from `A` towards `q` at parameter `1` is again on the circle, and lies
on the same side of `A` as `q`. -/
private theorem normSq_geodesicLine_rayToward_one_sub {A : ℍ} {q : ℍ ⊕ OnePoint ℝ} {m r : ℝ}
    (hq : q ≠ .inr ∞) (hA : Complex.normSq ((A : ℂ) - m) = r)
    (hqm : Complex.normSq (toComplex q - m) = r) (hre : A.re ≠ (toComplex q).re) :
    Complex.normSq ((geodesicLine (rayToward A q) 1 : ℂ) - m) = r ∧
      (A.re < (geodesicLine (rayToward A q) 1).re ∧ A.re < (toComplex q).re ∨
        (geodesicLine (rayToward A q) 1).re < A.re ∧ (toComplex q).re < A.re) := by
  have hAq : (.inl A : ℍ ⊕ OnePoint ℝ) ≠ q := fun h ↦ hre (by rw [← h, toComplex_inl, coe_re])
  have hg := isGeodesicFromTo_rayToward hAq
  obtain ⟨Q, hQ⟩ : ∃ Q, geodesicLine (rayToward A q) 1 = Q := ⟨_, rfl⟩
  have hgQ : IsGeodesicFromTo (rayToward A q) (.inl A) (.inl Q) :=
    isGeodesicFromTo_inl_inl.2 ⟨0, 1, one_pos, geodesicLine_rayToward_zero A q, hQ⟩
  have hp : (.inl A : ℍ ⊕ OnePoint ℝ) ≠ .inr ∞ := Sum.inl_ne_inr
  have hre' : (toComplex (.inl A)).re ≠ (toComplex q).re := by rwa [toComplex_inl, coe_re]
  have hQm : Complex.normSq ((Q : ℂ) - m) = r := by
    rw [← hQ]
    exact hg.normSq_geodesicLine_sub hp hq (by rwa [toComplex_inl]) hqm hre' 1
  have hlt := hg.re_toComplex_lt_iff hgQ hp hq hre'
  rw [toComplex_inl, toComplex_inl, coe_re, coe_re] at hlt
  -- `Q ≠ A` are two points of `ℍ` on the same circle, so they have different real parts
  have hAQ : A.re ≠ Q.re := fun h ↦ by
    have him : A.im = Q.im := by
      have h2 : A.im ^ 2 = Q.im ^ 2 := by
        simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.ofReal_re,
          Complex.ofReal_im, sub_zero, coe_re, coe_im] at hA hQm
        rw [h] at hA
        linear_combination hA - hQm
      exact (pow_left_inj₀ A.im_pos.le Q.im_pos.le two_ne_zero).1 h2
    exact zero_ne_one (geodesicLine_injective _ ((geodesicLine_rayToward_zero A q).trans
      ((UpperHalfPlane.ext (Complex.ext h him)).trans hQ.symm)))
  rw [hQ]
  refine ⟨hQm, ?_⟩
  rcases hAQ.lt_or_gt with h | h
  · exact .inl ⟨h, hlt.1 h⟩
  · exact .inr ⟨h, (lt_or_gt_of_ne hre).resolve_left fun h' ↦ (hlt.2 h').not_gt h⟩

/-- At a point `A` of a semicircle of centre `m`, the ray towards another point `q` of it (or of
its ideal endpoints) has velocity tangent to the semicircle, clockwise exactly when `q` is to the
right of `A`; so its angle with the upward vertical is the angle between `I` and that tangent. -/
private theorem exists_vertexAngle_inl_infty_eq {A : ℍ} {q : ℍ ⊕ OnePoint ℝ} {m ρ : ℝ}
    (hq : q ≠ .inr ∞) (hA : Complex.normSq ((A : ℂ) - m) = ρ ^ 2)
    (hqm : Complex.normSq (toComplex q - m) = ρ ^ 2) (hre : A.re ≠ (toComplex q).re) :
    ∃ μ : ℝ, μ * ((toComplex q).re - A.re) < 0 ∧ vertexAngle (.inl A) (.inr ∞) q =
      InnerProductGeometry.angle Complex.I (μ * (Complex.I * ((A : ℂ) - m))) := by
  obtain ⟨hQm, hside⟩ := normSq_geodesicLine_rayToward_one_sub hq hA hqm hre
  obtain ⟨Q, hQ⟩ : ∃ Q, geodesicLine (rayToward A q) 1 = Q := ⟨_, rfl⟩
  rw [hQ] at hQm hside
  have hAQ : A.re ≠ Q.re := by rcases hside with h | h <;> [exact h.1.ne; exact h.1.ne']
  obtain ⟨μ, hμ, hv⟩ := exists_velocity_geodesicBetween_zero_eq hAQ
  rw [circleCenter_eq_of_normSq_eq hAQ (hA.trans hQm.symm)] at hv
  refine ⟨μ, ?_, ?_⟩
  · rcases hside with h | h
    · exact mul_neg_of_neg_of_pos (neg_of_mul_neg_left hμ (sub_pos.2 h.1).le) (sub_pos.2 h.2)
    · exact mul_neg_of_pos_of_neg (pos_of_mul_neg_left hμ (sub_neg.2 h.1).le) (sub_neg.2 h.2)
  · rw [vertexAngle_inl, rayToward_inr_infty, rayToward_eq_geodesicBetween A q, hQ,
      geodesicAngle_def, hv, velocity_def, smulDeriv_toPoint, Real.exp_zero, Complex.ofReal_one,
      mul_one, ← Complex.real_smul, InnerProductGeometry.angle_smul_left_of_pos _ _ A.im_pos]

/-- **The angle at the left vertex of a triangle with an ideal vertex at `∞`.** If `p` and `q`
lie on the semicircle of centre `m` and radius `ρ` (or are among its ideal endpoints), with `p` to
the left of `q`, the angle at `p` between the upward vertical and the direction to `q` is
`π - arccos ((Re p - m) / ρ)`; it is `0` when `p` is the ideal endpoint `m - ρ`. -/
theorem vertexAngle_infty_of_re_lt {p q : ℍ ⊕ OnePoint ℝ} {m ρ : ℝ} (hρ : 0 < ρ)
    (hp : p ≠ .inr ∞) (hq : q ≠ .inr ∞) (hpm : Complex.normSq (toComplex p - m) = ρ ^ 2)
    (hqm : Complex.normSq (toComplex q - m) = ρ ^ 2) (hpq : (toComplex p).re < (toComplex q).re) :
    vertexAngle p (.inr ∞) q = π - Real.arccos (((toComplex p).re - m) / ρ) := by
  rcases p with A | ξ
  · rw [toComplex_inl] at hpm hpq ⊢
    rw [coe_re] at hpq ⊢
    obtain ⟨μ, hμ, h⟩ := exists_vertexAngle_inl_infty_eq hq hpm hqm hpq.ne
    have hμ' : 0 < -μ := neg_pos.2 (neg_of_mul_neg_left hμ (sub_pos.2 hpq).le)
    rw [h, ← neg_neg ((μ : ℂ) * _), ← neg_mul, ← Complex.ofReal_neg, ← Complex.real_smul,
      InnerProductGeometry.angle_neg_right, InnerProductGeometry.angle_smul_right_of_pos _ _ hμ',
      angle_I_I_mul (by simpa using A.im_pos), norm_sub_eq_of_normSq hρ hpm]
    simp
  · -- an ideal left vertex is the left endpoint `m - ρ` of the semicircle
    obtain ⟨x, rfl⟩ := OnePoint.ne_infty_iff_exists.1 fun h ↦ hp (congrArg _ h)
    rw [toComplex_inr_coe] at hpm hpq ⊢
    rw [Complex.ofReal_re, vertexAngle_inr, eq_comm, sub_eq_zero,
      eq_coe_sub_of_normSq_eq_of_lt hρ hpm hqm hpq, sub_sub_cancel_left, neg_div,
      div_self hρ.ne', Real.arccos_neg_one]

/-- **The angle at the right vertex of a triangle with an ideal vertex at `∞`.** If `p` and `q`
lie on the semicircle of centre `m` and radius `ρ` (or are among its ideal endpoints), with `p` to
the left of `q`, the angle at `q` between the direction to `p` and the upward vertical is
`arccos ((Re q - m) / ρ)`; it is `0` when `q` is the ideal endpoint `m + ρ`. -/
theorem vertexAngle_infty_of_lt_re {p q : ℍ ⊕ OnePoint ℝ} {m ρ : ℝ} (hρ : 0 < ρ)
    (hp : p ≠ .inr ∞) (hq : q ≠ .inr ∞) (hpm : Complex.normSq (toComplex p - m) = ρ ^ 2)
    (hqm : Complex.normSq (toComplex q - m) = ρ ^ 2) (hpq : (toComplex p).re < (toComplex q).re) :
    vertexAngle q p (.inr ∞) = Real.arccos (((toComplex q).re - m) / ρ) := by
  rw [← vertexAngle_comm]
  rcases q with B | ξ
  · rw [toComplex_inl] at hqm hpq ⊢
    rw [coe_re] at hpq ⊢
    obtain ⟨μ, hμ, h⟩ := exists_vertexAngle_inl_infty_eq hp hqm hpm hpq.ne'
    rw [h, ← Complex.real_smul, InnerProductGeometry.angle_smul_right_of_pos _ _
        (pos_of_mul_neg_left hμ (sub_neg.2 hpq).le),
      angle_I_I_mul (by simpa using B.im_pos), norm_sub_eq_of_normSq hρ hqm]
    simp
  · -- an ideal right vertex is the right endpoint `m + ρ` of the semicircle
    obtain ⟨x, rfl⟩ := OnePoint.ne_infty_iff_exists.1 fun h ↦ hq (congrArg _ h)
    rw [toComplex_inr_coe] at hqm hpq ⊢
    rw [Complex.ofReal_re, vertexAngle_inr, eq_coe_add_of_normSq_eq_of_lt hρ hqm hpm hpq,
      add_sub_cancel_left, div_self hρ.ne', Real.arccos_one]

/-- **An angle split by the upward vertical.** Let `A ∈ ℍ` lie on two semicircles, of centres
`m₁`, `m₂` and radii `ρ₁`, `ρ₂`; let `p` lie on the first, to the left of `A`, and `q` on the
second, to the right of `A` (each possibly an ideal endpoint), with `p` strictly outside the
second semicircle. Then the angle at `A` between the directions to `p` and `q` is the sum of the
angles they make with the upward vertical through `A`. -/
theorem vertexAngle_eq_add_of_mem_circles {A : ℍ} {p q : ℍ ⊕ OnePoint ℝ} {m₁ ρ₁ m₂ ρ₂ : ℝ}
    (hp : p ≠ .inr ∞) (hq : q ≠ .inr ∞)
    (hA₁ : Complex.normSq ((A : ℂ) - m₁) = ρ₁ ^ 2)
    (hp₁ : Complex.normSq (toComplex p - m₁) = ρ₁ ^ 2)
    (hA₂ : Complex.normSq ((A : ℂ) - m₂) = ρ₂ ^ 2)
    (hq₂ : Complex.normSq (toComplex q - m₂) = ρ₂ ^ 2)
    (hpA : (toComplex p).re < A.re) (hAq : A.re < (toComplex q).re)
    (hp₂ : ρ₂ ^ 2 < Complex.normSq (toComplex p - m₂)) :
    vertexAngle (.inl A) p q =
      vertexAngle (.inl A) p (.inr ∞) + vertexAngle (.inl A) (.inr ∞) q := by
  -- the angles at `A` are interior angles towards the points `B`, `C`, `D` at parameter `1` of
  -- the rays towards `q`, `∞` and `p`
  obtain ⟨hBm, hB⟩ := normSq_geodesicLine_rayToward_one_sub hq hA₂ hq₂ hAq.ne
  obtain ⟨hDm, hD⟩ := normSq_geodesicLine_rayToward_one_sub hp hA₁ hp₁ hpA.ne'
  rw [vertexAngle_inl_eq_interiorAngle, vertexAngle_inl_eq_interiorAngle,
    vertexAngle_inl_eq_interiorAngle, rayToward_inr_infty]
  generalize geodesicLine (rayToward A q) 1 = B at hBm hB ⊢
  generalize geodesicLine (rayToward A p) 1 = D at hDm hD ⊢
  have hgC := (rayToward_inr_infty A).symm.trans (rayToward_eq_geodesicBetween A (.inr ∞))
  rw [rayToward_inr_infty] at hgC
  have hCre := re_geodesicLine_toPoint A 1
  have hCim := im_geodesicLine_toPoint A 1
  generalize geodesicLine (toPoint A) 1 = C at hgC hCre hCim ⊢
  have hAB : A.re < B.re := (hB.resolve_right fun h ↦ h.2.not_gt hAq).1
  have hDA : D.re < A.re := (hD.resolve_left fun h ↦ h.2.not_gt hpA).1
  rw [interiorAngle_comm A B D, interiorAngle_comm A C D, interiorAngle_comm A B C, add_comm]
  -- the left half-plane of the ray towards `q` is the outside of the second circle
  have hleft (z : ℍ) (hz : ρ₂ ^ 2 < Complex.normSq ((z : ℂ) - m₂)) :
      z ∈ leftHalfPlane (geodesicBetween A B) := by
    rw [mem_leftHalfPlane_geodesicBetween_iff_of_re_ne hAB.ne,
      circleCenter_eq_of_normSq_eq hAB.ne (hA₂.trans hBm.symm), hA₂]
    exact mul_neg_of_neg_of_pos (sub_neg.2 hAB) (sub_pos.2 hz)
  refine interiorAngle_add (hleft C ?_) (hleft D ?_) ?_
  · -- `C` lies straight above `A`
    have h₁ : A.im < A.im * Real.exp 1 :=
      lt_mul_of_one_lt_right A.im_pos (Real.one_lt_exp_iff.2 one_pos)
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.ofReal_re,
      Complex.ofReal_im, sub_zero, coe_re, coe_im] at hA₂ ⊢
    rw [hCre, hCim, ← hA₂]
    linarith [mul_lt_mul'' h₁ h₁ A.im_pos.le A.im_pos.le]
  · -- `D` is on the first circle, to the left of `A`, like `p`
    exact lt_normSq_sub_of_normSq_eq hA₁ hA₂ hp₁ hp₂ hDm hpA (by rwa [coe_re])
  · rw [← hgC, mem_leftHalfPlane_iff, re_toPoint_inv_smul]
    exact div_neg_of_neg_of_pos (sub_neg.2 hDA) A.im_pos

end UpperHalfPlane
