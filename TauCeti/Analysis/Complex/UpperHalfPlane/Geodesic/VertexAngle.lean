/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.UpperHalfPlane.Geodesic.InteriorAngle
public import TauCeti.Analysis.Complex.UpperHalfPlane.Geodesic.Ray
import TauCeti.Analysis.Complex.Angle
import TauCeti.Analysis.Complex.NormSq
import TauCeti.Analysis.Complex.UpperHalfPlane.Geodesic.Orientation
import TauCeti.Analysis.Complex.UpperHalfPlane.Geodesic.Semicircle

/-!
# Angles at a vertex of `ℍ ∪ ∂ℍ`

The angle at a vertex `p` of `ℍ ∪ ∂ℍ` between the directions to `q` and `r`
(`TauCeti.UpperHalfPlane.vertexAngle p q r`) is the angle between the rays
`UpperHalfPlane.rayToward` towards `q` and `r` when `p ∈ ℍ`, and `0` at an ideal vertex
(Walkden §7.1: geodesics meet `∂ℍ` at right angles). The directional reading needs `q ≠ p` and
`r ≠ p` for `p ∈ ℍ`: a ray towards `p` itself is an arbitrary geodesic line through `p`, so the
value is then unspecified. On three points of `ℍ` it is `UpperHalfPlane.interiorAngle`
(`TauCeti.UpperHalfPlane.vertexAngle_inl_inl_inl`).

When the vertex is a point `w ∈ ℍ` of the semicircle of centre `m` and radius `ρ`, the angle
between the upward vertical through `w` and the semicircle is an arccosine of `(Re w - m) / ρ`;
when the vertex is one of the two ideal endpoints of the semicircle the angle is `0`. At a vertex
where two semicircles meet with the upward vertical inside the angle, the angle is the sum of the
angles to the vertical. These are the angles of a
hyperbolic triangle with an ideal vertex at `∞`, in the normal form of Walkden's and Katok's
proofs of the Gauss–Bonnet formula.

## Main declarations

* `TauCeti.UpperHalfPlane.vertexAngle p q r`: the angle at a vertex of `ℍ ∪ ∂ℍ`.
* `TauCeti.UpperHalfPlane.vertexAngle_comm`, `TauCeti.UpperHalfPlane.vertexAngle_self`,
  `TauCeti.UpperHalfPlane.vertexAngle_nonneg`, `TauCeti.UpperHalfPlane.vertexAngle_le_pi`,
  `TauCeti.UpperHalfPlane.vertexAngle_smul`: symmetry, vanishing, bounds and invariance.
* `TauCeti.UpperHalfPlane.vertexAngle_infty_of_re_lt`,
  `TauCeti.UpperHalfPlane.vertexAngle_infty_of_lt_re`: the angles at the two finite vertices of a
  triangle with an ideal vertex at `∞`.
* `TauCeti.UpperHalfPlane.vertexAngle_eq_add_of_mem_circles`: an angle split by the upward
  vertical.

## Source

Walkden, *Hyperbolic geometry* (MATH32051 lecture notes, Manchester 2019), §7.1 (the angle at an
ideal vertex is zero) and the proof of Theorem 7.2.1 (the angles of a triangle with a vertex at
`∞`, with the other two vertices on a semicircle, read off as `π - α` and `β` at the endpoints of
the radius vectors); Katok, *Fuchsian groups, geodesic flows…*, Clay Math. Proc. 10 (2010), §5,
proof of Theorem 5.4 (Figure 5.2: the angles at the two finite vertices are the angles between the
radius vectors and the real axis, "as angles with mutually perpendicular sides"), and §13, proof
of Siegel's theorem (the angle between consecutive sides is the sum `ωₖ = βₖ + γₖ₊₁` of the
angles they make with the vertical through their common vertex).
-/

public section

noncomputable section

open UpperHalfPlane TauCeti.UpperHalfPlane
open scoped MatrixGroups Pointwise OnePoint Real

namespace TauCeti.UpperHalfPlane

/-! ### The angle at a vertex of `ℍ ∪ ∂ℍ` -/

/-- The angle at the vertex `p` of `ℍ ∪ ∂ℍ` between the directions to `q` and `r`: the angle
between the rays towards `q` and `r` when `p ∈ ℍ`, and `0` when `p` is an ideal point. For
`p ∈ ℍ` it is an angle between directions only when `q ≠ p` and `r ≠ p`; otherwise the ray towards
`p` is an arbitrary geodesic line through `p` and the value is unspecified. -/
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

/-- The angle at a vertex between a direction and itself is `0`. -/
@[simp]
theorem vertexAngle_self (p q : ℍ ⊕ OnePoint ℝ) : vertexAngle p q q = 0 := by
  rcases p with A | ξ
  · rw [vertexAngle_inl, geodesicAngle_self]
  · rw [vertexAngle_inr]

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

/-- A ray towards a point strictly in the other ray's left half-plane is not on its line. -/
private theorem rayToward_one_notMem_geodesicBetween_of_mem_extLeftHalfPlane
    {A : ℍ} {q r : ℍ ⊕ OnePoint ℝ} (hr : r ∈ extLeftHalfPlane (rayToward A q)) :
    geodesicLine (rayToward A r) 1 ∉
      Set.range (geodesicLine (geodesicBetween A (geodesicLine (rayToward A q) 1))) := by
  have hAr : (.inl A : ℍ ⊕ OnePoint ℝ) ≠ r := by
    intro h
    rw [← h, inl_mem_extLeftHalfPlane_iff] at hr
    exact notMem_range_geodesicLine_of_mem_leftHalfPlane hr
      ⟨0, geodesicLine_rayToward_zero A q⟩
  rw [← rayToward_eq_geodesicBetween]
  rintro ⟨t, ht⟩
  have ht₀ : t ≠ 0 := by
    intro h
    rw [h, geodesicLine_rayToward_zero] at ht
    exact zero_ne_one (geodesicLine_injective _
      ((geodesicLine_rayToward_zero A r).trans ht))
  have hline := rayToward_eq_geodesicBetween A r
  rcases ht₀.lt_or_gt with hneg | hpos
  · have hrev : rayToward A r = rayToward A q * pslS := by
      calc
        rayToward A r = geodesicBetween (geodesicLine (rayToward A q * pslS) 0)
            (geodesicLine (rayToward A q * pslS) (-t)) := by
          simpa only [geodesicLine_mul_pslS, neg_zero, neg_neg,
            geodesicLine_rayToward_zero, ht] using hline
        _ = rayToward A q * pslS := by
          rw [geodesicBetween_geodesicLine_of_lt _ (neg_pos.2 hneg)]
          simp
    have hg := isGeodesicFromTo_mul_pslS_iff.1
      (hrev ▸ isGeodesicFromTo_rayToward hAr)
    exact hg.left_notMem_extLeftHalfPlane hr
  · have heq : rayToward A r = rayToward A q := by
      calc
        rayToward A r = geodesicBetween (geodesicLine (rayToward A q) 0)
            (geodesicLine (rayToward A q) t) := by
          simpa only [geodesicLine_rayToward_zero, ht] using hline
        _ = rayToward A q := by
          rw [geodesicBetween_geodesicLine_of_lt _ hpos]
          simp
    exact (heq ▸ isGeodesicFromTo_rayToward hAr).right_notMem_extLeftHalfPlane hr

/-- The angle at a finite vertex is positive when the second target lies strictly to the left
of the ray towards the first target. -/
theorem vertexAngle_pos_of_mem_extLeftHalfPlane {A : ℍ} {q r : ℍ ⊕ OnePoint ℝ}
    (hr : r ∈ extLeftHalfPlane (rayToward A q)) : 0 < vertexAngle (.inl A) q r := by
  rw [vertexAngle_inl_eq_interiorAngle]
  exact interiorAngle_pos (rayToward_one_notMem_geodesicBetween_of_mem_extLeftHalfPlane hr)

/-- The angle at a finite vertex is less than `π` when the second target lies strictly to the
left of the ray towards the first target. -/
theorem vertexAngle_lt_pi_of_mem_extLeftHalfPlane {A : ℍ} {q r : ℍ ⊕ OnePoint ℝ}
    (hr : r ∈ extLeftHalfPlane (rayToward A q)) : vertexAngle (.inl A) q r < π := by
  rw [vertexAngle_inl_eq_interiorAngle]
  exact interiorAngle_lt_pi (rayToward_one_notMem_geodesicBetween_of_mem_extLeftHalfPlane hr)

/-- Angles at a vertex are invariant under the action. -/
theorem vertexAngle_smul (h : PSL(2, ℝ)) {p q r : ℍ ⊕ OnePoint ℝ} (hpq : p ≠ q) (hpr : p ≠ r) :
    vertexAngle (h • p) (h • q) (h • r) = vertexAngle p q r := by
  rcases p with A | ξ
  · rw [Sum.smul_inl, vertexAngle_inl, vertexAngle_inl, rayToward_smul h hpq,
      rayToward_smul h hpr, geodesicAngle_mul _ _ _ (by
        rw [geodesicLine_rayToward_zero, geodesicLine_rayToward_zero])]
  · rw [Sum.smul_inr, vertexAngle_inr, vertexAngle_inr]

/-! ### Angles with the upward vertical -/

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
      Complex.angle_I_I_mul, Complex.norm_sub_eq_of_normSq_sub_eq hρ.le hpm]
    simp
  · -- an ideal left vertex is the left endpoint `m - ρ` of the semicircle
    obtain ⟨x, rfl⟩ := OnePoint.ne_infty_iff_exists.1 fun h ↦ hp (congrArg _ h)
    rw [toComplex_inr_coe] at hpm hpq ⊢
    rw [Complex.ofReal_re, vertexAngle_inr, eq_comm, sub_eq_zero,
      Complex.eq_sub_of_normSq_eq_of_lt_re hρ.le hpm hqm hpq, sub_sub_cancel_left, neg_div,
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
      Complex.angle_I_I_mul, Complex.norm_sub_eq_of_normSq_sub_eq hρ.le hqm]
    simp
  · -- an ideal right vertex is the right endpoint `m + ρ` of the semicircle
    obtain ⟨x, rfl⟩ := OnePoint.ne_infty_iff_exists.1 fun h ↦ hq (congrArg _ h)
    rw [toComplex_inr_coe] at hqm hpq ⊢
    rw [Complex.ofReal_re, vertexAngle_inr, Complex.eq_add_of_normSq_eq_of_re_lt hρ.le hqm hpm hpq,
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
    exact Complex.lt_normSq_sub_of_normSq_eq hA₁ hA₂ hp₁ hp₂ hDm hpA (by rwa [coe_re])
  · rw [← hgC, mem_leftHalfPlane_iff, re_toPoint_inv_smul]
    exact div_neg_of_neg_of_pos (sub_neg.2 hDA) A.im_pos

end TauCeti.UpperHalfPlane
