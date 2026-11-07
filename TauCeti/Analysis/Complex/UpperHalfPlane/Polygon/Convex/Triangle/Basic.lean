/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.UpperHalfPlane.Polygon.Convex
import TauCeti.Analysis.Complex.UpperHalfPlane.Polygon.Convex.GaussBonnet
import TauCeti.Analysis.Complex.UpperHalfPlane.Triangle
import TauCeti.Analysis.SpecialFunctions.Trigonometric.Bounds
import TauCeti.Topology.Circle.Metric

/-!
# Hyperbolic triangles with prescribed angles

For real numbers `α, β, γ ≥ 0` with `α + β + γ < π` there is a convex hyperbolic triangle, with
vertices in `ℍ ∪ ∂ℍ`, whose interior angles are `α`, `β` and `γ`; by
`ConvexPolygon.interiorAngle_eq_zero_iff`, a vertex is ideal exactly when its angle is `0`.
Conversely, by Gauss–Bonnet, the angles of every convex hyperbolic triangle are of this form
(`ConvexPolygon.exists_interiorAngle_eq_iff`).

The triangle is written down explicitly in one of two normal forms.

* If one angle vanishes, the corresponding vertex is `∞`, and the other two vertices lie on the
  unit semicircle at the points of argument `π - α` and `β` (at the ideal points `-1`, `1` when
  these angles vanish). Their angles are computed by `vertexAngle_infty_of_re_lt` and
  `vertexAngle_infty_of_lt_re`.
* If all three angles are positive and `β ≤ π / 2`, the vertices are `I`, a point `C` to the
  right of the imaginary axis, and `i e^d` with `cosh d = (cos α cos β + cos γ) / (sin α sin β)`,
  which exceeds `1` exactly because `α + β + γ < π`: this is the hyperbolic law of cosines for
  the side opposite `C`. The sides through `C` lie on the semicircles of centres `cot α` and
  `-e^d cot β` and radii `1 / sin α` and `e^d / sin β`, whose radius vectors at `C` make the angle
  `γ`. The angles are computed by `UpperHalfPlane.interiorAngle_of_normal_form` and its
  companions. At most one angle of a triangle exceeds `π / 2`, so a cyclic relabelling puts any
  triangle without ideal vertices in this form.

## Main results

* `ConvexPolygon.triangleInfty`: the convex triangle with vertices `p`, `q` and `∞`, for
  `Re p < Re q`.
* `ConvexPolygon.exists_interiorAngle_eq_iff`: the angle triples of convex hyperbolic triangles
  are exactly the nonnegative triples with sum less than `π`.

## References

* Alan Beardon, *The Geometry of Discrete Groups*, Graduate Texts in Mathematics 91, Springer,
  1983, Chapter 7 (the trigonometry of hyperbolic triangles, and the existence of a triangle with
  any prescribed angles of sum less than `π`).
* Svetlana Katok, *Fuchsian Groups*, Chicago Lectures in Mathematics, University of Chicago
  Press, 1992, Chapter 1 (hyperbolic trigonometry, including the cosine rule for angles).
-/

public section

noncomputable section

open UpperHalfPlane
open scoped MatrixGroups OnePoint Real

namespace TauCeti.UpperHalfPlane

/-! ### A triangle with an ideal vertex at `∞` -/

/-- The point of the upper unit semicircle of argument `θ ∈ [0, π]`, as a point of `ℍ ∪ ∂ℍ`:
it lies in `ℍ` for `0 < θ < π`, and is the ideal point `cos θ = ±1` otherwise. -/
private theorem exists_re_toComplex_eq_cos {θ : ℝ} (h₀ : 0 ≤ θ) (hπ : θ ≤ π) :
    ∃ p : ℍ ⊕ OnePoint ℝ, p ≠ .inr ∞ ∧ (toComplex p).re = Real.cos θ ∧
      Complex.normSq (toComplex p - ((0 : ℝ) : ℂ)) = 1 ^ 2 := by
  have hθ := Real.sin_sq_add_cos_sq θ
  rcases (Real.sin_nonneg_of_nonneg_of_le_pi h₀ hπ).lt_or_eq with hs | hs
  · refine ⟨.inl (UpperHalfPlane.mk ⟨Real.cos θ, Real.sin θ⟩ hs), Sum.inl_ne_inr, ?_, ?_⟩
    · rw [toComplex_inl, UpperHalfPlane.coe_mk]
    · rw [toComplex_inl, UpperHalfPlane.coe_mk, Complex.ofReal_zero, sub_zero,
        Complex.normSq_mk]
      linear_combination hθ
  · refine ⟨.inr (Real.cos θ : OnePoint ℝ),
      fun h ↦ OnePoint.coe_ne_infty _ (Sum.inr_injective h), ?_, ?_⟩
    · rw [toComplex_inr_coe, Complex.ofReal_re]
    · rw [toComplex_inr_coe, Complex.ofReal_zero, sub_zero, Complex.normSq_ofReal]
      linear_combination hθ + Real.sin θ * hs

/-- The convex triangle with vertices `p`, `q` and the ideal vertex `∞`, listed counterclockwise,
for points `p, q ≠ ∞` of `ℍ ∪ ∂ℍ` with `Re p < Re q`. -/
def ConvexPolygon.triangleInfty {p q : ℍ ⊕ OnePoint ℝ} (hp : p ≠ .inr ∞) (hq : q ≠ .inr ∞)
    (hlt : (toComplex p).re < (toComplex q).re) : ConvexPolygon 3 where
  vertex := ![p, q, .inr ∞]
  three_le := le_rfl
  vertex_ne_vertex_add_one i := by
    have hpq : p ≠ q := fun h ↦ hlt.ne (by rw [h])
    fin_cases i
    exacts [hpq, hq, hp.symm]
  vertex_mem_extLeftHalfPlane i j hji hji' := by
    have hpq : p ≠ q := fun h ↦ hlt.ne (by rw [h])
    -- the vertices `p`, `q`, `∞` run counterclockwise: `∞` is above the semicircle from `p` to
    -- `q`, and each of `p`, `q` is on the inner side of the vertical through the other
    have h₀ : (∞ : OnePoint ℝ) ∈ boundaryLeftHalfPlane (geodesicFromTo p q) :=
      ((isGeodesicFromTo_geodesicFromTo hpq).infty_mem_boundaryLeftHalfPlane_iff_re_lt hp hq).2
        hlt
    have h₁ : p ∈ extLeftHalfPlane (geodesicFromTo q (.inr ∞)) := by
      refine (mem_extLeftHalfPlane_iff_sideForm_toComplex_neg hp).2 ?_
      rw [(isGeodesicFromTo_geodesicFromTo hq).sideForm_eq_of_inr_infty_right hq]
      linarith
    have h₂ : q ∈ extLeftHalfPlane (geodesicFromTo (.inr ∞) p) := by
      refine (mem_extLeftHalfPlane_iff_sideForm_toComplex_neg hq).2 ?_
      rw [(isGeodesicFromTo_geodesicFromTo hp.symm).sideForm_eq_of_inr_infty_left hp]
      linarith
    fin_cases i <;> fin_cases j <;> simp [h₀, h₁, h₂] at hji hji' ⊢

/-- The vertices of `ConvexPolygon.triangleInfty` are `p`, `q` and `∞`. -/
@[simp]
theorem ConvexPolygon.vertex_triangleInfty {p q : ℍ ⊕ OnePoint ℝ} (hp : p ≠ .inr ∞)
    (hq : q ≠ .inr ∞) (hlt : (toComplex p).re < (toComplex q).re) :
    (ConvexPolygon.triangleInfty hp hq hlt).vertex = ![p, q, .inr ∞] :=
  (rfl)

/-- For `α, β ≥ 0` with `α + β < π` there is a convex triangle with angles `α` and `β` at its
first two vertices and the ideal vertex `∞` third. -/
private theorem exists_convexPolygon_three_vertex_two_eq_infty {α β : ℝ} (hα : 0 ≤ α)
    (hβ : 0 ≤ β) (h : α + β < π) :
    ∃ P : ConvexPolygon 3, P.interiorAngle 0 = α ∧ P.interiorAngle 1 = β ∧
      P.interiorAngle 2 = 0 := by
  obtain ⟨p, hp, hpre, hpm⟩ := exists_re_toComplex_eq_cos (θ := π - α) (by linarith)
    (by linarith)
  obtain ⟨q, hq, hqre, hqm⟩ := exists_re_toComplex_eq_cos hβ (by linarith)
  have hlt : (toComplex p).re < (toComplex q).re := by
    rw [hpre, hqre]
    exact Real.cos_lt_cos_of_nonneg_of_le_pi hβ (by linarith) (by linarith)
  refine ⟨ConvexPolygon.triangleInfty hp hq hlt, ?_, ?_, ?_⟩
  · have hsub : (0 : Fin 3) - 1 = 2 := by decide
    rw [ConvexPolygon.interiorAngle_def, hsub, zero_add, ConvexPolygon.vertex_triangleInfty]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons,
      Matrix.head_cons]
    rw [vertexAngle_infty_of_re_lt one_pos hp hq hpm hqm hlt, hpre, sub_zero, div_one,
      Real.cos_pi_sub, Real.arccos_neg, Real.arccos_cos hα (by linarith)]
    ring
  · have hadd : (1 : Fin 3) + 1 = 2 := by decide
    rw [ConvexPolygon.interiorAngle_def, sub_self, hadd, ConvexPolygon.vertex_triangleInfty]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons,
      Matrix.head_cons]
    rw [vertexAngle_infty_of_lt_re one_pos hp hq hpm hqm hlt, hqre, sub_zero, div_one,
      Real.arccos_cos hβ (by linarith)]
  · exact ConvexPolygon.interiorAngle_eq_zero_of_vertex_eq_inr _ (ξ := ∞) rfl

/-! ### A triangle with three finite vertices -/

/-- The data of the two semicircles through the third vertex `C`: for `α > 0`, `β ∈ (0, π / 2]`
and `γ > 0` with `α + β + γ < π`, there are `t > 1`, centres `c₁ > c₂` and radii `ρ₁, ρ₂ > 0` with
`ρ₁² = c₁² + 1` (the semicircle through `I`) and `ρ₂² = c₂² + t²` (the one through `i t`), such
that the radius vectors at an intersection point make the angle `γ`
(`(c₁ - c₂)² = ρ₁² + ρ₂² - 2 ρ₁ ρ₂ cos γ`), with `c₁ / ρ₁ = cos α` and `c₂ / ρ₂ = -cos β`. -/
private theorem exists_circles_of_angles {α β γ : ℝ} (hα : 0 < α) (hβ : 0 < β)
    (hβ' : β ≤ π / 2) (hγ : 0 < γ) (h : α + β + γ < π) :
    ∃ t c₁ c₂ ρ₁ ρ₂ : ℝ, 1 < t ∧ 0 < ρ₁ ∧ 0 < ρ₂ ∧ ρ₁ ^ 2 = c₁ ^ 2 + 1 ∧ ρ₂ ^ 2 = c₂ ^ 2 + t ^ 2 ∧
      0 < c₁ - c₂ ∧ (c₁ - c₂) ^ 2 = ρ₁ ^ 2 + ρ₂ ^ 2 - 2 * ρ₁ * ρ₂ * Real.cos γ ∧
      c₁ / ρ₁ = Real.cos α ∧ c₂ / ρ₂ = -Real.cos β := by
  have hsα : 0 < Real.sin α := Real.sin_pos_of_pos_of_lt_pi hα (by linarith)
  have hsβ : 0 < Real.sin β := Real.sin_pos_of_pos_of_lt_pi hβ (by linarith)
  have hcβ : 0 ≤ Real.cos β := Real.cos_nonneg_of_mem_Icc ⟨by linarith, hβ'⟩
  have hα₂ := Real.sin_sq_add_cos_sq α
  have hβ₂ := Real.sin_sq_add_cos_sq β
  obtain ⟨K, t, hKs, ht₁, htK⟩ := exists_cosine_rule_parameter hα hβ hγ.le h
  refine ⟨t, Real.cos α / Real.sin α, -(t * Real.cos β / Real.sin β), (Real.sin α)⁻¹,
    t / Real.sin β, ht₁, inv_pos.2 hsα, div_pos (by linarith) hsβ, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · field_simp
    linear_combination -hα₂
  · field_simp
    linear_combination -hβ₂
  · have h₁ : (Real.cos α / Real.sin α - -(t * Real.cos β / Real.sin β)) *
        (Real.sin α * Real.sin β) =
        Real.sin (α + β) + (t - 1) * (Real.sin α * Real.cos β) := by
      rw [Real.sin_add]
      field_simp
      ring
    have h₂ : 0 < Real.sin (α + β) := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
    have h₃ : 0 ≤ (t - 1) * (Real.sin α * Real.cos β) :=
      mul_nonneg (by linarith) (by positivity)
    nlinarith [mul_pos hsα hsβ]
  · field_simp
    linear_combination (-(Real.sin α ^ 2 * Real.sin β ^ 2)) * htK + Real.sin β ^ 2 * hα₂ +
      t ^ 2 * Real.sin α ^ 2 * hβ₂ - 2 * t * Real.sin α * Real.sin β * hKs
  · field_simp
  · field_simp

/-- The third vertex `C` of the triangle in normal form: the point where the semicircles of
centres `c₁`, `c₂` and radii `ρ₁`, `ρ₂` meet at the angle `γ`. It lies to the right of the
imaginary axis, since `t > 1`. -/
private theorem exists_third_vertex {c₁ c₂ ρ₁ ρ₂ t γ : ℝ} (ht : 1 < t) (hρ₁ : 0 < ρ₁)
    (hρ₂ : 0 < ρ₂) (hγ : 0 < γ) (hγπ : γ < π) (hρc₁ : ρ₁ ^ 2 = c₁ ^ 2 + 1)
    (hρc₂ : ρ₂ ^ 2 = c₂ ^ 2 + t ^ 2) (hD : 0 < c₁ - c₂)
    (hkey : (c₁ - c₂) ^ 2 = ρ₁ ^ 2 + ρ₂ ^ 2 - 2 * ρ₁ * ρ₂ * Real.cos γ) :
    ∃ C : ℍ, 0 < C.re ∧ Complex.normSq ((C : ℂ) - c₁) = ρ₁ ^ 2 ∧
      Complex.normSq ((C : ℂ) - c₂) = ρ₂ ^ 2 ∧
      Real.arccos ((C.re - c₁) / ρ₁) - Real.arccos ((C.re - c₂) / ρ₂) = γ := by
  obtain ⟨x, y, hy, h₁, h₂, hγ'⟩ := exists_arccos_sub_arccos_eq hρ₁ hρ₂ hγ hγπ hD hkey
  refine ⟨UpperHalfPlane.mk ⟨x, y⟩ hy, ?_, ?_, ?_, hγ'⟩
  · have hx : 2 * x * (c₁ - c₂) = t ^ 2 - 1 := by linear_combination h₂ - h₁ - hρc₁ + hρc₂
    have hx' := (mul_pos_iff_of_pos_right hD).1 (hx ▸ sub_pos.2 (one_lt_pow₀ ht two_ne_zero))
    simpa using hx'
  · rw [UpperHalfPlane.coe_mk, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im]
    linear_combination h₁
  · rw [UpperHalfPlane.coe_mk, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im]
    linear_combination h₂

/-- For `α > 0`, `β ∈ (0, π / 2]` and `γ > 0` with `α + β + γ < π` there is a compact convex
triangle with angles `α`, `γ` and `β` at its three vertices. -/
private theorem exists_compactConvexPolygon_three {α β γ : ℝ} (hα : 0 < α)
    (hβ : 0 < β) (hβ' : β ≤ π / 2) (hγ : 0 < γ) (h : α + β + γ < π) :
    ∃ P : CompactConvexPolygon 3,
      P.interiorAngle 0 = α ∧ P.interiorAngle 1 = γ ∧ P.interiorAngle 2 = β := by
  obtain ⟨t, c₁, c₂, ρ₁, ρ₂, ht, hρ₁, hρ₂, hρc₁, hρc₂, hD, hkey, hr₁, hr₂⟩ :=
    exists_circles_of_angles hα hβ hβ' hγ h
  obtain ⟨C, hCre, hCc₁, hCc₂, hγ'⟩ :=
    exists_third_vertex ht hρ₁ hρ₂ hγ (by linarith) hρc₁ hρc₂ hD hkey
  have hd : 0 < Real.log t := Real.log_pos ht
  obtain ⟨hIc₁, hcc₁⟩ := circleCenter_eq_of_re_eq_zero (B := UpperHalfPlane.I) (s := 1)
    (by rw [UpperHalfPlane.coe_I]; apply Complex.ext <;> simp) hCre (by rw [hρc₁]; ring) hCc₁
  obtain ⟨hBc₂, hcc₂⟩ := circleCenter_eq_of_re_eq_zero (coe_geodesicLine_one_log (by linarith))
    hCre hρc₂ hCc₂
  obtain ⟨hv₀, hv₁, hv₂⟩ := leftHalfPlane_normal_form ht hCre
  refine ⟨⟨![UpperHalfPlane.I, C, geodesicLine 1 (Real.log t)], le_rfl, fun i j hji hji' ↦ ?_⟩,
    ?_, ?_, ?_⟩
  · -- the vertex opposite each edge is on its left; the other six pairs are excluded by `hji`
    -- and `hji'`
    fin_cases i <;> fin_cases j
    exacts [absurd rfl hji, absurd rfl hji', hv₀, hv₁, absurd rfl hji, absurd rfl hji',
      absurd rfl hji', hv₂, absurd rfl hji]
  · have hsub : (0 : Fin 3) - 1 = 2 := by decide
    rw [CompactConvexPolygon.interiorAngle_def, hsub, zero_add]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons,
      Matrix.head_cons]
    rw [interiorAngle_I_geodesicLine_one hd hCre, hcc₁, hIc₁, Real.sqrt_sq hρ₁.le,
      hr₁, Real.arccos_cos hα.le (by linarith)]
  · have hadd : (1 : Fin 3) + 1 = 2 := by decide
    rw [CompactConvexPolygon.interiorAngle_def, sub_self, hadd]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons,
      Matrix.head_cons]
    rw [interiorAngle_of_normal_form hd hCre, hcc₁, hcc₂, hIc₁, hBc₂, Real.sqrt_sq hρ₁.le,
      Real.sqrt_sq hρ₂.le]
    exact hγ'
  · have hsub : (2 : Fin 3) - 1 = 1 := by decide
    have hadd : (2 : Fin 3) + 1 = 0 := by decide
    rw [CompactConvexPolygon.interiorAngle_def, hsub, hadd]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons,
      Matrix.head_cons]
    rw [interiorAngle_geodesicLine_one_I hd hCre, hcc₂, hBc₂, Real.sqrt_sq hρ₂.le,
      hr₂, Real.arccos_neg, Real.arccos_cos hβ.le (by linarith)]
    ring

/-! ### Triangles with prescribed angles -/

namespace ConvexPolygon

/-- A triangle with the angles `α`, `β`, `γ` gives one with the angles `β`, `γ`, `α`. -/
private theorem exists_interiorAngle_eq_rotate {α β γ : ℝ}
    (h : ∃ P : ConvexPolygon 3,
      P.interiorAngle 0 = α ∧ P.interiorAngle 1 = β ∧ P.interiorAngle 2 = γ) :
    ∃ P : ConvexPolygon 3,
      P.interiorAngle 0 = β ∧ P.interiorAngle 1 = γ ∧ P.interiorAngle 2 = α := by
  obtain ⟨P, hα, hβ, hγ⟩ := h
  have h₁₂ : (1 : Fin 3) + 1 = 2 := by decide
  have h₂₀ : (2 : Fin 3) + 1 = 0 := by decide
  exact ⟨P.rotate 1, by rw [interiorAngle_rotate, zero_add, hβ],
    by rw [interiorAngle_rotate, h₁₂, hγ],
    by rw [interiorAngle_rotate, h₂₀, hα]⟩

/-- **Hyperbolic triangles with prescribed angles.** Three real numbers are the interior angles of
a convex hyperbolic triangle, with vertices in `ℍ ∪ ∂ℍ`, exactly when they are nonnegative with
sum less than `π`. By `ConvexPolygon.interiorAngle_eq_zero_iff`, the ideal vertices of such a
triangle are those with angle `0`. -/
theorem exists_interiorAngle_eq_iff {α β γ : ℝ} :
    (∃ P : ConvexPolygon 3,
      P.interiorAngle 0 = α ∧ P.interiorAngle 1 = β ∧ P.interiorAngle 2 = γ) ↔
      0 ≤ α ∧ 0 ≤ β ∧ 0 ≤ γ ∧ α + β + γ < π := by
  refine ⟨?_, fun ⟨hα, hβ, hγ, h⟩ ↦ ?_⟩
  · rintro ⟨P, rfl, rfl, rfl⟩
    have h := P.sum_interiorAngle_lt
    rw [Fin.sum_univ_three] at h
    norm_num at h
    exact ⟨P.interiorAngle_nonneg 0, P.interiorAngle_nonneg 1, P.interiorAngle_nonneg 2, h⟩
  -- a triangle with an ideal vertex, put at `∞` after a cyclic relabelling
  rcases hγ.eq_or_lt with rfl | hγ
  · exact exists_convexPolygon_three_vertex_two_eq_infty hα hβ (by linarith)
  rcases hα.eq_or_lt with rfl | hα
  · exact exists_interiorAngle_eq_rotate (exists_interiorAngle_eq_rotate
      (exists_convexPolygon_three_vertex_two_eq_infty hβ hγ.le (by linarith)))
  rcases hβ.eq_or_lt with rfl | hβ
  · exact exists_interiorAngle_eq_rotate
      (exists_convexPolygon_three_vertex_two_eq_infty hγ.le hα.le (by linarith))
  -- a compact triangle with an angle at most `π / 2` at its vertex `2`
  have hcompact {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hc' : c ≤ π / 2)
      (h : a + b + c < π) : ∃ P : ConvexPolygon 3,
        P.interiorAngle 0 = a ∧ P.interiorAngle 1 = b ∧ P.interiorAngle 2 = c := by
    obtain ⟨Q, h₀, h₁, h₂⟩ := exists_compactConvexPolygon_three ha hc hc' hb (by linarith)
    exact ⟨Q.toConvexPolygon, by rw [CompactConvexPolygon.interiorAngle_toConvexPolygon, h₀],
      by rw [CompactConvexPolygon.interiorAngle_toConvexPolygon, h₁],
      by rw [CompactConvexPolygon.interiorAngle_toConvexPolygon, h₂]⟩
  by_cases hγ' : γ ≤ π / 2
  · exact hcompact hα hβ hγ hγ' h
  -- otherwise `β < π / 2`, and a rotation puts `β` last
  exact exists_interiorAngle_eq_rotate
    (hcompact hγ hα hβ (by linarith [not_le.1 hγ']) (by linarith))

end ConvexPolygon

end TauCeti.UpperHalfPlane
