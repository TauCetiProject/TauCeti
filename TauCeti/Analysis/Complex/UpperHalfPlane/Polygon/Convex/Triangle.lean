/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Fuchsian.TriangleOrder
public import TauCeti.Analysis.Complex.UpperHalfPlane.Polygon.Convex
import TauCeti.Analysis.Complex.UpperHalfPlane.Polygon.Convex.GaussBonnet
import TauCeti.Analysis.Complex.UpperHalfPlane.Triangle

/-!
# Hyperbolic triangles with prescribed angles

For real numbers `α, β, γ ≥ 0` with `α + β + γ < π` there is a convex hyperbolic triangle, with
vertices in `ℍ ∪ ∂ℍ`, whose interior angles are `α`, `β` and `γ`; by
`ConvexPolygon.interiorAngle_eq_zero_iff`, a vertex is ideal exactly when its angle is `0`.
Conversely, by Gauss–Bonnet, the angles of every convex hyperbolic triangle are of this form
(`ConvexPolygon.exists_interiorAngle_eq_iff`). In particular a triple of elliptic orders and cusps
is hyperbolic exactly when it is realised by a triangle with angle `π / m` at each elliptic vertex
of order `m` and an ideal vertex at each cusp
(`TauCeti.TriangleOrder.isHyperbolic_iff_exists_interiorAngle_eq`). The reflections in the sides
of such a triangle generate the corresponding extended triangle group.

The triangle is written down explicitly in one of two normal forms.

* If one angle vanishes, the corresponding vertex is `∞`, and the other two vertices lie on the
  unit semicircle at the points of argument `π - α` and `β` (at the ideal points `-1`, `1` when
  these angles vanish). Their angles are computed by `vertexAngle_infty_of_re_lt` and
  `vertexAngle_infty_of_lt_re`.
* If all three angles are positive and `α, β ≤ π / 2`, the vertices are `I`, a point `C` to the
  right of the imaginary axis, and `i e^d` with `cosh d = (cos α cos β + cos γ) / (sin α sin β)`,
  which exceeds `1` exactly because `α + β + γ < π`: this is the hyperbolic law of cosines for
  the side opposite `C`. The sides through `C` lie on the semicircles of centres `cot α` and
  `-e^d cot β` and radii `1 / sin α` and `e^d / sin β`, whose radius vectors at `C` make the angle
  `γ`. The angles are computed by `UpperHalfPlane.interiorAngle_of_normal_form` and its
  companions. At most one angle of a triangle exceeds `π / 2`, so a cyclic relabelling puts any
  triangle without ideal vertices in this form.

## Main results

* `ConvexPolygon.exists_interiorAngle_eq_iff`: the angle triples of convex hyperbolic triangles
  are exactly the nonnegative triples with sum less than `π`.
* `TauCeti.TriangleOrder.isHyperbolic_iff_exists_interiorAngle_eq`: a triple of elliptic orders
  and cusps is hyperbolic exactly when some convex hyperbolic triangle has the corresponding
  angles.

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
  have hpq : p ≠ q := fun h ↦ hlt.ne (by rw [h])
  -- the vertices `p`, `q`, `∞` run counterclockwise: `∞` is above the semicircle from `p` to
  -- `q`, and each of `p`, `q` is on the inner side of the vertical through the other
  have h₀ : (∞ : OnePoint ℝ) ∈ boundaryLeftHalfPlane (geodesicFromTo p q) :=
    ((isGeodesicFromTo_geodesicFromTo hpq).infty_mem_boundaryLeftHalfPlane_iff_re_lt hp hq).2 hlt
  have h₁ : p ∈ extLeftHalfPlane (geodesicFromTo q (.inr ∞)) := by
    refine (mem_extLeftHalfPlane_iff_sideForm_toComplex_neg hp).2 ?_
    rw [(isGeodesicFromTo_geodesicFromTo hq).sideForm_eq_of_inr_infty_right hq]
    linarith
  have h₂ : q ∈ extLeftHalfPlane (geodesicFromTo (.inr ∞) p) := by
    refine (mem_extLeftHalfPlane_iff_sideForm_toComplex_neg hq).2 ?_
    rw [(isGeodesicFromTo_geodesicFromTo hp.symm).sideForm_eq_of_inr_infty_left hp]
    linarith
  refine ⟨⟨![p, q, .inr ∞], le_rfl, fun i ↦ ?_, fun i j hji hji' ↦ ?_⟩, ?_, ?_, ?_⟩
  · fin_cases i
    exacts [hpq, hq, hp.symm]
  · fin_cases i <;> fin_cases j <;> simp [h₀, h₁, h₂] at hji hji' ⊢
  · rw [ConvexPolygon.interiorAngle_def, show (0 : Fin 3) - 1 = 2 from rfl, zero_add]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons,
      Matrix.head_cons]
    rw [vertexAngle_infty_of_re_lt one_pos hp hq hpm hqm hlt, hpre, sub_zero, div_one,
      Real.cos_pi_sub, Real.arccos_neg, Real.arccos_cos hα (by linarith)]
    ring
  · rw [ConvexPolygon.interiorAngle_def, sub_self, show (1 : Fin 3) + 1 = 2 from rfl]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons,
      Matrix.head_cons]
    rw [vertexAngle_infty_of_lt_re one_pos hp hq hpm hqm hlt, hqre, sub_zero, div_one,
      Real.arccos_cos hβ (by linarith)]
  · exact ConvexPolygon.interiorAngle_eq_zero_of_vertex_eq_inr _ (ξ := ∞) rfl

/-! ### A triangle with three finite vertices -/

/-- Two circles with centres `c₂ < c₁` on the real axis and radii `ρ₁`, `ρ₂`, whose distance of
centres satisfies the law of cosines for the angle `γ ∈ (0, π)`, meet at a point `x + i y` of the
upper half-plane where their radius vectors make the angle `γ`. -/
private theorem exists_arccos_sub_arccos_eq {c₁ c₂ ρ₁ ρ₂ γ : ℝ} (hρ₁ : 0 < ρ₁) (hρ₂ : 0 < ρ₂)
    (hγ : 0 < γ) (hγπ : γ < π) (hD : 0 < c₁ - c₂)
    (hkey : (c₁ - c₂) ^ 2 = ρ₁ ^ 2 + ρ₂ ^ 2 - 2 * ρ₁ * ρ₂ * Real.cos γ) :
    ∃ x y : ℝ, 0 < y ∧ (x - c₁) ^ 2 + y ^ 2 = ρ₁ ^ 2 ∧ (x - c₂) ^ 2 + y ^ 2 = ρ₂ ^ 2 ∧
      Real.arccos ((x - c₁) / ρ₁) - Real.arccos ((x - c₂) / ρ₂) = γ := by
  set D := c₁ - c₂
  set c := Real.cos γ
  set s := Real.sin γ
  have hs : 0 < s := Real.sin_pos_of_pos_of_lt_pi hγ hγπ
  have hcs : s ^ 2 + c ^ 2 = 1 := Real.sin_sq_add_cos_sq γ
  have hc : c < 1 := by
    rw [← Real.cos_zero]
    exact Real.cos_lt_cos_of_nonneg_of_le_pi le_rfl hγπ.le hγ
  -- the cosines `u₁`, `u₂` and sines `ρ₂ s / D`, `ρ₁ s / D` of the arguments of the radius vectors
  set u₁ := -(ρ₁ - ρ₂ * c) / D with hu₁
  set u₂ := (ρ₂ - ρ₁ * c) / D with hu₂
  have hx : c₁ + ρ₁ * u₁ - c₂ = ρ₂ * u₂ := by
    rw [hu₁, hu₂]
    field_simp
    linear_combination hkey
  have hu₁' : 1 - u₁ ^ 2 = (ρ₂ * s / D) ^ 2 := by
    rw [hu₁]
    field_simp
    linear_combination hkey - ρ₂ ^ 2 * hcs
  have hu₂' : 1 - u₂ ^ 2 = (ρ₁ * s / D) ^ 2 := by
    rw [hu₂]
    field_simp
    linear_combination hkey - ρ₁ ^ 2 * hcs
  have hsin₁ : Real.sin (Real.arccos u₁) = ρ₂ * s / D := by
    rw [Real.sin_arccos, hu₁', Real.sqrt_sq (by positivity)]
  have hsin₂ : Real.sin (Real.arccos u₂) = ρ₁ * s / D := by
    rw [Real.sin_arccos, hu₂', Real.sqrt_sq (by positivity)]
  have hb₁ : -1 ≤ u₁ ∧ u₁ ≤ 1 := by
    constructor <;> nlinarith [sq_nonneg (ρ₂ * s / D)]
  have hb₂ : -1 ≤ u₂ ∧ u₂ ≤ 1 := by
    constructor <;> nlinarith [sq_nonneg (ρ₁ * s / D)]
  -- the angle between the radius vectors has cosine `c`, and lies in `[0, π]` as `u₁ ≤ u₂`
  have hcos : Real.cos (Real.arccos u₁ - Real.arccos u₂) = c := by
    rw [Real.cos_sub, Real.cos_arccos hb₁.1 hb₁.2, Real.cos_arccos hb₂.1 hb₂.2, hsin₁, hsin₂,
      hu₁, hu₂]
    field_simp
    linear_combination (-c) * hkey + ρ₁ * ρ₂ * hcs
  have hle : u₁ ≤ u₂ := by
    rw [hu₁, hu₂, div_le_div_iff_of_pos_right hD]
    nlinarith
  clear_value u₁ u₂
  refine ⟨c₁ + ρ₁ * u₁, ρ₁ * (ρ₂ * s / D), by positivity, ?_, ?_, ?_⟩
  · linear_combination (-ρ₁ ^ 2) * hu₁'
  · rw [hx]
    linear_combination (-ρ₂ ^ 2) * hu₂'
  · rw [add_sub_cancel_left, mul_div_cancel_left₀ _ hρ₁.ne', hx, mul_div_cancel_left₀ _ hρ₂.ne',
      ← Real.arccos_cos (sub_nonneg.2 (Real.arccos_le_arccos hle))
        ((sub_le_self _ (Real.arccos_nonneg _)).trans (Real.arccos_le_pi _)), hcos,
      Real.arccos_cos hγ.le hγπ.le]

/-- For `α, β ∈ (0, π / 2]` and `γ > 0` with `α + β + γ < π` there is a compact convex triangle
with angles `α`, `γ` and `β` at its three vertices. -/
private theorem exists_compactConvexPolygon_three {α β γ : ℝ} (hα : 0 < α) (hα' : α ≤ π / 2)
    (hβ : 0 < β) (hβ' : β ≤ π / 2) (hγ : 0 < γ) (h : α + β + γ < π) :
    ∃ P : CompactConvexPolygon 3,
      P.interiorAngle 0 = α ∧ P.interiorAngle 1 = γ ∧ P.interiorAngle 2 = β := by
  have hsα : 0 < Real.sin α := Real.sin_pos_of_pos_of_lt_pi hα (by linarith)
  have hsβ : 0 < Real.sin β := Real.sin_pos_of_pos_of_lt_pi hβ (by linarith)
  have hcα : 0 ≤ Real.cos α := Real.cos_nonneg_of_mem_Icc ⟨by linarith, hα'⟩
  have hcβ : 0 ≤ Real.cos β := Real.cos_nonneg_of_mem_Icc ⟨by linarith, hβ'⟩
  have hα₂ := Real.sin_sq_add_cos_sq α
  have hβ₂ := Real.sin_sq_add_cos_sq β
  -- the side from `I` up to `i t` has length `log t`, where `(t + t⁻¹) / 2 = K` by the hyperbolic
  -- law of cosines; `K > 1` is the angle condition `γ < π - α - β`
  obtain ⟨K, hKs, hK₁⟩ : ∃ K : ℝ,
      K * (Real.sin α * Real.sin β) = Real.cos α * Real.cos β + Real.cos γ ∧ 1 < K := by
    refine ⟨(Real.cos α * Real.cos β + Real.cos γ) / (Real.sin α * Real.sin β),
      div_mul_cancel₀ _ (by positivity), ?_⟩
    have hc := Real.cos_lt_cos_of_nonneg_of_le_pi hγ.le (by linarith : π - (α + β) ≤ π)
      (by linarith : γ < π - (α + β))
    rw [Real.cos_pi_sub, Real.cos_add] at hc
    rw [one_lt_div (by positivity)]
    linarith
  obtain ⟨t, ht₁, htK⟩ : ∃ t : ℝ, 1 < t ∧ t ^ 2 + 1 = 2 * K * t := by
    refine ⟨K + √(K ^ 2 - 1), by linarith [Real.sqrt_nonneg (K ^ 2 - 1)], ?_⟩
    linear_combination Real.sq_sqrt (by nlinarith : (0 : ℝ) ≤ K ^ 2 - 1)
  have hd : 0 < Real.log t := Real.log_pos ht₁
  have hBc : (geodesicLine 1 (Real.log t) : ℂ) = ⟨0, t⟩ := by
    rw [geodesicLine_one_apply, UpperHalfPlane.coe_mk, Real.exp_log (by linarith)]
  -- the sides through the third vertex lie on circles of centres `c₁`, `c₂` and radii `ρ₁`, `ρ₂`
  obtain ⟨c₁, hc₁⟩ : ∃ c₁ : ℝ, c₁ = Real.cos α / Real.sin α := ⟨_, rfl⟩
  obtain ⟨ρ₁, hρ₁⟩ : ∃ ρ₁ : ℝ, ρ₁ = (Real.sin α)⁻¹ := ⟨_, rfl⟩
  obtain ⟨c₂, hc₂⟩ : ∃ c₂ : ℝ, c₂ = -(t * Real.cos β / Real.sin β) := ⟨_, rfl⟩
  obtain ⟨ρ₂, hρ₂⟩ : ∃ ρ₂ : ℝ, ρ₂ = t / Real.sin β := ⟨_, rfl⟩
  have hρ₁0 : 0 < ρ₁ := hρ₁ ▸ inv_pos.2 hsα
  have hρ₂0 : 0 < ρ₂ := hρ₂ ▸ div_pos (by linarith) hsβ
  have hρc₁ : ρ₁ ^ 2 = c₁ ^ 2 + 1 := by
    rw [hρ₁, hc₁]
    field_simp
    linear_combination -hα₂
  have hρc₂ : ρ₂ ^ 2 = c₂ ^ 2 + t ^ 2 := by
    rw [hρ₂, hc₂]
    field_simp
    linear_combination -hβ₂
  have hD : 0 < c₁ - c₂ := by
    have h₁ : (c₁ - c₂) * (Real.sin α * Real.sin β) =
        Real.sin (α + β) + (t - 1) * (Real.sin α * Real.cos β) := by
      rw [hc₁, hc₂, Real.sin_add]
      field_simp
      ring
    have h₂ : 0 < Real.sin (α + β) := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
    have h₃ : 0 ≤ (t - 1) * (Real.sin α * Real.cos β) :=
      mul_nonneg (by linarith) (by positivity)
    nlinarith [mul_pos hsα hsβ]
  have hkey : (c₁ - c₂) ^ 2 = ρ₁ ^ 2 + ρ₂ ^ 2 - 2 * ρ₁ * ρ₂ * Real.cos γ := by
    rw [hc₁, hc₂, hρ₁, hρ₂]
    field_simp
    linear_combination (-(Real.sin α ^ 2 * Real.sin β ^ 2)) * htK + Real.sin β ^ 2 * hα₂ +
      t ^ 2 * Real.sin α ^ 2 * hβ₂ - 2 * t * Real.sin α * Real.sin β * hKs
  -- the third vertex `C` is where the two circles meet at the angle `γ`
  obtain ⟨x, y, hy, h₁, h₂, hγ'⟩ := exists_arccos_sub_arccos_eq hρ₁0 hρ₂0 hγ (by linarith) hD hkey
  obtain ⟨C, hCc⟩ : ∃ C : ℍ, (C : ℂ) = ⟨x, y⟩ := ⟨UpperHalfPlane.mk _ hy, rfl⟩
  have hCre : 0 < C.re := by
    have hx : 2 * x * (c₁ - c₂) = t ^ 2 - 1 := by linear_combination h₂ - h₁ - hρc₁ + hρc₂
    have hx' := (mul_pos_iff_of_pos_right hD).1 (hx ▸ sub_pos.2 (one_lt_pow₀ ht₁ two_ne_zero))
    rw [← UpperHalfPlane.coe_re, hCc]
    linarith
  have hIc₁ : Complex.normSq ((UpperHalfPlane.I : ℂ) - c₁) = ρ₁ ^ 2 := by
    rw [UpperHalfPlane.coe_I, Complex.normSq_apply, hρc₁]
    simp only [Complex.sub_re, Complex.sub_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im]
    ring
  have hCc₁ : Complex.normSq ((C : ℂ) - c₁) = ρ₁ ^ 2 := by
    rw [hCc, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im]
    linear_combination h₁
  have hBc₂ : Complex.normSq ((geodesicLine 1 (Real.log t) : ℂ) - c₂) = ρ₂ ^ 2 := by
    rw [hBc, Complex.normSq_apply, hρc₂]
    simp only [Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im]
    ring
  have hCc₂ : Complex.normSq ((C : ℂ) - c₂) = ρ₂ ^ 2 := by
    rw [hCc, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im]
    linear_combination h₂
  -- `0 < C.re * (t ^ 2 - 1)` decides the sides of the two semicircles through `C`
  have ht₁t : 0 < C.re * (t ^ 2 - 1) := mul_pos hCre (sub_pos.2 (one_lt_pow₀ ht₁ two_ne_zero))
  have hIC : UpperHalfPlane.I.re ≠ C.re := by
    rw [UpperHalfPlane.I_re]
    exact hCre.ne
  have hBre : (geodesicLine 1 (Real.log t)).re = 0 := by
    rw [← UpperHalfPlane.coe_re, hBc]
  have hBC : (geodesicLine 1 (Real.log t)).re ≠ C.re := by
    rw [hBre]
    exact hCre.ne
  have hcc₁ : circleCenter UpperHalfPlane.I C = c₁ :=
    circleCenter_eq_of_normSq_eq hIC (hIc₁.trans hCc₁.symm)
  have hcc₂ : circleCenter (geodesicLine 1 (Real.log t)) C = c₂ :=
    circleCenter_eq_of_normSq_eq hBC (hBc₂.trans hCc₂.symm)
  -- the vertices `I`, `C`, `i t` run counterclockwise
  have hv₀ :
      geodesicLine 1 (Real.log t) ∈ leftHalfPlane (geodesicBetween UpperHalfPlane.I C) := by
    rw [mem_leftHalfPlane_geodesicBetween_iff_of_re_ne hIC, hcc₁, hIc₁, UpperHalfPlane.I_re,
      Complex.normSq_apply, hBc, hρc₁]
    simp only [Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im]
    linear_combination (exp := 1) ht₁t
  have hv₁ : UpperHalfPlane.I ∈
      leftHalfPlane (geodesicBetween C (geodesicLine 1 (Real.log t))) := by
    rw [mem_leftHalfPlane_geodesicBetween_iff_of_re_ne hBC.symm, circleCenter_comm, hcc₂, hCc₂,
      UpperHalfPlane.coe_I, Complex.normSq_apply, hρc₂, hBre]
    simp only [Complex.sub_re, Complex.sub_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im]
    linear_combination (exp := 1) ht₁t
  have hv₂ : C ∈
      leftHalfPlane (geodesicBetween (geodesicLine 1 (Real.log t)) UpperHalfPlane.I) := by
    have hIB : UpperHalfPlane.I ≠ geodesicLine 1 (Real.log t) := fun h ↦ by
      have him := congrArg (fun z : ℍ ↦ (z : ℂ).im) h
      simp only [UpperHalfPlane.coe_I, Complex.I_im, hBc] at him
      linarith
    rw [geodesicBetween_swap hIB, geodesicBetween_I_geodesicLine_one hd, leftHalfPlane_mul_pslS,
      rightHalfPlane_mul_dilation, mem_rightHalfPlane_iff, inv_one, one_smul]
    exact hCre
  refine ⟨⟨![UpperHalfPlane.I, C, geodesicLine 1 (Real.log t)], le_rfl, fun i j hji hji' ↦ ?_⟩,
    ?_, ?_, ?_⟩
  · -- the vertex opposite each edge is on its left; the other six pairs are excluded by `hji`
    -- and `hji'`
    fin_cases i <;> fin_cases j
    exacts [absurd rfl hji, absurd rfl hji', hv₀, hv₁, absurd rfl hji, absurd rfl hji',
      absurd rfl hji', hv₂, absurd rfl hji]
  · rw [CompactConvexPolygon.interiorAngle_def, show (0 : Fin 3) - 1 = 2 from rfl, zero_add]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons,
      Matrix.head_cons]
    rw [interiorAngle_I_geodesicLine_one hd hCre, hcc₁, hIc₁, Real.sqrt_sq hρ₁0.le,
      show c₁ / ρ₁ = Real.cos α by rw [hc₁, hρ₁]; field_simp, Real.arccos_cos hα.le (by linarith)]
  · rw [CompactConvexPolygon.interiorAngle_def, sub_self, show (1 : Fin 3) + 1 = 2 from rfl]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons,
      Matrix.head_cons]
    rw [interiorAngle_of_normal_form hd hCre, hcc₁, hcc₂, hIc₁, hBc₂, Real.sqrt_sq hρ₁0.le,
      Real.sqrt_sq hρ₂0.le, ← UpperHalfPlane.coe_re, hCc]
    exact hγ'
  · rw [CompactConvexPolygon.interiorAngle_def, show (2 : Fin 3) - 1 = 1 from rfl,
      show (2 : Fin 3) + 1 = 0 from rfl]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons,
      Matrix.head_cons]
    rw [interiorAngle_geodesicLine_one_I hd hCre, hcc₂, hBc₂, Real.sqrt_sq hρ₂0.le,
      show c₂ / ρ₂ = -Real.cos β by rw [hc₂, hρ₂]; field_simp, Real.arccos_neg,
      Real.arccos_cos hβ.le (by linarith)]
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
  exact ⟨P.rotate 1, by rw [interiorAngle_rotate, zero_add, hβ],
    by rw [interiorAngle_rotate, show (1 : Fin 3) + 1 = 2 from rfl, hγ],
    by rw [interiorAngle_rotate, show (2 : Fin 3) + 1 = 0 from rfl, hα]⟩

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
  -- a compact triangle, with an angle exceeding `π / 2`, if any, at its vertex `1`
  have hcompact {a b c : ℝ} (ha : 0 < a) (ha' : a ≤ π / 2) (hb : 0 < b) (hc : 0 < c)
      (hc' : c ≤ π / 2) (h : a + b + c < π) : ∃ P : ConvexPolygon 3,
        P.interiorAngle 0 = a ∧ P.interiorAngle 1 = b ∧ P.interiorAngle 2 = c := by
    obtain ⟨Q, h₀, h₁, h₂⟩ := exists_compactConvexPolygon_three ha ha' hc hc' hb (by linarith)
    exact ⟨Q.toConvexPolygon, by rw [CompactConvexPolygon.interiorAngle_toConvexPolygon, h₀],
      by rw [CompactConvexPolygon.interiorAngle_toConvexPolygon, h₁],
      by rw [CompactConvexPolygon.interiorAngle_toConvexPolygon, h₂]⟩
  by_cases hα' : π / 2 < α
  · exact exists_interiorAngle_eq_rotate
      (hcompact hγ (by linarith) hα hβ (by linarith) (by linarith))
  by_cases hγ' : π / 2 < γ
  · exact exists_interiorAngle_eq_rotate (exists_interiorAngle_eq_rotate
      (hcompact hβ (by linarith) hγ hα (by linarith) (by linarith)))
  exact hcompact hα (not_lt.1 hα') hβ hγ (not_lt.1 hγ') h

end ConvexPolygon

end TauCeti.UpperHalfPlane

namespace TauCeti.TriangleOrder

/-- **Hyperbolic triangles with elliptic and cusp vertices.** A triple of elliptic orders and
cusps is hyperbolic exactly when some convex hyperbolic triangle has the corresponding angles:
`π / m` at a vertex of elliptic order `m`, and `0` at a cusp, which is then an ideal vertex by
`UpperHalfPlane.ConvexPolygon.interiorAngle_eq_zero_iff`. -/
theorem isHyperbolic_iff_exists_interiorAngle_eq {p q r : TriangleOrder} :
    IsHyperbolic p q r ↔ ∃ P : UpperHalfPlane.ConvexPolygon 3,
      P.interiorAngle 0 = p.angle ∧ P.interiorAngle 1 = q.angle ∧
        P.interiorAngle 2 = r.angle := by
  rw [UpperHalfPlane.ConvexPolygon.exists_interiorAngle_eq_iff, isHyperbolic_iff_angle_sum_lt_pi]
  exact ⟨fun h ↦ ⟨p.angle_nonneg, q.angle_nonneg, r.angle_nonneg, h⟩, fun h ↦ h.2.2.2⟩

end TauCeti.TriangleOrder
