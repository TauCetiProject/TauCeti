/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Conformal.SchwarzChristoffel.Polygon.Mapping
public import TauCeti.Analysis.Complex.Conformal.SchwarzChristoffel.SideLength
import Mathlib.Analysis.Complex.Convex

/-!
# The Schwarz--Christoffel map onto a rectangle

For a modulus `0 < k < 1`, the four prevertices `-k⁻¹ < -1 < 1 < k⁻¹`, each with turning exponent
`-1 / 2`, give the classical Schwarz--Christoffel map of the upper half-plane onto a rectangle.
Up to the affine normalization `z ↦ (m - F z) / k`, where `F` is the normalized primitive and `m`
is the midpoint of the vertices at `-1` and `1`, its image is the open rectangle
`(-K, K) × (0, K')` with

* `K = ∫₀¹ dx / √((1 - x²)(1 - k²x²))`, the complete elliptic integral of the first kind, and
* `K' = ∫₁^{1/k} dx / √((x² - 1)(1 - k²x²))`, the height of the rectangle.

Since every exponent lies in `(-1, 0)` and the exponents sum to `-2`, the convex polygon mapping
theorem `TauCeti.bijOn_schwarzChristoffelPrimitive_interior_closedConvexHull` applies. What
remains is to identify the polygon. The density on the boundary is even, and it equals
`k / √(|1 - x²| (1 - k²x²))` between `-k⁻¹` and `k⁻¹`. So the side lengths are `kK'`, `2kK` and
`kK'`, and the edge angles turn the sides by right angles.

## Main results

* `TauCeti.schwarzChristoffelVertex_succ_sub_rectangle` -- the side vectors of the polygon.
* `TauCeti.bijOn_sub_schwarzChristoffelPrimitive_div_rectangle` -- the normalized map is a
  bijection of the upper half-plane onto `(-K, K) × (0, K')`.

## References

* L. Ahlfors, *Complex Analysis*, Ch. 6, Section 2.
* T. Driscoll and L. Trefethen, *Schwarz--Christoffel Mapping*, Ch. 2.
-/

public section

noncomputable section

open Complex Set UpperHalfPlane

namespace TauCeti

variable {k : ℝ}

private lemma strictMono_rectanglePrevertex (hk0 : 0 < k) (hk1 : k < 1) :
    StrictMono ![-k⁻¹, -1, 1, k⁻¹] := by
  have h1 : 1 < k⁻¹ := (one_lt_inv₀ hk0).mpr hk1
  refine Fin.strictMono_iff_lt_succ.mpr fun i => ?_
  fin_cases i <;> simp <;> linarith

private lemma schwarzChristoffelDensity_rectangle_neg (x : ℝ) :
    schwarzChristoffelDensity ![-k⁻¹, -1, 1, k⁻¹] (fun _ => -(1 / 2)) (-x) =
      schwarzChristoffelDensity ![-k⁻¹, -1, 1, k⁻¹] (fun _ => -(1 / 2)) x := by
  have h (c : ℝ) : |-x - c| = |x + c| := by rw [← abs_neg]; ring_nf
  simp only [schwarzChristoffelDensity_def, Fin.prod_univ_four, h]
  simp [← sub_eq_add_neg]
  ring

private lemma schwarzChristoffelDensity_rectangle (hk0 : 0 < k) {x : ℝ} (hx : |x| ≤ k⁻¹) :
    schwarzChristoffelDensity ![-k⁻¹, -1, 1, k⁻¹] (fun _ => -(1 / 2)) x =
      k * (1 / √(|1 - x ^ 2| * (1 - k ^ 2 * x ^ 2))) := by
  have hkx : 0 ≤ 1 - k ^ 2 * x ^ 2 := by
    have : |k * x| ≤ 1 := by
      rw [abs_mul, abs_of_pos hk0]
      calc k * |x| ≤ k * k⁻¹ := by gcongr
        _ = 1 := mul_inv_cancel₀ hk0.ne'
    nlinarith [abs_mul_abs_self (k * x), abs_nonneg (k * x)]
  simp only [schwarzChristoffelDensity_def, Fin.prod_univ_four, Matrix.cons_val, sub_neg_eq_add]
  rw [← Real.mul_rpow (abs_nonneg _) (abs_nonneg _),
    ← Real.mul_rpow (by positivity) (abs_nonneg _),
    ← Real.mul_rpow (by positivity) (abs_nonneg _)]
  have hprod : |x + k⁻¹| * |x + 1| * |x - 1| * |x - k⁻¹| =
      |1 - x ^ 2| * (1 - k ^ 2 * x ^ 2) / k ^ 2 := by
    have h1 : |x + k⁻¹| * |x - k⁻¹| = (1 - k ^ 2 * x ^ 2) / k ^ 2 := by
      rw [← abs_mul, show (x + k⁻¹) * (x - k⁻¹) = -((1 - k ^ 2 * x ^ 2) / k ^ 2) by
        field_simp; ring, abs_neg, abs_of_nonneg (by positivity)]
    have h2 : |x + 1| * |x - 1| = |1 - x ^ 2| := by
      rw [← abs_mul, ← abs_neg]
      ring_nf
    calc |x + k⁻¹| * |x + 1| * |x - 1| * |x - k⁻¹|
        = (|x + 1| * |x - 1|) * (|x + k⁻¹| * |x - k⁻¹|) := by ring
      _ = _ := by rw [h1, h2]; ring
  rw [hprod, Real.rpow_neg (by positivity),
    ← Real.sqrt_eq_rpow, Real.sqrt_div' _ (by positivity), Real.sqrt_sq hk0.le,
    Real.sqrt_mul (abs_nonneg _)]
  field_simp

private lemma exp_schwarzChristoffelEdgeAngle_rectangle (hk0 : 0 < k) (hk1 : k < 1) :
    Complex.exp (schwarzChristoffelEdgeAngle ![-k⁻¹, -1, 1, k⁻¹] (fun _ => -(1 / 2)) (-k⁻¹) *
        Complex.I) = Complex.I ∧
      Complex.exp (schwarzChristoffelEdgeAngle ![-k⁻¹, -1, 1, k⁻¹] (fun _ => -(1 / 2)) (-1) *
        Complex.I) = -1 ∧
      Complex.exp (schwarzChristoffelEdgeAngle ![-k⁻¹, -1, 1, k⁻¹] (fun _ => -(1 / 2)) 1 *
        Complex.I) = -Complex.I := by
  have h1 : 1 < k⁻¹ := (one_lt_inv₀ hk0).mpr hk1
  have hθ₀ : schwarzChristoffelEdgeAngle ![-k⁻¹, -1, 1, k⁻¹] (fun _ => -(1 / 2)) (-k⁻¹) =
      Real.pi / 2 - 2 * Real.pi := by
    rw [schwarzChristoffelEdgeAngle_eq_sum_filter, Finset.sum_filter, Fin.sum_univ_four]
    simp [show -k⁻¹ < -1 by linarith, show -k⁻¹ < 1 by linarith, show -k⁻¹ < k⁻¹ by linarith]
    ring
  have hθ₁ : schwarzChristoffelEdgeAngle ![-k⁻¹, -1, 1, k⁻¹] (fun _ => -(1 / 2)) (-1) =
      -Real.pi := by
    rw [schwarzChristoffelEdgeAngle_eq_sum_filter, Finset.sum_filter, Fin.sum_univ_four]
    simp [show ¬ (-1 < -k⁻¹) by linarith, show (-1 : ℝ) < k⁻¹ by linarith]
    ring
  have hθ₂ : schwarzChristoffelEdgeAngle ![-k⁻¹, -1, 1, k⁻¹] (fun _ => -(1 / 2)) 1 =
      -(Real.pi / 2) := by
    rw [schwarzChristoffelEdgeAngle_eq_sum_filter, Finset.sum_filter, Fin.sum_univ_four]
    simp [show ¬ (1 < -k⁻¹) by linarith, h1, show ¬ (1 : ℝ) < -1 by norm_num]
    ring
  rw [hθ₀, hθ₁, hθ₂]
  refine ⟨?_, ?_, ?_⟩ <;> apply Complex.ext <;>
    simp only [exp_ofReal_mul_I_re, exp_ofReal_mul_I_im] <;>
    simp [Real.cos_sub_two_pi, Real.sin_sub_two_pi]

private lemma schwarzChristoffelSideIntegral_rectangle (hk0 : 0 < k) (hk1 : k < 1) :
    schwarzChristoffelSideIntegral ![-k⁻¹, -1, 1, k⁻¹] (fun _ => -(1 / 2)) 0 =
        k * ∫ x in (1 : ℝ)..k⁻¹, 1 / √((x ^ 2 - 1) * (1 - k ^ 2 * x ^ 2)) ∧
      schwarzChristoffelSideIntegral ![-k⁻¹, -1, 1, k⁻¹] (fun _ => -(1 / 2)) 1 =
        2 * k * ∫ x in (0 : ℝ)..1, 1 / √((1 - x ^ 2) * (1 - k ^ 2 * x ^ 2)) ∧
      schwarzChristoffelSideIntegral ![-k⁻¹, -1, 1, k⁻¹] (fun _ => -(1 / 2)) 2 =
        k * ∫ x in (1 : ℝ)..k⁻¹, 1 / √((x ^ 2 - 1) * (1 - k ^ 2 * x ^ 2)) := by
  have h1 : 1 < k⁻¹ := (one_lt_inv₀ hk0).mpr hk1
  set D := schwarzChristoffelDensity ![-k⁻¹, -1, 1, k⁻¹] (fun _ => -(1 / 2)) with hD
  have hDneg (x : ℝ) : D (-x) = D x := schwarzChristoffelDensity_rectangle_neg x
  -- the outer sides: the density integral from `1` to `k⁻¹`
  have hout : ∫ x in (1 : ℝ)..k⁻¹, D x =
      k * ∫ x in (1 : ℝ)..k⁻¹, 1 / √((x ^ 2 - 1) * (1 - k ^ 2 * x ^ 2)) := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun x hx => ?_
    rw [uIcc_of_le h1.le] at hx
    rw [hD, schwarzChristoffelDensity_rectangle hk0 (abs_le.mpr ⟨by linarith [hx.1], hx.2⟩),
      abs_of_nonpos (by nlinarith [hx.1]), neg_sub]
  -- the middle side: the density integral from `0` to `1`
  have hin : ∫ x in (0 : ℝ)..1, D x =
      k * ∫ x in (0 : ℝ)..1, 1 / √((1 - x ^ 2) * (1 - k ^ 2 * x ^ 2)) := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun x hx => ?_
    rw [uIcc_of_le zero_le_one] at hx
    rw [hD, schwarzChristoffelDensity_rectangle hk0
      (abs_le.mpr ⟨by linarith [hx.1], by linarith [hx.2]⟩),
      abs_of_nonneg (by nlinarith [hx.1, hx.2])]
  have hint : IntervalIntegrable D MeasureTheory.volume (-1) 1 :=
    intervalIntegrable_schwarzChristoffelDensity_succ ![-k⁻¹, -1, 1, k⁻¹]
      (fun _ => -(1 / 2)) (strictMono_rectanglePrevertex hk0 hk1) 1 (by norm_num) (by norm_num)
  have hside₀ : schwarzChristoffelSideIntegral ![-k⁻¹, -1, 1, k⁻¹] (fun _ => -(1 / 2)) 0 =
      ∫ x in -k⁻¹..-1, D x :=
    schwarzChristoffelSideIntegral_def _ _ _
  have hside₁ : schwarzChristoffelSideIntegral ![-k⁻¹, -1, 1, k⁻¹] (fun _ => -(1 / 2)) 1 =
      ∫ x in (-1 : ℝ)..1, D x :=
    schwarzChristoffelSideIntegral_def _ _ _
  have hside₂ : schwarzChristoffelSideIntegral ![-k⁻¹, -1, 1, k⁻¹] (fun _ => -(1 / 2)) 2 =
      ∫ x in (1 : ℝ)..k⁻¹, D x :=
    schwarzChristoffelSideIntegral_def _ _ _
  have hneg (p q : ℝ) : ∫ x in -q..-p, D x = ∫ x in p..q, D x := by
    simp only [← intervalIntegral.integral_comp_neg, hDneg]
  refine ⟨by rw [hside₀, hneg, hout], ?_, by rw [hside₂, hout]⟩
  have hleft : ∫ x in (-1 : ℝ)..0, D x = ∫ x in (0 : ℝ)..1, D x := by simpa using hneg 0 1
  rw [hside₁, ← intervalIntegral.integral_add_adjacent_intervals (b := 0)
    (hint.mono_set (by simp [uIcc_of_le, Icc_subset_Icc]))
    (hint.mono_set (by simp [uIcc_of_le, Icc_subset_Icc])), hleft, hin]
  ring

/-- **The sides of the Schwarz--Christoffel rectangle.** For `0 < k < 1`, the vertices at the
prevertices `-k⁻¹`, `-1`, `1`, `k⁻¹` with exponents `-1 / 2` differ successively by `k K' i`,
`-2 k K` and `-k K' i`, where `K = ∫₀¹ dx / √((1 - x²)(1 - k²x²))` and
`K' = ∫₁^{1/k} dx / √((x² - 1)(1 - k²x²))`. -/
theorem schwarzChristoffelVertex_succ_sub_rectangle (hk0 : 0 < k) (hk1 : k < 1)
    (z₀ : UpperHalfPlane) :
    schwarzChristoffelVertex ![-k⁻¹, -1, 1, k⁻¹] (fun _ => -(1 / 2)) z₀ 1 -
        schwarzChristoffelVertex ![-k⁻¹, -1, 1, k⁻¹] (fun _ => -(1 / 2)) z₀ 0 =
        ((k * ∫ x in (1 : ℝ)..k⁻¹, 1 / √((x ^ 2 - 1) * (1 - k ^ 2 * x ^ 2)) : ℝ) : ℂ) *
          Complex.I ∧
      schwarzChristoffelVertex ![-k⁻¹, -1, 1, k⁻¹] (fun _ => -(1 / 2)) z₀ 2 -
        schwarzChristoffelVertex ![-k⁻¹, -1, 1, k⁻¹] (fun _ => -(1 / 2)) z₀ 1 =
        -((2 * k * ∫ x in (0 : ℝ)..1, 1 / √((1 - x ^ 2) * (1 - k ^ 2 * x ^ 2)) : ℝ) : ℂ) ∧
      schwarzChristoffelVertex ![-k⁻¹, -1, 1, k⁻¹] (fun _ => -(1 / 2)) z₀ 3 -
        schwarzChristoffelVertex ![-k⁻¹, -1, 1, k⁻¹] (fun _ => -(1 / 2)) z₀ 2 =
        -(((k * ∫ x in (1 : ℝ)..k⁻¹, 1 / √((x ^ 2 - 1) * (1 - k ^ 2 * x ^ 2)) : ℝ) : ℂ) *
          Complex.I) := by
  have ha := strictMono_rectanglePrevertex hk0 hk1
  obtain ⟨hθ₀, hθ₁, hθ₂⟩ := exp_schwarzChristoffelEdgeAngle_rectangle hk0 hk1
  obtain ⟨hL₀, hL₁, hL₂⟩ := schwarzChristoffelSideIntegral_rectangle hk0 hk1
  set a : Fin 4 → ℝ := ![-k⁻¹, -1, 1, k⁻¹]
  set e : Fin 4 → ℝ := fun _ => -(1 / 2)
  have hv₀ : schwarzChristoffelVertex a e z₀ 1 - schwarzChristoffelVertex a e z₀ 0 =
      schwarzChristoffelSideIntegral a e 0 *
        Complex.exp (schwarzChristoffelEdgeAngle a e (-k⁻¹) * Complex.I) :=
    schwarzChristoffelVertex_succ_sub_eq_sideIntegral_mul a e z₀ ha 0 (by norm_num) (by norm_num)
  have hv₁ : schwarzChristoffelVertex a e z₀ 2 - schwarzChristoffelVertex a e z₀ 1 =
      schwarzChristoffelSideIntegral a e 1 *
        Complex.exp (schwarzChristoffelEdgeAngle a e (-1) * Complex.I) :=
    schwarzChristoffelVertex_succ_sub_eq_sideIntegral_mul a e z₀ ha 1 (by norm_num) (by norm_num)
  have hv₂ : schwarzChristoffelVertex a e z₀ 3 - schwarzChristoffelVertex a e z₀ 2 =
      schwarzChristoffelSideIntegral a e 2 *
        Complex.exp (schwarzChristoffelEdgeAngle a e 1 * Complex.I) :=
    schwarzChristoffelVertex_succ_sub_eq_sideIntegral_mul a e z₀ ha 2 (by norm_num) (by norm_num)
  rw [hv₀, hv₁, hv₂, hθ₀, hθ₁, hθ₂, hL₀, hL₁, hL₂, mul_neg_one, mul_neg]
  exact ⟨rfl, rfl, rfl⟩

/-- If the four finite vertices of a Schwarz--Christoffel polygon are the corners `c + L`,
`c + L + M * I`, `c + M * I`, `c` of a closed rectangle, in this order, and the vertex at infinity
lies in that rectangle, then the closed convex hull of the polygon boundary is the rectangle. -/
private lemma closedConvexHull_schwarzChristoffelPolygon_boundary_rectangle
    {a e : Fin 4 → ℝ} {z₀ : UpperHalfPlane} {c : ℂ} {L M : ℝ} (hL : 0 ≤ L) (hM : 0 ≤ M)
    (h₀ : schwarzChristoffelVertex a e z₀ 0 = c + L)
    (h₁ : schwarzChristoffelVertex a e z₀ 1 = c + L + M * Complex.I)
    (h₂ : schwarzChristoffelVertex a e z₀ 2 = c + M * Complex.I)
    (h₃ : schwarzChristoffelVertex a e z₀ 3 = c)
    (hv : schwarzChristoffelVertexAtInfinity a e z₀ ∈
      Icc c.re (c.re + L) ×ℂ Icc c.im (c.im + M)) :
    closedConvexHull ℝ ((schwarzChristoffelPolygon a e z₀).boundary ℝ) =
      Icc c.re (c.re + L) ×ℂ Icc c.im (c.im + M) := by
  set w := schwarzChristoffelVertex a e z₀
  set v := schwarzChristoffelVertexAtInfinity a e z₀
  have hB : (schwarzChristoffelPolygon a e z₀).boundary ℝ =
      (⋃ i : Fin 3, segment ℝ (w i.castSucc) (w i.succ)) ∪ segment ℝ (w 3) v ∪
        segment ℝ v (w 0) :=
    schwarzChristoffelPolygon_boundary a e z₀
  have hR : Icc c.re (c.re + L) ×ℂ Icc c.im (c.im + M) =
      convexHull ℝ {w 3, w 2, w 0, w 1} := by
    have h₂' : w 2 = c.re + (c + L + M * Complex.I).im * Complex.I := by
      apply Complex.ext <;> simp [h₂]
    have h₀' : w 0 = (c + L + M * Complex.I).re + c.im * Complex.I := by
      apply Complex.ext <;> simp [h₀]
    rw [h₃, h₂', h₀', h₁, ← rectangle_eq_convexHull, Rectangle]
    simp [uIcc_of_le, hL, hM]
  have hcorner :
      ({w 3, w 2, w 0, w 1} : Set ℂ) ⊆ (schwarzChristoffelPolygon a e z₀).boundary ℝ := by
    simp only [hB, insert_subset_iff, singleton_subset_iff, mem_union, mem_iUnion]
    exact ⟨Or.inl (Or.inr (left_mem_segment _ _ _)),
      Or.inl (Or.inl ⟨2, left_mem_segment _ _ _⟩), Or.inl (Or.inl ⟨0, left_mem_segment _ _ _⟩),
      Or.inl (Or.inl ⟨1, left_mem_segment _ _ _⟩)⟩
  have hconv : Convex ℝ (convexHull ℝ ({w 3, w 2, w 0, w 1} : Set ℂ)) := convex_convexHull ℝ _
  have hmem {z : ℂ} (hz : z ∈ ({w 3, w 2, w 0, w 1} : Set ℂ)) :
      z ∈ convexHull ℝ ({w 3, w 2, w 0, w 1} : Set ℂ) :=
    subset_convexHull ℝ _ hz
  have hvR : v ∈ convexHull ℝ ({w 3, w 2, w 0, w 1} : Set ℂ) := hR ▸ hv
  have hBR : (schwarzChristoffelPolygon a e z₀).boundary ℝ ⊆
      convexHull ℝ ({w 3, w 2, w 0, w 1} : Set ℂ) := by
    rw [hB]
    refine union_subset (union_subset (iUnion_subset fun i => ?_) ?_) ?_
    · fin_cases i <;> exact hconv.segment_subset (hmem (by simp)) (hmem (by simp))
    · exact hconv.segment_subset (hmem (by simp)) hvR
    · exact hconv.segment_subset hvR (hmem (by simp))
  rw [hR]
  refine (closedConvexHull_min hBR hconv ?_).antisymm
    ((convexHull_mono hcorner).trans convexHull_subset_closedConvexHull)
  rw [← hR]
  exact isClosed_Icc.reProdIm isClosed_Icc

/-- Before normalization, the Schwarz--Christoffel primitive of the rectangle data maps the upper
half-plane bijectively onto the open rectangle with lower left corner the vertex at `k⁻¹`, width
`2 k K` and height `k K'`. -/
private lemma bijOn_schwarzChristoffelPrimitive_rectangle (hk0 : 0 < k) (hk1 : k < 1)
    (z₀ : UpperHalfPlane) :
    BijOn (schwarzChristoffelPrimitive ![-k⁻¹, -1, 1, k⁻¹] (fun _ => -(1 / 2)) z₀)
      upperHalfPlaneSet
      (Ioo (schwarzChristoffelVertex ![-k⁻¹, -1, 1, k⁻¹] (fun _ => -(1 / 2)) z₀ 3).re
          ((schwarzChristoffelVertex ![-k⁻¹, -1, 1, k⁻¹] (fun _ => -(1 / 2)) z₀ 3).re +
            2 * k * ∫ x in (0 : ℝ)..1, 1 / √((1 - x ^ 2) * (1 - k ^ 2 * x ^ 2))) ×ℂ
        Ioo (schwarzChristoffelVertex ![-k⁻¹, -1, 1, k⁻¹] (fun _ => -(1 / 2)) z₀ 3).im
          ((schwarzChristoffelVertex ![-k⁻¹, -1, 1, k⁻¹] (fun _ => -(1 / 2)) z₀ 3).im +
            k * ∫ x in (1 : ℝ)..k⁻¹, 1 / √((x ^ 2 - 1) * (1 - k ^ 2 * x ^ 2)))) := by
  have ha := strictMono_rectanglePrevertex hk0 hk1
  obtain ⟨h₀₁, h₁₂, h₂₃⟩ := schwarzChristoffelVertex_succ_sub_rectangle hk0 hk1 z₀
  obtain ⟨hL₀, hL₁, -⟩ := schwarzChristoffelSideIntegral_rectangle hk0 hk1
  set a : Fin 4 → ℝ := ![-k⁻¹, -1, 1, k⁻¹]
  set e : Fin 4 → ℝ := fun _ => -(1 / 2)
  set K := ∫ x in (0 : ℝ)..1, 1 / √((1 - x ^ 2) * (1 - k ^ 2 * x ^ 2))
  set K' := ∫ x in (1 : ℝ)..k⁻¹, 1 / √((x ^ 2 - 1) * (1 - k ^ 2 * x ^ 2))
  set w := schwarzChristoffelVertex a e z₀
  have he : ∀ i, e i ∈ Ioo (-1 : ℝ) 0 := fun _ => by norm_num [e]
  have hsum : ∑ i, e i = -2 := by norm_num [e]
  have hK : 0 < 2 * k * K := hL₁ ▸
    schwarzChristoffelSideIntegral_pos a e ha 1 (by norm_num [e]) (by norm_num [e])
  have hK' : 0 < k * K' := hL₀ ▸
    schwarzChristoffelSideIntegral_pos a e ha 0 (by norm_num [e]) (by norm_num [e])
  -- the finite vertices are the corners of the rectangle with lower left corner `w 3`
  have hw₂ : w 2 = w 3 + ((k * K' : ℝ) : ℂ) * Complex.I := by linear_combination -h₂₃
  have hw₁ : w 1 = w 3 + ((2 * k * K : ℝ) : ℂ) + ((k * K' : ℝ) : ℂ) * Complex.I := by
    linear_combination -h₂₃ - h₁₂
  have hw₀ : w 0 = w 3 + ((2 * k * K : ℝ) : ℂ) := by linear_combination -h₂₃ - h₁₂ - h₀₁
  -- and the vertex at infinity lies on its bottom side
  have hv : schwarzChristoffelVertexAtInfinity a e z₀ ∈
      Icc (w 3).re ((w 3).re + 2 * k * K) ×ℂ Icc (w 3).im ((w 3).im + k * K') := by
    obtain ⟨hl, hr⟩ := schwarzChristoffelVertex_last_lt_vertexAtInfinity_lt_vertex_zero a e z₀ ha
      (fun i => (he i).1) hsum
    rw [Complex.lt_def] at hl hr
    have hw₀re : (w 0).re = (w 3).re + 2 * k * K := by simp [hw₀]
    have hvim : (w 3).im = (schwarzChristoffelVertexAtInfinity a e z₀).im := hl.2
    exact ⟨⟨hl.1.le, (hw₀re ▸ hr.1).le⟩, hvim.le, by rw [← hvim]; linarith⟩
  have hF := bijOn_schwarzChristoffelPrimitive_interior_closedConvexHull a e z₀ ha he hsum
  rwa [closedConvexHull_schwarzChristoffelPolygon_boundary_rectangle hK.le hK'.le hw₀ hw₁ hw₂ rfl
    hv, interior_reProdIm, interior_Icc, interior_Icc] at hF

/-- **The Schwarz--Christoffel map onto a rectangle.** For `0 < k < 1`, let `F` be the normalized
Schwarz--Christoffel primitive with prevertices `-k⁻¹`, `-1`, `1`, `k⁻¹`, each of exponent `-1 / 2`,
and let `m` be the midpoint of its vertices at `-1` and `1`. Then `z ↦ (m - F z) / k` maps the
upper half-plane bijectively onto the open rectangle `(-K, K) × (0, K')`, where
`K = ∫₀¹ dx / √((1 - x²)(1 - k²x²))` is the complete elliptic integral of the first kind and
`K' = ∫₁^{1/k} dx / √((x² - 1)(1 - k²x²))`. -/
theorem bijOn_sub_schwarzChristoffelPrimitive_div_rectangle (hk0 : 0 < k) (hk1 : k < 1)
    (z₀ : UpperHalfPlane) :
    BijOn (fun z => ((schwarzChristoffelVertex ![-k⁻¹, -1, 1, k⁻¹] (fun _ => -(1 / 2)) z₀ 1 +
          schwarzChristoffelVertex ![-k⁻¹, -1, 1, k⁻¹] (fun _ => -(1 / 2)) z₀ 2) / 2 -
          schwarzChristoffelPrimitive ![-k⁻¹, -1, 1, k⁻¹] (fun _ => -(1 / 2)) z₀ z) / k)
      upperHalfPlaneSet
      (Ioo (-∫ x in (0 : ℝ)..1, 1 / √((1 - x ^ 2) * (1 - k ^ 2 * x ^ 2)))
          (∫ x in (0 : ℝ)..1, 1 / √((1 - x ^ 2) * (1 - k ^ 2 * x ^ 2))) ×ℂ
        Ioo 0 (∫ x in (1 : ℝ)..k⁻¹, 1 / √((x ^ 2 - 1) * (1 - k ^ 2 * x ^ 2)))) := by
  obtain ⟨-, h₁₂, h₂₃⟩ := schwarzChristoffelVertex_succ_sub_rectangle hk0 hk1 z₀
  set K := ∫ x in (0 : ℝ)..1, 1 / √((1 - x ^ 2) * (1 - k ^ 2 * x ^ 2))
  set K' := ∫ x in (1 : ℝ)..k⁻¹, 1 / √((x ^ 2 - 1) * (1 - k ^ 2 * x ^ 2))
  set w := schwarzChristoffelVertex ![-k⁻¹, -1, 1, k⁻¹] (fun _ => -(1 / 2)) z₀
  -- the midpoint of the top side, relative to the lower left corner `w 3`
  have hm : (w 1 + w 2) / 2 = w 3 + ((k * K : ℝ) : ℂ) + ((k * K' : ℝ) : ℂ) * Complex.I := by
    push_cast at h₁₂ h₂₃ ⊢
    linear_combination -h₂₃ - h₁₂ / 2
  have hk : (k : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hk0.ne'
  -- the affine map `u ↦ (m - u) / k` carries the rectangle of
  -- `bijOn_schwarzChristoffelPrimitive_rectangle` onto `(-K, K) × (0, K')`
  refine BijOn.comp (g := fun u => ((w 1 + w 2) / 2 - u) / k)
    ⟨fun u hu => ?_, fun u _ u' _ h => sub_right_inj.mp ((div_left_inj' hk).mp h),
      fun t ht => ⟨(w 1 + w 2) / 2 - k * t, ?_, by simp only; field_simp; ring⟩⟩
    (bijOn_schwarzChristoffelPrimitive_rectangle hk0 hk1 z₀)
  · simp only [mem_reProdIm, mem_Ioo, hm, Complex.div_ofReal_re, Complex.div_ofReal_im,
      Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im] at hu ⊢
    rw [lt_div_iff₀ hk0, div_lt_iff₀ hk0, lt_div_iff₀ hk0, div_lt_iff₀ hk0]
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> nlinarith
  · simp only [mem_reProdIm, mem_Ioo, hm, Complex.sub_re, Complex.sub_im, Complex.add_re,
      Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, Complex.mul_im,
      Complex.I_re, Complex.I_im] at ht ⊢
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> nlinarith

end TauCeti
