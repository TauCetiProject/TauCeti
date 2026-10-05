/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.UpperHalfPlane.IdealRegion
public import TauCeti.Analysis.Complex.UpperHalfPlane.Polygon.Convex
import TauCeti.Analysis.Complex.NormSq
import TauCeti.Data.Fin.Basic

/-!
# A convex polygon with an ideal vertex at `∞`

Let `P` be a convex polygon whose vertex `0` is the ideal point `∞`. Its sides from `∞` to
`vertex 1` and from `vertex (-1)` back to `∞` are vertical lines, and every other side runs along
a semicircle with `∞` on its left, from left to right. Writing `xᵢ` for the real part of
`toComplex (vertex i)`, which is the real coordinate of `vertex i` for `i ≠ 0` (for `i = 0` it is
the junk value `0`), the real parts `x₁ < ⋯ < xₙ₋₁` increase strictly and the carrier lies
between the verticals through `vertex 1` and `vertex (-1)`. Between the verticals through
`vertex i` and `vertex (i + 1)`, for `i ≠ 0, -1`, the carrier is the hyperbolic triangle with
vertices `∞`, `vertex i` and `vertex (i + 1)`: the region above the semicircle of the side `i`.
These triangles form the fan of diagonals from the ideal vertex `∞`, and the interior angle of
`P` at each vertex other than `∞`, `vertex 1` and `vertex (-1)` is the sum of the angles of the
two triangles of the fan meeting there.

## Main results

* `ConvexPolygon.sideForm_sideGeodesic_zero_of_vertex_zero`,
  `ConvexPolygon.sideForm_sideGeodesic_neg_one_of_vertex_zero`: the two sides at `∞` lie on
  vertical lines.
* `ConvexPolygon.exists_sideForm_sideGeodesic_eq_of_vertex_zero`,
  `ConvexPolygon.re_toComplex_vertex_lt_of_vertex_zero`: every other side is a semicircle with
  `∞` on its left, running from left to right.
* `ConvexPolygon.re_toComplex_vertex_lt_of_lt`: the real parts of `vertex 1, …, vertex (n - 1)`
  increase strictly.
* `ConvexPolygon.re_toComplex_vertex_one_le_of_mem_carrier`,
  `ConvexPolygon.re_le_re_toComplex_vertex_neg_one_of_mem_carrier`: the carrier lies between the
  verticals through `vertex 1` and `vertex (-1)`.
* `ConvexPolygon.exists_carrier_inter_strip_eq`: between the verticals through `vertex i` and
  `vertex (i + 1)`, the carrier is the region above the semicircle of the side `i`
  (`idealRegionAbove`).
* `ConvexPolygon.volume_carrier_inter_strip`: the area of this triangle is `π` minus its angles at
  `vertex i` and `vertex (i + 1)`, which sum to at most `π`
  (`ConvexPolygon.vertexAngle_add_vertexAngle_le_pi_of_vertex_zero`).
* `ConvexPolygon.interiorAngle_eq_add_of_vertex_zero`: the upward vertical splits the interior
  angle at a vertex other than `∞`, `vertex 1` and `vertex (-1)` into the angles of the two
  adjacent triangles.

## Source

Walkden, *Hyperbolic geometry* (MATH32051 lecture notes, Manchester 2019), the proof of
Theorem 7.2.1 in the case of a vertex on `∂ℍ` (map it to `∞`; the other two vertices lie on a
semicircle; the area is `∫ₐᵇ dx / √(1 - x²) = π - (α + β)`), and Theorem 7.2.2 ("Cut up P into
triangles. Apply Theorem 7.2.1 to each triangle and then sum the areas."); Katok, *Fuchsian
groups, geodesic flows…*, Clay Math. Proc. 10 (2010), §5, proof of Theorem 5.4.
-/

public section

noncomputable section

open MeasureTheory UpperHalfPlane
open scoped MatrixGroups Pointwise OnePoint Real

namespace TauCeti.UpperHalfPlane

namespace ConvexPolygon

variable {n : ℕ} [NeZero n] (P : ConvexPolygon n)

/-! ### The sides -/

/-- If `vertex 0` is `∞`, no other vertex is. -/
theorem vertex_ne_inr_infty_of_vertex_zero (h₀ : P.vertex 0 = .inr ∞) {i : Fin n} (hi : i ≠ 0) :
    P.vertex i ≠ .inr ∞ := by
  rw [← h₀]
  exact P.vertex_injective.ne hi

/-- If `vertex 0` is `∞`, the side from `∞` down to `vertex 1` is the vertical line through
`vertex 1`, with side form `x₁ - Re z`. -/
theorem sideForm_sideGeodesic_zero_of_vertex_zero (h₀ : P.vertex 0 = .inr ∞) (z : ℂ) :
    sideForm (P.sideGeodesic 0) z = (toComplex (P.vertex 1)).re - z.re := by
  have hg := P.isGeodesicFromTo_sideGeodesic 0
  have h₁ := P.vertex_ne_vertex_add_one 0
  rw [h₀, zero_add] at hg h₁
  exact hg.sideForm_eq_of_inr_infty_left h₁.symm z

/-- If `vertex 0` is `∞`, the side from `vertex (-1)` up to `∞` is the vertical line through
`vertex (-1)`, with side form `Re z - xₙ₋₁`. -/
theorem sideForm_sideGeodesic_neg_one_of_vertex_zero (h₀ : P.vertex 0 = .inr ∞) (z : ℂ) :
    sideForm (P.sideGeodesic (-1)) z = z.re - (toComplex (P.vertex (-1))).re := by
  have hg := P.isGeodesicFromTo_sideGeodesic (-1)
  have h₁ := P.vertex_ne_vertex_add_one (-1)
  rw [neg_add_cancel, h₀] at hg h₁
  exact hg.sideForm_eq_of_inr_infty_right h₁ z

/-- If `vertex 0` is `∞`, it lies strictly to the left of every side not ending at it. -/
theorem infty_mem_boundaryLeftHalfPlane_sideGeodesic_of_vertex_zero (h₀ : P.vertex 0 = .inr ∞)
    {i : Fin n} (hi : i ≠ 0) (hi' : i + 1 ≠ 0) :
    (∞ : OnePoint ℝ) ∈ boundaryLeftHalfPlane (P.sideGeodesic i) := by
  have h := P.vertex_mem_extLeftHalfPlane_sideGeodesic hi.symm hi'.symm
  rwa [h₀, inr_mem_extLeftHalfPlane_iff] at h

/-- If `vertex 0` is `∞`, every side not ending at `∞` runs from left to right. -/
theorem re_toComplex_vertex_lt_of_vertex_zero (h₀ : P.vertex 0 = .inr ∞) {i : Fin n}
    (hi : i ≠ 0) (hi' : i + 1 ≠ 0) :
    (toComplex (P.vertex i)).re < (toComplex (P.vertex (i + 1))).re :=
  (P.isGeodesicFromTo_sideGeodesic i).re_toComplex_lt
    (P.infty_mem_boundaryLeftHalfPlane_sideGeodesic_of_vertex_zero h₀ hi hi')

/-- If `vertex 0` is `∞`, every side not ending at `∞` is a semicircle with `∞` on its left: its
side form is a positive multiple of `ρ² - |z - m|²` for its centre `m` and radius `ρ > 0`. -/
theorem exists_sideForm_sideGeodesic_eq_of_vertex_zero (h₀ : P.vertex 0 = .inr ∞) {i : Fin n}
    (hi : i ≠ 0) (hi' : i + 1 ≠ 0) :
    ∃ m ρ κ : ℝ, 0 < ρ ∧ 0 < κ ∧
      ∀ z : ℂ, sideForm (P.sideGeodesic i) z = κ * (ρ ^ 2 - Complex.normSq (z - m)) :=
  exists_sideForm_eq_of_infty_mem_boundaryLeftHalfPlane
    (P.infty_mem_boundaryLeftHalfPlane_sideGeodesic_of_vertex_zero h₀ hi hi')

open Fin.NatCast in
/-- If `vertex 0` is `∞`, the real parts of `vertex 1, …, vertex (n - 1)` increase strictly. -/
theorem re_toComplex_vertex_lt_of_lt (h₀ : P.vertex 0 = .inr ∞) {i j : Fin n} (hi : i ≠ 0)
    (hij : i < j) : (toComplex (P.vertex i)).re < (toComplex (P.vertex j)).re := by
  -- induction on the value of `j`, through the cast `ℕ → Fin n`
  have hi₀ : (i : ℕ) ≠ 0 := Fin.val_ne_zero_iff.2 hi
  have key {k : ℕ} (hik : (i : ℕ) < k) (hkn : k < n) :
      (toComplex (P.vertex i)).re < (toComplex (P.vertex (k : Fin n))).re := by
    induction k, hik using Nat.le_induction with
    | base =>
      have hi' := Fin.natCast_ne_zero (n := n) (Nat.succ_ne_zero _) hkn
      rw [Nat.cast_add_one, Fin.cast_val_eq_self] at hi' ⊢
      exact P.re_toComplex_vertex_lt_of_vertex_zero h₀ hi hi'
    | succ k hik ih =>
      have h := P.re_toComplex_vertex_lt_of_vertex_zero h₀ (i := (k : Fin n))
        (Fin.natCast_ne_zero (by omega) (by omega))
        (by rw [← Nat.cast_add_one]; exact Fin.natCast_ne_zero (by omega) hkn)
      rw [← Nat.cast_add_one] at h
      exact (ih (by omega)).trans h
  have h := key (Fin.lt_def.1 hij) j.isLt
  rwa [Fin.cast_val_eq_self] at h

/-- If `vertex 0` is `∞`, the real parts increase along `vertex 1, …, vertex (n - 1)`. -/
private theorem re_toComplex_vertex_le_of_le (h₀ : P.vertex 0 = .inr ∞) {i j : Fin n}
    (hi : i ≠ 0) (hij : i ≤ j) : (toComplex (P.vertex i)).re ≤ (toComplex (P.vertex j)).re := by
  rcases hij.eq_or_lt with rfl | h
  · exact le_rfl
  · exact (P.re_toComplex_vertex_lt_of_lt h₀ hi h).le

/-- If `vertex 0` is `∞`, `vertex 1` has the smallest real part among the other vertices. -/
private theorem re_toComplex_vertex_one_le (h₀ : P.vertex 0 = .inr ∞) {i : Fin n} (hi : i ≠ 0) :
    (toComplex (P.vertex 1)).re ≤ (toComplex (P.vertex i)).re := by
  have hn := P.three_le
  have h₁ : ((1 : Fin n) : ℕ) = 1 := by rw [Fin.val_one', Nat.mod_eq_of_lt (by omega)]
  have hi₀ : (i : ℕ) ≠ 0 := Fin.val_ne_zero_iff.2 hi
  exact P.re_toComplex_vertex_le_of_le h₀ (Fin.val_ne_zero_iff.1 (by omega))
    (Fin.le_def.2 (by omega))

open Fin.NatCast in
/-- If `vertex 0` is `∞`, `vertex (-1)` has the largest real part among the other vertices. -/
private theorem re_toComplex_vertex_le_neg_one (h₀ : P.vertex 0 = .inr ∞) {i : Fin n}
    (hi : i ≠ 0) : (toComplex (P.vertex i)).re ≤ (toComplex (P.vertex (-1))).re := by
  -- `-1` is the cast of `n - 1`, the largest element of `Fin n`
  have hneg : ((n - 1 : ℕ) : Fin n) = -1 := eq_neg_of_add_eq_zero_left (by
    rw [← Nat.cast_add_one, Nat.sub_add_cancel NeZero.one_le, Fin.natCast_self])
  refine P.re_toComplex_vertex_le_of_le h₀ hi ?_
  rw [← hneg, Fin.le_def, Fin.val_cast_of_lt (Nat.sub_lt (NeZero.pos n) one_pos)]
  exact Nat.le_sub_one_of_lt i.isLt

/-! ### The carrier -/

/-- If `vertex 0` is `∞`, the carrier lies to the right of the vertical through `vertex 1`. -/
theorem re_toComplex_vertex_one_le_of_mem_carrier (h₀ : P.vertex 0 = .inr ∞) {z : ℍ}
    (hz : z ∈ P.carrier) : (toComplex (P.vertex 1)).re ≤ z.re := by
  have h := (P.mem_carrier_iff_sideForm_nonpos z).1 hz 0
  rwa [P.sideForm_sideGeodesic_zero_of_vertex_zero h₀, sub_nonpos, coe_re] at h

/-- If `vertex 0` is `∞`, the carrier lies to the left of the vertical through `vertex (-1)`. -/
theorem re_le_re_toComplex_vertex_neg_one_of_mem_carrier (h₀ : P.vertex 0 = .inr ∞) {z : ℍ}
    (hz : z ∈ P.carrier) : z.re ≤ (toComplex (P.vertex (-1))).re := by
  have h := (P.mem_carrier_iff_sideForm_nonpos z).1 hz (-1)
  rwa [P.sideForm_sideGeodesic_neg_one_of_vertex_zero h₀, sub_nonpos, coe_re] at h

/-- If `vertex 0` is `∞`, the endpoints of an side `i` not ending at `∞` lie on its
semicircle. -/
private theorem normSq_sub_eq_of_sideForm_sideGeodesic_eq (h₀ : P.vertex 0 = .inr ∞) {i : Fin n}
    (hi : i ≠ 0) (hi' : i + 1 ≠ 0) {m ρ κ : ℝ} (hκ : κ ≠ 0)
    (hform : ∀ z : ℂ, sideForm (P.sideGeodesic i) z = κ * (ρ ^ 2 - Complex.normSq (z - m))) :
    Complex.normSq (toComplex (P.vertex i) - m) = ρ ^ 2 ∧
      Complex.normSq (toComplex (P.vertex (i + 1)) - m) = ρ ^ 2 := by
  have hon {w : ℂ} (hw : sideForm (P.sideGeodesic i) w = 0) : Complex.normSq (w - m) = ρ ^ 2 := by
    rw [hform, mul_eq_zero, sub_eq_zero] at hw
    exact (hw.resolve_left hκ).symm
  exact ⟨hon ((P.isGeodesicFromTo_sideGeodesic i).sideForm_toComplex_left
      (P.vertex_ne_inr_infty_of_vertex_zero h₀ hi)),
    hon ((P.isGeodesicFromTo_sideGeodesic i).sideForm_toComplex_right
      (P.vertex_ne_inr_infty_of_vertex_zero h₀ hi'))⟩

/-- If `vertex 0` is `∞`, a point between the verticals through `vertex i` and `vertex (i + 1)`
and above the semicircle through them lies in the closed left half-plane of every side. -/
private theorem sideForm_sideGeodesic_nonpos_of_mem_idealRegionAbove (h₀ : P.vertex 0 = .inr ∞)
    {i : Fin n} (hi : i ≠ 0) (hi' : i + 1 ≠ 0) {m ρ : ℝ}
    (hi₁ : Complex.normSq (toComplex (P.vertex i) - m) = ρ ^ 2)
    (hi₂ : Complex.normSq (toComplex (P.vertex (i + 1)) - m) = ρ ^ 2) {z : ℍ}
    (hz : z ∈ idealRegionAbove m ρ (toComplex (P.vertex i)).re (toComplex (P.vertex (i + 1))).re)
    (j : Fin n) : sideForm (P.sideGeodesic j) z ≤ 0 := by
  obtain ⟨hz₁, hz₂, hz⟩ := (mem_idealRegionAbove_iff _ _ _ _ z).1 hz
  by_cases hj : j = 0
  · rw [hj, P.sideForm_sideGeodesic_zero_of_vertex_zero h₀, sub_nonpos, coe_re]
    exact (P.re_toComplex_vertex_one_le h₀ hi).trans hz₁
  by_cases hj' : j + 1 = 0
  · rw [eq_neg_of_add_eq_zero_left hj', P.sideForm_sideGeodesic_neg_one_of_vertex_zero h₀,
      sub_nonpos, coe_re]
    exact hz₂.trans (P.re_toComplex_vertex_le_neg_one h₀ hi')
  -- the side `j` is a semicircle, and `vertex i`, `vertex (i + 1)` lie outside it
  obtain ⟨m', ρ', κ', -, hκ', hform'⟩ := P.exists_sideForm_sideGeodesic_eq_of_vertex_zero h₀ hj hj'
  have hout {k : Fin n} (hk : k ≠ 0) :
      ρ' ^ 2 ≤ Complex.normSq (toComplex (P.vertex k) - m') := by
    have h :=
      P.sideForm_sideGeodesic_toComplex_nonpos j k (P.vertex_ne_inr_infty_of_vertex_zero h₀ hk)
    rw [hform'] at h
    exact sub_nonpos.1 (nonpos_of_mul_nonpos_right h hκ')
  rw [hform']
  exact mul_nonpos_of_nonneg_of_nonpos hκ'.le (sub_nonpos.2
    (Complex.le_normSq_sub_of_le_normSq_sub hi₁ hi₂ (hout hi) (hout hi') hz hz₁ hz₂))

/-- **The triangles of the fan from `∞`.** If `vertex 0` is `∞`, then between the verticals
through `vertex i` and `vertex (i + 1)`, for an side `i` not ending at `∞`, the carrier is the
region above the semicircle of that side, of centre `m` and radius `ρ`, through both vertices.

The centre and radius are shared by the four conclusions, which are therefore stated together. -/
theorem exists_carrier_inter_strip_eq (h₀ : P.vertex 0 = .inr ∞) {i : Fin n} (hi : i ≠ 0)
    (hi' : i + 1 ≠ 0) :
    ∃ m ρ : ℝ, 0 < ρ ∧ Complex.normSq (toComplex (P.vertex i) - m) = ρ ^ 2 ∧
      Complex.normSq (toComplex (P.vertex (i + 1)) - m) = ρ ^ 2 ∧
      P.carrier ∩ {z | (toComplex (P.vertex i)).re ≤ z.re ∧
          z.re ≤ (toComplex (P.vertex (i + 1))).re} =
        idealRegionAbove m ρ (toComplex (P.vertex i)).re (toComplex (P.vertex (i + 1))).re := by
  obtain ⟨m, ρ, κ, hρ, hκ, hform⟩ := P.exists_sideForm_sideGeodesic_eq_of_vertex_zero h₀ hi hi'
  obtain ⟨hi₁, hi₂⟩ := P.normSq_sub_eq_of_sideForm_sideGeodesic_eq h₀ hi hi' hκ.ne' hform
  refine ⟨m, ρ, hρ, hi₁, hi₂, Set.Subset.antisymm ?_ fun z hz ↦ ⟨?_, ?_⟩⟩
  · rintro z ⟨hz, hz₁, hz₂⟩
    have h := (P.mem_carrier_iff_sideForm_nonpos z).1 hz i
    rw [hform] at h
    exact (mem_idealRegionAbove_iff _ _ _ _ z).2
      ⟨hz₁, hz₂, sub_nonpos.1 (nonpos_of_mul_nonpos_right h hκ)⟩
  · exact (P.mem_carrier_iff_sideForm_nonpos z).2
      (P.sideForm_sideGeodesic_nonpos_of_mem_idealRegionAbove h₀ hi hi' hi₁ hi₂ hz)
  · obtain ⟨hz₁, hz₂, -⟩ := (mem_idealRegionAbove_iff _ _ _ _ z).1 hz
    exact ⟨hz₁, hz₂⟩

/-- **Gauss–Bonnet for the triangles of the fan from `∞`.** If `vertex 0` is `∞`, the part of
the carrier between the verticals through `vertex i` and `vertex (i + 1)`, for an side `i` not
ending at `∞`, has area `π` minus the angles at `vertex i` and `vertex (i + 1)` of the triangle
with vertices `∞`, `vertex i`, `vertex (i + 1)`. That part of the carrier is this triangle by
`exists_carrier_inter_strip_eq`. -/
theorem volume_carrier_inter_strip (h₀ : P.vertex 0 = .inr ∞) {i : Fin n} (hi : i ≠ 0)
    (hi' : i + 1 ≠ 0) :
    volume (P.carrier ∩ {z | (toComplex (P.vertex i)).re ≤ z.re ∧
        z.re ≤ (toComplex (P.vertex (i + 1))).re}) =
      ENNReal.ofReal (π - vertexAngle (P.vertex i) (.inr ∞) (P.vertex (i + 1)) -
        vertexAngle (P.vertex (i + 1)) (P.vertex i) (.inr ∞)) := by
  obtain ⟨m, ρ, hρ, hi₁, hi₂, heq⟩ := P.exists_carrier_inter_strip_eq h₀ hi hi'
  have hv := P.vertex_ne_inr_infty_of_vertex_zero h₀ hi
  have hv' := P.vertex_ne_inr_infty_of_vertex_zero h₀ hi'
  have hlt := P.re_toComplex_vertex_lt_of_vertex_zero h₀ hi hi'
  rw [heq, volume_idealRegionAbove hρ (Complex.re_mem_Icc_of_normSq_sub_eq hρ.le hi₁).1 hlt.le
    (Complex.re_mem_Icc_of_normSq_sub_eq hρ.le hi₂).2,
    vertexAngle_infty_of_re_lt hρ hv hv' hi₁ hi₂ hlt,
    vertexAngle_infty_of_lt_re hρ hv hv' hi₁ hi₂ hlt]
  congr 1
  ring

/-- The two finite angles of a triangle of the fan from `∞` sum to at most `π`. -/
theorem vertexAngle_add_vertexAngle_le_pi_of_vertex_zero (h₀ : P.vertex 0 = .inr ∞) {i : Fin n}
    (hi : i ≠ 0) (hi' : i + 1 ≠ 0) :
    vertexAngle (P.vertex i) (.inr ∞) (P.vertex (i + 1)) +
      vertexAngle (P.vertex (i + 1)) (P.vertex i) (.inr ∞) ≤ π := by
  obtain ⟨m, ρ, hρ, hi₁, hi₂, -⟩ := P.exists_carrier_inter_strip_eq h₀ hi hi'
  have hv := P.vertex_ne_inr_infty_of_vertex_zero h₀ hi
  have hv' := P.vertex_ne_inr_infty_of_vertex_zero h₀ hi'
  have hlt := P.re_toComplex_vertex_lt_of_vertex_zero h₀ hi hi'
  have h := Real.arccos_le_arccos ((div_le_div_iff_of_pos_right hρ).2 (sub_le_sub_right hlt.le m))
  rw [vertexAngle_infty_of_re_lt hρ hv hv' hi₁ hi₂ hlt,
    vertexAngle_infty_of_lt_re hρ hv hv' hi₁ hi₂ hlt]
  linarith

/-! ### The interior angles -/

/-- If `vertex 0` is `∞`, the interior angle at a vertex other than `∞`, `vertex 1` and
`vertex (-1)` is split by the upward vertical into the angles of the two triangles of the fan from
`∞` meeting there. -/
theorem interiorAngle_eq_add_of_vertex_zero (h₀ : P.vertex 0 = .inr ∞) {i : Fin n} (hi : i ≠ 0)
    (hi₁ : i - 1 ≠ 0) (hi' : i + 1 ≠ 0) :
    P.interiorAngle i = vertexAngle (P.vertex i) (P.vertex (i - 1)) (.inr ∞) +
      vertexAngle (P.vertex i) (.inr ∞) (P.vertex (i + 1)) := by
  have hn := P.three_le
  have hi₁' : i - 1 + 1 ≠ 0 := by rwa [sub_add_cancel]
  -- the sides `i - 1` and `i` run along semicircles through `vertex i`
  obtain ⟨m₁, ρ₁, κ₁, -, hκ₁, hform₁⟩ :=
    P.exists_sideForm_sideGeodesic_eq_of_vertex_zero h₀ hi₁ hi₁'
  obtain ⟨hp₁, hA₁⟩ := P.normSq_sub_eq_of_sideForm_sideGeodesic_eq h₀ hi₁ hi₁' hκ₁.ne' hform₁
  obtain ⟨m₂, ρ₂, κ₂, -, hκ₂, hform₂⟩ := P.exists_sideForm_sideGeodesic_eq_of_vertex_zero h₀ hi hi'
  obtain ⟨hA₂, hq₂⟩ := P.normSq_sub_eq_of_sideForm_sideGeodesic_eq h₀ hi hi' hκ₂.ne' hform₂
  have hpA := P.re_toComplex_vertex_lt_of_vertex_zero h₀ hi₁ hi₁'
  have hAq := P.re_toComplex_vertex_lt_of_vertex_zero h₀ hi hi'
  -- `vertex (i - 1)` lies strictly to the left of the side `i`, outside its semicircle
  have hp₂ := P.sideForm_sideGeodesic_toComplex_neg (P.vertex_ne_inr_infty_of_vertex_zero h₀ hi₁)
    (sub_one_ne_self (by omega) i) (add_one_ne_sub_one hn i).symm
  rw [hform₂] at hp₂
  rw [sub_add_cancel] at hA₁ hpA
  rw [interiorAngle_def]
  cases hv : P.vertex i with
  | inr ξ => rw [vertexAngle_inr, vertexAngle_inr, vertexAngle_inr, add_zero]
  | inl A =>
    rw [hv, toComplex_inl] at hA₁ hA₂
    rw [hv, toComplex_inl, coe_re] at hpA hAq
    exact vertexAngle_eq_add_of_mem_circles (P.vertex_ne_inr_infty_of_vertex_zero h₀ hi₁)
      (P.vertex_ne_inr_infty_of_vertex_zero h₀ hi') hA₁ hp₁ hA₂ hq₂ hpA hAq
      (sub_neg.1 (neg_of_mul_neg_right hp₂ hκ₂.le))

end ConvexPolygon

end TauCeti.UpperHalfPlane
