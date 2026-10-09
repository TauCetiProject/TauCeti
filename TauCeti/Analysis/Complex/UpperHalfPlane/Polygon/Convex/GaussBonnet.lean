/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.UpperHalfPlane.Polygon.Convex
import TauCeti.Algebra.BigOperators.Intervals
import TauCeti.Analysis.Complex.UpperHalfPlane.Polygon.Convex.NormalForm
import TauCeti.Analysis.Complex.UpperHalfPlane.Polygon.GaussBonnet
import TauCeti.Data.Fin.Basic

/-!
# The Gauss–Bonnet formula for convex hyperbolic polygons with ideal vertices

The invariant area of a convex hyperbolic polygon with `n` vertices in `ℍ ∪ ∂ℍ` and interior
angles `α₀, …, αₙ₋₁` (with `αᵢ = 0` at an ideal vertex) is `(n - 2) π - (α₀ + ⋯ + αₙ₋₁)`
(`ConvexPolygon.volume_carrier`). In particular the area is finite
(`ConvexPolygon.volume_carrier_ne_top`), the angle sum is at most `(n - 2) π`
(`ConvexPolygon.sum_interiorAngle_le`), an ideal polygon has area `(n - 2) π`, and an ideal
triangle has area `π`.

A polygon without ideal vertices is a compact convex polygon, whose area is
`CompactConvexPolygon.volume_carrier`. A polygon with an ideal vertex has the area and angle sum
of a convex polygon whose `vertex 0` is `∞` (`ConvexPolygon.exists_vertex_zero_eq_infty`). For
such a polygon the area of the part of the carrier to the left of the vertical through `vertex k`
is the sum of the areas of the first `k - 1` triangles of the fan from `∞`
(`ConvexPolygon.volume_carrier_inter_re_le_of_vertex_zero`), and the angle sum is the sum of
the finite angles of these triangles (`ConvexPolygon.sum_interiorAngle_eq_of_vertex_zero`). In
these statements the vertices are indexed by natural numbers `k`, cast to `Fin n` under
`open Fin.NatCast`.

## Main results

* `ConvexPolygon.volume_carrier`: **Gauss–Bonnet for convex polygons with ideal vertices**.
* `ConvexPolygon.volume_carrier_ne_top`, `ConvexPolygon.toReal_volume_carrier`: the area is
  finite, equal to the angular defect.
* `ConvexPolygon.sum_interiorAngle_le`: the angular defect is nonnegative.
* `ConvexPolygon.volume_carrier_of_forall_eq_inr`: an ideal polygon has area `(n - 2) π`;
  `ConvexPolygon.volume_carrier_three_of_forall_eq_inr`: an ideal triangle has area `π`.
* `ConvexPolygon.volume_carrier_three_of_vertex_one_of_vertex_two`: a triangle with two ideal
  vertices has area `π - α`, for its angle `α` at the third vertex.

## Source

Walkden, *Hyperbolic geometry* (MATH32051 lecture notes, Manchester 2019), Theorem 7.2.1 and
Remark 2 after it (an ideal triangle has area `π`), Theorem 7.2.2 and its proof ("Cut up P into
triangles. Apply Theorem 7.2.1 to each triangle and then sum the areas."), with ideal vertices as
in §7.1; Katok, *Fuchsian groups, geodesic flows…*, Clay Math. Proc. 10 (2010), Theorem 5.4.
-/

public section

noncomputable section

open MeasureTheory UpperHalfPlane
open scoped MatrixGroups Pointwise OnePoint Real Fin.NatCast

namespace TauCeti.UpperHalfPlane

namespace ConvexPolygon

variable {n : ℕ} [NeZero n] (P : ConvexPolygon n)

/-! ### A polygon with an ideal vertex at `∞` -/

/-- If `vertex 0` is `∞`, the angle sum is the sum of the finite angles of the triangles of the
fan from `∞`, indexed by the casts to `Fin n` of the natural numbers `1 ≤ k < n - 1`. -/
theorem sum_interiorAngle_eq_of_vertex_zero (h₀ : P.vertex 0 = .inr ∞) :
    ∑ i, P.interiorAngle i = ∑ k ∈ Finset.Ico 1 (n - 1),
      (vertexAngle (P.vertex k) (.inr ∞) (P.vertex (k + 1)) +
        vertexAngle (P.vertex (k + 1)) (P.vertex k) (.inr ∞)) := by
  obtain ⟨N, rfl⟩ : ∃ N, n = N + 3 := ⟨n - 3, by have := P.three_le; omega⟩
  have hsub {k : ℕ} (hk : k ≠ 0) : (k : Fin (N + 3)) - 1 = ((k - 1 : ℕ) : Fin (N + 3)) := by
    rw [sub_eq_iff_eq_add, ← Nat.cast_add_one, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 hk)]
  have hN : N + 3 - 1 = N + 2 := by omega
  have hsum : ∑ i, P.interiorAngle i =
      ∑ k ∈ Finset.range (N + 3), P.interiorAngle (k : Fin (N + 3)) := by
    rw [← Fin.sum_univ_eq_sum_range]
    simp only [Fin.cast_val_eq_self]
  rw [hsum, Finset.sum_range_eq_sum_Ico_add
    (β := fun k : ℕ ↦ vertexAngle (P.vertex k) (.inr ∞) (P.vertex (k + 1)))
    (γ := fun k : ℕ ↦ vertexAngle (P.vertex k) (P.vertex (k - 1)) (.inr ∞))]
  · rw [hN]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [Nat.cast_add_one, add_sub_cancel_right]
  · rw [Nat.cast_zero]
    exact P.interiorAngle_eq_zero_of_vertex_eq_inr h₀
  · -- at `vertex 1`, the previous vertex is `∞`
    rw [interiorAngle_def, Nat.cast_one, sub_self, h₀]
  · intro k hk
    obtain ⟨hk₁, hk₂⟩ := Finset.mem_Ico.1 hk
    exact P.interiorAngle_eq_add_of_vertex_zero h₀ (Fin.natCast_ne_zero (by omega) (by omega))
      (by rw [hsub (by omega)]; exact Fin.natCast_ne_zero (by omega) (by omega))
      (by rw [← Nat.cast_add_one]; exact Fin.natCast_ne_zero (by omega) (by omega))
  · -- at `vertex (N + 2)`, the next vertex is `∞`
    rw [interiorAngle_def, ← Nat.cast_add_one, Fin.natCast_self, h₀]

/-- The area of a triangle of the fan from `∞`, for an index cast from `ℕ`. -/
private theorem volume_carrier_inter_strip_natCast (h₀ : P.vertex 0 = .inr ∞) {k : ℕ}
    (hk : k ≠ 0) (hkn : k + 1 < n) :
    volume (P.carrier ∩ {z | (toComplex (P.vertex k)).re ≤ z.re ∧
        z.re ≤ (toComplex (P.vertex (k + 1))).re}) =
      ENNReal.ofReal (π - vertexAngle (P.vertex k) (.inr ∞) (P.vertex (k + 1)) -
        vertexAngle (P.vertex (k + 1)) (P.vertex k) (.inr ∞)) :=
  P.volume_carrier_inter_strip h₀ (Fin.natCast_ne_zero hk (by omega))
    (by rw [← Nat.cast_add_one]; exact Fin.natCast_ne_zero k.succ_ne_zero hkn)

/-- The two finite angles of a triangle of the fan from `∞`, for an index cast from `ℕ`, sum to
at most `π`. -/
private theorem vertexAngle_add_vertexAngle_le_pi_natCast (h₀ : P.vertex 0 = .inr ∞) {k : ℕ}
    (hk : k ≠ 0) (hkn : k + 1 < n) :
    vertexAngle (P.vertex k) (.inr ∞) (P.vertex (k + 1)) +
      vertexAngle (P.vertex (k + 1)) (P.vertex k) (.inr ∞) ≤ π :=
  P.vertexAngle_add_vertexAngle_le_pi_of_vertex_zero h₀ (Fin.natCast_ne_zero hk (by omega))
    (by rw [← Nat.cast_add_one]; exact Fin.natCast_ne_zero k.succ_ne_zero hkn)

/-- If `vertex 0` is `∞`, the part of the carrier to the left of the vertical through
`vertex (k + 1)` is cut by the vertical through `vertex k` into two parts whose areas add up. -/
private theorem volume_carrier_inter_re_le_add_one (h₀ : P.vertex 0 = .inr ∞) {k : ℕ}
    (hk : k ≠ 0) (hkn : k + 1 < n) :
    volume (P.carrier ∩ {z | z.re ≤ (toComplex (P.vertex (k + 1))).re}) =
      volume (P.carrier ∩ {z | z.re ≤ (toComplex (P.vertex k)).re}) +
        volume (P.carrier ∩ {z | (toComplex (P.vertex k)).re ≤ z.re ∧
          z.re ≤ (toComplex (P.vertex (k + 1))).re}) := by
  set x := (toComplex (P.vertex k)).re
  set x' := (toComplex (P.vertex (k + 1))).re
  have hlt : x < x' := P.re_toComplex_vertex_lt_of_vertex_zero h₀
    (Fin.natCast_ne_zero hk (by omega))
    (by rw [← Nat.cast_add_one]; exact Fin.natCast_ne_zero k.succ_ne_zero hkn)
  have hsplit : P.carrier ∩ {z | z.re ≤ x'} = P.carrier ∩ {z | z.re ≤ x} ∪
      P.carrier ∩ {z | x ≤ z.re ∧ z.re ≤ x'} := by
    ext z
    simp only [Set.mem_inter_iff, Set.mem_union, Set.mem_ofPred_eq]
    refine ⟨fun ⟨hz, hz'⟩ ↦ (le_total z.re x).imp (⟨hz, ·⟩) (⟨hz, ·, hz'⟩), ?_⟩
    rintro (⟨hz, h⟩ | ⟨hz, -, h⟩)
    exacts [⟨hz, h.trans hlt.le⟩, ⟨hz, h⟩]
  have hmeas : MeasurableSet (P.carrier ∩ {z | x ≤ z.re ∧ z.re ≤ x'}) :=
    P.measurableSet_carrier.inter
      ((measurableSet_le measurable_const UpperHalfPlane.continuous_re.measurable).inter
        (measurableSet_le UpperHalfPlane.continuous_re.measurable measurable_const))
  -- the two parts meet only along the vertical through `vertex k`
  have hdisj : AEDisjoint volume (P.carrier ∩ {z | z.re ≤ x})
      (P.carrier ∩ {z | x ≤ z.re ∧ z.re ≤ x'}) :=
    measure_mono_null (fun z hz ↦ le_antisymm hz.1.2 hz.2.2.1) (volume_setOf_re_eq x)
  rw [hsplit, measure_union₀ hmeas.nullMeasurableSet hdisj]

/-- If `vertex 0` is `∞`, the area of the part of the carrier to the left of the vertical through
`vertex k`, for `0 < k < n`, is the sum of the areas `π - αⱼ - βⱼ` of the first `k - 1` triangles
of the fan from `∞`, where `αⱼ`, `βⱼ` are the angles of the `j`-th triangle at `vertex j` and
`vertex (j + 1)`. -/
theorem volume_carrier_inter_re_le_of_vertex_zero (h₀ : P.vertex 0 = .inr ∞) {k : ℕ}
    (hk : k ≠ 0) (hkn : k < n) :
    volume (P.carrier ∩ {z | z.re ≤ (toComplex (P.vertex k)).re}) =
      ENNReal.ofReal (∑ j ∈ Finset.Ico 1 k,
        (π - vertexAngle (P.vertex j) (.inr ∞) (P.vertex (j + 1)) -
          vertexAngle (P.vertex (j + 1)) (P.vertex j) (.inr ∞))) := by
  induction k, Nat.one_le_iff_ne_zero.2 hk using Nat.le_induction with
  | base =>
    -- the part of the carrier to the left of its leftmost vertical is null
    rw [Finset.Ico_self, Finset.sum_empty, ENNReal.ofReal_zero, Nat.cast_one]
    exact measure_mono_null
      (fun z hz ↦ le_antisymm hz.2 (P.re_toComplex_vertex_one_le_of_mem_carrier h₀ hz.1))
      (volume_setOf_re_eq _)
  | succ k hk₁ ih =>
    have hk₀ : k ≠ 0 := by omega
    have hnonneg : 0 ≤ ∑ j ∈ Finset.Ico 1 k,
        (π - vertexAngle (P.vertex j) (.inr ∞) (P.vertex (j + 1)) -
          vertexAngle (P.vertex (j + 1)) (P.vertex j) (.inr ∞)) :=
      Finset.sum_nonneg fun j hj ↦ by
        have := P.vertexAngle_add_vertexAngle_le_pi_natCast h₀
          (Nat.one_le_iff_ne_zero.1 (Finset.mem_Ico.1 hj).1)
          (by have := (Finset.mem_Ico.1 hj).2; omega)
        linarith
    rw [Nat.cast_add_one, P.volume_carrier_inter_re_le_add_one h₀ hk₀ hkn, ih hk₀ (by omega),
      P.volume_carrier_inter_strip_natCast h₀ hk₀ hkn, ← ENNReal.ofReal_add hnonneg
        (by linarith [P.vertexAngle_add_vertexAngle_le_pi_natCast h₀ hk₀ hkn]),
      Finset.sum_Ico_succ_top hk₁]

/-- The Gauss–Bonnet formula for a convex polygon whose `vertex 0` is `∞`. -/
theorem volume_carrier_of_vertex_zero (h₀ : P.vertex 0 = .inr ∞) :
    volume P.carrier = ENNReal.ofReal ((n - 2) * π - ∑ i, P.interiorAngle i) := by
  have hn := P.three_le
  -- the carrier lies to the left of the vertical through `vertex (n - 1) = vertex (-1)`
  have hneg : ((n - 1 : ℕ) : Fin n) = -1 := eq_neg_of_add_eq_zero_left (by
    rw [← Nat.cast_add_one, Nat.sub_add_cancel NeZero.one_le, Fin.natCast_self])
  have hcarrier : P.carrier =
      P.carrier ∩ {z | z.re ≤ (toComplex (P.vertex ((n - 1 : ℕ) : Fin n))).re} := by
    rw [hneg]
    exact (Set.inter_eq_left.2 fun z hz ↦
      P.re_le_re_toComplex_vertex_neg_one_of_mem_carrier h₀ hz).symm
  rw [hcarrier, P.volume_carrier_inter_re_le_of_vertex_zero h₀ (by omega) (by omega),
    P.sum_interiorAngle_eq_of_vertex_zero h₀]
  simp_rw [sub_sub]
  rw [Finset.sum_sub_distrib, Finset.sum_Ico_one_sub_one_const (by omega) π]

/-- The angular defect of a convex polygon whose `vertex 0` is `∞` is nonnegative. -/
theorem sum_interiorAngle_le_of_vertex_zero (h₀ : P.vertex 0 = .inr ∞) :
    ∑ i, P.interiorAngle i ≤ (n - 2) * π := by
  have hn := P.three_le
  have hle := Finset.sum_le_sum fun k (hk : k ∈ Finset.Ico 1 (n - 1)) ↦
    P.vertexAngle_add_vertexAngle_le_pi_natCast h₀
      (Nat.one_le_iff_ne_zero.1 (Finset.mem_Ico.1 hk).1)
      (by have := (Finset.mem_Ico.1 hk).2; omega)
  rw [P.sum_interiorAngle_eq_of_vertex_zero h₀]
  exact hle.trans_eq (Finset.sum_Ico_one_sub_one_const (by omega) π)

/-! ### Gauss–Bonnet -/

/-- **The Gauss–Bonnet formula for convex hyperbolic polygons with ideal vertices**: the area of
a convex polygon with `n` vertices in `ℍ ∪ ∂ℍ` is `(n - 2) π` minus the sum of its interior
angles, the angle at an ideal vertex being `0`.
Source: Walkden, *Hyperbolic geometry* (MATH32051), Theorem 7.2.2 and §7.1. -/
theorem volume_carrier :
    volume P.carrier = ENNReal.ofReal ((n - 2) * π - ∑ i, P.interiorAngle i) := by
  by_cases h : ∀ i, ∃ z : ℍ, P.vertex i = .inl z
  · obtain ⟨Q, rfl⟩ := P.exists_eq_toConvexPolygon h
    simp_rw [CompactConvexPolygon.carrier_toConvexPolygon,
      CompactConvexPolygon.interiorAngle_toConvexPolygon]
    exact Q.volume_carrier
  · obtain ⟨Q, hQ₀, hvol, hsum⟩ := P.exists_vertex_zero_eq_infty_of_not_forall_eq_inl h
    rw [← hvol, ← hsum]
    exact Q.volume_carrier_of_vertex_zero hQ₀

/-- The angular defect of a convex polygon is nonnegative: the sum of its interior angles is at
most `(n - 2) π`. -/
theorem sum_interiorAngle_le : ∑ i, P.interiorAngle i ≤ (n - 2) * π := by
  by_cases h : ∀ i, ∃ z : ℍ, P.vertex i = .inl z
  · obtain ⟨Q, rfl⟩ := P.exists_eq_toConvexPolygon h
    simp_rw [CompactConvexPolygon.interiorAngle_toConvexPolygon]
    exact Q.sum_interiorAngle_le
  · obtain ⟨Q, hQ₀, -, hsum⟩ := P.exists_vertex_zero_eq_infty_of_not_forall_eq_inl h
    rw [← hsum]
    exact Q.sum_interiorAngle_le_of_vertex_zero hQ₀

/-- A convex polygon has finite area. -/
theorem volume_carrier_ne_top : volume P.carrier ≠ ⊤ := by
  rw [volume_carrier]
  exact ENNReal.ofReal_ne_top

/-- The area of a convex polygon, as a real number, is its angular defect. -/
theorem toReal_volume_carrier :
    (volume P.carrier).toReal = (n - 2) * π - ∑ i, P.interiorAngle i := by
  rw [volume_carrier, ENNReal.toReal_ofReal (sub_nonneg.2 P.sum_interiorAngle_le)]

/-- An ideal polygon, with all `n` vertices on `∂ℍ`, has area `(n - 2) π`. -/
theorem volume_carrier_of_forall_eq_inr (h : ∀ i, ∃ ξ : OnePoint ℝ, P.vertex i = .inr ξ) :
    volume P.carrier = ENNReal.ofReal ((n - 2) * π) := by
  rw [volume_carrier, Finset.sum_eq_zero fun i _ ↦
    P.interiorAngle_eq_zero_of_vertex_eq_inr (h i).choose_spec, sub_zero]

/-- **An ideal triangle has area `π`.**
Source: Walkden, *Hyperbolic geometry* (MATH32051), Remark 2 after Theorem 7.2.1. -/
theorem volume_carrier_three_of_forall_eq_inr (P : ConvexPolygon 3)
    (h : ∀ i, ∃ ξ : OnePoint ℝ, P.vertex i = .inr ξ) :
    volume P.carrier = ENNReal.ofReal π := by
  rw [P.volume_carrier_of_forall_eq_inr h]
  norm_num

/-- A triangle with two ideal vertices has area `π - α`, for its angle `α` at the third
vertex. -/
theorem volume_carrier_three_of_vertex_one_of_vertex_two (P : ConvexPolygon 3) {ξ η : OnePoint ℝ}
    (h₁ : P.vertex 1 = .inr ξ) (h₂ : P.vertex 2 = .inr η) :
    volume P.carrier = ENNReal.ofReal (π - P.interiorAngle 0) := by
  rw [volume_carrier, Fin.sum_univ_three, P.interiorAngle_eq_zero_of_vertex_eq_inr h₁,
    P.interiorAngle_eq_zero_of_vertex_eq_inr h₂]
  norm_num

end ConvexPolygon

end TauCeti.UpperHalfPlane
