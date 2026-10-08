/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.UpperHalfPlane.Polygon.Convex.VertexSector
public import TauCeti.Analysis.Complex.UpperHalfPlane.Polygon.SidePairing.Ideal
import Mathlib.Algebra.Order.ToIntervalMod
import Mathlib.Order.Interval.Set.Union
import TauCeti.Analysis.Complex.UpperHalfPlane.PSL.Translation

/-!
# The local tiling at a parabolic ideal vertex cycle

Let `ξ` be an ideal vertex of a side-paired convex polygon `P`. Following the side pairings from
`ξ` pulls `P` back to tiles `(partialCycleMap j m)⁻¹ • P`, all having `ξ` as an ideal vertex.
After moving `ξ` to `∞`, each tile agrees, above some height, with a vertical strip, and
consecutive strips share a vertical side
(`ConvexPolygon.SidePairing.inv_partialCycleMap_succ_smul_vertex_sub_one`). After a full cycle
the tile is moved by the cycle transformation, which fixes `ξ`.

If that cycle transformation is parabolic, it is conjugate to a translation, and the strips of one
cycle exactly fill a period of it. Its integer powers then move these finitely many tiles so that
they cover a whole horodisc at `ξ`. This is the local tessellation at an ideal vertex in
Poincaré's polygon theorem, whose hypothesis at ideal cycles is exactly that their
transformations are parabolic. Neither discreteness nor a fundamental-domain hypothesis is
assumed.

## Main result

* `ConvexPolygon.SidePairing.exists_setOf_lt_im_smul_subset_iUnion_smul_carrier`: at an ideal
  vertex with parabolic cycle transformation, the tiles of the cycle and their translates by
  powers of the cycle transformation cover a horodisc.

## References

Beardon, *The Geometry of Discrete Groups*, Chapter 9. Walkden, *Hyperbolic geometry*
(MATH32051 lecture notes, Manchester 2019), §§17.2 and 19–20 (parabolic cycles and the local
tessellation in Poincaré's polygon theorem). Maskit, *On Poincaré's theorem for fundamental
polygons*, Adv. Math. 7 (1971), 219–230.
-/

public section

open Matrix.ProjectiveSpecialLinearGroup Set UpperHalfPlane
open scoped MatrixGroups Pointwise OnePoint

namespace TauCeti.UpperHalfPlane.ConvexPolygon.SidePairing

variable {n : ℕ} [NeZero n] {P : ConvexPolygon n} (σ : P.SidePairing)

/-- **The local tiling at a parabolic ideal vertex.** Let `vertex j = ξ` be ideal with parabolic
cycle transformation `T`, and let `g` carry `ξ` to `∞`. Then above some height in the coordinate
`g`, every point lies in a tile `(T ^ k * (partialCycleMap j m)⁻¹) • P` with `k ∈ ℤ` and `m`
less than the cycle length. That is, these tiles cover a horodisc at `ξ`. -/
theorem exists_setOf_lt_im_smul_subset_iUnion_smul_carrier {j : Fin n} {ξ : OnePoint ℝ}
    (hj : P.vertex j = .inr ξ) (hpar : IsParabolic (σ.cycleMap j)) {g : PSL(2, ℝ)}
    (hg : g • ξ = ∞) :
    ∃ A : ℝ, {z : ℍ | A < (g • z).im} ⊆
      ⋃ k : ℤ, ⋃ m ∈ Finset.range (σ.cycleLength j),
        (σ.cycleMap j ^ k * (σ.partialCycleMap j m)⁻¹) • P.carrier := by
  -- in the coordinate `g`, the cycle transformation is a translation by some `x ≠ 0`
  have hfix : (g * σ.cycleMap j * g⁻¹) • (∞ : OnePoint ℝ) = ∞ := by
    rw [mul_smul, mul_smul, ← hg, inv_smul_smul, σ.cycleMap_smul_eq_self_of_vertex_eq_inr hj]
  obtain ⟨x, -, hx⟩ := (isParabolic_iff_exists_eq_upperRightHom hfix).1
    ((isParabolic_conj_iff g _).2 hpar)
  -- the `m`-th tile in the coordinate `g` has its vertex `next^[m] j` at `∞`, with sector the
  -- strip `u m ≤ Re ≤ v m`
  let Q (m : ℕ) : ConvexPolygon n := (g * (σ.partialCycleMap j m)⁻¹) • P
  have hQ (m : ℕ) : (Q m).vertex (σ.next^[m] j) = .inr ∞ := by
    rw [vertex_smul, mul_smul, ← σ.partialCycleMap_smul_vertex, inv_smul_smul, hj, Sum.smul_inr,
      hg]
  let u (m : ℕ) : ℝ := (toComplex ((Q m).vertex (σ.next^[m] j + 1))).re
  let v (m : ℕ) : ℝ := (toComplex ((Q m).vertex (σ.next^[m] j - 1))).re
  have huv (m : ℕ) : u m < v m := (Q m).re_toComplex_vertex_add_one_lt_of_vertex_eq_inr_infty (hQ m)
  have hvu (m : ℕ) : v (m + 1) = u m := by
    simp only [v, u, Q, vertex_smul, mul_smul, σ.inv_partialCycleMap_succ_smul_vertex_sub_one]
  -- after a full cycle the strip has moved by `-x`
  have hvr : v (σ.cycleLength j) = -x + v 0 := by
    have hQr : g * (σ.partialCycleMap j (σ.cycleLength j))⁻¹ = upperRightHom (-x) * g := by
      rw [AddChar.map_neg_eq_inv, ← hx, ← cycleMap_def]
      group
    have hne : g • P.vertex (j - 1) ≠ .inr ∞ := by
      rw [← hg, ← Sum.smul_inr, ← hj]
      exact (MulAction.injective g).ne (P.vertex_ne_vertex_sub_one j).symm
    simp only [v, Q]
    rw [hQr, σ.next_iterate_cycleLength, Function.iterate_zero_apply, partialCycleMap_zero,
      inv_one, mul_one, vertex_smul, vertex_smul, mul_smul, toComplex_upperRightHom_smul _ hne,
      Complex.add_re, Complex.ofReal_re]
  have hanti : StrictAnti v := strictAnti_nat_of_succ_lt fun m ↦ (hvu m).trans_lt (huv m)
  have hx0 : 0 < x := by
    have := hanti (σ.cycleLength_pos j)
    linarith
  -- above a common height every tile agrees with its strip
  obtain ⟨A, hA⟩ := (atImInfty_mem _).1 ((Finset.range (σ.cycleLength j)).eventually_all.2
    fun m _ ↦ ((Q m).eventuallyEq_carrier_vertexSector_atImInfty (hQ m)).mem_iff)
  refine ⟨A, fun z hz ↦ ?_⟩
  -- translate `g • z` by a multiple of `x` into the period filled by the strips of one cycle
  set k := toIocDiv hx0 (v (σ.cycleLength j)) (g • z).re
  have hk := sub_toIocDiv_zsmul_mem_Ioc hx0 (v (σ.cycleLength j)) (g • z).re
  -- one full cycle of strips spans exactly one period
  have hperiod : v (σ.cycleLength j) + x = v 0 := by rw [hvr]; ring
  rw [hperiod] at hk
  set w : ℍ := g • (σ.cycleMap j ^ (-k) • z)
  have hw : w = (((-k : ℤ) : ℝ) * x) +ᵥ (g • z) := smul_zpow_smul hx (-k) z
  have hwre : w.re ∈ Ioc (v (σ.cycleLength j)) (v 0) := by
    convert hk using 1
    rw [hw, vadd_re, zsmul_eq_mul, Int.cast_neg]
    ring
  obtain ⟨m, hm, hmw⟩ : ∃ m ∈ Finset.range (σ.cycleLength j), w.re ∈ Ioc (u m) (v m) := by
    have := Ico_subset_biUnion_Ico (σ.cycleLength j) (fun m ↦ -v m)
      ⟨neg_le_neg hwre.2, neg_lt_neg hwre.1⟩
    simp only [mem_iUnion, mem_Ico, neg_le_neg_iff, neg_lt_neg_iff, hvu] at this
    obtain ⟨m, hm, h₁, h₂⟩ := this
    exact ⟨m, hm, h₂, h₁⟩
  have hwQ : w ∈ (Q m).carrier := by
    refine ((hA w ?_) m hm).2 (((Q m).mem_vertexSector_iff_of_vertex_eq_inr_infty (hQ m) w).2
      ⟨hmw.1.le, hmw.2⟩)
    rw [hw, vadd_im]
    exact hz.le
  refine mem_iUnion.2 ⟨k, mem_iUnion₂.2 ⟨m, hm, ?_⟩⟩
  rw [carrier_smul, mem_smul_set_iff_inv_smul_mem, mul_inv_rev, inv_inv, mul_smul,
    inv_smul_smul] at hwQ
  rw [mem_smul_set_iff_inv_smul_mem, mul_inv_rev, inv_inv, mul_smul, ← zpow_neg]
  exact hwQ

end TauCeti.UpperHalfPlane.ConvexPolygon.SidePairing
