/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.LocallyFinite
public import TauCeti.Analysis.Complex.UpperHalfPlane.Polygon.Convex.VertexSector
public import TauCeti.Analysis.Complex.UpperHalfPlane.Polygon.SidePairing.Ideal
import TauCeti.Analysis.Complex.UpperHalfPlane.Polygon.Convex.IdealVertex.Stabilizer
import TauCeti.Analysis.Complex.UpperHalfPlane.Polygon.Convex.Sides
import Mathlib.Algebra.Order.ToIntervalMod
import Mathlib.Order.Interval.Set.Union
import Mathlib.Order.SuccPred.IntervalSucc
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

Since the strips move strictly in one direction, the tiles met along the cycle have pairwise
disjoint interiors, however often the cycle is traversed, and so do their translates by powers of
the cycle transformation. Unlike at a finite vertex, no angle condition is involved. When the
cycle transformation is parabolic, these tiles therefore tessellate a horodisc at the vertex.

An ideal cycle transformation is never the identity. It fixes a boundary point, so it is
parabolic or hyperbolic. If a group containing it has locally finite translates of `P`, then it
is parabolic (`ConvexPolygon.isParabolic_of_smul_eq_self_of_locallyFinite`). So the parabolic
cycle condition holds at every ideal vertex of a locally finite fundamental polygon.

## Main results

* `ConvexPolygon.SidePairing.strictAnti_re_toComplex_smul_vertex_sub_one`: in a coordinate
  moving an ideal vertex to `∞`, the strips of its cycle move strictly to the left.
* `SidePairing.pairwise_disjoint_inv_partialCycleMap_smul_interior_carrier_of_vertex_eq_inr`:
  the tiles met along an ideal vertex cycle have pairwise disjoint interiors.
* `ConvexPolygon.SidePairing.partialCycleMap_injective_of_vertex_eq_inr`: the partial cycle maps
  at an ideal vertex are pairwise distinct.
* `ConvexPolygon.SidePairing.cycleMap_ne_one_of_vertex_eq_inr`: an ideal cycle transformation is
  not the identity.
* `ConvexPolygon.SidePairing.isParabolic_cycleMap_of_locallyFinite`: an ideal cycle
  transformation is parabolic when a group containing it has locally finite translates of `P`.
* `ConvexPolygon.SidePairing.exists_pos_conj_cycleMap_eq_upperRightHom`: the parabolic cycle
  transformation is a positive translation in every scaling sending its vertex to infinity.
* `ConvexPolygon.SidePairing.exists_setOf_lt_im_smul_subset_iUnion_smul_carrier`: at an ideal
  vertex with parabolic cycle transformation, the tiles of the cycle and their translates by
  powers of the cycle transformation cover a horodisc.
* `SidePairing.pairwiseDisjoint_cycleMap_zpow_mul_inv_partialCycleMap_smul_interior_carrier`:
  these tiles have pairwise disjoint interiors.

## References

Beardon, *The Geometry of Discrete Groups*, Chapter 9. Walkden, *Hyperbolic geometry*
(MATH32051 lecture notes, Manchester 2019), §§17.2 and 19–20 (parabolic cycles and the local
tessellation in Poincaré's polygon theorem). Maskit, *On Poincaré's theorem for fundamental
polygons*, Adv. Math. 7 (1971), 219–230.
-/

public section

open Function Matrix.ProjectiveSpecialLinearGroup Set UpperHalfPlane
open scoped MatrixGroups Pointwise OnePoint

namespace TauCeti.UpperHalfPlane.ConvexPolygon.SidePairing

variable {n : ℕ} [NeZero n] {P : ConvexPolygon n} (σ : P.SidePairing)

/-- In a coordinate `g` moving an ideal vertex to `∞`, every tile of its cycle has its
corresponding vertex at `∞`. -/
private theorem mul_inv_partialCycleMap_smul_vertex {j : Fin n} {ξ : OnePoint ℝ}
    (hj : P.vertex j = .inr ξ) {g : PSL(2, ℝ)} (hg : g • ξ = ∞) (m : ℕ) :
    ((g * (σ.partialCycleMap j m)⁻¹) • P).vertex (σ.next^[m] j) = .inr ∞ := by
  rw [vertex_smul, mul_smul, ← σ.partialCycleMap_smul_vertex, inv_smul_smul, hj, Sum.smul_inr, hg]

/-- **The strips of an ideal cycle move strictly to the left.** Let `vertex j = ξ` be ideal and
let `g` carry `ξ` to `∞`. In the coordinate `g`, the tile `(partialCycleMap j m)⁻¹ • P` is near
`∞` the vertical strip ending on the right at the vertex before `next^[m] j`. The real part of
that vertex strictly decreases with `m`. -/
theorem strictAnti_re_toComplex_smul_vertex_sub_one {j : Fin n} {ξ : OnePoint ℝ}
    (hj : P.vertex j = .inr ξ) {g : PSL(2, ℝ)} (hg : g • ξ = ∞) :
    StrictAnti fun m : ℕ ↦
      (toComplex ((g * (σ.partialCycleMap j m)⁻¹) • P.vertex (σ.next^[m] j - 1))).re := by
  refine strictAnti_nat_of_succ_lt fun m ↦ ?_
  -- the right edge of the strip of tile `m + 1` is the left edge of the strip of tile `m`
  simpa only [mul_smul, σ.inv_partialCycleMap_succ_smul_vertex_sub_one, vertex_smul] using
    ((g * (σ.partialCycleMap j m)⁻¹) • P).re_toComplex_vertex_add_one_lt_of_vertex_eq_inr_infty
      (σ.mul_inv_partialCycleMap_smul_vertex hj hg m)

/-- **An ideal cycle transformation is not the identity**: going once around the cycle moves the
strips of its tiles strictly to the left. -/
theorem cycleMap_ne_one_of_vertex_eq_inr {j : Fin n} {ξ : OnePoint ℝ}
    (hj : P.vertex j = .inr ξ) : σ.cycleMap j ≠ 1 := by
  intro h
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq PSL(2, ℝ) ξ (∞ : OnePoint ℝ)
  have hlt := σ.strictAnti_re_toComplex_smul_vertex_sub_one hj hg (σ.cycleLength_pos j)
  beta_reduce at hlt
  rw [← cycleMap_def, h, σ.next_iterate_cycleLength, partialCycleMap_zero,
    Function.iterate_zero_apply] at hlt
  exact lt_irrefl _ hlt

/-- In a coordinate `g` moving an ideal vertex to `∞`, the interior of the `m`-th pulled-back
sector of its cycle is the open vertical strip whose right edge is that of the strip of tile `m`
and whose left edge is that of tile `m + 1`. -/
private theorem mem_smul_inv_partialCycleMap_smul_interior_vertexSector_iff {j : Fin n}
    {ξ : OnePoint ℝ} (hj : P.vertex j = .inr ξ) {g : PSL(2, ℝ)} (hg : g • ξ = ∞) (m : ℕ)
    (w : ℍ) :
    w ∈ g • (σ.partialCycleMap j m)⁻¹ • interior (P.vertexSector (σ.next^[m] j)) ↔
      (toComplex ((g * (σ.partialCycleMap j (m + 1))⁻¹) •
          P.vertex (σ.next^[m + 1] j - 1))).re < w.re ∧
        w.re < (toComplex ((g * (σ.partialCycleMap j m)⁻¹) • P.vertex (σ.next^[m] j - 1))).re := by
  rw [smul_smul, ← interior_smul, ← vertexSector_smul,
    mem_interior_vertexSector_iff_of_vertex_eq_inr_infty _
      (σ.mul_inv_partialCycleMap_smul_vertex hj hg m)]
  simp only [vertex_smul, mul_smul, σ.inv_partialCycleMap_succ_smul_vertex_sub_one]

/-- **The sectors of an ideal vertex cycle do not overlap.** Pulling the sectors at the vertices
of the cycle through an ideal vertex back along the partial cycle maps gives sectors at that
vertex with pairwise disjoint interiors, however many times the cycle is traversed. Unlike at a
finite vertex, no angle condition is needed: after moving the vertex to `∞`, these interiors are
open vertical strips moving strictly to the left. -/
theorem pairwise_disjoint_inv_partialCycleMap_smul_interior_vertexSector_of_vertex_eq_inr
    {j : Fin n} {ξ : OnePoint ℝ} (hj : P.vertex j = .inr ξ) :
    Pairwise (Disjoint on fun m : ℕ ↦
      (σ.partialCycleMap j m)⁻¹ • interior (P.vertexSector (σ.next^[m] j))) := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq PSL(2, ℝ) ξ (∞ : OnePoint ℝ)
  -- in the coordinate `g`, the sectors are open strips over consecutive intervals of reals
  intro m m' hne
  have h := (Antitone.pairwise_disjoint_on_Ioo_succ
    (σ.strictAnti_re_toComplex_smul_vertex_sub_one hj hg).antitone hne).preimage
    UpperHalfPlane.re
  rw [onFun, ← Set.disjoint_smul_set (a := g)]
  convert h using 1 <;>
    ext w <;>
    simp only [σ.mem_smul_inv_partialCycleMap_smul_interior_vertexSector_iff hj hg,
      mem_preimage, mem_Ioo, Order.succ_eq_add_one]

/-- **The tiles of an ideal vertex cycle do not overlap.** The tiles `(partialCycleMap j m)⁻¹ • P`
obtained by following the side pairings from an ideal vertex have pairwise disjoint interiors,
for all `m`. -/
theorem pairwise_disjoint_inv_partialCycleMap_smul_interior_carrier_of_vertex_eq_inr
    {j : Fin n} {ξ : OnePoint ℝ} (hj : P.vertex j = .inr ξ) :
    Pairwise (Disjoint on fun m : ℕ ↦ (σ.partialCycleMap j m)⁻¹ • interior P.carrier) :=
  pairwise_disjoint_mono
    (σ.pairwise_disjoint_inv_partialCycleMap_smul_interior_vertexSector_of_vertex_eq_inr hj)
    fun _ ↦ Set.smul_set_mono (interior_mono (P.carrier_subset_vertexSector _))

/-- The partial cycle maps at an ideal vertex are pairwise distinct. -/
theorem partialCycleMap_injective_of_vertex_eq_inr {j : Fin n} {ξ : OnePoint ℝ}
    (hj : P.vertex j = .inr ξ) : Injective (σ.partialCycleMap j) := by
  intro m m' h
  by_contra hne
  obtain ⟨w, hw⟩ := P.nonempty_interior_carrier
  have hdisj := σ.pairwise_disjoint_inv_partialCycleMap_smul_interior_carrier_of_vertex_eq_inr
    hj hne
  rw [onFun, h] at hdisj
  exact Set.disjoint_left.1 hdisj (Set.smul_mem_smul_set hw) (Set.smul_mem_smul_set hw)

/-- **Ideal cycle transformations of a locally finite tessellation are parabolic.** If a subgroup
`Γ` of `PSL(2, ℝ)` contains the cycle transformation at the ideal vertex `vertex j` and its
translates of `P` form a locally finite family, then this cycle transformation is parabolic. -/
theorem isParabolic_cycleMap_of_locallyFinite {j : Fin n} {ξ : OnePoint ℝ}
    (hj : P.vertex j = .inr ξ) {Γ : Subgroup PSL(2, ℝ)} (hT : σ.cycleMap j ∈ Γ)
    (hlf : LocallyFinite fun γ : Γ ↦ (γ : PSL(2, ℝ)) • P.carrier) :
    IsParabolic (σ.cycleMap j) :=
  P.isParabolic_of_smul_eq_self_of_locallyFinite hj hlf hT
    (σ.cycleMap_smul_eq_self_of_vertex_eq_inr hj) (σ.cycleMap_ne_one_of_vertex_eq_inr hj)

/-- If the conjugated cycle transformation is translation by `w`, the inverse full cycle
shifts the real part of the preceding vertex by `-w`. -/
private theorem re_toComplex_inv_partialCycleMap_cycleLength_smul_vertex_sub_one {j : Fin n}
    {ξ : OnePoint ℝ} (hj : P.vertex j = .inr ξ) {g : PSL(2, ℝ)} (hg : g • ξ = ∞)
    {w : ℝ} (hw : g * σ.cycleMap j * g⁻¹ = upperRightHom w) :
    (toComplex ((g * (σ.partialCycleMap j (σ.cycleLength j))⁻¹) • P.vertex (j - 1))).re =
      -w + (toComplex (g • P.vertex (j - 1))).re := by
  have hmove : g * (σ.cycleMap j)⁻¹ = upperRightHom (-w) * g := by
    rw [AddChar.map_neg_eq_inv, ← hw]
    group
  have hne : g • P.vertex (j - 1) ≠ .inr ∞ := by
    rw [← hg, ← Sum.smul_inr, ← hj]
    exact (MulAction.injective g).ne (P.vertex_ne_vertex_sub_one j).symm
  rw [← cycleMap_def, hmove, mul_smul, toComplex_upperRightHom_smul _ hne,
    Complex.add_re, Complex.ofReal_re]

/-- In any scaling sending an ideal vertex to infinity, its parabolic cycle transformation is
translation by a strictly positive amount. The sign is fixed by the side-pairing cycle order. -/
theorem exists_pos_conj_cycleMap_eq_upperRightHom {j : Fin n} {ξ : OnePoint ℝ}
    (hj : P.vertex j = .inr ξ) (hpar : IsParabolic (σ.cycleMap j)) {g : PSL(2, ℝ)}
    (hg : g • ξ = ∞) :
    ∃ w : ℝ, 0 < w ∧ g * σ.cycleMap j * g⁻¹ = upperRightHom w := by
  have hfix : (g * σ.cycleMap j * g⁻¹) • (∞ : OnePoint ℝ) = ∞ := by
    rw [mul_smul, mul_smul, ← hg, inv_smul_smul, σ.cycleMap_smul_eq_self_of_vertex_eq_inr hj]
  obtain ⟨w, -, hw⟩ := (isParabolic_iff_exists_eq_upperRightHom hfix).1
    ((isParabolic_conj_iff g _).2 hpar)
  -- The inverse cycle moves the right edge of its strip strictly left, so `w` is positive.
  have hlt := σ.strictAnti_re_toComplex_smul_vertex_sub_one hj hg (σ.cycleLength_pos j)
  simp only [σ.next_iterate_cycleLength, Function.iterate_zero_apply,
    partialCycleMap_zero, inv_one, mul_one,
    σ.re_toComplex_inv_partialCycleMap_cycleLength_smul_vertex_sub_one hj hg hw] at hlt
  exact ⟨w, by linarith, hw⟩

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
  -- in the coordinate `g`, the cycle transformation is translation by some `x > 0`
  obtain ⟨x, hx0, hx⟩ := σ.exists_pos_conj_cycleMap_eq_upperRightHom hj hpar hg
  -- the `m`-th tile in the coordinate `g` has its vertex `next^[m] j` at `∞`, with sector the
  -- strip `u m ≤ Re ≤ v m`
  let Q (m : ℕ) : ConvexPolygon n := (g * (σ.partialCycleMap j m)⁻¹) • P
  have hQ (m : ℕ) : (Q m).vertex (σ.next^[m] j) = .inr ∞ :=
    σ.mul_inv_partialCycleMap_smul_vertex hj hg m
  let u (m : ℕ) : ℝ := (toComplex ((Q m).vertex (σ.next^[m] j + 1))).re
  let v (m : ℕ) : ℝ := (toComplex ((Q m).vertex (σ.next^[m] j - 1))).re
  have hvu (m : ℕ) : v (m + 1) = u m := by
    simp only [v, u, Q, vertex_smul, mul_smul, σ.inv_partialCycleMap_succ_smul_vertex_sub_one]
  -- after a full cycle the strip has moved by `-x`
  have hvr : v (σ.cycleLength j) = -x + v 0 := by
    simpa only [v, Q, vertex_smul, σ.next_iterate_cycleLength,
      Function.iterate_zero_apply, partialCycleMap_zero, inv_one, mul_one] using
      σ.re_toComplex_inv_partialCycleMap_cycleLength_smul_vertex_sub_one hj hg hx
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

/-- **The local tiling at an ideal vertex has no overlaps.** Let `vertex j` be ideal with cycle
transformation `T`. The tiles `(T ^ k * (partialCycleMap j m)⁻¹) • P`, for `k ∈ ℤ` and `m` less
than the cycle length, have pairwise disjoint interiors. When `T` is parabolic these tiles also
cover a horodisc at the vertex (`exists_setOf_lt_im_smul_subset_iUnion_smul_carrier`), so they
tessellate it. -/
theorem pairwiseDisjoint_cycleMap_zpow_mul_inv_partialCycleMap_smul_interior_carrier
    {j : Fin n} {ξ : OnePoint ℝ} (hj : P.vertex j = .inr ξ) :
    (univ ×ˢ (Finset.range (σ.cycleLength j) : Set ℕ)).PairwiseDisjoint fun p : ℤ × ℕ ↦
      (σ.cycleMap j ^ p.1 * (σ.partialCycleMap j p.2)⁻¹) • interior P.carrier := by
  rintro ⟨k, m⟩ ⟨-, hm⟩ ⟨k', m'⟩ ⟨-, hm'⟩ hne
  rw [Finset.coe_range, mem_Iio] at hm hm'
  -- moved by `T ^ (-K)` with `K ≥ k`, the tile `(k, m)` is the tile of the partial cycle map
  -- after `K - k` full circuits and `m` further steps
  set K := max k k'
  have htile {k : ℤ} (hk : k ≤ K) (m : ℕ) :
      σ.cycleMap j ^ (-K) • (σ.cycleMap j ^ k * (σ.partialCycleMap j m)⁻¹) • interior P.carrier =
        (σ.partialCycleMap j ((K - k).toNat * σ.cycleLength j + m))⁻¹ • interior P.carrier := by
    rw [smul_smul, partialCycleMap_mul_cycleLength_add, ← zpow_natCast,
      Int.toNat_of_nonneg (sub_nonneg.2 hk)]
    group
  rw [onFun, ← Set.disjoint_smul_set (a := σ.cycleMap j ^ (-K)), htile (le_max_left k k'),
    htile (le_max_right k k')]
  refine σ.pairwise_disjoint_inv_partialCycleMap_smul_interior_carrier_of_vertex_eq_inr hj
    fun h ↦ hne ?_
  -- the number of circuits and the remaining steps are the quotient and remainder by the length
  dsimp only at h hm hm'
  have hq := (Nat.div_mod_unique (σ.cycleLength_pos j)).2
    ⟨(by ring : m + σ.cycleLength j * (K - k).toNat =
      (K - k).toNat * σ.cycleLength j + m), hm⟩
  have hq' := (Nat.div_mod_unique (σ.cycleLength_pos j)).2
    ⟨(by ring : m' + σ.cycleLength j * (K - k').toNat =
      (K - k').toNat * σ.cycleLength j + m'), hm'⟩
  rw [h] at hq
  have hK : k ≤ K ∧ k' ≤ K := ⟨le_max_left k k', le_max_right k k'⟩
  rw [Prod.mk.injEq]
  omega

end TauCeti.UpperHalfPlane.ConvexPolygon.SidePairing
