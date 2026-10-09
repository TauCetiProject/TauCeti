/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Dynamics.PeriodicPts.Lemmas
public import Mathlib.GroupTheory.Perm.Cycle.Basic
public import TauCeti.Analysis.Complex.UpperHalfPlane.Polygon.Convex
import TauCeti.Analysis.Complex.UpperHalfPlane.Stabilizer
import TauCeti.Data.Fin.Basic

/-!
# Side pairings and vertex cycles of a convex hyperbolic polygon

A side pairing of a convex polygon `P` is an involution `pair` of its sides together with,
for each side `i`, an element `map i` of `PSL(2, ℝ)` carrying side `i` onto side `pair i` with the
orientation reversed: `vertex i ↦ vertex (pair i + 1)` and `vertex (i + 1) ↦ vertex (pair i)`, the
map of the paired side being the inverse. Following a vertex `j` through the pairing of the side
leaving it, then switching to the other side at the image vertex, is the permutation
`next : j ↦ pair j + 1` of the vertices. Its orbits are the vertex cycles, and the product of the
side-pairing maps along a cycle is the cycle transformation.

Vertices may be finite or ideal, so the paired sides may be segments, rays, or full geodesic
lines. No Fuchsian group appears: these are the standalone definitions and their elementary
properties. Going around a cycle `k` times gives the `k`-th power of the cycle transformation.

At a finite vertex cycle, the relation `m · sum = 2π` between the order of a cycle transformation
and the angle sum needs the polygon to be a fundamental domain, and is proved in
`TauCeti.Analysis.Complex.UpperHalfPlane.Polygon.SidePairing.VertexStabilizer`.

## Main definitions

* `ConvexPolygon.SidePairing`: a side pairing of a convex polygon.
* `ConvexPolygon.SidePairing.next`: the successor of a vertex along its cycle,
  `j ↦ pair j + 1`.
* `ConvexPolygon.SidePairing.cycleLength`: the length of the vertex cycle through `j`.
* `ConvexPolygon.SidePairing.partialCycleMap`: the product of the first `m` side-pairing maps
  along the cycle starting at `j`.
* `ConvexPolygon.SidePairing.cycleMap`: the cycle transformation at the vertex `j`.
* `ConvexPolygon.SidePairing.cycle`: the vertex cycle through `j`, as a `Finset`.
* `ConvexPolygon.SidePairing.cycleAngleSum`: the sum of the interior angles along a cycle.

## Main results

* `ConvexPolygon.SidePairing.map_smul_side`: the side-pairing map carries side `i` onto side
  `pair i`.
* `ConvexPolygon.SidePairing.map_ne_one`: a side-pairing map is not the identity.
* `ConvexPolygon.SidePairing.cycleMap_smul_vertex`: the cycle transformation at `j` fixes
  `vertex j`.
* `ConvexPolygon.SidePairing.cycleMap_next`: the cycle transformations at the vertices of one
  cycle are conjugate.
* `ConvexPolygon.SidePairing.partialCycleMap_mul_cycleLength`: `k` circuits of a cycle give the
  `k`-th power of the cycle transformation.
* `ConvexPolygon.SidePairing.isElliptic_of_cycleMap_eq`: a nonidentity cycle transformation at
  a vertex in `ℍ` is elliptic.
* `ConvexPolygon.SidePairing.card_cycle`: the vertex cycle through `j` has `cycleLength j`
  vertices.
* `ConvexPolygon.SidePairing.cycleAngleSum_next`,
  `ConvexPolygon.SidePairing.cycleAngleSum_nonneg`: the angle sum does not depend on the
  starting vertex of the cycle, and is nonnegative.
* `ConvexPolygon.SidePairing.sum_range_mul_cycleLength_interiorAngle`: `t` circuits of a cycle
  have total angle `t` times the angle sum.

## Source

Walkden, *Hyperbolic geometry* (MATH32051 lecture notes, Manchester 2019), §16.1 (side-pairing
transformations), §17.1 (elliptic cycles and elliptic cycle transformations; Remarks 1–2 and the
paragraph after Exercise 17.1: an elliptic cycle transformation fixes its vertex, hence is
elliptic or the identity), §17.3 (the angle sum along an elliptic cycle).
-/

public section

noncomputable section

open Matrix.ProjectiveSpecialLinearGroup Set UpperHalfPlane
open scoped MatrixGroups Pointwise Real

namespace TauCeti.UpperHalfPlane

namespace ConvexPolygon

variable {n : ℕ} [NeZero n]

/-- A side pairing of the convex polygon `P`: an involution `pair` of the sides (side `i`
runs from `vertex i` to `vertex (i + 1)`) and, for each side `i`, an element `map i` of `PSL(2, ℝ)`
carrying side `i` onto side `pair i` with the orientation reversed, the map of the paired side being
the inverse. A side may be paired with itself. -/
@[ext]
structure SidePairing (P : ConvexPolygon n) where
  /-- The side paired with side `i`. -/
  pair : Equiv.Perm (Fin n)
  /-- Pairing is an involution. -/
  pair_pair : ∀ i, pair (pair i) = i
  /-- The transformation carrying side `i` onto side `pair i`. -/
  map : Fin n → PSL(2, ℝ)
  /-- The transformation of the paired side is the inverse. -/
  map_pair : ∀ i, map (pair i) = (map i)⁻¹
  /-- The start of side `i` goes to the end of side `pair i`. -/
  map_smul_vertex : ∀ i, map i • P.vertex i = P.vertex (pair i + 1)
  /-- The end of side `i` goes to the start of side `pair i`. -/
  map_smul_vertex_add_one : ∀ i, map i • P.vertex (i + 1) = P.vertex (pair i)

namespace SidePairing

attribute [simp] pair_pair map_pair

variable {P : ConvexPolygon n} (σ : P.SidePairing)

/-! ### The pairing of the sides -/

/-- Pairing is an involution. -/
theorem pair_involutive : Function.Involutive σ.pair :=
  σ.pair_pair

/-- The inverse of the pairing is the pairing. -/
@[simp]
theorem pair_symm : σ.pair.symm = σ.pair :=
  Equiv.ext fun i ↦ σ.pair.symm_apply_eq.2 (σ.pair_pair i).symm

/-- The map of the paired side carries the end of side `pair i` back to the start of side `i`. -/
theorem map_pair_smul_vertex (i : Fin n) :
    σ.map (σ.pair i) • P.vertex (σ.pair i + 1) = P.vertex i := by
  rw [σ.map_pair, inv_smul_eq_iff, σ.map_smul_vertex]

/-- The map of the paired side carries the start of side `pair i` back to the end of side `i`. -/
theorem map_pair_smul_vertex_add_one (i : Fin n) :
    σ.map (σ.pair i) • P.vertex (σ.pair i) = P.vertex (i + 1) := by
  rw [σ.map_pair, inv_smul_eq_iff, σ.map_smul_vertex_add_one]

/-- The side-pairing map carries side `i` onto side `pair i`. -/
theorem map_smul_side (i : Fin n) : σ.map i • P.side i = P.side (σ.pair i) := by
  rw [side_def, side_def, smul_extGeodesicSegment, σ.map_smul_vertex, σ.map_smul_vertex_add_one,
    extGeodesicSegment_comm]

/-- A side-pairing map is not the identity. -/
theorem map_ne_one (i : Fin n) : σ.map i ≠ 1 := by
  -- the identity would fix both endpoints of side `i`, forcing `pair i + 1 = i` and
  -- `pair i = i + 1`, impossible with at least three vertices
  intro h
  have h₁ := P.vertex_injective (by simpa [h] using σ.map_smul_vertex i)
  have h₂ := P.vertex_injective (by simpa [h] using σ.map_smul_vertex_add_one i)
  exact add_one_add_one_ne_self P.three_le i (by rw [h₂, ← h₁])

/-! ### The vertex successor -/

/-- The successor of a vertex along the cycles: the end of the side paired with the side leaving
it, `j ↦ pair j + 1`. -/
def next : Equiv.Perm (Fin n) :=
  σ.pair.trans (Equiv.addRight 1)

/-- The successor of `j` is `pair j + 1`. -/
@[simp]
theorem next_apply (j : Fin n) : σ.next j = σ.pair j + 1 :=
  (rfl)

/-- The predecessor of `j` is the pair of the side ending at `j`. -/
@[simp]
theorem next_symm_apply (j : Fin n) : σ.next.symm j = σ.pair (j - 1) := by
  simp [next, sub_eq_add_neg]

/-- The side-pairing map of the side leaving `j` carries `vertex j` to the successor vertex. -/
theorem map_smul_vertex_eq_next (j : Fin n) : σ.map j • P.vertex j = P.vertex (σ.next j) :=
  σ.map_smul_vertex j

/-- Every vertex is periodic for the successor. -/
theorem mem_periodicPts_next (j : Fin n) : j ∈ Function.periodicPts σ.next :=
  σ.next.injective.mem_periodicPts j

/-! ### Cycle transformations -/

/-- The product of the first `m` side-pairing maps along the cycle starting at `j`:
`map (next^[m-1] j) * ⋯ * map (next j) * map j`. -/
def partialCycleMap (j : Fin n) : ℕ → PSL(2, ℝ)
  | 0 => 1
  | m + 1 => σ.map (σ.next^[m] j) * partialCycleMap j m

/-- The empty product of side-pairing maps is the identity. -/
@[simp]
theorem partialCycleMap_zero (j : Fin n) : σ.partialCycleMap j 0 = 1 :=
  (rfl)

/-- The partial products grow by multiplying on the left by the next side-pairing map. -/
theorem partialCycleMap_succ (j : Fin n) (m : ℕ) :
    σ.partialCycleMap j (m + 1) = σ.map (σ.next^[m] j) * σ.partialCycleMap j m :=
  (rfl)

/-- The partial products can also be peeled off at the start: the first map applied is the
side-pairing map of the side leaving `j`, followed by the partial product from `next j`. -/
theorem partialCycleMap_succ' (j : Fin n) (m : ℕ) :
    σ.partialCycleMap j (m + 1) = σ.partialCycleMap (σ.next j) m * σ.map j := by
  induction m with
  | zero => simp [partialCycleMap_succ]
  | succ m ih =>
    rw [partialCycleMap_succ, ih, partialCycleMap_succ, Function.iterate_succ_apply, mul_assoc]

/-- The partial products are multiplicative along the cycle: the first `a + b` maps from `j` are
the first `a` maps from `j`, followed by the first `b` maps from `next^[a] j`. -/
theorem partialCycleMap_add (j : Fin n) (a b : ℕ) :
    σ.partialCycleMap j (a + b) = σ.partialCycleMap (σ.next^[a] j) b * σ.partialCycleMap j a := by
  induction b with
  | zero => simp
  | succ b ih =>
    rw [← add_assoc, partialCycleMap_succ, ih, partialCycleMap_succ, mul_assoc,
      add_comm a b, Function.iterate_add_apply]

/-- The partial products lie in every subgroup containing the side-pairing maps. -/
theorem partialCycleMap_mem {Γ : Subgroup PSL(2, ℝ)} (hmap : ∀ i, σ.map i ∈ Γ) (j : Fin n)
    (m : ℕ) : σ.partialCycleMap j m ∈ Γ := by
  induction m with
  | zero => exact Γ.one_mem
  | succ m ih => exact Γ.mul_mem (hmap _) ih

/-- The partial product of the first `m` side-pairing maps carries `vertex j` to the vertex at
the `m`-th successor of `j`. -/
theorem partialCycleMap_smul_vertex (j : Fin n) (m : ℕ) :
    σ.partialCycleMap j m • P.vertex j = P.vertex (σ.next^[m] j) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [partialCycleMap_succ, mul_smul, ih, map_smul_vertex_eq_next, Function.iterate_succ_apply']

/-- Consecutive tiles `(partialCycleMap j m)⁻¹ • P` along a vertex cycle share a side: pulled back
to the initial vertex, the vertex before the cycle vertex in tile `m + 1` is the vertex after it
in tile `m`. -/
theorem inv_partialCycleMap_succ_smul_vertex_sub_one (j : Fin n) (m : ℕ) :
    (σ.partialCycleMap j (m + 1))⁻¹ • P.vertex (σ.next^[m + 1] j - 1) =
      (σ.partialCycleMap j m)⁻¹ • P.vertex (σ.next^[m] j + 1) := by
  rw [partialCycleMap_succ, mul_inv_rev, mul_smul, Function.iterate_succ_apply', next_apply,
    add_sub_cancel_right, ← σ.map_smul_vertex_add_one, inv_smul_smul]

/-- The length of the vertex cycle through `j`: the minimal period of `j` under the successor. -/
def cycleLength (j : Fin n) : ℕ :=
  Function.minimalPeriod σ.next j

-- The body of `cycleLength` is not `@[expose]`d, so downstream modules rewrite with this.
/-- The cycle length, unfolded. -/
theorem cycleLength_def (j : Fin n) : σ.cycleLength j = Function.minimalPeriod σ.next j :=
  (rfl)

/-- Cycles are nonempty. -/
theorem cycleLength_pos (j : Fin n) : 0 < σ.cycleLength j :=
  Function.minimalPeriod_pos_of_mem_periodicPts (σ.mem_periodicPts_next j)

/-- A cycle has at most `n` vertices. -/
theorem cycleLength_le (j : Fin n) : σ.cycleLength j ≤ n :=
  by
  simpa [cycleLength] using Function.minimalPeriod_le_card (f := σ.next) (x := j)

/-- The cycle length is constant along a cycle. -/
theorem cycleLength_next (j : Fin n) : σ.cycleLength (σ.next j) = σ.cycleLength j :=
  Function.minimalPeriod_apply (σ.mem_periodicPts_next j)

/-- The cycle length is constant along a cycle, in the simp-normal form of `next`. -/
@[simp]
theorem cycleLength_pair_add_one (j : Fin n) : σ.cycleLength (σ.pair j + 1) = σ.cycleLength j := by
  rw [← next_apply, cycleLength_next]

/-- Going once around the cycle returns to the starting vertex. -/
theorem next_iterate_cycleLength (j : Fin n) : σ.next^[σ.cycleLength j] j = j :=
  Function.iterate_minimalPeriod

/-- **The cycle transformation** at the vertex `j`: the product of the side-pairing maps along the
vertex cycle through `j`, starting with the side leaving `j`. -/
def cycleMap (j : Fin n) : PSL(2, ℝ) :=
  σ.partialCycleMap j (σ.cycleLength j)

-- The body of `cycleMap` is not `@[expose]`d, so downstream modules rewrite with this.
/-- The cycle transformation, unfolded. -/
theorem cycleMap_def (j : Fin n) : σ.cycleMap j = σ.partialCycleMap j (σ.cycleLength j) :=
  (rfl)

/-- Going `k` times around the cycle through `j` gives the `k`-th power of the cycle
transformation. -/
theorem partialCycleMap_mul_cycleLength (j : Fin n) (k : ℕ) :
    σ.partialCycleMap j (k * σ.cycleLength j) = σ.cycleMap j ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hper : σ.next^[k * σ.cycleLength j] j = j := by
      rw [cycleLength_def]
      exact ((Function.isPeriodicPt_minimalPeriod σ.next j).const_mul k).eq
    rw [Nat.succ_mul, partialCycleMap_add, hper, ih, ← cycleMap_def, pow_succ']

/-- The cycle transformation lies in every subgroup containing the side-pairing maps. -/
theorem cycleMap_mem {Γ : Subgroup PSL(2, ℝ)} (hmap : ∀ i, σ.map i ∈ Γ) (j : Fin n) :
    σ.cycleMap j ∈ Γ :=
  σ.partialCycleMap_mem hmap j _

/-- **The cycle transformation at `j` fixes `vertex j`.** -/
theorem cycleMap_smul_vertex (j : Fin n) : σ.cycleMap j • P.vertex j = P.vertex j := by
  rw [cycleMap, partialCycleMap_smul_vertex, next_iterate_cycleLength]

/-- **The cycle transformations along a cycle are conjugate**: the one at the successor of `j` is
the conjugate of the one at `j` by the side-pairing map of the side leaving `j`. -/
theorem cycleMap_next (j : Fin n) :
    σ.cycleMap (σ.next j) = σ.map j * σ.cycleMap j * (σ.map j)⁻¹ := by
  refine eq_mul_inv_of_mul_eq ?_
  rw [cycleMap, cycleMap, cycleLength_next, ← partialCycleMap_succ', partialCycleMap_succ,
    next_iterate_cycleLength]

/-- The cycle transformation at the predecessor of `j` is the conjugate of the one at `j` by the
inverse of the side-pairing map of the side leaving the predecessor. -/
theorem cycleMap_next_symm (j : Fin n) :
    σ.cycleMap (σ.next.symm j) =
      (σ.map (σ.next.symm j))⁻¹ * σ.cycleMap j * σ.map (σ.next.symm j) := by
  have h := σ.cycleMap_next (σ.next.symm j)
  rw [Equiv.apply_symm_apply] at h
  simp [h, mul_assoc]

/-- A nonidentity cycle transformation at a vertex in `ℍ` is elliptic. Ideal vertices are
excluded: their cycle transformations instead fix a point of the projective boundary. -/
theorem isElliptic_of_cycleMap_eq {j : Fin n} {z : ℍ} (hz : P.vertex j = .inl z)
    (hj : σ.cycleMap j ≠ 1) {g : SL(2, ℝ)} (hg : (↑g : PSL(2, ℝ)) = σ.cycleMap j) :
    Matrix.GeneralLinearGroup.IsElliptic (Matrix.SpecialLinearGroup.mapGL ℝ g) := by
  have hfix := σ.cycleMap_smul_vertex j
  rw [hz, Sum.smul_inl, Sum.inl.injEq] at hfix
  exact Matrix.SpecialLinearGroup.isElliptic_of_smul_eq_self_of_ne_one
    (by rw [← pslMk_smul, hg, hfix]) (hg ▸ hj)

/-! ### Vertex cycles and angle sums -/

/-- The vertex cycle through `j`: the orbit of `j` under the successor. -/
def cycle (j : Fin n) : Finset (Fin n) :=
  Finset.univ.filter fun i ↦ σ.next.SameCycle j i

/-- A vertex `i` is on the cycle through `j` if and only if it is an iterated successor of `j`. -/
theorem mem_cycle_iff (j i : Fin n) : i ∈ σ.cycle j ↔ ∃ m, σ.next^[m] j = i := by
  simp only [cycle, Finset.mem_filter, Finset.mem_univ, true_and, ← Equiv.Perm.coe_pow]
  exact ⟨Equiv.Perm.SameCycle.exists_nat_pow_eq, fun ⟨m, hm⟩ ↦
    hm ▸ Equiv.Perm.sameCycle_pow_right.2 (.refl _ _)⟩

/-- A vertex lies on its own cycle. -/
theorem self_mem_cycle (j : Fin n) : j ∈ σ.cycle j :=
  (σ.mem_cycle_iff j j).2 ⟨0, rfl⟩

/-- The cycle does not depend on the starting vertex. -/
theorem cycle_next (j : Fin n) : σ.cycle (σ.next j) = σ.cycle j := by
  ext i
  simp only [cycle, Finset.mem_filter, Finset.mem_univ, true_and]
  exact Equiv.Perm.sameCycle_apply_left

/-- The cycle does not depend on the starting vertex, in the simp-normal form of `next`. -/
@[simp]
theorem cycle_pair_add_one (j : Fin n) : σ.cycle (σ.pair j + 1) = σ.cycle j := by
  rw [← next_apply, cycle_next]

/-- The cycle through `j` is enumerated by the first `cycleLength j` successors of `j`. -/
theorem cycle_eq_image (j : Fin n) :
    σ.cycle j = (Finset.range (σ.cycleLength j)).image fun m ↦ σ.next^[m] j := by
  ext i
  rw [mem_cycle_iff, Finset.mem_image]
  constructor
  · rintro ⟨m, rfl⟩
    exact ⟨m % σ.cycleLength j, Finset.mem_range.2 (Nat.mod_lt _ (σ.cycleLength_pos j)),
      Function.iterate_mod_minimalPeriod_eq⟩
  · rintro ⟨m, -, h⟩
    exact ⟨m, h⟩

/-- The number of vertices on the cycle through `j` is its length. -/
theorem card_cycle (j : Fin n) : (σ.cycle j).card = σ.cycleLength j := by
  rw [cycle_eq_image, Finset.card_image_of_injOn (Finset.coe_range _ ▸
    Function.iterate_injOn_Iio_minimalPeriod), Finset.card_range]

/-- The angle sum along the vertex cycle through `j`: the sum of the interior angles of `P` at
the vertices of the cycle. -/
def cycleAngleSum (j : Fin n) : ℝ :=
  ∑ i ∈ σ.cycle j, P.interiorAngle i

-- The body of `cycleAngleSum` is not `@[expose]`d, so downstream modules rewrite with this.
/-- The angle sum along a cycle, unfolded. -/
theorem cycleAngleSum_def (j : Fin n) : σ.cycleAngleSum j = ∑ i ∈ σ.cycle j, P.interiorAngle i :=
  (rfl)

/-- The angle sum does not depend on the starting vertex of the cycle. -/
theorem cycleAngleSum_next (j : Fin n) : σ.cycleAngleSum (σ.next j) = σ.cycleAngleSum j := by
  rw [cycleAngleSum, cycleAngleSum, cycle_next]

/-- The angle sum does not depend on the starting vertex, in the simp-normal form of `next`. -/
@[simp]
theorem cycleAngleSum_pair_add_one (j : Fin n) :
    σ.cycleAngleSum (σ.pair j + 1) = σ.cycleAngleSum j := by
  rw [← next_apply, cycleAngleSum_next]

/-- The angle sum along a cycle is nonnegative. -/
theorem cycleAngleSum_nonneg (j : Fin n) : 0 ≤ σ.cycleAngleSum j :=
  Finset.sum_nonneg fun i _ ↦ P.interiorAngle_nonneg i

/-- The angle sum along the cycle of a finite vertex is positive. -/
theorem cycleAngleSum_pos_of_isLeft_vertex {j : Fin n} (hj : (P.vertex j).isLeft) :
    0 < σ.cycleAngleSum j := by
  rw [cycleAngleSum_def]
  exact Finset.sum_pos' (fun i _ ↦ P.interiorAngle_nonneg i)
    ⟨j, σ.self_mem_cycle j, P.interiorAngle_pos_of_isLeft_vertex hj⟩

/-- The angle sum as a sum over the first `cycleLength j` successors of `j`. -/
theorem cycleAngleSum_eq_sum_range (j : Fin n) :
    σ.cycleAngleSum j =
      ∑ m ∈ Finset.range (σ.cycleLength j), P.interiorAngle (σ.next^[m] j) := by
  rw [cycleAngleSum, cycle_eq_image, Finset.sum_image (Finset.coe_range _ ▸
    Function.iterate_injOn_Iio_minimalPeriod)]

/-- Summing the interior angles over `t` circuits of the cycle through `j` gives `t` times its
angle sum. -/
theorem sum_range_mul_cycleLength_interiorAngle (j : Fin n) (t : ℕ) :
    ∑ m ∈ Finset.range (t * σ.cycleLength j), P.interiorAngle (σ.next^[m] j) =
      t * σ.cycleAngleSum j := by
  induction t with
  | zero => simp
  | succ t ih =>
    have hper : σ.next^[t * σ.cycleLength j] j = j := by
      rw [cycleLength_def]
      exact ((Function.isPeriodicPt_minimalPeriod σ.next j).const_mul t).eq
    rw [Nat.succ_mul, Finset.sum_range_add, ih, Nat.cast_succ, add_mul, one_mul,
      σ.cycleAngleSum_eq_sum_range]
    congr 1
    refine Finset.sum_congr rfl fun l _ ↦ ?_
    rw [add_comm, Function.iterate_add_apply, hper]

end SidePairing

end ConvexPolygon

namespace CompactConvexPolygon

variable {n : ℕ} [NeZero n] {P : CompactConvexPolygon n}

/-- A vertex cycle of a compact convex polygon has positive angle sum. -/
theorem cycleAngleSum_pos (σ : P.toConvexPolygon.SidePairing) (j : Fin n) :
    0 < σ.cycleAngleSum j := by
  exact σ.cycleAngleSum_pos_of_isLeft_vertex (by simp)

end CompactConvexPolygon

end TauCeti.UpperHalfPlane
