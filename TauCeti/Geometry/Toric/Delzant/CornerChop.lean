/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.Filter.Basic
public import Mathlib.Topology.Order.Basic
public import TauCeti.Geometry.Toric.Algebraic.Lattice.Basic
public import TauCeti.Geometry.Toric.Delzant.Basic
public import TauCeti.Geometry.Toric.Delzant.Simplex

import Mathlib.LinearAlgebra.Dimension.OrzechProperty
import TauCeti.Algebra.Group.Pi.Lemmas
import Mathlib.Order.Filter.Finite
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Order.OrderClosed

/-!
# Corner chops of Delzant polytopes

Let `Δ = {x | c j ≤ ⟨x, u j⟩ for every j}` be a facet presentation in an integral lattice
`i : N →+ V`, and let `v` be a smooth vertex of `Δ`, at which the facets indexed by a finite set
`s` meet. Chopping the corner `v` off `Δ` at depth `ε` adds one facet, with inward normal the sum
`∑ j ∈ s, u j` of the normals at `v` and support constant `∑ j ∈ s, c j + ε`
(`TauCeti.Toric.cornerChopNormal u s` and `TauCeti.Toric.cornerChopSupport c s ε`, indexed by
`Option ι`, the new facet being `none`). The chopped polyhedron is

`{x ∈ Δ | ε ≤ ∑ j ∈ s, (⟨x, u j⟩ - c j)}`

(`TauCeti.Toric.mem_facetPolyhedron_cornerChop_iff`). For `ε > 0` it no longer contains `v`
(`TauCeti.Toric.notMem_facetPolyhedron_cornerChop`). On the symplectic side, chopping a vertex of
the moment polytope of a symplectic toric manifold corresponds to the toric symplectic blowup of
the fixed point over that vertex, with a ball whose size is set by `ε`. For instance, chopping a
corner of the triangle of `ℂP²` gives a Hirzebruch trapezoid, the moment polytope of the blowup
of `ℂP²` at a point. This file treats the polytopes only; the Betti numbers and volumes of the
corresponding Delzant quotients are in `TauCeti.Geometry.Toric.Delzant.Quotient.Topology` and
`TauCeti.Geometry.Toric.Delzant.Quotient.Volume`.

**Small corner chops of a Delzant polytope are Delzant**
(`TauCeti.Toric.IsDelzant.eventually_isDelzant_cornerChop`): in dimension at least two, every
sufficiently small depth `ε > 0` gives a Delzant polytope. Write `y j = ⟨x, u j⟩ - c j` for the
coordinates of `x` relative to the corner `v`; since the normals `u j` at `v` form a basis of the
lattice, the `y j` are affine coordinates on `V*` vanishing at `v`.

* A vertex of the chopped polytope off the new facet is a vertex of `Δ`, with the same active
  constraints, so it is smooth.
* For small `ε`, the constraints of `Δ` inactive at `v` stay inactive on the small simplex
  `{y j ≥ 0, ∑ j, y j ≤ ε}` near `v`. A vertex `x` on the new facet `∑ j, y j = ε` therefore has
  exactly one nonzero coordinate `y j₀`: if `y j₀` and `y j₁` were both nonzero, the coordinate
  difference `y j₀ - y j₁` would be a nonzero functional vanishing on all active normals. Its active
  normals are `∑ j ∈ s, u j` and the `u j` for `j ≠ j₀`, which generate the lattice since
  `u j₀ = ∑ j ∈ s, u j - ∑ j ≠ j₀, u j`, and so form a basis of it.
* Each old facet keeps a point lying only on it, once `ε` is less than the depth of such a point,
  and the barycentre of the new facet lies only on the new facet.

In dimension one the chop translates a facet, and the old facet becomes redundant, so the
dimension hypothesis is needed. The argument needs only that the constraints inactive at `v` stay
inactive on the simplex `{y j ≥ 0, ∑ j, y j ≤ ε}` and that each old facet keeps a point lying only
on it beyond depth `ε`, so the same holds at every depth with these two properties
(`TauCeti.Toric.IsDelzant.isDelzant_cornerChop`).

**The vertices of a corner chop.** At such a depth the chop replaces the vertex `v` by the
`n = dim V` points at depth `ε` on the edges from `v`, at which one coordinate `y j₀` is `ε` and
the others vanish
(`TauCeti.Toric.IsSmoothVertex.mem_extremePoints_facetPolyhedron_cornerChop_iff`): every other
vertex of `Δ` lies deeper than `ε`, since near the corner only constraints in `s` can be active,
and fewer than `n` of them do not determine a point. So the chopped polytope has `n - 1` more
vertices than `Δ` (`TauCeti.Toric.IsSmoothVertex.ncard_extremePoints_facetPolyhedron_cornerChop`).
On the symplectic side, the toric blowup replaces the fixed point over `v` by `n` fixed points on
the exceptional divisor `ℂPⁿ⁻¹`.

**The blown-up projective space.** For the corner `0` of the standard simplex of size `a` in `ℝⁿ`,
the moment polytope of `ℂPⁿ`, both properties hold at every depth `0 < ε < a` when `n ≥ 2`. The
chopped simplex `{0 ≤ x(eₖ), ε ≤ ∑ k, x(eₖ) ≤ a}`, the moment polytope of `ℂPⁿ` blown up at a
point, is therefore Delzant (`TauCeti.Toric.isDelzant_simplex_cornerChop`), with `2 n` vertices
(`TauCeti.Toric.ncard_extremePoints_facetPolyhedron_simplex_cornerChop`).

## Main definitions

* `TauCeti.Toric.cornerChopNormal u s`: the facet normals after chopping the corner where the
  facets in `s` meet.
* `TauCeti.Toric.cornerChopSupport c s ε`: the support constants after chopping that corner at
  depth `ε`.

## Main results

* `TauCeti.Toric.mem_facetPolyhedron_cornerChop_iff`: the chopped polyhedron.
* `TauCeti.Toric.some_mem_activeSet_cornerChop_iff`,
  `TauCeti.Toric.none_mem_activeSet_cornerChop_iff`: its old and new facets.
* `TauCeti.Toric.notMem_facetPolyhedron_cornerChop`: the chopped corner is removed.
* `TauCeti.Toric.IsSmoothVertex.exists_coord`: coordinates relative to a smooth vertex.
* `TauCeti.Toric.IsSmoothVertex.eventually_forall_mem_facetPolyhedron`: the small simplex at a
  smooth vertex lies in the polyhedron.
* `TauCeti.Toric.IsSmoothVertex.eventually_forall_lt_apply`: the constraints inactive at a smooth
  vertex stay inactive on the small simplex there.
* `TauCeti.Toric.IsDelzant.isDelzant_cornerChop`,
  `TauCeti.Toric.IsDelzant.eventually_isDelzant_cornerChop`: corner chops of a Delzant polytope at
  a vertex are Delzant polytopes, at every small depth.
* `TauCeti.Toric.IsSmoothVertex.mem_extremePoints_facetPolyhedron_cornerChop_iff`,
  `TauCeti.Toric.IsSmoothVertex.ncard_extremePoints_facetPolyhedron_cornerChop`,
  `TauCeti.Toric.IsSmoothVertex.eventually_ncard_extremePoints_facetPolyhedron_cornerChop`: the
  vertices of a corner chop, and their number.
* `TauCeti.Toric.isDelzant_simplex_cornerChop`,
  `TauCeti.Toric.ncard_extremePoints_facetPolyhedron_simplex_cornerChop`: the moment polytope of
  `ℂPⁿ` blown up at a point is Delzant and has `2 n` vertices.

## References

* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Section 28.
* V. Guillemin, *Moment Maps and Combinatorial Invariants of Hamiltonian `T^n`-spaces*,
  Birkhäuser, 1994, Chapter 1.
-/

public section

noncomputable section

open Set Filter Topology

namespace TauCeti.Toric

variable {ι N V : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {u : ι → N} {c : ι → ℝ}

/-- The inward facet normals after chopping the corner where the facets indexed by `s` meet: the
old normals `u j`, indexed by `some j`, and the new normal `∑ j ∈ s, u j`, indexed by `none`. -/
def cornerChopNormal (u : ι → N) (s : Finset ι) : Option ι → N
  | none => ∑ j ∈ s, u j
  | some j => u j

/-- The support constants after chopping the corner where the facets indexed by `s` meet, at
depth `ε`: the old constants `c j`, indexed by `some j`, and `∑ j ∈ s, c j + ε` for the new
facet, indexed by `none`. -/
def cornerChopSupport (c : ι → ℝ) (s : Finset ι) (ε : ℝ) : Option ι → ℝ
  | none => ∑ j ∈ s, c j + ε
  | some j => c j

@[simp]
theorem cornerChopNormal_none (u : ι → N) (s : Finset ι) :
    cornerChopNormal u s none = ∑ j ∈ s, u j :=
  (rfl)

@[simp]
theorem cornerChopNormal_some (u : ι → N) (s : Finset ι) (j : ι) :
    cornerChopNormal u s (some j) = u j :=
  (rfl)

@[simp]
theorem cornerChopSupport_none (c : ι → ℝ) (s : Finset ι) (ε : ℝ) :
    cornerChopSupport c s ε none = ∑ j ∈ s, c j + ε :=
  (rfl)

@[simp]
theorem cornerChopSupport_some (c : ι → ℝ) (s : Finset ι) (ε : ℝ) (j : ι) :
    cornerChopSupport c s ε (some j) = c j :=
  (rfl)

variable {s : Finset ι} {ε : ℝ} {x : StrongDual ℝ V}

-- The three characterisations below have `high` priority so that `simp` reaches them before the
-- general `mem_facetPolyhedron` and `mem_activeSet` unfold their left-hand sides.

/-- **The chopped polyhedron.** Chopping the corner where the facets in `s` meet at depth `ε`
keeps the points of the polyhedron whose coordinates `⟨x, u j⟩ - c j`, for `j ∈ s`, sum to at
least `ε`. -/
@[simp high]
theorem mem_facetPolyhedron_cornerChop_iff :
    x ∈ facetPolyhedron i (cornerChopNormal u s) (cornerChopSupport c s ε) ↔
      x ∈ facetPolyhedron i u c ∧ ε ≤ ∑ j ∈ s, (x (i (u j)) - c j) := by
  simp only [mem_facetPolyhedron, Option.forall, cornerChopNormal_none, cornerChopSupport_none,
    cornerChopNormal_some, cornerChopSupport_some, map_sum, Finset.sum_sub_distrib,
    le_sub_iff_add_le']
  exact and_comm

theorem facetPolyhedron_cornerChop_subset :
    facetPolyhedron i (cornerChopNormal u s) (cornerChopSupport c s ε) ⊆ facetPolyhedron i u c :=
  fun _ hx ↦ (mem_facetPolyhedron_cornerChop_iff.1 hx).1

/-- An old facet `j` of the chopped polyhedron is active where it was active before. -/
@[simp high]
theorem some_mem_activeSet_cornerChop_iff {j : ι} :
    some j ∈ activeSet (facetPairing i (cornerChopNormal u s)) (cornerChopSupport c s ε) x ↔
      j ∈ activeSet (facetPairing i u) c x := by
  simp

/-- The new facet of the chopped polyhedron is where the coordinates `⟨x, u j⟩ - c j`, for
`j ∈ s`, sum to `ε`. -/
@[simp high]
theorem none_mem_activeSet_cornerChop_iff :
    none ∈ activeSet (facetPairing i (cornerChopNormal u s)) (cornerChopSupport c s ε) x ↔
      ∑ j ∈ s, (x (i (u j)) - c j) = ε := by
  simp only [mem_activeSet, facetPairing_apply, cornerChopNormal_none, cornerChopSupport_none,
    map_sum, Finset.sum_sub_distrib]
  constructor <;> intro h <;> linarith

/-- **The corner is cut off.** For `ε > 0`, a point at which all the facets in `s` are active does
not lie in the polyhedron chopped at depth `ε`. -/
theorem notMem_facetPolyhedron_cornerChop {v : StrongDual ℝ V}
    (hs : (s : Set ι) ⊆ activeSet (facetPairing i u) c v) (hε : 0 < ε) :
    v ∉ facetPolyhedron i (cornerChopNormal u s) (cornerChopSupport c s ε) := by
  intro hv
  have h0 : ∑ j ∈ s, (v (i (u j)) - c j) = 0 :=
    Finset.sum_eq_zero fun j hj ↦ sub_eq_zero.2 (by simpa using hs hj)
  linarith [(mem_facetPolyhedron_cornerChop_iff.1 hv).2]

/-! ### Coordinates at a smooth vertex -/

section Coordinates

variable {v : StrongDual ℝ V} {w : ι → StrongDual ℝ V}

/-- The facets in `s`, active at `v`, pass through `v`. -/
private theorem apply_eq_of_coe_eq_activeSet
    (hs : (s : Set ι) = activeSet (facetPairing i u) c v) : ∀ j ∈ s, v (i (u j)) = c j :=
  fun j hj ↦ by rwa [← Finset.mem_coe, hs, mem_activeSet, facetPairing_apply] at hj

/-- At a smooth vertex there are as many active facets as the rank of the lattice. -/
private theorem card_eq_finrank_of_isSmoothVertex (hv : IsSmoothVertex i u c v)
    (hs : (s : Set ι) = activeSet (facetPairing i u) c v) : s.card = Module.finrank ℤ N := by
  rw [← hv.ncard_activeSet, ← hs, ncard_coe_finset]

/-- If all the coordinates `⟨x, u j⟩ - c j`, `j ∈ s`, but the `j₀`-th vanish, their sum is the
`j₀`-th. -/
private theorem sum_sub_eq_of_forall_ne {j₀ : ι} (hj₀ : j₀ ∈ s)
    (h : ∀ j ∈ s, j ≠ j₀ → x (i (u j)) = c j) :
    ∑ j ∈ s, (x (i (u j)) - c j) = x (i (u j₀)) - c j₀ :=
  Finset.sum_eq_single_of_mem j₀ hj₀ fun k hk hkj ↦ by rw [h k hk hkj, sub_self]

/-- Evaluating a combination of the functionals `w j` dual to the normals `u j`, `j ∈ s`, on a
normal `u k` picks out the coefficient of `w k`. -/
private theorem sum_mul_apply_eq [DecidableEq ι]
    (hw : ∀ j ∈ s, ∀ k ∈ s, w j (i (u k)) = if j = k then 1 else 0) (a : ι → ℝ) {k : ι}
    (hk : k ∈ s) : ∑ j ∈ s, a j * w j (i (u k)) = a k := by
  rw [Finset.sum_congr rfl fun j hj ↦ by rw [hw j hj k hk, mul_ite, mul_one, mul_zero],
    Finset.sum_ite_eq', ite_eq_left hk]

/-- A functional `w j` dual to the normals `u k`, `k ∈ s`, takes the value `1` on their sum. -/
private theorem sum_apply_eq_one [DecidableEq ι]
    (hw : ∀ j ∈ s, ∀ k ∈ s, w j (i (u k)) = if j = k then 1 else 0) {j : ι} (hj : j ∈ s) :
    ∑ k ∈ s, w j (i (u k)) = 1 := by
  rw [Finset.sum_congr rfl fun k hk ↦ hw j hj k hk, Finset.sum_ite_eq, ite_eq_left hj]

/-- At a smooth vertex `v` of a presentation in an integral lattice, with active facets `s`, there
are functionals `w j` dual to the active normals, in which every point `x` of `V*` has the
coordinates `⟨x, u j⟩ - c j` relative to `v`. -/
theorem IsSmoothVertex.exists_coord [DecidableEq ι] (hi : IsIntegralLattice i)
    (hv : IsSmoothVertex i u c v) (hs : (s : Set ι) = activeSet (facetPairing i u) c v) :
    ∃ w : ι → StrongDual ℝ V, (∀ j ∈ s, ∀ k ∈ s, w j (i (u k)) = if j = k then 1 else 0) ∧
      ∀ x : StrongDual ℝ V, x = v + ∑ j ∈ s, (x (i (u j)) - c j) • w j := by
  obtain ⟨b, hb⟩ := isSmoothVertex_def.1 hv
  let b' := b.reindex (Equiv.subtypeEquivRight (p := (· ∈ activeSet (facetPairing i u) c v))
    (q := (· ∈ (s : Set ι))) fun _ ↦ by rw [hs])
  let B := hi.isBaseChange.basis b'
  have hB (j : (s : Set ι)) : B j = i (u j) := by
    simpa [B, b', hb] using hi.isBaseChange.basis_apply b' j
  have := Module.Finite.of_basis B
  let w (j : ι) : StrongDual ℝ V :=
    if h : j ∈ s then LinearMap.toContinuousLinearMap (B.coord ⟨j, h⟩) else 0
  have hw (j) (hj : j ∈ s) (k) (hk : k ∈ s) : w j (i (u k)) = if j = k then 1 else 0 := by
    rw [← hB ⟨k, hk⟩]
    simp only [w, dite_eq_left hj, LinearMap.coe_toContinuousLinearMap', Module.Basis.coord_apply,
      Module.Basis.repr_self, Finsupp.single_apply, Subtype.mk.injEq]
    exact if_congr eq_comm rfl rfl
  refine ⟨w, hw, fun x ↦ ContinuousLinearMap.coe_injective (B.ext fun k ↦ ?_)⟩
  obtain ⟨k, hk⟩ := k
  simp only [ContinuousLinearMap.coe_coe, add_apply,
    sum_apply, smul_apply, smul_eq_mul, hB]
  rw [sum_mul_apply_eq hw _ hk, ← apply_eq_of_coe_eq_activeSet hs k hk]
  ring

/-- **Small depths.** At a point `v` of the polyhedron with active facets `s`, every sufficiently
small `ε` is small compared with the slack of every constraint inactive at `v`, which is
positive. -/
private theorem eventually_mul_sum_abs_lt [Finite ι] (hvP : v ∈ facetPolyhedron i u c)
    (hs : (s : Set ι) = activeSet (facetPairing i u) c v) :
    ∀ᶠ ε in 𝓝 (0 : ℝ), ∀ k ∉ s, ε * ∑ j ∈ s, |w j (i (u k))| < v (i (u k)) - c k := by
  refine eventually_all.2 fun k ↦ ?_
  by_cases hk : k ∈ s
  · exact Eventually.of_forall fun _ h ↦ absurd hk h
  have hslack : 0 < v (i (u k)) - c k := by
    refine sub_pos.2 ((mem_facetPolyhedron.1 hvP k).lt_of_ne fun h ↦ hk ?_)
    rw [← Finset.mem_coe, hs, mem_activeSet, facetPairing_apply, h]
  exact ((continuous_id.mul continuous_const).tendsto' 0 0 (by simp)).eventually_lt_const
    hslack |>.mono fun ε hε _ ↦ hε

variable (hx : ∀ x : StrongDual ℝ V, x = v + ∑ j ∈ s, (x (i (u j)) - c j) • w j)
include hx

/-- The value of a point on any lattice vector, in coordinates relative to the corner. -/
private theorem apply_eq_add_sum (x : StrongDual ℝ V) (n : V) :
    x n = v n + ∑ j ∈ s, (x (i (u j)) - c j) * w j n := by
  conv_lhs => rw [hx x]
  simp [sum_apply]

/-- A point of the polyhedron whose coordinates relative to the corner all vanish is the
corner. -/
private theorem eq_of_forall_apply_eq (h : ∀ j ∈ s, x (i (u j)) = c j) : x = v := by
  rw [hx x, Finset.sum_eq_zero fun j hj ↦ by rw [h j hj, sub_self, zero_smul], add_zero]

/-- A functional vanishing on the normals `u j`, `j ∈ s`, at the corner vanishes. -/
private theorem eq_zero_of_forall_apply_eq_zero (hvs : ∀ j ∈ s, v (i (u j)) = c j)
    {f : StrongDual ℝ V} (hf : ∀ j ∈ s, f (i (u j)) = 0) : f = 0 :=
  add_eq_left.1 (eq_of_forall_apply_eq hx fun j hj ↦ by rw [add_apply, hvs j hj, hf j hj, add_zero])

/-- A point other than the corner, with nonnegative coordinates relative to the corner, has
positive depth: its coordinates have positive sum. -/
private theorem sum_sub_pos (hxs : ∀ j ∈ s, c j ≤ x (i (u j))) (hxv : x ≠ v) :
    0 < ∑ j ∈ s, (x (i (u j)) - c j) := by
  have hnn (j) (hj : j ∈ s) : 0 ≤ x (i (u j)) - c j := sub_nonneg.2 (hxs j hj)
  refine (Finset.sum_nonneg hnn).lt_of_ne fun h ↦ hxv (eq_of_forall_apply_eq hx fun j hj ↦ ?_)
  exact sub_eq_zero.1 ((Finset.sum_eq_zero_iff_of_nonneg hnn).1 h.symm j hj)

/-- **Slack on the small simplex at the corner.** If `ε` is small compared with the slack of every
constraint inactive at the corner, then every constraint inactive at the corner stays inactive at
the points of the simplex `{y j ≥ 0, ∑ j, y j ≤ ε}`. -/
private theorem lt_apply_of_sum_le
    (hε : ∀ k ∉ s, ε * ∑ j ∈ s, |w j (i (u k))| < v (i (u k)) - c k)
    (hxs : ∀ j ∈ s, c j ≤ x (i (u j))) (hxε : ∑ j ∈ s, (x (i (u j)) - c j) ≤ ε) {k : ι}
    (hk : k ∉ s) : c k < x (i (u k)) := by
  set S := ∑ j ∈ s, |w j (i (u k))|
  have hS : 0 ≤ S := Finset.sum_nonneg fun j _ ↦ abs_nonneg _
  have hlow : -(S * ∑ j ∈ s, (x (i (u j)) - c j)) ≤
      ∑ j ∈ s, (x (i (u j)) - c j) * w j (i (u k)) := by
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_le_sum fun j hj ↦ ?_
    have hy : 0 ≤ x (i (u j)) - c j := sub_nonneg.2 (hxs j hj)
    have hj' : |w j (i (u k))| ≤ S :=
      Finset.single_le_sum (f := fun j ↦ |w j (i (u k))|) (fun _ _ ↦ abs_nonneg _) hj
    nlinarith [neg_abs_le (w j (i (u k)))]
  have := mul_le_mul_of_nonneg_left hxε hS
  rw [apply_eq_add_sum hx]
  linarith [hε k hk]

end Coordinates

/-- **The small simplex at a smooth vertex.** Let `v` be a smooth vertex of the polyhedron
`Δ = {x | c j ≤ ⟨x, u j⟩}` in an integral lattice, at which the facets indexed by `s` meet. Then for
every sufficiently small `ε`, the simplex `{y j ≥ 0, ∑ j, y j ≤ ε}` in the coordinates
`y j = ⟨x, u j⟩ - c j`, `j ∈ s`, relative to `v` lies in `Δ`: the constraints inactive at `v` stay
inactive on it. -/
theorem IsSmoothVertex.eventually_forall_mem_facetPolyhedron [Finite ι] (hi : IsIntegralLattice i)
    {v : StrongDual ℝ V} (hv : IsSmoothVertex i u c v) (hvP : v ∈ facetPolyhedron i u c)
    (hs : (s : Set ι) = activeSet (facetPairing i u) c v) :
    ∀ᶠ ε in 𝓝 0, ∀ x : StrongDual ℝ V, (∀ j ∈ s, c j ≤ x (i (u j))) →
      ∑ j ∈ s, (x (i (u j)) - c j) ≤ ε → x ∈ facetPolyhedron i u c := by
  classical
  obtain ⟨w, -, hx⟩ := hv.exists_coord hi hs
  filter_upwards [eventually_mul_sum_abs_lt (w := w) hvP hs] with ε hε x hxs hxε
  refine mem_facetPolyhedron.2 fun k ↦ ?_
  by_cases hk : k ∈ s
  · exact hxs k hk
  · exact (lt_apply_of_sum_le hx hε hxs hxε hk).le

/-- **Slack near a smooth vertex.** Let `v` be a smooth vertex of the polyhedron
`Δ = {x | c j ≤ ⟨x, u j⟩}` in an integral lattice, at which the facets indexed by `s` meet. Then for
every sufficiently small `ε`, the constraints inactive at `v` stay inactive on the simplex
`{y j ≥ 0, ∑ j, y j ≤ ε}` in the coordinates `y j = ⟨x, u j⟩ - c j`, `j ∈ s`, relative to `v`. -/
theorem IsSmoothVertex.eventually_forall_lt_apply [Finite ι] (hi : IsIntegralLattice i)
    {v : StrongDual ℝ V} (hv : IsSmoothVertex i u c v) (hvP : v ∈ facetPolyhedron i u c)
    (hs : (s : Set ι) = activeSet (facetPairing i u) c v) :
    ∀ᶠ ε in 𝓝 0, ∀ x : StrongDual ℝ V, (∀ j ∈ s, c j ≤ x (i (u j))) →
      ∑ j ∈ s, (x (i (u j)) - c j) ≤ ε → ∀ k ∉ s, c k < x (i (u k)) := by
  classical
  obtain ⟨w, -, hx⟩ := hv.exists_coord hi hs
  filter_upwards [eventually_mul_sum_abs_lt (w := w) hvP hs] with ε hε x hxs hxε k hk
  exact lt_apply_of_sum_le hx hε hxs hxε hk

/-! ### Vertices of the chopped polytope -/

section Vertices

/-- Off the new facet, the constraints active on the chopped polytope are the old ones. -/
private theorem activeSet_cornerChop_of_none_notMem
    (hnone : none ∉
      activeSet (facetPairing i (cornerChopNormal u s)) (cornerChopSupport c s ε) x) :
    activeSet (facetPairing i (cornerChopNormal u s)) (cornerChopSupport c s ε) x =
      some '' activeSet (facetPairing i u) c x := by
  ext o
  cases o with
  | none => simpa using hnone
  | some j => simp

variable [Finite ι] {v : StrongDual ℝ V} {w : ι → StrongDual ℝ V}

/-- A vertex of the chopped polytope off the new facet is a vertex of the original polytope. -/
private theorem mem_extremePoints_of_none_notMem
    (hx : x ∈ (facetPolyhedron i (cornerChopNormal u s) (cornerChopSupport c s ε)).extremePoints ℝ)
    (hnone : none ∉
      activeSet (facetPairing i (cornerChopNormal u s)) (cornerChopSupport c s ε) x) :
    x ∈ (facetPolyhedron i u c).extremePoints ℝ := by
  obtain ⟨hxP, hker⟩ := mem_extremePoints_facetPolyhedron_iff.1 hx
  refine mem_extremePoints_facetPolyhedron_iff.2
    ⟨facetPolyhedron_cornerChop_subset hxP, fun f hf ↦ hker f fun o ho ↦ ?_⟩
  rw [activeSet_cornerChop_of_none_notMem hnone] at ho
  obtain ⟨j, hj, rfl⟩ := ho
  exact hf j hj

/-- A vertex of the chopped polytope off the new facet is a smooth vertex, when every vertex of the
original polytope is smooth. -/
private theorem isSmoothVertex_cornerChop_of_none_notMem
    (hsmooth : ∀ x ∈ (facetPolyhedron i u c).extremePoints ℝ, IsSmoothVertex i u c x)
    (hx : x ∈ (facetPolyhedron i (cornerChopNormal u s) (cornerChopSupport c s ε)).extremePoints ℝ)
    (hnone : none ∉
      activeSet (facetPairing i (cornerChopNormal u s)) (cornerChopSupport c s ε) x) :
    IsSmoothVertex i (cornerChopNormal u s) (cornerChopSupport c s ε) x := by
  obtain ⟨hli, hsp⟩ :=
    isSmoothVertex_iff_linearIndepOn.1 (hsmooth x (mem_extremePoints_of_none_notMem hx hnone))
  rw [isSmoothVertex_iff_linearIndepOn, activeSet_cornerChop_of_none_notMem hnone, image_image]
  exact ⟨hli.image_of_comp some (cornerChopNormal u s), hsp⟩

-- The hypothesis `hε` says that the depth `ε` is small: the constraints inactive at the corner stay
-- inactive on the simplex `{y j ≥ 0, ∑ j, y j ≤ ε}` in the coordinates `y j = ⟨x, u j⟩ - c j`.
variable [DecidableEq ι] (hw : ∀ j ∈ s, ∀ k ∈ s, w j (i (u k)) = if j = k then 1 else 0)
  (hε : ∀ x : StrongDual ℝ V, (∀ j ∈ s, c j ≤ x (i (u j))) → ∑ j ∈ s, (x (i (u j)) - c j) ≤ ε →
    ∀ k ∉ s, c k < x (i (u k)))
include hw hε

/-- At a vertex of the chopped polytope on the new facet, exactly one of the coordinates relative
to the corner is nonzero, and the active constraints are the new facet and the old facets in `s`
other than that coordinate's. -/
private theorem exists_activeSet_cornerChop_eq_image
    (hx' : x ∈ (facetPolyhedron i (cornerChopNormal u s) (cornerChopSupport c s ε)).extremePoints ℝ)
    (hε0 : 0 < ε) (hnone : ∑ j ∈ s, (x (i (u j)) - c j) = ε) :
    ∃ j₀ ∈ s, activeSet (facetPairing i (cornerChopNormal u s)) (cornerChopSupport c s ε) x =
      (fun j ↦ if j = j₀ then none else some j) '' s := by
  classical
  obtain ⟨hxP, hker⟩ := mem_extremePoints_facetPolyhedron_iff.1 hx'
  have hxΔ := mem_facetPolyhedron.1 (facetPolyhedron_cornerChop_subset hxP)
  -- Off `s`, the constraints are inactive near the corner.
  have hslack {k} (hk : k ∉ s) : c k < x (i (u k)) := hε x (fun j _ ↦ hxΔ j) hnone.le k hk
  -- Some coordinate is nonzero, since they sum to `ε > 0`.
  obtain ⟨j₀, hj₀, hj₀ne⟩ : ∃ j₀ ∈ s, x (i (u j₀)) ≠ c j₀ := by
    by_contra! h
    rw [Finset.sum_eq_zero fun j hj ↦ by rw [h j hj, sub_self]] at hnone
    exact hε0.ne hnone
  -- The active old constraints lie in `s`, other than `j₀`.
  have hact {k} (hk : x (i (u k)) = c k) : k ∈ s ∧ k ≠ j₀ :=
    ⟨by_contra fun hks ↦ (hslack hks).ne' hk, fun h ↦ hj₀ne (h ▸ hk)⟩
  -- Two nonzero coordinates would give the nonzero functional `w j₀ - w j₁` vanishing on all
  -- active normals.
  have huniq {j₁} (hj₁ : j₁ ∈ s) (hne : j₁ ≠ j₀) : x (i (u j₁)) = c j₁ := by
    by_contra hj₁ne
    have h0 := hker (w j₀ - w j₁) fun o ho ↦ ?_
    · have := congrArg (· (i (u j₀))) h0
      simp only [sub_apply, hw j₀ hj₀ j₀ hj₀, hw j₁ hj₁ j₀ hj₀,
        ite_eq_right hne, zero_apply] at this
      norm_num at this
    cases o with
    | none =>
      simp only [cornerChopNormal_none, map_sum, sub_apply]
      rw [Finset.sum_sub_distrib, sum_apply_eq_one hw hj₀, sum_apply_eq_one hw hj₁, sub_self]
    | some k =>
      have hk : x (i (u k)) = c k := by simpa using ho
      obtain ⟨hks, hk₀⟩ := hact hk
      have hk₁ : j₁ ≠ k := fun h ↦ hj₁ne (h ▸ hk)
      simp [hw j₀ hj₀ k hks, hw j₁ hj₁ k hks, hk₀.symm, hk₁]
  refine ⟨j₀, hj₀, Set.ext fun o ↦ ?_⟩
  cases o with
  | none =>
    simp only [none_mem_activeSet_cornerChop_iff, hnone, mem_image, Finset.mem_coe, true_iff]
    exact ⟨j₀, hj₀, ite_eq_left rfl⟩
  | some k =>
    simp only [mem_activeSet, facetPairing_apply, mem_image, Finset.mem_coe]
    constructor
    · intro hk
      obtain ⟨hks, hk₀⟩ := hact hk
      exact ⟨k, hks, ite_eq_right hk₀⟩
    · rintro ⟨k', hk', hkk'⟩
      split_ifs at hkk' with h
      cases hkk'
      exact huniq hk' h

/-- A vertex of the chopped polytope on the new facet is a smooth vertex. -/
private theorem isSmoothVertex_cornerChop_of_none_mem
    (hsp : Submodule.span ℤ (u '' s) = ⊤) (hcard : s.card ≤ Module.finrank ℤ N)
    (hx' : x ∈ (facetPolyhedron i (cornerChopNormal u s) (cornerChopSupport c s ε)).extremePoints ℝ)
    (hε0 : 0 < ε) (hnone : ∑ j ∈ s, (x (i (u j)) - c j) = ε) :
    IsSmoothVertex i (cornerChopNormal u s) (cornerChopSupport c s ε) x := by
  classical
  obtain ⟨j₀, hj₀, hA⟩ := exists_activeSet_cornerChop_eq_image hw hε hx' hε0 hnone
  set φ : ι → Option ι := fun j ↦ if j = j₀ then none else some j
  -- The new normal and the old normals in `s` other than `u j₀` generate the lattice.
  have hspan : ⊤ ≤ Submodule.span ℤ (range fun j : (s : Set ι) ↦ cornerChopNormal u s (φ j)) := by
    rw [← hsp, Submodule.span_le]
    rintro _ ⟨k, hk, rfl⟩
    have hmem (j) (hj : j ∈ s) : cornerChopNormal u s (φ j) ∈
        Submodule.span ℤ (range fun j : (s : Set ι) ↦ cornerChopNormal u s (φ j)) :=
      Submodule.subset_span ⟨⟨j, hj⟩, rfl⟩
    by_cases hk₀ : k = j₀
    · subst hk₀
      have hsum : u k = cornerChopNormal u s (φ k) -
          ∑ j ∈ s.erase k, cornerChopNormal u s (φ j) := by
        have h₁ (j) (hj : j ∈ s.erase k) : cornerChopNormal u s (φ j) = u j := by
          simp [φ, Finset.ne_of_mem_erase hj]
        rw [Finset.sum_congr rfl h₁]
        simp [φ, ← Finset.add_sum_erase s u hk]
      rw [SetLike.mem_coe, hsum]
      exact Submodule.sub_mem _ (hmem k hk)
        (Submodule.sum_mem _ fun j hj ↦ hmem j (Finset.mem_of_mem_erase hj))
    · simpa [φ, hk₀] using hmem k hk
  have hli : LinearIndepOn ℤ (cornerChopNormal u s ∘ φ) (s : Set ι) :=
    linearIndependent_of_top_le_span_of_card_le_finrank hspan (by simpa using hcard)
  rw [isSmoothVertex_iff_linearIndepOn, hA]
  refine ⟨hli.image_of_comp φ _, ?_⟩
  rw [image_image, image_eq_range]
  exact top_le_iff.1 hspan

variable (hx : ∀ x : StrongDual ℝ V, x = v + ∑ j ∈ s, (x (i (u j)) - c j) • w j)
include hx

/-- A vertex of the polyhedron other than the corner lies beyond the small simplex at the corner:
its coordinates relative to the corner sum to more than `ε`. -/
private theorem lt_sum_sub_of_mem_extremePoints {y : StrongDual ℝ V}
    (hy : y ∈ (facetPolyhedron i u c).extremePoints ℝ) (hyv : y ≠ v) :
    ε < ∑ j ∈ s, (y (i (u j)) - c j) := by
  by_contra! hle
  obtain ⟨hyP, hker⟩ := mem_extremePoints_facetPolyhedron_iff.1 hy
  -- Some coordinate `y j₀` is nonzero. Near the corner the active constraints at `y` lie in `s`,
  -- so the functional `w j₀` vanishes on all active normals, although it is nonzero.
  obtain ⟨j₀, hj₀, hne⟩ : ∃ j₀ ∈ s, y (i (u j₀)) ≠ c j₀ := by
    by_contra! h
    exact hyv (eq_of_forall_apply_eq hx h)
  have h0 := hker (w j₀) fun k hk ↦ ?_
  · simpa [hw j₀ hj₀ j₀ hj₀] using congrArg (· (i (u j₀))) h0
  rw [mem_activeSet, facetPairing_apply] at hk
  have hks : k ∈ s := by
    by_contra hks
    exact (hε y (fun j _ ↦ mem_facetPolyhedron.1 hyP j) hle k hks).ne' hk
  rw [hw j₀ hj₀ k hks, ite_eq_right_iff]
  rintro rfl
  exact absurd hk hne

end Vertices

/-! ### Corner chops of Delzant polytopes -/

/-- A point with the coordinates `ε / #s` relative to the corner lies only on the new facet. -/
private theorem exists_activeSet_cornerChop_eq_none [DecidableEq ι] {v : StrongDual ℝ V}
    {w : ι → StrongDual ℝ V}
    (hw : ∀ j ∈ s, ∀ k ∈ s, w j (i (u k)) = if j = k then 1 else 0)
    (hε : ∀ x : StrongDual ℝ V, (∀ j ∈ s, c j ≤ x (i (u j))) → ∑ j ∈ s, (x (i (u j)) - c j) ≤ ε →
      ∀ k ∉ s, c k < x (i (u k)))
    (hvs : ∀ j ∈ s, v (i (u j)) = c j) (hs : s.Nonempty) (hε0 : 0 < ε) :
    ∃ x ∈ facetPolyhedron i (cornerChopNormal u s) (cornerChopSupport c s ε),
      activeSet (facetPairing i (cornerChopNormal u s)) (cornerChopSupport c s ε) x = {none} := by
  classical
  have hn : (0 : ℝ) < s.card := Nat.cast_pos.2 hs.card_pos
  set z := v + (ε / s.card) • ∑ j ∈ s, w j
  have hz (k) (hk : k ∈ s) : z (i (u k)) = c k + ε / s.card := by
    simp only [z, add_apply, smul_apply, sum_apply, smul_eq_mul, hvs k hk, Finset.mul_sum]
    rw [sum_mul_apply_eq hw (fun _ ↦ ε / s.card) hk]
  have hzsum : ∑ j ∈ s, (z (i (u j)) - c j) = ε := by
    rw [Finset.sum_congr rfl fun j hj ↦ by rw [hz j hj, add_sub_cancel_left], Finset.sum_const,
      nsmul_eq_mul, mul_div_cancel₀ _ hn.ne']
  have hpos : 0 < ε / s.card := div_pos hε0 hn
  have hslack {k} (hk : k ∉ s) : c k < z (i (u k)) :=
    hε z (fun j hj ↦ by rw [hz j hj]; linarith) hzsum.le k hk
  refine ⟨z, mem_facetPolyhedron_cornerChop_iff.2 ⟨mem_facetPolyhedron.2 fun k ↦ ?_, hzsum.ge⟩,
    Set.ext fun o ↦ ?_⟩
  · by_cases hk : k ∈ s
    · rw [hz k hk]; linarith
    · exact (hslack hk).le
  · cases o with
    | none => simpa using none_mem_activeSet_cornerChop_iff.2 hzsum
    | some k =>
      rw [some_mem_activeSet_cornerChop_iff]
      simp only [mem_activeSet, facetPairing_apply, mem_singleton_iff, reduceCtorEq, iff_false]
      by_cases hk : k ∈ s
      · rw [hz k hk]; linarith
      · exact (hslack hk).ne'

/-- **Corner chops of a Delzant polytope are Delzant.** Let `Δ` be a Delzant polytope in an
integral lattice of positive rank, and `v` a vertex of `Δ`, at which the facets indexed by `s`
meet. Chop the corner `v` off `Δ` at a depth `ε > 0`, by the new facet
`∑ j ∈ s, (⟨x, u j⟩ - c j) = ε` with inward normal `∑ j ∈ s, u j`, such that

* the constraints of `Δ` inactive at `v` stay inactive on the simplex `{y j ≥ 0, ∑ j, y j ≤ ε}` in
  the coordinates `y j = ⟨x, u j⟩ - c j` relative to `v`, and
* each facet of `Δ` contains a point lying on no other facet whose coordinates sum to more than
  `ε`.

Then the chopped polytope is a Delzant polytope: the polytope of the toric symplectic blowup at
the fixed point over `v`. -/
theorem IsDelzant.isDelzant_cornerChop [Finite ι] (hi : IsIntegralLattice i)
    (hΔ : IsDelzant i u c) {v : StrongDual ℝ V} (hv : v ∈ (facetPolyhedron i u c).extremePoints ℝ)
    (hs : (s : Set ι) = activeSet (facetPairing i u) c v) (hV : 0 < Module.finrank ℝ V)
    (hε0 : 0 < ε)
    (hε : ∀ x : StrongDual ℝ V, (∀ j ∈ s, c j ≤ x (i (u j))) → ∑ j ∈ s, (x (i (u j)) - c j) ≤ ε →
      ∀ k ∉ s, c k < x (i (u k)))
    (hirr : ∀ j, ∃ y ∈ facetPolyhedron i u c, activeSet (facetPairing i u) c y = {j} ∧
      ε < ∑ k ∈ s, (y (i (u k)) - c k)) :
    IsDelzant i (cornerChopNormal u s) (cornerChopSupport c s ε) := by
  classical
  have hsv := hΔ.isSmoothVertex v hv
  obtain ⟨w, hw, -⟩ := hsv.exists_coord hi hs
  have hvs := apply_eq_of_coe_eq_activeSet hs
  have hcard := card_eq_finrank_of_isSmoothVertex hsv hs
  have hsp : Submodule.span ℤ (u '' s) = ⊤ := by
    rw [hs]; exact (isSmoothVertex_iff_linearIndepOn.1 hsv).2
  refine ⟨hΔ.isBounded.subset facetPolyhedron_cornerChop_subset, fun x hx' ↦ ?_, fun o ↦ ?_⟩
  · by_cases hnone : ∑ j ∈ s, (x (i (u j)) - c j) = ε
    · exact isSmoothVertex_cornerChop_of_none_mem hw hε hsp hcard.le hx' hε0 hnone
    · exact isSmoothVertex_cornerChop_of_none_notMem hΔ.isSmoothVertex hx' (by simpa using hnone)
  cases o with
  | none =>
    exact exists_activeSet_cornerChop_eq_none hw hε hvs
      (Finset.card_pos.1 (by rw [hcard, hi.finrank_eq]; exact hV)) hε0
  | some j =>
    obtain ⟨y, hyP, hyj, hεy⟩ := hirr j
    refine ⟨y, mem_facetPolyhedron_cornerChop_iff.2 ⟨hyP, hεy.le⟩, Set.ext fun o ↦ ?_⟩
    cases o with
    | none => simpa using hεy.ne'
    | some k => rw [some_mem_activeSet_cornerChop_iff, hyj]; simp

/-- **Small corner chops of a Delzant polytope are Delzant.** Let `Δ` be a Delzant polytope in an
integral lattice of rank at least two, and `v` a vertex of `Δ`, at which the facets indexed by
`s` meet. Then for every sufficiently small `ε > 0`, chopping the corner `v` off `Δ` at depth `ε`,
by the new facet `∑ j ∈ s, (⟨x, u j⟩ - c j) = ε` with inward normal `∑ j ∈ s, u j`, gives a
Delzant polytope. This is the polytope of the toric symplectic blowup at the fixed point over
`v`. -/
theorem IsDelzant.eventually_isDelzant_cornerChop [Finite ι] (hi : IsIntegralLattice i)
    (hΔ : IsDelzant i u c) {v : StrongDual ℝ V} (hv : v ∈ (facetPolyhedron i u c).extremePoints ℝ)
    (hs : (s : Set ι) = activeSet (facetPairing i u) c v) (hV : 2 ≤ Module.finrank ℝ V) :
    ∀ᶠ ε in 𝓝[>] 0, IsDelzant i (cornerChopNormal u s) (cornerChopSupport c s ε) := by
  classical
  have hsv := hΔ.isSmoothVertex v hv
  obtain ⟨w, -, hx⟩ := hsv.exists_coord hi hs
  have hcard := card_eq_finrank_of_isSmoothVertex hsv hs
  have hcard2 : 2 ≤ s.card := hcard ▸ hi.finrank_eq ▸ hV
  -- Points lying on only one old facet, and their (positive) depths relative to the corner.
  choose y hyP hyj using hΔ.irredundant
  have hdepth (j) : 0 < ∑ k ∈ s, (y j (i (u k)) - c k) := by
    refine sum_sub_pos hx (fun k _ ↦ mem_facetPolyhedron.1 (hyP j) k) fun hyv ↦ ?_
    -- Otherwise the corner would lie on the single facet `j`, while at least two meet there.
    have : s = {j} := Finset.coe_injective (by rw [hs, ← hyv, hyj j, Finset.coe_singleton])
    rw [this, Finset.card_singleton] at hcard2
    omega
  have h₁ : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ j, ε < ∑ k ∈ s, (y j (i (u k)) - c k) :=
    eventually_all.2 fun j ↦ (eventually_lt_nhds (hdepth j)).filter_mono nhdsWithin_le_nhds
  have h₂ := (hsv.eventually_forall_lt_apply hi (extremePoints_subset hv) hs).filter_mono
    (nhdsWithin_le_nhds (s := Ioi 0))
  filter_upwards [self_mem_nhdsWithin, h₁, h₂] with ε (hε0 : 0 < ε) hεy hε
  exact hΔ.isDelzant_cornerChop hi hv hs (by omega) hε0 hε fun j ↦ ⟨y j, hyP j, hyj j, hεy j⟩

/-! ### The vertices of a corner chop -/

/-- **The vertices of a corner chop.** Let `v` be a smooth vertex of `Δ` in an integral lattice, at
which the facets indexed by `s` meet, and chop the corner `v` off `Δ` at a depth `ε > 0` for which
the constraints of `Δ` inactive at `v` stay inactive on the simplex `{y j ≥ 0, ∑ j, y j ≤ ε}` in the
coordinates `y j = ⟨x, u j⟩ - c j` relative to `v`. The vertices of the chopped polytope are the
vertices of `Δ` other than `v`, together with the points at depth `ε` on the edges of `Δ` from `v`:
the points at which one coordinate `y j₀` is `ε` and the others vanish. -/
theorem IsSmoothVertex.mem_extremePoints_facetPolyhedron_cornerChop_iff [Finite ι]
    (hi : IsIntegralLattice i)
    {v : StrongDual ℝ V} (hv : IsSmoothVertex i u c v)
    (hs : (s : Set ι) = activeSet (facetPairing i u) c v) (hε0 : 0 < ε)
    (hε : ∀ x : StrongDual ℝ V, (∀ j ∈ s, c j ≤ x (i (u j))) → ∑ j ∈ s, (x (i (u j)) - c j) ≤ ε →
      ∀ k ∉ s, c k < x (i (u k))) :
    x ∈ (facetPolyhedron i (cornerChopNormal u s) (cornerChopSupport c s ε)).extremePoints ℝ ↔
      x ∈ (facetPolyhedron i u c).extremePoints ℝ ∧ x ≠ v ∨
        ∃ j₀ ∈ s, x (i (u j₀)) = c j₀ + ε ∧ ∀ j ∈ s, j ≠ j₀ → x (i (u j)) = c j := by
  classical
  obtain ⟨w, hw, hx⟩ := hv.exists_coord hi hs
  have hvs := apply_eq_of_coe_eq_activeSet hs
  constructor
  · intro hx'
    by_cases hnone : ∑ j ∈ s, (x (i (u j)) - c j) = ε
    · -- On the new facet, all coordinates but one vanish.
      obtain ⟨j₀, hj₀, hA⟩ := exists_activeSet_cornerChop_eq_image hw hε hx' hε0 hnone
      have hzero (j) (hj : j ∈ s) (hne : j ≠ j₀) : x (i (u j)) = c j := by
        have hmem : some j ∈
            activeSet (facetPairing i (cornerChopNormal u s)) (cornerChopSupport c s ε) x := by
          rw [hA]
          exact ⟨j, hj, by simp [hne]⟩
        rwa [some_mem_activeSet_cornerChop_iff, mem_activeSet, facetPairing_apply] at hmem
      refine Or.inr ⟨j₀, hj₀, ?_, hzero⟩
      rw [sum_sub_eq_of_forall_ne hj₀ hzero] at hnone
      linarith
    · -- Off the new facet, the vertices are those of `Δ`, and the corner is cut off.
      refine Or.inl ⟨mem_extremePoints_of_none_notMem hx' (by simpa using hnone), ?_⟩
      rintro rfl
      exact notMem_facetPolyhedron_cornerChop hs.subset hε0 (extremePoints_subset hx')
  · rintro (⟨hxΔ, hxv⟩ | ⟨j₀, hj₀, hxj₀, hxj⟩)
    · exact inter_extremePoints_subset_extremePoints_of_subset facetPolyhedron_cornerChop_subset
        ⟨mem_facetPolyhedron_cornerChop_iff.2 ⟨extremePoints_subset hxΔ,
          (lt_sum_sub_of_mem_extremePoints hw hε hx hxΔ hxv).le⟩, hxΔ⟩
    · -- A point on an edge at depth `ε` lies on the new facet and on the old facets in `s` other
      -- than `j₀`, and a functional vanishing on their normals vanishes on all the normals in `s`.
      have hxs (j) (hj : j ∈ s) : c j ≤ x (i (u j)) := by
        by_cases h : j = j₀
        · subst h; rw [hxj₀]; linarith
        · rw [hxj j hj h]
      have hsum : ∑ j ∈ s, (x (i (u j)) - c j) = ε := by
        rw [sum_sub_eq_of_forall_ne hj₀ hxj, hxj₀, add_sub_cancel_left]
      have hxP : x ∈ facetPolyhedron i u c := mem_facetPolyhedron.2 fun k ↦
        if hk : k ∈ s then hxs k hk else (hε x hxs hsum.le k hk).le
      refine mem_extremePoints_facetPolyhedron_iff.2
        ⟨mem_facetPolyhedron_cornerChop_iff.2 ⟨hxP, hsum.ge⟩, fun f hf ↦ ?_⟩
      have hrest (j) (hj : j ∈ s) (hne : j ≠ j₀) : f (i (u j)) = 0 := by
        simpa using hf (some j) (by simp [hxj j hj hne])
      refine eq_zero_of_forall_apply_eq_zero hx hvs fun j hj ↦ ?_
      by_cases h : j = j₀
      · subst h
        have h0 := hf none (none_mem_activeSet_cornerChop_iff.2 hsum)
        simp only [cornerChopNormal_none, map_sum] at h0
        rwa [Finset.sum_eq_single_of_mem j hj fun k hk hkj ↦ hrest k hk hkj] at h0
      · exact hrest j hj h

/-- **A corner chop has `n - 1` more vertices**, in dimension `n`. Let `v` be a smooth vertex of
the polytope `Δ` in an integral lattice, at which the facets indexed by `s` meet, and chop the
corner `v` off `Δ` at a depth `ε > 0` for which the constraints of `Δ` inactive at `v` stay
inactive on the simplex `{y j ≥ 0, ∑ j, y j ≤ ε}` in the coordinates `y j = ⟨x, u j⟩ - c j`
relative to `v`. The chop replaces the vertex `v` by the `n` points at depth `ε` on the edges from
`v`. -/
theorem IsSmoothVertex.ncard_extremePoints_facetPolyhedron_cornerChop [Finite ι]
    (hi : IsIntegralLattice i)
    {v : StrongDual ℝ V} (hv : IsSmoothVertex i u c v)
    (hvΔ : v ∈ (facetPolyhedron i u c).extremePoints ℝ)
    (hs : (s : Set ι) = activeSet (facetPairing i u) c v) (hε0 : 0 < ε)
    (hε : ∀ x : StrongDual ℝ V, (∀ j ∈ s, c j ≤ x (i (u j))) → ∑ j ∈ s, (x (i (u j)) - c j) ≤ ε →
      ∀ k ∉ s, c k < x (i (u k))) :
    ((facetPolyhedron i (cornerChopNormal u s) (cornerChopSupport c s ε)).extremePoints ℝ).ncard +
        1 = ((facetPolyhedron i u c).extremePoints ℝ).ncard + Module.finrank ℝ V := by
  classical
  obtain ⟨w, hw, hx⟩ := hv.exists_coord hi hs
  have hvs := apply_eq_of_coe_eq_activeSet hs
  -- The points at depth `ε` on the edges from `v` are the points `v + ε w j`, `j ∈ s`.
  have hedge (x : StrongDual ℝ V) :
      (∃ j₀ ∈ s, x (i (u j₀)) = c j₀ + ε ∧ ∀ j ∈ s, j ≠ j₀ → x (i (u j)) = c j) ↔
        x ∈ (fun j ↦ v + ε • w j) '' s := by
    constructor
    · rintro ⟨j₀, hj₀, hxj₀, hxj⟩
      refine ⟨j₀, hj₀, ?_⟩
      rw [hx x, Finset.sum_eq_single_of_mem j₀ hj₀ fun k hk hkj ↦ by
        rw [hxj k hk hkj, sub_self, zero_smul], hxj₀, add_sub_cancel_left]
    · rintro ⟨j₀, hj₀, rfl⟩
      exact ⟨j₀, hj₀, by simp [hvs j₀ hj₀, hw j₀ hj₀ j₀ hj₀],
        fun j hj hne ↦ by simp [hvs j hj, hw j₀ hj₀ j hj, Ne.symm hne]⟩
  have hS : (facetPolyhedron i (cornerChopNormal u s) (cornerChopSupport c s ε)).extremePoints ℝ =
      (facetPolyhedron i u c).extremePoints ℝ \ {v} ∪ (fun j ↦ v + ε • w j) '' s := by
    ext x
    rw [hv.mem_extremePoints_facetPolyhedron_cornerChop_iff hi hs hε0 hε, hedge, mem_union,
      Set.mem_sdiff, mem_singleton_iff]
  have hfin : ((facetPolyhedron i u c).extremePoints ℝ).Finite :=
    finite_extremePoints_facetPolyhedron
  -- The old vertices other than `v` lie deeper than `ε`.
  have hdisj : Disjoint ((facetPolyhedron i u c).extremePoints ℝ \ {v})
      ((fun j ↦ v + ε • w j) '' s) := by
    refine Set.disjoint_left.2 fun x ⟨hxΔ, hxv⟩ hx' ↦ ?_
    obtain ⟨j₀, hj₀, hxj₀, hxj⟩ := (hedge x).2 hx'
    have hlt := lt_sum_sub_of_mem_extremePoints hw hε hx hxΔ hxv
    rw [sum_sub_eq_of_forall_ne hj₀ hxj, hxj₀, add_sub_cancel_left] at hlt
    exact lt_irrefl ε hlt
  have hinj : InjOn (fun j ↦ v + ε • w j) s := fun j hj k hk h ↦ by
    have h' := congrArg (· (i (u j))) h
    by_contra hne
    simp [hw j hj j hj, hw k hk j hj, Ne.symm hne, hε0.ne'] at h'
  have hcard := (card_eq_finrank_of_isSmoothVertex hv hs).trans hi.finrank_eq
  rw [hS, ncard_union_eq hdisj (hfin.subset sdiff_subset) (s.finite_toSet.image _),
    hinj.ncard_image, ncard_coe_finset, add_right_comm, ncard_sdiff_singleton_add_one hvΔ hfin,
    hcard]

/-- **A small corner chop has `n - 1` more vertices**, in dimension `n`. Let `v` be a smooth vertex
of the polytope `Δ` in an integral lattice. For every sufficiently small depth `ε > 0`, chopping the
corner `v` off `Δ` replaces the vertex `v` by `n` new vertices, one on each edge from `v`. -/
theorem IsSmoothVertex.eventually_ncard_extremePoints_facetPolyhedron_cornerChop [Finite ι]
    (hi : IsIntegralLattice i) {v : StrongDual ℝ V} (hv : IsSmoothVertex i u c v)
    (hvΔ : v ∈ (facetPolyhedron i u c).extremePoints ℝ)
    (hs : (s : Set ι) = activeSet (facetPairing i u) c v) :
    ∀ᶠ ε in 𝓝[>] 0, ((facetPolyhedron i (cornerChopNormal u s)
        (cornerChopSupport c s ε)).extremePoints ℝ).ncard + 1 =
      ((facetPolyhedron i u c).extremePoints ℝ).ncard + Module.finrank ℝ V := by
  filter_upwards [self_mem_nhdsWithin, (hv.eventually_forall_lt_apply hi (extremePoints_subset hvΔ)
    hs).filter_mono nhdsWithin_le_nhds] with ε (hε0 : 0 < ε) hε
  exact hv.ncard_extremePoints_facetPolyhedron_cornerChop hi hvΔ hs hε0 hε

/-! ### The blown-up projective space -/

section Simplex

variable {n : ℕ} {a : ℝ}

/-- The corner `0` of the standard simplex is where its coordinate facets meet. -/
private theorem coe_map_some_eq_activeSet_simplex_zero (ha : a ≠ 0) :
    ((Finset.univ.map .some : Finset (Option (Fin n))) : Set (Option (Fin n))) =
      activeSet (facetPairing ((Int.castAddHom ℝ).compLeft (Fin n)) (simplexNormal (Fin n)))
        (simplexSupport a) 0 := by
  ext o
  cases o with
  | none => exact iff_of_false (by simp) (none_notMem_activeSet_simplex_zero ha)
  | some k => exact iff_of_true (by simp) (some_mem_activeSet_simplex_iff.2 (by simp))

/-- Up to the depth `a`, the slanted facet of the simplex of size `a` stays inactive on the
simplex `{0 ≤ x(eₖ), ∑ k, x(eₖ) ≤ ε}` at the corner `0`. -/
private theorem lt_apply_simplex_of_sum_le {ε : ℝ} (hεa : ε < a) (x : StrongDual ℝ (Fin n → ℝ))
    (hxs : ∀ j ∈ (Finset.univ.map .some : Finset (Option (Fin n))),
      simplexSupport a j ≤ x ((Int.castAddHom ℝ).compLeft (Fin n) (simplexNormal (Fin n) j)))
    (hxε : ∑ j ∈ (Finset.univ.map .some : Finset (Option (Fin n))),
      (x ((Int.castAddHom ℝ).compLeft (Fin n) (simplexNormal (Fin n) j)) - simplexSupport a j) ≤ ε)
    (k : Option (Fin n)) (hk : k ∉ (Finset.univ.map .some : Finset (Option (Fin n)))) :
    simplexSupport a k < x ((Int.castAddHom ℝ).compLeft (Fin n) (simplexNormal (Fin n) k)) := by
  obtain rfl : k = none := by
    cases k with
    | none => rfl
    | some k => simp at hk
  have hxP := mem_facetPolyhedron_simplex_of_sum_le hεa.le hxs hxε
  refine (mem_facetPolyhedron.1 hxP none).lt_of_ne fun h ↦ ?_
  have hnone : none ∈ activeSet (facetPairing ((Int.castAddHom ℝ).compLeft (Fin n))
      (simplexNormal (Fin n))) (simplexSupport a) x := by
    rw [mem_activeSet, facetPairing_apply]
    exact h.symm
  have hxε' : ∑ k, x (Pi.single k 1) ≤ ε := by simpa [Finset.sum_map] using hxε
  linarith [none_mem_activeSet_simplex_iff.1 hnone]

/-- Up to the depth `a`, each facet of the simplex of size `a` in `ℝⁿ`, `n ≥ 2`, contains a point
lying on no other facet whose coordinates sum to more than `ε`. -/
private theorem exists_activeSet_simplex_eq_singleton (hn : 2 ≤ n) {ε : ℝ} (hε : 0 < ε)
    (hεa : ε < a) (o : Option (Fin n)) :
    ∃ y ∈ facetPolyhedron ((Int.castAddHom ℝ).compLeft (Fin n)) (simplexNormal (Fin n))
        (simplexSupport a),
      activeSet (facetPairing ((Int.castAddHom ℝ).compLeft (Fin n)) (simplexNormal (Fin n)))
          (simplexSupport a) y = {o} ∧
        ε < ∑ j ∈ (Finset.univ.map .some : Finset (Option (Fin n))),
          (y ((Int.castAddHom ℝ).compLeft (Fin n) (simplexNormal (Fin n) j)) -
            simplexSupport a j) := by
  have ha : 0 < a := hε.trans hεa
  have : NeZero n := ⟨by omega⟩
  -- The depth of a point below the corner `0` is the sum of its coordinates.
  have hdepth (y : StrongDual ℝ (Fin n → ℝ)) :
      ∑ j ∈ (Finset.univ.map .some : Finset (Option (Fin n))),
        (y ((Int.castAddHom ℝ).compLeft (Fin n) (simplexNormal (Fin n) j)) -
          simplexSupport a j) = ∑ k, y (Pi.single k 1) := by
    simp [Finset.sum_map]
  simp only [hdepth]
  cases o with
  | none =>
    -- The barycentre of the facet `∑ k, x (e k) = a`, at depth `a`.
    obtain ⟨y, hyP, hy⟩ := exists_activeSet_simplex_eq_none (κ := Fin n) ha
    refine ⟨y, hyP, hy, ?_⟩
    rw [none_mem_activeSet_simplex_iff.1 (hy ▸ mem_singleton none)]
    exact hεa
  | some k =>
    -- A point with `x (e k) = 0` and all other coordinates equal, at depth `(a + ε) / 2`.
    have hn1 : (0 : ℝ) < n - 1 := by
      have : (2 : ℝ) ≤ n := by exact_mod_cast hn
      linarith
    have hsum : (Fintype.card (Fin n) - 1) * ((a + ε) / (2 * (n - 1))) = (a + ε) / 2 := by
      rw [Fintype.card_fin]
      field_simp
    obtain ⟨y, hyP, hy, hy'⟩ := exists_activeSet_simplex_eq_some (a := a)
      (b := (a + ε) / (2 * (n - 1))) (by positivity) k (by rw [hsum]; linarith)
    exact ⟨y, hyP, hy, by rw [hy', hsum]; linarith⟩

/-- **The blown-up projective space is Delzant at every depth.** For `n ≥ 2` and `0 < ε < a`,
chopping the corner `0` off the standard simplex of size `a` in `ℝⁿ` at depth `ε` gives the
Delzant polytope `{0 ≤ x(eₖ) for every k, ε ≤ ∑ k, x(eₖ) ≤ a}`, the moment polytope of `ℂPⁿ`
blown up at a fixed point. For `n = 1` the chop is the interval `[ε, a]` with the redundant facet
`x(e₁) ≥ 0`, so it is not Delzant. For `n = 2`, chopping the vertex `(0, a)` instead gives a
Hirzebruch trapezoid (`TauCeti.Toric.isDelzant_cornerChop_simplex`). -/
theorem isDelzant_simplex_cornerChop (hn : 2 ≤ n) {ε : ℝ} (hε : 0 < ε) (hεa : ε < a) :
    IsDelzant ((Int.castAddHom ℝ).compLeft (Fin n))
      (cornerChopNormal (simplexNormal (Fin n)) (Finset.univ.map .some))
      (cornerChopSupport (simplexSupport a) (Finset.univ.map .some) ε) := by
  have ha : 0 < a := hε.trans hεa
  have : NeZero n := ⟨by omega⟩
  exact (isDelzant_simplex ha).isDelzant_cornerChop (isIntegralLattice_intCast n)
    ((mem_extremePoints_facetPolyhedron_simplex_iff ha).2 (Or.inl rfl))
    (coe_map_some_eq_activeSet_simplex_zero ha.ne') (by rw [Module.finrank_fin_fun]; omega) hε
    (lt_apply_simplex_of_sum_le hεa) (exists_activeSet_simplex_eq_singleton hn hε hεa)

/-- **The blown-up projective space has `2 n` vertices.** For `n ≥ 1` and `0 < ε < a`, chopping
the corner `0` off the standard simplex of size `a` in `ℝⁿ` at depth `ε` replaces that vertex by the
`n` vertices `ε eₖ*`, which leaves the `n` vertices `a eₖ*` and these. -/
theorem ncard_extremePoints_facetPolyhedron_simplex_cornerChop [NeZero n] {ε : ℝ} (hε : 0 < ε)
    (hεa : ε < a) :
    ((facetPolyhedron ((Int.castAddHom ℝ).compLeft (Fin n))
      (cornerChopNormal (simplexNormal (Fin n)) (Finset.univ.map .some))
      (cornerChopSupport (simplexSupport a) (Finset.univ.map .some) ε)).extremePoints ℝ).ncard =
        2 * n := by
  have ha : 0 < a := hε.trans hεa
  have h0 := (mem_extremePoints_facetPolyhedron_simplex_iff (κ := Fin n) ha).2 (Or.inl rfl)
  have h :=
    ((isDelzant_simplex ha).isSmoothVertex 0 h0).ncard_extremePoints_facetPolyhedron_cornerChop
    (isIntegralLattice_intCast n) h0 (coe_map_some_eq_activeSet_simplex_zero ha.ne') hε
    (lt_apply_simplex_of_sum_le hεa)
  rw [ncard_extremePoints_facetPolyhedron_simplex ha, Fintype.card_fin,
    Module.finrank_fin_fun] at h
  omega

end Simplex

end TauCeti.Toric
