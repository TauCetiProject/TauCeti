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

import Mathlib.LinearAlgebra.Dimension.OrzechProperty
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
of `ℂP²` at a point. This file treats the polytopes only.

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
dimension hypothesis is needed.

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
* `TauCeti.Toric.IsDelzant.eventually_isDelzant_cornerChop`: small corner chops of a Delzant
  polytope at a vertex are Delzant polytopes.

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
  have hvs (j) (hj : j ∈ s) : c j = v (i (u j)) := by
    rw [← Finset.mem_coe, hs, mem_activeSet, facetPairing_apply] at hj
    exact hj.symm
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
  rw [sum_mul_apply_eq hw _ hk, hvs k hk]
  ring

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

/-! ### Vertices of the chopped polytope -/

section Vertices

variable [Finite ι] {v : StrongDual ℝ V} {w : ι → StrongDual ℝ V}

/-- A vertex of the chopped polytope off the new facet is a smooth vertex, when every vertex of the
original polytope is smooth. -/
private theorem isSmoothVertex_cornerChop_of_none_notMem
    (hsmooth : ∀ x ∈ (facetPolyhedron i u c).extremePoints ℝ, IsSmoothVertex i u c x)
    (hx : x ∈ (facetPolyhedron i (cornerChopNormal u s) (cornerChopSupport c s ε)).extremePoints ℝ)
    (hnone : none ∉
      activeSet (facetPairing i (cornerChopNormal u s)) (cornerChopSupport c s ε) x) :
    IsSmoothVertex i (cornerChopNormal u s) (cornerChopSupport c s ε) x := by
  obtain ⟨hxP, hker⟩ := mem_extremePoints_facetPolyhedron_iff.1 hx
  -- The active constraints are the old ones active at `x`.
  have hA : activeSet (facetPairing i (cornerChopNormal u s)) (cornerChopSupport c s ε) x =
      some '' activeSet (facetPairing i u) c x := by
    ext o
    cases o with
    | none => simpa using hnone
    | some j => simp
  have hxΔ : x ∈ (facetPolyhedron i u c).extremePoints ℝ := by
    refine mem_extremePoints_facetPolyhedron_iff.2
      ⟨facetPolyhedron_cornerChop_subset hxP, fun f hf ↦ hker f fun o ho ↦ ?_⟩
    rw [hA] at ho
    obtain ⟨j, hj, rfl⟩ := ho
    exact hf j hj
  obtain ⟨hli, hsp⟩ := isSmoothVertex_iff_linearIndepOn.1 (hsmooth x hxΔ)
  rw [isSmoothVertex_iff_linearIndepOn, hA, image_image]
  exact ⟨hli.image_of_comp some (cornerChopNormal u s), hsp⟩

variable [DecidableEq ι] (hw : ∀ j ∈ s, ∀ k ∈ s, w j (i (u k)) = if j = k then 1 else 0)
  (hx : ∀ x : StrongDual ℝ V, x = v + ∑ j ∈ s, (x (i (u j)) - c j) • w j)
  (hε : ∀ k ∉ s, ε * ∑ j ∈ s, |w j (i (u k))| < v (i (u k)) - c k)
include hw hx hε

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
  have hslack {k} (hk : k ∉ s) : c k < x (i (u k)) :=
    lt_apply_of_sum_le hx hε (fun j _ ↦ hxΔ j) hnone.le hk
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
  obtain ⟨j₀, hj₀, hA⟩ := exists_activeSet_cornerChop_eq_image hw hx hε hx' hε0 hnone
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

end Vertices

/-! ### Small corner chops are Delzant -/

/-- A point with the coordinates `ε / #s` relative to the corner lies only on the new facet. -/
private theorem exists_activeSet_cornerChop_eq_none [DecidableEq ι] {v : StrongDual ℝ V}
    {w : ι → StrongDual ℝ V}
    (hw : ∀ j ∈ s, ∀ k ∈ s, w j (i (u k)) = if j = k then 1 else 0)
    (hx : ∀ x : StrongDual ℝ V, x = v + ∑ j ∈ s, (x (i (u j)) - c j) • w j)
    (hε : ∀ k ∉ s, ε * ∑ j ∈ s, |w j (i (u k))| < v (i (u k)) - c k)
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
    lt_apply_of_sum_le hx hε (fun j hj ↦ by rw [hz j hj]; linarith) hzsum.le hk
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
  obtain ⟨w, hw, hx⟩ := hsv.exists_coord hi hs
  have hsA (j) : j ∈ s ↔ v (i (u j)) = c j := by
    rw [← Finset.mem_coe, hs, mem_activeSet, facetPairing_apply]
  have hvs (j) (hj : j ∈ s) : v (i (u j)) = c j := (hsA j).1 hj
  have hvP := mem_facetPolyhedron.1 (extremePoints_subset hv)
  have hcard : s.card = Module.finrank ℤ N := by
    rw [← hsv.ncard_activeSet, ← hs, ncard_coe_finset]
  have hcard2 : 2 ≤ s.card := hcard ▸ hi.finrank_eq ▸ hV
  have hsp : Submodule.span ℤ (u '' s) = ⊤ := by
    rw [hs]; exact (isSmoothVertex_iff_linearIndepOn.1 hsv).2
  -- Points lying on only one old facet, and their (positive) depths relative to the corner.
  choose y hyP hyj using hΔ.irredundant
  have hdepth (j) : 0 < ∑ k ∈ s, (y j (i (u k)) - c k) := by
    refine sum_sub_pos hx (fun k _ ↦ mem_facetPolyhedron.1 (hyP j) k) fun hyv ↦ ?_
    -- Otherwise the corner would lie on the single facet `j`, while at least two meet there.
    have : s = {j} := Finset.coe_injective (by rw [hs, ← hyv, hyj j, Finset.coe_singleton])
    rw [this, Finset.card_singleton] at hcard2
    omega
  -- The constraints inactive at the corner have positive slack there.
  have hslack (k) (hk : k ∉ s) : 0 < v (i (u k)) - c k :=
    sub_pos.2 ((hvP k).lt_of_ne fun h ↦ hk ((hsA k).2 h.symm))
  have h₁ : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ j, ε < ∑ k ∈ s, (y j (i (u k)) - c k) :=
    eventually_all.2 fun j ↦ (eventually_lt_nhds (hdepth j)).filter_mono nhdsWithin_le_nhds
  have h₂ : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ k ∉ s, ε * ∑ j ∈ s, |w j (i (u k))| < v (i (u k)) - c k := by
    refine eventually_all.2 fun k ↦ ?_
    by_cases hk : k ∈ s
    · exact Eventually.of_forall fun _ h ↦ absurd hk h
    refine (((continuous_id.mul continuous_const).tendsto' 0 0 (by simp)).eventually_lt_const
      (hslack k hk)).filter_mono nhdsWithin_le_nhds |>.mono fun ε hε _ ↦ hε
  filter_upwards [self_mem_nhdsWithin, h₁, h₂] with ε (hε0 : 0 < ε) hεy hε
  refine ⟨hΔ.isBounded.subset facetPolyhedron_cornerChop_subset, fun x hx' ↦ ?_, fun o ↦ ?_⟩
  · by_cases hnone : ∑ j ∈ s, (x (i (u j)) - c j) = ε
    · exact isSmoothVertex_cornerChop_of_none_mem hw hx hε hsp hcard.le hx' hε0 hnone
    · exact isSmoothVertex_cornerChop_of_none_notMem hΔ.isSmoothVertex hx' (by simpa using hnone)
  cases o with
  | none =>
    exact exists_activeSet_cornerChop_eq_none hw hx hε hvs
      (Finset.card_pos.1 (by omega)) hε0
  | some j =>
    refine ⟨y j, mem_facetPolyhedron_cornerChop_iff.2 ⟨hyP j, (hεy j).le⟩, Set.ext fun o ↦ ?_⟩
    cases o with
    | none => simpa using (hεy j).ne'
    | some k => rw [some_mem_activeSet_cornerChop_iff, hyj j]; simp

end TauCeti.Toric
