/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Toric.Delzant.Irredundant

import Mathlib.Analysis.Convex.Extrema
import Mathlib.Analysis.LocallyConvex.Separation
import TauCeti.Analysis.Convex.KreinMilman
import TauCeti.Analysis.Convex.Polyhedron.TangentCone

/-!
# Polytopes with smooth vertex cones are Delzant

Let `i : N →+ V` be an integral lattice and let `Δ` be a nonempty compact convex subset of the
dual space `V*` with finitely many extreme points. Suppose that `Δ` has a *smooth corner* at each
of its vertices `v`: some `ℤ`-basis `s` of `N` cuts out `Δ` near `v`,

`y ∈ Δ ↔ ⟨v, n⟩ ≤ ⟨y, n⟩ for every n ∈ s`, for `y` near `v`.

Then `Δ` is a Delzant polytope: it is cut out by the finitely many inequalities `⟨v, n⟩ ≤ ⟨y, n⟩`
for the vertices `v` and the `n ∈ s_v`, and this presentation is Delzant
(`TauCeti.Toric.existsUnique_isDelzant_facetPolyhedron_eq`). The presentation is recorded as the
finite set `F ⊆ N × ℝ` of pairs (inward normal, support constant), indexed by itself. This set is
unique: a Delzant polytope determines its facets
(`TauCeti.Toric.eq_of_isDelzant_of_facetPolyhedron_eq`, the set-indexed form of
`TauCeti.Toric.IsDelzant.facetPolyhedron_eq_iff`). Conversely, every Delzant polytope is nonempty,
compact and convex with finitely many vertices, and has a smooth corner at each of them, so these
conditions characterize Delzant polytopes among subsets of `V*`
(`TauCeti.Toric.exists_isDelzant_facetPolyhedron_eq_iff`).

This is the polytope half of the theorem that the moment image of a symplectic toric manifold is
a Delzant polytope: by convexity the image is the convex hull of the finitely many images of the
fixed points, and the local normal form at a fixed point makes the image a smooth corner there.

The proof has three steps.

* Convexity spreads the local inequalities at a vertex `v` to all of `Δ`: the segment from `v` to
  a point of `Δ` starts in the neighbourhood of `v` where the inequalities hold. Conversely, a
  point satisfying the inequalities at `v` is reached from `v` by a short segment inside `Δ`. So
  `Δ` lies in the polyhedron `P` cut out by all these inequalities, and if some `x ∈ P` were not in
  `Δ`, a functional separating `x` from `Δ` would attain its minimum on `Δ` at a vertex `v`, from
  which the segment towards `x` enters `Δ` and decreases the functional. Hence `P = Δ`.
* An inequality `⟨v', n⟩ ≤ ⟨y, n⟩` coming from a vertex `v'` and active at another vertex `v` has
  `n ∈ s_v`. Write `n` in the real basis `s_v`, with coefficients `t_m ≥ 0`, the values of `n` on
  the edge directions at `v`. The face of `n` contains `v'` and the points `v' + ε e'_l` along the
  edge directions at `v'` other than the one dual to `n`, and on this face every basis vector
  `m ∈ s_v` with `t_m > 0` is constant. So such an `m` is killed by all those edge directions,
  hence is a real multiple of `n`; both are primitive, so `n = m`.
* So the inequalities active at a vertex `v` are exactly those of `s_v`, which form a lattice
  basis. A point `v + ε Σ_{m ≠ k} e_m` near `v`, with `e_m` the edge directions at `v`, lies on the
  facet of the `k`-th normal and on no other, which proves irredundancy.

## Main results

* `TauCeti.Toric.existsUnique_isDelzant_facetPolyhedron_eq`: a nonempty compact convex set with
  finitely many extreme points and a smooth corner at each of them is a Delzant polytope, with a
  unique facet set.
* `TauCeti.Toric.exists_isDelzant_facetPolyhedron_eq_iff`: these conditions characterize Delzant
  polytopes.

## References

* T. Delzant, *Hamiltoniens périodiques et images convexes de l'application moment*,
  Bull. Soc. Math. France 116 (1988), 315–339.
* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Theorem 28.2 and Section 29.
* V. Guillemin, *Moment Maps and Combinatorial Invariants of Hamiltonian `T^n`-spaces*,
  Birkhäuser, 1994, Chapter 1.
-/

public section

open Set Filter
open scoped Topology

namespace TauCeti.Toric

variable {N V : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V] {i : N →+ V}
  {Δ : Set (StrongDual ℝ V)}

/-! ### Corners of a convex set -/

section Corner

variable {s : Set N} {v : StrongDual ℝ V}

/-- The inequalities of a corner `v` of a convex set `Δ` hold on all of `Δ`: a local minimum of
the linear function `y ↦ ⟨y, n⟩` on `Δ` is a global one. -/
private theorem apply_le_apply_of_corner (hΔ : Convex ℝ Δ) (hv : v ∈ Δ)
    (hloc : ∀ᶠ y in 𝓝 v, y ∈ Δ ↔ ∀ n ∈ s, v (i n) ≤ y (i n)) {y : StrongDual ℝ V}
    (hy : y ∈ Δ) {n : N} (hn : n ∈ s) : v (i n) ≤ y (i n) :=
  isMinOn_iff.1 (IsMinOn.of_isLocalMinOn_of_convexOn (f := fun y : StrongDual ℝ V ↦ y (i n)) hv
    (eventually_nhdsWithin_iff.2 (hloc.mono fun _ h hy ↦ h.1 hy n hn))
    ((ContinuousLinearMap.apply ℝ ℝ (i n)).toLinearMap.convexOn hΔ)) y hy

/-- From a corner `v` of `Δ`, a short segment in any direction `w` that is nonnegative on the
normals of the corner stays in `Δ`. -/
private theorem eventually_add_smul_mem
    (hloc : ∀ᶠ y in 𝓝 v, y ∈ Δ ↔ ∀ n ∈ s, v (i n) ≤ y (i n)) {w : StrongDual ℝ V}
    (hw : ∀ n ∈ s, 0 ≤ w (i n)) : ∀ᶠ t in 𝓝[>] (0 : ℝ), v + t • w ∈ Δ := by
  have h : Tendsto (fun t : ℝ ↦ v + t • w) (𝓝[>] 0) (𝓝 v) :=
    (Continuous.tendsto' (by fun_prop) 0 v (by simp)).mono_left nhdsWithin_le_nhds
  filter_upwards [h.eventually hloc, self_mem_nhdsWithin] with t ht ht0
  refine ht.2 fun n hn ↦ ?_
  simp only [add_apply, smul_apply, smul_eq_mul]
  nlinarith [hw n hn, mem_Ioi.1 ht0]

/-- The normals of a corner, a `ℤ`-basis of the lattice, are finitely many and index a basis of
`N`. -/
private theorem finite_and_exists_basis (hi : IsIntegralLattice i) (hli : LinearIndepOn ℤ id s)
    (hsp : Submodule.span ℤ s = ⊤) : Finite s ∧ ∃ b : Module.Basis s ℤ N, ∀ k, b k = k := by
  let b := Module.Basis.mk hli (by simp [hsp])
  have := hi.finite
  exact ⟨Module.Finite.finite_basis b, b, fun _ ↦ Module.Basis.mk_apply ..⟩

variable (hi : IsIntegralLattice i) [Finite s] {b : Module.Basis s ℤ N} (hb : ∀ k, b k = k)
include hi hb

/-- The edge directions of a corner, the dual basis of its normals, pair with the normals as
dual bases. -/
private theorem dualBasis_apply_of_basis [DecidableEq s] (m k : s) :
    hi.dualBasis b m (i k) = if k = m then 1 else 0 := by
  simpa [hb] using hi.dualBasis_apply_apply b m k

/-- A vector killed by all edge directions of a corner but one, `e_l₀`, is a multiple of the
normal `l₀`. -/
private theorem eq_smul_of_dualBasis_apply_eq_zero {z : V} {l₀ : s}
    (hz : ∀ l, l ≠ l₀ → hi.dualBasis b l z = 0) : z = hi.dualBasis b l₀ z • i l₀ := by
  have := Fintype.ofFinite s
  conv_lhs => rw [← hi.sum_dualBasis_apply_smul b z]
  rw [Finset.sum_eq_single l₀ (fun l _ hl ↦ by rw [hz l hl, zero_smul]) (by simp), hb]

omit hb in
/-- A nonzero vector with nonnegative coordinates along the edge directions has a positive one. -/
private theorem exists_dualBasis_apply_pos {z : V} (hz : z ≠ 0)
    (ht : ∀ m, 0 ≤ hi.dualBasis b m z) : ∃ m, 0 < hi.dualBasis b m z := by
  have := Fintype.ofFinite s
  by_contra! hneg
  refine hz ?_
  rw [← hi.sum_dualBasis_apply_smul b z]
  exact Finset.sum_eq_zero fun k _ ↦ by rw [le_antisymm (hneg k) (ht k), zero_smul]

/-- The edge directions of a corner are nonnegative on its normals. -/
private theorem dualBasis_apply_nonneg (m : s) {k : N} (hk : k ∈ s) :
    0 ≤ hi.dualBasis b m (i k) := by
  classical
  rw [dualBasis_apply_of_basis hi hb m ⟨k, hk⟩]
  split_ifs <;> norm_num

variable (hΔ : Convex ℝ Δ) (hv : v ∈ Δ) (hloc : ∀ᶠ y in 𝓝 v, y ∈ Δ ↔ ∀ n ∈ s, v (i n) ≤ y (i n))
  {n : N} (hn : ∀ y ∈ Δ, v (i n) ≤ y (i n))
include hloc hn

/-- **Valid inequalities at a corner.** If the inequality `⟨v, n⟩ ≤ ⟨y, n⟩` holds on `Δ`, then
`n` lies in the cone of the normals of the corner at `v`: its coordinates `⟨e_m, n⟩` along the
edge directions `e_m` are nonnegative, since the edges stay in `Δ` near `v`. -/
private theorem dualBasis_apply_nonneg_of_forall_le (m : s) : 0 ≤ hi.dualBasis b m (i n) := by
  obtain ⟨t, htΔ, ht0⟩ := ((eventually_add_smul_mem hloc
    fun k hk ↦ dualBasis_apply_nonneg hi hb m hk).and self_mem_nhdsWithin).exists
  have h := hn _ htΔ
  simp only [add_apply, smul_apply, smul_eq_mul] at h
  nlinarith [mem_Ioi.1 ht0]

include hΔ hv in
/-- **Faces of a valid inequality at a corner.** On the face where a valid inequality
`⟨v, n⟩ ≤ ⟨y, n⟩` at the corner `v` is active, each normal `m` of the corner along which `n` has a
positive coordinate is constant. -/
private theorem apply_eq_of_dualBasis_apply_pos {p : StrongDual ℝ V} (hp : p ∈ Δ)
    (hpn : p (i n) = v (i n)) (m : s) (hm : 0 < hi.dualBasis b m (i n)) : p (i m) = v (i m) := by
  have := Fintype.ofFinite s
  -- `⟨p - v, n⟩ = Σ_k ⟨p - v, k⟩ ⟨e_k, n⟩` is a sum of nonnegative terms which vanishes.
  have hsum := hi.sum_apply_mul_dualBasis_apply b (p - v) (i n)
  rw [sub_apply, hpn, sub_self, Finset.sum_eq_zero_iff_of_nonneg fun k _ ↦ mul_nonneg (by
    rw [sub_apply, hb, sub_nonneg]
    exact apply_le_apply_of_corner hΔ hv hloc hp k.property)
    (dualBasis_apply_nonneg_of_forall_le hi hb hloc hn k)] at hsum
  have h := hsum m (Finset.mem_univ m)
  rw [hb, sub_apply, mul_eq_zero, sub_eq_zero] at h
  exact h.resolve_right hm.ne'

end Corner

/-! ### The facets of a convex set with smooth corners -/

section Facets

variable (hi : IsIntegralLattice i) (hΔ : Convex ℝ Δ) {s : StrongDual ℝ V → Set N}
  (hs : ∀ v ∈ Δ.extremePoints ℝ, LinearIndepOn ℤ id (s v) ∧ Submodule.span ℤ (s v) = ⊤ ∧
    ∀ᶠ y in 𝓝 v, y ∈ Δ ↔ ∀ n ∈ s v, v (i n) ≤ y (i n))
include hi hΔ hs

/-- **Facets at a vertex.** If the inequality of a normal `n` of the corner at a vertex `v'` is
active at another vertex `v`, then `n` is a normal of the corner at `v`. -/
private theorem mem_of_apply_eq {v v' : StrongDual ℝ V} (hv : v ∈ Δ.extremePoints ℝ)
    (hv' : v' ∈ Δ.extremePoints ℝ) {n : N} (hn : n ∈ s v') (hvn : v (i n) = v' (i n)) :
    n ∈ s v := by
  classical
  obtain ⟨hli, hsp, hloc⟩ := hs v hv
  obtain ⟨hli', hsp', hloc'⟩ := hs v' hv'
  have hvΔ : v ∈ Δ := extremePoints_subset hv
  have hv'Δ : v' ∈ Δ := extremePoints_subset hv'
  obtain ⟨_, b, hb⟩ := finite_and_exists_basis hi hli hsp
  obtain ⟨_, b', hb'⟩ := finite_and_exists_basis hi hli' hsp'
  have := Fintype.ofFinite (s v')
  set w := hi.dualBasis b
  set w' := hi.dualBasis b'
  -- The inequality of `n` holds on `Δ` and is active at `v`.
  have hle (y : StrongDual ℝ V) (hy : y ∈ Δ) : v (i n) ≤ y (i n) :=
    hvn ▸ apply_le_apply_of_corner hΔ hv'Δ hloc' hy hn
  have ht := dualBasis_apply_nonneg_of_forall_le hi hb hloc hle
  -- A normal `m` at `v` along which `n` has a positive coordinate is killed by every edge
  -- direction at `v'` other than the one dual to `n`: the edge from `v'` lies in the face of `n`.
  have hedge (m : s v) (hm : 0 < w m (i n)) (l : s v') (hl : l ≠ ⟨n, hn⟩) : w' l (i m) = 0 := by
    obtain ⟨ε, hεΔ, hε0⟩ := ((eventually_add_smul_mem hloc'
      fun k hk ↦ dualBasis_apply_nonneg hi hb' l hk).and self_mem_nhdsWithin).exists
    have hεn : (v' + ε • w' l) (i n) = v (i n) := by
      have h : w' l (i n) = 0 := by
        simpa [Ne.symm hl] using dualBasis_apply_of_basis hi hb' l ⟨n, hn⟩
      rw [add_apply, smul_apply, h, smul_zero, add_zero, hvn]
    have h₁ := apply_eq_of_dualBasis_apply_pos hi hb hΔ hvΔ hloc hle hεΔ hεn m hm
    have h₂ := apply_eq_of_dualBasis_apply_pos hi hb hΔ hvΔ hloc hle hv'Δ hvn.symm m hm
    simp only [add_apply, smul_apply, smul_eq_mul, h₂] at h₁
    exact (mul_eq_zero.1 (by linarith)).resolve_left (mem_Ioi.1 hε0).ne'
  -- Some coordinate of `n` is positive, since `n ≠ 0`.
  have hprim : IsPrimitive n := by simpa [hb'] using b'.isPrimitive ⟨n, hn⟩
  obtain ⟨m, hm⟩ := exists_dualBasis_apply_pos hi
    ((map_ne_zero_iff i hi.injective).2 hprim.ne_zero) ht
  -- So `m` is a multiple of `n`, by a positive factor, and both are primitive.
  have hmn : i m = w' ⟨n, hn⟩ (i m) • i n :=
    eq_smul_of_dualBasis_apply_eq_zero hi hb' (hedge m hm)
  have h1 : w' ⟨n, hn⟩ (i m) * w m (i n) = 1 := by
    have hmm : w m (i m) = 1 := by simpa using dualBasis_apply_of_basis hi hb m m
    have h := congrArg (w m) hmn
    rw [hmm, ContinuousLinearMap.map_smul, smul_eq_mul] at h
    exact h.symm
  have hnm : i n = w m (i n) • i m := by
    rw [hmn, smul_smul, mul_comm, h1, one_smul]
  rw [hi.eq_of_isPrimitive_of_eq_smul (by simpa [hb] using b.isPrimitive m) hprim (ht m) hnm]
  exact m.property

variable {ι : Type*} {u : ι → N} {c : ι → ℝ}
  (hu : ∀ j, ∃ v ∈ Δ.extremePoints ℝ, u j ∈ s v ∧ c j = v (i (u j)))
  (hsurj : ∀ v ∈ Δ.extremePoints ℝ, ∀ n ∈ s v, ∃ j, u j = n ∧ c j = v (i n))
include hu

omit hi hsurj in
/-- Every point of `Δ` satisfies the corner inequalities. -/
private theorem le_apply_of_mem (j : ι) {y : StrongDual ℝ V} (hy : y ∈ Δ) : c j ≤ y (i (u j)) := by
  obtain ⟨v, hv, hn, hcj⟩ := hu j
  rw [hcj]
  exact apply_le_apply_of_corner hΔ (extremePoints_subset hv) (hs v hv).2.2 hy hn

omit hi in
include hsurj in
/-- **The corner inequalities cut out `Δ`.** If some `x` satisfying them were not in `Δ`, a
functional separating `x` from `Δ` would attain its minimum on `Δ` at a vertex `v`; the segment
from `v` towards `x` enters `Δ` and decreases the functional. -/
private theorem facetPolyhedron_eq (hne : Δ.Nonempty) (hc : IsCompact Δ) :
    facetPolyhedron i u c = Δ := by
  refine Subset.antisymm (fun x hx ↦ ?_) fun y hy ↦
    mem_facetPolyhedron.2 fun j ↦ le_apply_of_mem hΔ hs hu j hy
  by_contra hxΔ
  obtain ⟨f, r, hfx, hfΔ⟩ := geometric_hahn_banach_point_closed hΔ hc.isClosed hxΔ
  obtain ⟨v, hv, hmin⟩ := hc.exists_mem_extremePoints_isMinOn hne f
  obtain ⟨t, htΔ, ht0⟩ := ((eventually_add_smul_mem (hs v hv).2.2 (w := x - v) fun n hn ↦ by
    obtain ⟨j, rfl, hcj⟩ := hsurj v hv n hn
    rw [sub_apply, sub_nonneg, ← hcj]
    exact mem_facetPolyhedron.1 hx j).and self_mem_nhdsWithin).exists
  have h := isMinOn_iff.1 hmin _ htΔ
  have hfv := hfΔ v (extremePoints_subset hv)
  simp only [map_add, map_smul, map_sub, smul_eq_mul] at h
  nlinarith [mem_Ioi.1 ht0]

omit hsurj in
/-- The inequalities active at a vertex `v` are those of the corner at `v`. -/
private theorem mem_activeSet_iff {v : StrongDual ℝ V} (hv : v ∈ Δ.extremePoints ℝ) (j : ι) :
    j ∈ activeSet (facetPairing i u) c v ↔ u j ∈ s v ∧ c j = v (i (u j)) := by
  rw [mem_activeSet, facetPairing_apply]
  refine ⟨fun h ↦ ⟨?_, h.symm⟩, fun h ↦ h.2.symm⟩
  obtain ⟨v', hv', hn, hcj⟩ := hu j
  exact mem_of_apply_eq hi hΔ hs hv hv' hn (h.trans hcj)

include hsurj in
/-- **Smoothness.** At a vertex, the active normals are the basis of the corner. -/
private theorem isSmoothVertex_of_mem_extremePoints
    (hinj : ∀ j j', u j = u j' → c j = c j' → j = j') {v : StrongDual ℝ V}
    (hv : v ∈ Δ.extremePoints ℝ) : IsSmoothVertex i u c v := by
  have himage : u '' activeSet (facetPairing i u) c v = s v := by
    ext n
    constructor
    · rintro ⟨j, hj, rfl⟩
      exact ((mem_activeSet_iff hi hΔ hs hu hv j).1 hj).1
    · intro hn
      obtain ⟨j, rfl, hcj⟩ := hsurj v hv n hn
      exact ⟨j, (mem_activeSet_iff hi hΔ hs hu hv j).2 ⟨hn, hcj⟩, rfl⟩
  have hinjOn : InjOn u (activeSet (facetPairing i u) c v) := fun j hj j' hj' h ↦
    hinj j j' h (by rw [((mem_activeSet_iff hi hΔ hs hu hv j).1 hj).2,
      ((mem_activeSet_iff hi hΔ hs hu hv j').1 hj').2, h])
  obtain ⟨hli, hsp, -⟩ := hs v hv
  rw [isSmoothVertex_iff_linearIndepOn, linearIndepOn_iff_image hinjOn, himage]
  exact ⟨hli, hsp⟩

omit hsurj in
/-- **Irredundancy.** Pushing the vertex `v` of the facet `j` into the facet, along the edge
directions at `v` other than the one leaving the facet, gives a point on that facet only. -/
private theorem exists_activeSet_eq_singleton [Finite ι]
    (hinj : ∀ j j', u j = u j' → c j = c j' → j = j') (hP : facetPolyhedron i u c = Δ) (j : ι) :
    ∃ x ∈ facetPolyhedron i u c, activeSet (facetPairing i u) c x = {j} := by
  classical
  obtain ⟨v, hv, hn, hcj⟩ := hu j
  obtain ⟨hli, hsp, hloc⟩ := hs v hv
  obtain ⟨_, b, hb⟩ := finite_and_exists_basis hi hli hsp
  let k : s v := ⟨u j, hn⟩
  -- The direction `σ` pairs to `0` with `u j` and to `1` with the other normals at `v`.
  let σ := (hi.dualBasis b).equivFun.symm fun m ↦ if m = k then 0 else 1
  have hσ (m : s v) : σ (i m) = if m = k then 0 else 1 := by
    rw [← hb m, ← hi.dualBasis_repr b σ m, ← Module.Basis.equivFun_apply,
      LinearEquiv.apply_symm_apply]
  have hvP : v ∈ facetPolyhedron i u c := hP ▸ extremePoints_subset hv
  -- For small `t`, the point `v + t σ` lies in `Δ` and strictly inside every facet inactive at `v`.
  have hslack : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ j' : ι, j' ∉ activeSet (facetPairing i u) c v →
      c j' < (v + t • σ) (i (u j')) := by
    rw [eventually_all]
    intro j'
    by_cases hj' : j' ∈ activeSet (facetPairing i u) c v
    · exact Eventually.of_forall fun _ h ↦ (h hj').elim
    have hlt : c j' < v (i (u j')) := (mem_facetPolyhedron.1 hvP j').lt_of_ne fun h ↦
      hj' (by rw [mem_activeSet, facetPairing_apply]; exact h.symm)
    have hcont : Tendsto (fun t : ℝ ↦ (v + t • σ) (i (u j'))) (𝓝[>] 0) (𝓝 (v (i (u j')))) :=
      (Continuous.tendsto' (by fun_prop) 0 _ (by simp)).mono_left nhdsWithin_le_nhds
    exact (hcont.eventually (lt_mem_nhds hlt)).mono fun _ h _ ↦ h
  obtain ⟨t, ⟨htΔ, hts⟩, ht0⟩ := (((eventually_add_smul_mem hloc (w := σ) fun n hn ↦ by
    rw [hσ ⟨n, hn⟩]; split_ifs <;> norm_num).and hslack).and self_mem_nhdsWithin).exists
  refine ⟨v + t • σ, hP ▸ htΔ, ?_⟩
  ext j'
  rw [mem_singleton_iff, mem_activeSet, facetPairing_apply, add_apply, smul_apply, smul_eq_mul]
  constructor
  · intro h
    by_cases hj' : j' ∈ activeSet (facetPairing i u) c v
    · obtain ⟨hn', hc'⟩ := (mem_activeSet_iff hi hΔ hs hu hv j').1 hj'
      have hσ' : σ (i (u j')) = if (⟨u j', hn'⟩ : s v) = k then 0 else 1 := hσ ⟨u j', hn'⟩
      rw [hσ', ← hc'] at h
      split_ifs at h with hk
      · have hu : u j' = u j := congrArg Subtype.val hk
        exact hinj j' j hu (by rw [hc', hcj, hu])
      · exact absurd h (by linarith [mem_Ioi.1 ht0])
    · exact absurd (by rw [add_apply, smul_apply, smul_eq_mul]; exact h) (hts j' hj').ne'
  · rintro rfl
    have hσk : σ (i (u j')) = 0 := by simpa using hσ k
    rw [hσk, mul_zero, add_zero, hcj]

include hsurj in
/-- **The presentation by the corner inequalities is Delzant.** A finite family `(u j, c j)` listing
each inequality `⟨v, n⟩ ≤ ⟨y, n⟩` of the corners of `Δ` exactly once is a Delzant presentation of
`Δ`. -/
private theorem isDelzant_and_facetPolyhedron_eq [Finite ι] (hne : Δ.Nonempty) (hc : IsCompact Δ)
    (hinj : ∀ j j', u j = u j' → c j = c j' → j = j') :
    IsDelzant i u c ∧ facetPolyhedron i u c = Δ := by
  have hP := facetPolyhedron_eq hΔ hs hu hsurj hne hc
  refine ⟨⟨hP ▸ hc.isBounded, fun x hx ↦ ?_, exists_activeSet_eq_singleton hi hΔ hs hu hinj hP⟩,
    hP⟩
  rw [hP] at hx
  exact isSmoothVertex_of_mem_extremePoints hi hΔ hs hu hsurj hinj hx

end Facets

/-! ### Delzant polytopes from smooth corners -/

/-- **Polytopes with smooth vertex cones are Delzant.** Let `Δ ⊆ V*` be a nonempty compact convex
set with finitely many extreme points, such that near each extreme point `v` it is cut out by the
inequalities `⟨v, n⟩ ≤ ⟨y, n⟩` for the members `n` of a `ℤ`-basis of the lattice. Then `Δ` is a
Delzant polytope: there is a unique finite set `F` of pairs (inward normal, support constant)
whose Delzant presentation cuts out `Δ`. -/
theorem existsUnique_isDelzant_facetPolyhedron_eq (hi : IsIntegralLattice i) (hne : Δ.Nonempty)
    (hc : IsCompact Δ) (hΔ : Convex ℝ Δ) (hfin : (Δ.extremePoints ℝ).Finite)
    (hs : ∀ v ∈ Δ.extremePoints ℝ, ∃ s : Set N, LinearIndepOn ℤ id s ∧
      Submodule.span ℤ s = ⊤ ∧ ∀ᶠ y in 𝓝 v, y ∈ Δ ↔ ∀ n ∈ s, v (i n) ≤ y (i n)) :
    ∃! F : Set (N × ℝ), F.Finite ∧
      IsDelzant i (fun j : F ↦ (j : N × ℝ).1) (fun j : F ↦ (j : N × ℝ).2) ∧
      facetPolyhedron i (fun j : F ↦ (j : N × ℝ).1) (fun j : F ↦ (j : N × ℝ).2) = Δ := by
  refine existsUnique_of_exists_of_unique ?_ fun F F' ⟨hF, hFΔ, hFP⟩ ⟨hF', hFΔ', hFP'⟩ ↦
    eq_of_isDelzant_of_facetPolyhedron_eq hi hF hF' hFΔ hFΔ' (hFP.trans hFP'.symm)
  -- Choose the basis of the corner at each vertex.
  choose s hs using fun v ↦ (em (v ∈ Δ.extremePoints ℝ)).elim (fun hv ↦ (hs v hv).imp
    fun _ h _ ↦ h) fun hv ↦ ⟨∅, fun h ↦ (hv h).elim⟩
  -- The facet set: the inequalities of all corners.
  have hF : {p : N × ℝ | ∃ v ∈ Δ.extremePoints ℝ, p.1 ∈ s v ∧ p.2 = v (i p.1)}.Finite := by
    refine Set.Finite.subset (s := ⋃ v ∈ Δ.extremePoints ℝ, (fun n ↦ (n, v (i n))) '' s v)
      (hfin.biUnion fun v hv ↦ ?_) ?_
    · obtain ⟨hli, hsp, -⟩ := hs v hv
      have := (finite_and_exists_basis hi hli hsp).1
      exact (Set.toFinite (s v)).image _
    · rintro ⟨n, a⟩ ⟨v, hv, hn, ha⟩
      dsimp only at hn ha
      subst ha
      exact mem_biUnion hv ⟨n, hn, rfl⟩
  have := hF.to_subtype
  obtain ⟨hD, hP⟩ := isDelzant_and_facetPolyhedron_eq hi hΔ hs
    (u := fun j : {p : N × ℝ | ∃ v ∈ Δ.extremePoints ℝ, p.1 ∈ s v ∧ p.2 = v (i p.1)} ↦
      (j : N × ℝ).1) (c := fun j ↦ (j : N × ℝ).2) (fun j ↦ j.property)
    (fun v hv n hn ↦ ⟨⟨(n, v (i n)), v, hv, hn, rfl⟩, rfl, rfl⟩) hne hc
    fun j j' h h' ↦ Subtype.ext (Prod.ext h h')
  exact ⟨_, hF, hD, hP⟩

/-- **Delzant polytopes, characterized by their vertex cones.** A subset `Δ` of `V*` is cut out
by the Delzant presentation of a finite set of pairs (inward normal, support constant) exactly when
it is nonempty, compact and convex with finitely many extreme points, and near each extreme point
`v` it is cut out by the inequalities `⟨v, n⟩ ≤ ⟨y, n⟩` for the members `n` of a `ℤ`-basis of the
lattice. -/
theorem exists_isDelzant_facetPolyhedron_eq_iff (hi : IsIntegralLattice i) :
    (∃ F : Set (N × ℝ), F.Finite ∧
      IsDelzant i (fun j : F ↦ (j : N × ℝ).1) (fun j : F ↦ (j : N × ℝ).2) ∧
      facetPolyhedron i (fun j : F ↦ (j : N × ℝ).1) (fun j : F ↦ (j : N × ℝ).2) = Δ) ↔
    Δ.Nonempty ∧ IsCompact Δ ∧ Convex ℝ Δ ∧ (Δ.extremePoints ℝ).Finite ∧
      ∀ v ∈ Δ.extremePoints ℝ, ∃ s : Set N, LinearIndepOn ℤ id s ∧
        Submodule.span ℤ s = ⊤ ∧ ∀ᶠ y in 𝓝 v, y ∈ Δ ↔ ∀ n ∈ s, v (i n) ≤ y (i n) := by
  refine ⟨?_, fun ⟨hne, hc, hΔ, hfin, hs⟩ ↦
    (existsUnique_isDelzant_facetPolyhedron_eq hi hne hc hΔ hfin hs).exists⟩
  rintro ⟨F, hF, hFΔ, rfl⟩
  have := hF.to_subtype
  have := hi.finiteDimensional
  refine ⟨hFΔ.nonempty, hFΔ.isCompact, convex_facetPolyhedron,
    finite_extremePoints_facetPolyhedron, fun v hv ↦ ?_⟩
  -- The corner at a vertex is cut out by its active facets, whose normals form a basis.
  obtain ⟨hli, hsp⟩ := isSmoothVertex_iff_linearIndepOn.1 (hFΔ.isSmoothVertex v hv)
  refine ⟨_, (linearIndepOn_iff_image hli.injOn).1 hli, hsp, ?_⟩
  have hvP := extremePoints_subset hv
  rw [facetPolyhedron_eq_polyhedron] at hvP
  filter_upwards [eventually_mem_polyhedron_iff (continuous_facetPairing _ _) hvP] with y hy
  rw [facetPolyhedron_eq_polyhedron, hy, forall_mem_image]
  refine forall₂_congr fun j _ ↦ ?_
  rw [map_sub, sub_nonneg, facetPairing_apply, facetPairing_apply]

end TauCeti.Toric
