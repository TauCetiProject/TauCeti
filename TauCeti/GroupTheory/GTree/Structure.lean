/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GTree.QuotientGraphOfGroups
public import TauCeti.GroupTheory.GraphOfGroups.BassSerre.Tree

/-!
# A tree with a group action is the Bass–Serre tree of its quotient graph of groups

Let a group `G` act on a tree `T` without inversions, let `D : T.Lifting` be a lifting of the
quotient graph `B = T / G`, and let `𝔹 = D.graphOfGroups` be the quotient graph of groups. For a
base vertex `b₀` of `B`, the fundamental group `π₁(𝔹, b₀)` is isomorphic to `G` by
`D.π₁Equiv b₀`, which sends the class of a closed `𝔹`-path `p` at `b₀` to its image in `G`: the
product of its vertex group elements, read in `G`, and of the elements `D.twist y` of its darts `y`.
This file shows that, through this isomorphism, `T` is the Bass–Serre tree `X(𝔹, b₀)` of `𝔹`.

The comparison maps send the vertex `p 𝔹_b` of `X(𝔹, b₀)` to the translate of the lifted vertex
`D.vertex b` by the image of `p` in `G`, and the dart `p α_y(𝔹_y)` over a dart `y` of `B` to the
translate of the lifted dart `D.dart y` by the image of `p`. They are bijective, commute with the
source and reversal maps, lie over the quotient graph `B` and are equivariant for `D.π₁Equiv b₀`;
together they form the isomorphism of Serre graphs `D.treeIso b₀` from `X(𝔹, b₀)` to `T`.

## Main definitions

* `TauCeti.GTree.Lifting.treeMapV`, `TauCeti.GTree.Lifting.treeMapE`: the comparison maps from the
  vertices and darts of the Bass–Serre tree of `D.graphOfGroups` to those of `T`.
* `TauCeti.GTree.Lifting.treeIso`: the isomorphism of Serre graphs from the Bass–Serre tree of
  `D.graphOfGroups` to `T`.

## Main results

* `TauCeti.GTree.Lifting.treeMapV_smul`, `TauCeti.GTree.Lifting.treeMapE_smul`: the comparison
  maps are equivariant for the isomorphism `D.π₁Equiv b₀ : π₁(𝔹, b₀) ≃* G`.
* `TauCeti.GTree.Lifting.quotientMap_mapV_treeMapV`,
  `TauCeti.GTree.Lifting.quotientMap_mapE_treeMapE`: the comparison maps lie over the quotient
  graph.
* `TauCeti.GTree.Lifting.treeMapV_bijective`, `TauCeti.GTree.Lifting.treeMapE_bijective`: the
  comparison maps are bijective.

## References

* I. Kapovich, R. Weidmann and A. Myasnikov, *Foldings, graphs of groups and the membership
  problem*, Internat. J. Algebra Comput. 15 (2005), §2, Proposition 2.6 and Remark 2.7.
* J.-P. Serre, *Trees*, Chapter I, §5.4, Theorem 13.
-/

public section

universe u v w

namespace TauCeti

open SerreGraph GraphOfGroups _root_.MulAction

namespace GTree

variable {G : Type w} [Group G] {T : GTree.{u, v} G}

namespace Lifting

variable (D : T.Lifting) (b₀ : T.quotient.V)

/-- The comparison map on vertices: the vertex `p 𝔹_b` of the Bass–Serre tree of the quotient
graph of groups maps to the translate of the lifted vertex `D.vertex b` by the image of `p` in
`G` (`GTree.Lifting.treeMapV_bassSerreVertex`). -/
noncomputable def treeMapV (x : (bassSerreTree D.graphOfGroups b₀).V) : T.V :=
  D.π₁TreeToGroup ((bassSerreVertex_surjective x).choose_spec.choose.toπ₁Tree D.tree.darts) •
    D.vertex (bassSerreVertex_surjective x).choose

/-- The comparison map on darts: the dart `p α_y(𝔹_y)` of the Bass–Serre tree of the quotient
graph of groups over a dart `y` of the quotient graph maps to the translate of the lifted dart
`D.dart y` by the image of `p` in `G` (`GTree.Lifting.treeMapE_bassSerreDart`). -/
noncomputable def treeMapE (d : (bassSerreTree D.graphOfGroups b₀).E) : T.E :=
  D.π₁TreeToGroup
      ((bassSerreDart_surjective d).choose_spec.choose_spec.choose.toπ₁Tree D.tree.darts) •
    D.dart (bassSerreDart_surjective d).choose_spec.choose_spec.choose_spec.choose.val

variable {D b₀}

-- Two `𝔹`-paths defining the same vertex of the Bass–Serre tree translate the lifted vertices of
-- their ends to the same vertex of `T`: the paths end at the same vertex `b` and differ by an
-- element of `𝔹_b`, the stabilizer of `D.vertex b`.
private theorem smul_vertex_eq_of_bassSerreVertex_eq {b c : T.quotient.V}
    {p : D.graphOfGroups.Path ⟨b₀⟩ ⟨b⟩} {q : D.graphOfGroups.Path ⟨b₀⟩ ⟨c⟩}
    (h : bassSerreVertex p = bassSerreVertex q) :
    D.π₁TreeToGroup (p.toπ₁Tree D.tree.darts) • D.vertex b =
      D.π₁TreeToGroup (q.toπ₁Tree D.tree.darts) • D.vertex c := by
  obtain rfl : b = c := by
    simpa using congrArg (bassSerreProjection D.graphOfGroups b₀).mapV h
  obtain ⟨g, hg⟩ := bassSerreVertex_eq_bassSerreVertex_iff.1 h
  simp [Path.Homotopic.toπ₁Tree_eq _ hg, mul_smul,
    mem_stabilizer_iff.mp (D.vertexGroupSubtype_mem b g)]

-- Two `𝔹`-paths and arrows defining the same dart of the Bass–Serre tree translate the lifted
-- darts to the same dart of `T`: the arrows are the same dart `y` of the quotient graph and the
-- paths differ by an element of `α_y(𝔹_y)`, which fixes `D.dart y`.
private theorem smul_dart_eq_of_bassSerreDart_eq {b c b' c' : T.quotient.V}
    {p : D.graphOfGroups.Path ⟨b₀⟩ ⟨b⟩} {e : b ⟶ c} {q : D.graphOfGroups.Path ⟨b₀⟩ ⟨b'⟩}
    {e' : b' ⟶ c'} (h : bassSerreDart p e = bassSerreDart q e') :
    D.π₁TreeToGroup (p.toπ₁Tree D.tree.darts) • D.dart e.val =
      D.π₁TreeToGroup (q.toπ₁Tree D.tree.darts) • D.dart e'.val := by
  obtain ⟨y, rfl, rfl⟩ := e
  obtain ⟨y', rfl, rfl⟩ := e'
  obtain rfl : y = y' := by
    simpa using congrArg (bassSerreProjection D.graphOfGroups b₀).mapE h
  obtain ⟨c₀, hc₀⟩ := bassSerreDart_eq_bassSerreDart_iff.1 h
  simp [Path.Homotopic.toπ₁Tree_eq _ hc₀, mul_smul,
    mem_stabilizer_iff.mp (D.mem_range_α_iff.mp ⟨c₀, rfl⟩)]

/-- The comparison map sends the vertex `p 𝔹_b` of the Bass–Serre tree to the translate of
`D.vertex b` by the image of `p` in `G`. -/
@[simp] theorem treeMapV_bassSerreVertex {b : T.quotient.V} (p : D.graphOfGroups.Path ⟨b₀⟩ ⟨b⟩) :
    D.treeMapV b₀ (bassSerreVertex p) = D.π₁TreeToGroup (p.toπ₁Tree D.tree.darts) • D.vertex b :=
  smul_vertex_eq_of_bassSerreVertex_eq (bassSerreVertex_surjective _).choose_spec.choose_spec

/-- The comparison map sends the dart `p α_e(𝔹_e)` of the Bass–Serre tree, for an arrow `e` of the
quotient graph, to the translate of the lifted dart `D.dart e.val` by the image of `p` in `G`. -/
@[simp] theorem treeMapE_bassSerreDart {b c : T.quotient.V} (p : D.graphOfGroups.Path ⟨b₀⟩ ⟨b⟩)
    (e : b ⟶ c) :
    D.treeMapE b₀ (bassSerreDart p e) = D.π₁TreeToGroup (p.toπ₁Tree D.tree.darts) • D.dart e.val :=
  smul_dart_eq_of_bassSerreDart_eq
    (bassSerreDart_surjective _).choose_spec.choose_spec.choose_spec.choose_spec

variable (D b₀)

/-- The comparison maps commute with the source maps. -/
@[simp] theorem src_treeMapE (d : (bassSerreTree D.graphOfGroups b₀).E) :
    T.src (D.treeMapE b₀ d) = D.treeMapV b₀ ((bassSerreTree D.graphOfGroups b₀).src d) := by
  obtain ⟨_, _, p, ⟨y, rfl, rfl⟩, rfl⟩ := bassSerreDart_surjective d
  simp

/-- The comparison maps commute with reversal. -/
@[simp] theorem treeMapE_rev (d : (bassSerreTree D.graphOfGroups b₀).E) :
    D.treeMapE b₀ ((bassSerreTree D.graphOfGroups b₀).rev d) = T.rev (D.treeMapE b₀ d) := by
  obtain ⟨_, _, p, ⟨y, rfl, rfl⟩, rfl⟩ := bassSerreDart_surjective d
  simp [mul_smul, D.twist_smul_dart_rev]

/-- The comparison map on vertices lies over the quotient graph. -/
@[simp] theorem quotientMap_mapV_treeMapV (x : (bassSerreTree D.graphOfGroups b₀).V) :
    T.quotientMap.mapV (D.treeMapV b₀ x) = (bassSerreProjection D.graphOfGroups b₀).mapV x := by
  obtain ⟨b, p, rfl⟩ := bassSerreVertex_surjective x
  simp

/-- The comparison map on darts lies over the quotient graph. -/
@[simp] theorem quotientMap_mapE_treeMapE (d : (bassSerreTree D.graphOfGroups b₀).E) :
    T.quotientMap.mapE (D.treeMapE b₀ d) = (bassSerreProjection D.graphOfGroups b₀).mapE d := by
  obtain ⟨_, _, p, e, rfl⟩ := bassSerreDart_surjective d
  simp

/-- The comparison map on vertices is equivariant for the isomorphism
`D.π₁Equiv b₀ : π₁(𝔹, b₀) ≃* G`. -/
@[simp] theorem treeMapV_smul (g : π₁ D.graphOfGroups b₀)
    (x : (bassSerreTree D.graphOfGroups b₀).V) :
    D.treeMapV b₀ (g • x) = D.π₁Equiv b₀ g • D.treeMapV b₀ x := by
  obtain ⟨b, p, rfl⟩ := bassSerreVertex_surjective x
  induction g using π₁.induction_on with | h γ => ?_
  simp [mul_smul]

/-- The comparison map on darts is equivariant for the isomorphism
`D.π₁Equiv b₀ : π₁(𝔹, b₀) ≃* G`. -/
@[simp] theorem treeMapE_smul (g : π₁ D.graphOfGroups b₀)
    (d : (bassSerreTree D.graphOfGroups b₀).E) :
    D.treeMapE b₀ (g • d) = D.π₁Equiv b₀ g • D.treeMapE b₀ d := by
  obtain ⟨_, _, p, e, rfl⟩ := bassSerreDart_surjective d
  induction g using π₁.induction_on with | h γ => ?_
  simp [mul_smul]

variable {D b₀}

-- The comparison map is injective on the darts issuing from each vertex: two darts issuing from
-- `p 𝔹_b` with the same image lie over the same dart `y` of the quotient graph and differ by an
-- element of `𝔹_b` fixing `D.dart y`, that is, by an element of the image of `α_y`.
private theorem treeMapE_injective_of_src_eq {d d' : (bassSerreTree D.graphOfGroups b₀).E}
    (hs : (bassSerreTree D.graphOfGroups b₀).src d = (bassSerreTree D.graphOfGroups b₀).src d')
    (h : D.treeMapE b₀ d = D.treeMapE b₀ d') : d = d' := by
  obtain ⟨_, _, p, ⟨y, rfl, rfl⟩, rfl⟩ := bassSerreDart_surjective d
  obtain ⟨_, _, q, ⟨y', rfl, rfl⟩, rfl⟩ := bassSerreDart_surjective d'
  obtain rfl : y = y' := by simpa using congrArg T.quotientMap.mapE h
  rw [src_bassSerreDart, src_bassSerreDart] at hs
  obtain ⟨g, hg⟩ := bassSerreVertex_eq_bassSerreVertex_iff.1 hs
  simp only [treeMapE_bassSerreDart, Path.Homotopic.toπ₁Tree_eq _ hg, Path.toπ₁Tree_cons,
    Letter.toπ₁Tree_vertex, map_mul, π₁TreeToGroup_of, mul_smul, smul_left_cancel_iff] at h
  obtain ⟨c₀, rfl⟩ :=
    (D.mem_range_αArrow_iff (e := ⟨y, rfl, rfl⟩)).mpr (mem_stabilizer_iff.mpr h.symm)
  rw [bassSerreDart_congr hg, bassSerreDart_cons_vertex_αArrow]

-- Every dart of `T` issuing from the image of a vertex of the Bass–Serre tree is the image of a
-- dart: every dart issuing from a lifted vertex is a translate of a lifted dart by an element of
-- the stabilizer of that vertex.
private theorem mem_range_treeMapE {t : T.E} (ht : T.src t ∈ Set.range (D.treeMapV b₀)) :
    t ∈ Set.range (D.treeMapE b₀) := by
  obtain ⟨x, hx⟩ := ht
  obtain ⟨b, p, rfl⟩ := bassSerreVertex_surjective x
  rw [treeMapV_bassSerreVertex] at hx
  have hsrc : T.src ((D.π₁TreeToGroup (p.toπ₁Tree D.tree.darts))⁻¹ • t) = D.vertex b := by
    rw [src_smul, ← hx, inv_smul_smul]
  obtain ⟨g, hg, hgt⟩ := D.exists_smul_dart_eq hsrc
  rw [← D.range_vertexGroupSubtype] at hg
  obtain ⟨g, rfl⟩ := hg
  rw [quotientMap_mapE_smul] at hgt
  have hy : T.quotient.src (T.quotientMap.mapE t) = b := by
    rw [T.quotientMap.map_src, ← hx, quotientMap_mapV_smul, D.quotientMap_vertex]
  refine ⟨bassSerreDart (p.cons (.vertex g)) ⟨_, hy, rfl⟩, ?_⟩
  simp [mul_smul, hgt]

variable (D b₀)

/-- **Structure theorem for groups acting on trees.** A tree `T` with an action of `G` without
inversions is isomorphic to the Bass–Serre tree of its quotient graph of groups: this is the
isomorphism of Serre graphs from the Bass–Serre tree of `D.graphOfGroups` at `b₀` to `T` whose maps
are the comparison maps `treeMapV`, `treeMapE` (`GTree.Lifting.treeIso_equivV_apply`,
`GTree.Lifting.treeIso_equivE_apply`). It is equivariant for `D.π₁Equiv b₀ : π₁(𝔹, b₀) ≃* G`
(`GTree.Lifting.treeMapV_smul`, `GTree.Lifting.treeMapE_smul`) and lies over the quotient graph. -/
noncomputable def treeIso : (bassSerreTree D.graphOfGroups b₀).Iso T.toSerreGraph :=
  -- The comparison morphism is injective on the darts issuing from each vertex and every dart
  -- issuing from the image of a vertex is the image of a dart; since the Bass–Serre tree is
  -- connected and `T` is a tree, such a morphism is an isomorphism.
  Iso.ofLocallyBijective
    { mapV := D.treeMapV b₀
      mapE := D.treeMapE b₀
      map_src := D.src_treeMapE b₀
      map_rev := D.treeMapE_rev b₀ }
    (bassSerreTree D.graphOfGroups b₀).preconnected T.preconnected T.isAcyclic
    (fun _ _ => treeMapE_injective_of_src_eq) fun _ => mem_range_treeMapE

/-- The isomorphism `treeIso` is the comparison map on vertices. -/
@[simp] theorem treeIso_equivV_apply (x : (bassSerreTree D.graphOfGroups b₀).V) :
    (D.treeIso b₀).equivV x = D.treeMapV b₀ x :=
  Iso.ofLocallyBijective_equivV_apply ..

/-- The isomorphism `treeIso` is the comparison map on darts. -/
@[simp] theorem treeIso_equivE_apply (d : (bassSerreTree D.graphOfGroups b₀).E) :
    (D.treeIso b₀).equivE d = D.treeMapE b₀ d :=
  Iso.ofLocallyBijective_equivE_apply ..

/-- The comparison map on vertices is a bijection. -/
theorem treeMapV_bijective : Function.Bijective (D.treeMapV b₀) := by
  rw [← funext (D.treeIso_equivV_apply b₀)]
  exact (D.treeIso b₀).equivV.bijective

/-- The comparison map on darts is a bijection. -/
theorem treeMapE_bijective : Function.Bijective (D.treeMapE b₀) := by
  rw [← funext (D.treeIso_equivE_apply b₀)]
  exact (D.treeIso b₀).equivE.bijective

end Lifting

end GTree

end TauCeti
