/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Serre.BarycentricSubdivision
public import TauCeti.GroupTheory.GTree.Basic

/-!
# Removing inversions by barycentric subdivision

An action of a group `G` on a tree by graph automorphisms may have inversions: an element may
map a dart to its reverse. The induced action on the barycentric subdivision has none, so the
subdivision is a `G`-tree, `GTree.ofBarycentricSubdivision`. An element is elliptic in it exactly
when it fixes a vertex or inverts an edge of the original tree: an inverted edge contributes its
midpoint as a fixed vertex. When the action already has no inversions, the tree and its
subdivision dominate each other, so they lie in the same deformation space.

The group of order two acts on the segment by exchanging its two vertices,
`SerreGraph.segmentSwapHom`. This action inverts the edge, so the segment with this action is not
a `G`-tree; in the subdivided segment the whole group fixes the midpoint, while the generator
still exchanges the two original vertices.

## Main declarations

* `TauCeti.GTree.ofBarycentricSubdivision`: the `G`-tree on the barycentric subdivision of a tree
  with an action of `G`.
* `TauCeti.GTree.isElliptic_ofBarycentricSubdivision_iff`: its elliptic elements.
* `TauCeti.GTree.sameDeformationSpace_ofBarycentricSubdivision`: a `G`-tree and its subdivision
  lie in the same deformation space.
* `TauCeti.GTree.isEllipticSubgroup_ofBarycentricSubdivision_segment`: the group of order two
  acting on the subdivided segment fixes a vertex.

## References

* J.-P. Serre, *Trees*, Chapter I, §2.1 and §3.1.
* V. Guirardel and G. Levitt, *JSJ decompositions of groups*, Astérisque 395 (2017), §1.2.
-/

public section

universe u v w

namespace TauCeti

open SerreGraph _root_.MulAction

namespace GTree

variable {G : Type w} [Group G] {Γ : SerreGraph.{u, v}}

/-- The `G`-tree on the barycentric subdivision of a tree `Γ` with an action of `G` by graph
automorphisms, possibly with inversions. The body is exposed so that the vertices and darts of
`Γ.barycentricSubdivision` are vertices and darts of this tree. -/
@[expose] def ofBarycentricSubdivision (hΓ : Γ.IsTree) (ρ : G →* Γ.Aut) :
    GTree.{max u v, v} G where
  toSerreGraph := Γ.barycentricSubdivision
  isTree := hΓ.barycentricSubdivision
  action := Aut.barycentricSubdivision.comp ρ
  action_smul_ne_rev g e := Aut.barycentricSubdivision_smul_ne_rev (ρ g) e

variable (hΓ : Γ.IsTree) (ρ : G →* Γ.Aut)

/-- The action on the subdivided tree is the one induced by the action on the tree. -/
theorem ofBarycentricSubdivision_action (g : G) :
    (ofBarycentricSubdivision hΓ ρ).action g = Aut.barycentricSubdivision (ρ g) := (rfl)

-- In the next three statements the argument `β` makes the vertex or dart of
-- `Γ.barycentricSubdivision` a vertex or dart of the subdivided tree, on which `G` acts.

/-- An element acts on the vertices of the tree, seen in the subdivided tree, as before. -/
@[simp] theorem ofBarycentricSubdivision_smul_barycentricVertex (g : G) (v : Γ.V) :
    HSMul.hSMul (β := (ofBarycentricSubdivision hΓ ρ).V) g (Γ.barycentricVertex v) =
      Γ.barycentricVertex (ρ g • v) :=
  Aut.barycentricSubdivision_smul_barycentricVertex (ρ g) v

/-- An element acts on the midpoints of the subdivided tree as on the geometric edges. -/
@[simp] theorem ofBarycentricSubdivision_smul_barycentricMidpoint (g : G) (m : Γ.GeomEdge) :
    HSMul.hSMul (β := (ofBarycentricSubdivision hΓ ρ).V) g (Γ.barycentricMidpoint m) =
      Γ.barycentricMidpoint (ρ g • m) :=
  Aut.barycentricSubdivision_smul_barycentricMidpoint (ρ g) m

/-- An element maps each half of a dart to the same half of the image dart. -/
@[simp] theorem ofBarycentricSubdivision_smul_barycentricDart (g : G) (e : Γ.E) (b : Bool) :
    HSMul.hSMul (β := (ofBarycentricSubdivision hΓ ρ).E) g (Γ.barycentricDart e b) =
      Γ.barycentricDart (ρ g • e) b :=
  Aut.barycentricSubdivision_smul_barycentricDart (ρ g) e b

/-- An element is elliptic in the subdivided tree exactly when it fixes a vertex or inverts an
edge of the original tree. -/
theorem isElliptic_ofBarycentricSubdivision_iff {g : G} :
    (ofBarycentricSubdivision hΓ ρ).IsElliptic g ↔
      (∃ v : Γ.V, ρ g • v = v) ∨ ∃ e : Γ.E, ρ g • e = Γ.rev e := by
  rw [isElliptic_iff]
  constructor
  · rintro ⟨x, hx⟩
    induction x using barycentricSubdivision_vertex_cases with
    | vertex v =>
      rw [ofBarycentricSubdivision_smul_barycentricVertex] at hx
      exact .inl ⟨v, Γ.barycentricVertex_injective hx⟩
    | midpoint m =>
      obtain ⟨e, rfl⟩ := Γ.toGeomEdge_surjective m
      rcases (Aut.barycentricSubdivision_smul_barycentricMidpoint_eq_iff (ρ g) e).mp hx with h | h
      · exact .inl ⟨Γ.src e, by rw [← Aut.src_smul, h]⟩
      · exact .inr ⟨e, h⟩
  · rintro (⟨v, hv⟩ | ⟨e, he⟩)
    · exact ⟨Γ.barycentricVertex v, by rw [ofBarycentricSubdivision_smul_barycentricVertex, hv]⟩
    · exact ⟨Γ.barycentricMidpoint (Γ.toGeomEdge e),
        (Aut.barycentricSubdivision_smul_barycentricMidpoint_eq_iff (ρ g) e).mpr (.inr he)⟩

/-! ### Subdividing a `G`-tree -/

variable (T : GTree.{u, v} G)

/-- A `G`-tree dominates its barycentric subdivision: its vertices are vertices of the
subdivision. -/
theorem dominates_ofBarycentricSubdivision :
    T.Dominates (ofBarycentricSubdivision T.isTree T.action) :=
  dominates_iff_nonempty.mpr ⟨{
    toFun := T.barycentricVertex
    map_smul' := fun g v =>
      (ofBarycentricSubdivision_smul_barycentricVertex T.isTree T.action g v).symm }⟩

/-- The barycentric subdivision of a `G`-tree dominates it: as there are no inversions, an
element fixing the midpoint of a dart fixes the source of the dart. -/
theorem ofBarycentricSubdivision_dominates :
    (ofBarycentricSubdivision T.isTree T.action).Dominates T := by
  refine dominates_iff.mpr fun x => ?_
  induction x using barycentricSubdivision_vertex_cases with
  | vertex v =>
    refine isEllipticSubgroup_iff_forall.mpr ⟨v, fun g hg => T.barycentricVertex_injective ?_⟩
    exact (ofBarycentricSubdivision_smul_barycentricVertex T.isTree T.action g v).symm.trans
      (mem_stabilizer_iff.mp hg)
  | midpoint m =>
    obtain ⟨e, rfl⟩ := T.toGeomEdge_surjective m
    refine isEllipticSubgroup_iff_forall.mpr ⟨T.src e, fun g hg => ?_⟩
    have h := (Aut.barycentricSubdivision_smul_barycentricMidpoint_eq_iff (T.action g) e).mp
      (mem_stabilizer_iff.mp hg)
    rw [← src_smul, smul_dart_def, h.resolve_right (T.action_smul_ne_rev g e)]

/-- A `G`-tree and its barycentric subdivision lie in the same deformation space. -/
theorem sameDeformationSpace_ofBarycentricSubdivision :
    T.SameDeformationSpace (ofBarycentricSubdivision T.isTree T.action) :=
  sameDeformationSpace_iff.mpr
    ⟨dominates_ofBarycentricSubdivision T, ofBarycentricSubdivision_dominates T⟩

/-! ### The group of order two acting on the segment -/

/-- After barycentric subdivision of the segment, the group of order two fixes the midpoint. -/
theorem isEllipticSubgroup_ofBarycentricSubdivision_segment :
    (ofBarycentricSubdivision segment_isTree segmentSwapHom).IsEllipticSubgroup ⊤ :=
  isEllipticSubgroup_iff_forall.mpr ⟨segment.barycentricMidpoint default, fun g _ => by
    rw [ofBarycentricSubdivision_smul_barycentricMidpoint]
    exact congrArg _ (Subsingleton.elim _ _)⟩

/-- After barycentric subdivision of the segment, the generator of the group of order two is
elliptic. -/
theorem isElliptic_ofBarycentricSubdivision_segment :
    (ofBarycentricSubdivision segment_isTree segmentSwapHom).IsElliptic
      (Multiplicative.ofAdd 1) :=
  isEllipticSubgroup_ofBarycentricSubdivision_segment.isElliptic (Subgroup.mem_top _)

/-- In the subdivided segment, the midpoint is the only vertex fixed by the generator of the
group of order two. -/
theorem ofBarycentricSubdivision_segment_ofAdd_one_smul_eq_iff
    (x : (ofBarycentricSubdivision segment_isTree segmentSwapHom).V) :
    Multiplicative.ofAdd (1 : ZMod 2) • x = x ↔ x = segment.barycentricMidpoint default := by
  induction x using barycentricSubdivision_vertex_cases with
  | vertex v =>
    obtain ⟨e, rfl⟩ := segment_src_surjective v
    rw [ofBarycentricSubdivision_smul_barycentricVertex, segmentSwapHom_ofAdd_one,
      segmentSwap_smul_src]
    exact iff_of_false
      (fun h => segment_isTree.isAcyclic.src_ne_tgt e (segment.barycentricVertex_injective h).symm)
      (segment.barycentricVertex_ne_barycentricMidpoint _ _)
  | midpoint m =>
    obtain rfl : m = default := Subsingleton.elim _ _
    rw [ofBarycentricSubdivision_smul_barycentricMidpoint]
    exact iff_of_true (congrArg _ (Subsingleton.elim _ _)) rfl

end GTree

end TauCeti
