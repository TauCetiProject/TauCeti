/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Serre.Between
public import TauCeti.GroupTheory.GTree.Collapse

/-!
# Collapse maps, refinements and geodesic morphisms of group actions on trees

Let `T` and `T'` be `G`-trees. Equivariant maps between them are given on vertices.

* A *collapse map* is a surjective equivariant map under which the preimage of every convex set
  of vertices is convex: the preimage of every subtree is a subtree. The identity is a collapse
  map, collapse maps compose, and the map from a tree to its collapse along an invariant set of
  edges is a collapse map (`TauCeti.GTree.isCollapseMap_collapseHom`). A collapse map preserves
  betweenness (`TauCeti.GTree.IsCollapseMap.isBetween`).
* `T` *refines* `T'` when there is a collapse map from `T` to `T'`. Refinement is reflexive and
  transitive, a tree refines each of its collapses, and a refinement of a tree dominates it.
* A *geodesic morphism* is an equivariant map which identifies the two ends of no dart. Extended
  to each edge by the geodesic between the images of its ends, it collapses no edge to a point:
  it is a morphism in the sense of Guirardel and Levitt which maps each edge onto an arc. Their
  morphisms send edges to edge paths, which may backtrack, so a morphism may fold an edge onto
  itself and send its two ends to the same vertex; the vertex map of such a morphism is not a
  geodesic morphism.
  Conversely, a morphism maps each edge onto an edge once the source tree is suitably
  subdivided, and the vertex map of the subdivided tree is then a geodesic morphism.
* The stabilizer of a dart of the source of a geodesic morphism fixes a dart of the target
  (`TauCeti.GTree.IsGeodesicMorphism.exists_stabilizer_le`), so a tree with a geodesic morphism
  to a tree relative to families `𝒜` and `ℋ` of subgroups is relative to them as soon as `𝒜` is
  closed under passing to subgroups and the members of `ℋ` are elliptic in it. Injective
  equivariant maps are geodesic morphisms, and a collapse map is a geodesic morphism exactly
  when it is injective (`TauCeti.GTree.IsCollapseMap.isGeodesicMorphism_iff_injective`): the map
  from a tree to a collapse is a geodesic morphism exactly when no edge is collapsed.

## Main declarations

* `TauCeti.GTree.IsCollapseMap`, `TauCeti.GTree.Refines`: collapse maps and refinements.
* `TauCeti.GTree.IsGeodesicMorphism`: equivariant maps identifying the two ends of no dart.
* `TauCeti.GTree.IsGeodesicMorphism.exists_stabilizer_le`,
  `TauCeti.GTree.IsRelative.of_isGeodesicMorphism`: dart stabilizers under a geodesic morphism.
* `TauCeti.GTree.IsCollapseMap.isGeodesicMorphism_iff_injective`: collapse maps that are
  geodesic morphisms.

## References

* V. Guirardel and G. Levitt, *JSJ decompositions of groups*, Astérisque 395 (2017), §1.4.1
  (morphisms, collapse maps, refinements; collapse maps preserve alignment).
-/

public section

universe u v u' v' u'' v'' w

namespace TauCeti

open SerreGraph _root_.MulAction

namespace GTree

variable {G : Type w} [Group G] {T : GTree.{u, v} G} {T' : GTree.{u', v'} G}
  {T'' : GTree.{u'', v''} G}

/-! ### Collapse maps -/

/-- An equivariant map of vertices is a *collapse map* when it is surjective and the preimage of
every convex set of vertices is convex. -/
def IsCollapseMap (f : T.V →[G] T'.V) : Prop :=
  Function.Surjective f ∧ ∀ S : Set T'.V, T'.IsConvex S → T.IsConvex (f ⁻¹' S)

/-- Unfold the definition of a collapse map. -/
theorem isCollapseMap_iff {f : T.V →[G] T'.V} : IsCollapseMap f ↔
    Function.Surjective f ∧ ∀ S : Set T'.V, T'.IsConvex S → T.IsConvex (f ⁻¹' S) := Iff.rfl

/-- A collapse map is surjective. -/
theorem IsCollapseMap.surjective {f : T.V →[G] T'.V} (hf : IsCollapseMap f) :
    Function.Surjective f :=
  hf.1

/-- The preimage of a convex set of vertices under a collapse map is convex. -/
theorem IsCollapseMap.isConvex_preimage {f : T.V →[G] T'.V} (hf : IsCollapseMap f) {S : Set T'.V}
    (hS : T'.IsConvex S) : T.IsConvex (f ⁻¹' S) :=
  hf.2 S hS

/-- A collapse map preserves betweenness: a vertex between `a` and `b` is sent to a vertex
between the images of `a` and `b`. -/
theorem IsCollapseMap.isBetween {f : T.V →[G] T'.V} (hf : IsCollapseMap f) {a x b : T.V}
    (h : T.IsBetween a x b) : T'.IsBetween (f a) (f x) (f b) := by
  -- The vertices between `f a` and `f b` form a convex set. Its preimage is convex and contains
  -- `a` and `b`, so it contains the reduced path from `a` to `b`, whose vertices are those
  -- between `a` and `b`.
  obtain ⟨q⟩ := h.nonempty_path
  have hq := Path.isReduced_reduce T.toSerreGraph q
  refine (hf.isConvex_preimage (T'.isAcyclic.isConvex_setOf_isBetween _ _)).convexHull_subset
    (Set.pair_subset (isBetween_left (T'.nonempty_path _ _))
      (isBetween_right (T'.nonempty_path _ _))) ?_
  rw [T.isAcyclic.convexHull_pair hq]
  exact (T.isAcyclic.isBetween_iff_mem_vertices hq).mp h

variable (T) in
/-- The identity of a `G`-tree is a collapse map. -/
@[simp] theorem isCollapseMap_id : IsCollapseMap (MulActionHom.id G : T.V →[G] T.V) :=
  ⟨Function.surjective_id, fun _ hS => hS⟩

/-- A composite of collapse maps is a collapse map. -/
theorem IsCollapseMap.comp {g : T'.V →[G] T''.V} {f : T.V →[G] T'.V} (hg : IsCollapseMap g)
    (hf : IsCollapseMap f) : IsCollapseMap (g.comp f) :=
  ⟨hg.surjective.comp hf.surjective, fun _ hS => hf.isConvex_preimage (hg.isConvex_preimage hS)⟩

/-- The collapse of a `G`-tree along an invariant set of edges is a collapse map. -/
@[simp] theorem isCollapseMap_collapseHom (S : Set T.E) (hS : ∀ e ∈ S, T.rev e ∈ S)
    (hG : ∀ g : G, ∀ e ∈ S, g • e ∈ S) : IsCollapseMap (T.collapseHom S hS hG) :=
  ⟨T.collapseHom_surjective S hS hG, fun _ => isConvex_collapseHom_preimage hS hG⟩

/-! ### Refinements -/

variable (T T') in
/-- `T` *refines* `T'` when there is a collapse map from `T` to `T'`. -/
def Refines : Prop :=
  ∃ f : T.V →[G] T'.V, IsCollapseMap f

/-- Unfold the definition of refinement. -/
theorem refines_iff : T.Refines T' ↔ ∃ f : T.V →[G] T'.V, IsCollapseMap f := Iff.rfl

variable (T) in
/-- Every `G`-tree refines itself. -/
@[simp] theorem Refines.refl : T.Refines T :=
  ⟨MulActionHom.id G, isCollapseMap_id T⟩

/-- Refinement is transitive. -/
theorem Refines.trans (h : T.Refines T') (h' : T'.Refines T'') : T.Refines T'' :=
  let ⟨f, hf⟩ := h
  let ⟨g, hg⟩ := h'
  ⟨g.comp f, hg.comp hf⟩

/-- A refinement of a tree dominates it. -/
theorem Refines.dominates (h : T.Refines T') : T.Dominates T' :=
  let ⟨f, _⟩ := h
  dominates_iff_nonempty.mpr ⟨f⟩

variable (T) in
/-- A `G`-tree refines its collapse along an invariant set of edges. -/
@[simp] theorem refines_collapse (S : Set T.E) (hS : ∀ e ∈ S, T.rev e ∈ S)
    (hG : ∀ g : G, ∀ e ∈ S, g • e ∈ S) : T.Refines (T.collapse S hS hG) :=
  ⟨T.collapseHom S hS hG, isCollapseMap_collapseHom S hS hG⟩

/-! ### Geodesic morphisms -/

/-- An equivariant map of vertices is a *geodesic morphism* when it identifies the two ends of no
dart. Extended to each edge by the geodesic between the images of its ends, it is then a morphism
of trees which collapses no edge to a point. The vertex map of a morphism which folds an edge onto
itself along a backtracking edge path, so that the two ends of the edge have the same image, is
not a geodesic morphism. A composite of geodesic morphisms need not be one: the first may send a
dart to a geodesic of length two which the second folds onto a single edge. -/
def IsGeodesicMorphism (f : T.V →[G] T'.V) : Prop :=
  ∀ e : T.E, f (T.src e) ≠ f (T.tgt e)

/-- Unfold the definition of a geodesic morphism. -/
theorem isGeodesicMorphism_iff {f : T.V →[G] T'.V} : IsGeodesicMorphism f ↔
    ∀ e : T.E, f (T.src e) ≠ f (T.tgt e) := Iff.rfl

/-- An injective equivariant map of vertices is a geodesic morphism. -/
theorem IsGeodesicMorphism.of_injective {f : T.V →[G] T'.V} (hf : Function.Injective f) :
    IsGeodesicMorphism f :=
  fun e h => T.isAcyclic.src_ne_tgt e (hf h)

variable (T) in
/-- The identity of a `G`-tree is a geodesic morphism. -/
@[simp] theorem isGeodesicMorphism_id : IsGeodesicMorphism (MulActionHom.id G : T.V →[G] T.V) :=
  .of_injective Function.injective_id

/-- A collapse map is a geodesic morphism exactly when it is injective: a collapse map that is
not injective collapses some edge. -/
theorem IsCollapseMap.isGeodesicMorphism_iff_injective {f : T.V →[G] T'.V}
    (hf : IsCollapseMap f) : IsGeodesicMorphism f ↔ Function.Injective f := by
  refine ⟨fun h x y hxy => ?_, .of_injective⟩
  by_contra hne
  -- A dart of the reduced path from `x` to `y` has both ends in the convex fibre of `f y`.
  obtain ⟨p⟩ := T.nonempty_path x y
  have hp := Path.isReduced_reduce T.toSerreGraph p
  obtain ⟨d, hd⟩ := List.exists_mem_of_ne_nil _ fun h0 =>
    hne (Path.eq_of_darts_eq_nil _ (Path.reduce T.toSerreGraph p) h0)
  have hC := hf.isConvex_preimage (T'.isAcyclic.isConvex_singleton (f y))
  have hs : f (T.src d) = f y := isConvex_iff.mp hC x hxy y rfl _ hp d hd
  exact h d (hs.trans (hC.tgt_mem hxy rfl hp hd).symm)

/-- The map from a `G`-tree to its collapse along an invariant set of edges is a geodesic morphism
exactly when no edge is collapsed. -/
@[simp] theorem isGeodesicMorphism_collapseHom_iff {S : Set T.E} (hS : ∀ e ∈ S, T.rev e ∈ S)
    (hG : ∀ g : G, ∀ e ∈ S, g • e ∈ S) :
    IsGeodesicMorphism (T.collapseHom S hS hG) ↔ S = ∅ := by
  rw [(isCollapseMap_collapseHom S hS hG).isGeodesicMorphism_iff_injective,
    collapseHom_injective_iff]

/-- Under a geodesic morphism, the stabilizer of a dart of the source fixes a dart of the
target. -/
theorem IsGeodesicMorphism.exists_stabilizer_le {f : T.V →[G] T'.V} (hf : IsGeodesicMorphism f)
    (e : T.E) : ∃ e' : T'.E, stabilizer G e ≤ stabilizer G e' := by
  -- Take a dart of the reduced path joining the distinct images of the ends of `e`.
  obtain ⟨p⟩ := T'.nonempty_path (f (T.src e)) (f (T.tgt e))
  obtain ⟨e', he'⟩ := List.exists_mem_of_ne_nil _ fun h0 =>
    hf e (Path.eq_of_darts_eq_nil _ (Path.reduce T'.toSerreGraph p) h0)
  refine ⟨e', fun g hg => mem_stabilizer_iff.mpr ?_⟩
  -- An element fixing `e` fixes the images of its ends, hence the path between them.
  have hs : g • f (T.src e) = f (T.src e) := by
    rw [← map_smul, ← src_smul, mem_stabilizer_iff.mp hg]
  have ht : g • f (T.tgt e) = f (T.tgt e) := by
    rw [← map_smul, ← tgt_smul, mem_stabilizer_iff.mp hg]
  exact Aut.smul_eq_of_mem_darts T'.isAcyclic (T'.action g) hs ht
    (Path.isReduced_reduce _ p) he'

/-- A tree with a geodesic morphism to a tree relative to `𝒜` and `ℋ` is relative to `𝒜` and
`ℋ`, when `𝒜` is closed under passing to subgroups and the members of `ℋ` are elliptic in it. -/
theorem IsRelative.of_isGeodesicMorphism {𝒜 ℋ : Set (Subgroup G)} {f : T.V →[G] T'.V}
    (hT' : T'.IsRelative 𝒜 ℋ) (hf : IsGeodesicMorphism f) (h𝒜 : ∀ A ∈ 𝒜, ∀ B ≤ A, B ∈ 𝒜)
    (hℋ : ∀ H ∈ ℋ, T.IsEllipticSubgroup H) : T.IsRelative 𝒜 ℋ := by
  refine isRelative_iff.mpr ⟨fun e => ?_, hℋ⟩
  obtain ⟨e', he'⟩ := hf.exists_stabilizer_le e
  exact h𝒜 _ (hT'.stabilizer_mem e') _ he'

end GTree

end TauCeti
