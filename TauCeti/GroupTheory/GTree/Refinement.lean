/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GTree.Collapse

/-!
# Collapse maps, refinements and morphisms of group actions on trees

Let `T` and `T'` be `G`-trees. Equivariant maps between them are given on vertices.

* A *collapse map* is a surjective equivariant map under which the preimage of every convex set
  of vertices is convex: the preimage of every subtree is a subtree. The identity is a collapse
  map, collapse maps compose, and the map from a tree to its collapse along an invariant set of
  edges is a collapse map (`TauCeti.GTree.isCollapseMap_collapseHom`).
* `T` *refines* `T'` when there is a collapse map from `T` to `T'`. Refinement is reflexive and
  transitive, a tree refines each of its collapses, and a refinement of a tree dominates it.
* A *morphism* is an equivariant map which identifies the two ends of no dart: extended to the
  edges by geodesics, it collapses no edge. The stabilizer of a dart of the source then fixes a
  dart of the target (`TauCeti.GTree.IsMorphism.exists_stabilizer_le`), so a tree with a
  morphism to a tree relative to families `𝒜` and `ℋ` of subgroups is relative to them as soon
  as `𝒜` is closed under passing to subgroups and the members of `ℋ` are elliptic in it.
  Injective equivariant maps are morphisms, and a collapse map is a morphism exactly when it is
  injective (`TauCeti.GTree.IsCollapseMap.isMorphism_iff_injective`): the map from a tree to a
  collapse is a morphism exactly when no edge is collapsed.

## Main declarations

* `TauCeti.GTree.IsCollapseMap`, `TauCeti.GTree.Refines`: collapse maps and refinements.
* `TauCeti.GTree.IsMorphism`: morphisms of trees with a group action.
* `TauCeti.GTree.IsMorphism.exists_stabilizer_le`, `TauCeti.GTree.IsRelative.of_isMorphism`:
  dart stabilizers under a morphism.
* `TauCeti.GTree.IsCollapseMap.isMorphism_iff_injective`: collapse maps that are morphisms.

## References

* V. Guirardel and G. Levitt, *JSJ decompositions of groups*, Astérisque 395 (2017), §1.4.1
  (morphisms, collapse maps, refinements).
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

variable (T) in
/-- The identity of a `G`-tree is a collapse map. -/
theorem isCollapseMap_id : IsCollapseMap (MulActionHom.id G : T.V →[G] T.V) :=
  ⟨Function.surjective_id, fun _ hS => hS⟩

/-- A composite of collapse maps is a collapse map. -/
theorem IsCollapseMap.comp {g : T'.V →[G] T''.V} {f : T.V →[G] T'.V} (hg : IsCollapseMap g)
    (hf : IsCollapseMap f) : IsCollapseMap (g.comp f) :=
  ⟨hg.surjective.comp hf.surjective, fun _ hS => hf.isConvex_preimage (hg.isConvex_preimage hS)⟩

/-- The collapse of a `G`-tree along an invariant set of edges is a collapse map. -/
theorem isCollapseMap_collapseHom (S : Set T.E) (hS : ∀ e ∈ S, T.rev e ∈ S)
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
theorem Refines.refl : T.Refines T :=
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
theorem refines_collapse (S : Set T.E) (hS : ∀ e ∈ S, T.rev e ∈ S)
    (hG : ∀ g : G, ∀ e ∈ S, g • e ∈ S) : T.Refines (T.collapse S hS hG) :=
  ⟨T.collapseHom S hS hG, isCollapseMap_collapseHom S hS hG⟩

/-! ### Morphisms -/

/-- An equivariant map of vertices is a *morphism* when it identifies the two ends of no dart.
Extended to the edges by geodesics it collapses no edge; maps of trees which fold an edge onto
itself, so that its two ends have the same image, are not morphisms in this sense. In particular
a composite of morphisms need not be a morphism: the first may send a dart to a geodesic of
length two which the second folds onto a single edge. -/
def IsMorphism (f : T.V →[G] T'.V) : Prop :=
  ∀ e : T.E, f (T.src e) ≠ f (T.tgt e)

/-- Unfold the definition of a morphism. -/
theorem isMorphism_iff {f : T.V →[G] T'.V} : IsMorphism f ↔
    ∀ e : T.E, f (T.src e) ≠ f (T.tgt e) := Iff.rfl

/-- An injective equivariant map of vertices is a morphism. -/
theorem IsMorphism.of_injective {f : T.V →[G] T'.V} (hf : Function.Injective f) : IsMorphism f :=
  fun e h => T.isAcyclic.src_ne_tgt e (hf h)

variable (T) in
/-- The identity of a `G`-tree is a morphism. -/
theorem isMorphism_id : IsMorphism (MulActionHom.id G : T.V →[G] T.V) :=
  .of_injective Function.injective_id

/-- A collapse map is a morphism exactly when it is injective: a collapse map that is not
injective collapses some edge. -/
theorem IsCollapseMap.isMorphism_iff_injective {f : T.V →[G] T'.V} (hf : IsCollapseMap f) :
    IsMorphism f ↔ Function.Injective f := by
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

/-- The map from a `G`-tree to its collapse along an invariant set of edges is a morphism exactly
when no edge is collapsed. -/
theorem isMorphism_collapseHom_iff {S : Set T.E} (hS : ∀ e ∈ S, T.rev e ∈ S)
    (hG : ∀ g : G, ∀ e ∈ S, g • e ∈ S) : IsMorphism (T.collapseHom S hS hG) ↔ S = ∅ := by
  rw [(isCollapseMap_collapseHom S hS hG).isMorphism_iff_injective, collapseHom_injective_iff]

/-- Under a morphism, the stabilizer of a dart of the source fixes a dart of the target. -/
theorem IsMorphism.exists_stabilizer_le {f : T.V →[G] T'.V} (hf : IsMorphism f) (e : T.E) :
    ∃ e' : T'.E, stabilizer G e ≤ stabilizer G e' := by
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

/-- A tree with a morphism to a tree relative to `𝒜` and `ℋ` is relative to `𝒜` and `ℋ`, when
`𝒜` is closed under passing to subgroups and the members of `ℋ` are elliptic in it. -/
theorem IsRelative.of_isMorphism {𝒜 ℋ : Set (Subgroup G)} {f : T.V →[G] T'.V}
    (hT' : T'.IsRelative 𝒜 ℋ) (hf : IsMorphism f) (h𝒜 : ∀ A ∈ 𝒜, ∀ B ≤ A, B ∈ 𝒜)
    (hℋ : ∀ H ∈ ℋ, T.IsEllipticSubgroup H) : T.IsRelative 𝒜 ℋ := by
  refine isRelative_iff.mpr ⟨fun e => ?_, hℋ⟩
  obtain ⟨e', he'⟩ := hf.exists_stabilizer_le e
  exact h𝒜 _ (hT'.stabilizer_mem e') _ he'

end GTree

end TauCeti
