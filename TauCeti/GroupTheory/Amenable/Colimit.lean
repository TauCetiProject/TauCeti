/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.Grp.Colimits
public import TauCeti.Algebra.Colimit.DirectLimit
public import TauCeti.GroupTheory.Amenable.DirectedUnion

/-!
# Filtered colimits of amenable groups

The colimit of a filtered diagram of amenable groups is amenable. The transition maps need not be
injective. Every finite subset of the apex of a colimit cocone over a filtered diagram in `GrpCat`
lies in the image of a single leg, so the criterion
`TauCeti.Amenable.of_forall_finset_subset_range`, which pushes left-invariant means forward along
the legs, applies as soon as the legs are continuous.

The stages of the diagram are arbitrary groups, so their topologies are supplied as instances. In
the discrete setting every leg is continuous, and the apex may carry any group topology. A nonempty
directed preorder is a filtered category, so this covers colimits of directed systems of groups
indexed by such a preorder.

For Mathlib's concrete model `DirectLimit G f` of the colimit of a directed system of groups, the
same argument applies directly: every finite subset of `DirectLimit G f` lies in the image of a
single canonical map `DirectLimit.Monoid.of G f i`
(`DirectLimit.Monoid.exists_subset_range_of`). This needs neither that the groups live in a common
universe with the index set, nor that the transition maps be injective. The identification of
`DirectLimit G f` with the colimit in `GrpCat` is `TauCeti.GrpCat.directLimitIsColimit`.

## Main results

* `TauCeti.Amenable.of_isColimit`: the apex of a colimit cocone over a filtered diagram of amenable
  topological groups is amenable, provided the legs are continuous.
* `TauCeti.Amenable.of_isColimit_of_discreteTopology`: the apex of a colimit cocone over a filtered
  diagram of discrete amenable groups is amenable for every group topology.
* `TauCeti.Amenable.directLimit`: the direct limit of a directed system of amenable topological
  groups is amenable, provided the canonical maps are continuous.
* `TauCeti.Amenable.directLimit_of_discreteTopology`: the direct limit of a directed system of
  discrete amenable groups is amenable for every group topology.

## References

* B. Bekka, P. de la Harpe, A. Valette, *Kazhdan's Property (T)*, Proposition G.2.2.
* A. Garrido, *An introduction to amenable groups*, Proposition 2.2.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits

universe u

variable {J : Type*} [Category* J] [IsFiltered J] {F : J ⥤ _root_.GrpCat.{u}}
  [∀ j, TopologicalSpace (F.obj j)] {c : Cocone F} [TopologicalSpace c.pt]
  [IsTopologicalGroup c.pt]

/-- The apex of a colimit cocone over a filtered diagram of amenable topological groups in `GrpCat`
is amenable, provided the legs of the cocone are continuous. -/
theorem Amenable.of_isColimit [∀ j, IsTopologicalGroup (F.obj j)] [∀ j, Amenable (F.obj j)]
    (hc : IsColimit c) (hcont : ∀ j, Continuous (Y := c.pt) (c.ι.app j).hom) : Amenable c.pt :=
  .of_forall_finset_subset_range (fun j => ⟨(c.ι.app j).hom, hcont j⟩)
    (GrpCat.exists_subset_range_of_isColimit hc)

/-- The apex of a colimit cocone over a filtered diagram of discrete amenable groups in `GrpCat` is
amenable, for every group topology on the apex. -/
theorem Amenable.of_isColimit_of_discreteTopology [∀ j, DiscreteTopology (F.obj j)]
    [∀ j, Amenable (F.obj j)] (hc : IsColimit c) : Amenable c.pt :=
  .of_isColimit hc fun _ => continuous_of_discreteTopology

section DirectLimit

variable {ι : Type*} [Preorder ι] [IsDirectedOrder ι] [Nonempty ι] {G : ι → Type*}
  [∀ i, Group (G i)] {T : ∀ ⦃i j : ι⦄, i ≤ j → Type*} {f : ∀ _ _ h, T h}
  [∀ i j (h : i ≤ j), FunLike (T h) (G i) (G j)] [∀ i j h, MonoidHomClass (T h) (G i) (G j)]
  [DirectedSystem G (f · · ·)] [∀ i, TopologicalSpace (G i)] [TopologicalSpace (DirectLimit G f)]
  [IsTopologicalGroup (DirectLimit G f)]

/-- The direct limit of a directed system of amenable topological groups is amenable, provided
the canonical maps from the groups of the system are continuous. -/
theorem Amenable.directLimit [∀ i, IsTopologicalGroup (G i)] [∀ i, Amenable (G i)]
    (hcont : ∀ i, Continuous (DirectLimit.Monoid.of G f i)) : Amenable (DirectLimit G f) :=
  .of_forall_finset_subset_range (fun i => ⟨DirectLimit.Monoid.of G f i, hcont i⟩)
    DirectLimit.Monoid.exists_subset_range_of

/-- The direct limit of a directed system of discrete amenable groups is amenable, for every group
topology on the direct limit. -/
theorem Amenable.directLimit_of_discreteTopology [∀ i, DiscreteTopology (G i)]
    [∀ i, Amenable (G i)] : Amenable (DirectLimit G f) :=
  .directLimit fun _ => continuous_of_discreteTopology

end DirectLimit

end TauCeti
