/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Groupoid.ActionCategory.Map
public import TauCeti.Topology.CategoryTheory.ActionGroupoid

/-!
# Slice charts of topological action groupoids

Let a group `G` act on a topological space `X`, let `H` be a subgroup of `G` and let `S` be an
`H`-invariant subset of `X`. The inclusion functor
`CategoryTheory.ActionCategory.inclusion S : H ⋉ S ⥤ G ⋉ X` keeps the label of each arrow. With
the object and arrow topologies of action groupoids, it is a topological chart of `G ⋉ X`: when
`S` is open, it is an open embedding on objects, and, when `H` is also open in `G` (for instance
when `G` is discrete), on total arrows. When `S` is a slice for `H`, that is every element of `G`
carrying a point of `S` into `S` lies in `H`, its arrows are exactly the arrows of `G ⋉ X` with
source and target in `S` (`CategoryTheory.ActionCategory.range_inclusion_total`).

So the full restriction of `G ⋉ X` to an open slice `S` for an open subgroup `H` is isomorphic
to `H ⋉ S`, as a topological groupoid: on objects and on arrows the inclusion is a homeomorphism
onto the restriction, and it is fully faithful by
`CategoryTheory.ActionCategory.full_inclusion_iff`. For a proper action of a discrete group,
`ProperSMul.exists_slice` provides such slices `S` at `x` for the finite stabilizer `G_x`, inside
any neighbourhood of `x`. This is the local isotropy chart
`Γ|S ≅ G_x ⋉ S` of the action presentation `Γ = G ⋉ X` of `[X/G]`. Every label is retained,
including elements of `G_x` that act trivially on `S`.

## Main results

* `TauCeti.ActionGroupoid.isOpenEmbedding_inclusion_obj`: on objects, the inclusion of an open
  invariant subset is an open embedding.
* `TauCeti.ActionGroupoid.isOpenEmbedding_inclusion_total`: for an open subgroup, the inclusion
  of an open invariant subset is an open embedding on total arrows.

## References

* I. Moerdijk, *Orbifolds as groupoids: an introduction*, Section 2.
* I. Moerdijk and J. Mrčun, *Introduction to foliations and Lie groupoids*, Section 5.1.
-/

public section

open CategoryTheory Topology
open CategoryTheory.ActionCategory

namespace TauCeti.ActionGroupoid

variable {G X : Type*} [Group G] [MulAction G X] {H : Subgroup G} (S : SubMulAction H X)

variable [TopologicalSpace X]

/-- On objects, the inclusion of the action groupoid of a subgroup on an open invariant subset is
an open embedding. -/
theorem isOpenEmbedding_inclusion_obj (hS : IsOpen (S : Set X)) :
    IsOpenEmbedding (inclusion S).obj := by
  have : (inclusion S).obj =
      (objectHomeomorph G X).symm ∘ ((↑) : S → X) ∘ objectHomeomorph H S := by
    funext a
    apply (objectHomeomorph G X).injective
    simp [objEquiv]
  rw [this]
  exact (objectHomeomorph G X).symm.isOpenEmbedding.comp
    (hS.isOpenEmbedding_subtypeVal.comp (objectHomeomorph H S).isOpenEmbedding)

variable [TopologicalSpace G]

/-- The inclusion of the action groupoid of an open subgroup on an open invariant subset is an
open embedding on total arrows. In label-source coordinates it is the product of the inclusions
of the subgroup and of the subset. Every subgroup of a discrete group is open. -/
theorem isOpenEmbedding_inclusion_total (hH : IsOpen (H : Set G)) (hS : IsOpen (S : Set X)) :
    IsOpenEmbedding (fun f : Quiver.Total (ActionCategory H S) =>
      (⟨(inclusion S).obj f.left, (inclusion S).obj f.right, (inclusion S).map f.hom⟩ :
        Quiver.Total (ActionCategory G X))) := by
  have : (fun f : Quiver.Total (ActionCategory H S) =>
      (⟨(inclusion S).obj f.left, (inclusion S).obj f.right, (inclusion S).map f.hom⟩ :
        Quiver.Total (ActionCategory G X))) =
      (arrowHomeomorph G X).symm ∘ Prod.map Subtype.val Subtype.val ∘ arrowHomeomorph H S := by
    funext f
    apply (arrowHomeomorph G X).injective
    simp [objEquiv]
  rw [this]
  exact (arrowHomeomorph G X).symm.isOpenEmbedding.comp
    ((hH.isOpenEmbedding_subtypeVal.prodMap
      hS.isOpenEmbedding_subtypeVal).comp (arrowHomeomorph H S).isOpenEmbedding)

end TauCeti.ActionGroupoid
