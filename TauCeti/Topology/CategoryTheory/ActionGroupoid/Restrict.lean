/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.CategoryTheory.ActionGroupoid.Nerve

/-!
# Open restriction of the fat classifying space of an action groupoid

Let a group `G` act on a space `X`, and let `Γ = G ⋉ X` be the action groupoid with its
label-source topology on arrows. Its fat classifying space `BΓ` maps to the orbit space `X/G` by
the coarse map `q` (`TauCeti.ActionGroupoid.coarseMap`), which sends a point `[F, t]` to the orbit
of any vertex of `F`.

Let `U` be a `G`-invariant open subset of `X`, that is, a saturated open set of objects of `Γ`, and
let `Γ|U = G ⋉ U` be the full subgroupoid on `U` (`CategoryTheory.ActionCategory.restrict`). A
string of composable arrows of `Γ` lies in the nerve of `Γ|U` exactly when its first vertex lies
in `U`, and the restricted nerve is levelwise an open subspace. Hence the induced map
`B(Γ|U) → BΓ` is an open embedding
(`TauCeti.ActionGroupoid.isOpenEmbedding_fatClassifyingSpaceMap_restrict`) whose image is the
preimage under `q` of the image of `U` in `X/G`
(`TauCeti.ActionGroupoid.preimage_coarseMap_eq_range_fatClassifyingSpaceMap_restrict`): the part
of `BΓ` over a saturated open set is the fat classifying space of the restricted groupoid, with its
own quotient topology. No continuity of the action is needed, and labels acting trivially are
kept, so ineffective isotropy survives in `BΓ`.

## References

* G. Segal, *Classifying spaces and spectral sequences*, Publ. Math. IHÉS **34** (1968), 105–112.
* I. Moerdijk, *Orbifolds as groupoids: an introduction*, Section 4.
-/

public noncomputable section

open CategoryTheory Opposite Set Topology MulAction
open CategoryTheory.ActionCategory

universe u

namespace TauCeti.ActionGroupoid

section Monoid

variable {M X : Type*} [Monoid M] [MulAction M X] (U : SubMulAction M X)
  [TopologicalSpace M] [TopologicalSpace X]

/-- For an open invariant subset `U`, the nerve of `M ⋉ U` is levelwise an open subspace of the
nerve of `M ⋉ X`. -/
theorem isOpenEmbedding_topologicalNerveMap_restrict (hU : IsOpen (U : Set X))
    (Δ : SimplexCategoryᵒᵖ) :
    IsOpenEmbedding
      (((restrict U).topologicalNerveMap (isEmbedding_mapTotal_restrict U).continuous).app Δ) := by
  rw [Functor.coe_topologicalNerveMap_app]
  refine ⟨ComposableArrows.isEmbedding_mapComposableArrows_obj (isEmbedding_mapTotal_restrict U),
    ?_⟩
  -- The level of the topological nerve is `ComposableArrows` with its composite topology.
  have : IsOpen (range ((restrict U).mapComposableArrows Δ.unop.len).obj) := by
    rw [range_mapComposableArrows_obj_restrict]
    exact hU.preimage continuous_back_obj_zero
  exact this

end Monoid

variable {G X : Type u} [Group G] [MulAction G X] [TopologicalSpace G] [TopologicalSpace X]
  (U : SubMulAction G X)

/-- The image of the nerve of `G ⋉ U` in each level of the nerve of `G ⋉ X` is the preimage, under
the coarse augmentation, of the image of `U` in the orbit space. -/
theorem range_topologicalNerveMap_restrict (m : SemiSimplexCategoryᵒᵖ) :
    range (((restrict U).topologicalNerveMap (isEmbedding_mapTotal_restrict U).continuous).app
        (SemiSimplexCategory.toSimplexCategory.op.obj m)) =
      (coarseAugmentation G X).app m ⁻¹' (Quotient.mk _ '' (U : Set X)) := by
  rw [Functor.coe_topologicalNerveMap_app]
  refine (range_mapComposableArrows_obj_restrict U _).trans (Set.ext fun F => ?_)
  refine ⟨fun hF => ⟨_, hF, (coarseAugmentation_app_apply m F).symm⟩, ?_⟩
  rintro ⟨x, hx, hxF⟩
  obtain ⟨g, rfl⟩ := Quotient.exact (hxF.trans (coarseAugmentation_app_apply m F))
  simpa using U.smul_mem g⁻¹ hx

/-- **Open restriction.** For a `G`-invariant open subset `U`, the map of fat classifying spaces
induced by the inclusion `G ⋉ U ⥤ G ⋉ X` is an open embedding. -/
theorem isOpenEmbedding_fatClassifyingSpaceMap_restrict (hU : IsOpen (U : Set X)) :
    IsOpenEmbedding ((restrict U).fatClassifyingSpaceMap
      (isEmbedding_mapTotal_restrict U).continuous) := by
  rw [Functor.fatClassifyingSpaceMap_eq]
  exact fatRealization.isOpenEmbedding_map_of_range_eq_preimage (coarseAugmentation G X)
    (V := Quotient.mk _ '' (U : Set X))
    (fun _ => isOpenEmbedding_topologicalNerveMap_restrict U hU _)
    (range_topologicalNerveMap_restrict U)

/-- **Open restriction.** The part of the fat classifying space of `G ⋉ X` lying over the image of
a `G`-invariant subset `U` is the image of the fat classifying space of `G ⋉ U`. -/
theorem preimage_coarseMap_eq_range_fatClassifyingSpaceMap_restrict :
    coarseMap G X ⁻¹' (Quotient.mk _ '' (U : Set X)) =
      range ((restrict U).fatClassifyingSpaceMap (isEmbedding_mapTotal_restrict U).continuous) := by
  rw [coarseMap_eq_augment, Functor.fatClassifyingSpaceMap_eq]
  exact fatRealization.preimage_augment_eq_range_map _ (range_topologicalNerveMap_restrict U)

end TauCeti.ActionGroupoid
