/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.PreAdicSpace.LocallyOfFiniteType.Refine

/-!
# Open restriction of morphisms locally of finite type

Finite-type affinoid charts can be refined by rational subsets of the source, by
`TauCeti.ValuationSpectrum.locallyOfFiniteType_ofRestrict_comp_presentationLimitPreAdicSpaceComap`.
This file passes from that chart-level result to source restrictions of arbitrary morphisms
locally of finite type. Consequently the property can be tested on any open cover of the source,
independently of the neighbourhoods used in its definition.

The source restriction theorem needs neither adicness nor a Tate hypothesis: the sheafy
affinoid source charts in the definition suffice.

## References

* T. Wedhorn, *Adic Spaces*, arXiv:1910.05934v1, Definitions 8.42 and 8.48 and Proposition 8.46.
-/

public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Topology

namespace TauCeti.PreAdicSpace

open TauCeti.Huber TauCeti.ValuationSpectrum

universe u

variable {X Y Z : PreAdicSpace.{u}}

/-- Restricting the source of a morphism locally of finite type to any open preserves the
property. No sheaf condition on the target is needed. -/
theorem LocallyOfFiniteType.ofRestrict_comp {f : X ⟶ Y} (hf : LocallyOfFiniteType f)
    (W : Opens X) : LocallyOfFiniteType (X.ofRestrict W.isOpenEmbedding ≫ f) := by
  rw [locallyOfFiniteType_iff] at hf
  refine LocallyOfFiniteType.ofRestrict_comp_of_forall_exists_le W fun x ↦ ?_
  obtain ⟨U, hx, V, hUV, A, _, _, _, _, S, P, hP, B, _, _, _, _, _, _, _, T, P', hP', φ, hφ,
    hsheaf, eU, eV, hfac⟩ := hf x.1
  let C := presentationLimitPreAdicSpace P' T.plus
    T.isRingOfIntegralElements.isPowerBounded_of_mem hP'
  let g : C ⟶ X := eU.inv ≫ X.ofRestrict U.isOpenEmbedding
  let O : Opens C := (Opens.map g.base).obj W
  let D : Opens X := g.isOpenEmbedding.isOpenMap.functor.obj O
  -- Unfolding g, base maps of composites reduce to function composition, and the
  -- base map of the restriction inclusion reduces to the subtype projection.
  have hg : g.base (eU.hom.base ⟨x.1, hx⟩) = x.1 :=
    congrArg (fun k : X.restrict U.isOpenEmbedding ⟶ X ↦ k.base ⟨x.1, hx⟩)
      (Iso.hom_inv_id_assoc eU (X.ofRestrict U.isOpenEmbedding))
  have hy : eU.hom.base ⟨x.1, hx⟩ ∈ O :=
    Opens.mem_map.mpr (by rw [hg]; exact x.2)
  refine ⟨D, ⟨_, hy, hg⟩, ?_, ?_⟩
  · rintro _ ⟨y, hy, rfl⟩
    exact hy
  · let j := C.ofRestrict O.isOpenEmbedding ≫ g
    have hr : Set.range j.base = Set.range (X.ofRestrict D.isOpenEmbedding).base :=
      IsOpenImmersion.range_ofRestrict_comp_base g O
    have hc := locallyOfFiniteType_ofRestrict_comp_presentationLimitPreAdicSpaceComap
      P P' hP hP' φ hφ hsheaf O
    have hj : LocallyOfFiniteType (j ≫ f) := by
      dsimp only [j, g]
      rw [Category.assoc, Category.assoc, hfac, Iso.inv_hom_id_assoc]
      rw [← Category.assoc]
      exact hc.comp_of_isOpenImmersion _
    rw [← IsOpenImmersion.isoOfRangeEq_inv_comp j (X.ofRestrict D.isOpenEmbedding) hr,
      Category.assoc, MorphismProperty.cancel_left_of_respectsIso @LocallyOfFiniteType.{u}]
    exact hj

/-- Precomposing a morphism locally of finite type with an open immersion preserves the
property, without any adicness hypothesis on the spaces. -/
theorem LocallyOfFiniteType.isOpenImmersion_comp {f : X ⟶ Y} (hf : LocallyOfFiniteType f)
    (g : Z ⟶ X) [IsOpenImmersion g] : LocallyOfFiniteType (g ≫ f) := by
  let O : Opens X := ⟨Set.range g.base, g.isOpenEmbedding.isOpen_range⟩
  have hr : Set.range g.base = Set.range (X.ofRestrict O.isOpenEmbedding).base :=
    (Opens.set_range_inclusion' O).symm
  rw [← IsOpenImmersion.isoOfRangeEq_hom_comp g (X.ofRestrict O.isOpenEmbedding) hr,
    Category.assoc, MorphismProperty.cancel_left_of_respectsIso @LocallyOfFiniteType.{u}]
  exact hf.ofRestrict_comp O

/-- Being locally of finite type is local on the source: it can be tested on any open cover,
not only on the affinoid neighbourhoods used to witness the definition. -/
theorem locallyOfFiniteType_iff_of_iSup_eq_top_source {f : X ⟶ Y} {ι : Type*}
    (U : ι → Opens X) (hU : iSup U = ⊤) :
    LocallyOfFiniteType f ↔ ∀ i, LocallyOfFiniteType (X.ofRestrict (U i).isOpenEmbedding ≫ f) :=
  ⟨fun hf i ↦ hf.ofRestrict_comp (U i), LocallyOfFiniteType.of_iSup_eq_top U hU⟩

end TauCeti.PreAdicSpace
