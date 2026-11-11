/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.Basic
import TauCeti.AlgebraicGeometry.Restrict
import TauCeti.AlgebraicGeometry.Scheme.LocallyDirected

/-!
# Extending a morphism from an open subscheme

Let `j : U ⟶ B` be an open immersion, let `V` be an open of `B`, and let `f : Y ⟶ U` be a morphism
which is an isomorphism over `j⁻¹(V)`. Gluing `Y` and `V` along `f⁻¹(j⁻¹(V)) ≅ j⁻¹(V)` gives a
scheme `Y'` with a morphism `f' : Y' ⟶ B` which restricts to `f` over `U` and to an isomorphism
over `V`. If `U` and `V` cover `B`, every property of morphisms local on the target and holding for
isomorphisms passes from `f` to `f'`; for instance `f'` is proper when `f` is.

This is how a modification of an open subscheme which only changes a closed subset of `B` lying
inside `U` (such as a sequence of blowups at closed points of `U`) is extended to a modification of
`B`: take `V` to be the complement of that closed subset.

## Main results

* `AlgebraicGeometry.Scheme.Hom.exists_isPullback_isIso_morphismRestrict`: the extension `f'` of
  `f` along `j`, with `f` its base change along `j` and `f'` an isomorphism over `V`.
* `AlgebraicGeometry.IsZariskiLocalAtTarget.of_isPullback_of_isIso_morphismRestrict`: a property
  local on the target and holding for isomorphisms passes from `f` to such an extension `f'`.

## References

* [The Stacks Project, Section 26.14, Gluing schemes](https://stacks.math.columbia.edu/tag/01JA)
-/

public section

noncomputable section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry

namespace Scheme.Hom

variable {U B Y : Scheme.{u}} (j : U ⟶ B) (V : B.Opens) (f : Y ⟶ U)

/-- The part `f⁻¹(j⁻¹(V)) ⟶ j⁻¹(V) ⟶ V` of `f` over `V`, along which `Y` and `V` are glued. -/
private def overlapMap : (f ⁻¹ᵁ j ⁻¹ᵁ V).toScheme ⟶ V :=
  f ∣_ j ⁻¹ᵁ V ≫ j ∣_ V

private theorem overlapMap_ι : overlapMap j V f ≫ V.ι = (f ⁻¹ᵁ j ⁻¹ᵁ V).ι ≫ f ≫ j := by
  rw [overlapMap, Category.assoc, morphismRestrict_ι, morphismRestrict_ι_assoc]

variable [IsOpenImmersion j] [IsIso (f ∣_ j ⁻¹ᵁ V)]

private instance : IsOpenImmersion (overlapMap j V f) := by
  rw [overlapMap]
  infer_instance

/-- The morphism from the glued scheme to `B`, given by `f ≫ j` on `Y` and the inclusion on `V`. -/
private def gluedToBase : pushout (f ⁻¹ᵁ j ⁻¹ᵁ V).ι (overlapMap j V f) ⟶ B :=
  pushout.desc (f ≫ j) V.ι (overlapMap_ι j V f).symm

/-- A point of the glued scheme lying over `j(U)` comes from `Y`. -/
private theorem preimage_opensRange_gluedToBase :
    gluedToBase j V f ⁻¹ᵁ j.opensRange =
      (pushout.inl (f ⁻¹ᵁ j ⁻¹ᵁ V).ι (overlapMap j V f)).opensRange := by
  refine le_antisymm (fun p hp ↦ ?_) ?_
  · rcases (Set.ext_iff.mp (Scheme.range_pushout_inl_union_range_pushout_inr _ _) p).mpr
      trivial with ⟨y, rfl⟩ | ⟨v, rfl⟩
    · exact ⟨y, rfl⟩
    -- A point `v` of `V` lying in `j(U)` is the image of a point of `f⁻¹(j⁻¹(V))`.
    obtain ⟨u, hu⟩ := hp
    rw [← Scheme.Hom.comp_apply, gluedToBase, pushout.inr_desc] at hu
    have hu' : u ∈ j ⁻¹ᵁ V := by
      rw [Scheme.Hom.mem_preimage, hu]
      exact v.2
    obtain ⟨w, hw⟩ := (f ∣_ j ⁻¹ᵁ V).surjective ⟨u, hu'⟩
    refine ⟨(f ⁻¹ᵁ j ⁻¹ᵁ V).ι w, ?_⟩
    rw [← Scheme.Hom.comp_apply, pushout.condition, Scheme.Hom.comp_apply]
    congr 1
    apply V.ι.isOpenEmbedding.injective
    rw [← Scheme.Hom.comp_apply, overlapMap, Category.assoc, morphismRestrict_ι,
      Scheme.Hom.comp_apply, hw]
    exact hu
  · rintro _ ⟨y, rfl⟩
    refine ⟨f y, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, gluedToBase, pushout.inl_desc]

/-- A point of the glued scheme lying over `V` comes from `V`. -/
private theorem preimage_gluedToBase_le :
    gluedToBase j V f ⁻¹ᵁ V ≤ (pushout.inr (f ⁻¹ᵁ j ⁻¹ᵁ V).ι (overlapMap j V f)).opensRange := by
  intro p hp
  rcases (Set.ext_iff.mp (Scheme.range_pushout_inl_union_range_pushout_inr _ _) p).mpr
    trivial with ⟨y, rfl⟩ | ⟨v, rfl⟩
  · -- A point `y` of `Y` lying over `V` lies in `f⁻¹(j⁻¹(V))`, along which `Y` is glued to `V`.
    rw [Scheme.Hom.mem_preimage, ← Scheme.Hom.comp_apply, gluedToBase, pushout.inl_desc] at hp
    obtain ⟨z, rfl⟩ : y ∈ Set.range (f ⁻¹ᵁ j ⁻¹ᵁ V).ι := by
      rw [Scheme.Opens.range_ι]
      exact hp
    exact ⟨overlapMap j V f z, by rw [← Scheme.Hom.comp_apply, ← pushout.condition,
      Scheme.Hom.comp_apply]⟩
  · exact ⟨v, rfl⟩

/-- **Extending a morphism along an open immersion.** Let `j : U ⟶ B` be an open immersion, `V` an
open of `B`, and `f : Y ⟶ U` a morphism which is an isomorphism over `j⁻¹(V)`. Then there are an
open immersion `ι : Y ⟶ Y'` and a morphism `f' : Y' ⟶ B` such that `f` is the base change of `f'`
along `j`, `f'` is an isomorphism over `V`, and `Y'` is covered by `Y` and the inverse image of
`V`. The scheme `Y'` is glued from `Y` and `V` along `f⁻¹(j⁻¹(V)) ≅ j⁻¹(V)`. -/
theorem exists_isPullback_isIso_morphismRestrict :
    ∃ (Y' : Scheme.{u}) (ι : Y ⟶ Y') (f' : Y' ⟶ B) (_ : IsOpenImmersion ι),
      IsPullback f ι j f' ∧ IsIso (f' ∣_ V) ∧ ι.opensRange ⊔ f' ⁻¹ᵁ V = ⊤ := by
  refine ⟨_, pushout.inl _ _, gluedToBase j V f, inferInstance,
    IsOpenImmersion.isPullback _ _ _ _ (by rw [gluedToBase, pushout.inl_desc])
      (preimage_opensRange_gluedToBase j V f), ?_, ?_⟩
  · -- Over `V`, the glued scheme lies in the image of `V`, on which `f'` is the inclusion.
    refine (gluedToBase j V f).isIso_morphismRestrict_of_isIso_comp _
      (preimage_gluedToBase_le j V f) ?_
    rw [gluedToBase, pushout.inr_desc]
    exact V.ι.isIso_morphismRestrict_of_le_opensRange (by rw [Scheme.Opens.opensRange_ι])
  · refine top_le_iff.mp fun p _ ↦ ?_
    rcases (Set.ext_iff.mp (Scheme.range_pushout_inl_union_range_pushout_inr _ _) p).mpr
      trivial with ⟨y, rfl⟩ | ⟨v, rfl⟩
    · exact Or.inl ⟨y, rfl⟩
    · refine Or.inr ?_
      rw [SetLike.mem_coe, Scheme.Hom.mem_preimage, ← Scheme.Hom.comp_apply, gluedToBase,
        pushout.inr_desc]
      exact v.2

end Scheme.Hom

/-- Let `j : U ⟶ B` be an open immersion and `V` an open of `B` with `j(U) ∪ V = B`, and let
`f' : Y' ⟶ B` be an isomorphism over `V` whose base change along `j` is `f : Y ⟶ U`. A property
local on the target and holding for isomorphisms passes from `f` to `f'`. -/
theorem IsZariskiLocalAtTarget.of_isPullback_of_isIso_morphismRestrict
    {P : MorphismProperty Scheme.{u}} [IsZariskiLocalAtTarget P] [P.ContainsIdentities]
    {U B Y Y' : Scheme.{u}} {j : U ⟶ B} [IsOpenImmersion j] {V : B.Opens} {f : Y ⟶ U}
    {ι : Y ⟶ Y'} {f' : Y' ⟶ B} (h : IsPullback f ι j f') (hV : IsIso (f' ∣_ V))
    (hjV : j.opensRange ⊔ V = ⊤) (hf : P f) : P f' := by
  refine IsZariskiLocalAtTarget.of_iSup_eq_top (P := P) (fun b ↦ cond b j.opensRange V)
    (by rwa [iSup_bool_eq]) fun b ↦ ?_
  cases b
  · have : IsIso (f' ∣_ V) := hV
    exact P.of_isIso (f' ∣_ V)
  · refine (P.arrow_mk_iso_iff (morphismRestrictOpensRange f' j)).mpr ?_
    rw [← h.flip.isoPullback_hom_snd] at hf
    exact (P.cancel_left_of_respectsIso _ _).mp hf

end AlgebraicGeometry
