/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.StructurePresheaf.Rational
public import TauCeti.RingTheory.Huber.LocalizationTopology.Trivial

/-!
# Global sections of the presentation limit are `A`

Let `A` be a complete Hausdorff Huber ring and `A⁺` a subring of power-bounded elements. This file
identifies the value of `presentationLimitPresheaf` on the whole adic spectrum `X = Spa(A,A⁺)`
with `A` itself, as an isomorphism of complete separated topological rings, and says which map
realises it: the canonical map from `A` to the sections over an open. This is Wedhorn's
`𝒪_X(X) = A` for a complete affinoid ring, stated for `presentationLimit`.

## The argument

For every presentation `p` the structure map `A → A⟨p⟩` is a morphism of
`CompleteSeparatedTopCommRingCat` (`Presentation.toCompletionLocObjHom`), and the restriction
morphisms of refinements are compatible with these structure maps. They therefore form a cone
over the diagram of any open `V`, whose lift is `toPresentationLimit : A ⟶ presentationLimit V`.

At `V = ⊤` take the trivial presentation `({1}, 1)`. Its rational subset `R({1}/1)` is the whole
spectrum (`rationalSubset_singleton_one`), so the projection of the limit at it is an isomorphism
(`isIso_presentationLimitπ`); and for complete Hausdorff `A` its structure map `A → A⟨1/1⟩` is an
isomorphism (`toCompletionLocHomeomorphDenomOne`, a consequence of the universal property of
`A⟨T/s⟩`). Since `toPresentationLimit` followed by that projection is that structure map, it is
itself an isomorphism.

## Main definitions

* `TauCeti.Huber.PairOfDefinition.Presentation.toCompletionLocObjHom` : the structure map
  `A → A⟨p⟩` as a morphism of `CompleteSeparatedTopCommRingCat`.
* `TauCeti.ValuationSpectrum.toPresentationLimit` : the canonical map `A ⟶ presentationLimit V`.
* `TauCeti.ValuationSpectrum.presentationLimitTopIso` : the isomorphism
  `presentationLimit Aplus ⊤ ≅ A`.

## Main results

* `TauCeti.Huber.PairOfDefinition.Presentation.toCompletionLocObjHom_comp_completionLocObjHom`
  and `TauCeti.Huber.PairOfDefinition.Presentation.toCompletionLocObjHom_comp_restrictionHom` :
  comparison and restriction morphisms commute with the structure maps.
* `TauCeti.ValuationSpectrum.toPresentationLimit_comp_πToPresentation` and
  `TauCeti.ValuationSpectrum.toPresentationLimit_comp_presentationLimitMap` : the canonical map
  projects to the structure maps and commutes with restriction.
* `TauCeti.ValuationSpectrum.isIso_toPresentationLimit_top` : on the whole spectrum the canonical
  map is an isomorphism.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), §8.1, where `𝒪_X(X) = A` for a
  complete affinoid ring is the case `U = X = R({1}/1)` of `𝒪_X(U) = A_U`.
-/

open CategoryTheory CategoryTheory.Limits _root_.TopologicalSpace

public section

universe v

namespace TauCeti.ValuationSpectrum

open TauCeti.Huber TauCeti.Huber.PairOfDefinition

variable {A : Type v} [CommRing A] [UniformSpace A] [IsUniformAddGroup A] [IsTopologicalRing A]
  [CompleteSpace A] [T0Space A] {P : PairOfDefinition A}

/-! ### The canonical map from `A` to the sections over an open -/

variable (Aplus : Subring A)

/-- **The canonical map `A ⟶ presentationLimit V`**: the lift of the cone formed by the structure
maps `A → A⟨T/s⟩` of the presentations refining `V`: Wedhorn's map `A → 𝒪_X(V)`, stated for
`presentationLimit`. -/
noncomputable def toPresentationLimit (V : Opens ↥(spa Aplus)) :
    CompleteSeparatedTopCommRingCat.of A ⟶ presentationLimit (P := P) Aplus V :=
  eqToHom (presentationIndexCone_pt Aplus V _ (fun i ↦ i.pres.toCompletionLocObjHom)
      fun f ↦ Presentation.toCompletionLocObjHom_comp_restrictionHom f.le).symm ≫
    presentationLimitLift Aplus V (presentationIndexCone Aplus V _
      (fun i ↦ i.pres.toCompletionLocObjHom)
      fun f ↦ Presentation.toCompletionLocObjHom_comp_restrictionHom f.le)

/-- **The canonical map projects to the structure maps**: its component at a presentation
refining `V` is the structure map `A → A⟨T/s⟩`. -/
@[reassoc (attr := simp)]
theorem toPresentationLimit_comp_πToPresentation (V : Opens ↥(spa Aplus))
    (i : PresentationIndex (P := P) Aplus V) :
    toPresentationLimit Aplus V ≫ presentationLimitπToPresentation Aplus V i =
      i.pres.toCompletionLocObjHom := by
  rw [toPresentationLimit, Category.assoc]
  exact presentationIndexCone_lift_comp_πToPresentation Aplus V _
    (fun i ↦ i.pres.toCompletionLocObjHom)
    (fun f ↦ Presentation.toCompletionLocObjHom_comp_restrictionHom f.le) i

/-- **The canonical map commutes with restriction**: restricting the image of `A` in the sections
over `V` to `W ≤ V` gives its image in the sections over `W`. -/
@[reassoc (attr := simp)]
theorem toPresentationLimit_comp_presentationLimitMap {V W : Opens ↥(spa Aplus)} (h : W ≤ V) :
    toPresentationLimit Aplus V ≫ presentationLimitMap (P := P) h =
      toPresentationLimit Aplus W := by
  refine presentationLimit_hom_ext_toPresentation fun i ↦ ?_
  rw [Category.assoc, presentationLimitMap_comp_πToPresentation,
    toPresentationLimit_comp_πToPresentation_assoc, toPresentationLimit_comp_πToPresentation]
  -- the index of `V` obtained by restricting `i` has the same presentation as `i`
  have key {p q : Presentation P} (e : p = q) :
      p.toCompletionLocObjHom ≫ eqToHom (congrArg Presentation.completionLocObj e) =
        q.toCompletionLocObjHom := by
    subst e
    simp
  exact key (presentationIndexRestrict_obj_pres h i)

/-! ### Global sections -/

/-- The structure map of the trivial presentation `({1}, 1)` is an isomorphism, for complete
Hausdorff `A`. -/
private theorem isIso_toCompletionLocObjHom_one :
    IsIso (Presentation.toCompletionLocObjHom (P := P)
      ⟨{1}, 1, hasDenominatorPower_denom_one P {1} _⟩) := by
  have hpb : ∀ t ∈ ({1} : Finset A), IsPowerBounded t := fun t ht ↦ by
    rw [Finset.mem_singleton.mp ht]
    exact isPowerBounded_one
  let _ := locUniformSpace P {1} 1 (Localization.Away (1 : A))
    (hasDenominatorPower_denom_one P {1} _)
  let _ := isUniformAddGroup_locUniformSpace P {1} 1 (Localization.Away (1 : A))
    (hasDenominatorPower_denom_one P {1} _)
  let _ := isTopologicalRing_locUniformSpace P {1} 1 (Localization.Away (1 : A))
    (hasDenominatorPower_denom_one P {1} _)
  let r := toCompletionLocEquivDenomOne P {1} hpb (Localization.Away (1 : A))
  let F : TopCommRingCat.of A ⟶
      TopCommRingCat.of (UniformSpace.Completion (Localization.Away (1 : A))) :=
    ⟨_, continuous_toCompletionLoc P {1} 1 _ (hasDenominatorPower_denom_one P {1} _)⟩
  let G : TopCommRingCat.of (UniformSpace.Completion (Localization.Away (1 : A))) ⟶
      TopCommRingCat.of A :=
    ⟨r.symm.toRingHom, continuous_toCompletionLocEquivDenomOne_symm P {1} hpb _⟩
  have hFG : F ≫ G = 𝟙 _ := Subtype.ext <| RingHom.ext fun x ↦
    (congrArg r.symm (toCompletionLocEquivDenomOne_apply P {1} hpb _ x).symm).trans
      (r.symm_apply_apply x)
  have hGF : G ≫ F = 𝟙 _ := Subtype.ext <| RingHom.ext fun x ↦
    (toCompletionLocEquivDenomOne_apply P {1} hpb _ (r.symm x)).symm.trans
      (r.apply_symm_apply x)
  refine ⟨ObjectProperty.homMk
    (eqToHom (completionLocObj_obj P {1} 1 _ (hasDenominatorPower_denom_one P {1} _)) ≫ G ≫
      eqToHom (CompleteSeparatedTopCommRingCat.of_obj A).symm), ?_, ?_⟩ <;>
    apply InducedCategory.hom_ext
  -- by `Presentation.toCompletionLocObjHom_hom`, the underlying morphism of the structure
  -- morphism is `F` between transports; `change` names it so that `hFG` and `hGF` apply
  · rw [ObjectProperty.FullSubcategory.comp_hom, Presentation.toCompletionLocObjHom_hom]
    change (eqToHom _ ≫ F ≫ eqToHom _) ≫ eqToHom _ ≫ G ≫ eqToHom _ = 𝟙 _
    simp [reassoc_of% hFG]
  · rw [ObjectProperty.FullSubcategory.comp_hom, Presentation.toCompletionLocObjHom_hom]
    change (eqToHom _ ≫ G ≫ eqToHom _) ≫ eqToHom _ ≫ F ≫ eqToHom _ = 𝟙 _
    simp [reassoc_of% hGF]

/-- The index of the whole spectrum given by the trivial presentation `({1}, 1)`: its rational
subset `R({1}/1)` is the whole adic spectrum. -/
private noncomputable def trivialIndex :
    PresentationIndex (P := P) Aplus ⊤ where
  pres := ⟨{1}, 1, hasDenominatorPower_denom_one P {1} _⟩
  isOpen_span := by simp
  le_open := le_top

/-- **On the whole spectrum the canonical map is an isomorphism**: for a complete Hausdorff Huber
ring and a subring `A⁺` of power-bounded elements, `A ⟶ presentationLimit Aplus ⊤` is an
isomorphism of complete separated topological rings. -/
theorem isIso_toPresentationLimit_top (hAplus : ∀ ⦃a⦄, a ∈ Aplus → IsPowerBounded a) :
    IsIso (toPresentationLimit (P := P) Aplus ⊤) := by
  have hV : (⊤ : Opens ↥(spa Aplus)) ≤
      spaBasicOpen Aplus (trivialIndex (P := P) Aplus).pres.num
        (trivialIndex (P := P) Aplus).pres.den := fun v _ ↦
    mem_spaBasicOpen.mpr (by simp [trivialIndex])
  have := isIso_presentationLimitπ hAplus (trivialIndex Aplus) hV
  have : IsIso (trivialIndex (P := P) Aplus).pres.toCompletionLocObjHom :=
    isIso_toCompletionLocObjHom_one
  exact IsIso.of_isIso_fac_right
    (toPresentationLimit_comp_πToPresentation Aplus ⊤ (trivialIndex Aplus))

/-- **The global sections are `A`**: for a complete Hausdorff Huber ring and a subring `A⁺` of
power-bounded elements, the presentation limit over the whole adic spectrum is isomorphic to `A` as
a complete separated topological ring. This is Wedhorn §8.1's `𝒪_X(X) = A`, stated for
`presentationLimit`. Its inverse is the canonical map `toPresentationLimit`
(`presentationLimitTopIso_inv`). -/
noncomputable def presentationLimitTopIso (hAplus : ∀ ⦃a⦄, a ∈ Aplus → IsPowerBounded a) :
    presentationLimit (P := P) Aplus ⊤ ≅ CompleteSeparatedTopCommRingCat.of A :=
  haveI := isIso_toPresentationLimit_top (P := P) Aplus hAplus
  (asIso (toPresentationLimit (P := P) Aplus ⊤)).symm

/-- The inverse of `presentationLimitTopIso` is the canonical map from `A`. -/
@[simp]
theorem presentationLimitTopIso_inv (hAplus : ∀ ⦃a⦄, a ∈ Aplus → IsPowerBounded a) :
    (presentationLimitTopIso (P := P) Aplus hAplus).inv = toPresentationLimit Aplus ⊤ :=
  (rfl)

end TauCeti.ValuationSpectrum

end
