/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tau Ceti contributors
-/
module

public import Mathlib.Condensed.Light.AB
public import TauCeti.Condensed.Light.Colimits
public import TauCeti.Condensed.Light.Solid.Abelian

import Mathlib.CategoryTheory.Presentable.OrthogonalReflection
import Mathlib.CategoryTheory.Presentable.Retracts
import TauCeti.CategoryTheory.ObjectProperty.ColimitsOfShape

/-!
# Light solidification

Each null-sequence test map is an endomorphism of a retract of a free module on
a light profinite test space. These retracts are finitely presentable. Mathlib's
orthogonal reflection (`MorphismProperty.isRightAdjoint_ι_isLocal`) gives the left adjoint
to the inclusion of light solid modules. Its local-object theorem gives closure under
filtered colimits. Closure under finite and filtered colimits gives closure under all
small colimits, and filtered exactness and reflection yield the Grothendieck structure.

The summability test and reflection follow Rodríguez Camargo, *Notes on Solid Geometry*,
Definition 3.2.1 and Theorem 3.2.4
([arXiv:2603.03012v1](https://arxiv.org/abs/2603.03012v1)).
-/

public section

universe u

open CategoryTheory Category Limits LightCondensed MonoidalCategory

namespace TauCeti

variable (R : Type u) [CommRing R]

attribute [local instance] Cardinal.fact_isRegular_aleph0

/-- The reduced free sequence module tensored with a free test module is finitely presentable. -/
instance isFinitelyPresentable_nullSeq_tensor_free (S : LightProfinite.{u}) :
    IsFinitelyPresentable.{u} (nullSeq R ⊗ (free R).obj S.toCondensed) := by
  let F := lightProfiniteToLightCondSet ⋙ free R
  let e := Functor.Monoidal.μIso F liftedSequence S
  have : IsFinitelyPresentable.{u} (F.obj (liftedSequence ⊗ S)) :=
    LightProfinite.isFinitelyPresentable_free R _
  have : IsFinitelyPresentable.{u} (F.obj liftedSequence ⊗ F.obj S) :=
    isCardinalPresentable_of_iso e.symm _
  let r : Retract (nullSeq R ⊗ F.obj S) (F.obj liftedSequence ⊗ F.obj S) :=
    (reducedLightFreeRetract R (Under.mk inftyPoint)).map (tensorRight (F.obj S))
  exact r.isCardinalPresentable (Cardinal.aleph0 : Cardinal.{u})

/-- Both endpoints of every null-sequence test are finitely presentable. -/
private lemma nullSeqTest_isFinitelyPresentable {X Y : LightCondMod R} {f : X ⟶ Y}
    (hf : nullSeqTest R f) : IsFinitelyPresentable.{u} X ∧ IsFinitelyPresentable.{u} Y := by
  rw [nullSeqTest_def] at hf
  obtain ⟨S⟩ := hf
  exact ⟨inferInstance, inferInstance⟩

/-- A family of null-sequence tests indexed by a small model of the site. -/
private def smallNullSeqTest : MorphismProperty (LightCondMod R) :=
  MorphismProperty.ofHoms fun T : SmallModel.{u} LightProfinite.{u} ↦
    let S := (equivSmallModel.{u} LightProfinite.{u}).inverse.obj T
    𝟙 (nullSeq R ⊗ (free R).obj S.toCondensed) - nullShift R ▷ (free R).obj S.toCondensed

private lemma smallNullSeqTest_le : smallNullSeqTest R ≤ nullSeqTest R := by
  rintro _ _ _ ⟨T⟩
  exact nullSeqTest_mk R _

private lemma isLightSolid_eq_isLocal_smallNullSeqTest :
    IsLightSolid (R := R) = (smallNullSeqTest R).isLocal := by
  rw [isLightSolid_eq_isLocal]
  apply le_antisymm (MorphismProperty.isLocal_antitone (smallNullSeqTest_le R))
  apply (ObjectProperty.le_isLocal_iff _ _).mp
  intro X Y f hf
  rw [nullSeqTest_def] at hf
  obtain ⟨S⟩ := hf
  -- The site equivalence identifies each test with one in the small family.
  let e := equivSmallModel.{u} LightProfinite.{u}
  let i := (lightProfiniteToLightCondSet ⋙ free R).mapIso (e.unitIso.app S)
  let j := (tensorLeft (nullSeq R)).mapIso i
  have w : (𝟙 _ - nullShift R ▷ _) ≫ j.hom = j.hom ≫ (𝟙 _ - nullShift R ▷ _) := by
    simp [j, Preadditive.sub_comp, Preadditive.comp_sub, whisker_exchange]
  apply ((smallNullSeqTest R).isLocal.isLocal.arrow_mk_iso_iff (Arrow.isoMk j j w.symm)).mpr
  exact (ObjectProperty.le_isLocal_iff _ _).mpr le_rfl _
    (MorphismProperty.ofHoms.mk (e.functor.obj S))

/-- The inclusion of light solid modules admits a left adjoint, light solidification. -/
instance isLightSolid_isRightAdjoint : (IsLightSolid (R := R)).ι.IsRightAdjoint := by
  rw [isLightSolid_eq_isLocal_smallNullSeqTest]
  have : MorphismProperty.IsSmall.{u} (smallNullSeqTest R) := by
    unfold smallNullSeqTest
    infer_instance
  have : HasColimitsOfSize.{u, u} (LightCondMod R) :=
    IsGrothendieckAbelian.hasColimits (LightCondMod R)
  exact (smallNullSeqTest R).isRightAdjoint_ι_isLocal (Cardinal.aleph0 : Cardinal.{u})
    (fun _ _ _ hf ↦ nullSeqTest_isFinitelyPresentable R (smallNullSeqTest_le R _ hf))

/-- Light solid modules are closed under filtered colimits in light condensed modules. -/
private lemma isLightSolid_isClosedUnderFilteredColimits (J : Type u) [SmallCategory J]
    [IsFiltered J] :
    (IsLightSolid (R := R)).IsClosedUnderColimitsOfShape J := by
  rw [isLightSolid_eq_isLocal]
  have := (nullSeqTest R).isClosedUnderCardinalFilteredColimits_isLocal Cardinal.aleph0
    (fun _ _ _ hf ↦ nullSeqTest_isFinitelyPresentable R hf)
  have := (isCardinalFiltered_aleph0_iff J).mpr ‹IsFiltered J›
  exact ObjectProperty.IsClosedUnderCardinalFilteredColimits.isCardinalClosedUnderColimitsOfShape
    (nullSeqTest R).isLocal Cardinal.aleph0 J

/-- The full subcategory of light solid modules is closed under all small colimits. -/
instance isLightSolid_isClosedUnderColimitsOfShape (J : Type u) [SmallCategory J] :
    (IsLightSolid (R := R)).IsClosedUnderColimitsOfShape J := by
  have : HasColimitsOfSize.{u, u} (LightCondMod R) :=
    IsGrothendieckAbelian.hasColimits (LightCondMod R)
  exact (IsLightSolid (R := R)).isClosedUnderColimitsOfShape_of_finite_and_filtered
    (isLightSolid_isClosedUnderFilteredColimits R) J

/-- Light solid modules form a Grothendieck abelian category. A separator is obtained by
solidifying an ambient separator, and filtered colimits are exact by ambient exactness. -/
instance isGrothendieckAbelian_lightSolid :
    IsGrothendieckAbelian.{u} (IsLightSolid (R := R)).FullSubcategory := by
  let P := IsLightSolid (R := R)
  have : HasColimitsOfSize.{u, u} (LightCondMod R) :=
    IsGrothendieckAbelian.hasColimits (LightCondMod R)
  have : HasColimitsOfSize.{u, u} P.FullSubcategory := ⟨fun _ _ ↦ inferInstance⟩
  exact
    { ab5OfSize := ⟨fun J _ _ ↦ HasExactColimitsOfShape.domain_of_functor J P.ι⟩
      hasSeparator := HasSeparator.of_adjunction (Adjunction.ofIsRightAdjoint P.ι) }

end TauCeti
