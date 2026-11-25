/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.ObjectProperty.Local
public import TauCeti.Condensed.Light.NullSequence.Basic
public import TauCeti.Condensed.Light.InternalHom.Basic

import TauCeti.CategoryTheory.Monoidal.Closed.Preadditive
import TauCeti.Condensed.Light.Basic

/-!
# Light solid modules

A light condensed module is solid if the difference of identity and precomposition by
`nullShift` is invertible on its internal Hom from `nullSeq`. The tensor test formulation
expresses unique summability in every light profinite family. By the tensor–Hom adjunction
it is equivalent to the same unique summability on maps out of `nullSeq R ⊗ Z` for every light
condensed module `Z`. So solid modules are the local objects for an explicit family of test maps,
indexed by light profinite sets, and they are closed under all limits.

This is the null-sequence criterion of Rodríguez Camargo, *Notes on Solid Geometry*,
Definition 3.2.1, over a commutative coefficient ring; see also Wagner, *q-de Rham cohomology and
topological Hochschild homology over ku*, §2.1. The tensor criterion and the closure under limits
are formal consequences of the tensor–Hom adjunction and of the general theory of local objects.
-/

public section

universe u

open CategoryTheory Category Limits MonoidalCategory LightCondensed

open scoped ZeroObject

namespace LightCondMod

open TauCeti

variable {R : Type u} [CommRing R]

/-- The internal difference operator for the null-sequence summability test. -/
noncomputable def lightSolidDifference (M : LightCondMod R) :
    (nullSeq R ⟶[LightCondMod R] M) ⟶ (nullSeq R ⟶[LightCondMod R] M) :=
  𝟙 _ - (MonoidalClosed.pre (nullShift R)).app M

/-- The characteristic equation of the internal null-sequence difference. -/
lemma lightSolidDifference_def (M : LightCondMod R) :
    lightSolidDifference M = 𝟙 _ - (MonoidalClosed.pre (nullShift R)).app M := by rfl

/-- On sections, the internal null-sequence difference subtracts the precomposition map. -/
@[simp]
lemma lightSolidDifference_app_apply (M : LightCondMod R) (S : LightProfinite.{u})
    (s : (nullSeq R ⟶[LightCondMod R] M).obj.obj (Opposite.op S)) :
    (lightSolidDifference M).hom.app (Opposite.op S) s =
      s - ((MonoidalClosed.pre (nullShift R)).app M).hom.app (Opposite.op S) s := by
  rw [lightSolidDifference_def, hom_app_sub_apply]
  simp only [ObjectProperty.FullSubcategory.id_hom, NatTrans.id_app, ModuleCat.id_apply]

/-- The null-sequence difference commutes with maps of the coefficient object. -/
@[reassoc]
lemma lightSolidDifference_naturality {M N : LightCondMod R} (f : M ⟶ N) :
    lightSolidDifference M ≫ (ihom (nullSeq R)).map f =
      (ihom (nullSeq R)).map f ≫ lightSolidDifference N := by
  simp only [lightSolidDifference_def, Preadditive.sub_comp, Preadditive.comp_sub,
    id_comp, comp_id, MonoidalClosed.pre_comm_ihom_map]

end LightCondMod

open TauCeti LightCondMod

namespace LightCondensed

variable {R : Type u} [CommRing R]

/-- The tensor test equivalence sends the external difference to the internal difference. -/
lemma tensorHomSectionsAddEquiv_sub_precomp (M : LightCondMod R) (S : LightProfinite.{u})
    (g : nullSeq R ⊗ (free R).obj S.toCondensed ⟶ M) :
    tensorHomSectionsAddEquiv R (nullSeq R) M S (g - (nullShift R ▷ _) ≫ g) =
      (lightSolidDifference M).hom.app (Opposite.op S)
        (tensorHomSectionsAddEquiv R (nullSeq R) M S g) := by
  rw [map_sub, tensorHomSectionsAddEquiv_precomp, lightSolidDifference_app_apply]

end LightCondensed

namespace TauCeti

variable {R : Type u} [CommRing R]

/-- A light condensed module is solid if its internal null-sequence difference is invertible. -/
def IsLightSolid : ObjectProperty (LightCondMod R) := fun M ↦ IsIso (lightSolidDifference M)

/-- The defining invertibility criterion for solidity. -/
lemma isLightSolid_iff (M : LightCondMod R) :
    IsLightSolid M ↔ IsIso (lightSolidDifference M) := by rfl

/-- Solidity is equivalent to unique solvability of the difference equation on every test family. -/
lemma isLightSolid_iff_bijective (M : LightCondMod R) :
    IsLightSolid M ↔ ∀ S : LightProfinite.{u}, Function.Bijective
      (fun g : nullSeq R ⊗ (free R).obj S.toCondensed ⟶ M ↦
        g - (nullShift R ▷ _) ≫ g) := by
  have h (S : LightProfinite.{u}) :
      Function.Bijective ((lightSolidDifference M).hom.app (Opposite.op S)) ↔
        Function.Bijective (fun g : nullSeq R ⊗ (free R).obj S.toCondensed ⟶ M ↦
          g - (nullShift R ▷ _) ≫ g) := by
    rw [← Function.Bijective.of_comp_iff _ (tensorHomSectionsAddEquiv R (nullSeq R) M S).bijective]
    simp_rw [Function.comp_def, ← tensorHomSectionsAddEquiv_sub_precomp]
    exact Function.Bijective.of_comp_iff' (tensorHomSectionsAddEquiv R (nullSeq R) M S).bijective _
  -- The sheaf-to-presheaf functor detects invertibility componentwise.
  rw [isLightSolid_iff]
  rw [← isIso_iff_of_reflects_iso _ (sheafToPresheaf _ _),
    NatTrans.isIso_iff_isIso_app]
  constructor
  · intro hs S
    exact (h S).mp ((ConcreteCategory.isIso_iff_bijective _).mp (hs (Opposite.op S)))
  · intro hs S
    exact (ConcreteCategory.isIso_iff_bijective _).mpr ((h S.unop).mpr (hs S.unop))

/-- Uncurrying turns postcomposition with the internal null-sequence difference into
precomposition with one minus the whiskered null shift. -/
private lemma uncurry_comp_lightSolidDifference {Z M : LightCondMod R}
    (g : Z ⟶ (nullSeq R ⟶[LightCondMod R] M)) :
    MonoidalClosed.uncurry (g ≫ lightSolidDifference M) =
      (𝟙 _ - nullShift R ▷ Z) ≫ MonoidalClosed.uncurry g := by
  rw [lightSolidDifference_def, Preadditive.comp_sub, comp_id, uncurry_sub,
    MonoidalClosed.uncurry_pre_app, Preadditive.sub_comp, id_comp]

/-- Solidity is equivalent to unique solvability of the difference equation on maps out of
`nullSeq R ⊗ Z`, for every light condensed module `Z`. -/
theorem isLightSolid_iff_bijective_tensor (M : LightCondMod R) :
    IsLightSolid M ↔ ∀ Z : LightCondMod R,
      Function.Bijective fun g : nullSeq R ⊗ Z ⟶ M ↦ g - (nullShift R ▷ Z) ≫ g := by
  rw [isLightSolid_iff, isIso_iff_yoneda_map_bijective]
  refine forall_congr' fun Z ↦ ?_
  have h : (fun g : nullSeq R ⊗ Z ⟶ M ↦ g - (nullShift R ▷ Z) ≫ g) =
      ((ihom.adjunction (nullSeq R)).homEquiv Z M).symm ∘
        (fun g ↦ g ≫ lightSolidDifference M) ∘ (ihom.adjunction (nullSeq R)).homEquiv Z M := by
    ext g : 1
    simp only [Function.comp_apply, MonoidalClosed.homEquiv_apply_eq,
      MonoidalClosed.homEquiv_symm_apply_eq, uncurry_comp_lightSolidDifference,
      MonoidalClosed.uncurry_curry, Preadditive.sub_comp, id_comp]
  rw [h, Equiv.comp_bijective, Equiv.bijective_comp]

variable (R) in
/-- The null-sequence test maps: for each light profinite set `S`, one minus the null shift
tensored with the free module on `S`. -/
def nullSeqTest : MorphismProperty (LightCondMod R) :=
  MorphismProperty.ofHoms fun S : LightProfinite.{u} ↦
    𝟙 (nullSeq R ⊗ (free R).obj S.toCondensed) - nullShift R ▷ (free R).obj S.toCondensed

variable (R) in
/-- The characteristic equation of the null-sequence test maps. -/
lemma nullSeqTest_def : nullSeqTest R = MorphismProperty.ofHoms fun S : LightProfinite.{u} ↦
    𝟙 (nullSeq R ⊗ (free R).obj S.toCondensed) - nullShift R ▷ (free R).obj S.toCondensed :=
  (rfl)

variable (R) in
/-- The test map indexed by a light profinite set `S` is a null-sequence test map. -/
lemma nullSeqTest_mk (S : LightProfinite.{u}) :
    nullSeqTest R
      (𝟙 (nullSeq R ⊗ (free R).obj S.toCondensed) - nullShift R ▷ (free R).obj S.toCondensed) :=
  MorphismProperty.ofHoms.mk S

variable (R) in
/-- Solid modules are the local objects for the null-sequence test maps. -/
theorem isLightSolid_eq_isLocal : IsLightSolid (R := R) = (nullSeqTest R).isLocal := by
  ext M
  rw [isLightSolid_iff_bijective, MorphismProperty.isLocal_iff]
  constructor
  · intro h _ _ _ hf
    rw [nullSeqTest_def] at hf
    obtain ⟨S⟩ := hf
    simpa only [Preadditive.sub_comp, id_comp] using h S
  · intro h S
    simpa only [Preadditive.sub_comp, id_comp] using h _ (nullSeqTest_mk R S)

/-- Solid modules are closed under all limits. -/
instance (J : Type*) [Category* J] : (IsLightSolid (R := R)).IsClosedUnderLimitsOfShape J := by
  rw [isLightSolid_eq_isLocal]
  infer_instance

instance : (IsLightSolid (R := R)).IsClosedUnderIsomorphisms where
  of_iso e hM := by
    let difference : ihom (nullSeq R) ⟶ ihom (nullSeq R) :=
      { app := lightSolidDifference
        naturality _ _ f := (lightSolidDifference_naturality f).symm }
    exact (NatTrans.isIso_app_iff_of_iso difference e).mp hM

instance : (IsLightSolid (R := R)).ContainsZero where
  exists_zero := by
    refine ⟨0, Limits.isZero_zero _, ?_⟩
    apply (isLightSolid_iff _).mpr
    have h := (ihom (nullSeq R)).map_isZero (Limits.isZero_zero (LightCondMod R))
    exact h.isIso h _

end TauCeti
