/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tau Ceti contributors
-/
module

public import TauCeti.Condensed.Light.NullSequence.Basic
public import TauCeti.Condensed.Light.InternalHom

/-!
# Light solid modules

A light condensed module is solid if the difference of identity and precomposition by
`nullShift` is invertible on its internal Hom from `nullSeq`. The tensor test formulation
expresses unique summability in every light profinite family.

This is the null-sequence criterion of Rodríguez Camargo, *Notes on Solid Geometry*,
Definition 3.2.1, over a commutative coefficient ring.
-/

public section

universe u

open CategoryTheory Category Limits MonoidalCategory LightCondensed

open scoped ZeroObject

namespace TauCeti

variable {R : Type u} [CommRing R]

/-- The internal difference operator for the null-sequence summability test. -/
noncomputable def lightSolidDifference (M : LightCondMod R) :
    (nullSeq R ⟶[LightCondMod R] M) ⟶ (nullSeq R ⟶[LightCondMod R] M) :=
  𝟙 _ - (MonoidalClosed.pre (nullShift R)).app M

/-- The characteristic equation of the internal null-sequence difference. -/
lemma lightSolidDifference_eq (M : LightCondMod R) :
    lightSolidDifference M = 𝟙 _ - (MonoidalClosed.pre (nullShift R)).app M := by rfl

/-- A light condensed module is solid if its internal null-sequence difference is invertible. -/
def IsLightSolid : ObjectProperty (LightCondMod R) := fun M ↦ IsIso (lightSolidDifference M)

/-- The defining invertibility criterion for solidity. -/
lemma isLightSolid_iff (M : LightCondMod R) :
    IsLightSolid M ↔ IsIso (lightSolidDifference M) := by rfl

/-- The tensor test equivalence sends the external difference to the internal difference. -/
lemma lightSolidDifference_tensorHomSectionsAddEquiv (M : LightCondMod R) (S : LightProfinite.{u})
    (g : nullSeq R ⊗ (free R).obj S.toCondensed ⟶ M) :
    tensorHomSectionsAddEquiv R (nullSeq R) M S (g - (nullShift R ▷ _) ≫ g) =
      (lightSolidDifference M).hom.app (Opposite.op S)
        (tensorHomSectionsAddEquiv R (nullSeq R) M S g) := by
  rw [map_sub, tensorHomSectionsAddEquiv_precomp]
  -- Section maps of sheaf differences are differences of the section maps.
  rfl

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
    simp_rw [Function.comp_def, ← lightSolidDifference_tensorHomSectionsAddEquiv]
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

/-- The null-sequence difference commutes with maps of the coefficient object. -/
@[reassoc]
lemma lightSolidDifference_naturality {M N : LightCondMod R} (f : M ⟶ N) :
    lightSolidDifference M ≫ (ihom (nullSeq R)).map f =
      (ihom (nullSeq R)).map f ≫ lightSolidDifference N := by
  simp only [lightSolidDifference_eq, Preadditive.sub_comp, Preadditive.comp_sub,
    id_comp, comp_id, MonoidalClosed.pre_comm_ihom_map]

/-- Solidity transports across an isomorphism of light condensed modules. -/
lemma IsLightSolid.of_iso {M N : LightCondMod R} (hM : IsLightSolid M) (e : M ≅ N) :
    IsLightSolid N := by
  have : IsIso (lightSolidDifference M) := (isLightSolid_iff M).mp hM
  apply (isLightSolid_iff N).mpr
  have : IsIso ((ihom (nullSeq R)).map e.hom ≫ lightSolidDifference N) := by
    rw [← lightSolidDifference_naturality]
    infer_instance
  exact IsIso.of_isIso_comp_left ((ihom (nullSeq R)).map e.hom) _

/-- Solidity depends only on the isomorphism class of the coefficient object. -/
lemma isLightSolid_iso_iff {M N : LightCondMod R} (e : M ≅ N) :
    IsLightSolid M ↔ IsLightSolid N :=
  ⟨fun h ↦ h.of_iso e, fun h ↦ h.of_iso e.symm⟩

/-- Every zero light condensed module is solid. -/
lemma isLightSolid_of_isZero {M : LightCondMod R} (hM : Limits.IsZero M) :
    IsLightSolid M := by
  apply (isLightSolid_iff M).mpr
  have h := (ihom (nullSeq R)).map_isZero hM
  exact h.isIso h _

/-- The zero light condensed module is solid. -/
lemma isLightSolid_zero : IsLightSolid (0 : LightCondMod R) :=
  isLightSolid_of_isZero (Limits.isZero_zero _)

end TauCeti
