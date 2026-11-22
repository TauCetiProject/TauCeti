/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.ObjectProperty.FiniteProducts
public import Mathlib.CategoryTheory.ObjectProperty.Local
public import TauCeti.Condensed.Light.Monoidal
public import TauCeti.Condensed.Light.NullSequence.Basic

import Mathlib.CategoryTheory.Adjunction.Additive

/-!
# Light solid modules

A light condensed module `B` is solid when one minus precomposition with the null shift is
invertible on the internal Hom out of the null-sequence module into `B`. At the point this asks
that every null sequence `b` admits exactly one null sequence `x` with `x n - x (n + 1) = b n`;
the internal Hom asks the same in families over every light profinite set.

Through the tensor–Hom adjunction this internal condition becomes an external one: `B` is solid
exactly when precomposition with `1 - σ ⊗ Z` is bijective on maps `P ⊗ Z ⟶ B` for every `Z`,
where `P` is the null-sequence module and `σ` its shift. Testing against the free modules on
light profinite sets suffices. So solid modules are the local objects for an explicit family of
test maps, indexed by light profinite sets, and they are closed under isomorphisms and under
all limits.

The definition follows Rodríguez Camargo, *Notes on Solid Geometry*, Definition 3.2.1, and
Wagner, *q-de Rham cohomology and topological Hochschild homology over ku*, §2.1.
-/

public section

universe u

open CategoryTheory Category Limits MonoidalCategory MonoidalClosed LightCondensed

namespace TauCeti

variable (R : Type u) [CommRing R]

/-- A light condensed module `B` is solid when one minus precomposition with the null shift is
an isomorphism of the internal Hom from the null-sequence module to `B`. -/
def IsLightSolid : ObjectProperty (LightCondMod.{u} R) := fun B ↦
  IsIso (𝟙 ((ihom (nullSeq R)).obj B) - (pre (nullShift R)).app B)

/-- The null-sequence test maps: for each light profinite set `S`, one minus the null shift
tensored with the free module on `S`. -/
def nullSeqTest : MorphismProperty (LightCondMod.{u} R) :=
  MorphismProperty.ofHoms fun S : LightProfinite.{u} ↦
    𝟙 (nullSeq R ⊗ (free R).obj S.toCondensed) - nullShift R ▷ (free R).obj S.toCondensed

variable {R}

/-- Restatement of the definition of light solidity. -/
lemma isLightSolid_iff_isIso (B : LightCondMod.{u} R) :
    IsLightSolid R B ↔ IsIso (𝟙 ((ihom (nullSeq R)).obj B) - (pre (nullShift R)).app B) :=
  Iff.rfl

/-- Uncurrying turns postcomposition with one minus `pre (nullShift R)` into precomposition
with one minus the whiskered null shift. -/
private lemma uncurry_comp_sub_pre {Z B : LightCondMod.{u} R}
    (g : Z ⟶ (ihom (nullSeq R)).obj B) :
    uncurry (g ≫ (𝟙 _ - (pre (nullShift R)).app B)) =
      (𝟙 _ - nullShift R ▷ Z) ≫ uncurry g := by
  rw [Preadditive.comp_sub, Preadditive.sub_comp, Category.comp_id, Category.id_comp,
    ← uncurry_pre_app, ← homEquiv_symm_apply_eq, ← homEquiv_symm_apply_eq,
    ← homEquiv_symm_apply_eq, (ihom.adjunction (nullSeq R)).homAddEquiv_symm_sub]

/-- Under currying, one minus the whiskered null shift on maps `nullSeq R ⊗ Z ⟶ B` is
postcomposition with the solidity test map on maps `Z ⟶ ihom (nullSeq R) B`. -/
private lemma bijective_sub_whiskerRight_comp_iff (Z B : LightCondMod.{u} R) :
    Function.Bijective (fun g : nullSeq R ⊗ Z ⟶ B ↦ g - nullShift R ▷ Z ≫ g) ↔
      Function.Bijective fun g : Z ⟶ (ihom (nullSeq R)).obj B ↦
        g ≫ (𝟙 _ - (pre (nullShift R)).app B) := by
  have h : (fun g : nullSeq R ⊗ Z ⟶ B ↦ g - nullShift R ▷ Z ≫ g) =
      ((ihom.adjunction (nullSeq R)).homEquiv Z B).symm ∘ (fun g ↦
        g ≫ (𝟙 _ - (pre (nullShift R)).app B)) ∘ (ihom.adjunction (nullSeq R)).homEquiv Z B := by
    ext g : 1
    simp only [Function.comp_apply, homEquiv_apply_eq, homEquiv_symm_apply_eq,
      uncurry_comp_sub_pre, uncurry_curry, Preadditive.sub_comp, Category.id_comp]
  rw [h, Equiv.comp_bijective, Equiv.bijective_comp]

/-- Solidity is invertibility of one minus the null shift on maps out of `P ⊗ Z`, for every
light condensed module `Z`, where `P` is the null-sequence module. -/
theorem isLightSolid_iff_bijective (B : LightCondMod.{u} R) :
    IsLightSolid R B ↔ ∀ Z : LightCondMod.{u} R,
      Function.Bijective fun g : nullSeq R ⊗ Z ⟶ B ↦ g - nullShift R ▷ Z ≫ g := by
  simp only [bijective_sub_whiskerRight_comp_iff, isLightSolid_iff_isIso,
    isIso_iff_yoneda_map_bijective]

/-- Solidity is detected by the free modules on light profinite sets: it suffices that one minus
the null shift is invertible on maps out of `P ⊗ R[S]` for every light profinite `S`. -/
theorem isLightSolid_iff_bijective_free (B : LightCondMod.{u} R) :
    IsLightSolid R B ↔ ∀ S : LightProfinite.{u},
      Function.Bijective fun g : nullSeq R ⊗ (free R).obj S.toCondensed ⟶ B ↦
        g - nullShift R ▷ (free R).obj S.toCondensed ≫ g := by
  simp only [bijective_sub_whiskerRight_comp_iff, isLightSolid_iff_isIso,
    LightCondMod.isIso_iff_bijective_comp_free]

variable (R) in
/-- Solid modules are the local objects for the null-sequence test maps. -/
theorem isLightSolid_eq_isLocal : IsLightSolid R = (nullSeqTest R).isLocal := by
  ext B
  rw [isLightSolid_iff_bijective_free, MorphismProperty.isLocal_iff]
  constructor
  · rintro h _ _ _ ⟨S⟩
    simpa only [Preadditive.sub_comp, Category.id_comp] using h S
  · intro h S
    simpa only [Preadditive.sub_comp, Category.id_comp] using
      h _ (MorphismProperty.ofHoms.mk S)

/-- Solidity is invariant under isomorphism. -/
instance : (IsLightSolid R).IsClosedUnderIsomorphisms := by
  rw [isLightSolid_eq_isLocal]
  infer_instance

/-- Solid modules are closed under all limits. -/
instance (J : Type*) [Category* J] : (IsLightSolid R).IsClosedUnderLimitsOfShape J := by
  rw [isLightSolid_eq_isLocal]
  infer_instance

/-- A zero module is solid. -/
lemma isLightSolid_of_isZero {B : LightCondMod.{u} R} (hB : IsZero B) : IsLightSolid R B :=
  (IsLightSolid R).prop_of_isTerminal B hB.isTerminal

end TauCeti
