/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DG.Bimodule.Hom.Basic
public import TauCeti.Algebra.Homology.DG.Module.Right.Category

/-!
# The linear category of DG bimodules

`DGBimoduleCat hA hB` bundles DG `(A, B)`-bimodules. It extends the bundled right module
by a compatible left action and its Leibniz rule, retaining a single grading and differential.
Morphisms are the existing degree-zero closed bimodule maps. Forgetting the left action gives a
faithful linear functor to right DG modules.

This follows the bundling and category interface of `DGRightModuleCat`.

## References

* B. Keller, *Deriving DG categories*, Sections 2 and 6.1.
-/

public section

open CategoryTheory

namespace TauCeti

universe uR uA uB uM

variable {R : Type uR} {A : Type uA} {B : Type uB}
  [CommRing R] [Ring A] [Ring B] [Algebra R A] [Algebra R B]
  {𝒜 : ℤ → Submodule R A} {ℬ : ℤ → Submodule R B}
  [GradedAlgebra 𝒜] [GradedAlgebra ℬ]
  {dA : A →ₗ[R] A} {dB : B →ₗ[R] B}

/-- A bundled DG `(A, B)`-bimodule, with left `A` and right `B` actions. -/
structure DGBimoduleCat (hA : IsDGAlgebra 𝒜 dA) (hB : IsDGAlgebra ℬ dB)
    extends DGRightModuleCat.{uR, uB, uM} hB where
  [moduleLeft : Module A carrier]
  [scalarTowerLeft : IsScalarTower R A carrier]
  [commute : SMulCommClass A Bᵐᵒᵖ carrier]
  [gradedLeft : SetLike.GradedSMul 𝒜 grading]
  /-- The left Leibniz rule for the existing right-module differential. -/
  isDGLeftModule : IsDGLeftModule hA grading differential

namespace DGBimoduleCat

attribute [instance] moduleLeft scalarTowerLeft commute gradedLeft

variable {hA : IsDGAlgebra 𝒜 dA} {hB : IsDGAlgebra ℬ dB}

instance : CoeSort (DGBimoduleCat.{uR, uA, uB, uM} hA hB) (Type uM) := ⟨fun M ↦ M.carrier⟩

/-- The two Leibniz rules of a bundled bimodule give its DG bimodule structure. -/
theorem isDGBimodule (M : DGBimoduleCat.{uR, uA, uB, uM} hA hB) :
    IsDGBimodule hA hB M.grading M.differential where
  toIsDGLeftModule := M.isDGLeftModule
  leibniz_right := M.isDGRightModule.leibniz

/-- Bundle a DG bimodule with its existing grading, actions and differential. -/
abbrev of {M : Type uM} [AddCommGroup M] [Module R M] [Module A M] [Module Bᵐᵒᵖ M]
    [IsScalarTower R A M] [IsScalarTower R Bᵐᵒᵖ M] [SMulCommClass A Bᵐᵒᵖ M]
    {ℳ : ℤ → Submodule R M} [DirectSum.Decomposition ℳ] [SetLike.GradedSMul 𝒜 ℳ]
    [SetLike.GradedSMul (InternalGrading.ofDecomposition ℬ).opposite.piece ℳ]
    {dM : M →ₗ[R] M} (hM : IsDGBimodule hA hB ℳ dM) : DGBimoduleCat hA hB where
  toDGRightModuleCat := DGRightModuleCat.of hM.isDGRightModule
  isDGLeftModule := hM.toIsDGLeftModule

instance : Category (DGBimoduleCat.{uR, uA, uB, uM} hA hB) where
  Hom M N := DGBimoduleHom M.isDGBimodule N.isDGBimodule
  id M := DGBimoduleHom.id M.isDGBimodule
  comp f g := g.comp f
  id_comp f := DGBimoduleHom.comp_id f
  comp_id f := DGBimoduleHom.id_comp f
  assoc f g k := (DGBimoduleHom.comp_assoc k g f).symm

variable {M N P : DGBimoduleCat.{uR, uA, uB, uM} hA hB}

instance : FunLike (M ⟶ N) M N :=
  inferInstanceAs (FunLike (DGBimoduleHom M.isDGBimodule N.isDGBimodule) M N)

/-- Bimodule morphisms are determined by their values. -/
@[ext]
theorem hom_ext {f g : M ⟶ N} (hfg : ∀ x, f x = g x) : f = g :=
  DGBimoduleHom.ext hfg

@[simp]
theorem id_apply (M : DGBimoduleCat.{uR, uA, uB, uM} hA hB) (x : M) : (𝟙 M) x = x :=
  DGBimoduleHom.id_apply M.isDGBimodule x

@[simp]
theorem comp_apply (f : M ⟶ N) (g : N ⟶ P) (x : M) : (f ≫ g) x = g (f x) :=
  DGBimoduleHom.comp_apply g f x

instance : Preadditive (DGBimoduleCat.{uR, uA, uB, uM} hA hB) where
  homGroup M N := inferInstanceAs (AddCommGroup (DGBimoduleHom M.isDGBimodule N.isDGBimodule))
  add_comp _ _ _ f g k := DGBimoduleHom.comp_add k f g
  comp_add _ _ _ f g k := DGBimoduleHom.add_comp g k f

instance : Linear R (DGBimoduleCat.{uR, uA, uB, uM} hA hB) where
  homModule M N := inferInstanceAs (Module R (DGBimoduleHom M.isDGBimodule N.isDGBimodule))
  smul_comp _ _ _ r f g := DGBimoduleHom.comp_smul r g f
  comp_smul _ _ _ f r g := DGBimoduleHom.smul_comp r g f

instance : LinearMapClass (M ⟶ N) Bᵐᵒᵖ M N :=
  inferInstanceAs (LinearMapClass (DGBimoduleHom M.isDGBimodule N.isDGBimodule) Bᵐᵒᵖ M N)

instance : GradedFunLike (M ⟶ N) M.grading N.grading :=
  inferInstanceAs
    (GradedFunLike (DGBimoduleHom M.isDGBimodule N.isDGBimodule) M.grading N.grading)

@[simp]
theorem zero_apply (x : M) : (0 : M ⟶ N) x = 0 := DGBimoduleHom.zero_apply x

@[simp]
theorem add_apply (f g : M ⟶ N) (x : M) : (f + g) x = f x + g x :=
  DGBimoduleHom.add_apply f g x

@[simp]
theorem smul_apply (r : R) (f : M ⟶ N) (x : M) : (r • f) x = r • f x :=
  DGBimoduleHom.smul_apply r f x

/-- A bimodule morphism preserves the left action. -/
@[simp]
theorem map_smul_left (f : M ⟶ N) (a : A) (x : M) : f (a • x) = a • f x :=
  DGBimoduleHom.map_smul_left f a x

/-- A bimodule morphism commutes with the differential. -/
@[simp]
theorem map_d (f : M ⟶ N) (x : M) : N.differential (f x) = f (M.differential x) :=
  DGBimoduleHom.map_d f x

/-- Forget the left action of a DG bimodule. The object map is exposed so the underlying
right module remains definitionally the bundled right module. -/
@[expose]
def forgetToRightModuleCat :
    DGBimoduleCat.{uR, uA, uB, uM} hA hB ⥤ DGRightModuleCat.{uR, uB, uM} hB where
  obj M := M.toDGRightModuleCat
  map f := f.1
  map_id M := DGBimoduleHom.id_val M.isDGBimodule
  map_comp f g := DGBimoduleHom.comp_val g f

@[simp]
theorem forgetToRightModuleCat_obj (M : DGBimoduleCat.{uR, uA, uB, uM} hA hB) :
    (forgetToRightModuleCat (hA := hA) (hB := hB)).obj M = M.toDGRightModuleCat := (rfl)

@[simp]
theorem forgetToRightModuleCat_map (f : M ⟶ N) :
    (forgetToRightModuleCat (hA := hA) (hB := hB)).map f = f.1 := (rfl)

instance : (forgetToRightModuleCat.{uR, uA, uB, uM} (hA := hA) (hB := hB)).Faithful where
  map_injective := Subtype.ext

instance : (forgetToRightModuleCat.{uR, uA, uB, uM} (hA := hA) (hB := hB)).Additive where
  map_add := by intros; rfl

instance : (forgetToRightModuleCat.{uR, uA, uB, uM} (hA := hA) (hB := hB)).Linear R where
  map_smul _ _ := rfl

end DGBimoduleCat

end TauCeti
