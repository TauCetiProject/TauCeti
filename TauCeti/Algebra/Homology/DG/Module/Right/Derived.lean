/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Localization.HasLocalization
public import Mathlib.CategoryTheory.Localization.LocalizerMorphism
public import TauCeti.Algebra.Homology.DG.Module.Right.Restriction.QuasiIso

/-!
# Derived categories of DG right modules

The derived category of a DG algebra is the localization of its right DG modules at
quasi-isomorphisms. Cohomology descends to this category, and detects precisely which original
module maps become invertible. Restriction along a DG algebra morphism descends as well, since
it preserves the underlying differential and hence preserves quasi-isomorphisms.

These are ordinary categorical localizations. No triangulated structure, semi-free resolution,
or derived tensor product is asserted here. The localization is chosen through Mathlib's
`MorphismProperty.HasLocalization`, allowing a later smaller Hom-universe model. The instance
`MorphismProperty.HasLocalization.standard` always supplies the constructed localization.
The universal property and the lifting of functors and natural transformations are Mathlib's
`Functor.IsLocalization`, `Localization.lift`, and `Localization.liftNatIso`.

## References

* B. Keller, *Deriving DG categories*, Sections 3 and 6.

The categorical constructions reuse Mathlib's localization and localizer-morphism API.
-/

public noncomputable section

open CategoryTheory CategoryTheory.Functor

namespace TauCeti.DGRightModuleCat

universe uR uA uB uC uM wA wB wC

variable {R : Type uR} {A : Type uA} {B : Type uB} {C : Type uC}
  [CommRing R] [Ring A] [Ring B] [Ring C] [Algebra R A] [Algebra R B] [Algebra R C]
  {𝒜 : ℤ → Submodule R A} {ℬ : ℤ → Submodule R B} {𝒞 : ℤ → Submodule R C}
  [GradedAlgebra 𝒜] [GradedAlgebra ℬ] [GradedAlgebra 𝒞]
  {dA : A →ₗ[R] A} {dB : B →ₗ[R] B} {dC : C →ₗ[R] C}
  (hA : IsDGAlgebra 𝒜 dA) {hB : IsDGAlgebra ℬ dB} {hC : IsDGAlgebra 𝒞 dC}
  [MorphismProperty.HasLocalization.{wA} (quasiIsos.{uR, uA, uM} hA)]

/-- The derived category of right DG modules over `hA`, with the chosen localization model. -/
abbrev DerivedCategory := (quasiIsos.{uR, uA, uM} hA).Localization'

/-- The localization functor from DG right modules to their derived category. -/
abbrev toDerived : DGRightModuleCat.{uR, uA, uM} hA ⥤ DerivedCategory hA :=
  (quasiIsos hA).Q'

namespace DerivedCategory

/-- Cohomology of a derived DG module, as a right module over the cohomology algebra. -/
def cohomology : DerivedCategory hA ⥤ ModuleCat.{uM} hA.Cohomologyᵐᵒᵖ :=
  Localization.lift (W := quasiIsos hA) cohomologyFunctor
    (fun _ _ f hf ↦ (ConcreteCategory.isIso_iff_bijective _).mpr
      ((DGRightModuleHom.isQuasiIso_iff f).mp ((quasiIsos_iff f).mp hf)))
    (toDerived hA)

/-- Derived cohomology agrees with cohomology on DG modules, naturally in the module. -/
def cohomologyIso : toDerived hA ⋙ cohomology hA ≅ cohomologyFunctor :=
  Localization.fac (W := quasiIsos hA) cohomologyFunctor
    (fun _ _ f hf ↦ (ConcreteCategory.isIso_iff_bijective _).mpr
      ((DGRightModuleHom.isQuasiIso_iff f).mp ((quasiIsos_iff f).mp hf))) (toDerived hA)

instance : Localization.Lifting (toDerived hA) (quasiIsos hA) cohomologyFunctor
    (cohomology hA) := ⟨cohomologyIso hA⟩

end DerivedCategory

/-- A DG module map becomes invertible in the derived category exactly when it is a
quasi-isomorphism. In particular the localization introduces no additional weak equivalences. -/
@[simp]
theorem isIso_toDerived_map_iff {M N : DGRightModuleCat.{uR, uA, uM} hA} (f : M ⟶ N) :
    IsIso ((toDerived hA).map f) ↔ IsQuasiIso f := by
  constructor
  · intro hf
    have : IsIso ((toDerived hA ⋙ DerivedCategory.cohomology hA).map f) :=
      Functor.map_isIso (DerivedCategory.cohomology hA) ((toDerived hA).map f)
    have := (NatIso.isIso_map_iff (DerivedCategory.cohomologyIso hA) f).mp this
    exact (DGRightModuleHom.isQuasiIso_iff f).mpr
      ((ConcreteCategory.isIso_iff_bijective _).mp this)
  · intro hf
    exact Localization.inverts (toDerived hA) (quasiIsos hA) f ((quasiIsos_iff f).mpr hf)

variable {hA}

/-- Restriction of scalars, regarded as a morphism of localizers at quasi-isomorphisms. -/
private def restrictScalarsLocalizer (f : DGAlgHom hA hB) :
    LocalizerMorphism (quasiIsos.{uR, uB, uM} hB) (quasiIsos.{uR, uA, uM} hA) where
  functor := restrictScalars f
  map _ _ g hg := (quasiIsos_iff _).mpr
    ((isQuasiIso_restrictScalars_map_iff f g).mpr ((quasiIsos_iff _).mp hg))

namespace DerivedCategory

variable [MorphismProperty.HasLocalization.{wB} (quasiIsos.{uR, uB, uM} hB)]

/-- Restriction of scalars on derived right DG modules. No resolution is necessary. -/
def restrictScalars (f : DGAlgHom hA hB) :
    DerivedCategory hB ⥤ DerivedCategory hA :=
  (restrictScalarsLocalizer f).localizedFunctor (toDerived hB) (toDerived hA)

/-- Derived restriction agrees with restriction followed by localization on DG modules. -/
def restrictScalarsIso (f : DGAlgHom hA hB) :
    toDerived hB ⋙ restrictScalars f ≅
      DGRightModuleCat.restrictScalars f ⋙ toDerived hA :=
  Localization.Lifting.iso (toDerived hB) (quasiIsos hB)
    ((restrictScalarsLocalizer f).functor ⋙ toDerived hA)
    ((restrictScalarsLocalizer f).localizedFunctor (toDerived hB) (toDerived hA))

instance (f : DGAlgHom hA hB) :
    Localization.Lifting (toDerived hB) (quasiIsos hB)
      (DGRightModuleCat.restrictScalars f ⋙ toDerived hA) (restrictScalars f) :=
  ⟨restrictScalarsIso f⟩

/-- Restriction along the identity algebra morphism is the identity on the derived category. -/
def restrictScalarsId : restrictScalars (DGAlgHom.id hA) ≅ 𝟭 (DerivedCategory hA) :=
  (Localization.fullyFaithfulWhiskeringLeft (toDerived hA) (quasiIsos hA) _).preimageIso
    (restrictScalarsIso (DGAlgHom.id hA) ≪≫
      isoWhiskerRight DGRightModuleCat.restrictScalarsId (toDerived hA) ≪≫
      Functor.leftUnitor _ ≪≫ (Functor.rightUnitor _).symm)

variable [MorphismProperty.HasLocalization.{wC} (quasiIsos.{uR, uC, uM} hC)]

/-- Restriction along a composite algebra morphism is successive derived restriction. -/
def restrictScalarsComp (f : DGAlgHom hA hB) (g : DGAlgHom hB hC) :
    restrictScalars (g.comp f) ≅ restrictScalars g ⋙ restrictScalars f :=
  (Localization.fullyFaithfulWhiskeringLeft (toDerived hC) (quasiIsos hC) _).preimageIso
    (restrictScalarsIso (g.comp f) ≪≫
      isoWhiskerRight (DGRightModuleCat.restrictScalarsComp f g) (toDerived hA) ≪≫
      Functor.associator _ _ _ ≪≫
      isoWhiskerLeft (DGRightModuleCat.restrictScalars g) (restrictScalarsIso f).symm ≪≫
      (Functor.associator _ _ _).symm ≪≫
      isoWhiskerRight (restrictScalarsIso g).symm (restrictScalars f) ≪≫
      Functor.associator _ _ _)

end DerivedCategory

end TauCeti.DGRightModuleCat
