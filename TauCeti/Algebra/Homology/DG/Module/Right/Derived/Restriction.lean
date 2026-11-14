/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DG.Module.Right.Derived.Basic
public import TauCeti.Algebra.Homology.DG.Module.Right.Restriction.QuasiIso

/-!
# Restriction of scalars on derived categories of DG modules

Restriction along a DG algebra morphism preserves and reflects quasi-isomorphisms, since its
underlying differential is unchanged. It therefore induces a functor on derived categories.
The comparison with ordinary restriction is natural, and restriction along an identity or a
composite agrees, up to natural isomorphism, with identity or successive derived restriction.

No flatness hypothesis on the algebra map or its modules is needed for restriction. Derived
extension of scalars and derived tensor products require separate constructions.

## References

* B. Keller, *Deriving DG categories*, Sections 2 and 6.
-/

public section

open CategoryTheory Functor

namespace TauCeti.DGRightModuleCat

universe uR uA uB uC uM

variable {R : Type uR} {A : Type uA} {B : Type uB} {C : Type uC}
  [CommRing R] [Ring A] [Ring B] [Ring C] [Algebra R A] [Algebra R B] [Algebra R C]
  {𝒜 : ℤ → Submodule R A} {ℬ : ℤ → Submodule R B} {𝒞 : ℤ → Submodule R C}
  [GradedAlgebra 𝒜] [GradedAlgebra ℬ] [GradedAlgebra 𝒞]
  {dA : A →ₗ[R] A} {dB : B →ₗ[R] B} {dC : C →ₗ[R] C}
  {hA : IsDGAlgebra 𝒜 dA} {hB : IsDGAlgebra ℬ dB} {hC : IsDGAlgebra 𝒞 dC}

namespace DerivedCategory

/-- Restriction of scalars along a DG algebra morphism on derived categories of right modules. -/
noncomputable def restrictScalars (f : DGAlgHom hA hB) :
    DerivedCategory.{uR, uB, uM} hB ⥤ DerivedCategory.{uR, uA, uM} hA :=
  Localization.lift (DGRightModuleCat.restrictScalars f ⋙ Q hA) (W := quasiIsos hB) (by
    simpa only [restrictScalarsLocalizerMorphism_functor] using
      (restrictScalarsLocalizerMorphism f).inverts (Q hA)) (Q hB)

/-- Derived restriction lifts ordinary restriction followed by localization. -/
noncomputable instance (f : DGAlgHom hA hB) :
    Localization.Lifting (Q.{uR, uB, uM} hB) (quasiIsos hB)
      (DGRightModuleCat.restrictScalars f ⋙ Q hA) (restrictScalars f) :=
  inferInstanceAs (Localization.Lifting (Q hB) (quasiIsos hB)
    (DGRightModuleCat.restrictScalars f ⋙ Q hA)
    (Localization.lift (DGRightModuleCat.restrictScalars f ⋙ Q hA) (W := quasiIsos hB) (by
      simpa only [restrictScalarsLocalizerMorphism_functor] using
        (restrictScalarsLocalizerMorphism f).inverts (Q hA)) (Q hB)))

/-- Derived restriction agrees with ordinary restriction on DG modules, naturally in the module.
This is the characteristic comparison for computing the descended functor. -/
noncomputable def restrictScalarsFactors (f : DGAlgHom hA hB) :
    Q.{uR, uB, uM} hB ⋙ restrictScalars f ≅ DGRightModuleCat.restrictScalars f ⋙ Q hA :=
  Localization.Lifting.iso (Q hB) (quasiIsos hB) _ _

/-- Derived restriction along the identity algebra map is naturally isomorphic to the identity. -/
noncomputable def restrictScalarsId :
    restrictScalars.{uR, uA, uA, uM} (DGAlgHom.id hA) ≅ 𝟭 (DerivedCategory hA) :=
  Localization.liftNatIso (Q hA) (quasiIsos hA) _ _ _ _
    (isoWhiskerRight DGRightModuleCat.restrictScalarsId (Q hA) ≪≫ Functor.leftUnitor (Q hA))

/-- Derived restriction along a composite agrees with successive derived restrictions. -/
noncomputable def restrictScalarsComp (f : DGAlgHom hA hB) (g : DGAlgHom hB hC) :
    restrictScalars.{uR, uA, uC, uM} (g.comp f) ≅ restrictScalars g ⋙ restrictScalars f := by
  letI : Localization.Lifting (Q.{uR, uC, uM} hC) (quasiIsos hC)
      ((DGRightModuleCat.restrictScalars g ⋙ DGRightModuleCat.restrictScalars f) ⋙ Q hA)
      (restrictScalars g ⋙ restrictScalars f) :=
    ⟨(Functor.associator _ _ _).symm ≪≫
      isoWhiskerRight (restrictScalarsFactors g) (restrictScalars f) ≪≫
      Functor.associator _ _ _ ≪≫
      isoWhiskerLeft (DGRightModuleCat.restrictScalars g) (restrictScalarsFactors f) ≪≫
      (Functor.associator _ _ _).symm⟩
  exact Localization.liftNatIso (Q hC) (quasiIsos hC) _ _ _ _
    (isoWhiskerRight (DGRightModuleCat.restrictScalarsComp f g) (Q hA))

end DerivedCategory

end TauCeti.DGRightModuleCat
