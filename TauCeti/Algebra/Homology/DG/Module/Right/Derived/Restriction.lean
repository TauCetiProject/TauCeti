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
underlying differential is unchanged. As a morphism of localizers it therefore induces a functor
on derived categories, which lifts ordinary restriction along localization. The comparison with
ordinary restriction is natural, and restriction along an identity or a composite agrees, up to
natural isomorphism, with identity or successive derived restriction; their components on DG
modules are computed from the ordinary comparisons.

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

/-- Restriction of scalars along a DG algebra morphism on derived categories of right modules,
induced by ordinary restriction as a morphism of localizers. -/
noncomputable def restrictScalars (f : DGAlgHom hA hB) :
    DerivedCategory.{uR, uB, uM} hB ⥤ DerivedCategory.{uR, uA, uM} hA :=
  (restrictScalarsLocalizerMorphism f).localizedFunctor (Q hB) (Q hA)

/-- Derived restriction is the localized functor of the ordinary restriction localizer morphism. -/
theorem restrictScalars_def (f : DGAlgHom hA hB) :
    restrictScalars.{uR, uA, uB, uM} f =
      (restrictScalarsLocalizerMorphism f).localizedFunctor (Q hB) (Q hA) := (rfl)

/-- Derived restriction lifts ordinary restriction followed by localization. -/
noncomputable instance liftingRestrictScalars (f : DGAlgHom hA hB) :
    Localization.Lifting (Q.{uR, uB, uM} hB) (quasiIsos hB)
      (DGRightModuleCat.restrictScalars f ⋙ Q hA) (restrictScalars f) := by
  rw [restrictScalars_def]
  exact restrictScalarsLocalizerMorphism_functor f ▸
    (restrictScalarsLocalizerMorphism f).liftingLocalizedFunctor (Q hB) (Q hA)

/-- Localization intertwines ordinary and derived restriction. -/
noncomputable instance catCommSqRestrictScalars (f : DGAlgHom hA hB) :
    CatCommSq (DGRightModuleCat.restrictScalars f) (Q.{uR, uB, uM} hB) (Q hA)
      (restrictScalars f) := by
  rw [restrictScalars_def]
  exact restrictScalarsLocalizerMorphism_functor f ▸
    (restrictScalarsLocalizerMorphism f).catCommSq (Q hB) (Q hA)

/-- Derived restriction agrees with ordinary restriction on DG modules, naturally in the module.
This is the characteristic comparison for computing the descended functor. -/
noncomputable def restrictScalarsFactors (f : DGAlgHom hA hB) :
    Q.{uR, uB, uM} hB ⋙ restrictScalars f ≅ DGRightModuleCat.restrictScalars f ⋙ Q hA :=
  Localization.Lifting.iso (Q hB) (quasiIsos hB) _ _

/-- The lifting isomorphism of derived restriction is `restrictScalarsFactors`. -/
@[simp]
theorem liftingIso_restrictScalars (f : DGAlgHom hA hB) :
    Localization.Lifting.iso (Q.{uR, uB, uM} hB) (quasiIsos hB)
      (DGRightModuleCat.restrictScalars f ⋙ Q hA) (restrictScalars f) =
      restrictScalarsFactors f := (rfl)

/-- The square intertwining ordinary and derived restriction is `restrictScalarsFactors`. -/
@[simp]
theorem catCommSq_iso_restrictScalars (f : DGAlgHom hA hB) :
    CatCommSq.iso (DGRightModuleCat.restrictScalars f) (Q.{uR, uB, uM} hB) (Q hA)
      (restrictScalars f) = (restrictScalarsFactors f).symm := by
  unfold restrictScalarsFactors
  delta catCommSqRestrictScalars liftingRestrictScalars
  cases restrictScalars_def.{uR, uA, uB, uM} f
  have compatible (F : DGRightModuleCat.{uR, uB, uM} hB ⥤ DGRightModuleCat hA)
      (e : (restrictScalarsLocalizerMorphism f).functor = F) :
      letI : CatCommSq F (Q hB) (Q hA)
          ((restrictScalarsLocalizerMorphism f).localizedFunctor (Q hB) (Q hA)) :=
        e ▸ (restrictScalarsLocalizerMorphism f).catCommSq (Q hB) (Q hA)
      letI : Localization.Lifting (Q hB) (quasiIsos hB) (F ⋙ Q hA)
          ((restrictScalarsLocalizerMorphism f).localizedFunctor (Q hB) (Q hA)) :=
        e ▸ (restrictScalarsLocalizerMorphism f).liftingLocalizedFunctor (Q hB) (Q hA)
      CatCommSq.iso F (Q hB) (Q hA)
          ((restrictScalarsLocalizerMorphism f).localizedFunctor (Q hB) (Q hA)) =
        (Localization.Lifting.iso (Q hB) (quasiIsos hB) (F ⋙ Q hA)
          ((restrictScalarsLocalizerMorphism f).localizedFunctor (Q hB) (Q hA))).symm := by
    cases e
    rfl
  exact compatible _ (restrictScalarsLocalizerMorphism_functor f)

/-- The comparison of derived and ordinary restriction is natural in maps of DG modules. -/
@[reassoc (attr := simp)]
theorem restrictScalarsFactors_hom_naturality (f : DGAlgHom hA hB)
    {M N : DGRightModuleCat.{uR, uB, uM} hB} (g : M ⟶ N) :
    (restrictScalars f).map ((Q hB).map g) ≫ (restrictScalarsFactors f).hom.app N =
      (restrictScalarsFactors f).hom.app M ≫
        (Q hA).map ((DGRightModuleCat.restrictScalars f).map g) :=
  (restrictScalarsFactors f).hom.naturality g

/-- Successive derived restrictions lift successive ordinary restrictions. -/
noncomputable instance liftingRestrictScalarsComp (f : DGAlgHom hA hB) (g : DGAlgHom hB hC) :
    Localization.Lifting (Q.{uR, uC, uM} hC) (quasiIsos hC)
      ((DGRightModuleCat.restrictScalars g ⋙ DGRightModuleCat.restrictScalars f) ⋙ Q hA)
      (restrictScalars g ⋙ restrictScalars f) :=
  ⟨(CatCommSq.hComp' (inferInstance :
      CatCommSq (DGRightModuleCat.restrictScalars g) (Q hC) (Q hB) (restrictScalars g))
    inferInstance).iso.symm⟩

/-- Derived restriction along the identity algebra map is naturally isomorphic to the identity. -/
noncomputable def restrictScalarsId :
    restrictScalars.{uR, uA, uA, uM} (DGAlgHom.id hA) ≅ 𝟭 (DerivedCategory hA) :=
  Localization.liftNatIso (Q hA) (quasiIsos hA) _ _ _ _
    (isoWhiskerRight DGRightModuleCat.restrictScalarsId (Q hA) ≪≫ Functor.leftUnitor (Q hA))

/-- On a DG module, derived restriction along the identity is identified with the module through
ordinary restriction along the identity. -/
@[simp, reassoc]
theorem restrictScalarsId_hom_app_Q (M : DGRightModuleCat.{uR, uA, uM} hA) :
    restrictScalarsId.hom.app ((Q hA).obj M) =
      (restrictScalarsFactors (DGAlgHom.id hA)).hom.app M ≫
        (Q hA).map (DGRightModuleCat.restrictScalarsId.hom.app M) := by
  simp [restrictScalarsId]

/-- The inverse comparison for derived restriction along the identity on a DG module. -/
@[simp, reassoc]
theorem restrictScalarsId_inv_app_Q (M : DGRightModuleCat.{uR, uA, uM} hA) :
    restrictScalarsId.inv.app ((Q hA).obj M) =
      (Q hA).map (DGRightModuleCat.restrictScalarsId.inv.app M) ≫
        (restrictScalarsFactors (DGAlgHom.id hA)).inv.app M := by
  simp [restrictScalarsId]

/-- Derived restriction along a composite agrees with successive derived restrictions. -/
noncomputable def restrictScalarsComp (f : DGAlgHom hA hB) (g : DGAlgHom hB hC) :
    restrictScalars.{uR, uA, uC, uM} (g.comp f) ≅ restrictScalars g ⋙ restrictScalars f :=
  Localization.liftNatIso (Q hC) (quasiIsos hC) _ _ _ _
    (isoWhiskerRight (DGRightModuleCat.restrictScalarsComp f g) (Q hA))

/-- On a DG module, the composite comparison of derived restrictions is the ordinary one,
conjugated by the comparisons of derived and ordinary restriction. -/
@[simp, reassoc]
theorem restrictScalarsComp_hom_app_Q (f : DGAlgHom hA hB) (g : DGAlgHom hB hC)
    (M : DGRightModuleCat.{uR, uC, uM} hC) :
    (restrictScalarsComp f g).hom.app ((Q hC).obj M) =
      (restrictScalarsFactors (g.comp f)).hom.app M ≫
        (Q hA).map ((DGRightModuleCat.restrictScalarsComp f g).hom.app M) ≫
          (restrictScalarsFactors f).inv.app ((DGRightModuleCat.restrictScalars g).obj M) ≫
            (restrictScalars f).map ((restrictScalarsFactors g).inv.app M) := by
  simp [restrictScalarsComp, liftingRestrictScalarsComp]

/-- The inverse composite comparison of derived restrictions on a DG module. -/
@[simp, reassoc]
theorem restrictScalarsComp_inv_app_Q (f : DGAlgHom hA hB) (g : DGAlgHom hB hC)
    (M : DGRightModuleCat.{uR, uC, uM} hC) :
    (restrictScalarsComp f g).inv.app ((Q hC).obj M) =
      (restrictScalars f).map ((restrictScalarsFactors g).hom.app M) ≫
        (restrictScalarsFactors f).hom.app ((DGRightModuleCat.restrictScalars g).obj M) ≫
          (Q hA).map ((DGRightModuleCat.restrictScalarsComp f g).inv.app M) ≫
            (restrictScalarsFactors (g.comp f)).inv.app M := by
  simp [restrictScalarsComp, liftingRestrictScalarsComp]

end DerivedCategory

end TauCeti.DGRightModuleCat
