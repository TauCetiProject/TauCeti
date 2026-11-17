/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Jie Xu, Shitan Xu
-/
module

public import TauCeti.AlgebraicGeometry.VectorBundle.FiniteLocallyFree
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import TauCeti.AlgebraicGeometry.Morphisms.Finite.Basic
import TauCeti.AlgebraicGeometry.VectorBundle.Affine.Basic
import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.Pushforward.Finite

/-!
# Finite flat pushforward of vector bundles

A finite flat morphism locally of finite presentation sends finite locally free sheaves to
finite locally free sheaves, over arbitrary base schemes. On affine opens, this is restriction
of scalars through a finite projective algebra. The source and target need not be Noetherian,
and the ranks need not be constant.

The resulting functor on finite locally free sheaves gives the vector bundles whose determinants
enter norm constructions for line bundles along finite locally free families of divisors.

## References

* The Stacks Project, Tags 00NX (finite projective modules) and 02K9 (finite locally free maps).
-/

public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}}

/-- Finite flat morphisms locally of finite presentation preserve finite local freeness of
module sheaves, without any Noetherian hypothesis or constant-rank assumption. -/
theorem isFiniteLocallyFree_pushforward (f : X ⟶ Y) [IsFinite f] [Flat f]
    [LocallyOfFinitePresentation f] (M : X.Modules) (hM : isFiniteLocallyFree X M) :
    isFiniteLocallyFree Y ((pushforward f).obj M) := by
  have : M.IsFinitePresentation := hM.2
  have : M.IsQuasicoherent := inferInstance
  have : ((pushforward f).obj M).IsQuasicoherent := isQuasicoherent_pushforward M f
  refine isFiniteLocallyFree_of_finite_projective_sections _
    (fun U : Y.affineOpens ↦ U) (fun U ↦ U.property)
    (iSup_affineOpens_eq_top Y) (fun U ↦ ?_)
  have hproj := (M.finite_projective_sections hM (U.property.preimage f)).2
  let P := (ModuleCat.restrictScalars (f.app U).hom).obj
    (ModuleCat.of Γ(X, f ⁻¹ᵁ U) Γ(M, f ⁻¹ᵁ U))
  have hP : Module.Projective Γ(Y, U) P :=
    (f.app U).hom.projective_restrictScalars_of_projective
      (f.projective_app U) (ModuleCat.of Γ(X, f ⁻¹ᵁ U) Γ(M, f ⁻¹ᵁ U))
  let e : Γ((pushforward f).obj M, U) ≃ₗ[Γ(Y, U)] P :=
    { AddEquiv.refl _ with
      map_smul' := fun r x ↦ TauCeti.AlgebraicGeometry.pushforward_obj_smul f M r x }
  exact ⟨M.finite_sections_pushforward f U U.property,
    Module.Projective.of_equiv e.symm⟩

end AlgebraicGeometry.Scheme.Modules

namespace TauCeti.AlgebraicGeometry.FiniteLocallyFreeSheaf

open _root_.AlgebraicGeometry

variable {X Y Z : Scheme.{u}}

/-- Pushforward of finite locally free sheaves along a finite flat morphism locally of finite
presentation, with the usual pushforward on morphisms of module sheaves. -/
noncomputable def pushforward (f : X ⟶ Y) [IsFinite f] [Flat f]
    [LocallyOfFinitePresentation f] :
    FiniteLocallyFreeSheaf X ⥤ FiniteLocallyFreeSheaf Y :=
  ObjectProperty.lift _ ((Scheme.Modules.isFiniteLocallyFree X).ι ⋙ Scheme.Modules.pushforward f)
    (fun M ↦ Scheme.Modules.isFiniteLocallyFree_pushforward f M.obj M.property)

/-- The underlying module sheaf of finite-flat pushforward is the usual pushforward. -/
@[simp]
lemma pushforward_obj_obj (f : X ⟶ Y) [IsFinite f] [Flat f]
    [LocallyOfFinitePresentation f] (E : FiniteLocallyFreeSheaf X) :
    ((pushforward f).obj E).obj = (Scheme.Modules.pushforward f).obj E.obj :=
  (rfl)

/-- On morphisms, finite-flat pushforward agrees with pushforward of module sheaves. -/
@[simp]
lemma pushforward_map_hom (f : X ⟶ Y) [IsFinite f] [Flat f]
    [LocallyOfFinitePresentation f] {E F : FiniteLocallyFreeSheaf X} (φ : E ⟶ F) :
    ((pushforward f).map φ).hom =
      eqToHom (pushforward_obj_obj f E) ≫ (Scheme.Modules.pushforward f).map φ.hom ≫
        eqToHom (pushforward_obj_obj f F).symm := by
  cases pushforward_obj_obj f E
  cases pushforward_obj_obj f F
  unfold pushforward
  simp

/-- The inclusion comparison for finite-flat pushforward. -/
noncomputable def pushforwardCompιIso (f : X ⟶ Y) [IsFinite f] [Flat f]
    [LocallyOfFinitePresentation f] :
    pushforward f ⋙ (Scheme.Modules.isFiniteLocallyFree Y).ι ≅
      (Scheme.Modules.isFiniteLocallyFree X).ι ⋙ Scheme.Modules.pushforward f :=
  ObjectProperty.liftCompιIso _ _ _

/-- The inclusion comparison is the canonical identification of the underlying objects. -/
@[simp]
lemma pushforwardCompιIso_hom_app (f : X ⟶ Y) [IsFinite f] [Flat f]
    [LocallyOfFinitePresentation f] (E : FiniteLocallyFreeSheaf X) :
    (pushforwardCompιIso f).hom.app E = eqToHom (pushforward_obj_obj f E) :=
  by rfl

/-- The inverse inclusion comparison is the inverse identification of the underlying objects. -/
@[simp]
lemma pushforwardCompιIso_inv_app (f : X ⟶ Y) [IsFinite f] [Flat f]
    [LocallyOfFinitePresentation f] (E : FiniteLocallyFreeSheaf X) :
    (pushforwardCompιIso f).inv.app E = eqToHom (pushforward_obj_obj f E).symm :=
  by rfl

instance (f : X ⟶ Y) [IsFinite f] [Flat f] [LocallyOfFinitePresentation f] :
    (pushforward f).Additive := by
  unfold pushforward
  infer_instance

/-- Pushforward along the identity is the identity on finite locally free sheaves. -/
noncomputable def pushforwardId (X : Scheme.{u}) : pushforward (𝟙 X) ≅ 𝟭 _ :=
  NatIso.ofComponents (fun E ↦ ObjectProperty.isoMk _
    (eqToIso (pushforward_obj_obj (𝟙 X) E) ≪≫
      (Scheme.Modules.pushforwardId X).app E.obj)) (fun φ ↦ by
        apply ObjectProperty.hom_ext
        simp [pushforward_map_hom])

/-- The identity comparison agrees with that of module sheaves. -/
@[simp]
lemma pushforwardId_hom_app_hom (X : Scheme.{u}) (E : FiniteLocallyFreeSheaf X) :
    ((pushforwardId X).hom.app E).hom =
      eqToHom (pushforward_obj_obj (𝟙 X) E) ≫
        (Scheme.Modules.pushforwardId X).hom.app E.obj := by
  rfl

/-- The inverse identity comparison agrees with that of module sheaves. -/
@[simp]
lemma pushforwardId_inv_app_hom (X : Scheme.{u}) (E : FiniteLocallyFreeSheaf X) :
    ((pushforwardId X).inv.app E).hom =
      (Scheme.Modules.pushforwardId X).inv.app E.obj ≫
        eqToHom (pushforward_obj_obj (𝟙 X) E).symm :=
  by rfl

/-- Pushforward along a composite is the composite of the pushforwards. -/
noncomputable def pushforwardComp (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsFinite f] [Flat f] [LocallyOfFinitePresentation f]
    [IsFinite g] [Flat g] [LocallyOfFinitePresentation g] :
    pushforward f ⋙ pushforward g ≅ pushforward (f ≫ g) :=
  NatIso.ofComponents (fun E ↦ ObjectProperty.isoMk _
    (eqToIso (pushforward_obj_obj g ((pushforward f).obj E)) ≪≫
      (Scheme.Modules.pushforward g).mapIso (eqToIso (pushforward_obj_obj f E)) ≪≫
      (Scheme.Modules.pushforwardComp f g).app E.obj ≪≫
      eqToIso (pushforward_obj_obj (f ≫ g) E).symm)) (fun φ ↦ by
        apply ObjectProperty.hom_ext
        -- The underlying composition comparison and object identifications are identities
        -- on sections, so naturality is the same equality on both sides.
        ext U x
        rfl)

/-- The composition comparison agrees with that of module sheaves. -/
@[simp]
lemma pushforwardComp_hom_app_hom (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsFinite f] [Flat f] [LocallyOfFinitePresentation f]
    [IsFinite g] [Flat g] [LocallyOfFinitePresentation g] (E : FiniteLocallyFreeSheaf X) :
    ((pushforwardComp f g).hom.app E).hom =
      eqToHom (pushforward_obj_obj g ((pushforward f).obj E)) ≫
        (Scheme.Modules.pushforward g).map (eqToHom (pushforward_obj_obj f E)) ≫
        (Scheme.Modules.pushforwardComp f g).hom.app E.obj ≫
        eqToHom (pushforward_obj_obj (f ≫ g) E).symm := by
  rfl

/-- The inverse composition comparison agrees with that of module sheaves. -/
@[simp]
lemma pushforwardComp_inv_app_hom (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsFinite f] [Flat f] [LocallyOfFinitePresentation f]
    [IsFinite g] [Flat g] [LocallyOfFinitePresentation g] (E : FiniteLocallyFreeSheaf X) :
    ((pushforwardComp f g).inv.app E).hom =
      eqToHom (pushforward_obj_obj (f ≫ g) E) ≫
        (Scheme.Modules.pushforwardComp f g).inv.app E.obj ≫
        (Scheme.Modules.pushforward g).map (eqToHom (pushforward_obj_obj f E).symm) ≫
        eqToHom (pushforward_obj_obj g ((pushforward f).obj E)).symm :=
  by rfl

/-- Pullback of finite locally free sheaves commutes with inclusion into module sheaves. -/
private noncomputable def pullbackCompιIso (f : X ⟶ Y) :
    pullback f ⋙ (Scheme.Modules.isFiniteLocallyFree X).ι ≅
      (Scheme.Modules.isFiniteLocallyFree Y).ι ⋙ Scheme.Modules.pullback f :=
  NatIso.ofComponents (fun E ↦ eqToIso (pullback_obj_obj f E)) (fun φ ↦ by
    simp [pullback_map_hom])

/-- Pullback and finite-flat pushforward remain adjoint after restricting to finite locally free
sheaves. -/
noncomputable def pullbackPushforwardAdjunction (f : X ⟶ Y) [IsFinite f] [Flat f]
    [LocallyOfFinitePresentation f] : pullback f ⊣ pushforward f :=
  (Scheme.Modules.pullbackPushforwardAdjunction f).restrictFullyFaithful
    (Scheme.Modules.isFiniteLocallyFree Y).fullyFaithfulι
    (Scheme.Modules.isFiniteLocallyFree X).fullyFaithfulι
    (pullbackCompιIso f).symm (pushforwardCompιIso f).symm

/-- The unit is the usual module-sheaf unit, with the underlying objects identified. -/
@[simp]
lemma pullbackPushforwardAdjunction_unit_app_hom (f : X ⟶ Y) [IsFinite f] [Flat f]
    [LocallyOfFinitePresentation f] (E : FiniteLocallyFreeSheaf Y) :
    ((pullbackPushforwardAdjunction f).unit.app E).hom =
      (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app E.obj ≫
        (Scheme.Modules.pushforward f).map (eqToHom (pullback_obj_obj f E).symm) ≫
        eqToHom (pushforward_obj_obj f ((pullback f).obj E)).symm := by
  dsimp only [pullbackPushforwardAdjunction]
  exact Adjunction.map_restrictFullyFaithful_unit_app
    (Scheme.Modules.pullbackPushforwardAdjunction f)
    (Scheme.Modules.isFiniteLocallyFree Y).fullyFaithfulι
    (Scheme.Modules.isFiniteLocallyFree X).fullyFaithfulι
    (pullbackCompιIso f).symm (pushforwardCompιIso f).symm E

/-- The counit is the usual module-sheaf counit, with the underlying objects identified. -/
@[simp]
lemma pullbackPushforwardAdjunction_counit_app_hom (f : X ⟶ Y) [IsFinite f] [Flat f]
    [LocallyOfFinitePresentation f] (E : FiniteLocallyFreeSheaf X) :
    ((pullbackPushforwardAdjunction f).counit.app E).hom =
      eqToHom (pullback_obj_obj f ((pushforward f).obj E)) ≫
        (Scheme.Modules.pullback f).map (eqToHom (pushforward_obj_obj f E)) ≫
        (Scheme.Modules.pullbackPushforwardAdjunction f).counit.app E.obj := by
  dsimp only [pullbackPushforwardAdjunction]
  exact Adjunction.map_restrictFullyFaithful_counit_app
    (Scheme.Modules.pullbackPushforwardAdjunction f)
    (Scheme.Modules.isFiniteLocallyFree Y).fullyFaithfulι
    (Scheme.Modules.isFiniteLocallyFree X).fullyFaithfulι
    (pullbackCompιIso f).symm (pushforwardCompιIso f).symm E

end TauCeti.AlgebraicGeometry.FiniteLocallyFreeSheaf
