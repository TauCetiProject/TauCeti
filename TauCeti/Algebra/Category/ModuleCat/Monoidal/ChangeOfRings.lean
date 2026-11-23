/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Adjunction
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
public import TauCeti.CategoryTheory.Monoidal.Braided.Adjunction
import Mathlib.CategoryTheory.Adjunction.FullyFaithful

/-!
# Change of rings and tensor products of modules

Extension and restriction of scalars along a morphism of commutative rings are compatible with the
symmetric braiding on module categories.

For a morphism `f : A →+* P` and a `P`-module `M`, tensoring an extension of scalars with `M`
over `P` is tensoring with `M` over `A`: `M ⊗[P] (P ⊗[A] X) ≅ M ⊗[A] X`, naturally in the
`A`-module `X` (`ModuleCat.extendScalarsCompTensorLeftIso`). This computes `Tor` over `A` by a
projective resolution over `P` after a flat extension of scalars. Specializing to
`M = 𝟙_ (ModuleCat P)` identifies extension followed by restriction of scalars with tensoring by
`P` over `A` (`ModuleCat.extendScalarsCompRestrictScalarsIso`). When restriction of scalars along
`f` is full, the counit `P ⊗[A] M₂ ⟶ M₂` is an isomorphism, so restriction of scalars preserves
binary tensor products (`ModuleCat.isIso_laxMonoidal_μ_restrictScalars`).
-/

public section

open CategoryTheory MonoidalCategory

namespace TauCeti.ModuleCat

universe u

noncomputable section

variable {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)

/-- Restriction of scalars between module categories preserves the symmetric braiding. -/
instance restrictScalarsLaxBraided : (_root_.ModuleCat.restrictScalars f).LaxBraided where
  braided _ _ := _root_.ModuleCat.MonoidalCategory.tensor_ext fun _ _ ↦ rfl

/-- Extension of scalars between module categories preserves the symmetric braiding. -/
instance extendScalarsBraided : (_root_.ModuleCat.extendScalars f).Braided :=
  (_root_.ModuleCat.extendRestrictScalarsAdj f).leftAdjointBraided

end

end TauCeti.ModuleCat

namespace ModuleCat

open scoped TensorProduct ChangeOfRings

universe u

variable {A P : Type u} [CommRing A] [CommRing P] (f : A →+* P)

/-- The `A`-linear equivalence `M ⊗[P] (P ⊗[A] X) ≃ M ⊗[A] X`, `m ⊗ (s ⊗ x) ↦ (s • m) ⊗ x`,
where `A` acts through `f`. -/
private noncomputable def tensorExtendScalarsLinearEquiv (M : ModuleCat.{u} P)
    (X : ModuleCat.{u} A) :
    (restrictScalars f).obj (M ⊗ (extendScalars f).obj X) ≃ₗ[A]
      ((restrictScalars f).obj M ⊗ X : ModuleCat A) :=
  letI := f.toAlgebra
  letI : Module A M := Module.compHom M f
  haveI : IsScalarTower A P M := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  (TensorProduct.AlgebraTensorModule.cancelBaseChange A P P M X).restrictScalars A

/-- **Projection formula for extension of scalars.** For `f : A →+* P` and a `P`-module `M`,
`M ⊗[P] (P ⊗[A] X) ≅ M ⊗[A] X` as `A`-modules, naturally in the `A`-module `X`; it sends
`m ⊗ (s ⊗ x)` to `(s • m) ⊗ x`. -/
noncomputable def extendScalarsCompTensorLeftIso (M : ModuleCat.{u} P) :
    extendScalars.{u, u, u} f ⋙ tensorLeft M ⋙ restrictScalars.{u} f ≅
      tensorLeft ((restrictScalars f).obj M) :=
  (NatIso.ofComponents (fun X ↦ (tensorExtendScalarsLinearEquiv f M X).toModuleIso.symm)
    fun _ ↦ by apply MonoidalCategory.tensor_ext; intros; rfl).symm

/-- The forward map of `extendScalarsCompTensorLeftIso` sends `m ⊗ (s ⊗ x)` to `(s • m) ⊗ x`. -/
@[simp]
theorem extendScalarsCompTensorLeftIso_hom_app_tmul (M : ModuleCat.{u} P) (X : ModuleCat.{u} A)
    (m : M) (s : P) (x : X) :
    (Hom.hom : ((restrictScalars f).obj (M ⊗ (extendScalars f).obj X) ⟶
        (restrictScalars f).obj M ⊗ X) → _) ((extendScalarsCompTensorLeftIso f M).hom.app X)
        (TensorProduct.tmul P (M := M) (N := (extendScalars f).obj X) m (s ⊗ₜ[A, f] x)) =
      TensorProduct.tmul A (M := (restrictScalars f).obj M) (N := X) (s • m) x :=
  (rfl)

/-- The inverse of `extendScalarsCompTensorLeftIso` sends `m ⊗ x` to `m ⊗ (1 ⊗ x)`. -/
@[simp]
theorem extendScalarsCompTensorLeftIso_inv_app_tmul (M : ModuleCat.{u} P) (X : ModuleCat.{u} A)
    (m : (restrictScalars f).obj M) (x : X) :
    (Hom.hom : ((restrictScalars f).obj M ⊗ X ⟶
        (restrictScalars f).obj (M ⊗ (extendScalars f).obj X)) → _)
        ((extendScalarsCompTensorLeftIso f M).inv.app X)
        (TensorProduct.tmul A (M := (restrictScalars f).obj M) (N := X) m x) =
      TensorProduct.tmul P (M := M) (N := (extendScalars f).obj X) m ((1 : P) ⊗ₜ[A, f] x) :=
  (rfl)

/-- **Extension followed by restriction of scalars is tensoring with the target ring.** For
`f : A →+* P`, `extendScalars f ⋙ restrictScalars f` is naturally isomorphic to left tensoring
with `(restrictScalars f).obj (𝟙_ (ModuleCat P))`, sending `s ⊗ x` to `s ⊗ x`. -/
noncomputable def extendScalarsCompRestrictScalarsIso :
    extendScalars.{u, u, u} f ⋙ restrictScalars.{u} f ≅
      tensorLeft ((restrictScalars f).obj (𝟙_ (ModuleCat.{u} P))) :=
  Functor.isoWhiskerLeft (extendScalars f)
    ((Functor.leftUnitor (restrictScalars f)).symm ≪≫
      Functor.isoWhiskerRight (MonoidalCategory.leftUnitorNatIso (ModuleCat.{u} P)).symm
        (restrictScalars f)) ≪≫
    extendScalarsCompTensorLeftIso f (𝟙_ (ModuleCat.{u} P))

-- The carrier of `(restrictScalars f).obj (𝟙_ (ModuleCat.{u} P))` is definitionally `P`
-- (`𝟙_ (ModuleCat.{u} P)` is `ModuleCat.of P P` and `restrictScalars` leaves the carrier
-- unchanged), with `P`-action given by multiplication on `P`.
private lemma smul_one_unit (s : P) :
    (s • (1 : P) : (restrictScalars f).obj (𝟙_ (ModuleCat.{u} P))) =
      (s : (restrictScalars f).obj (𝟙_ (ModuleCat.{u} P))) :=
  mul_one s

/-- The forward map of `extendScalarsCompRestrictScalarsIso` sends `s ⊗ x` to `s ⊗ x`. -/
@[simp]
theorem extendScalarsCompRestrictScalarsIso_hom_app_tmul (X : ModuleCat.{u} A)
    (s : P) (x : X) :
    (Hom.hom : ((restrictScalars f).obj ((extendScalars f).obj X) ⟶
        (restrictScalars f).obj (𝟙_ (ModuleCat.{u} P)) ⊗ X) → _)
        ((extendScalarsCompRestrictScalarsIso f).hom.app X) (s ⊗ₜ[A, f] x) =
      TensorProduct.tmul A (M := (restrictScalars f).obj (𝟙_ (ModuleCat.{u} P))) (N := X)
        (s : (restrictScalars f).obj (𝟙_ (ModuleCat.{u} P))) x := by
  have hhom : ((extendScalarsCompRestrictScalarsIso f).hom.app X :
      (restrictScalars f).obj ((extendScalars f).obj X) ⟶
        (restrictScalars f).obj (𝟙_ (ModuleCat.{u} P)) ⊗ X) =
      (restrictScalars f).map (λ_ ((extendScalars f).obj X)).inv ≫
        (extendScalarsCompTensorLeftIso f (𝟙_ (ModuleCat.{u} P))).hom.app X := by
    dsimp [extendScalarsCompRestrictScalarsIso]
    rw [Category.id_comp, MonoidalCategory.leftUnitorNatIso_inv_app]
  calc
    (Hom.hom : ((restrictScalars f).obj ((extendScalars f).obj X) ⟶
        (restrictScalars f).obj (𝟙_ (ModuleCat.{u} P)) ⊗ X) → _)
        ((extendScalarsCompRestrictScalarsIso f).hom.app X) (s ⊗ₜ[A, f] x)
      = ((extendScalarsCompTensorLeftIso f (𝟙_ (ModuleCat.{u} P))).hom.app X)
          (((restrictScalars f).map (λ_ ((extendScalars f).obj X)).inv) (s ⊗ₜ[A, f] x)) :=
        (congrArg (fun g ↦ g.hom (s ⊗ₜ[A, f] x)) hhom).trans (ModuleCat.comp_apply _ _ _)
    _ = ((extendScalarsCompTensorLeftIso f (𝟙_ (ModuleCat.{u} P))).hom.app X)
          (TensorProduct.tmul P (M := 𝟙_ (ModuleCat.{u} P)) (N := (extendScalars f).obj X)
            (1 : P) (s ⊗ₜ[A, f] x)) :=
        congrArg ((extendScalarsCompTensorLeftIso f (𝟙_ (ModuleCat.{u} P))).hom.app X)
          ((restrictScalars.map_apply f (λ_ ((extendScalars f).obj X)).inv (s ⊗ₜ[A, f] x)).trans
            (MonoidalCategory.leftUnitor_inv_apply (M := (extendScalars f).obj X) (s ⊗ₜ[A, f] x)))
    _ = TensorProduct.tmul A (M := (restrictScalars f).obj (𝟙_ (ModuleCat.{u} P))) (N := X)
          (s • (1 : P)) x :=
        extendScalarsCompTensorLeftIso_hom_app_tmul f (𝟙_ (ModuleCat.{u} P)) X (1 : P) s x
    _ = TensorProduct.tmul A (M := (restrictScalars f).obj (𝟙_ (ModuleCat.{u} P))) (N := X)
          (s : (restrictScalars f).obj (𝟙_ (ModuleCat.{u} P))) x := by
        rw [smul_one_unit]

/-- The inverse of `extendScalarsCompRestrictScalarsIso` sends `s ⊗ x` to `s ⊗ x`. -/
@[simp]
theorem extendScalarsCompRestrictScalarsIso_inv_app_tmul (X : ModuleCat.{u} A)
    (s : (restrictScalars f).obj (𝟙_ (ModuleCat.{u} P))) (x : X) :
    (Hom.hom : ((restrictScalars f).obj (𝟙_ (ModuleCat.{u} P)) ⊗ X ⟶
        (restrictScalars f).obj ((extendScalars f).obj X)) → _)
        ((extendScalarsCompRestrictScalarsIso f).inv.app X)
        (TensorProduct.tmul A (M := (restrictScalars f).obj (𝟙_ (ModuleCat.{u} P))) (N := X) s x) =
      (s : P) ⊗ₜ[A, f] x := by
  have hinv : ((extendScalarsCompRestrictScalarsIso f).inv.app X :
      (restrictScalars f).obj (𝟙_ (ModuleCat.{u} P)) ⊗ X ⟶
        (restrictScalars f).obj ((extendScalars f).obj X)) =
      (extendScalarsCompTensorLeftIso f (𝟙_ (ModuleCat.{u} P))).inv.app X ≫
        (restrictScalars f).map (λ_ ((extendScalars f).obj X)).hom := by
    dsimp [extendScalarsCompRestrictScalarsIso]
    rw [Category.comp_id, MonoidalCategory.leftUnitorNatIso_hom_app]
  -- View `s` in the definitionally equal carrier `P` of
  -- `(restrictScalars f).obj (𝟙_ (ModuleCat P))`.
  let s' : P := s
  have hstep₁ :
      ((extendScalarsCompRestrictScalarsIso f).inv.app X :
          (restrictScalars f).obj (𝟙_ (ModuleCat.{u} P)) ⊗ X ⟶
            (restrictScalars f).obj ((extendScalars f).obj X))
        (TensorProduct.tmul A (M := (restrictScalars f).obj (𝟙_ (ModuleCat.{u} P))) (N := X) s x) =
      ((restrictScalars f).map (λ_ ((extendScalars f).obj X)).hom)
        (TensorProduct.tmul P (M := 𝟙_ (ModuleCat.{u} P)) (N := (extendScalars f).obj X)
          s ((1 : P) ⊗ₜ[A, f] x)) :=
    (congrArg (fun g ↦ g.hom (TensorProduct.tmul A
      (M := (restrictScalars f).obj (𝟙_ (ModuleCat.{u} P))) (N := X) s x)) hinv).trans
      ((ModuleCat.comp_apply _ _ _).trans
        (congrArg ((restrictScalars f).map (λ_ ((extendScalars f).obj X)).hom)
          (extendScalarsCompTensorLeftIso_inv_app_tmul f (𝟙_ (ModuleCat.{u} P)) X s x)))
  have hstep₂ :
      ((restrictScalars f).map (λ_ ((extendScalars f).obj X)).hom)
        (TensorProduct.tmul P (M := 𝟙_ (ModuleCat.{u} P)) (N := (extendScalars f).obj X)
          s ((1 : P) ⊗ₜ[A, f] x)) =
      s' ⊗ₜ[A, f] x :=
    (restrictScalars.map_apply f (λ_ ((extendScalars f).obj X)).hom _).trans
      ((MonoidalCategory.leftUnitor_hom_apply (M := (extendScalars f).obj X) s'
          ((1 : P) ⊗ₜ[A, f] x)).trans
        ((ExtendScalars.smul_tmul f s' 1 x).trans (by rw [mul_one])))
  exact hstep₁.trans hstep₂

/-- When restriction of scalars along `f : A →+* P` is full, for instance when `f` is surjective or
a localization, it preserves binary tensor products: the lax monoidal comparison
`M₁ ⊗[A] M₂ ⟶ M₁ ⊗[P] M₂` is an isomorphism. -/
instance isIso_laxMonoidal_μ_restrictScalars [(restrictScalars.{u} f).Full]
    (M₁ M₂ : ModuleCat.{u} P) :
    IsIso (Functor.LaxMonoidal.μ (restrictScalars.{u} f) M₁ M₂) := by
  have h : Functor.LaxMonoidal.μ (restrictScalars.{u} f) M₁ M₂ =
      (extendScalarsCompTensorLeftIso f M₁).inv.app ((restrictScalars f).obj M₂) ≫
        (restrictScalars.{u} f).map (M₁ ◁ (extendRestrictScalarsAdj f).counit.app M₂) := by
    refine MonoidalCategory.tensor_ext fun m₁ m₂ ↦ ?_
    simp only [hom_comp, LinearMap.comp_apply]
    -- `tensor_ext` exposes `ModuleCat` tensor products; `erw` evaluates `restrictScalars.map` and
    -- the counit on `1 ⊗ₜ m₂`, after which both sides reduce definitionally to `m₁ ⊗ₜ m₂`.
    erw [restrictScalars.map_apply, MonoidalCategory.whiskerLeft_apply,
      extendRestrictScalarsAdj_counit_app_apply_one_tmul]
    rfl
  rw [h]
  infer_instance

end ModuleCat
