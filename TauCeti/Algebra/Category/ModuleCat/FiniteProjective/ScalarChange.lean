/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.BalancedExtension
public import TauCeti.Algebra.Category.ModuleCat.CartanMap.Basic
public import TauCeti.Algebra.Category.ModuleCat.RestrictScalars
public import TauCeti.CategoryTheory.GrothendieckGroup.Split

/-!
# Scalar change on finitely generated projective modules

Let `f : R →+* S` be a ring homomorphism of possibly noncommutative rings. This file records how
the two scalar-change functors act on the object property `TauCeti.finiteProjectiveModules`
whose split Grothendieck group is the projective `K₀`.

* Extension of scalars `P ↦ S ⊗_R P` (`TauCeti.BalancedExtension.functor f`) sends finitely
  generated projective `R`-modules to finitely generated projective `S`-modules, for every `f`.
  This is what lets it induce a homomorphism `K₀(R) → K₀(S)`.
* Restriction of scalars (`ModuleCat.restrictScalars f`) sends finitely generated projective
  `S`-modules to finitely generated projective `R`-modules exactly when `S` itself is a finitely
  generated projective `R`-module through `f`. Necessity is seen on the regular module `S`; for
  instance along `ℤ → ℚ` the finitely generated projective `ℚ`-module `ℚ` restricts to a
  `ℤ`-module that is not finitely generated.

The module-level statements are the `Module.Finite` and `Module.Projective` instances on
`TauCeti.BalancedExtension f P`, and `RingHom.isFG_restrictScalars_of_finite` together with
`RingHom.projective_restrictScalars_of_projective`.

## Main definitions

* `RingHom.finiteProjectiveModulesExtendScalars`: extension of scalars as an additive functor
  between the categories of finitely generated projective modules.
* `RingHom.finiteProjectiveModulesExtendScalarsCompιIso`: followed by the inclusion into all
  modules, it is extension of scalars `TauCeti.BalancedExtension.functor` on all modules.
* `RingHom.finiteProjectiveModulesExtendScalarsCompIso`: for a commuting square
  `g₁ ∘ f₁ = g₂ ∘ f₂` of ring homomorphisms, the natural isomorphism between extending along `f₁`
  then `g₁` and along `f₂` then `g₂`, through extension along the common composite.

## Main results

* `TauCeti.SplitK0.of_extendScalars_obj`: the split `K₀` class of an extended module agrees
  with the class of any module linearly isomorphic to its balanced extension.
* `TauCeti.BalancedExtension.finiteProjectiveModules_le_inverseImage_functor`: extension of
  scalars preserves finitely generated projective modules.
* `RingHom.finiteProjectiveModules_le_inverseImage_restrictScalars_iff`: restriction of scalars
  along `f` preserves finitely generated projective modules if and only if `S` is a finitely
  generated projective `R`-module through `f`.

## References

* C. A. Weibel, *The K-book*, Chapter II, §2.8 and Example 2.8.1, pp. 12–13.
-/

public section

open CategoryTheory

universe u

variable {R S : Type u} [Ring R] [Ring S] (f : R →+* S)

namespace TauCeti.BalancedExtension

/-- **Extension of scalars preserves finitely generated projective modules.** Along any ring
homomorphism `f : R →+* S`, the extension of scalars `S ⊗_R P` of a finitely generated projective
`R`-module `P` is a finitely generated projective `S`-module. -/
theorem finiteProjectiveModules_le_inverseImage_functor :
    finiteProjectiveModules R ≤ (finiteProjectiveModules S).inverseImage (functor f) := by
  intro P hP
  obtain ⟨_, _⟩ := finiteProjectiveModules_iff.mp hP
  exact finiteProjectiveModules_iff.mpr
    ⟨inferInstanceAs (Module.Finite S (BalancedExtension f P)),
      inferInstanceAs (Module.Projective S (BalancedExtension f P))⟩

end TauCeti.BalancedExtension

namespace RingHom

open TauCeti

/-- **Extension of scalars on finitely generated projective modules.** A ring homomorphism
`f : R →+* S` induces a functor from the finitely generated projective `R`-modules to the
finitely generated projective `S`-modules, sending `P` to `S ⊗_R P`. -/
noncomputable def finiteProjectiveModulesExtendScalars :
    (finiteProjectiveModules R).FullSubcategory ⥤ (finiteProjectiveModules S).FullSubcategory :=
  (finiteProjectiveModules S).lift
    ((finiteProjectiveModules R).ι ⋙ BalancedExtension.functor.{u, u, u} f)
    fun P ↦ BalancedExtension.finiteProjectiveModules_le_inverseImage_functor f P.obj P.property

instance : f.finiteProjectiveModulesExtendScalars.Additive := by
  -- Instance search does not find Mathlib's additivity instance for `ObjectProperty.lift` here,
  -- so additivity is read off the composite with the faithful inclusion, which is the additive
  -- functor `ι ⋙ BalancedExtension.functor f`.
  have : (f.finiteProjectiveModulesExtendScalars ⋙ (finiteProjectiveModules S).ι).Additive :=
    inferInstanceAs ((finiteProjectiveModules R).ι ⋙ BalancedExtension.functor.{u, u, u} f).Additive
  exact Functor.additive_of_comp_faithful _ (finiteProjectiveModules S).ι

@[simp]
theorem finiteProjectiveModulesExtendScalars_obj_obj
    (P : (finiteProjectiveModules R).FullSubcategory) :
    (f.finiteProjectiveModulesExtendScalars.obj P).obj =
      ModuleCat.of S (BalancedExtension f P.obj) :=
  (rfl)

@[simp]
theorem finiteProjectiveModulesExtendScalars_map_hom
    {P Q : (finiteProjectiveModules R).FullSubcategory} (g : P ⟶ Q) :
    (f.finiteProjectiveModulesExtendScalars.map g).hom =
      eqToHom (f.finiteProjectiveModulesExtendScalars_obj_obj P) ≫
        ModuleCat.ofHom (BalancedExtension.map f g.hom.hom) ≫
          eqToHom (f.finiteProjectiveModulesExtendScalars_obj_obj Q).symm :=
  (rfl)

/-- Extension of scalars on finitely generated projective modules, followed by the inclusion into
all modules, is the inclusion followed by extension of scalars
`TauCeti.BalancedExtension.functor f` on all modules. Its components are the identifications
`RingHom.finiteProjectiveModulesExtendScalars_obj_obj`. -/
noncomputable def finiteProjectiveModulesExtendScalarsCompιIso :
    f.finiteProjectiveModulesExtendScalars ⋙ (finiteProjectiveModules S).ι ≅
      (finiteProjectiveModules R).ι ⋙ BalancedExtension.functor.{u, u, u} f :=
  ObjectProperty.liftCompιIso _ _ _

@[simp]
theorem finiteProjectiveModulesExtendScalarsCompιIso_hom_app
    (P : (finiteProjectiveModules R).FullSubcategory) :
    f.finiteProjectiveModulesExtendScalarsCompιIso.hom.app P =
      eqToHom ((f.finiteProjectiveModulesExtendScalars_obj_obj P).trans
        (BalancedExtension.functor_obj f P.obj).symm) :=
  (rfl)

@[simp]
theorem finiteProjectiveModulesExtendScalarsCompιIso_inv_app
    (P : (finiteProjectiveModules R).FullSubcategory) :
    f.finiteProjectiveModulesExtendScalarsCompιIso.inv.app P =
      eqToHom ((f.finiteProjectiveModulesExtendScalars_obj_obj P).trans
        (BalancedExtension.functor_obj f P.obj).symm).symm :=
  (rfl)

section Square

variable {A B C D : Type u} [Ring A] [Ring B] [Ring C] [Ring D] (f₁ : A →+* B) (g₁ : B →+* D)
  (f₂ : A →+* C) (g₂ : C →+* D) (h : g₁.comp f₁ = g₂.comp f₂)

/-- **Extension of scalars around a commuting square.** For ring homomorphisms with
`g₁ ∘ f₁ = g₂ ∘ f₂`, extending a finitely generated projective `A`-module along `f₁` and then
along `g₁` is naturally isomorphic to extending it along `f₂` and then along `g₂`: both are
extension along the common composite, through `TauCeti.BalancedExtension.cancelBaseChange`. The
component at `P` sends `t ⊗ (s ⊗ p)` to `(t * g₁ s) ⊗ (1 ⊗ p)`, in particular `1 ⊗ (1 ⊗ p)` to
`1 ⊗ (1 ⊗ p)` (`RingHom.finiteProjectiveModulesExtendScalarsCompIso_hom_app_hom`); for the
trivial square it is the identity (`RingHom.finiteProjectiveModulesExtendScalarsCompIso_refl`). -/
noncomputable def finiteProjectiveModulesExtendScalarsCompIso :
    f₁.finiteProjectiveModulesExtendScalars ⋙ g₁.finiteProjectiveModulesExtendScalars ≅
      f₂.finiteProjectiveModulesExtendScalars ⋙ g₂.finiteProjectiveModulesExtendScalars :=
  ((finiteProjectiveModules D).fullyFaithfulι.whiskeringRight _).preimageIso
    (Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ g₁.finiteProjectiveModulesExtendScalarsCompιIso ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight f₁.finiteProjectiveModulesExtendScalarsCompιIso _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ ((BalancedExtension.functorComp.{u, u} f₁ g₁).symm ≪≫
        BalancedExtension.functorCongr h ≪≫ BalancedExtension.functorComp f₂ g₂) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight f₂.finiteProjectiveModulesExtendScalarsCompιIso.symm _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ g₂.finiteProjectiveModulesExtendScalarsCompιIso.symm ≪≫
      (Functor.associator _ _ _).symm)

/-- The component of `RingHom.finiteProjectiveModulesExtendScalarsCompIso` at `P` is, on underlying
modules, `D ⊗_B (B ⊗_A P) ≃ D ⊗_A P ≃ D ⊗_C (C ⊗_A P)`, the composite of the inverse of
`TauCeti.BalancedExtension.functorComp f₁ g₁`, of `TauCeti.BalancedExtension.functorCongr h` and of
`TauCeti.BalancedExtension.functorComp f₂ g₂`: it sends `t ⊗ (s ⊗ p)` to `(t * g₁ s) ⊗ (1 ⊗ p)`. -/
theorem finiteProjectiveModulesExtendScalarsCompIso_hom_app_hom
    (P : (finiteProjectiveModules A).FullSubcategory) :
    ((finiteProjectiveModulesExtendScalarsCompIso f₁ g₁ f₂ g₂ h).hom.app P).hom =
      eqToHom (by
          simp only [Functor.comp_obj]
          rw [finiteProjectiveModulesExtendScalars_obj_obj,
            finiteProjectiveModulesExtendScalars_obj_obj]
          rfl) ≫
        (BalancedExtension.functorComp f₁ g₁).inv.app P.obj ≫
          (BalancedExtension.functorCongr h).hom.app P.obj ≫
            (BalancedExtension.functorComp f₂ g₂).hom.app P.obj ≫
              eqToHom (by
                simp only [Functor.comp_obj]
                rw [finiteProjectiveModulesExtendScalars_obj_obj,
                  finiteProjectiveModulesExtendScalars_obj_obj]
                rfl) := by
  -- Unfold the whiskered isomorphisms; the components of the inclusion isomorphisms are `eqToHom`.
  simp only [finiteProjectiveModulesExtendScalarsCompIso, Functor.FullyFaithful.preimageIso_hom,
    Functor.FullyFaithful.whiskeringRight_preimage_app, Functor.comp_obj, ObjectProperty.ι_obj,
    Functor.associator_hom_app, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
    finiteProjectiveModulesExtendScalarsCompιIso_hom_app, Functor.associator_inv_app,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app, Functor.isoWhiskerLeft_trans,
    Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    finiteProjectiveModulesExtendScalarsCompιIso_inv_app, Category.comp_id, Category.id_comp,
    Category.assoc, ObjectProperty.homMk_hom]
  rw [eqToHom_map, eqToHom_map]
  simp

/-- Extension of scalars around the trivial square `g ∘ f = g ∘ f` is the identity. -/
@[simp]
theorem finiteProjectiveModulesExtendScalarsCompIso_refl :
    finiteProjectiveModulesExtendScalarsCompIso f₁ g₁ f₁ g₁ rfl = Iso.refl _ := by
  refine Iso.ext (NatTrans.ext (funext fun P ↦ ObjectProperty.hom_ext _ ?_))
  simp [finiteProjectiveModulesExtendScalarsCompIso_hom_app_hom]

end Square

/-- **Restriction of scalars on finitely generated projective modules.** Restriction of scalars
along `f : R →+* S` sends finitely generated projective `S`-modules to finitely generated
projective `R`-modules if and only if `S` is a finitely generated projective `R`-module through
`f`. -/
theorem finiteProjectiveModules_le_inverseImage_restrictScalars_iff :
    finiteProjectiveModules S ≤
        (finiteProjectiveModules R).inverseImage (ModuleCat.restrictScalars f) ↔
      letI := f.toModule; Module.Finite R S ∧ Module.Projective R S := by
  refine ⟨fun h ↦ ?_, fun ⟨hfin, hproj⟩ M hM ↦ ?_⟩
  · -- Test the regular module `S`: its restriction of scalars is `S` with the `R`-module
    -- structure `f.toModule`, by definition of `ModuleCat.restrictScalars`.
    exact finiteProjectiveModules_iff.mp (h (ModuleCat.of S S)
      (finiteProjectiveModules_iff.mpr ⟨Module.Finite.self S, Module.Projective.of_free⟩))
  · obtain ⟨hMfin, _⟩ := finiteProjectiveModules_iff.mp hM
    exact finiteProjectiveModules_iff.mpr
      ⟨(ModuleCat.isFG_iff _).mp (f.isFG_restrictScalars_of_finite hfin
          ((ModuleCat.isFG_iff M).mpr hMfin)),
        f.projective_restrictScalars_of_projective hproj M⟩

end RingHom

namespace TauCeti.SplitK0

variable {f}

/-- The class of `S ⊗_R P` is the class of any module isomorphic to it. -/
theorem of_extendScalars_obj {P : (finiteProjectiveModules R).FullSubcategory}
    {Q : (finiteProjectiveModules S).FullSubcategory}
    (θ : BalancedExtension f P.obj ≃ₗ[S] Q.obj) :
    SplitK0.of.{u} (f.finiteProjectiveModulesExtendScalars.obj P) = SplitK0.of.{u} Q :=
  SplitK0.of_congr (ObjectProperty.isoMk _
    (eqToIso (f.finiteProjectiveModulesExtendScalars_obj_obj P) ≪≫ θ.toModuleIso))

end TauCeti.SplitK0
