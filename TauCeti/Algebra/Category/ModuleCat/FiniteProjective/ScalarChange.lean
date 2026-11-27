/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.BalancedExtension
public import TauCeti.Algebra.Category.ModuleCat.FiniteProjective.Basic
public import TauCeti.CategoryTheory.GrothendieckGroup.Split

import TauCeti.CategoryTheory.ObjectProperty.FullSubcategory

/-!
# Scalar change on finitely generated projective modules

Let `f : R →+* S` be a ring homomorphism of possibly noncommutative rings. This file records how
the two scalar-change functors act on the object property `TauCeti.finiteProjectiveModules`
whose split Grothendieck group is the projective `K₀`.

* Extension of scalars `P ↦ S ⊗_R P` (`TauCeti.BalancedExtension.functor f`) sends finitely
  generated projective `R`-modules to finitely generated projective `S`-modules, for every `f`.
  This is what lets it induce a homomorphism `K₀(R) → K₀(S)`. When `f` is surjective, for
  instance the reduction `R → R/I` modulo a two-sided ideal, the functor is moreover full: maps
  between extended modules lift, because a finitely generated projective module is projective and
  `N → S ⊗_R N`, `n ↦ 1 ⊗ n`, is onto. Fullness of reduction modulo `I` is the property of this
  base change used for the relative group `K₀(R, I)`.
* Restriction of scalars (`ModuleCat.restrictScalars f`) sends finitely generated projective
  `S`-modules to finitely generated projective `R`-modules exactly when `S` itself is a finitely
  generated projective `R`-module through `f`. Necessity is seen on the regular module `S`; for
  instance along `ℤ → ℚ` the finitely generated projective `ℚ`-module `ℚ` restricts to a
  `ℤ`-module that is not finitely generated. When it holds, restriction is an additive functor
  between the two categories, which induces the transfer `K₀(S) → K₀(R)`.

The module-level statements are the `Module.Finite` and `Module.Projective` instances on
`TauCeti.BalancedExtension f P`, and `RingHom.isFG_restrictScalars_of_finite` together with
`RingHom.projective_restrictScalars_of_projective`.

## Main definitions

* `RingHom.finiteProjectiveModulesExtendScalars`: extension of scalars as an additive functor
  between the categories of finitely generated projective modules.
* `RingHom.finiteProjectiveModulesExtendScalars{Congr,Id,Comp,CompCongr}`: congruence, unit,
  composition, and commutative-square coherence natural isomorphisms, with unit and pentagon laws.
* `RingHom.finiteProjectiveModulesExtendScalarsCompιIso`: followed by the inclusion into all
  modules, it is extension of scalars `TauCeti.BalancedExtension.functor` on all modules.
* `RingHom.finiteProjectiveModulesExtendScalarsCompIso`: for a commuting square
  `g₁ ∘ f₁ = g₂ ∘ f₂` of ring homomorphisms, the natural isomorphism between extending along `f₁`
  then `g₁` and along `f₂` then `g₂`, through extension along the common composite.
* `RingHom.finiteProjectiveModulesRestrictScalars`: when `S` is a finitely generated projective
  `R`-module through `f`, restriction of scalars as an additive functor between the categories of
  finitely generated projective modules.
* `RingHom.finiteProjectiveModulesRestrictScalarsCompιIso`: followed by the inclusion into all
  modules, it is restriction of scalars `ModuleCat.restrictScalars f` on all modules.

## Main results

* `TauCeti.SplitK0.of_extendScalars_obj`: the split `K₀` class of an extended module agrees
  with the class of any module linearly isomorphic to its balanced extension; in particular
  `TauCeti.SplitK0.of_extendScalars_obj_finiteProjectiveModulesRegular`: `[S ⊗_R R] = [S]`.
* `TauCeti.SplitK0.map_finiteProjectiveModulesExtendScalars_{congr,id,comp}`,
  `map_extendScalars_comp_restrictScalars_{self,eq_zero}`: functoriality and restriction-extension
  compositions on split `K₀`.
* `TauCeti.BalancedExtension.finiteProjectiveModules_le_inverseImage_functor`: extension of
  scalars preserves finitely generated projective modules.
* `RingHom.finiteProjectiveModulesExtendScalarsCompIso_hom_app_hom_apply`: on every element, the
  component of the square isomorphism is `D ⊗_B (B ⊗_A P) ≃ D ⊗_A P ≃ D ⊗_C (C ⊗_A P)`.
* `RingHom.full_finiteProjectiveModulesExtendScalars`: extension of scalars along a surjective
  ring homomorphism is full on finitely generated projective modules, and in particular reduction
  modulo a two-sided ideal is full on finitely generated projective right modules (an instance);
  `RingHom.not_full_finiteProjectiveModulesExtendScalars_int_rat`: along `ℤ → ℚ` it is not.
* `RingHom.finiteProjectiveModules_le_inverseImage_restrictScalars_iff`: restriction of scalars
  along `f` preserves finitely generated projective modules if and only if `S` is a finitely
  generated projective `R`-module through `f`.

## References

* C. A. Weibel, *The K-book*, Chapter II, §2.8 and Example 2.8.1, pp. 12–13, and, for the
  relative group `K₀(R, I)` of the base change `R → R/I`, Definition 2.10 and Exercise 2.17.
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
-- Exposed, like `TauCeti.BalancedExtension.functor`, so that elements of the extended modules can
-- be written as tensors in `S ⊗_R P`.
@[expose]
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
  ObjectProperty.map_hom_of_comp_ι_eq (ObjectProperty.lift_comp_ι _ _ _) g
    (f.finiteProjectiveModulesExtendScalars_obj_obj P)
    (f.finiteProjectiveModulesExtendScalars_obj_obj Q)

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

/-! ### Coherence of extension of scalars on finitely generated projective modules -/

/-- Equal ring homomorphisms induce naturally isomorphic extension-of-scalars functors. -/
noncomputable def finiteProjectiveModulesExtendScalarsCongr {f₁ f₂ : R →+* S} (h : f₁ = f₂) :
    f₁.finiteProjectiveModulesExtendScalars ≅ f₂.finiteProjectiveModulesExtendScalars :=
  ObjectProperty.liftNatIso f₁.finiteProjectiveModulesExtendScalarsCompιIso
    f₂.finiteProjectiveModulesExtendScalarsCompιIso (BalancedExtension.functorCongr.{u, u, u} h)

@[simp] theorem finiteProjectiveModulesExtendScalarsCongr_hom_app_hom {f₁ f₂ : R →+* S}
    (h : f₁ = f₂) (P) : ((finiteProjectiveModulesExtendScalarsCongr h).hom.app P).hom =
      eqToHom (f₁.finiteProjectiveModulesExtendScalars_obj_obj P) ≫
        (BalancedExtension.functorCongr h).hom.app P.obj ≫
          eqToHom (f₂.finiteProjectiveModulesExtendScalars_obj_obj P).symm := by
  rw [finiteProjectiveModulesExtendScalarsCongr, ObjectProperty.liftNatIso_hom_app_hom,
    finiteProjectiveModulesExtendScalarsCompιIso_hom_app,
    finiteProjectiveModulesExtendScalarsCompιIso_inv_app]
  -- `ObjectProperty.ι_obj` / `Functor.comp_obj` definitional equality inside `eqToHom` endpoints.
  rfl

@[simp] theorem finiteProjectiveModulesExtendScalarsCongr_inv_app_hom {f₁ f₂ : R →+* S}
    (h : f₁ = f₂) (P) : ((finiteProjectiveModulesExtendScalarsCongr h).inv.app P).hom =
      eqToHom (f₂.finiteProjectiveModulesExtendScalars_obj_obj P) ≫
        (BalancedExtension.functorCongr h).inv.app P.obj ≫
          eqToHom (f₁.finiteProjectiveModulesExtendScalars_obj_obj P).symm := by
  rw [finiteProjectiveModulesExtendScalarsCongr, ObjectProperty.liftNatIso_inv_app_hom,
    finiteProjectiveModulesExtendScalarsCompιIso_hom_app,
    finiteProjectiveModulesExtendScalarsCompιIso_inv_app]
  -- `ObjectProperty.ι_obj` / `Functor.comp_obj` definitional equality inside `eqToHom` endpoints.
  rfl

@[simp] theorem finiteProjectiveModulesExtendScalarsCongr_refl :
    finiteProjectiveModulesExtendScalarsCongr (rfl : f = f) =
      Iso.refl f.finiteProjectiveModulesExtendScalars := by
  rw [finiteProjectiveModulesExtendScalarsCongr, BalancedExtension.functorCongr_refl,
    ObjectProperty.liftNatIso_refl]

@[simp] theorem finiteProjectiveModulesExtendScalarsCongr_symm {f₁ f₂ : R →+* S} (h : f₁ = f₂) :
    (finiteProjectiveModulesExtendScalarsCongr h).symm =
      finiteProjectiveModulesExtendScalarsCongr h.symm := by
  rw [finiteProjectiveModulesExtendScalarsCongr, finiteProjectiveModulesExtendScalarsCongr,
    ObjectProperty.liftNatIso_symm, BalancedExtension.functorCongr_symm]

@[simp] theorem finiteProjectiveModulesExtendScalarsCongr_trans {f₁ f₂ f₃ : R →+* S}
    (h₁₂ : f₁ = f₂) (h₂₃ : f₂ = f₃) : finiteProjectiveModulesExtendScalarsCongr h₁₂ ≪≫
      finiteProjectiveModulesExtendScalarsCongr h₂₃ =
        finiteProjectiveModulesExtendScalarsCongr (h₁₂.trans h₂₃) := by
  simp [finiteProjectiveModulesExtendScalarsCongr, ObjectProperty.liftNatIso_trans]

/-- **Extension of scalars along `RingHom.id`** is naturally isomorphic to the identity functor. -/
noncomputable def finiteProjectiveModulesExtendScalarsId (R : Type u) [Ring R] :
    (RingHom.id R).finiteProjectiveModulesExtendScalars ≅
      𝟭 (finiteProjectiveModules R).FullSubcategory :=
  ObjectProperty.liftNatIso (RingHom.id R).finiteProjectiveModulesExtendScalarsCompιIso
    (Functor.leftUnitor _ ≪≫ (Functor.rightUnitor _).symm) (BalancedExtension.functorId.{u, u} R)

private theorem extendScalarsId_hom_app_hom (R : Type u) [Ring R] (P) :
    ((finiteProjectiveModulesExtendScalarsId R).hom.app P).hom =
      (RingHom.id R).finiteProjectiveModulesExtendScalarsCompιIso.hom.app P ≫
        (BalancedExtension.functorId R).hom.app P.obj := by
  simp [finiteProjectiveModulesExtendScalarsId, ObjectProperty.liftNatIso_hom_app_hom,
    -finiteProjectiveModulesExtendScalarsCompιIso_hom_app]

@[simp] theorem finiteProjectiveModulesExtendScalarsId_hom_app_hom (R : Type u) [Ring R] (P) :
    ((finiteProjectiveModulesExtendScalarsId R).hom.app P).hom =
      eqToHom ((RingHom.id R).finiteProjectiveModulesExtendScalars_obj_obj P) ≫
        (BalancedExtension.functorId R).hom.app P.obj := by
  rw [extendScalarsId_hom_app_hom, finiteProjectiveModulesExtendScalarsCompιIso_hom_app]
  -- `ObjectProperty.ι_obj` / `Functor.comp_obj` definitional equality inside `eqToHom` endpoints.
  rfl

@[simp] theorem finiteProjectiveModulesExtendScalarsId_inv_app_hom (R : Type u) [Ring R] (P) :
    ((finiteProjectiveModulesExtendScalarsId R).inv.app P).hom =
      (BalancedExtension.functorId R).inv.app P.obj ≫
        eqToHom ((RingHom.id R).finiteProjectiveModulesExtendScalars_obj_obj P).symm := by
  rw [finiteProjectiveModulesExtendScalarsId, ObjectProperty.liftNatIso_inv_app_hom]
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.leftUnitor_hom_app, Iso.symm_hom,
    Functor.rightUnitor_inv_app, Category.comp_id,
    finiteProjectiveModulesExtendScalarsCompιIso_inv_app]
  -- `ObjectProperty.ι_obj` / `Functor.comp_obj` definitional equality inside `eqToHom` endpoints.
  rfl

private noncomputable def compCompιIso {T : Type u} [Ring T] (g : S →+* T) :
    (f.finiteProjectiveModulesExtendScalars ⋙ g.finiteProjectiveModulesExtendScalars) ⋙
        (finiteProjectiveModules T).ι ≅ (finiteProjectiveModules R).ι ⋙
      (BalancedExtension.functor.{u, u, u} f ⋙ BalancedExtension.functor.{u, u, u} g) :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ g.finiteProjectiveModulesExtendScalarsCompιIso ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight f.finiteProjectiveModulesExtendScalarsCompιIso _ ≪≫
    Functor.associator _ _ _

/-- Extending along `f` and then along `g` on finitely generated projective modules has the same
underlying module as extending along `f` and then along `g` on all modules. -/
theorem finiteProjectiveModulesExtendScalars_comp_obj_obj {T : Type u} [Ring T] (g : S →+* T)
    (P : (finiteProjectiveModules R).FullSubcategory) :
    ((f.finiteProjectiveModulesExtendScalars ⋙ g.finiteProjectiveModulesExtendScalars).obj P).obj =
      (BalancedExtension.functor.{u, u, u} f ⋙ BalancedExtension.functor.{u, u, u} g).obj P.obj :=
  ((g.finiteProjectiveModulesExtendScalars_obj_obj _).trans
    (BalancedExtension.functor_obj g _).symm).trans
      (congrArg (BalancedExtension.functor g).obj
        ((f.finiteProjectiveModulesExtendScalars_obj_obj P).trans
          (BalancedExtension.functor_obj f P.obj).symm))

private theorem compCompιIso_hom_app_eq {T : Type u} [Ring T] (g : S →+* T) (P) :
    (f.compCompιIso g).hom.app P =
      g.finiteProjectiveModulesExtendScalarsCompιIso.hom.app
        (f.finiteProjectiveModulesExtendScalars.obj P) ≫
      (BalancedExtension.functor g).map
        (f.finiteProjectiveModulesExtendScalarsCompιIso.hom.app P) := by
  simp [compCompιIso, -finiteProjectiveModulesExtendScalarsCompιIso_hom_app]

private theorem compCompιIso_hom_app {T : Type u} [Ring T] (g : S →+* T) (P) :
    (f.compCompιIso g).hom.app P =
      eqToHom (f.finiteProjectiveModulesExtendScalars_comp_obj_obj g P) := by
  simp only [compCompιIso_hom_app_eq, finiteProjectiveModulesExtendScalarsCompιIso_hom_app]
  exact (congrArg _ (eqToHom_map _ _)).trans (eqToHom_trans _ _)

private theorem compCompιIso_inv_app {T : Type u} [Ring T] (g : S →+* T) (P) :
    (f.compCompιIso g).inv.app P =
      eqToHom (f.finiteProjectiveModulesExtendScalars_comp_obj_obj g P).symm := by
  rw [← cancel_mono ((f.compCompιIso g).hom.app P), Iso.inv_hom_id_app, compCompιIso_hom_app,
    eqToHom_trans]; exact (eqToHom_refl _ _).symm

/-- **Extension of scalars along a composite** `g ∘ f` is naturally isomorphic to extending along
`f` and then along `g`. -/
noncomputable def finiteProjectiveModulesExtendScalarsComp {T : Type u} [Ring T] (g : S →+* T) :
    (g.comp f).finiteProjectiveModulesExtendScalars ≅
      f.finiteProjectiveModulesExtendScalars ⋙ g.finiteProjectiveModulesExtendScalars :=
  ObjectProperty.liftNatIso (g.comp f).finiteProjectiveModulesExtendScalarsCompιIso
    (f.compCompιIso g) (BalancedExtension.functorComp.{u, u} f g)

@[simp] theorem finiteProjectiveModulesExtendScalarsComp_hom_app_hom {T : Type u} [Ring T]
    (g : S →+* T) (P) : ((f.finiteProjectiveModulesExtendScalarsComp g).hom.app P).hom =
      eqToHom ((g.comp f).finiteProjectiveModulesExtendScalars_obj_obj P) ≫
        (BalancedExtension.functorComp f g).hom.app P.obj ≫
          eqToHom (f.finiteProjectiveModulesExtendScalars_comp_obj_obj g P).symm := by
  rw [finiteProjectiveModulesExtendScalarsComp, ObjectProperty.liftNatIso_hom_app_hom,
    finiteProjectiveModulesExtendScalarsCompιIso_hom_app, compCompιIso_inv_app]
  -- `ObjectProperty.ι_obj` / `Functor.comp_obj` definitional equality inside `eqToHom` endpoints.
  rfl

@[simp] theorem finiteProjectiveModulesExtendScalarsComp_inv_app_hom {T : Type u} [Ring T]
    (g : S →+* T) (P) : ((f.finiteProjectiveModulesExtendScalarsComp g).inv.app P).hom =
      eqToHom (f.finiteProjectiveModulesExtendScalars_comp_obj_obj g P) ≫
        (BalancedExtension.functorComp f g).inv.app P.obj ≫
          eqToHom ((g.comp f).finiteProjectiveModulesExtendScalars_obj_obj P).symm := by
  rw [finiteProjectiveModulesExtendScalarsComp, ObjectProperty.liftNatIso_inv_app_hom,
    finiteProjectiveModulesExtendScalarsCompιIso_inv_app, compCompιIso_hom_app]

@[reassoc] private theorem extendScalars_map_hom_comp {P Q} (u : P ⟶ Q) :
    (f.finiteProjectiveModulesExtendScalars.map u).hom ≫
      f.finiteProjectiveModulesExtendScalarsCompιIso.hom.app Q =
    f.finiteProjectiveModulesExtendScalarsCompιIso.hom.app P ≫
      (BalancedExtension.functor f).map u.hom :=
  f.finiteProjectiveModulesExtendScalarsCompιIso.hom.naturality u

@[reassoc] private theorem extendScalarsComp_hom_app_hom_comp {T : Type u} [Ring T]
    (g : S →+* T) (P) :
    ((f.finiteProjectiveModulesExtendScalarsComp g).hom.app P).hom ≫
      g.finiteProjectiveModulesExtendScalarsCompιIso.hom.app
        (f.finiteProjectiveModulesExtendScalars.obj P) ≫
      (BalancedExtension.functor g).map (f.finiteProjectiveModulesExtendScalarsCompιIso.hom.app P) =
    (g.comp f).finiteProjectiveModulesExtendScalarsCompιIso.hom.app P ≫
      (BalancedExtension.functorComp f g).hom.app P.obj := by
  rw [← compCompιIso_hom_app_eq]; exact ObjectProperty.liftNatIso_hom_app_hom_comp ..

@[reassoc] private theorem map_extendScalarsComp_hom_app_hom_comp {T : Type u} [Ring T]
    {C : Type*} [Category* C] (F : ModuleCat.{u} T ⥤ C) (g : S →+* T) (P) :
    F.map ((f.finiteProjectiveModulesExtendScalarsComp g).hom.app P).hom ≫
      F.map (g.finiteProjectiveModulesExtendScalarsCompιIso.hom.app
        (f.finiteProjectiveModulesExtendScalars.obj P)) ≫
      F.map ((BalancedExtension.functor g).map
        (f.finiteProjectiveModulesExtendScalarsCompιIso.hom.app P)) =
    F.map ((g.comp f).finiteProjectiveModulesExtendScalarsCompιIso.hom.app P) ≫
      F.map ((BalancedExtension.functorComp f g).hom.app P.obj) := by
  simp only [← Functor.map_comp, extendScalarsComp_hom_app_hom_comp]

/-- **Pentagon coherence** for `RingHom.finiteProjectiveModulesExtendScalarsComp`. -/
@[reassoc] theorem finiteProjectiveModulesExtendScalarsComp_assoc {R₁ R₂ R₃ R₄ : Type u}
    [Ring R₁] [Ring R₂] [Ring R₃] [Ring R₄] (f₁₂ : R₁ →+* R₂) (f₂₃ : R₂ →+* R₃) (f₃₄ : R₃ →+* R₄) :
    ((f₂₃.comp f₁₂).finiteProjectiveModulesExtendScalarsComp f₃₄).hom ≫
      Functor.whiskerRight (f₁₂.finiteProjectiveModulesExtendScalarsComp f₂₃).hom
        f₃₄.finiteProjectiveModulesExtendScalars =
    (f₁₂.finiteProjectiveModulesExtendScalarsComp (f₃₄.comp f₂₃)).hom ≫
      Functor.whiskerLeft f₁₂.finiteProjectiveModulesExtendScalars
        (f₂₃.finiteProjectiveModulesExtendScalarsComp f₃₄).hom ≫
      (Functor.associator _ _ _).inv := by
  refine NatTrans.ext <| funext fun P ↦ ObjectProperty.hom_ext _ ?_
  -- Post-compose with the three inclusion isomorphisms (for `f₃₄`, `F₃₄(f₂₃)`, and `F₃₄(F₂₃(f₁₂))`)
  -- so both sides cancel into `BalancedExtension.functorComp_assoc` along the naturality and
  -- `extendScalarsComp_hom_app_hom_comp` identities.
  rw [← cancel_mono (f₃₄.finiteProjectiveModulesExtendScalarsCompιIso.hom.app _),
    ← cancel_mono ((BalancedExtension.functor f₃₄).map
      (f₂₃.finiteProjectiveModulesExtendScalarsCompιIso.hom.app _)),
    ← cancel_mono ((BalancedExtension.functor f₃₄).map ((BalancedExtension.functor f₂₃).map
      (f₁₂.finiteProjectiveModulesExtendScalarsCompιIso.hom.app P)))]
  have hcomp := congrArg (fun α ↦ α.app P.obj)
    (BalancedExtension.functorComp_assoc.{u, u} f₁₂ f₂₃ f₃₄)
  have hnat := ((BalancedExtension.functorComp f₂₃ f₃₄).hom.naturality
    (f₁₂.finiteProjectiveModulesExtendScalarsCompιIso.hom.app P)).symm
  dsimp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_inv_app, Functor.comp_obj, Functor.comp_map, ObjectProperty.ι_obj,
    ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.FullSubcategory.id_hom] at hcomp hnat ⊢
  simp only [Category.comp_id, Category.assoc] at hcomp ⊢
  simp only [extendScalars_map_hom_comp_assoc, map_extendScalarsComp_hom_app_hom_comp,
    extendScalarsComp_hom_app_hom_comp_assoc, hnat, hcomp]
  -- Both sides agree up to `Category.comp_id` and definitional
  -- `((f₃₄ ∘ f₂₃) ∘ f₁₂) ≡ (f₃₄ ∘ (f₂₃ ∘ f₁₂))`.
  rfl

/-- **Left-unit coherence** for `RingHom.finiteProjectiveModulesExtendScalars{Id,Comp}`. -/
@[reassoc] theorem finiteProjectiveModulesExtendScalarsComp_id_comp :
    ((RingHom.id R).finiteProjectiveModulesExtendScalarsComp f).hom ≫
      Functor.whiskerRight (finiteProjectiveModulesExtendScalarsId R).hom
        f.finiteProjectiveModulesExtendScalars ≫
      (Functor.leftUnitor f.finiteProjectiveModulesExtendScalars).hom = 𝟙 _ := by
  refine NatTrans.ext <| funext fun P ↦ ObjectProperty.hom_ext _ ?_
  rw [← cancel_mono (f.finiteProjectiveModulesExtendScalarsCompιIso.hom.app P)]
  have hcomp := congrArg (fun α ↦ α.app P.obj) (BalancedExtension.functorComp_id_comp.{u, u} f)
  dsimp only [NatTrans.comp_app, NatTrans.id_app, Functor.whiskerRight_app,
    Functor.leftUnitor_hom_app, Functor.comp_obj, Functor.id_obj, ObjectProperty.ι_obj,
    ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.FullSubcategory.id_hom] at hcomp ⊢
  simp only [Category.comp_id, Category.id_comp, Category.assoc] at hcomp ⊢
  simp only [extendScalars_map_hom_comp, extendScalarsId_hom_app_hom, Functor.map_comp,
    extendScalarsComp_hom_app_hom_comp_assoc, hcomp]; exact Category.comp_id _

/-- **Right-unit coherence** for `RingHom.finiteProjectiveModulesExtendScalars{Id,Comp}`. -/
@[reassoc] theorem finiteProjectiveModulesExtendScalarsComp_comp_id :
    (f.finiteProjectiveModulesExtendScalarsComp (RingHom.id S)).hom ≫
      Functor.whiskerLeft f.finiteProjectiveModulesExtendScalars
        (finiteProjectiveModulesExtendScalarsId S).hom ≫
      (Functor.rightUnitor f.finiteProjectiveModulesExtendScalars).hom = 𝟙 _ := by
  refine NatTrans.ext <| funext fun P ↦ ObjectProperty.hom_ext _ ?_
  rw [← cancel_mono (f.finiteProjectiveModulesExtendScalarsCompιIso.hom.app P)]
  have hcomp := congrArg (fun α ↦ α.app P.obj) (BalancedExtension.functorComp_comp_id.{u, u} f)
  have hnat := ((BalancedExtension.functorId S).hom.naturality
    (f.finiteProjectiveModulesExtendScalarsCompιIso.hom.app P)).symm
  dsimp only [NatTrans.comp_app, NatTrans.id_app, Functor.whiskerLeft_app,
    Functor.rightUnitor_hom_app, Functor.comp_obj, Functor.id_obj, Functor.id_map,
    ObjectProperty.ι_obj, ObjectProperty.FullSubcategory.comp_hom,
    ObjectProperty.FullSubcategory.id_hom] at hcomp hnat ⊢
  simp only [Category.comp_id, Category.id_comp, Category.assoc] at hcomp ⊢
  simp only [extendScalarsId_hom_app_hom, Category.assoc, hnat,
    extendScalarsComp_hom_app_hom_comp_assoc, hcomp]; exact Category.comp_id _

section Square

variable {A B C D : Type u} [Ring A] [Ring B] [Ring C] [Ring D]
  (f₁ : A →+* B) (g₁ : B →+* D) (f₂ : A →+* C) (g₂ : C →+* D) (h : g₁.comp f₁ = g₂.comp f₂)

/-- **Coherence of extension of scalars across a commutative square:** `g₁ ∘ f₁ = g₂ ∘ f₂` induces
a natural isomorphism between the two composite extension-of-scalars functors. -/
noncomputable def finiteProjectiveModulesExtendScalarsCompCongr :
    f₁.finiteProjectiveModulesExtendScalars ⋙ g₁.finiteProjectiveModulesExtendScalars ≅
      f₂.finiteProjectiveModulesExtendScalars ⋙ g₂.finiteProjectiveModulesExtendScalars :=
  ObjectProperty.liftNatIso (f₁.compCompιIso g₁) (f₂.compCompιIso g₂)
    (BalancedExtension.functorCompCongr.{u, u} f₁ g₁ f₂ g₂ h)

theorem finiteProjectiveModulesExtendScalarsCompCongr_eq :
    finiteProjectiveModulesExtendScalarsCompCongr f₁ g₁ f₂ g₂ h =
      (f₁.finiteProjectiveModulesExtendScalarsComp g₁).symm ≪≫
        finiteProjectiveModulesExtendScalarsCongr h ≪≫
        f₂.finiteProjectiveModulesExtendScalarsComp g₂ := by
  rw [finiteProjectiveModulesExtendScalarsCompCongr, finiteProjectiveModulesExtendScalarsComp,
    finiteProjectiveModulesExtendScalarsCongr, finiteProjectiveModulesExtendScalarsComp,
    ObjectProperty.liftNatIso_symm, ObjectProperty.liftNatIso_trans,
    ObjectProperty.liftNatIso_trans, ← BalancedExtension.functorCompCongr_def]

@[simp] theorem finiteProjectiveModulesExtendScalarsCompCongr_hom_app_hom (P) :
    ((finiteProjectiveModulesExtendScalarsCompCongr f₁ g₁ f₂ g₂ h).hom.app P).hom =
      eqToHom (f₁.finiteProjectiveModulesExtendScalars_comp_obj_obj g₁ P) ≫
        (BalancedExtension.functorCompCongr f₁ g₁ f₂ g₂ h).hom.app P.obj ≫
          eqToHom (f₂.finiteProjectiveModulesExtendScalars_comp_obj_obj g₂ P).symm := by
  rw [finiteProjectiveModulesExtendScalarsCompCongr, ObjectProperty.liftNatIso_hom_app_hom,
    compCompιIso_hom_app, compCompιIso_inv_app]

@[simp] theorem finiteProjectiveModulesExtendScalarsCompCongr_inv_app_hom (P) :
    ((finiteProjectiveModulesExtendScalarsCompCongr f₁ g₁ f₂ g₂ h).inv.app P).hom =
      eqToHom (f₂.finiteProjectiveModulesExtendScalars_comp_obj_obj g₂ P) ≫
        (BalancedExtension.functorCompCongr f₁ g₁ f₂ g₂ h).inv.app P.obj ≫
          eqToHom (f₁.finiteProjectiveModulesExtendScalars_comp_obj_obj g₁ P).symm := by
  rw [finiteProjectiveModulesExtendScalarsCompCongr, ObjectProperty.liftNatIso_inv_app_hom,
    compCompιIso_hom_app, compCompιIso_inv_app]

@[simp] theorem finiteProjectiveModulesExtendScalarsCompCongr_symm :
    (finiteProjectiveModulesExtendScalarsCompCongr f₁ g₁ f₂ g₂ h).symm =
      finiteProjectiveModulesExtendScalarsCompCongr f₂ g₂ f₁ g₁ h.symm := by
  rw [finiteProjectiveModulesExtendScalarsCompCongr, finiteProjectiveModulesExtendScalarsCompCongr,
    ObjectProperty.liftNatIso_symm, BalancedExtension.functorCompCongr_symm]

end Square

@[simp] theorem finiteProjectiveModulesExtendScalarsCompCongr_self {A B D : Type u} [Ring A]
    [Ring B] [Ring D] (f₁ : A →+* B) (g₁ : B →+* D) :
    finiteProjectiveModulesExtendScalarsCompCongr f₁ g₁ f₁ g₁ rfl = Iso.refl _ := by
  rw [finiteProjectiveModulesExtendScalarsCompCongr, BalancedExtension.functorCompCongr_self,
    ObjectProperty.liftNatIso_refl]

@[simp] theorem finiteProjectiveModulesExtendScalarsCompCongr_trans {A B₁ B₂ B₃ D : Type u}
    [Ring A] [Ring B₁] [Ring B₂] [Ring B₃] [Ring D] (f₁ : A →+* B₁) (g₁ : B₁ →+* D) (f₂ : A →+* B₂)
    (g₂ : B₂ →+* D) (f₃ : A →+* B₃) (g₃ : B₃ →+* D) (h₁₂ : g₁.comp f₁ = g₂.comp f₂)
    (h₂₃ : g₂.comp f₂ = g₃.comp f₃) :
    finiteProjectiveModulesExtendScalarsCompCongr f₁ g₁ f₂ g₂ h₁₂ ≪≫
        finiteProjectiveModulesExtendScalarsCompCongr f₂ g₂ f₃ g₃ h₂₃ =
      finiteProjectiveModulesExtendScalarsCompCongr f₁ g₁ f₃ g₃ (h₁₂.trans h₂₃) := by
  rw [finiteProjectiveModulesExtendScalarsCompCongr, finiteProjectiveModulesExtendScalarsCompCongr,
    finiteProjectiveModulesExtendScalarsCompCongr, ObjectProperty.liftNatIso_trans,
    BalancedExtension.functorCompCongr_trans.{u, u}]

section Square

variable {A B C D : Type u} [Ring A] [Ring B] [Ring C] [Ring D] (f₁ : A →+* B) (g₁ : B →+* D)
  (f₂ : A →+* C) (g₂ : C →+* D) (h : g₁.comp f₁ = g₂.comp f₂)

/-- **Extension of scalars around a commuting square.** For ring homomorphisms with
`g₁ ∘ f₁ = g₂ ∘ f₂`, extending a finitely generated projective `A`-module along `f₁` and then
along `g₁` is naturally isomorphic to extending it along `f₂` and then along `g₂`: both are
extension along the common composite, through `TauCeti.BalancedExtension.cancelBaseChange`. The
component at `P` sends `t ⊗ (s ⊗ p)` to `(t * g₁ s) ⊗ (1 ⊗ p)`, in particular `1 ⊗ (1 ⊗ p)` to
`1 ⊗ (1 ⊗ p)` (`RingHom.finiteProjectiveModulesExtendScalarsCompIso_hom_app_hom_tmul`); for the
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
`TauCeti.BalancedExtension.functorComp f₂ g₂`: it sends `t ⊗ (s ⊗ p)` to `(t * g₁ s) ⊗ (1 ⊗ p)`
(`RingHom.finiteProjectiveModulesExtendScalarsCompIso_hom_app_hom_tmul`). -/
theorem finiteProjectiveModulesExtendScalarsCompIso_hom_app_hom
    (P : (finiteProjectiveModules A).FullSubcategory) :
    ((finiteProjectiveModulesExtendScalarsCompIso f₁ g₁ f₂ g₂ h).hom.app P).hom =
      eqToHom (finiteProjectiveModulesExtendScalars_comp_obj_obj f₁ g₁ P) ≫
        (BalancedExtension.functorComp f₁ g₁).inv.app P.obj ≫
          (BalancedExtension.functorCongr h).hom.app P.obj ≫
            (BalancedExtension.functorComp f₂ g₂).hom.app P.obj ≫
              eqToHom (finiteProjectiveModulesExtendScalars_comp_obj_obj f₂ g₂ P).symm := by
  simp [finiteProjectiveModulesExtendScalarsCompIso,
    Functor.FullyFaithful.whiskeringRight_preimage_app, eqToHom_map]

/-- The component of `RingHom.finiteProjectiveModulesExtendScalarsCompIso` at `P` on an arbitrary
element of `D ⊗_B (B ⊗_A P)`: it is `TauCeti.BalancedExtension.cancelBaseChange` along `f₁, g₁`,
followed by the transport `TauCeti.BalancedExtension.congrRingHom h` and by the inverse of
`cancelBaseChange` along `f₂, g₂`. -/
theorem finiteProjectiveModulesExtendScalarsCompIso_hom_app_hom_apply
    (P : (finiteProjectiveModules A).FullSubcategory)
    (x : BalancedExtension g₁ (BalancedExtension f₁ P.obj)) :
    ((finiteProjectiveModulesExtendScalarsCompIso f₁ g₁ f₂ g₂ h).hom.app P).hom x =
      (BalancedExtension.cancelBaseChange f₂ g₂).symm
        (BalancedExtension.congrRingHom h (BalancedExtension.cancelBaseChange f₁ g₁ x)) := by
  -- The `eqToHom`s of `finiteProjectiveModulesExtendScalarsCompIso_hom_app_hom` act as identities.
  calc _ = (BalancedExtension.functorComp f₂ g₂).hom.app P.obj
        ((BalancedExtension.functorCongr h).hom.app P.obj
          ((BalancedExtension.functorComp f₁ g₁).inv.app P.obj x)) :=
      congr($(finiteProjectiveModulesExtendScalarsCompIso_hom_app_hom f₁ g₁ f₂ g₂ h P) x)
    _ = _ := by
      rw [BalancedExtension.functorComp_inv_app_apply, BalancedExtension.functorCongr_hom_app_apply,
        BalancedExtension.functorComp_hom_app_apply]

/-- The component of `RingHom.finiteProjectiveModulesExtendScalarsCompIso` at `P` sends
`t ⊗ (s ⊗ p)` to `(t * g₁ s) ⊗ (1 ⊗ p)`; in particular it sends `1 ⊗ (1 ⊗ p)` to `1 ⊗ (1 ⊗ p)`. -/
theorem finiteProjectiveModulesExtendScalarsCompIso_hom_app_hom_tmul
    (P : (finiteProjectiveModules A).FullSubcategory) (t : D) (s : B) (p : P.obj) :
    (eqToHom (finiteProjectiveModulesExtendScalars_comp_obj_obj f₁ g₁ P).symm ≫
        ((finiteProjectiveModulesExtendScalarsCompIso f₁ g₁ f₂ g₂ h).hom.app P).hom ≫
          eqToHom (finiteProjectiveModulesExtendScalars_comp_obj_obj f₂ g₂ P)).hom
        (BalancedExtension.tmul g₁ t (BalancedExtension.tmul f₁ s p)) =
      BalancedExtension.tmul g₂ (t * g₁ s) (BalancedExtension.tmul f₂ 1 p) := by
  simp only [finiteProjectiveModulesExtendScalarsCompIso_hom_app_hom, Category.assoc,
    eqToHom_trans, eqToHom_refl, Category.comp_id, eqToHom_trans_assoc, Category.id_comp]
  exact (congrArg ((BalancedExtension.functorComp f₂ g₂).hom.app P.obj)
    ((congrArg ((BalancedExtension.functorCongr h).hom.app P.obj)
      (BalancedExtension.functorComp_inv_app_tmul f₁ g₁ P.obj t s p)).trans
        (BalancedExtension.functorCongr_hom_app_tmul h P.obj _ p))).trans
    (BalancedExtension.functorComp_hom_app_tmul f₂ g₂ P.obj _ p)

/-- The inverse of the component of `RingHom.finiteProjectiveModulesExtendScalarsCompIso` at `P`
sends `t ⊗ (c ⊗ p)` to `(t * g₂ c) ⊗ (1 ⊗ p)`. -/
theorem finiteProjectiveModulesExtendScalarsCompIso_inv_app_hom_tmul
    (P : (finiteProjectiveModules A).FullSubcategory) (t : D) (c : C) (p : P.obj) :
    (eqToHom (finiteProjectiveModulesExtendScalars_comp_obj_obj f₂ g₂ P).symm ≫
        ((finiteProjectiveModulesExtendScalarsCompIso f₁ g₁ f₂ g₂ h).inv.app P).hom ≫
          eqToHom (finiteProjectiveModulesExtendScalars_comp_obj_obj f₁ g₁ P)).hom
        (BalancedExtension.tmul g₂ t (BalancedExtension.tmul f₂ c p)) =
      BalancedExtension.tmul g₁ (t * g₂ c) (BalancedExtension.tmul f₁ 1 p) := by
  -- The argument `t ⊗ (c ⊗ p) = (t * g₂ c * g₁ 1) ⊗ (1 ⊗ p)` is the image of the claimed value
  -- under the component composite, and the inverse composite undoes the component composite.
  have key : BalancedExtension.tmul g₂ t
      (BalancedExtension.tmul f₂ c p : (BalancedExtension.functor f₂).obj P.obj) =
        BalancedExtension.tmul g₂ (t * g₂ c * g₁ 1)
          (BalancedExtension.tmul f₂ 1 p : (BalancedExtension.functor f₂).obj P.obj) := by
    rw [map_one, mul_one]
    exact (congrArg (BalancedExtension.tmul g₂ t)
      (BalancedExtension.tmul_eq_smul_one_tmul c p)).trans (BalancedExtension.tmul_smul t c _)
  have hinv : (eqToHom (finiteProjectiveModulesExtendScalars_comp_obj_obj f₁ g₁ P).symm ≫
      ((finiteProjectiveModulesExtendScalarsCompIso f₁ g₁ f₂ g₂ h).hom.app P).hom ≫
        eqToHom (finiteProjectiveModulesExtendScalars_comp_obj_obj f₂ g₂ P)) ≫
      eqToHom (finiteProjectiveModulesExtendScalars_comp_obj_obj f₂ g₂ P).symm ≫
        ((finiteProjectiveModulesExtendScalarsCompIso f₁ g₁ f₂ g₂ h).inv.app P).hom ≫
          eqToHom (finiteProjectiveModulesExtendScalars_comp_obj_obj f₁ g₁ P) = 𝟙 _ := by
    simp
  refine (congrArg _ (key.trans (finiteProjectiveModulesExtendScalarsCompIso_hom_app_hom_tmul
    f₁ g₁ f₂ g₂ h P _ 1 p).symm)).trans ?_
  exact (ModuleCat.comp_apply _ _ _).symm.trans
    ((congrArg (fun φ ↦ ModuleCat.Hom.hom φ _) hinv).trans (ModuleCat.id_apply _ _))

/-- Extension of scalars around the trivial square `g ∘ f = g ∘ f` is the identity. -/
@[simp]
theorem finiteProjectiveModulesExtendScalarsCompIso_refl :
    finiteProjectiveModulesExtendScalarsCompIso f₁ g₁ f₁ g₁ rfl = Iso.refl _ := by
  refine Iso.ext (NatTrans.ext (funext fun P ↦ ObjectProperty.hom_ext _ ?_))
  simp [finiteProjectiveModulesExtendScalarsCompIso_hom_app_hom]

end Square

/-- **Extension of scalars along a surjection is full on finitely generated projective modules.**
If `f : R →+* S` is surjective, every `S`-linear map `S ⊗_R P → S ⊗_R Q` between extensions of
finitely generated projective `R`-modules is `S ⊗_R g` for an `R`-linear map `g : P → Q`. Along the
non-surjective `ℤ → ℚ` the functor is not full. -/
theorem full_finiteProjectiveModulesExtendScalars (hf : Function.Surjective f) :
    f.finiteProjectiveModulesExtendScalars.Full where
  map_surjective {P Q} φ := by
    obtain ⟨_, _⟩ := finiteProjectiveModules_iff.mp P.property
    obtain ⟨g, hg⟩ := BalancedExtension.functor_map_surjective.{u, u, u} f hf
      (P := P.obj) (N := Q.obj) φ.hom
    exact ⟨ObjectProperty.homMk g, ObjectProperty.hom_ext _ hg⟩

/-- **Reduction modulo a two-sided ideal is full on finitely generated projective right modules.**
For a two-sided ideal `I` of `R`, base change `P ↦ P ⊗_R R/I` from finitely generated projective
right `R`-modules to finitely generated projective right `R/I`-modules, the extension of scalars
along `(R → R/I)ᵐᵒᵖ`, is full: a right `R/I`-linear map `P/PI → Q/QI` lifts to a right `R`-linear
map `P → Q`. -/
instance full_finiteProjectiveModulesExtendScalars_op_quotientMk (I : Ideal R) [I.IsTwoSided] :
    (Ideal.Quotient.mk I).op.finiteProjectiveModulesExtendScalars.Full :=
  full_finiteProjectiveModulesExtendScalars _ fun x ↦
    ⟨.op (Ideal.Quotient.mk_surjective x.unop).choose,
      MulOpposite.unop_injective (Ideal.Quotient.mk_surjective x.unop).choose_spec⟩

/-- **Fullness needs surjectivity.** Extension of scalars along the inclusion `ℤ → ℚ` is not full
on finitely generated projective modules: multiplication by `1/2` on `ℚ ⊗_ℤ ℤ ≅ ℚ` is not
`ℚ ⊗_ℤ g` for any `g : ℤ → ℤ`, since `ℚ ⊗_ℤ g` is multiplication by the integer `g 1`. -/
theorem not_full_finiteProjectiveModulesExtendScalars_int_rat :
    ¬(Int.castRingHom ℚ).finiteProjectiveModulesExtendScalars.Full := by
  intro h
  let Z : (finiteProjectiveModules ℤ).FullSubcategory :=
    ⟨ModuleCat.of ℤ ℤ, finiteProjectiveModules_iff.mpr ⟨inferInstance, inferInstance⟩⟩
  obtain ⟨g, hg⟩ := h.map_surjective (X := Z) (Y := Z)
    (ObjectProperty.homMk (ModuleCat.ofHom ((1 / 2 : ℚ) • LinearMap.id)))
  -- Evaluate both sides at `1 ⊗ 1`. The functor acts on morphisms by `BalancedExtension.map`
  -- (`finiteProjectiveModulesExtendScalars_map_hom`, whose `eqToHom`s are identities).
  have key : BalancedExtension.map (Int.castRingHom ℚ) g.hom.hom
      (BalancedExtension.tmul (Int.castRingHom ℚ) 1 (1 : ℤ)) =
      (1 / 2 : ℚ) • BalancedExtension.tmul (Int.castRingHom ℚ) 1 (1 : ℤ) :=
    congr($(hg).hom (BalancedExtension.tmul (Int.castRingHom ℚ) 1 (1 : ℤ)))
  -- Identify `ℚ ⊗_ℤ ℤ` with `ℚ`: the left side becomes the integer `g 1`, the right side `1 / 2`.
  have h := congrArg (BalancedExtension.rid (Int.castRingHom ℚ)) key
  simp only [BalancedExtension.map_tmul, BalancedExtension.rid_tmul, eq_intCast, one_mul, one_div,
    BalancedExtension.smul_tmul, mul_one, Int.cast_one] at h
  have h2 : (2 * g.hom.hom 1 : ℤ) = 1 := by
    exact_mod_cast (show 2 * (g.hom.hom 1 : ℚ) = 1 by rw [h]; norm_num)
  omega

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

/-- **Restriction of scalars on finitely generated projective modules.** A ring homomorphism
`f : R →+* S` making `S` a finitely generated projective `R`-module induces a functor from the
finitely generated projective `S`-modules to the finitely generated projective `R`-modules,
sending a module to the same module with scalars restricted along `f`. -/
noncomputable def finiteProjectiveModulesRestrictScalars
    (hfin : letI := f.toModule; Module.Finite R S)
    (hproj : letI := f.toModule; Module.Projective R S) :
    (finiteProjectiveModules S).FullSubcategory ⥤ (finiteProjectiveModules R).FullSubcategory :=
  (finiteProjectiveModules R).lift ((finiteProjectiveModules S).ι ⋙ ModuleCat.restrictScalars f)
    fun M ↦ (f.finiteProjectiveModules_le_inverseImage_restrictScalars_iff.mpr ⟨hfin, hproj⟩)
      M.obj M.property

section RestrictScalars

variable (hfin : letI := f.toModule; Module.Finite R S)
  (hproj : letI := f.toModule; Module.Projective R S)

instance : (f.finiteProjectiveModulesRestrictScalars hfin hproj).Additive := by
  -- As for `RingHom.finiteProjectiveModulesExtendScalars`, additivity is read off the composite
  -- with the faithful inclusion, which is the additive functor `ι ⋙ ModuleCat.restrictScalars f`.
  have : (f.finiteProjectiveModulesRestrictScalars hfin hproj ⋙
      (finiteProjectiveModules R).ι).Additive :=
    inferInstanceAs ((finiteProjectiveModules S).ι ⋙ ModuleCat.restrictScalars f).Additive
  exact Functor.additive_of_comp_faithful _ (finiteProjectiveModules R).ι

@[simp]
theorem finiteProjectiveModulesRestrictScalars_obj_obj
    (M : (finiteProjectiveModules S).FullSubcategory) :
    ((f.finiteProjectiveModulesRestrictScalars hfin hproj).obj M).obj =
      (ModuleCat.restrictScalars f).obj M.obj :=
  (rfl)

@[simp]
theorem finiteProjectiveModulesRestrictScalars_map_hom
    {M N : (finiteProjectiveModules S).FullSubcategory} (g : M ⟶ N) :
    ((f.finiteProjectiveModulesRestrictScalars hfin hproj).map g).hom =
      eqToHom (f.finiteProjectiveModulesRestrictScalars_obj_obj hfin hproj M) ≫
        (ModuleCat.restrictScalars f).map g.hom ≫
          eqToHom (f.finiteProjectiveModulesRestrictScalars_obj_obj hfin hproj N).symm :=
  (rfl)

/-- Restriction of scalars on finitely generated projective modules, followed by the inclusion
into all modules, is the inclusion followed by restriction of scalars on all modules. Its
components are the identifications `RingHom.finiteProjectiveModulesRestrictScalars_obj_obj`. -/
noncomputable def finiteProjectiveModulesRestrictScalarsCompιIso :
    f.finiteProjectiveModulesRestrictScalars hfin hproj ⋙ (finiteProjectiveModules R).ι ≅
      (finiteProjectiveModules S).ι ⋙ ModuleCat.restrictScalars f :=
  ObjectProperty.liftCompιIso _ _ _

@[simp]
theorem finiteProjectiveModulesRestrictScalarsCompιIso_hom_app
    (M : (finiteProjectiveModules S).FullSubcategory) :
    (f.finiteProjectiveModulesRestrictScalarsCompιIso hfin hproj).hom.app M =
      eqToHom (f.finiteProjectiveModulesRestrictScalars_obj_obj hfin hproj M) :=
  (rfl)

@[simp]
theorem finiteProjectiveModulesRestrictScalarsCompιIso_inv_app
    (M : (finiteProjectiveModules S).FullSubcategory) :
    (f.finiteProjectiveModulesRestrictScalarsCompιIso hfin hproj).inv.app M =
      eqToHom (f.finiteProjectiveModulesRestrictScalars_obj_obj hfin hproj M).symm :=
  (rfl)

end RestrictScalars

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

/-- Equal ring homomorphisms induce equal extension-of-scalars maps on split `K₀`. -/
theorem map_finiteProjectiveModulesExtendScalars_congr {f₁ f₂ : R →+* S} (h : f₁ = f₂) :
    SplitK0.map.{u, u} f₁.finiteProjectiveModulesExtendScalars =
      SplitK0.map.{u, u} f₂.finiteProjectiveModulesExtendScalars :=
  SplitK0.map_congr.{u, u} fun P ↦ ⟨(RingHom.finiteProjectiveModulesExtendScalarsCongr h).app P⟩

/-- Extension of scalars along `RingHom.id` induces the identity on split `K₀`. -/
@[simp] theorem map_finiteProjectiveModulesExtendScalars_id :
    SplitK0.map.{u, u} (RingHom.id R).finiteProjectiveModulesExtendScalars = AddMonoidHom.id _ :=
  (SplitK0.map_congr.{u, u} fun P ↦
    ⟨(RingHom.finiteProjectiveModulesExtendScalarsId R).app P⟩).trans SplitK0.map_id.{u}

/-- Extension of scalars along a composite `g ∘ f` induces the composite on split `K₀`. -/
theorem map_finiteProjectiveModulesExtendScalars_comp {T : Type u} [Ring T] (g : S →+* T) :
    SplitK0.map.{u, u} (g.comp f).finiteProjectiveModulesExtendScalars =
      (SplitK0.map.{u, u} g.finiteProjectiveModulesExtendScalars).comp
        (SplitK0.map.{u, u} f.finiteProjectiveModulesExtendScalars) :=
  (SplitK0.map_congr.{u, u} fun P ↦ ⟨(f.finiteProjectiveModulesExtendScalarsComp g).app P⟩).trans
    (SplitK0.map_comp.{u, u, u} _ _)

@[simp] theorem map_finiteProjectiveModulesExtendScalars_apply_map {T : Type u} [Ring T]
    (g : S →+* T) (x) : SplitK0.map.{u, u} g.finiteProjectiveModulesExtendScalars
      (SplitK0.map.{u, u} f.finiteProjectiveModulesExtendScalars x) =
    SplitK0.map.{u, u} (g.comp f).finiteProjectiveModulesExtendScalars x :=
  (DFunLike.congr_fun (map_finiteProjectiveModulesExtendScalars_comp (f := f) g) x).symm

variable (f) in
/-- The class of `S ⊗_R R` is the class `[S]` of the free module of rank one. -/
@[simp]
theorem of_extendScalars_obj_finiteProjectiveModulesRegular :
    SplitK0.of.{u} (f.finiteProjectiveModulesExtendScalars.obj (finiteProjectiveModulesRegular R)) =
      SplitK0.of.{u} (finiteProjectiveModulesRegular S) :=
  of_extendScalars_obj (BalancedExtension.rid f)

/-- Along a surjective `p : E →+* A` making `A` finite projective over `E`, extending scalars after
restricting scalars induces the identity on `SplitK0`. -/
theorem map_extendScalars_comp_restrictScalars_self {E A : Type u} [Ring E] [Ring A] (p : E →+* A)
    (hp : Function.Surjective p) (hfin : letI := p.toModule; Module.Finite E A)
    (hproj : letI := p.toModule; Module.Projective E A) :
    (SplitK0.map.{u, u} p.finiteProjectiveModulesExtendScalars).comp
      (SplitK0.map.{u, u} (p.finiteProjectiveModulesRestrictScalars hfin hproj)) =
        AddMonoidHom.id _ :=
  SplitK0.hom_ext fun M ↦ by
    rw [AddMonoidHom.comp_apply, SplitK0.map_of, SplitK0.map_of, AddMonoidHom.id_apply]
    exact of_extendScalars_obj <| (BalancedExtension.congr p
      (eqToIso (p.finiteProjectiveModulesRestrictScalars_obj_obj hfin hproj M)).toLinearEquiv).trans
        (BalancedExtension.restrictScalarsSelfEquiv p hp M.obj)

/-- If `p : E →+* A`, `p' : E →+* B` satisfy `p e = 1` and `p' e = 0`, then extending along `p`
after restricting along `p'` induces the zero map on `SplitK0`. -/
theorem map_extendScalars_comp_restrictScalars_eq_zero {E A B : Type u} [Ring E] [Ring A] [Ring B]
    (p : E →+* A) (p' : E →+* B) (hfin : letI := p'.toModule; Module.Finite E B)
    (hproj : letI := p'.toModule; Module.Projective E B) (e : E) (hp : p e = 1) (hp' : p' e = 0) :
    (SplitK0.map.{u, u} p.finiteProjectiveModulesExtendScalars).comp
      (SplitK0.map.{u, u} (p'.finiteProjectiveModulesRestrictScalars hfin hproj)) = 0 :=
  SplitK0.hom_ext fun N ↦ by
    rw [AddMonoidHom.comp_apply, SplitK0.map_of, SplitK0.map_of, AddMonoidHom.zero_apply]
    have : Subsingleton ((BalancedExtension.functor p).obj
        ((ModuleCat.restrictScalars.{u} p').obj N.obj)) :=
      BalancedExtension.subsingleton_extendScalars_restrictScalars_of_map_eq_one_of_map_eq_zero
        p p' e hp hp' _
    exact of_eq_zero_of_isZero <| Limits.IsZero.of_full_of_faithful_of_isZero
      (finiteProjectiveModules A).ι _ <| (ModuleCat.isZero_of_subsingleton _).of_iso <|
        eqToIso ((p.finiteProjectiveModulesExtendScalars_obj_obj _).trans <| congrArg
          (BalancedExtension.functor p).obj
          (p'.finiteProjectiveModulesRestrictScalars_obj_obj _ _ N))

end TauCeti.SplitK0
