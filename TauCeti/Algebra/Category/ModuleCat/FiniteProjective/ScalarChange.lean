/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.BalancedExtension
public import TauCeti.Algebra.Category.ModuleCat.FiniteProjective.Basic
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
* `RingHom.finiteProjectiveModulesExtendScalars{Congr,Id,Comp,CompCongr}`: congruence, unit,
  composition, and commutative-square coherence natural isomorphisms, with unit and pentagon laws.
* `RingHom.finiteProjectiveModulesRestrictScalars`: restriction of scalars as an additive functor
  when `S` is finitely generated projective over `R`.

## Main results

* `TauCeti.SplitK0.of_extendScalars_obj`,
  `of_finiteProjectiveModulesExtendScalars_finiteProjectiveModulesRegular`:
  the split `K₀` class of an extended module and `[S ⊗_R R] = [S]`.
* `TauCeti.SplitK0.map_finiteProjectiveModulesExtendScalars_{id,comp}`,
  `map_extendScalars_comp_restrictScalars_{self,eq_zero}`: functoriality and restriction-extension
  compositions on split `K₀`.
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
  ObjectProperty.lift_map_hom_of_eq rfl g (f.finiteProjectiveModulesExtendScalars_obj_obj P)
    (f.finiteProjectiveModulesExtendScalars_obj_obj Q)

/-- Composing `finiteProjectiveModulesExtendScalars` with the inclusion is naturally isomorphic to
restricting `TauCeti.BalancedExtension.functor` to finitely generated projective modules. -/
noncomputable def finiteProjectiveModulesExtendScalarsCompιIso :
    f.finiteProjectiveModulesExtendScalars ⋙ (finiteProjectiveModules S).ι ≅
      (finiteProjectiveModules R).ι ⋙ BalancedExtension.functor.{u, u, u} f :=
  (finiteProjectiveModules S).liftCompιIso _ _

@[simp] theorem finiteProjectiveModulesExtendScalarsCompιIso_hom_app (P) :
    f.finiteProjectiveModulesExtendScalarsCompιIso.hom.app P =
      eqToHom (f.finiteProjectiveModulesExtendScalars_obj_obj P) := (eqToHom_refl _ _).symm

@[simp] theorem finiteProjectiveModulesExtendScalarsCompιIso_inv_app (P) :
    f.finiteProjectiveModulesExtendScalarsCompιIso.inv.app P =
      eqToHom (f.finiteProjectiveModulesExtendScalars_obj_obj P).symm := (eqToHom_refl _ _).symm

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

theorem finiteProjectiveModulesExtendScalars_comp_obj_obj {T : Type u} [Ring T] (g : S →+* T) (P) :
    ((f.finiteProjectiveModulesExtendScalars ⋙ g.finiteProjectiveModulesExtendScalars).obj P).obj =
      (BalancedExtension.functor g).obj ((BalancedExtension.functor f).obj P.obj) := (rfl)

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
    (f.compCompιIso g) (BalancedExtension.functorComp.{u, u, u, u} f g)

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
  -- `ObjectProperty.ι_obj` / `Functor.comp_obj` definitional equality inside `eqToHom` endpoints.
  rfl

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
    (BalancedExtension.functorComp_assoc.{u, u, u, u, u} f₁₂ f₂₃ f₃₄)
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
  have hcomp := congrArg (fun α ↦ α.app P.obj) (BalancedExtension.functorComp_id_comp.{u, u, u} f)
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
  have hcomp := congrArg (fun α ↦ α.app P.obj) (BalancedExtension.functorComp_comp_id.{u, u, u} f)
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
    (BalancedExtension.functorCompCongr.{u, u, u, u, u} f₁ g₁ f₂ g₂ h)

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
    BalancedExtension.functorCompCongr_trans.{u, u, u, u, u, u}]

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

section RestrictScalars
variable (hfin : letI := f.toModule; Module.Finite R S)
  (hproj : letI := f.toModule; Module.Projective R S)

/-- **Restriction of scalars on finitely generated projective modules**, when `S` is finitely
generated projective over `R` through `f : R →+* S`. -/
noncomputable def finiteProjectiveModulesRestrictScalars :
    (finiteProjectiveModules S).FullSubcategory ⥤ (finiteProjectiveModules R).FullSubcategory :=
  (finiteProjectiveModules R).lift ((finiteProjectiveModules S).ι ⋙ ModuleCat.restrictScalars.{u} f)
    fun M ↦ (f.finiteProjectiveModules_le_inverseImage_restrictScalars_iff.mpr
      ⟨hfin, hproj⟩) M.obj M.property

instance : (f.finiteProjectiveModulesRestrictScalars hfin hproj).Additive :=
  have : (f.finiteProjectiveModulesRestrictScalars hfin hproj ⋙
      (finiteProjectiveModules R).ι).Additive :=
    inferInstanceAs ((finiteProjectiveModules S).ι ⋙ ModuleCat.restrictScalars.{u} f).Additive
  Functor.additive_of_comp_faithful _ (finiteProjectiveModules R).ι

@[simp] theorem finiteProjectiveModulesRestrictScalars_obj_obj (M) :
    ((f.finiteProjectiveModulesRestrictScalars hfin hproj).obj M).obj =
      (ModuleCat.restrictScalars.{u} f).obj M.obj := (rfl)

@[simp] theorem finiteProjectiveModulesRestrictScalars_map_hom
    {M N : (finiteProjectiveModules S).FullSubcategory} (g : M ⟶ N) :
    ((f.finiteProjectiveModulesRestrictScalars hfin hproj).map g).hom =
      eqToHom (f.finiteProjectiveModulesRestrictScalars_obj_obj hfin hproj M) ≫
        (ModuleCat.restrictScalars.{u} f).map g.hom ≫
          eqToHom (f.finiteProjectiveModulesRestrictScalars_obj_obj hfin hproj N).symm :=
  ObjectProperty.lift_map_hom_of_eq rfl g
    (f.finiteProjectiveModulesRestrictScalars_obj_obj hfin hproj M)
    (f.finiteProjectiveModulesRestrictScalars_obj_obj hfin hproj N)

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

variable (f)

/-- Extension of scalars along `f : R →+* S` sends `[R]` to `[S]`. -/
@[simp] theorem of_finiteProjectiveModulesExtendScalars_finiteProjectiveModulesRegular :
    SplitK0.of.{u} (f.finiteProjectiveModulesExtendScalars.obj
      (finiteProjectiveModulesRegular R)) = SplitK0.of.{u} (finiteProjectiveModulesRegular S) :=
  of_extendScalars_obj <| (BalancedExtension.congr f
    ((eqToIso (finiteProjectiveModulesRegular_obj R)).toLinearEquiv.trans
      (LinearEquiv.funUnique Unit R R).symm)).trans <|
    (BalancedExtension.piScalarRight f Unit).trans ((LinearEquiv.funUnique Unit S S).trans
      (eqToIso (finiteProjectiveModulesRegular_obj S).symm).toLinearEquiv)

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
      BalancedExtension.subsingleton_restrictScalars_of_map_eq_one_of_map_eq_zero p p' e hp hp' _
    exact of_eq_zero_of_isZero <| Limits.IsZero.of_full_of_faithful_of_isZero
      (finiteProjectiveModules A).ι _ <| (ModuleCat.isZero_of_subsingleton _).of_iso <|
        eqToIso ((p.finiteProjectiveModulesExtendScalars_obj_obj _).trans <| congrArg
          (BalancedExtension.functor p).obj
          (p'.finiteProjectiveModulesRestrictScalars_obj_obj _ _ N))

end TauCeti.SplitK0
