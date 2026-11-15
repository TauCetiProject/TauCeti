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
* `RingHom.finiteProjectiveModulesExtendScalarsCongr`,
  `RingHom.finiteProjectiveModulesExtendScalarsId`,
  `RingHom.finiteProjectiveModulesExtendScalarsComp`, and
  `RingHom.finiteProjectiveModulesExtendScalarsCompCongr`: congruence, identity, composition, and
  commutative-square coherence natural isomorphisms for
  `RingHom.finiteProjectiveModulesExtendScalars`, with unit and pentagon coherence laws.
* `RingHom.finiteProjectiveModulesRestrictScalars`: restriction of scalars as an additive functor
  between the categories of finitely generated projective modules when `S` is finitely generated
  projective over `R`.

## Main results

* `TauCeti.SplitK0.of_extendScalars_obj`: the split `K₀` class of an extended module agrees
  with the class of any module linearly isomorphic to its balanced extension.
* `TauCeti.SplitK0.map_finiteProjectiveModulesExtendScalars_id` and
  `TauCeti.SplitK0.map_finiteProjectiveModulesExtendScalars_comp`: functoriality of extension of
  scalars on the split `K₀` of finitely generated projective modules.
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
  ObjectProperty.lift_map_hom_of_eq rfl g
    (f.finiteProjectiveModulesExtendScalars_obj_obj P)
    (f.finiteProjectiveModulesExtendScalars_obj_obj Q)

/-- Composing `RingHom.finiteProjectiveModulesExtendScalars` with the full-subcategory inclusion is
naturally isomorphic to restricting `TauCeti.BalancedExtension.functor` to finitely generated
projective modules. -/
noncomputable def finiteProjectiveModulesExtendScalarsCompιIso :
    f.finiteProjectiveModulesExtendScalars ⋙ (finiteProjectiveModules S).ι ≅
      (finiteProjectiveModules R).ι ⋙ BalancedExtension.functor.{u, u, u} f :=
  (finiteProjectiveModules S).liftCompιIso _ _

@[simp] theorem finiteProjectiveModulesExtendScalarsCompιIso_hom_app
    (P : (finiteProjectiveModules R).FullSubcategory) :
    f.finiteProjectiveModulesExtendScalarsCompιIso.hom.app P =
      eqToHom (f.finiteProjectiveModulesExtendScalars_obj_obj P) := by
  unfold finiteProjectiveModulesExtendScalarsCompιIso ObjectProperty.liftCompιIso
  rw [Iso.refl_hom, NatTrans.id_app]
  exact (eqToHom_refl _ _).symm

@[simp] theorem finiteProjectiveModulesExtendScalarsCompιIso_inv_app
    (P : (finiteProjectiveModules R).FullSubcategory) :
    f.finiteProjectiveModulesExtendScalarsCompιIso.inv.app P =
      eqToHom (f.finiteProjectiveModulesExtendScalars_obj_obj P).symm := by
  unfold finiteProjectiveModulesExtendScalarsCompιIso ObjectProperty.liftCompιIso
  rw [Iso.refl_inv, NatTrans.id_app]
  exact (eqToHom_refl _ _).symm

/-! ### Coherence of extension of scalars on finitely generated projective modules -/

section Coherence

/-- Equal ring homomorphisms induce naturally isomorphic extension-of-scalars functors on finitely
generated projective modules. -/
noncomputable def finiteProjectiveModulesExtendScalarsCongr {f₁ f₂ : R →+* S} (h : f₁ = f₂) :
    f₁.finiteProjectiveModulesExtendScalars ≅ f₂.finiteProjectiveModulesExtendScalars :=
  ((finiteProjectiveModules S).fullyFaithfulι.whiskeringRight _).preimageIso
    (f₁.finiteProjectiveModulesExtendScalarsCompιIso ≪≫
      (finiteProjectiveModules R).ι.isoWhiskerLeft (BalancedExtension.functorCongr.{u, u, u} h) ≪≫
      f₂.finiteProjectiveModulesExtendScalarsCompιIso.symm)

@[simp] theorem finiteProjectiveModulesExtendScalarsCongr_hom_app_hom {f₁ f₂ : R →+* S}
    (h : f₁ = f₂) (P : (finiteProjectiveModules R).FullSubcategory) :
    ((finiteProjectiveModulesExtendScalarsCongr h).hom.app P).hom =
      eqToHom (f₁.finiteProjectiveModulesExtendScalars_obj_obj P) ≫
        (BalancedExtension.functorCongr h).hom.app P.obj ≫
          eqToHom (f₂.finiteProjectiveModulesExtendScalars_obj_obj P).symm := by
  rw [← ObjectProperty.ι_map, finiteProjectiveModulesExtendScalarsCongr,
    Functor.FullyFaithful.preimageIso_hom, Functor.FullyFaithful.whiskeringRight_preimage_app,
    Functor.FullyFaithful.map_preimage]
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, ObjectProperty.ι_obj,
    finiteProjectiveModulesExtendScalarsCompιIso_hom_app,
    finiteProjectiveModulesExtendScalarsCompιIso_inv_app]
  rfl

@[simp] theorem finiteProjectiveModulesExtendScalarsCongr_inv_app_hom {f₁ f₂ : R →+* S}
    (h : f₁ = f₂) (P : (finiteProjectiveModules R).FullSubcategory) :
    ((finiteProjectiveModulesExtendScalarsCongr h).inv.app P).hom =
      eqToHom (f₂.finiteProjectiveModulesExtendScalars_obj_obj P) ≫
        (BalancedExtension.functorCongr h).inv.app P.obj ≫
          eqToHom (f₁.finiteProjectiveModulesExtendScalars_obj_obj P).symm := by
  rw [← ObjectProperty.ι_map, finiteProjectiveModulesExtendScalarsCongr,
    Functor.FullyFaithful.preimageIso_inv, Functor.FullyFaithful.whiskeringRight_preimage_app,
    Functor.FullyFaithful.map_preimage]
  simp only [Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app, Functor.isoWhiskerLeft_inv,
    Functor.whiskerLeft_app, ObjectProperty.ι_obj, Category.assoc,
    finiteProjectiveModulesExtendScalarsCompιIso_hom_app,
    finiteProjectiveModulesExtendScalarsCompιIso_inv_app]
  rfl

@[simp] theorem finiteProjectiveModulesExtendScalarsCongr_refl :
    finiteProjectiveModulesExtendScalarsCongr (rfl : f = f) =
      Iso.refl f.finiteProjectiveModulesExtendScalars := by
  refine Iso.ext <| ((finiteProjectiveModules S).fullyFaithfulι.whiskeringRight _).map_injective ?_
  simp [-Functor.whiskeringRight_obj_map, finiteProjectiveModulesExtendScalarsCongr]

@[simp] theorem finiteProjectiveModulesExtendScalarsCongr_symm {f₁ f₂ : R →+* S} (h : f₁ = f₂) :
    (finiteProjectiveModulesExtendScalarsCongr h).symm =
      finiteProjectiveModulesExtendScalarsCongr h.symm := by
  refine Iso.ext <| ((finiteProjectiveModules S).fullyFaithfulι.whiskeringRight _).map_injective ?_
  simp only [finiteProjectiveModulesExtendScalarsCongr, Iso.symm_hom,
    Functor.FullyFaithful.preimageIso_inv, Functor.FullyFaithful.preimageIso_hom,
    Functor.FullyFaithful.map_preimage, Iso.trans_hom, Iso.trans_inv, Iso.symm_inv,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerLeft_inv, Category.assoc,
    Iso.cancel_iso_hom_left, Iso.cancel_iso_inv_right]
  rw [← Iso.symm_hom, BalancedExtension.functorCongr_symm]

@[simp] theorem finiteProjectiveModulesExtendScalarsCongr_trans {f₁ f₂ f₃ : R →+* S}
    (h₁₂ : f₁ = f₂) (h₂₃ : f₂ = f₃) :
    finiteProjectiveModulesExtendScalarsCongr h₁₂ ≪≫
        finiteProjectiveModulesExtendScalarsCongr h₂₃ =
      finiteProjectiveModulesExtendScalarsCongr (h₁₂.trans h₂₃) := by
  refine Iso.ext <| ((finiteProjectiveModules S).fullyFaithfulι.whiskeringRight _).map_injective ?_
  simp only [finiteProjectiveModulesExtendScalarsCongr, Iso.trans_hom, Functor.map_comp,
    Functor.FullyFaithful.preimageIso_hom, Functor.FullyFaithful.map_preimage, Iso.symm_hom,
    Functor.isoWhiskerLeft_hom, Category.assoc, Iso.inv_hom_id_assoc, Iso.cancel_iso_hom_left]
  rw [← Category.assoc, ← Functor.whiskerLeft_comp, ← Iso.trans_hom,
    BalancedExtension.functorCongr_trans]

/-- **Extension of scalars along the identity ring homomorphism** on finitely generated projective
modules is naturally isomorphic to the identity functor. -/
noncomputable def finiteProjectiveModulesExtendScalarsId (R : Type u) [Ring R] :
    (RingHom.id R).finiteProjectiveModulesExtendScalars ≅
      𝟭 (finiteProjectiveModules R).FullSubcategory :=
  ((finiteProjectiveModules R).fullyFaithfulι.whiskeringRight _).preimageIso
    ((RingHom.id R).finiteProjectiveModulesExtendScalarsCompιIso ≪≫
      (finiteProjectiveModules R).ι.isoWhiskerLeft (BalancedExtension.functorId.{u, u} R) ≪≫
      Functor.rightUnitor _ ≪≫ (Functor.leftUnitor _).symm)

private theorem finiteProjectiveModulesExtendScalarsId_hom_app_eq (R : Type u) [Ring R]
    (P : (finiteProjectiveModules R).FullSubcategory) :
    ((finiteProjectiveModulesExtendScalarsId R).hom.app P).hom =
      (RingHom.id R).finiteProjectiveModulesExtendScalarsCompιIso.hom.app P ≫
        (BalancedExtension.functorId R).hom.app P.obj := by
  rw [← ObjectProperty.ι_map, finiteProjectiveModulesExtendScalarsId,
    Functor.FullyFaithful.preimageIso_hom, Functor.FullyFaithful.whiskeringRight_preimage_app,
    Functor.FullyFaithful.map_preimage]
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Functor.comp_obj, ObjectProperty.ι_obj, Functor.rightUnitor_hom_app,
    Functor.leftUnitor_inv_app, Functor.id_obj, Category.comp_id]

@[simp] theorem finiteProjectiveModulesExtendScalarsId_hom_app_hom (R : Type u) [Ring R]
    (P : (finiteProjectiveModules R).FullSubcategory) :
    ((finiteProjectiveModulesExtendScalarsId R).hom.app P).hom =
      eqToHom ((RingHom.id R).finiteProjectiveModulesExtendScalars_obj_obj P) ≫
        (BalancedExtension.functorId R).hom.app P.obj := by
  rw [finiteProjectiveModulesExtendScalarsId_hom_app_eq,
    finiteProjectiveModulesExtendScalarsCompιIso_hom_app]
  rfl

@[simp] theorem finiteProjectiveModulesExtendScalarsId_inv_app_hom (R : Type u) [Ring R]
    (P : (finiteProjectiveModules R).FullSubcategory) :
    ((finiteProjectiveModulesExtendScalarsId R).inv.app P).hom =
      (BalancedExtension.functorId R).inv.app P.obj ≫
        eqToHom ((RingHom.id R).finiteProjectiveModulesExtendScalars_obj_obj P).symm := by
  rw [← ObjectProperty.ι_map, finiteProjectiveModulesExtendScalarsId,
    Functor.FullyFaithful.preimageIso_inv, Functor.FullyFaithful.whiskeringRight_preimage_app,
    Functor.FullyFaithful.map_preimage]
  simp only [Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app, Functor.isoWhiskerLeft_inv,
    Functor.whiskerLeft_app, ObjectProperty.ι_obj, Functor.leftUnitor_hom_app,
    Functor.rightUnitor_inv_app, Category.id_comp, Category.assoc,
    finiteProjectiveModulesExtendScalarsCompιIso_inv_app]
  rfl

private noncomputable def finiteProjectiveModulesExtendScalarsCompCompιIso {T : Type u} [Ring T]
    (g : S →+* T) :
    (f.finiteProjectiveModulesExtendScalars ⋙ g.finiteProjectiveModulesExtendScalars) ⋙
        (finiteProjectiveModules T).ι ≅
      (finiteProjectiveModules R).ι ⋙
        (BalancedExtension.functor.{u, u, u} f ⋙ BalancedExtension.functor.{u, u, u} g) :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ g.finiteProjectiveModulesExtendScalarsCompιIso ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight f.finiteProjectiveModulesExtendScalarsCompιIso _ ≪≫
    Functor.associator _ _ _

theorem finiteProjectiveModulesExtendScalars_comp_obj_obj {T : Type u} [Ring T] (g : S →+* T)
    (P : (finiteProjectiveModules R).FullSubcategory) :
    ((f.finiteProjectiveModulesExtendScalars ⋙ g.finiteProjectiveModulesExtendScalars).obj P).obj =
      (BalancedExtension.functor g).obj ((BalancedExtension.functor f).obj P.obj) := (rfl)

private theorem finiteProjectiveModulesExtendScalarsCompCompιIso_hom_app_eq {T : Type u} [Ring T]
    (g : S →+* T) (P : (finiteProjectiveModules R).FullSubcategory) :
    (f.finiteProjectiveModulesExtendScalarsCompCompιIso g).hom.app P =
      g.finiteProjectiveModulesExtendScalarsCompιIso.hom.app
        (f.finiteProjectiveModulesExtendScalars.obj P) ≫
      (BalancedExtension.functor g).map
        (f.finiteProjectiveModulesExtendScalarsCompιIso.hom.app P) := by
  simp only [finiteProjectiveModulesExtendScalarsCompCompιIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Category.id_comp, Category.comp_id]

private theorem finiteProjectiveModulesExtendScalarsCompCompιIso_hom_app {T : Type u} [Ring T]
    (g : S →+* T) (P : (finiteProjectiveModules R).FullSubcategory) :
    (f.finiteProjectiveModulesExtendScalarsCompCompιIso g).hom.app P =
      eqToHom (f.finiteProjectiveModulesExtendScalars_comp_obj_obj g P) := by
  have h1 : (f.finiteProjectiveModulesExtendScalars ⋙ (finiteProjectiveModules S).ι).obj P =
      ((finiteProjectiveModules R).ι ⋙ BalancedExtension.functor f).obj P := rfl
  have h2 : (g.finiteProjectiveModulesExtendScalars ⋙ (finiteProjectiveModules T).ι).obj
        (f.finiteProjectiveModulesExtendScalars.obj P) =
      ((finiteProjectiveModules S).ι ⋙ BalancedExtension.functor g).obj
        (f.finiteProjectiveModulesExtendScalars.obj P) := rfl
  have hf : f.finiteProjectiveModulesExtendScalarsCompιIso.hom.app P = eqToHom h1 :=
    f.finiteProjectiveModulesExtendScalarsCompιIso_hom_app P
  have hg : g.finiteProjectiveModulesExtendScalarsCompιIso.hom.app
      (f.finiteProjectiveModulesExtendScalars.obj P) = eqToHom h2 :=
    g.finiteProjectiveModulesExtendScalarsCompιIso_hom_app _
  rw [finiteProjectiveModulesExtendScalarsCompCompιIso_hom_app_eq, hf, hg,
    eqToHom_map, eqToHom_trans]

private theorem finiteProjectiveModulesExtendScalarsCompCompιIso_inv_app {T : Type u} [Ring T]
    (g : S →+* T) (P : (finiteProjectiveModules R).FullSubcategory) :
    (f.finiteProjectiveModulesExtendScalarsCompCompιIso g).inv.app P =
      eqToHom (f.finiteProjectiveModulesExtendScalars_comp_obj_obj g P).symm := by
  have h1 : ((finiteProjectiveModules R).ι ⋙ BalancedExtension.functor f).obj P =
      (f.finiteProjectiveModulesExtendScalars ⋙ (finiteProjectiveModules S).ι).obj P := rfl
  have h2 : ((finiteProjectiveModules S).ι ⋙ BalancedExtension.functor g).obj
        (f.finiteProjectiveModulesExtendScalars.obj P) =
      (g.finiteProjectiveModulesExtendScalars ⋙ (finiteProjectiveModules T).ι).obj
        (f.finiteProjectiveModulesExtendScalars.obj P) := rfl
  have hf : f.finiteProjectiveModulesExtendScalarsCompιIso.inv.app P = eqToHom h1 :=
    f.finiteProjectiveModulesExtendScalarsCompιIso_inv_app P
  have hg : g.finiteProjectiveModulesExtendScalarsCompιIso.inv.app
      (f.finiteProjectiveModulesExtendScalars.obj P) = eqToHom h2 :=
    g.finiteProjectiveModulesExtendScalarsCompιIso_inv_app _
  simp only [finiteProjectiveModulesExtendScalarsCompCompιIso, Iso.trans_inv, Iso.symm_inv,
    NatTrans.comp_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.isoWhiskerLeft_inv, Functor.whiskerLeft_app, Functor.isoWhiskerRight_inv,
    Functor.whiskerRight_app, Category.id_comp, Category.comp_id]
  rw [hf, hg, eqToHom_map, eqToHom_trans]

/-- **Extension of scalars along a composite ring homomorphism** `g ∘ f` on finitely generated
projective modules is naturally isomorphic to extending along `f` and then along `g`. -/
noncomputable def finiteProjectiveModulesExtendScalarsComp {T : Type u} [Ring T] (g : S →+* T) :
    (g.comp f).finiteProjectiveModulesExtendScalars ≅
      f.finiteProjectiveModulesExtendScalars ⋙ g.finiteProjectiveModulesExtendScalars :=
  ((finiteProjectiveModules T).fullyFaithfulι.whiskeringRight _).preimageIso
    ((g.comp f).finiteProjectiveModulesExtendScalarsCompιIso ≪≫
      (finiteProjectiveModules R).ι.isoWhiskerLeft
        (BalancedExtension.functorComp.{u, u, u, u} f g) ≪≫
      (f.finiteProjectiveModulesExtendScalarsCompCompιIso g).symm)

private theorem finiteProjectiveModulesExtendScalarsComp_hom_app_eq {T : Type u} [Ring T]
    (g : S →+* T) (P : (finiteProjectiveModules R).FullSubcategory) :
    ((f.finiteProjectiveModulesExtendScalarsComp g).hom.app P).hom =
      (g.comp f).finiteProjectiveModulesExtendScalarsCompιIso.hom.app P ≫
        (BalancedExtension.functorComp f g).hom.app P.obj ≫
          (f.finiteProjectiveModulesExtendScalarsCompCompιIso g).inv.app P := by
  rw [← ObjectProperty.ι_map, finiteProjectiveModulesExtendScalarsComp,
    Functor.FullyFaithful.preimageIso_hom, Functor.FullyFaithful.whiskeringRight_preimage_app,
    Functor.FullyFaithful.map_preimage]
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, ObjectProperty.ι_obj]

@[simp] theorem finiteProjectiveModulesExtendScalarsComp_hom_app_hom {T : Type u} [Ring T]
    (g : S →+* T) (P : (finiteProjectiveModules R).FullSubcategory) :
    ((f.finiteProjectiveModulesExtendScalarsComp g).hom.app P).hom =
      eqToHom ((g.comp f).finiteProjectiveModulesExtendScalars_obj_obj P) ≫
        (BalancedExtension.functorComp f g).hom.app P.obj ≫
          eqToHom (f.finiteProjectiveModulesExtendScalars_comp_obj_obj g P).symm := by
  rw [finiteProjectiveModulesExtendScalarsComp_hom_app_eq,
    finiteProjectiveModulesExtendScalarsCompιIso_hom_app,
    finiteProjectiveModulesExtendScalarsCompCompιIso_inv_app]
  rfl

@[simp] theorem finiteProjectiveModulesExtendScalarsComp_inv_app_hom {T : Type u} [Ring T]
    (g : S →+* T) (P : (finiteProjectiveModules R).FullSubcategory) :
    ((f.finiteProjectiveModulesExtendScalarsComp g).inv.app P).hom =
      eqToHom (f.finiteProjectiveModulesExtendScalars_comp_obj_obj g P) ≫
        (BalancedExtension.functorComp f g).inv.app P.obj ≫
          eqToHom ((g.comp f).finiteProjectiveModulesExtendScalars_obj_obj P).symm := by
  rw [← ObjectProperty.ι_map, finiteProjectiveModulesExtendScalarsComp,
    Functor.FullyFaithful.preimageIso_inv, Functor.FullyFaithful.whiskeringRight_preimage_app,
    Functor.FullyFaithful.map_preimage]
  simp only [Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app, Functor.isoWhiskerLeft_inv,
    Functor.whiskerLeft_app, ObjectProperty.ι_obj, Category.assoc,
    finiteProjectiveModulesExtendScalarsCompCompιIso_hom_app,
    finiteProjectiveModulesExtendScalarsCompιIso_inv_app]
  rfl

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
  have hcomp := congrArg (fun α ↦ α.app P.obj)
    (BalancedExtension.functorComp_assoc.{u, u, u, u, u} f₁₂ f₂₃ f₃₄)
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_inv_app, Functor.comp_obj, Category.comp_id] at hcomp
  have hobj : ∀ {A B : Type u} [Ring A] [Ring B] (f : A →+* B)
      (X : (finiteProjectiveModules A).FullSubcategory),
      (f.finiteProjectiveModulesExtendScalars.obj X).obj =
        (BalancedExtension.functor f).obj X.obj := fun _ _ ↦ rfl
  have hcompHom : ∀ {A B C : Type u} [Ring A] [Ring B] [Ring C] (f : A →+* B) (g : B →+* C)
      (X : (finiteProjectiveModules A).FullSubcategory),
      ((f.finiteProjectiveModulesExtendScalarsComp g).hom.app X).hom =
        eqToHom (hobj (g.comp f) X) ≫
          (BalancedExtension.functorComp f g).hom.app X.obj ≫
            eqToHom (f.finiteProjectiveModulesExtendScalars_comp_obj_obj g X).symm :=
    fun f g X ↦ f.finiteProjectiveModulesExtendScalarsComp_hom_app_hom g X
  have hnat := (BalancedExtension.functorComp f₂₃ f₃₄).hom.naturality (eqToHom (hobj f₁₂ P).symm)
  simp only [Functor.comp_obj, Functor.comp_map, eqToHom_map] at hnat
  have hmap : (f₃₄.finiteProjectiveModulesExtendScalars.map
      ((f₁₂.finiteProjectiveModulesExtendScalarsComp f₂₃).hom.app P)).hom =
      eqToHom (hobj f₃₄ _) ≫
        (BalancedExtension.functor f₃₄).map
          ((f₁₂.finiteProjectiveModulesExtendScalarsComp f₂₃).hom.app P).hom ≫
        eqToHom (hobj f₃₄ _).symm :=
    f₃₄.finiteProjectiveModulesExtendScalars_map_hom _
  simp only [NatTrans.comp_app, ObjectProperty.FullSubcategory.comp_hom, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Functor.associator_inv_app, Functor.comp_obj, Category.comp_id]
  rw [hmap, hcompHom f₁₂ f₂₃ P, hcompHom (f₂₃.comp f₁₂) f₃₄ P,
    hcompHom f₁₂ (f₃₄.comp f₂₃) P,
    hcompHom f₂₃ f₃₄ (f₁₂.finiteProjectiveModulesExtendScalars.obj P)]
  simp only [Functor.map_comp, eqToHom_map, Category.assoc, eqToHom_trans_assoc,
    eqToHom_refl, Category.id_comp]
  rw [← Category.assoc (eqToHom _) ((BalancedExtension.functorComp f₂₃ f₃₄).hom.app _), hnat]
  simp only [Category.assoc, eqToHom_trans]
  rw [← Category.assoc ((BalancedExtension.functorComp (f₂₃.comp f₁₂) f₃₄).hom.app _),
    ← Category.assoc ((BalancedExtension.functorComp f₁₂ (f₃₄.comp f₂₃)).hom.app _), hcomp]

/-- **Left-unit coherence** for `RingHom.finiteProjectiveModulesExtendScalarsId` and
`RingHom.finiteProjectiveModulesExtendScalarsComp`. -/
@[reassoc] theorem finiteProjectiveModulesExtendScalarsComp_id_comp :
    ((RingHom.id R).finiteProjectiveModulesExtendScalarsComp f).hom ≫
      Functor.whiskerRight (finiteProjectiveModulesExtendScalarsId R).hom
        f.finiteProjectiveModulesExtendScalars ≫
      (Functor.leftUnitor f.finiteProjectiveModulesExtendScalars).hom = 𝟙 _ := by
  refine NatTrans.ext <| funext fun P ↦ ObjectProperty.hom_ext _ ?_
  rw [← cancel_mono (f.finiteProjectiveModulesExtendScalarsCompιIso.hom.app P)]
  have hcomp := congrArg (fun α ↦ α.app P.obj)
    (BalancedExtension.functorComp_id_comp.{u, u, u} f)
  have hnat := f.finiteProjectiveModulesExtendScalarsCompιIso.hom.naturality
    ((finiteProjectiveModulesExtendScalarsId R).hom.app P)
  simp only [Functor.comp_obj, Functor.comp_map, ObjectProperty.ι_obj, ObjectProperty.ι_map,
    Functor.id_obj] at hnat
  simp only [NatTrans.comp_app, NatTrans.id_app, Functor.whiskerRight_app,
    Functor.leftUnitor_hom_app, Functor.comp_obj, Functor.id_obj, Category.comp_id] at hcomp
  simp only [NatTrans.comp_app, NatTrans.id_app, ObjectProperty.FullSubcategory.comp_hom,
    ObjectProperty.FullSubcategory.id_hom, Functor.whiskerRight_app, Functor.leftUnitor_hom_app,
    Functor.comp_obj, ObjectProperty.ι_obj, Functor.id_obj, Category.id_comp, Category.assoc]
  rw [finiteProjectiveModulesExtendScalarsComp_hom_app_eq]
  simp only [Category.assoc]
  rw [hnat, finiteProjectiveModulesExtendScalarsId_hom_app_eq, Functor.map_comp,
    ← Category.assoc (f.finiteProjectiveModulesExtendScalarsCompιIso.hom.app _),
    ← finiteProjectiveModulesExtendScalarsCompCompιIso_hom_app_eq, Iso.inv_hom_id_app_assoc,
    hcomp]
  simp only [Functor.comp_obj, ObjectProperty.ι_obj, Category.comp_id]
  rw [finiteProjectiveModulesExtendScalarsCompιIso_hom_app,
    finiteProjectiveModulesExtendScalarsCompιIso_hom_app]

/-- **Right-unit coherence** for `RingHom.finiteProjectiveModulesExtendScalarsId` and
`RingHom.finiteProjectiveModulesExtendScalarsComp`. -/
@[reassoc] theorem finiteProjectiveModulesExtendScalarsComp_comp_id :
    (f.finiteProjectiveModulesExtendScalarsComp (RingHom.id S)).hom ≫
      Functor.whiskerLeft f.finiteProjectiveModulesExtendScalars
        (finiteProjectiveModulesExtendScalarsId S).hom ≫
      (Functor.rightUnitor f.finiteProjectiveModulesExtendScalars).hom = 𝟙 _ := by
  refine NatTrans.ext <| funext fun P ↦ ObjectProperty.hom_ext _ ?_
  rw [← cancel_mono (f.finiteProjectiveModulesExtendScalarsCompιIso.hom.app P)]
  have hcomp := congrArg (fun α ↦ α.app P.obj)
    (BalancedExtension.functorComp_comp_id.{u, u, u} f)
  have hnat := (BalancedExtension.functorId S).hom.naturality
    (f.finiteProjectiveModulesExtendScalarsCompιIso.hom.app P)
  simp only [Functor.comp_obj, ObjectProperty.ι_obj, Functor.id_map] at hnat
  simp only [NatTrans.comp_app, NatTrans.id_app, Functor.whiskerLeft_app,
    Functor.rightUnitor_hom_app, Functor.comp_obj, Functor.id_obj, Category.comp_id] at hcomp
  simp only [NatTrans.comp_app, NatTrans.id_app, ObjectProperty.FullSubcategory.comp_hom,
    ObjectProperty.FullSubcategory.id_hom, Functor.whiskerLeft_app, Functor.rightUnitor_hom_app,
    Functor.comp_obj, ObjectProperty.ι_obj, Functor.id_obj, Category.id_comp, Category.assoc]
  rw [finiteProjectiveModulesExtendScalarsComp_hom_app_eq,
    finiteProjectiveModulesExtendScalarsId_hom_app_eq]
  simp only [Category.assoc]
  rw [← hnat,
    ← Category.assoc ((RingHom.id S).finiteProjectiveModulesExtendScalarsCompιIso.hom.app _),
    ← finiteProjectiveModulesExtendScalarsCompCompιIso_hom_app_eq, Iso.inv_hom_id_app_assoc,
    hcomp]
  simp only [Functor.comp_obj, ObjectProperty.ι_obj, Category.comp_id]
  rw [finiteProjectiveModulesExtendScalarsCompιIso_hom_app,
    finiteProjectiveModulesExtendScalarsCompιIso_hom_app]

section Square

variable {A B C D : Type u} [Ring A] [Ring B] [Ring C] [Ring D]

/-- **Coherence of extension of scalars on finitely generated projective modules across a
commutative square.** Given `g₁.comp f₁ = g₂.comp f₂`, the two composite extension-of-scalars
functors are naturally isomorphic. -/
noncomputable def finiteProjectiveModulesExtendScalarsCompCongr
    (f₁ : A →+* B) (g₁ : B →+* D) (f₂ : A →+* C) (g₂ : C →+* D) (h : g₁.comp f₁ = g₂.comp f₂) :
    f₁.finiteProjectiveModulesExtendScalars ⋙ g₁.finiteProjectiveModulesExtendScalars ≅
      f₂.finiteProjectiveModulesExtendScalars ⋙ g₂.finiteProjectiveModulesExtendScalars :=
  ((finiteProjectiveModules D).fullyFaithfulι.whiskeringRight _).preimageIso
    (f₁.finiteProjectiveModulesExtendScalarsCompCompιIso g₁ ≪≫
      (finiteProjectiveModules A).ι.isoWhiskerLeft
        (BalancedExtension.functorCompCongr.{u, u, u, u, u} f₁ g₁ f₂ g₂ h) ≪≫
      (f₂.finiteProjectiveModulesExtendScalarsCompCompιIso g₂).symm)

theorem finiteProjectiveModulesExtendScalarsCompCongr_eq
    (f₁ : A →+* B) (g₁ : B →+* D) (f₂ : A →+* C) (g₂ : C →+* D) (h : g₁.comp f₁ = g₂.comp f₂) :
    finiteProjectiveModulesExtendScalarsCompCongr f₁ g₁ f₂ g₂ h =
      (f₁.finiteProjectiveModulesExtendScalarsComp g₁).symm ≪≫
        finiteProjectiveModulesExtendScalarsCongr h ≪≫
        f₂.finiteProjectiveModulesExtendScalarsComp g₂ := by
  refine Iso.ext <| ((finiteProjectiveModules D).fullyFaithfulι.whiskeringRight _).map_injective ?_
  simp [-Functor.whiskeringRight_obj_map, finiteProjectiveModulesExtendScalarsCompCongr,
    finiteProjectiveModulesExtendScalarsComp, finiteProjectiveModulesExtendScalarsCongr,
    BalancedExtension.functorCompCongr_def, Category.assoc]

@[simp] theorem finiteProjectiveModulesExtendScalarsCompCongr_hom_app_hom
    (f₁ : A →+* B) (g₁ : B →+* D) (f₂ : A →+* C) (g₂ : C →+* D)
    (h : g₁.comp f₁ = g₂.comp f₂) (P : (finiteProjectiveModules A).FullSubcategory) :
    ((finiteProjectiveModulesExtendScalarsCompCongr f₁ g₁ f₂ g₂ h).hom.app P).hom =
      eqToHom (f₁.finiteProjectiveModulesExtendScalars_comp_obj_obj g₁ P) ≫
        (BalancedExtension.functorCompCongr f₁ g₁ f₂ g₂ h).hom.app P.obj ≫
          eqToHom (f₂.finiteProjectiveModulesExtendScalars_comp_obj_obj g₂ P).symm := by
  rw [← ObjectProperty.ι_map, finiteProjectiveModulesExtendScalarsCompCongr,
    Functor.FullyFaithful.preimageIso_hom, Functor.FullyFaithful.whiskeringRight_preimage_app,
    Functor.FullyFaithful.map_preimage]
  simp [finiteProjectiveModulesExtendScalarsCompCompιIso_hom_app,
    finiteProjectiveModulesExtendScalarsCompCompιIso_inv_app]

@[simp] theorem finiteProjectiveModulesExtendScalarsCompCongr_inv_app_hom
    (f₁ : A →+* B) (g₁ : B →+* D) (f₂ : A →+* C) (g₂ : C →+* D)
    (h : g₁.comp f₁ = g₂.comp f₂) (P : (finiteProjectiveModules A).FullSubcategory) :
    ((finiteProjectiveModulesExtendScalarsCompCongr f₁ g₁ f₂ g₂ h).inv.app P).hom =
      eqToHom (f₂.finiteProjectiveModulesExtendScalars_comp_obj_obj g₂ P) ≫
        (BalancedExtension.functorCompCongr f₁ g₁ f₂ g₂ h).inv.app P.obj ≫
          eqToHom (f₁.finiteProjectiveModulesExtendScalars_comp_obj_obj g₁ P).symm := by
  rw [← ObjectProperty.ι_map, finiteProjectiveModulesExtendScalarsCompCongr,
    Functor.FullyFaithful.preimageIso_inv, Functor.FullyFaithful.whiskeringRight_preimage_app,
    Functor.FullyFaithful.map_preimage]
  simp [finiteProjectiveModulesExtendScalarsCompCompιIso_hom_app,
    finiteProjectiveModulesExtendScalarsCompCompιIso_inv_app, Category.assoc]

@[simp] theorem finiteProjectiveModulesExtendScalarsCompCongr_self (f₁ : A →+* B) (g₁ : B →+* D) :
    finiteProjectiveModulesExtendScalarsCompCongr f₁ g₁ f₁ g₁ rfl =
      Iso.refl (f₁.finiteProjectiveModulesExtendScalars ⋙
        g₁.finiteProjectiveModulesExtendScalars) := by
  refine Iso.ext <| ((finiteProjectiveModules D).fullyFaithfulι.whiskeringRight _).map_injective ?_
  simp [-Functor.whiskeringRight_obj_map, finiteProjectiveModulesExtendScalarsCompCongr]

@[simp] theorem finiteProjectiveModulesExtendScalarsCompCongr_symm
    (f₁ : A →+* B) (g₁ : B →+* D) (f₂ : A →+* C) (g₂ : C →+* D) (h : g₁.comp f₁ = g₂.comp f₂) :
    (finiteProjectiveModulesExtendScalarsCompCongr f₁ g₁ f₂ g₂ h).symm =
      finiteProjectiveModulesExtendScalarsCompCongr f₂ g₂ f₁ g₁ h.symm := by
  refine Iso.ext <| ((finiteProjectiveModules D).fullyFaithfulι.whiskeringRight _).map_injective ?_
  simp only [finiteProjectiveModulesExtendScalarsCompCongr, Iso.symm_hom,
    Functor.FullyFaithful.preimageIso_inv, Functor.FullyFaithful.preimageIso_hom,
    Functor.FullyFaithful.map_preimage, Iso.trans_hom, Iso.trans_inv, Iso.symm_inv,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerLeft_inv, Category.assoc,
    Iso.cancel_iso_hom_left, Iso.cancel_iso_inv_right]
  rw [← Iso.symm_hom, BalancedExtension.functorCompCongr_symm]

end Square

@[simp] theorem finiteProjectiveModulesExtendScalarsCompCongr_trans {A B₁ B₂ B₃ D : Type u}
    [Ring A] [Ring B₁] [Ring B₂] [Ring B₃] [Ring D]
    (f₁ : A →+* B₁) (g₁ : B₁ →+* D) (f₂ : A →+* B₂) (g₂ : B₂ →+* D) (f₃ : A →+* B₃) (g₃ : B₃ →+* D)
    (h₁₂ : g₁.comp f₁ = g₂.comp f₂) (h₂₃ : g₂.comp f₂ = g₃.comp f₃) :
    finiteProjectiveModulesExtendScalarsCompCongr f₁ g₁ f₂ g₂ h₁₂ ≪≫
        finiteProjectiveModulesExtendScalarsCompCongr f₂ g₂ f₃ g₃ h₂₃ =
      finiteProjectiveModulesExtendScalarsCompCongr f₁ g₁ f₃ g₃ (h₁₂.trans h₂₃) := by
  refine Iso.ext <| ((finiteProjectiveModules D).fullyFaithfulι.whiskeringRight _).map_injective ?_
  simp only [finiteProjectiveModulesExtendScalarsCompCongr, Iso.trans_hom, Functor.map_comp,
    Functor.FullyFaithful.preimageIso_hom, Functor.FullyFaithful.map_preimage, Iso.symm_hom,
    Functor.isoWhiskerLeft_hom, Category.assoc, Iso.inv_hom_id_assoc, Iso.cancel_iso_hom_left]
  rw [← Category.assoc, ← Functor.whiskerLeft_comp, ← Iso.trans_hom,
    BalancedExtension.functorCompCongr_trans.{u, u, u, u, u, u}]

end Coherence

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

/-- **Restriction of scalars on finitely generated projective modules, as a functor.** When `S` is
a finitely generated projective `R`-module through `f : R →+* S`, restriction of scalars along `f`
induces an additive functor from finitely generated projective `S`-modules to finitely generated
projective `R`-modules. -/
noncomputable def finiteProjectiveModulesRestrictScalars
    (hfin : letI := f.toModule; Module.Finite R S)
    (hproj : letI := f.toModule; Module.Projective R S) :
    (finiteProjectiveModules S).FullSubcategory ⥤ (finiteProjectiveModules R).FullSubcategory :=
  (finiteProjectiveModules R).lift
    ((finiteProjectiveModules S).ι ⋙ ModuleCat.restrictScalars.{u} f)
    fun M ↦ (f.finiteProjectiveModules_le_inverseImage_restrictScalars_iff.mpr
      ⟨hfin, hproj⟩) M.obj M.property

instance (hfin : letI := f.toModule; Module.Finite R S)
    (hproj : letI := f.toModule; Module.Projective R S) :
    (f.finiteProjectiveModulesRestrictScalars hfin hproj).Additive := by
  have : (f.finiteProjectiveModulesRestrictScalars hfin hproj ⋙
      (finiteProjectiveModules R).ι).Additive :=
    inferInstanceAs ((finiteProjectiveModules S).ι ⋙ ModuleCat.restrictScalars.{u} f).Additive
  exact Functor.additive_of_comp_faithful _ (finiteProjectiveModules R).ι

@[simp]
theorem finiteProjectiveModulesRestrictScalars_obj_obj
    (hfin : letI := f.toModule; Module.Finite R S)
    (hproj : letI := f.toModule; Module.Projective R S)
    (M : (finiteProjectiveModules S).FullSubcategory) :
    ((f.finiteProjectiveModulesRestrictScalars hfin hproj).obj M).obj =
      (ModuleCat.restrictScalars.{u} f).obj M.obj :=
  (rfl)

@[simp]
theorem finiteProjectiveModulesRestrictScalars_map_hom
    (hfin : letI := f.toModule; Module.Finite R S)
    (hproj : letI := f.toModule; Module.Projective R S)
    {M N : (finiteProjectiveModules S).FullSubcategory} (g : M ⟶ N) :
    ((f.finiteProjectiveModulesRestrictScalars hfin hproj).map g).hom =
      eqToHom (f.finiteProjectiveModulesRestrictScalars_obj_obj hfin hproj M) ≫
        (ModuleCat.restrictScalars.{u} f).map g.hom ≫
          eqToHom (f.finiteProjectiveModulesRestrictScalars_obj_obj hfin hproj N).symm :=
  ObjectProperty.lift_map_hom_of_eq rfl g
    (f.finiteProjectiveModulesRestrictScalars_obj_obj hfin hproj M)
    (f.finiteProjectiveModulesRestrictScalars_obj_obj hfin hproj N)

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

/-- Extension of scalars along the identity ring homomorphism induces the identity on split `K₀`. -/
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
    (g : S →+* T) (x : SplitK0.{u} (finiteProjectiveModules R).FullSubcategory) :
    SplitK0.map.{u, u} g.finiteProjectiveModulesExtendScalars
        (SplitK0.map.{u, u} f.finiteProjectiveModulesExtendScalars x) =
      SplitK0.map.{u, u} (g.comp f).finiteProjectiveModulesExtendScalars x :=
  (DFunLike.congr_fun (map_finiteProjectiveModulesExtendScalars_comp (f := f) g) x).symm

/-- **Extension of scalars on idempotent matrices in split `K₀`.** If `P` is isomorphic to the
image `Rⁿ e` of an idempotent matrix `e`, then its class is sent to the class of any finitely
generated projective `S`-module isomorphic to `Sⁿ f(e)`. -/
theorem map_finiteProjectiveModulesExtendScalars_of_linearEquiv_range {ι : Type*} [Fintype ι]
    {e : Matrix ι ι R} (he : IsIdempotentElem e)
    (P : (finiteProjectiveModules R).FullSubcategory)
    (Q : (finiteProjectiveModules S).FullSubcategory)
    (θ : P.obj ≃ₗ[R] LinearMap.range e.vecMulLinear)
    (θ' : Q.obj ≃ₗ[S] LinearMap.range (e.map f).vecMulLinear) :
    SplitK0.map.{u, u} f.finiteProjectiveModulesExtendScalars (SplitK0.of.{u} P) =
      SplitK0.of.{u} Q :=
  (SplitK0.map_of.{u, u} f.finiteProjectiveModulesExtendScalars P).trans <|
    of_extendScalars_obj ((BalancedExtension.congr f θ).trans
      ((BalancedExtension.rangeVecMulLinearEquiv f he).trans θ'.symm))

/-- Extension of scalars in split `K₀` sends the class of a free module `Rⁿ` to the class of
`Sⁿ`. -/
theorem map_finiteProjectiveModulesExtendScalars_of_linearEquiv_pi {ι : Type*} [_root_.Finite ι]
    (P : (finiteProjectiveModules R).FullSubcategory)
    (Q : (finiteProjectiveModules S).FullSubcategory)
    (θ : P.obj ≃ₗ[R] (ι → R)) (θ' : Q.obj ≃ₗ[S] (ι → S)) :
    SplitK0.map.{u, u} f.finiteProjectiveModulesExtendScalars (SplitK0.of.{u} P) =
      SplitK0.of.{u} Q :=
  have := Fintype.ofFinite ι
  (SplitK0.map_of.{u, u} f.finiteProjectiveModulesExtendScalars P).trans <|
    of_extendScalars_obj ((BalancedExtension.congr f θ).trans
      ((BalancedExtension.piScalarRight f ι).trans θ'.symm))

end TauCeti.SplitK0
