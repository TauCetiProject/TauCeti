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

variable (f) in
/-- The class of `S ⊗_R R` is the class `[S]` of the free module of rank one. -/
@[simp]
theorem of_extendScalars_obj_finiteProjectiveModulesRegular :
    SplitK0.of.{u} (f.finiteProjectiveModulesExtendScalars.obj (finiteProjectiveModulesRegular R)) =
      SplitK0.of.{u} (finiteProjectiveModulesRegular S) :=
  of_extendScalars_obj (BalancedExtension.rid f)

end TauCeti.SplitK0
