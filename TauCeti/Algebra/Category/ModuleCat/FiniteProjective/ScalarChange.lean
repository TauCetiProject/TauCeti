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
  `ℤ`-module that is not finitely generated.

The module-level statements are the `Module.Finite` and `Module.Projective` instances on
`TauCeti.BalancedExtension f P`, and `RingHom.isFG_restrictScalars_of_finite` together with
`RingHom.projective_restrictScalars_of_projective`.

## Main definitions

* `RingHom.finiteProjectiveModulesExtendScalars`: extension of scalars as an additive functor
  between the categories of finitely generated projective modules.

## Main results

* `TauCeti.SplitK0.of_extendScalars_obj`: the split `K₀` class of an extended module agrees
  with the class of any module linearly isomorphic to its balanced extension.
* `TauCeti.BalancedExtension.finiteProjectiveModules_le_inverseImage_functor`: extension of
  scalars preserves finitely generated projective modules.
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
