/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.LineBundle.Rigidified
public import TauCeti.CategoryTheory.Limits.Shapes.Pullback.SplitEpi
public import Mathlib.CategoryTheory.Comma.Over.Pullback

/-!
# The rigidified Picard functor

Let `f : X ⟶ S` be a morphism of schemes with a section `x₀ : S ⟶ X`. For a scheme `T` over `S`,
the base change `X_T = T ×_S X` of `X` has the section `x₀_T : T ⟶ X_T` induced by `x₀`. The
*rigidified Picard functor* of `(X, x₀)` sends `T` to the set of isomorphism classes of line
bundles on `X_T` rigidified along `x₀_T`: line bundles `L` on `X_T` together with a trivialization
`x₀_T^* L ≅ 𝒪_T`, up to isomorphisms of line bundles respecting the trivializations. A morphism
`T' ⟶ T` over `S` acts by pullback along the induced morphism `X_{T'} ⟶ X_T`.

The rigidification is how the section `x₀` enters the construction of the Picard scheme: when
`f_* 𝒪_X = 𝒪_S` holds universally, a rigidified line bundle has no automorphisms other than the
identity, and the rigidified functor is the relative Picard functor `T ↦ Pic(X_T) / Pic(T)`.
Neither statement is proved in this file, which constructs the functor.

## Main declarations

* `TauCeti.AlgebraicGeometry.baseChangeSection`: the section `x₀_T : T ⟶ X_T`;
* `TauCeti.AlgebraicGeometry.rigidifiedPicardFunctor`: the rigidified Picard functor
  `(Over S)ᵒᵖ ⥤ Type`, with `rigidifiedPicardFunctor_map` computing its action on classes and
  `rigidifiedPicardFunctor_map_mk` on representatives.

## References

* S. Bosch, W. Lütkebohmert, M. Raynaud, *Néron Models*, Section 8.1.
* S. Kleiman, *The Picard scheme*, in *Fundamental Algebraic Geometry: Grothendieck's FGA
  Explained*, Section 9.2.
-/

public section

open CategoryTheory Limits

namespace TauCeti

namespace AlgebraicGeometry

open _root_.AlgebraicGeometry

universe u

noncomputable section

variable {S X : Scheme.{u}} (f : X ⟶ S) (x₀ : S ⟶ X) (hx₀ : x₀ ≫ f = 𝟙 S)

/-- The base change `x₀_T : T ⟶ T ×_S X` of a section `x₀` of `f : X ⟶ S` to a scheme `T` over
`S`. -/
def baseChangeSection (T : Over S) : T.left ⟶ pullback T.hom f :=
  ((⟨x₀, hx₀⟩ : SplitEpi f).pullback T.hom).section_ ≫
    (pullbackSymmetry f T.hom).hom

/-- The base-changed section is a section of the projection `T ×_S X ⟶ T`. -/
@[reassoc (attr := simp)]
lemma baseChangeSection_fst (T : Over S) :
    baseChangeSection f x₀ hx₀ T ≫ pullback.fst T.hom f = 𝟙 T.left :=
  by simp [baseChangeSection, Category.assoc]

/-- The base-changed section followed by the projection to `X` is `T ⟶ S ⟶ X`. -/
@[reassoc (attr := simp)]
lemma baseChangeSection_snd (T : Over S) :
    baseChangeSection f x₀ hx₀ T ≫ pullback.snd T.hom f = T.hom ≫ x₀ :=
  by simp [baseChangeSection, Category.assoc]

/-- The base-changed sections are compatible with the morphisms `T' ×_S X ⟶ T ×_S X` induced by
morphisms `T' ⟶ T` over `S`. -/
@[reassoc]
lemma baseChangeSection_comp_pullback_map {T' T : Over S} (φ : T' ⟶ T) :
    baseChangeSection f x₀ hx₀ T' ≫
        ((Over.pullback f).map φ).left =
      φ.left ≫ baseChangeSection f x₀ hx₀ T := by
  let h : SplitEpi f := ⟨x₀, hx₀⟩
  have hcomm : (pullbackSymmetry f T'.hom).hom ≫ ((Over.pullback f).map φ).left =
      pullback.map f T'.hom f T.hom (𝟙 X) φ.left (𝟙 S) (by simp)
        (by simp [Over.w φ]) ≫ (pullbackSymmetry f T.hom).hom := by
    apply pullback.hom_ext
    · simp only [Over.pullback_map_left]
      rw [pullback.map]
      simp only [Category.assoc, pullback.lift_fst, pullback.lift_snd,
        pullbackSymmetry_hom_comp_fst]
      rw [← Category.assoc, pullbackSymmetry_hom_comp_fst]
    · simp only [Over.pullback_map_left]
      rw [pullback.map]
      simp only [Category.assoc, pullback.lift_fst, pullback.lift_snd,
        pullbackSymmetry_hom_comp_snd]
      simp
  have hsection : (h.pullback T'.hom).section_ ≫
      pullback.map f T'.hom f T.hom (𝟙 X) φ.left (𝟙 S) (by simp)
        (by simp [Over.w φ]) = φ.left ≫ (h.pullback T.hom).section_ := by
    exact h.pullback_section_map_of_eq T.hom T'.hom φ.left (Over.w φ)
  simp only [baseChangeSection, hcomm, Category.assoc]
  exact congrArg (· ≫ (pullbackSymmetry f T.hom).hom) hsection

/-- The **rigidified Picard functor** of a morphism `f : X ⟶ S` with a section `x₀`: it sends a
scheme `T` over `S` to the isomorphism classes of line bundles on `X_T = T ×_S X` rigidified along
the base-changed section `x₀_T`, and a morphism over `S` to pullback along the induced morphism of
base changes. -/
-- `@[expose]`: the value of the functor at `T` must reduce to classes of rigidified line bundles
-- for its action on such classes (`rigidifiedPicardFunctor_map_mk`) to be stated.
@[expose]
def rigidifiedPicardFunctor : (Over S)ᵒᵖ ⥤ Type (u + 1) where
  obj T := RigidifiedLineBundleClass (baseChangeSection f x₀ hx₀ T.unop)
  map φ := TypeCat.ofHom <| RigidifiedLineBundleClass.pullback
    (baseChangeSection_comp_pullback_map f x₀ hx₀ φ.unop)
  map_id T := by
    ext a
    simp only [TypeCat.Fun.toFun_apply, TypeCat.ofHom_apply, types_id_apply]
    exact RigidifiedLineBundleClass.pullback_id (by simp) (by simp) _ a
  map_comp φ ψ := by
    ext a
    simp only [TypeCat.Fun.toFun_apply, TypeCat.ofHom_apply, types_comp_apply]
    refine (RigidifiedLineBundleClass.pullback_comp ?_ (by simp) _ _ _ a).symm
    rw [← Over.comp_left, ← Functor.map_comp, ← unop_comp]

/-- The value of the rigidified Picard functor at `T` is the set of classes of line bundles on
`X_T` rigidified along the base-changed section. -/
lemma rigidifiedPicardFunctor_obj (T : (Over S)ᵒᵖ) :
    (rigidifiedPicardFunctor f x₀ hx₀).obj T =
      RigidifiedLineBundleClass (baseChangeSection f x₀ hx₀ T.unop) :=
  rfl

/-- The rigidified Picard functor acts on every class by pullback along the induced map of base
changes. -/
lemma rigidifiedPicardFunctor_map {T T' : (Over S)ᵒᵖ} (φ : T ⟶ T')
    (a : RigidifiedLineBundleClass (baseChangeSection f x₀ hx₀ T.unop)) :
    (rigidifiedPicardFunctor f x₀ hx₀).map φ a =
      RigidifiedLineBundleClass.pullback
        (baseChangeSection_comp_pullback_map f x₀ hx₀ φ.unop) a :=
  rfl

/-- The rigidified Picard functor acts on the class of a rigidified line bundle by pulling it
back along the induced morphism of base changes. -/
@[simp]
lemma rigidifiedPicardFunctor_map_mk {T T' : (Over S)ᵒᵖ} (φ : T ⟶ T')
    (P : RigidifiedLineBundle (baseChangeSection f x₀ hx₀ T.unop)) :
    (rigidifiedPicardFunctor f x₀ hx₀).map φ (RigidifiedLineBundleClass.mk P) =
      RigidifiedLineBundleClass.mk (RigidifiedLineBundle.pullback
        (baseChangeSection_comp_pullback_map f x₀ hx₀ φ.unop) P) :=
  (rigidifiedPicardFunctor_map f x₀ hx₀ φ _).trans
    (RigidifiedLineBundleClass.pullback_mk _ P)

end

end AlgebraicGeometry

end TauCeti
