/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.LineBundle.Rigidified.TensorProduct
public import TauCeti.AlgebraicGeometry.BaseChangeSection
public import Mathlib.Algebra.Category.Grp.Basic

/-!
# The rigidified Picard functor

Let `f : X ⟶ S` be a morphism of schemes with a section `x₀ : S ⟶ X`. For a scheme `T` over `S`,
the base change `X_T = T ×_S X` of `X` has the section `x₀_T : T ⟶ X_T` induced by `x₀`. The
*rigidified Picard functor* of `(X, x₀)` sends `T` to the set of isomorphism classes of line
bundles on `X_T` rigidified along `x₀_T`: line bundles `L` on `X_T` together with a trivialization
`x₀_T^* L ≅ 𝒪_T`, up to isomorphisms of line bundles respecting the trivializations. These classes
form a commutative group under tensor product
(`TauCeti.AlgebraicGeometry.LineBundle.Rigidified.TensorProduct`), and a morphism `T' ⟶ T` over
`S` acts by the group homomorphism of pullback along the induced morphism `X_{T'} ⟶ X_T`.

The rigidification is how the section `x₀` enters the construction of the Picard scheme: when
`f_* 𝒪_X = 𝒪_S` holds universally, a rigidified line bundle has no automorphisms other than the
identity, and for every section the rigidified functor is the relative Picard presheaf
`T ↦ Pic(X_T) / Pic(T)`. The first statement is the rigidity theorem
`TauCeti.AlgebraicGeometry.RigidifiedLineBundle.autSubgroup_eq_bot_iff` of the separate module
`TauCeti.AlgebraicGeometry.LineBundle.Rigidified.Automorphisms`, which this file does not import;
it identifies the automorphisms of a rigidified line bundle with the kernel of the pullback of
global units along the section. The second statement is
`TauCeti.AlgebraicGeometry.rigidifiedPicardFunctorIso` of the module
`TauCeti.AlgebraicGeometry.PicardFunctor.Relative`; this file constructs the functor.

## Main declarations

* `TauCeti.AlgebraicGeometry.rigidifiedPicardFunctor`: the rigidified Picard functor
  `(Over S)ᵒᵖ ⥤ CommGrpCat`, with `rigidifiedPicardFunctor_map_apply` computing its action on
  classes and `rigidifiedPicardFunctor_map_mk` on representatives.

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

/-- The **rigidified Picard functor** of a morphism `f : X ⟶ S` with a section `x₀`: it sends a
scheme `T` over `S` to the commutative group, under tensor product, of isomorphism classes of line
bundles on `X_T = T ×_S X` rigidified along the base-changed section `x₀_T`, and a morphism over `S`
to pullback along the induced morphism of base changes. -/
-- Expose the object type so the functor's action can be stated directly on rigidified classes.
@[expose]
def rigidifiedPicardFunctor : (Over S)ᵒᵖ ⥤ CommGrpCat.{u + 1} where
  obj T := CommGrpCat.of (RigidifiedLineBundleClass (baseChangeSection f x₀ hx₀ T.unop))
  map φ := CommGrpCat.ofHom <| RigidifiedLineBundleClass.pullbackHom
    (baseChangeSection_comp_pullback_map f x₀ hx₀ φ.unop)
  map_id T := by
    ext a
    simpa using RigidifiedLineBundleClass.pullback_id (by simp) (by simp) _ a
  map_comp φ ψ := by
    ext a
    simp only [CommGrpCat.hom_comp, CommGrpCat.hom_ofHom, MonoidHom.coe_comp,
      Function.comp_apply, RigidifiedLineBundleClass.pullbackHom_apply]
    refine (RigidifiedLineBundleClass.pullback_comp ?_ (by simp) _ _ _ a).symm
    rw [← Over.comp_left, ← Functor.map_comp, ← unop_comp]

/-- The value of the rigidified Picard functor at `T` is the group of classes of line bundles on
`X_T` rigidified along the base-changed section. -/
lemma rigidifiedPicardFunctor_obj (T : (Over S)ᵒᵖ) :
    (rigidifiedPicardFunctor f x₀ hx₀).obj T =
      CommGrpCat.of (RigidifiedLineBundleClass (baseChangeSection f x₀ hx₀ T.unop)) :=
  rfl

/-- The rigidified Picard functor acts by pullback along the induced map of base changes. -/
@[simp]
lemma rigidifiedPicardFunctor_map_apply {T T' : (Over S)ᵒᵖ} (φ : T ⟶ T')
    (a : RigidifiedLineBundleClass (baseChangeSection f x₀ hx₀ T.unop)) :
    (rigidifiedPicardFunctor f x₀ hx₀).map φ a = RigidifiedLineBundleClass.pullback
      (baseChangeSection_comp_pullback_map f x₀ hx₀ φ.unop) a :=
  RigidifiedLineBundleClass.pullbackHom_apply _ a

/-- The rigidified Picard functor acts on the class of a rigidified line bundle by pulling it
back along the induced morphism of base changes. -/
lemma rigidifiedPicardFunctor_map_mk {T T' : (Over S)ᵒᵖ} (φ : T ⟶ T')
    (P : RigidifiedLineBundle (baseChangeSection f x₀ hx₀ T.unop)) :
    (rigidifiedPicardFunctor f x₀ hx₀).map φ (RigidifiedLineBundleClass.mk P) =
      RigidifiedLineBundleClass.mk (RigidifiedLineBundle.pullback
        (baseChangeSection_comp_pullback_map f x₀ hx₀ φ.unop) P) := by
  rw [rigidifiedPicardFunctor_map_apply]
  exact RigidifiedLineBundleClass.pullback_mk _ P

end

end AlgebraicGeometry

end TauCeti
