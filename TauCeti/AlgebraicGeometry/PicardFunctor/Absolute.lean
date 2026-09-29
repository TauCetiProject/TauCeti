/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Subfunctor.Image
public import TauCeti.AlgebraicGeometry.LineBundle.Rigidified.Automorphisms
public import TauCeti.AlgebraicGeometry.PicardFunctor.Rigidified

/-!
# The absolute Picard functor and its rigidified subfunctor

Let `f : X ⟶ S` be a morphism of schemes. The *absolute Picard functor* of `f` sends a scheme `T`
over `S` to the set `Pic(X_T)` of isomorphism classes of line bundles on the base change
`X_T = T ×_S X`, and a morphism `T' ⟶ T` over `S` to pullback along the induced morphism
`X_{T'} ⟶ X_T`. The relative Picard functor `T ↦ Pic(X_T) / Pic(T)` is its quotient by the
classes pulled back from `T`, and the Picard functors whose representability is studied are
sheafifications of that quotient.

When `f` has a section `x₀`, forgetting the trivialization is a natural transformation from the
rigidified Picard functor of `(X, x₀)` to the absolute Picard functor. It is injective at every
`T`: the base-changed section `x₀_T` is a section of the projection `X_T ⟶ T`, so every global
unit of `T` is the pullback along `x₀_T` of a global unit of `X_T`, and two rigidifications of the
same line bundle therefore give the same class. Its image consists of the classes of line bundles
whose pullback along `x₀_T` is trivial. Hence the rigidified Picard functor is isomorphic to the
subfunctor of the absolute Picard functor of classes trivial along the base-changed section, which
identifies rigidified classes with honest line-bundle classes on `X_T`.

## Main declarations

* `TauCeti.AlgebraicGeometry.absolutePicardFunctor`: the functor `T ↦ Pic(X_T)` on schemes over
  `S`;
* `TauCeti.AlgebraicGeometry.trivialAlongSectionSubfunctor`: its subfunctor of classes whose
  pullback along the base-changed section is trivial;
* `TauCeti.AlgebraicGeometry.forgetRigidification`: the natural transformation forgetting the
  trivialization, a monomorphism (`mono_forgetRigidification`) with range
  `trivialAlongSectionSubfunctor` (`range_forgetRigidification`);
* `TauCeti.AlgebraicGeometry.rigidifiedPicardFunctorIsoTrivialAlongSection`: the resulting
  isomorphism of the rigidified Picard functor with `trivialAlongSectionSubfunctor`.

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

section Absolute

variable {S X : Scheme.{u}} (f : X ⟶ S)

/-- The **absolute Picard functor** of `f : X ⟶ S`: it sends a scheme `T` over `S` to the
isomorphism classes of line bundles on `X_T = T ×_S X`, and a morphism over `S` to pullback along
the induced morphism of base changes. -/
-- Expose the object type so the functor's action can be stated directly on line-bundle classes.
@[expose]
def absolutePicardFunctor : (Over S)ᵒᵖ ⥤ Type (u + 1) where
  obj T := LineBundleClass (pullback T.unop.hom f)
  map φ := TypeCat.ofHom (LineBundleClass.pullback ((Over.pullback f).map φ.unop).left)
  map_id T := by
    ext a
    simp
  map_comp φ ψ := by
    ext a
    simp

/-- The value of the absolute Picard functor at `T` is the set of line-bundle classes on `X_T`. -/
@[simp]
lemma absolutePicardFunctor_obj (T : (Over S)ᵒᵖ) :
    (absolutePicardFunctor f).obj T = LineBundleClass (pullback T.unop.hom f) :=
  rfl

/-- The absolute Picard functor acts by pullback along the induced map of base changes. -/
lemma absolutePicardFunctor_map {T T' : (Over S)ᵒᵖ} (φ : T ⟶ T') :
    (absolutePicardFunctor f).map φ =
      TypeCat.ofHom (LineBundleClass.pullback ((Over.pullback f).map φ.unop).left) :=
  rfl

/-- The absolute Picard functor acts on a class by pulling it back along the induced morphism of
base changes. -/
@[simp]
lemma absolutePicardFunctor_map_apply {T T' : (Over S)ᵒᵖ} (φ : T ⟶ T')
    (a : LineBundleClass (pullback T.unop.hom f)) :
    (@ConcreteCategory.hom _ _ _ _ _ _
      (LineBundleClass (pullback T.unop.hom f))
      (LineBundleClass (pullback T'.unop.hom f))
      ((absolutePicardFunctor f).map φ)) a =
      LineBundleClass.pullback ((Over.pullback f).map φ.unop).left a :=
  rfl

end Absolute

section Rigidified

variable {S X : Scheme.{u}} (f : X ⟶ S) (x₀ : S ⟶ X) (hx₀ : x₀ ≫ f = 𝟙 S)

/-- Pulling back along the base-changed section commutes with the action of the absolute Picard
functor: along `φ : T' ⟶ T` over `S`, pulling back to `X_{T'}` and then along `x₀_{T'}` agrees with
pulling back along `x₀_T` and then along `T' ⟶ T`. -/
lemma pullback_baseChangeSection_absolutePicardFunctor_map {T T' : (Over S)ᵒᵖ} (φ : T ⟶ T')
    (a : (absolutePicardFunctor f).obj T) :
    LineBundleClass.pullback (baseChangeSection f x₀ hx₀ T'.unop)
        ((absolutePicardFunctor f).map φ a) =
      LineBundleClass.pullback φ.unop.left
        (LineBundleClass.pullback (baseChangeSection f x₀ hx₀ T.unop) a) := by
  -- `a` is typed by the functor's object, so the composition law is applied as a term.
  change LineBundleClass.pullback (baseChangeSection f x₀ hx₀ T'.unop)
      (LineBundleClass.pullback ((Over.pullback f).map φ.unop).left a) = _
  refine (LineBundleClass.pullback_comp _ _ a).trans ?_
  rw [baseChangeSection_comp_pullback_map]
  exact (LineBundleClass.pullback_comp _ _ a).symm

/-- The subfunctor of the absolute Picard functor of `f` consisting, over `T`, of the classes of
line bundles on `X_T` whose pullback along the base-changed section `x₀_T` is trivial: the classes
admitting a rigidification along `x₀_T`. -/
def trivialAlongSectionSubfunctor : Subfunctor (absolutePicardFunctor f) where
  obj T := {a | LineBundleClass.pullback (baseChangeSection f x₀ hx₀ T.unop) a = 1}
  map {T T'} φ a (ha : LineBundleClass.pullback _ a = 1) := by
    have h := pullback_baseChangeSection_absolutePicardFunctor_map f x₀ hx₀ φ a
    rw [ha, LineBundleClass.pullback_one] at h
    exact h

/-- A class lies in the subfunctor exactly when its pullback along the base-changed section is
trivial. -/
@[simp]
lemma mem_trivialAlongSectionSubfunctor_obj_iff {T : (Over S)ᵒᵖ}
    (a : (absolutePicardFunctor f).obj T) :
    a ∈ (trivialAlongSectionSubfunctor f x₀ hx₀).obj T ↔
      LineBundleClass.pullback (baseChangeSection f x₀ hx₀ T.unop) a = 1 :=
  Iff.rfl

/-- Forgetting the trivialization, as a natural transformation from the rigidified Picard functor
of `(X, x₀)` to the absolute Picard functor of `f`. -/
def forgetRigidification : rigidifiedPicardFunctor f x₀ hx₀ ⟶ absolutePicardFunctor f where
  app _ := TypeCat.ofHom RigidifiedLineBundleClass.toLineBundleClass
  naturality _ _ φ := by
    ext a
    exact RigidifiedLineBundleClass.toLineBundleClass_pullback _ a

/-- Forgetting the trivialization sends a rigidified class to its underlying line-bundle class. -/
@[simp]
lemma forgetRigidification_app_apply (T : (Over S)ᵒᵖ)
    (a : RigidifiedLineBundleClass (baseChangeSection f x₀ hx₀ T.unop)) :
    (@ConcreteCategory.hom _ _ _ _ _ _
      (RigidifiedLineBundleClass (baseChangeSection f x₀ hx₀ T.unop))
      (LineBundleClass (pullback T.unop.hom f))
      ((forgetRigidification f x₀ hx₀).app T)) a =
      RigidifiedLineBundleClass.toLineBundleClass a :=
  (rfl)

/-- Forgetting the trivialization is injective on rigidified classes over every `T`, because the
base-changed section is a section of the projection `X_T ⟶ T`. -/
lemma forgetRigidification_app_injective (T : (Over S)ᵒᵖ) :
    Function.Injective ((forgetRigidification f x₀ hx₀).app T) :=
  RigidifiedLineBundleClass.toLineBundleClass_injective_of_comp_eq_id
    (baseChangeSection_fst f x₀ hx₀ T.unop)

/-- Forgetting the trivialization is a monomorphism of functors. -/
instance mono_forgetRigidification : Mono (forgetRigidification f x₀ hx₀) :=
  have (T : (Over S)ᵒᵖ) : Mono ((forgetRigidification f x₀ hx₀).app T) :=
    (mono_iff_injective _).mpr (forgetRigidification_app_injective f x₀ hx₀ T)
  NatTrans.mono_of_mono_app _

/-- The line-bundle classes underlying rigidified classes are exactly those that are trivial along
the base-changed section. -/
lemma range_forgetRigidification :
    Subfunctor.range (forgetRigidification f x₀ hx₀) = trivialAlongSectionSubfunctor f x₀ hx₀ := by
  ext T a
  rw [Subfunctor.range_obj, mem_trivialAlongSectionSubfunctor_obj_iff]
  -- The component of `forgetRigidification` is `toLineBundleClass`, whose range is known.
  exact Set.ext_iff.mp RigidifiedLineBundleClass.range_toLineBundleClass a

/-- The rigidified Picard functor of `(X, x₀)` is isomorphic to the subfunctor of the absolute
Picard functor of classes of line bundles trivial along the base-changed section. -/
def rigidifiedPicardFunctorIsoTrivialAlongSection :
    rigidifiedPicardFunctor f x₀ hx₀ ≅ (trivialAlongSectionSubfunctor f x₀ hx₀).toFunctor :=
  have : IsIso (Subfunctor.lift (forgetRigidification f x₀ hx₀)
      (range_forgetRigidification f x₀ hx₀).le) := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro T
    rw [isIso_iff_bijective]
    refine ⟨fun a b hab ↦ forgetRigidification_app_injective f x₀ hx₀ T
      (congrArg Subtype.val hab), fun ⟨a, ha⟩ ↦ ?_⟩
    rw [← range_forgetRigidification, Subfunctor.range_obj] at ha
    obtain ⟨b, rfl⟩ := ha
    exact ⟨b, rfl⟩
  asIso (Subfunctor.lift (forgetRigidification f x₀ hx₀) (range_forgetRigidification f x₀ hx₀).le)

/-- The isomorphism followed by the inclusion of the subfunctor is forgetting the
trivialization. -/
@[reassoc (attr := simp)]
lemma rigidifiedPicardFunctorIsoTrivialAlongSection_hom_ι :
    (rigidifiedPicardFunctorIsoTrivialAlongSection f x₀ hx₀).hom ≫
        (trivialAlongSectionSubfunctor f x₀ hx₀).ι = forgetRigidification f x₀ hx₀ :=
  (rfl)

end Rigidified

end

end AlgebraicGeometry

end TauCeti
