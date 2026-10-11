/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.PicardFunctor.Rigidified
public import TauCeti.AlgebraicGeometry.LineBundle.Rigidified.Automorphisms
public import Mathlib.Algebra.Category.Grp.Basic

/-!
# The relative Picard presheaf and the rigidified Picard functor

Let `f : X ⟶ S` be a morphism of schemes. The *relative Picard presheaf* of `f` sends a scheme `T`
over `S` to the quotient `Pic(X_T) / Pic(T)` of the Picard group of the base change
`X_T = T ×_S X` by the line-bundle classes pulled back from `T`, and a morphism `T' ⟶ T` over `S`
to pullback along the induced morphism `X_{T'} ⟶ X_T`. The relative Picard functor `Pic_{X/S}`
is its sheafification for the fppf (or étale) topology.

When `f` has a section `x₀`, the presheaf `T ↦ Pic(X_T) / Pic(T)` is already the rigidified Picard
functor: forgetting the rigidification is a natural bijection from the classes of line bundles on
`X_T` rigidified along the base-changed section `x₀_T` onto `Pic(X_T) / Pic(T)`. Pointwise this is
a statement about any section `s` of a morphism `p : Y ⟶ T`: forgetting the rigidification is
injective on classes rigidified along `s`, with image the kernel of `s^* : Pic(Y) → Pic(T)`, and
`p^*` splits `s^*`, so that this kernel maps isomorphically onto `Pic(Y) / p^* Pic(T)`
(`TauCeti.AlgebraicGeometry.RigidifiedLineBundleClass.mk_toLineBundleClass_bijective`). No
hypothesis on `f` beyond the existence of the section is needed.

## Main declarations

* `TauCeti.AlgebraicGeometry.relativePicardPresheaf`: the presheaf of commutative groups
  `T ↦ Pic(X_T) / Pic(T)` on schemes over `S`;
* `TauCeti.AlgebraicGeometry.rigidifiedPicardFunctorIso`: the rigidified Picard functor of
  `(X, x₀)` is naturally isomorphic to the underlying presheaf of sets of the relative Picard
  presheaf.

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

variable {S X : Scheme.{u}} (f : X ⟶ S)

/-- Pullback along the morphism `X_{T'} ⟶ X_T` induced by `φ : T' ⟶ T` over `S` carries the
line-bundle classes pulled back from `T` to line-bundle classes pulled back from `T'`. -/
lemma range_pullbackHom_fst_le_comap {T' T : Over S} (φ : T' ⟶ T) :
    (LineBundleClass.pullbackHom (pullback.fst T.hom f)).range ≤
      (LineBundleClass.pullbackHom (pullback.fst T'.hom f)).range.comap
        (LineBundleClass.pullbackHom ((Over.pullback f).map φ).left) := by
  rintro _ ⟨c, rfl⟩
  refine ⟨LineBundleClass.pullbackHom φ.left c, ?_⟩
  simp only [← MonoidHom.comp_apply, LineBundleClass.pullbackHom_comp, Over.pullback_map_left,
    pullback.lift_fst]

/-- The **relative Picard presheaf** of a morphism `f : X ⟶ S`: it sends a scheme `T` over `S` to
the quotient `Pic(X_T) / Pic(T)` of the Picard group of `X_T = T ×_S X` by the classes pulled back
along the projection `X_T ⟶ T`, and a morphism over `S` to pullback along the induced morphism of
base changes. -/
-- Expose the object type so elements can be written as classes of line bundles on `X_T`.
@[expose]
def relativePicardPresheaf : (Over S)ᵒᵖ ⥤ CommGrpCat.{u + 1} where
  obj T := CommGrpCat.of (LineBundleClass (pullback T.unop.hom f) ⧸
    (LineBundleClass.pullbackHom (pullback.fst T.unop.hom f)).range)
  map φ := CommGrpCat.ofHom <| QuotientGroup.map _ _
    (LineBundleClass.pullbackHom ((Over.pullback f).map φ.unop).left)
    (range_pullbackHom_fst_le_comap f φ.unop)
  map_id T := by
    ext a
    simp
  map_comp φ ψ := by
    ext a
    simp

/-- The value of the relative Picard presheaf at `T` is `Pic(X_T) / Pic(T)`. -/
lemma relativePicardPresheaf_obj (T : (Over S)ᵒᵖ) :
    (relativePicardPresheaf f).obj T = CommGrpCat.of (LineBundleClass (pullback T.unop.hom f) ⧸
      (LineBundleClass.pullbackHom (pullback.fst T.unop.hom f)).range) :=
  rfl

/-- The relative Picard presheaf acts on the image of a line-bundle class on `X_T` by pulling it
back along the induced morphism of base changes. -/
@[simp]
lemma relativePicardPresheaf_map_mk {T T' : (Over S)ᵒᵖ} (φ : T ⟶ T')
    (a : LineBundleClass (pullback T.unop.hom f)) :
    (relativePicardPresheaf f).map φ (QuotientGroup.mk a) =
      QuotientGroup.mk (LineBundleClass.pullback ((Over.pullback f).map φ.unop).left a) :=
  (QuotientGroup.map_mk _ _ _ (range_pullbackHom_fst_le_comap f φ.unop) a).trans
    (by rw [LineBundleClass.pullbackHom_apply])

variable (x₀ : S ⟶ X) (hx₀ : x₀ ≫ f = 𝟙 S)

/-- **The rigidified Picard functor is the relative Picard presheaf.** For a morphism
`f : X ⟶ S` with a section `x₀`, forgetting the rigidification identifies the classes of line
bundles on `X_T` rigidified along `x₀_T` with `Pic(X_T) / Pic(T)`, naturally in the scheme `T`
over `S`. -/
def rigidifiedPicardFunctorIso :
    rigidifiedPicardFunctor f x₀ hx₀ ≅ relativePicardPresheaf f ⋙ forget CommGrpCat :=
  NatIso.ofComponents (fun T ↦ (Equiv.ofBijective
    (fun a : (rigidifiedPicardFunctor f x₀ hx₀).obj T ↦
      (QuotientGroup.mk (RigidifiedLineBundleClass.toLineBundleClass a) :
        (relativePicardPresheaf f).obj T))
    (RigidifiedLineBundleClass.mk_toLineBundleClass_bijective
      (baseChangeSection_fst f x₀ hx₀ T.unop))).toIso) (by
      intro T T' φ
      ext a
      -- Both components send a class to the image of its underlying line-bundle class (by
      -- definition of `Equiv.ofBijective` and `Equiv.toIso`; the rewriting lemmas for these do not
      -- apply because the objects of the functors only unfold to the carriers at default
      -- transparency), so naturality is compatibility of forgetting the rigidification with
      -- pullback.
      exact (congrArg QuotientGroup.mk
        (RigidifiedLineBundleClass.toLineBundleClass_pullback _ a)).trans
          (relativePicardPresheaf_map_mk f φ _).symm)

/-- The comparison `rigidifiedPicardFunctorIso` sends the class of a rigidified line bundle to the
image of its underlying line-bundle class. -/
lemma rigidifiedPicardFunctorIso_hom_app (T : (Over S)ᵒᵖ)
    (a : (rigidifiedPicardFunctor f x₀ hx₀).obj T) :
    (rigidifiedPicardFunctorIso f x₀ hx₀).hom.app T a =
      (QuotientGroup.mk (RigidifiedLineBundleClass.toLineBundleClass a) :
        (relativePicardPresheaf f).obj T) :=
  (rfl)

end

end AlgebraicGeometry

end TauCeti
