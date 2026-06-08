/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TauCeti.Algebra.AlgebraicGroup.FunctorOfPoints

/-!
# Functoriality in the coordinate Hopf algebra

`TauCeti.Algebra.AlgebraicGroup.FunctorOfPoints` gives the convolution group on
`WithConv (H →ₐ[R] A)`, functorial in the value algebra `A`. This file adds the other
variance needed for the functor-of-points dictionary: a bialgebra morphism
`φ : H₁ →ₐc[R] H₂` induces, by pre-composition, a monoid homomorphism
`WithConv (H₂ →ₐ[R] A) →* WithConv (H₁ →ₐ[R] A)`.

For a commutative Hopf algebra `H`, this is the contravariant functoriality of
`A ↦ Hom_R(H, A)` in the coordinate Hopf algebra. It is one of the formal pieces needed by
the reductive-groups roadmap Layer 0 target "R-points as a group" and its follow-up
"the functor of points" dictionary.

## Main declarations

* `AlgHom.mapDomain`: pre-composition by a bialgebra morphism as a monoid homomorphism of
  convolution monoids.
* `AlgHom.mapDomain_id` and `AlgHom.mapDomain_comp`: identity and composition laws.
* `AlgHom.mapValue_mapDomain`: pre-composition in the coordinate algebra commutes with
  post-composition in the value algebra.
* `AlgHom.mapDomain_inv_apply`: pointwise inverse formula after pre-composition.

The convolution-preservation proof reuses Mathlib's
`AlgHom.convMul_comp_bialgHom_distrib`, from `Mathlib.RingTheory.Bialgebra.Convolution`.
-/

open WithConv

namespace TauCeti

namespace AlgHom

variable {R H₁ H₂ H₃ A B : Type*} [CommSemiring R]

section Bialgebra

variable [CommSemiring H₁] [Semiring H₂]
variable [_root_.Bialgebra R H₁] [_root_.Bialgebra R H₂]
variable [CommSemiring A] [Algebra R A]

/-- Contravariant functoriality of convolution algebra homomorphisms in the source
bialgebra. A bialgebra morphism `φ : H₁ →ₐc[R] H₂` sends an `A`-valued point of `H₂` to an
`A`-valued point of `H₁` by pre-composition. -/
noncomputable def mapDomain (φ : H₁ →ₐc[R] H₂) :
    WithConv (H₂ →ₐ[R] A) →* WithConv (H₁ →ₐ[R] A) where
  toFun f := toConv (f.ofConv.comp (φ : H₁ →ₐ[R] H₂))
  map_one' := by
    ext x
    simp
  map_mul' f g := by
    ext x
    have h := congrFun (congrArg DFunLike.coe (AlgHom.convMul_comp_bialgHom_distrib f g φ)) x
    simpa using h

/-- `mapDomain φ` acts pointwise by pre-composition with `φ`. -/
@[simp]
lemma mapDomain_apply (φ : H₁ →ₐc[R] H₂) (f : WithConv (H₂ →ₐ[R] A)) :
    mapDomain φ f = toConv (f.ofConv.comp (φ : H₁ →ₐ[R] H₂)) := rfl

/-- Pointwise form of `mapDomain_apply`. -/
lemma mapDomain_apply_apply (φ : H₁ →ₐc[R] H₂) (f : WithConv (H₂ →ₐ[R] A)) (h : H₁) :
    mapDomain φ f h = f.ofConv (φ h) := rfl

end Bialgebra

section BialgebraId

variable [CommSemiring H₁] [_root_.Bialgebra R H₁]
variable [CommSemiring A] [Algebra R A]

/-- Pre-composition by the identity bialgebra morphism is the identity map on the
convolution monoid. -/
@[simp]
lemma mapDomain_id :
    (mapDomain (BialgHom.id R H₁) : WithConv (H₁ →ₐ[R] A) →* WithConv (H₁ →ₐ[R] A)) =
      MonoidHom.id (WithConv (H₁ →ₐ[R] A)) := by
  refine MonoidHom.ext fun f => ?_
  rw [mapDomain_apply, BialgHom.id_toAlgHom, AlgHom.comp_id, toConv_ofConv,
    MonoidHom.id_apply]

end BialgebraId

section BialgebraComp

variable [CommSemiring H₁] [CommSemiring H₂] [Semiring H₃]
variable [_root_.Bialgebra R H₁] [_root_.Bialgebra R H₂] [_root_.Bialgebra R H₃]
variable [CommSemiring A] [Algebra R A]

/-- Pre-composition by a composite bialgebra morphism is the composite of the corresponding
pre-composition maps. -/
lemma mapDomain_comp (ψ : H₂ →ₐc[R] H₃) (φ : H₁ →ₐc[R] H₂) :
    (mapDomain (H₁ := H₁) (H₂ := H₃) (ψ.comp φ) :
        WithConv (H₃ →ₐ[R] A) →* WithConv (H₁ →ₐ[R] A)) =
      (mapDomain (H₁ := H₁) (H₂ := H₂) φ :
          WithConv (H₂ →ₐ[R] A) →* WithConv (H₁ →ₐ[R] A)).comp
        (mapDomain (H₁ := H₂) (H₂ := H₃) ψ :
          WithConv (H₃ →ₐ[R] A) →* WithConv (H₂ →ₐ[R] A)) := by
  refine MonoidHom.ext fun f => ?_
  rw [MonoidHom.comp_apply, mapDomain_apply, mapDomain_apply, mapDomain_apply,
    toConv_ofConv, BialgHom.comp_toAlgHom, AlgHom.comp_assoc]

end BialgebraComp

section BialgebraMapValue

variable [CommSemiring H₁] [Semiring H₂] [_root_.Bialgebra R H₁] [_root_.Bialgebra R H₂]
variable [CommSemiring A] [Algebra R A]
variable [CommSemiring B] [Algebra R B]

/-- Pre-composition in the coordinate bialgebra commutes with post-composition in the value
algebra. -/
lemma mapValue_mapDomain (φ : H₁ →ₐc[R] H₂) (χ : A →ₐ[R] B) :
    (mapDomain (H₁ := H₁) (H₂ := H₂) φ :
        WithConv (H₂ →ₐ[R] B) →* WithConv (H₁ →ₐ[R] B)).comp
        (mapValue (H := H₂) χ) =
      (mapValue (H := H₁) χ).comp
        (mapDomain (H₁ := H₁) (H₂ := H₂) φ :
          WithConv (H₂ →ₐ[R] A) →* WithConv (H₁ →ₐ[R] A)) := by
  refine MonoidHom.ext fun f => ?_
  rw [MonoidHom.comp_apply, MonoidHom.comp_apply, mapDomain_apply, mapValue_apply,
    mapDomain_apply, mapValue_apply, toConv_ofConv, toConv_ofConv, AlgHom.comp_assoc]

end BialgebraMapValue

section Hopf

variable [CommSemiring H₁] [Semiring H₂]
variable [_root_.Bialgebra R H₁] [_root_.HopfAlgebra R H₂]
variable [CommSemiring A] [Algebra R A]

/-- The inverse in the target convolution group is transported by `mapDomain` pointwise as
pre-composition with the bialgebra morphism. The group homomorphism statement follows from
`mapDomain` being a `MonoidHom`; this lemma records the concrete formula used at points. -/
lemma mapDomain_inv_apply (φ : H₁ →ₐc[R] H₂) (f : WithConv (H₂ →ₐ[R] A)) (h : H₁) :
    mapDomain (H₁ := H₁) (H₂ := H₂) φ (f⁻¹ : WithConv (H₂ →ₐ[R] A)) h =
      f.ofConv (HopfAlgebra.antipode R (φ h)) := by
  rw [mapDomain_apply_apply]
  exact convInv_apply f (φ h)

end Hopf

end AlgHom

end TauCeti
