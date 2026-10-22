/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Hopf.Map
public import TauCeti.Algebra.AlgebraicGroup.Tangent.Representation

/-!
# Equivariance of the differential for the adjoint action

A morphism of affine group schemes intertwines conjugation. Differentiating at the identity says
that its differential intertwines the corresponding adjoint actions. In coordinate rings, a
bialgebra morphism `φ : A' →ₐc[R] A` acts on both points and tangent derivations by precomposition,
and the compatibility is

```text
dφ (Ad(g)(d)) = Ad(g ∘ φ)(dφ(d)).
```

This file proves that identity directly from functoriality of convolution and packages it as an
intertwining identity for the adjoint representations.

## Main declarations

* `TauCeti.derivationComp_adDerivation`: the differential intertwines the adjoint action.
* `BialgHom.lTensor_dualCotangentMap_adjointAction`: the same equivariance on scalar
  extensions of cotangent duals.

## References

* J. S. Milne, *Algebraic Groups* (2017), §14.
-/

public section

namespace TauCeti

open _root_.Coalgebra WithConv

universe u v w x

variable {R : Type u} {A : Type v} {A' : Type w} {B : Type x}
variable [CommSemiring R] [CommSemiring A] [HopfAlgebra R A]
variable [CommSemiring A'] [HopfAlgebra R A']
variable [CommSemiring B] [Algebra R B]

private lemma derivationComp_toLinearMap (φ : A' →ₐc[R] A)
    (d : Derivation R A (Bialgebra.CounitAlgebra R A B)) :
    (derivationComp (B := B) φ d :
        A' →ₗ[R] Bialgebra.CounitAlgebra R A' B) =
      (d : A →ₗ[R] Bialgebra.CounitAlgebra R A B).comp
        (φ : A' →ₐc[R] A).toLinearMap := by
  ext x
  -- The codomains are two exported synonyms for `B`; the pointwise API states exactly
  -- the equality after that identification.
  change derivationComp (B := B) φ d x = d ((φ : A' →ₐ[R] A) x)
  exact derivationComp_apply φ d x

private lemma convTriple_comp_apply (φ : A' →ₐc[R] A)
    (f g h : A →ₗ[R] Bialgebra.CounitAlgebra R A B) (a : A') :
    (toConv f * toConv g * toConv h).ofConv ((φ : A' →ₐ[R] A) a) =
      (toConv (f.comp (φ : A' →ₐc[R] A).toLinearMap) *
        toConv (g.comp (φ : A' →ₐc[R] A).toLinearMap) *
        toConv (h.comp (φ : A' →ₐc[R] A).toLinearMap)).ofConv a := by
  have houter := DFunLike.congr_fun
    (LinearMap.convMul_comp_coalgHom_distrib (toConv f * toConv g) (toConv h)
      (φ : A' →ₗc[R] A)) a
  have hinner := LinearMap.convMul_comp_coalgHom_distrib (toConv f) (toConv g)
    (φ : A' →ₗc[R] A)
  simp only [LinearMap.comp_apply] at houter
  rw [hinner] at houter
  exact houter

/-- **The differential of a Hopf-algebra morphism intertwines the adjoint actions.**

Contravariantly, `φ : A' →ₐc[R] A` represents a morphism `Spec A → Spec A'`.
Precomposing both a point and a tangent derivation with `φ` commutes with convolution
conjugation. -/
@[simp]
theorem derivationComp_adDerivation (φ : A' →ₐc[R] A)
    (g : WithConv (A →ₐ[R] Bialgebra.CounitAlgebra R A B))
    (d : Derivation R A (Bialgebra.CounitAlgebra R A B)) :
    derivationComp (B := B) φ (Derivation.adDerivation B g d) =
      Derivation.adDerivation B
        (BialgHom.mapDomain (A := Bialgebra.CounitAlgebra R A' B) φ g)
        (derivationComp (B := B) φ d) := by
  have mapDomain_inv :
      (BialgHom.mapDomain (A := Bialgebra.CounitAlgebra R A' B) φ g)⁻¹ =
        BialgHom.mapDomain (A := Bialgebra.CounitAlgebra R A' B) φ (g⁻¹) :=
    ((BialgHom.mapDomain (A := Bialgebra.CounitAlgebra R A' B) φ).map_inv g).symm
  have mapDomain_toLinearMap :
      (BialgHom.mapDomain (A := Bialgebra.CounitAlgebra R A' B) φ g).ofConv.toLinearMap =
        g.ofConv.toLinearMap.comp φ.toLinearMap := by
    ext x
    exact BialgHom.mapDomain_apply_apply (A := Bialgebra.CounitAlgebra R A' B) φ g x
  apply Derivation.ext
  intro a
  apply (Bialgebra.CounitAlgebra.algEquivSelf R A' B).injective
  rw [algEquivSelf_derivationComp_apply, Derivation.adDerivation_apply,
    Derivation.adDerivation_apply,
    Bialgebra.CounitAlgebra.algEquivSelf_apply,
    Bialgebra.CounitAlgebra.algEquivSelf_apply, convTriple_comp_apply,
    mapDomain_inv, derivationComp_toLinearMap]
  rw [mapDomain_toLinearMap]
  simp only [BialgHom.mapDomain_apply, ofConv_toConv, AlgHom.comp_toLinearMap]
  rfl

end TauCeti

namespace BialgHom

open TauCeti WithConv Derivation
open scoped TensorProduct

universe u

variable {R H K : Type u} [CommRing R] [CommRing H] [CommRing K]
  [HopfAlgebra R H] [HopfAlgebra R K]
  [Module.Finite R (Bialgebra.CotangentSpace R H)]
  [Module.Projective R (Bialgebra.CotangentSpace R H)]
  [Module.Finite R (Bialgebra.CotangentSpace R K)]
  [Module.Projective R (Bialgebra.CotangentSpace R K)]

/-- Scalar extension of the differential intertwines the adjoint actions on cotangent duals.
This is equivariance of the differential over every coefficient algebra. -/
theorem lTensor_dualCotangentMap_adjointAction (φ : H →ₐc[R] K)
    (A : CommAlgCat.{u} R) (g : WithConv (K →ₐ[R] A))
    (x : A ⊗[R] Module.Dual R (Bialgebra.CotangentSpace R K)) :
    (dualCotangentMap φ).lTensor A ((adjointAction A g).val x) =
      (adjointAction A (BialgHom.mapDomain φ g)).val
        ((dualCotangentMap φ).lTensor A x) := by
  apply (tangentScalarExtensionEquiv (R := R) (A := H) (B := A)).injective
  rw [tangentScalarExtensionEquiv_lTensor_dualCotangentMap,
    tangentScalarExtensionEquiv_adjointAction, derivationComp_adDerivation,
    tangentScalarExtensionEquiv_adjointAction,
    tangentScalarExtensionEquiv_lTensor_dualCotangentMap]
  congr 1
  simpa only [BialgHom.mapDomain_apply, toConv_ofConv] using
    (pointInCounitAlgebra_comp A φ g.ofConv).symm

end BialgHom
