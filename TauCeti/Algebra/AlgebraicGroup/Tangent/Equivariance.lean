/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Hopf.Map
public import TauCeti.Algebra.AlgebraicGroup.Tangent.Representation
public import TauCeti.Algebra.AlgebraicGroup.Tangent.FiniteType
public import TauCeti.Algebra.AlgebraicGroup.Representation.PointsAction.Basic
public import TauCeti.Algebra.AlgebraicGroup.CommHopfAlgCat.DominantPoints

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
intertwining identity for the adjoint representations. Over an algebraically closed field,
a dominant morphism of finite-type affine groups maps rational adjoint orbits onto the
corresponding orbits; an injective differential also reflects conjugacy.

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

/-- The differential intertwines the adjoint representations on the original cotangent
duals, without scalar extension, for base-valued points. -/
theorem dualCotangentMap_basePointsRepresentation (φ : H →ₐc[R] K)
    (g : WithConv (K →ₐ[R] R)) (x : Module.Dual R (Bialgebra.CotangentSpace R K)) :
    letI := adjointComodule (R := R) (H := K)
    letI := adjointComodule (R := R) (H := H)
    dualCotangentMap φ (Comodule.basePointsRepresentation (H := K) _ g x) =
      Comodule.basePointsRepresentation (H := H) _ (mapDomain φ g) (dualCotangentMap φ x) := by
  let _ := adjointComodule (R := R) (H := K)
  let _ := adjointComodule (R := R) (H := H)
  have h := φ.lTensor_dualCotangentMap_adjointAction (CommAlgCat.of R R) g (1 ⊗ₜ[R] x)
  rw [← adjointComodule_endOfPoint_eq_adjointAction,
    ← adjointComodule_endOfPoint_eq_adjointAction, LinearMap.lTensor_tmul] at h
  simp only [Comodule.endOfPoint_tmul, one_smul,
    Comodule.endOfPoint_one_tmul_eq_one_tmul_basePointsRepresentation,
    LinearMap.lTensor_tmul] at h
  simpa only [TensorProduct.lid_tmul, one_smul] using
    congrArg (TensorProduct.lid R (Module.Dual R (Bialgebra.CotangentSpace R H))) h

end BialgHom

namespace TauCeti.CommHopfAlgCat

open Derivation

universe u

variable {k : Type u} [Field k] [IsAlgClosed k]
  {H K : _root_.CommHopfAlgCat.{u} k} [Algebra.FiniteType k H]
  [Algebra.FiniteType k K] {f : H ⟶ K}

attribute [local instance] Derivation.adjointComodule

/-- A dominant morphism of finite-type affine groups maps a rational adjoint orbit onto
its corresponding orbit. This is a statement about sets of rational Lie algebra points,
not about points over arbitrary coefficient algebras. -/
theorem image_range_basePointsRepresentation (hf : Function.Injective f.hom)
    (x : Module.Dual k (Bialgebra.CotangentSpace k K)) :
    dualCotangentMap f.hom '' Set.range (fun g : WithConv (K →ₐ[k] k) =>
      Comodule.basePointsRepresentation (H := K) _ g x) =
    Set.range (fun g : WithConv (H →ₐ[k] k) =>
      Comodule.basePointsRepresentation (H := H) _ g (dualCotangentMap f.hom x)) := by
  ext y
  constructor
  · rintro ⟨_, ⟨g, rfl⟩, rfl⟩
    exact ⟨BialgHom.mapDomain f.hom g, (f.hom.dualCotangentMap_basePointsRepresentation g x).symm⟩
  · rintro ⟨g, rfl⟩
    obtain ⟨q, hq⟩ := mapDomain_surjective_of_injective k f hf g
    exact ⟨_, ⟨q, rfl⟩, (f.hom.dualCotangentMap_basePointsRepresentation q x).trans
      (congrArg (fun p => Comodule.basePointsRepresentation (H := H) _ p
        (dualCotangentMap f.hom x)) hq)⟩

/-- If a dominant morphism of finite-type affine groups has injective differential,
two rational Lie algebra points are conjugate exactly when their images are conjugate. -/
theorem exists_basePointsRepresentation_eq_iff_of_injective (hf : Function.Injective f.hom)
    (hinj : Function.Injective (dualCotangentMap f.hom))
    (x y : Module.Dual k (Bialgebra.CotangentSpace k K)) :
    (∃ g : WithConv (H →ₐ[k] k),
      Comodule.basePointsRepresentation (H := H) _ g (dualCotangentMap f.hom x) =
        dualCotangentMap f.hom y) ↔
    ∃ g : WithConv (K →ₐ[k] k), Comodule.basePointsRepresentation (H := K) _ g x = y := by
  constructor
  · intro h
    have hm : dualCotangentMap f.hom y ∈ Set.range (fun g : WithConv (H →ₐ[k] k) =>
        Comodule.basePointsRepresentation (H := H) _ g (dualCotangentMap f.hom x)) := h
    rw [← image_range_basePointsRepresentation hf x] at hm
    obtain ⟨_, ⟨g, rfl⟩, hg⟩ := hm
    exact ⟨g, hinj hg⟩
  · rintro ⟨g, rfl⟩
    exact ⟨BialgHom.mapDomain f.hom g, (f.hom.dualCotangentMap_basePointsRepresentation g x).symm⟩

end TauCeti.CommHopfAlgCat
