/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Algebra.AlgebraicGroup.BaseChangeNaturality
public import TauCeti.Algebra.AlgebraicGroup.FiniteTypeCommHopfAlgCat
public import TauCeti.Algebra.Category.CommAlgCat.RestrictScalars
public import Mathlib.RingTheory.FiniteStability

/-!
# Base change of finite-type commutative Hopf algebras

This file packages the scalar extension `K ⊗[k] H` of a finite-type commutative Hopf
`k`-algebra as a finite-type commutative Hopf `K`-algebra. The Hopf algebra structure is
Mathlib's tensor-product Hopf algebra, and finite generation over `K` is Mathlib's finite-type
base-change instance.

It is the finite-type coordinate-Hopf-algebra wrapper for the ReductiveGroups roadmap Layer 0
base-change item: geometric notions are studied after replacing the coordinate Hopf algebra
`H` by `K ⊗[k] H`, and the functor of points of this base-changed object is identified with
the original points evaluated on `K`-algebras.

## Main declarations

* `FiniteTypeCommHopfAlgCat.baseChange`: the bundled finite-type Hopf `K`-algebra
  `K ⊗[k] H`.
* `FiniteTypeCommHopfAlgCat.baseChangeMap`: scalar extension of a coordinate morphism.
* `FiniteTypeCommHopfAlgCat.baseChangeFunctor`: functorial base change.
* `FiniteTypeCommHopfAlgCat.baseChangePointsMulEquiv`: the inherited point equivalence
  `(K ⊗[k] H →ₐ[K] A) ≃* (H →ₐ[k] A)`.

## References

This builds on Tau Ceti's unbundled base-change equivalence
`AlgHom.baseChangePointsMulEquiv` and its naturality lemmas, plus Mathlib's
`Bialgebra.TensorProduct.map` and `Algebra.FiniteType.baseChange`.
-/

public section

open CategoryTheory TensorProduct WithConv

namespace TauCeti

universe u v w x

namespace FiniteTypeCommHopfAlgCat

variable {k : Type u} {K : Type w} [CommRing k] [CommRing K] [Algebra k K]

/-- Base change of a finite-type commutative Hopf algebra along `k → K`.

The underlying coordinate Hopf algebra is `K ⊗[k] H`, with the tensor-product Hopf algebra
structure over `K`. -/
noncomputable abbrev baseChange (H : FiniteTypeCommHopfAlgCat.{u, v} k) :
    FiniteTypeCommHopfAlgCat.{w, max w v} K :=
  of K (K ⊗[k] H)

/-- Scalar extension of a morphism of finite-type commutative Hopf algebras. -/
noncomputable abbrev baseChangeMap {H L : FiniteTypeCommHopfAlgCat.{u, v} k}
    (φ : H ⟶ L) : baseChange (K := K) H ⟶ baseChange (K := K) L :=
  ofHom (_root_.Bialgebra.TensorProduct.map (_root_.BialgHom.id K K) (toBialgHom φ))

@[simp]
lemma toBialgHom_baseChangeMap {H L : FiniteTypeCommHopfAlgCat.{u, v} k}
    (φ : H ⟶ L) :
    toBialgHom (baseChangeMap (K := K) φ) =
      _root_.Bialgebra.TensorProduct.map (_root_.BialgHom.id K K) (toBialgHom φ) :=
  rfl

lemma baseChangeMap_apply_tmul {H L : FiniteTypeCommHopfAlgCat.{u, v} k}
    (φ : H ⟶ L) (s : K) (h : H) :
    toBialgHom (baseChangeMap (K := K) φ) (s ⊗ₜ[k] h) = s ⊗ₜ[k] toBialgHom φ h := by
  rw [toBialgHom_baseChangeMap, _root_.Bialgebra.TensorProduct.map_tmul,
    _root_.BialgHom.id_apply]

/-- Base change is functorial on finite-type commutative Hopf algebras. -/
@[expose] noncomputable def baseChangeFunctor :
    FiniteTypeCommHopfAlgCat.{u, v} k ⥤ FiniteTypeCommHopfAlgCat.{w, max w v} K where
  obj H := baseChange (K := K) H
  map φ := baseChangeMap (K := K) φ
  map_id H := by
    apply hom_ext
    apply BialgHom.ext
    intro x
    have hAlg :
        (toBialgHom (baseChangeMap (K := K) (𝟙 H))).toAlgHom =
          (toBialgHom (𝟙 (baseChange (K := K) H))).toAlgHom := by
      apply Algebra.TensorProduct.ext'
      intro s h
      simp
    exact AlgHom.congr_fun hAlg x
  map_comp φ ψ := by
    apply hom_ext
    apply BialgHom.ext
    intro x
    have hAlg :
        (toBialgHom (baseChangeMap (K := K) (φ ≫ ψ))).toAlgHom =
          (toBialgHom (baseChangeMap (K := K) φ ≫ baseChangeMap (K := K) ψ)).toAlgHom := by
      apply Algebra.TensorProduct.ext'
      intro s h
      simp
    exact AlgHom.congr_fun hAlg x

@[simp]
lemma baseChangeFunctor_obj (H : FiniteTypeCommHopfAlgCat.{u, v} k) :
    (baseChangeFunctor (K := K)).obj H = baseChange (K := K) H :=
  rfl

@[simp]
lemma baseChangeFunctor_map {H L : FiniteTypeCommHopfAlgCat.{u, v} k} (φ : H ⟶ L) :
    (baseChangeFunctor (K := K)).map φ = baseChangeMap (K := K) φ :=
  rfl

variable (A : CommAlgCat.{x} K)

/-- The points of the base-changed finite-type Hopf algebra are the original points evaluated
on the same algebra, with scalars restricted from `K` to `k`. -/
noncomputable def baseChangePointsMulEquiv (H : FiniteTypeCommHopfAlgCat.{u, v} k) :
    HopfAlgebra.points (R := K) (H := baseChange (K := K) H) A ≃*
      HopfAlgebra.points (R := k) (H := H) (CommAlgCat.restrictScalars (k := k) A) :=
  letI : Algebra k A := Algebra.compHom A (algebraMap k K)
  letI : IsScalarTower k K A := IsScalarTower.of_algebraMap_eq' rfl
  (AlgHom.baseChangePointsMulEquiv (k := k) (K := K) (A := H) (R := A)).symm

/-- Applying the base-change points equivalence restricts a `K`-point along `h ↦ 1 ⊗ h`. -/
@[simp]
lemma baseChangePointsMulEquiv_apply_apply (H : FiniteTypeCommHopfAlgCat.{u, v} k)
    (f : HopfAlgebra.points (R := K) (H := baseChange (K := K) H) A) (h : H) :
    (baseChangePointsMulEquiv (K := K) A H f).ofConv h = f.ofConv (1 ⊗ₜ[k] h) :=
  letI : Algebra k A := Algebra.compHom A (algebraMap k K)
  letI : IsScalarTower k K A := IsScalarTower.of_algebraMap_eq' rfl
  AlgHom.baseChangePointsMulEquiv_symm_apply f h

/-- The inverse base-change points equivalence sends a restricted point to
`s ⊗ h ↦ s • f h`. -/
@[simp]
lemma baseChangePointsMulEquiv_symm_apply_tmul
    (H : FiniteTypeCommHopfAlgCat.{u, v} k)
    (f : HopfAlgebra.points (R := k) (H := H) (CommAlgCat.restrictScalars (k := k) A))
    (s : K) (h : H) :
    ((baseChangePointsMulEquiv (K := K) A H).symm f).ofConv (s ⊗ₜ[k] h) = s • f.ofConv h :=
  letI : Algebra k A := Algebra.compHom A (algebraMap k K)
  letI : IsScalarTower k K A := IsScalarTower.of_algebraMap_eq' rfl
  AlgHom.baseChangePointsMulEquiv_apply_tmul f s h

variable {A}

/-- The base-change points equivalence is natural in the value algebra. -/
lemma baseChangePointsMulEquiv_mapValue
    {B : CommAlgCat.{x} K} (H : FiniteTypeCommHopfAlgCat.{u, v} k)
    (χ : A ⟶ B) (f : HopfAlgebra.points (R := K) (H := baseChange (K := K) H) A) :
    baseChangePointsMulEquiv (K := K) B H (HopfAlgebra.mapPoints (H := baseChange (K := K) H) χ f) =
      HopfAlgebra.mapPoints (H := H) ((CommAlgCat.restrictScalarsFunctor (k := k)).map χ)
        (baseChangePointsMulEquiv (K := K) A H f) := by
  letI : Algebra k A := Algebra.compHom A (algebraMap k K)
  letI : IsScalarTower k K A := IsScalarTower.of_algebraMap_eq' rfl
  letI : Algebra k B := Algebra.compHom B (algebraMap k K)
  letI : IsScalarTower k K B := IsScalarTower.of_algebraMap_eq' rfl
  -- `restrictScalarsFunctor.map χ` is definitionally `restrictScalarsMap χ`, so it suffices to
  -- prove the statement for the underlying restriction-of-scalars morphism.
  have key : baseChangePointsMulEquiv (K := K) B H
        (HopfAlgebra.mapPoints (H := baseChange (K := K) H) χ f) =
      HopfAlgebra.mapPoints (H := H) (CommAlgCat.restrictScalarsMap (k := k) χ)
        (baseChangePointsMulEquiv (K := K) A H f) := by
    simpa [baseChangePointsMulEquiv, HopfAlgebra.mapPoints, CommAlgCat.restrictScalarsMap]
      using AlgHom.baseChangePointsMulEquiv_symm_mapValue (k := k) (K := K) (A := H)
        (R := A) (S := B) χ.hom f
  exact key

/-- The base-change points equivalence is natural in the coordinate Hopf algebra. -/
lemma baseChangePointsMulEquiv_mapDomain {H L : FiniteTypeCommHopfAlgCat.{u, v} k}
    (φ : H ⟶ L) (f : HopfAlgebra.points (R := K) (H := baseChange (K := K) L) A) :
    baseChangePointsMulEquiv (K := K) A H
        (AlgHom.mapDomain (A := A) (toBialgHom (baseChangeMap (K := K) φ)) f) =
      AlgHom.mapDomain (A := CommAlgCat.restrictScalars (k := k) A) (toBialgHom φ)
        (baseChangePointsMulEquiv (K := K) A L f) := by
  letI : Algebra k A := Algebra.compHom A (algebraMap k K)
  letI : IsScalarTower k K A := IsScalarTower.of_algebraMap_eq' rfl
  simpa [baseChangePointsMulEquiv, toBialgHom_baseChangeMap]
    using AlgHom.baseChangePointsMulEquiv_symm_mapDomain (k := k) (K := K)
      (A := H) (B := L) (R := A) (toBialgHom φ) f

end FiniteTypeCommHopfAlgCat

end TauCeti
