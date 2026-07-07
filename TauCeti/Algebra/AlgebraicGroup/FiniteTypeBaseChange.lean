/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Algebra.AlgebraicGroup.CommHopfAlgCatBaseChange
public import TauCeti.Algebra.AlgebraicGroup.FiniteTypeCommHopfAlgCat
public import Mathlib.RingTheory.FiniteStability

/-!
# Base change of finite-type commutative Hopf algebras

This file packages the scalar extension `K ⊗[k] H` of a finite-type commutative Hopf
`k`-algebra as a finite-type commutative Hopf `K`-algebra. The generic bundled commutative
Hopf-algebra base-change API is in `CommHopfAlgCatBaseChange`; this file restricts it to the
finite-type full subcategory, using Mathlib's finite-type base-change instance.

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

This builds on `CommHopfAlgCat.baseChange` and `CommHopfAlgCat.baseChangeFunctor`, whose
point equivalence ultimately comes from Tau Ceti's unbundled
`AlgHom.baseChangePointsMulEquiv`, plus Mathlib's `Algebra.FiniteType.baseChange`.
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
  ⟨CommHopfAlgCat.baseChange (K := K) H.obj,
    inferInstanceAs (Algebra.FiniteType K (K ⊗[k] H))⟩

/-- Scalar extension of a morphism of finite-type commutative Hopf algebras. -/
noncomputable abbrev baseChangeMap {H L : FiniteTypeCommHopfAlgCat.{u, v} k}
    (φ : H ⟶ L) : baseChange (K := K) H ⟶ baseChange (K := K) L :=
  ObjectProperty.homMk (CommHopfAlgCat.baseChangeMap (K := K) φ.hom)

/-- The underlying bialgebra hom of `baseChangeMap` is tensoring the morphism with
the identity on the new base. -/
@[simp]
lemma toBialgHom_baseChangeMap {H L : FiniteTypeCommHopfAlgCat.{u, v} k}
    (φ : H ⟶ L) :
    toBialgHom (baseChangeMap (K := K) φ) =
      _root_.Bialgebra.TensorProduct.map (_root_.BialgHom.id K K) (toBialgHom φ) :=
  rfl

/-- On pure tensors, `baseChangeMap` applies the original morphism to the second factor. -/
lemma baseChangeMap_apply_tmul {H L : FiniteTypeCommHopfAlgCat.{u, v} k}
    (φ : H ⟶ L) (s : K) (h : H) :
    toBialgHom (baseChangeMap (K := K) φ) (s ⊗ₜ[k] h) = s ⊗ₜ[k] toBialgHom φ h :=
  CommHopfAlgCat.baseChangeMap_apply_tmul (K := K) φ.hom s h

/-- Base change is functorial on finite-type commutative Hopf algebras. -/
@[expose] noncomputable def baseChangeFunctor :
    FiniteTypeCommHopfAlgCat.{u, v} k ⥤ FiniteTypeCommHopfAlgCat.{w, max w v} K where
  obj H := baseChange (K := K) H
  map φ := baseChangeMap (K := K) φ
  map_id H := by
    apply hom_ext
    exact congrArg _root_.CommHopfAlgCat.Hom.hom
      ((CommHopfAlgCat.baseChangeFunctor (K := K)).map_id H.obj)
  map_comp φ ψ := by
    apply hom_ext
    exact congrArg _root_.CommHopfAlgCat.Hom.hom
      ((CommHopfAlgCat.baseChangeFunctor (K := K)).map_comp φ.hom ψ.hom)

/-- The object part of `baseChangeFunctor` is the bundled base-change object. -/
@[simp]
lemma baseChangeFunctor_obj (H : FiniteTypeCommHopfAlgCat.{u, v} k) :
    (baseChangeFunctor (K := K)).obj H = baseChange (K := K) H :=
  rfl

/-- The morphism part of `baseChangeFunctor` is scalar extension of coordinate morphisms. -/
@[simp]
lemma baseChangeFunctor_map {H L : FiniteTypeCommHopfAlgCat.{u, v} k} (φ : H ⟶ L) :
    (baseChangeFunctor (K := K)).map φ = baseChangeMap (K := K) φ :=
  rfl

variable (A : CommAlgCat.{x} K)

/-- The points of the base-changed finite-type Hopf algebra are the original points evaluated
on the same algebra, with scalars restricted from `K` to `k`. -/
noncomputable def baseChangePointsMulEquiv (H : FiniteTypeCommHopfAlgCat.{u, v} k) :
    HopfAlgebra.points (R := K) (H := baseChange (K := K) H) A ≃*
      HopfAlgebra.points (R := k) (H := H)
        (_root_.TauCeti.CommAlgCat.restrictScalarsObj (algebraMap k K) A) :=
  CommHopfAlgCat.baseChangePointsMulEquiv (K := K) A H.obj

/-- Applying the base-change points equivalence restricts a `K`-point along `h ↦ 1 ⊗ h`. -/
@[simp]
lemma baseChangePointsMulEquiv_apply_apply (H : FiniteTypeCommHopfAlgCat.{u, v} k)
    (f : HopfAlgebra.points (R := K) (H := baseChange (K := K) H) A) (h : H) :
    (baseChangePointsMulEquiv (K := K) A H f).ofConv h = f.ofConv (1 ⊗ₜ[k] h) :=
  CommHopfAlgCat.baseChangePointsMulEquiv_apply_apply (K := K) A H.obj f h

/-- The inverse base-change points equivalence sends a restricted point to
`s ⊗ h ↦ s • f h`. -/
@[simp]
lemma baseChangePointsMulEquiv_symm_apply_tmul
    (H : FiniteTypeCommHopfAlgCat.{u, v} k)
    (f : HopfAlgebra.points (R := k) (H := H)
      (_root_.TauCeti.CommAlgCat.restrictScalarsObj (algebraMap k K) A))
    (s : K) (h : H) :
    ((baseChangePointsMulEquiv (K := K) A H).symm f).ofConv (s ⊗ₜ[k] h) = s • f.ofConv h :=
  CommHopfAlgCat.baseChangePointsMulEquiv_symm_apply_tmul (K := K) A H.obj f s h

variable {A}

/-- The base-change points equivalence is natural in the value algebra. -/
lemma baseChangePointsMulEquiv_mapValue
    {B : CommAlgCat.{x} K} (H : FiniteTypeCommHopfAlgCat.{u, v} k)
    (χ : A ⟶ B) (f : HopfAlgebra.points (R := K) (H := baseChange (K := K) H) A) :
    baseChangePointsMulEquiv (K := K) B H (HopfAlgebra.mapPoints (H := baseChange (K := K) H) χ f) =
      HopfAlgebra.mapPoints (H := H)
        ((_root_.TauCeti.CommAlgCat.restrictScalars (algebraMap k K)).map χ)
        (baseChangePointsMulEquiv (K := K) A H f) :=
  CommHopfAlgCat.baseChangePointsMulEquiv_mapValue (K := K) H.obj χ f

/-- The base-change points equivalence is natural in the coordinate Hopf algebra. -/
lemma baseChangePointsMulEquiv_mapDomain {H L : FiniteTypeCommHopfAlgCat.{u, v} k}
    (φ : H ⟶ L) (f : HopfAlgebra.points (R := K) (H := baseChange (K := K) L) A) :
    baseChangePointsMulEquiv (K := K) A H
        (AlgHom.mapDomain (A := A) (toBialgHom (baseChangeMap (K := K) φ)) f) =
      AlgHom.mapDomain
        (A := _root_.TauCeti.CommAlgCat.restrictScalarsObj (algebraMap k K) A)
        (toBialgHom φ)
        (baseChangePointsMulEquiv (K := K) A L f) :=
  CommHopfAlgCat.baseChangePointsMulEquiv_mapDomain (K := K) φ.hom f

end FiniteTypeCommHopfAlgCat

end TauCeti
