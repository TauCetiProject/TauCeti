/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RingTheory.FiniteStability
public import TauCeti.Algebra.AlgebraicGroup.FiniteTypeCommHopfAlgCat
public import TauCeti.Algebra.AlgebraicGroup.Product

/-!
# Products of finite-type commutative Hopf algebras

This file packages the tensor product of two finite-type commutative Hopf algebras as another
object of `FiniteTypeCommHopfAlgCat`. On affine group schemes this is the coordinate algebra
of the direct product. The Hopf-algebra structure is Mathlib's tensor-product Hopf algebra;
the finite-type input is Mathlib's stability of finite type under base change, followed by
transitivity of finite type along `R → H₁ → H₁ ⊗[R] H₂`.

The coordinate inclusions `H₁ → H₁ ⊗[R] H₂` and `H₂ → H₁ ⊗[R] H₂` are also bundled as
morphisms in `FiniteTypeCommHopfAlgCat`, and the points API is connected to the existing
product-points equivalence from `TauCeti.Algebra.AlgebraicGroup.Product`.

This is a finite-type wrapper for the ReductiveGroups roadmap Layer 0 product/functor-of-points
infrastructure: affine group schemes of finite type should remain finite type under products.
-/

public section

open CategoryTheory TensorProduct WithConv

namespace TauCeti

universe u v w

namespace FiniteTypeCommHopfAlgCat

variable {R : Type u} [CommRing R]

/-- The coordinate algebra `H ⊗[R] K` of a product of finite-type affine group schemes is
again finite type over `R`. -/
theorem tensorProduct_finiteType (H K : FiniteTypeCommHopfAlgCat.{u, v} R) :
    Algebra.FiniteType R (H ⊗[R] K) :=
  Algebra.FiniteType.trans (R := R) (S := H) (A := H ⊗[R] K) inferInstance inferInstance

/-- The tensor product of two finite-type commutative Hopf algebras, bundled as a finite-type
commutative Hopf algebra.

Contravariantly, this is the coordinate-Hopf-algebra model for the product of the represented
affine group schemes. -/
noncomputable abbrev tensorProduct (H K : FiniteTypeCommHopfAlgCat.{u, v} R) :
    FiniteTypeCommHopfAlgCat.{u, v} R :=
  letI : Algebra.FiniteType R (H ⊗[R] K) := tensorProduct_finiteType H K
  of R (H ⊗[R] K)

/-- The left coordinate inclusion `H → H ⊗[R] K`, bundled in the finite-type commutative
Hopf-algebra category. On points this is the first projection from product points. -/
noncomputable abbrev includeLeft (H K : FiniteTypeCommHopfAlgCat.{u, v} R) :
    H ⟶ tensorProduct H K :=
  letI : Algebra.FiniteType R (H ⊗[R] K) := tensorProduct_finiteType H K
  ofHom (Bialgebra.TensorProduct.includeLeft (R := R) (H₁ := H) (H₂ := K))

/-- The right coordinate inclusion `K → H ⊗[R] K`, bundled in the finite-type commutative
Hopf-algebra category. On points this is the second projection from product points. -/
noncomputable abbrev includeRight (H K : FiniteTypeCommHopfAlgCat.{u, v} R) :
    K ⟶ tensorProduct H K :=
  letI : Algebra.FiniteType R (H ⊗[R] K) := tensorProduct_finiteType H K
  ofHom (Bialgebra.TensorProduct.includeRight (R := R) (H₁ := H) (H₂ := K))

/-- The underlying bialgebra morphism of `includeLeft` is `x ↦ x ⊗ 1`. -/
@[simp]
lemma toBialgHom_includeLeft (H K : FiniteTypeCommHopfAlgCat.{u, v} R) :
    toBialgHom (includeLeft H K) =
      Bialgebra.TensorProduct.includeLeft (R := R) (H₁ := H) (H₂ := K) := by
  letI : Algebra.FiniteType R (H ⊗[R] K) := tensorProduct_finiteType H K
  exact toBialgHom_ofHom (Bialgebra.TensorProduct.includeLeft (R := R) (H₁ := H) (H₂ := K))

/-- The underlying bialgebra morphism of `includeRight` is `y ↦ 1 ⊗ y`. -/
@[simp]
lemma toBialgHom_includeRight (H K : FiniteTypeCommHopfAlgCat.{u, v} R) :
    toBialgHom (includeRight H K) =
      Bialgebra.TensorProduct.includeRight (R := R) (H₁ := H) (H₂ := K) := by
  letI : Algebra.FiniteType R (H ⊗[R] K) := tensorProduct_finiteType H K
  exact toBialgHom_ofHom (Bialgebra.TensorProduct.includeRight (R := R) (H₁ := H) (H₂ := K))

variable (A : CommAlgCat.{w} R)

/-- The finite-type points functor sends the left coordinate inclusion to first-factor
restriction on product points. -/
@[simp]
theorem pointsFunctor_map_includeLeft_app_apply_apply
    (H K : FiniteTypeCommHopfAlgCat.{u, v} R)
    (f : HopfAlgebra.points (R := R) (H := tensorProduct H K) A) (h : H) :
    (((pointsFunctor (R := R)).map (includeLeft H K).op).app A f).ofConv h =
      f.ofConv (Bialgebra.TensorProduct.includeLeft (R := R) (H₁ := H) (H₂ := K) h) := by
  simp [pointsFunctor_map_app_apply_apply]

/-- The finite-type points functor sends the right coordinate inclusion to second-factor
restriction on product points. -/
@[simp]
theorem pointsFunctor_map_includeRight_app_apply_apply
    (H K : FiniteTypeCommHopfAlgCat.{u, v} R)
    (f : HopfAlgebra.points (R := R) (H := tensorProduct H K) A) (k : K) :
    (((pointsFunctor (R := R)).map (includeRight H K).op).app A f).ofConv k =
      f.ofConv (Bialgebra.TensorProduct.includeRight (R := R) (H₁ := H) (H₂ := K) k) := by
  simp [pointsFunctor_map_app_apply_apply]

end FiniteTypeCommHopfAlgCat

end TauCeti
