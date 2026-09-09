/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Basic
public import Mathlib.LinearAlgebra.CliffordAlgebra.Prod
public import Mathlib.LinearAlgebra.CliffordAlgebra.Star
public import Mathlib.RingTheory.Flat.Basic

/-!
# Functoriality of Clifford algebras

This file records structural properties of the algebra map induced by a quadratic isometry. Such
maps commute with Clifford conjugation and preserve the even subalgebra. For an orthogonal product,
the map induced by the left-summand inclusion is injective when the left Clifford algebra is flat
and scalar action on the right Clifford algebra is faithful.

## Main results

* `CliffordAlgebra.map_star` proves naturality of Clifford conjugation.
* `CliffordAlgebra.map_mem_even` proves preservation of the even subalgebra.
* `CliffordAlgebra.map_inl_injective` proves injectivity for a left orthogonal summand.
-/

public section


open QuadraticMap
open scoped TensorProduct

namespace CliffordAlgebra

universe u v w


variable {R : Type u} [CommRing R]
  {M₁ : Type v} [AddCommGroup M₁] [Module R M₁]
  {M₂ : Type w} [AddCommGroup M₂] [Module R M₂]
  {Q₁ : QuadraticForm R M₁} {Q₂ : QuadraticForm R M₂}

/-- Clifford conjugation commutes with the algebra map induced by a quadratic isometry. -/
@[simp]
theorem map_star (f : Q₁ →qᵢ Q₂) (x : CliffordAlgebra Q₁) :
    map f (star x) = star (map f x) := by
  induction x using CliffordAlgebra.induction with
  | algebraMap r => simp
  | ι m => simp
  | add x y hx hy => simp only [star_add, map_add, hx, hy]
  | mul x y hx hy => simp only [star_mul, map_mul, hx, hy]

/-- A quadratic isometry sends the even Clifford subalgebra into the even Clifford subalgebra. -/
theorem map_mem_even (f : Q₁ →qᵢ Q₂) {x : CliffordAlgebra Q₁} (hx : x ∈ even Q₁) :
    map f x ∈ even Q₂ := by
  -- `even` is the subalgebra wrapper around degree zero of `evenOdd`; its induction principle is
  -- stated for the underlying graded submodule.
  change x ∈ evenOdd Q₁ 0 at hx
  change map f x ∈ evenOdd Q₂ 0
  induction x, hx using CliffordAlgebra.even_induction with
  | algebraMap r =>
      simpa using one_le_evenOdd_zero Q₂
        (Submodule.mem_one.mpr ⟨r, (map f).commutes r |>.symm⟩)
  | add x y _ _ hx hy => simpa only [map_add] using Submodule.add_mem _ hx hy
  | ι_mul_ι_mul m₁ m₂ x _ hx =>
      simpa only [map_mul, map_apply_ι, zero_add] using
        SetLike.mul_mem_graded (ι_mul_ι_mem_evenOdd_zero Q₂ (f m₁) (f m₂)) hx

section OrthogonalProduct

variable {K : Type u} [CommRing K] [Invertible (2 : K)]
  {N₁ : Type v} [AddCommGroup N₁] [Module K N₁]
  {N₂ : Type w} [AddCommGroup N₂] [Module K N₂]

private noncomputable def decomposeTensorEquiv
    (P₁ : QuadraticForm K N₁) (P₂ : QuadraticForm K N₂) :
    CliffordAlgebra P₁ ⊗[K] CliffordAlgebra P₂ ≃ₗ[K]
      (DirectSum (ZMod 2) fun i ↦ evenOdd P₁ i) ⊗[K]
        DirectSum (ZMod 2) fun i ↦ evenOdd P₂ i :=
  ((DirectSum.decomposeAlgEquiv (evenOdd P₁)).toLinearEquiv.rTensor
      (CliffordAlgebra P₂)).trans
    ((DirectSum.decomposeAlgEquiv (evenOdd P₂)).toLinearEquiv.lTensor
      (DirectSum (ZMod 2) fun i ↦ evenOdd P₁ i))

omit [Invertible (2 : K)] in
private theorem auxEquiv_includeLeft (P₁ : QuadraticForm K N₁) (P₂ : QuadraticForm K N₂)
    (x : CliffordAlgebra P₁) :
    GradedTensorProduct.auxEquiv K (evenOdd P₁) (evenOdd P₂)
        (GradedTensorProduct.includeLeft (evenOdd P₁) (evenOdd P₂) x) =
      decomposeTensorEquiv P₁ P₂
        (Algebra.TensorProduct.includeLeft (R := K) (S := K)
          (A := CliffordAlgebra P₁) (B := CliffordAlgebra P₂) x) := by
  simp only [GradedTensorProduct.includeLeft_apply, GradedTensorProduct.auxEquiv_tmul,
    decomposeTensorEquiv, Algebra.TensorProduct.includeLeft_apply, LinearEquiv.trans_apply,
    LinearEquiv.rTensor_tmul, LinearEquiv.lTensor_tmul]
  have h₁ : (DirectSum.decomposeAlgEquiv (evenOdd P₁)).toLinearEquiv x =
      DirectSum.decompose (evenOdd P₁) x := rfl
  have h₂ : (DirectSum.decomposeAlgEquiv (evenOdd P₂)).toLinearEquiv 1 =
      DirectSum.decompose (evenOdd P₂) 1 := rfl
  rw [h₁, h₂]

private theorem gradedTensorIncludeLeft_injective
    (P₁ : QuadraticForm K N₁) (P₂ : QuadraticForm K N₂)
    [Module.Flat K (CliffordAlgebra P₁)] :
    Function.Injective (GradedTensorProduct.includeLeft (evenOdd P₁) (evenOdd P₂)) := by
  intro x y hxy
  apply Algebra.TensorProduct.includeLeft_injective
    (R := K) (S := K) (A := CliffordAlgebra P₁) (B := CliffordAlgebra P₂)
    (FaithfulSMul.algebraMap_injective K (CliffordAlgebra P₂))
  have h := congrArg (GradedTensorProduct.auxEquiv K (evenOdd P₁) (evenOdd P₂)) hxy
  rw [auxEquiv_includeLeft, auxEquiv_includeLeft] at h
  exact (decomposeTensorEquiv P₁ P₂).injective h

omit [Invertible (2 : K)] in
private theorem toProd_includeLeft (P₁ : QuadraticForm K N₁) (P₂ : QuadraticForm K N₂)
    (x : CliffordAlgebra P₁) :
    toProd P₁ P₂ (GradedTensorProduct.includeLeft (evenOdd P₁) (evenOdd P₂) x) =
      map (QuadraticMap.Isometry.inl P₁ P₂) x := by
  simp [toProd]

/-- The Clifford-algebra map induced by the inclusion of the left summand of an orthogonal product
is injective when the left Clifford algebra is flat and `2` is invertible. -/
theorem map_inl_injective (P₁ : QuadraticForm K N₁) (P₂ : QuadraticForm K N₂)
    [Module.Flat K (CliffordAlgebra P₁)] :
    Function.Injective (map (QuadraticMap.Isometry.inl P₁ P₂)) := by
  intro x y hxy
  apply gradedTensorIncludeLeft_injective P₁ P₂
  apply (prodEquiv P₁ P₂).symm.injective
  -- Transport both elements through the product equivalence to expose `includeLeft`.
  change toProd P₁ P₂ (GradedTensorProduct.includeLeft (evenOdd P₁) (evenOdd P₂) x) =
    toProd P₁ P₂ (GradedTensorProduct.includeLeft (evenOdd P₁) (evenOdd P₂) y)
  rw [toProd_includeLeft, toProd_includeLeft]
  exact hxy

end OrthogonalProduct

end CliffordAlgebra
