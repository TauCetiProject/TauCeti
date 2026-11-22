/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeromie Beasley
-/
module

public import TauCeti.RepresentationTheory.ClassicalGroups.Adjoint
public import TauCeti.RepresentationTheory.ClassicalGroups.AdjointSquare.Products
public import TauCeti.RepresentationTheory.ClassicalGroups.AdjointSquare.Surjectivity
public import Mathlib.LinearAlgebra.Contraction
public import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Trace transposes into the tensor square of the adjoint representation

The tensor product of the two trace pairings is a perfect invariant pairing.
Its inverse turns the dual of each contraction into an equivariant embedding.
The evaluation formulas characterize the images on arbitrary test tensors.
-/

public section

namespace TauCeti.AdjointSquare

open scoped TensorProduct
variable {K : Type*} [Field K] [NeZero (3 : K)]
local notation "V" => LieAlgebra.SpecialLinear.sl (Fin 3) K
local notation "T" => V ⊗[K] V
local notation "ρ" => TauCeti.adjointRep K 3
local notation "σ" => Representation.tprod ρ ρ

private abbrev traceForm₃ : LinearMap.BilinForm K V := TauCeti.traceForm K 3

private noncomputable abbrev traceDual₃ : V ≃ₗ[K] Module.Dual K V := TauCeti.traceDual K 3

private noncomputable def squareTrace : T ≃ₗ[K] Module.Dual K T :=
  TensorProduct.congr traceDual₃ traceDual₃ ≪≫ₗ TensorProduct.dualDistribEquiv K V V

private theorem square_tmul (x y u v : V) :
    squareTrace (x ⊗ₜ[K] y) (u ⊗ₜ[K] v) = traceForm₃ x u * traceForm₃ y v := by
  simp [squareTrace, mul_comm]

private theorem square_invariant (g : Matrix.SpecialLinearGroup (Fin 3) K) (a b : T) :
    squareTrace (σ g a) (σ g b) = squareTrace a b := by
  induction a using TensorProduct.inductionOn with
  | add a₁ a₂ h₁ h₂ => simp only [map_add, LinearMap.add_apply, h₁, h₂]
  | tmul x y =>
    induction b using TensorProduct.inductionOn with
    | add b₁ b₂ h₁ h₂ => simp only [map_add, h₁, h₂]
    | tmul u v => simp only [Representation.tprod_apply, TensorProduct.map_tmul,
        square_tmul, TauCeti.traceForm_adjointRep]

private noncomputable def liftMap (f : Representation.IntertwiningMap σ ρ) :
    Representation.IntertwiningMap ρ σ where
  toLinearMap := squareTrace.symm.toLinearMap ∘ₗ f.toLinearMap.dualMap ∘ₗ traceDual₃.toLinearMap
  isIntertwining' g := by
    ext1 x
    -- The intertwiner is the composite of `squareTrace.symm`, `dualMap` and `traceDual`.
    -- Those three maps are definitionally the linear maps written below.
    change squareTrace.symm (f.toLinearMap.dualMap (traceDual₃ (ρ g x))) =
      σ g (squareTrace.symm (f.toLinearMap.dualMap (traceDual₃ x)))
    apply squareTrace.injective
    apply LinearMap.ext
    intro t
    rw [LinearEquiv.apply_symm_apply]
    have h := square_invariant g
      (squareTrace.symm (f.toLinearMap.dualMap (traceDual₃ x))) (σ g⁻¹ t)
    rw [Representation.self_inv_apply, LinearEquiv.apply_symm_apply] at h
    rw [h]
    -- `dualMap` applies the functional; `coe_toLinearMap` removes the underlying linear map.
    rw [LinearMap.dualMap_apply, LinearMap.dualMap_apply, TauCeti.traceDual_apply,
      TauCeti.traceDual_apply, Representation.IntertwiningMap.coe_toLinearMap, f.isIntertwining]
    simpa only [TauCeti.traceForm_apply, Representation.self_inv_apply] using
      TauCeti.traceForm_adjointRep K 3 g x (ρ g⁻¹ (f t))

private theorem liftMap_injective (f : Representation.IntertwiningMap σ ρ)
    (hf : Function.Surjective f) :
    Function.Injective (liftMap f) :=
  squareTrace.symm.injective.comp ((LinearMap.dualMap_injective_of_surjective hf).comp
    traceDual₃.injective)

private theorem liftMap_pairing (f : Representation.IntertwiningMap σ ρ) (x : V) (t : T) :
    TensorProduct.dualDistrib K V V
      (TensorProduct.map traceDual₃.toLinearMap traceDual₃.toLinearMap (liftMap f x)) t =
        traceDual₃ x (f t) := by
  rw [← TensorProduct.toLinearMap_dualDistribEquiv]
  -- `squareTrace` is `congr traceDual₃` followed by `dualDistribEquiv`.
  change squareTrace (squareTrace.symm (f.toLinearMap.dualMap (traceDual₃ x))) t = _
  rw [LinearEquiv.apply_symm_apply, LinearMap.dualMap_apply,
    Representation.IntertwiningMap.coe_toLinearMap]

/-- The trace transpose of the Lie bracket as an equivariant map into the tensor square. -/
noncomputable def alternatingEmbeddingMap : Representation.IntertwiningMap ρ σ :=
  liftMap (TauCeti.alternatingProductMap (K := K) (n := 3))

/-- The alternating product is surjective, so its trace transpose is injective. -/
theorem alternatingEmbeddingMap_injective : Function.Injective (alternatingEmbeddingMap (K := K)) :=
  liftMap_injective _ (alternatingProductMap_surjective K)

/-- The trace pairing on the tensor square characterizes the alternating embedding. -/
theorem alternatingEmbeddingMap_pairing (x : V) (t : T) :
    TensorProduct.dualDistrib K V V
      (TensorProduct.map (TauCeti.traceDual K 3).toLinearMap (TauCeti.traceDual K 3).toLinearMap
        (alternatingEmbeddingMap x)) t =
        TauCeti.traceDual K 3 x (TauCeti.alternatingProductMap (K := K) (n := 3) t) :=
  liftMap_pairing _ x t

/-- The trace transpose of the traceless symmetric product into the tensor square. -/
noncomputable def symmetricEmbeddingMap : Representation.IntertwiningMap ρ σ :=
  liftMap (symmetricProductMap K)

/-- The symmetric product is surjective, so its trace transpose is injective. -/
theorem symmetricEmbeddingMap_injective : Function.Injective (symmetricEmbeddingMap (K := K)) :=
  liftMap_injective _ (symmetricProductMap_surjective K)

/-- The trace pairing on the tensor square characterizes the symmetric embedding. -/
theorem symmetricEmbeddingMap_pairing (x : V) (t : T) :
    TensorProduct.dualDistrib K V V
      (TensorProduct.map (TauCeti.traceDual K 3).toLinearMap (TauCeti.traceDual K 3).toLinearMap
        (symmetricEmbeddingMap x)) t =
        TauCeti.traceDual K 3 x (symmetricProductMap K t) :=
  liftMap_pairing _ x t

end TauCeti.AdjointSquare
