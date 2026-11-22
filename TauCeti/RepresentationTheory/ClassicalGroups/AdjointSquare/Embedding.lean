/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeromie Beasley
-/
module

public import TauCeti.RepresentationTheory.ClassicalGroups.AdjointSquare.Products
public import TauCeti.RepresentationTheory.ClassicalGroups.AdjointSquare.TracePairing
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
local notation "ρ" => adjointRep K
local notation "σ" => Representation.tprod (adjointRep K) (adjointRep K)

private noncomputable def squareTrace : T ≃ₗ[K] Module.Dual K T :=
  TensorProduct.congr traceDual traceDual ≪≫ₗ TensorProduct.dualDistribEquiv K V V

private theorem square_tmul (x y u v : V) :
    squareTrace (x ⊗ₜ[K] y) (u ⊗ₜ[K] v) = traceForm x u * traceForm y v := by
  simp [squareTrace, mul_comm]

private theorem square_invariant (g : Matrix.SpecialLinearGroup (Fin 3) K) (a b : T) :
    squareTrace (σ g a) (σ g b) = squareTrace a b := by
  induction a using TensorProduct.inductionOn with
  | add a₁ a₂ h₁ h₂ => simp only [map_add, LinearMap.add_apply, h₁, h₂]
  | tmul x y =>
    induction b using TensorProduct.inductionOn with
    | add b₁ b₂ h₁ h₂ => simp only [map_add, h₁, h₂]
    | tmul u v => simp only [Representation.tprod_apply, TensorProduct.map_tmul,
        square_tmul, traceForm_adjointRep]

private noncomputable def liftMap (f : Representation.IntertwiningMap σ ρ) :
    Representation.IntertwiningMap ρ σ where
  toLinearMap := squareTrace.symm.toLinearMap ∘ₗ f.toLinearMap.dualMap ∘ₗ traceDual.toLinearMap
  isIntertwining' g := by
    ext1 x
    change squareTrace.symm (f.toLinearMap.dualMap (traceDual (ρ g x))) =
      σ g (squareTrace.symm (f.toLinearMap.dualMap (traceDual x)))
    apply squareTrace.injective
    apply LinearMap.ext
    intro t
    rw [LinearEquiv.apply_symm_apply]
    have h := square_invariant g
      (squareTrace.symm (f.toLinearMap.dualMap (traceDual x))) (σ g⁻¹ t)
    rw [Representation.self_inv_apply, LinearEquiv.apply_symm_apply] at h
    rw [h]
    change traceForm (ρ g x) (f t) = traceForm x (f (σ g⁻¹ t))
    rw [f.isIntertwining]
    simpa only [Representation.self_inv_apply] using traceForm_adjointRep g x (ρ g⁻¹ (f t))

private theorem liftMap_injective (f : Representation.IntertwiningMap σ ρ)
    (hf : Function.Surjective f) :
    Function.Injective (liftMap f) :=
  squareTrace.symm.injective.comp ((LinearMap.dualMap_injective_of_surjective hf).comp
    traceDual.injective)

private theorem liftMap_pairing (f : Representation.IntertwiningMap σ ρ) (x : V) (t : T) :
    TensorProduct.dualDistrib K V V
      (TensorProduct.map traceDual.toLinearMap traceDual.toLinearMap (liftMap f x)) t =
        traceDual x (f t) := by
  rw [← TensorProduct.toLinearMap_dualDistribEquiv]
  change squareTrace (squareTrace.symm (f.toLinearMap.dualMap (traceDual x))) t = _
  rw [LinearEquiv.apply_symm_apply]
  rfl


/-- The trace transpose of the Lie bracket as an equivariant map into the tensor square. -/
noncomputable def alternatingEmbeddingMap : Representation.IntertwiningMap ρ σ :=
  liftMap (alternatingProductMap K)

/-- The alternating product is surjective, so its trace transpose is injective. -/
theorem alternatingEmbeddingMap_injective : Function.Injective (alternatingEmbeddingMap (K := K)) :=
  liftMap_injective _ (alternating_surjective_of_tmul
    (alternatingProductMap K).toLinearMap fun _ _ => rfl)

/-- The trace pairing on the tensor square characterizes the alternating embedding. -/
theorem alternatingEmbeddingMap_pairing (x : V) (t : T) :
    TensorProduct.dualDistrib K V V
      (TensorProduct.map traceDual.toLinearMap traceDual.toLinearMap
        (alternatingEmbeddingMap x)) t =
        traceDual x (alternatingProductMap K t) :=
  liftMap_pairing _ x t

/-- The trace transpose of the traceless symmetric product into the tensor square. -/
noncomputable def symmetricEmbeddingMap : Representation.IntertwiningMap ρ σ :=
  liftMap (symmetricProductMap K)

/-- The symmetric product is surjective, so its trace transpose is injective. -/
theorem symmetricEmbeddingMap_injective : Function.Injective (symmetricEmbeddingMap (K := K)) :=
  liftMap_injective _ (symmetric_surjective_of_tmul
    (symmetricProductMap K).toLinearMap fun _ _ => rfl)

/-- The trace pairing on the tensor square characterizes the symmetric embedding. -/
theorem symmetricEmbeddingMap_pairing (x : V) (t : T) :
    TensorProduct.dualDistrib K V V
      (TensorProduct.map traceDual.toLinearMap traceDual.toLinearMap (symmetricEmbeddingMap x)) t =
        traceDual x (symmetricProductMap K t) :=
  liftMap_pairing _ x t

end TauCeti.AdjointSquare
