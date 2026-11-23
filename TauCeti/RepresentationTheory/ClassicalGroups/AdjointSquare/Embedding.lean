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
import TauCeti.RepresentationTheory.Intertwining

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
local notation "ρ" => SLAdjoint.adjointRep K 3
local notation "σ" => Representation.tprod ρ ρ

private abbrev traceForm₃ : LinearMap.BilinForm K V := SLAdjoint.traceForm K 3

private noncomputable abbrev traceDual₃ : V ≃ₗ[K] Module.Dual K V := SLAdjoint.traceDual K 3

/-- The tensor product of the two perfect trace pairings identifies the square with its dual. -/
noncomputable def squareTrace : T ≃ₗ[K] Module.Dual K T :=
  TensorProduct.congr traceDual₃ traceDual₃ ≪≫ₗ TensorProduct.dualDistribEquiv K V V

/-- Evaluating the square trace pairing amounts to evaluating the tensor product of the duals. -/
theorem squareTrace_apply (a b : T) :
    squareTrace a b = TensorProduct.dualDistrib K V V
      (TensorProduct.map (SLAdjoint.traceDual K 3).toLinearMap
        (SLAdjoint.traceDual K 3).toLinearMap a) b := by
  rw [← TensorProduct.toLinearMap_dualDistribEquiv]
  rfl

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
        square_tmul, SLAdjoint.traceForm_adjointRep]

private noncomputable def squareTraceEquiv : Representation.Equiv σ (Representation.dual σ) :=
  Representation.Equiv.mk squareTrace fun g => by
    apply LinearMap.ext
    intro a
    apply LinearMap.ext
    intro b
    simpa only [LinearMap.comp_apply, Representation.dual_apply, Module.Dual.transpose_apply,
      LinearEquiv.coe_coe, Representation.self_inv_apply] using square_invariant g a (σ g⁻¹ b)

private noncomputable def liftMap (f : Representation.IntertwiningMap σ ρ) :
    Representation.IntertwiningMap ρ σ :=
  let hf : Representation.IsIntertwiningMap σ ρ f.toLinearMap := ⟨f.isIntertwining⟩
  squareTraceEquiv.symm.toIntertwiningMap.comp
    ((f.toLinearMap.dualMap.intertwiningMap_of_isIntertwiningMap _ _ hf.dualMap.isIntertwining).comp
      (SLAdjoint.traceDualEquiv K 3).toIntertwiningMap)

private theorem liftMap_injective (f : Representation.IntertwiningMap σ ρ)
    (hf : Function.Surjective f) : Function.Injective (liftMap f) :=
  squareTrace.symm.injective.comp ((LinearMap.dualMap_injective_of_surjective hf).comp
    (SLAdjoint.traceDualEquiv K 3).toLinearEquiv.injective)

private theorem liftMap_pairing (f : Representation.IntertwiningMap σ ρ) (x : V) (t : T) :
    squareTrace (liftMap f x) t = (SLAdjoint.traceDualEquiv K 3 x) (f t) := by
  -- The inverse equivalence in the composite is the inverse of the square trace pairing.
  change squareTrace (squareTrace.symm _) t = _
  rw [LinearEquiv.apply_symm_apply]
  rfl

/-- Swapping the factors on one side of the tensor pairing swaps them on the other side. -/
theorem squareTrace_comm (a b : T) :
    squareTrace (TensorProduct.comm K V V a) b = squareTrace a (TensorProduct.comm K V V b) := by
  rw [squareTrace_apply, squareTrace_apply, TensorProduct.map_comm,
    TensorProduct.dualDistrib_apply_comm]

/-- The trace transpose of the Lie bracket as an equivariant map into the tensor square. -/
noncomputable def alternatingEmbeddingMap : Representation.IntertwiningMap ρ σ :=
  liftMap (SLAdjoint.alternatingProductMap (K := K) (n := 3))

/-- The alternating product is surjective, so its trace transpose is injective. -/
theorem alternatingEmbeddingMap_injective : Function.Injective (alternatingEmbeddingMap (K := K)) :=
  liftMap_injective _ (alternatingProductMap_surjective K)

/-- The trace pairing on the tensor square characterizes the alternating embedding. -/
theorem alternatingEmbeddingMap_pairing (x : V) (t : T) :
    squareTrace (alternatingEmbeddingMap x) t =
      (SLAdjoint.traceDualEquiv K 3 x) (SLAdjoint.alternatingProductMap K 3 t) :=
  liftMap_pairing _ x t

/-- The trace transpose of the traceless symmetric product into the tensor square. -/
noncomputable def symmetricEmbeddingMap : Representation.IntertwiningMap ρ σ :=
  liftMap (symmetricProductMap K 3)

/-- The symmetric product is surjective, so its trace transpose is injective. -/
theorem symmetricEmbeddingMap_injective : Function.Injective (symmetricEmbeddingMap (K := K)) :=
  liftMap_injective _ (symmetricProductMap_surjective K)

/-- The trace pairing on the tensor square characterizes the symmetric embedding. -/
theorem symmetricEmbeddingMap_pairing (x : V) (t : T) :
    squareTrace (symmetricEmbeddingMap x) t =
      (SLAdjoint.traceDualEquiv K 3 x) (symmetricProductMap K 3 t) :=
  liftMap_pairing _ x t

end TauCeti.AdjointSquare
