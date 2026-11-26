/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeromie Beasley
-/
module

public import TauCeti.RepresentationTheory.ClassicalGroups.Adjoint.Basic
import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import Mathlib.LinearAlgebra.Contraction
public import Mathlib.LinearAlgebra.Dual.Lemmas
import TauCeti.RepresentationTheory.Intertwining

/-!
# Invariant trace pairing on the adjoint square of SLₙ

The product of the trace pairings gives an equivariant self-duality of the tensor square.
-/

public section

namespace TauCeti.AdjointSquare

open scoped TensorProduct
variable {K : Type*} [Field K] {n : ℕ} [NeZero (n : K)]
local notation "V" => LieAlgebra.SpecialLinear.sl (Fin n) K
local notation "T" => V ⊗[K] V
local notation "ρ" => SLAdjoint.adjointRep K n
local notation "σ" => Representation.tprod ρ ρ


/-- The tensor product of the two perfect trace pairings identifies the square with its dual. -/
noncomputable def squareTrace : T ≃ₗ[K] Module.Dual K T :=
  let e := (SLAdjoint.traceDualEquiv K n).toLinearEquiv
  TensorProduct.congr e e ≪≫ₗ TensorProduct.dualDistribEquiv K V V

/-- Evaluating the square trace pairing amounts to evaluating the tensor product of the duals. -/
theorem squareTrace_apply (a b : T) :
    squareTrace a b = TensorProduct.dualDistrib K V V
      (TensorProduct.map (SLAdjoint.traceDualEquiv K n).toLinearEquiv.toLinearMap
        (SLAdjoint.traceDualEquiv K n).toLinearEquiv.toLinearMap a) b := by
  -- The underlying map of the composite equivalence is dualDistrib after the two trace duals.
  rw [squareTrace, LinearEquiv.trans_apply, ← TensorProduct.toLinearMap_congr,
    ← TensorProduct.toLinearMap_dualDistribEquiv]
  simp only [LinearEquiv.coe_coe]

/-- On pure tensors the square trace is the product of the factor trace forms. -/
@[simp] theorem squareTrace_tmul (x y u v : V) :
    squareTrace (x ⊗ₜ[K] y) (u ⊗ₜ[K] v) =
      LieAlgebra.SpecialLinear.traceForm K (Fin n) x u *
        LieAlgebra.SpecialLinear.traceForm K (Fin n) y v := by
  simp [squareTrace, Representation.Equiv.toLinearEquiv_apply, mul_comm]

/-- The tensor-square action preserves the square trace pairing. -/
@[simp↓] theorem squareTrace_tprod (g : Matrix.SpecialLinearGroup (Fin n) K) (a b : T) :
    squareTrace (σ g a) (σ g b) = squareTrace a b := by
  induction a using TensorProduct.inductionOn with
  | add a₁ a₂ h₁ h₂ => simp only [map_add, LinearMap.add_apply, h₁, h₂]
  | tmul x y =>
    induction b using TensorProduct.inductionOn with
    | add b₁ b₂ h₁ h₂ => simp only [map_add, h₁, h₂]
    | tmul u v => simp only [Representation.tprod_apply, TensorProduct.map_tmul,
        squareTrace_tmul, SLAdjoint.traceForm_adjointRep]

/-- The square trace pairing identifies the tensor-square action with its dual action. -/
noncomputable def squareTraceEquiv : Representation.Equiv σ (Representation.dual σ) :=
  let h : TauCeti.Representation.IsInvariantForm σ squareTrace.toLinearMap :=
    TauCeti.Representation.isInvariantForm_iff_isIsometry.mpr fun g =>
      TauCeti.BilinForm.isIsometry_iff.mpr (squareTrace_tprod g)
  h.equivDual (LinearMap.BilinForm.nondegenerate_iff_ker_eq_bot.mpr
    (LinearMap.ker_eq_bot_of_injective squareTrace.injective))

/-- The equivariant square trace identification evaluates by the square trace pairing. -/
@[simp] theorem squareTraceEquiv_apply (a b : T) : squareTraceEquiv a b = squareTrace a b := by
  rw [squareTraceEquiv, TauCeti.Representation.IsInvariantForm.equivDual_apply, LinearEquiv.coe_coe]

/-- Swapping the factors on one side of the tensor pairing swaps them on the other side. -/
theorem squareTrace_comm (a b : T) :
    squareTrace (TensorProduct.comm K V V a) b = squareTrace a (TensorProduct.comm K V V b) := by
  rw [squareTrace_apply, squareTrace_apply, TensorProduct.map_comm,
    TensorProduct.dualDistrib_apply_comm]

end TauCeti.AdjointSquare
