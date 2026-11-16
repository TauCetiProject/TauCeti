/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Lie modules with the same action matrices

A Lie module over a commutative ring with a finite basis is determined up to equivalence by the
matrices of the action of the Lie algebra in that basis: the linear equivalence matching two bases
with the same index type intertwines two actions with the same matrices.

## Main results

* `TauCeti.nonempty_lieModuleEquiv_of_toMatrix_eq`: two Lie modules whose actions
  have the same matrices in bases with the same index type are equivalent.
-/

public section

open Module

namespace TauCeti

variable {R : Type*} {L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]

/-- **A Lie module is determined by the matrices of its action.** Two Lie modules whose actions
have the same matrices in bases indexed by the same type are equivalent, through the linear
equivalence matching the two bases. -/
theorem nonempty_lieModuleEquiv_of_toMatrix_eq {ι : Type*} [Fintype ι] [DecidableEq ι]
    {M N : Type*} [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]
    [AddCommGroup N] [Module R N] [LieRingModule L N] [LieModule R L N]
    (b : Basis ι R M) (c : Basis ι R N)
    (h : ∀ x : L, LinearMap.toMatrix b b (LieModule.toEnd R L M x) =
      LinearMap.toMatrix c c (LieModule.toEnd R L N x)) :
    Nonempty (M ≃ₗ⁅R,L⁆ N) := by
  let e := b.equiv c (Equiv.refl ι)
  refine ⟨{ e with map_lie' := fun {x m} ↦ ?_ }⟩
  have key : e.toLinearMap ∘ₗ LieModule.toEnd R L M x =
      (LieModule.toEnd R L N x : N →ₗ[R] N) ∘ₗ e.toLinearMap := by
    obtain ⟨A, hA⟩ : ∃ A, LinearMap.toMatrix c c (LieModule.toEnd R L N x) = A := ⟨_, rfl⟩
    have hM : (LieModule.toEnd R L M x : M →ₗ[R] M) = Matrix.toLin b b A := by
      rw [← hA, ← h x, Matrix.toLin_toMatrix]
    have hN : (LieModule.toEnd R L N x : N →ₗ[R] N) = Matrix.toLin c c A := by
      rw [← hA, Matrix.toLin_toMatrix]
    refine b.ext fun i ↦ ?_
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, hM, hN, Matrix.toLin_self, map_sum,
      map_smul, e, Basis.equiv_apply, Equiv.refl_apply]
  simpa using LinearMap.congr_fun key m

end TauCeti
