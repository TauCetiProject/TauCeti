/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.QuadraticForm.IsometryEquiv

/-!
# Diagonal quadratic forms

This file provides general infrastructure for diagonal quadratic forms expressed as weighted sums
of squares.

## Main results

* `TauCeti.equivalent_weightedSumSquares_comp`: reindexing the coefficients preserves equivalence.
-/

public section

namespace TauCeti

universe u v

variable {R : Type u} [CommSemiring R] {ι : Type v} [Fintype ι]

/-- Permuting the coefficients of a diagonal form does not change its equivalence class. -/
theorem equivalent_weightedSumSquares_comp (w : ι → R) (σ : Equiv.Perm ι) :
    (QuadraticMap.weightedSumSquares R w).Equivalent
      (QuadraticMap.weightedSumSquares R (w ∘ σ)) := by
  refine ⟨{
    toLinearEquiv := LinearEquiv.funCongrLeft R R σ
    map_app' := fun x => ?_ }⟩
  simp only [QuadraticMap.weightedSumSquares_apply, Function.comp_apply, smul_eq_mul]
  simpa using (Equiv.sum_comp σ.symm (fun i => w (σ i) * (x (σ i) * x (σ i)))).symm

end TauCeti
