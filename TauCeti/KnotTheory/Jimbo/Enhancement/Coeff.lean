/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Jimbo.Enhancement.Basic

/-!
# Coefficients of the Jimbo enhancement

The enhancement is diagonal in the canonical word basis. This file exposes its coefficient
formula on arbitrary finitely supported vectors, so later trace and stabilization calculations
can use the enhancement without unfolding its linear-combination definition.
-/

public section

open Finsupp
open scoped BigOperators

namespace TauCeti.KnotTheory

variable {R : Type*} [CommRing R] {N n : ℕ}

/-- The coefficient of a word after applying the tensor-power enhancement is its original
coefficient multiplied by the product of the colour weights. -/
@[simp]
theorem jimboEnhancement_apply (q : Rˣ) (v : (Fin n → Fin N) →₀ R) (w : Fin n → Fin N) :
    jimboEnhancement q v w = (∏ i, jimboWeight q (w i)) * v w := by
  classical
  rw [jimboEnhancement_def]
  change (Finsupp.lapply w : ((Fin n → Fin N) →₀ R) →ₗ[R] R)
      (Finsupp.linearCombination R (fun u ↦ (∏ i, jimboWeight q (u i)) • single u 1) v) = _
  rw [Finsupp.apply_linearCombination]
  have hfamily :
      (Finsupp.lapply w : ((Fin n → Fin N) →₀ R) →ₗ[R] R) ∘
          (fun u ↦ (∏ i, jimboWeight q (u i)) • single u 1) =
        Pi.single w (∏ i, jimboWeight q (w i)) := by
    funext u
    by_cases h : u = w
    · subst u
      simp
    · simp [h]
  rw [hfamily, Finsupp.linearCombination_single_index]
  exact mul_comm _ _



end TauCeti.KnotTheory
