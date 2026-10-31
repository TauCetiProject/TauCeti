/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.DirichletCharacter.Bounds
import Mathlib.Data.Nat.Periodic

/-!
# Partial sums of nonprincipal Dirichlet characters

The sum of a nonprincipal character over a full period vanishes. Consequently its partial
sums depend only on the endpoint modulo the level, and for characters valued in a normed
field their norms are bounded by the level. This cancellation is the input to partial
summation estimates for continued Dirichlet L-functions.
-/

public section

open Finset

namespace DirichletCharacter

variable {N : ℕ} [NeZero N]

/-- The partial sum of a nonprincipal character depends only on the endpoint modulo its level. -/
theorem sum_range_eq_sum_range_mod {R : Type*} [CommRing R] [IsDomain R]
    (χ : DirichletCharacter R N) (hχ : χ ≠ 1) (n : ℕ) :
    ∑ k ∈ range n, χ k = ∑ k ∈ range (n % N), χ k := by
  have hzero : ∑ k ∈ range N, χ k = 0 := by
    rw [← Fin.sum_univ_eq_sum_range]
    have hcast (i : Fin N) : ZMod.finEquiv N i = (i.val : ZMod N) := by
      -- The equivalence is defined by the successor presentation of `ZMod`.
      cases N with
      | zero => exact (NeZero.ne 0 rfl).elim
      | succ N => exact (Fin.cast_val_eq_self i).symm
    simpa only [RingEquiv.toEquiv_eq_coe, RingEquiv.coe_toEquiv, hcast] using
      ((ZMod.finEquiv N).toEquiv.sum_comp χ).trans (MulChar.sum_eq_zero_of_ne_one hχ)
  have hperiod : Function.Periodic (fun n : ℕ ↦ ∑ k ∈ range n, χ k) N := by
    intro n
    dsimp only
    rw [add_comm n N, sum_range_add, hzero, zero_add]
    simp
  exact (hperiod.map_mod_nat n).symm

/-- Partial sums of a nonprincipal character valued in a normed field are bounded by its level,
independently of the endpoint. -/
theorem norm_sum_Icc_le_level {F : Type*} [NormedField F]
    (χ : DirichletCharacter F N) (hχ : χ ≠ 1) (n : ℕ) :
    ‖∑ k ∈ Icc 1 n, χ k‖ ≤ (N : ℝ) := by
  have hsum : ∑ k ∈ Icc 1 n, χ k = ∑ k ∈ range (n + 1), χ k := by
    rw [Nat.range_succ_eq_Icc_zero, ← insert_Icc_add_one_left_eq_Icc n.zero_le]
    simp [χ.map_zero' (by rintro rfl; exact hχ (Subsingleton.elim _ _))]
  rw [hsum, χ.sum_range_eq_sum_range_mod hχ]
  calc
    _ ≤ ∑ k ∈ range ((n + 1) % N), (1 : ℝ) :=
      (norm_sum_le _ _).trans (sum_le_sum fun k _ ↦ χ.norm_le_one k)
    _ ≤ (N : ℝ) := by simpa using (Nat.cast_le.mpr (Nat.mod_lt (n + 1) (NeZero.pos N)).le :
      (((n + 1) % N : ℕ) : ℝ) ≤ N)

end DirichletCharacter
