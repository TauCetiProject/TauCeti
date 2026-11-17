/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.NumberTheory.DirichletCharacter.Bounds
import Mathlib.Data.Nat.Periodic
import TauCeti.Data.ZMod.FinEquiv

/-!
# Partial sums of nonprincipal Dirichlet characters

The sum of a nonprincipal character over a full period vanishes (both on `0 ≤ k < N` and on
`1 ≤ k ≤ N`). Consequently its partial sums depend only on the endpoint modulo the level, and for
characters valued in a normed field their norms are bounded by the level (hence `O(n ^ 0)` for
every level `N`, including `N = 0`). This cancellation is the input to partial summation estimates
for continued Dirichlet L-functions.

## Main results

* `DirichletCharacter.sum_range_level_eq_zero`, `DirichletCharacter.sum_Icc_one_level_eq_zero`:
  cancellation of a nonprincipal character over a full period `0 ≤ k < N` and `1 ≤ k ≤ N`.
* `DirichletCharacter.sum_range_eq_sum_range_mod`: periodicity of partial sums modulo the level.
* `DirichletCharacter.norm_sum_Icc_le_level`: `‖∑ k ∈ Icc 1 n, χ k‖ ≤ N` for normed-field-valued
  nonprincipal characters of nonzero level `N`.
* `DirichletCharacter.sum_Icc_isBigO_rpow_zero`: `∑ k ∈ Icc 1 n, χ k = O(n ^ 0)` as `n → ∞`,
  without a nonzero-level assumption.
-/

public section

open Asymptotics Filter Finset

namespace DirichletCharacter

variable {N : ℕ} [NeZero N]

/-- The sum of a nonprincipal character over a full period vanishes. -/
theorem sum_range_level_eq_zero {R : Type*} [CommRing R] [IsDomain R]
    (χ : DirichletCharacter R N) (hχ : χ ≠ 1) : ∑ k ∈ range N, χ k = 0 := by
  rw [← Fin.sum_univ_eq_sum_range]
  simpa only [RingEquiv.toEquiv_eq_coe, RingEquiv.coe_toEquiv, ZMod.finEquiv_apply] using
    ((ZMod.finEquiv N).toEquiv.sum_comp χ).trans (MulChar.sum_eq_zero_of_ne_one hχ)

omit [NeZero N] in
/-- A nonprincipal Dirichlet character sums to zero over `1 ≤ k ≤ N`. -/
theorem sum_Icc_one_level_eq_zero {R : Type*} [CommRing R] [IsDomain R]
    (χ : DirichletCharacter R N) (hχ : χ ≠ 1) :
    ∑ k ∈ Icc 1 N, χ k = 0 := by
  rcases N.eq_zero_or_pos with rfl | hN
  · simp
  have : NeZero N := ⟨hN.ne'⟩
  have h1 : ∑ k ∈ Icc 1 N, χ k = χ (0 : ZMod N) + ∑ k ∈ Ico 1 N, χ k := by
    rw [← insert_right_Ico hN, sum_insert right_notMem_Ico, ZMod.natCast_self]
  have h2 : ∑ k ∈ range N, χ k = χ (0 : ZMod N) + ∑ k ∈ Ico 1 N, χ k := by
    rw [range_eq_Ico, ← insert_Ico_add_one_left_eq_Ico hN, zero_add,
      sum_insert (by simp), Nat.cast_zero]
  exact h1.trans (h2.symm.trans (χ.sum_range_level_eq_zero hχ))

/-- The partial sum of a nonprincipal character depends only on the endpoint modulo its level. -/
theorem sum_range_eq_sum_range_mod {R : Type*} [CommRing R] [IsDomain R]
    (χ : DirichletCharacter R N) (hχ : χ ≠ 1) (n : ℕ) :
    ∑ k ∈ range n, χ k = ∑ k ∈ range (n % N), χ k := by
  have hperiod : Function.Periodic (fun n : ℕ ↦ ∑ k ∈ range n, χ k) N := by
    intro n
    dsimp only
    rw [add_comm n N, sum_range_add, χ.sum_range_level_eq_zero hχ, zero_add]
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
    _ ≤ ∑ _ ∈ range ((n + 1) % N), (1 : ℝ) :=
      (norm_sum_le _ _).trans (sum_le_sum fun k _ ↦ χ.norm_le_one k)
    _ ≤ (N : ℝ) := by simpa using (Nat.cast_le.mpr (Nat.mod_lt (n + 1) (NeZero.pos N)).le :
      (((n + 1) % N : ℕ) : ℝ) ≤ N)

omit [NeZero N] in
/-- The partial sums `∑_{k=1}^n χ(k)` of a nonprincipal Dirichlet character are `O(n ^ 0)` as
`n → ∞`. -/
theorem sum_Icc_isBigO_rpow_zero {F : Type*} [NormedField F] (χ : DirichletCharacter F N)
    (hχ : χ ≠ 1) :
    (fun n : ℕ ↦ ∑ k ∈ Icc 1 n, χ k) =O[atTop] fun n ↦ (n : ℝ) ^ (0 : ℝ) := by
  rcases N.eq_zero_or_pos with rfl | hN
  · refine isBigO_iff.mpr ⟨‖χ 1‖, Eventually.of_forall fun n ↦ ?_⟩
    have hsub : ∑ k ∈ Icc 1 n, χ k = if 1 ≤ n then χ 1 else 0 := by
      split_ifs with hn
      · rw [← sum_erase_add (Icc 1 n) _ (left_mem_Icc.mpr hn), sum_eq_zero, zero_add, Nat.cast_one]
        intro k hk
        rw [mem_erase, mem_Icc] at hk
        -- In `ZMod 0`, `k : ℕ` is a unit iff `k.Coprime 0`, i.e., `k = 1`.
        exact MulChar.map_nonunit χ fun hu ↦
          hk.1 ((Nat.coprime_zero_right k).mp ((ZMod.isUnit_iff_coprime k 0).mp hu))
      · rw [Icc_eq_empty hn, sum_empty]
    split_ifs at hsub <;> simp [hsub]
  · have : NeZero N := ⟨hN.ne'⟩
    refine isBigO_iff.mpr ⟨N, Eventually.of_forall fun n ↦ ?_⟩
    simpa using χ.norm_sum_Icc_le_level hχ n

end DirichletCharacter
