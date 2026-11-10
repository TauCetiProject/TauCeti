/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula

/-!
# Level-one cusp forms: odd-weight vanishing and the dimension formula

Mathlib's `Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula` proves that every level-one
modular form of odd weight vanishes (`ModularForm.levelOne_odd_weight_eq_zero`), and computes the
dimension of the space of level-one modular forms of even weight
(`ModularForm.dimension_level_one`). This file records the `CuspForm` companions: the first via the
injective inclusion `CuspForm.toModularFormₗ`, the second from the decomposition
`dim M_k = 1 + dim S_k` (`ModularForm.rank_eq_one_add_rank_cuspForm`) in weight `k ≥ 3`.

## Main results

* `CuspForm.levelOne_odd_weight_eq_zero`: every cusp form of odd weight on `SL(2, ℤ)` is zero.
* `CuspForm.dimension_level_one`: for even `k`, `dim S_k(SL(2, ℤ))` is `⌊k / 12⌋ - 1` if
  `k ≡ 2 (mod 12)` and `⌊k / 12⌋` otherwise.
-/

public section

open Module
open scoped MatrixGroups

namespace CuspForm

/-- A level-one cusp form of odd weight is zero, the `CuspForm` companion to
`ModularForm.levelOne_odd_weight_eq_zero`. -/
theorem levelOne_odd_weight_eq_zero {k : ℤ} (hk : Odd k) (f : CuspForm 𝒮ℒ k) : f = 0 :=
  toModularFormₗ_injective (ModularForm.levelOne_odd_weight_eq_zero hk f)

/-- **The dimension formula for level-one cusp forms of even weight**: `dim S_k(SL(2, ℤ))` is
`⌊k / 12⌋ - 1` if `k ≡ 2 (mod 12)` and `⌊k / 12⌋` otherwise. This is the `CuspForm` companion to
`ModularForm.dimension_level_one`; in weights below `12` both sides vanish. -/
theorem dimension_level_one (k : ℕ) (hk2 : Even k) :
    finrank ℂ (CuspForm 𝒮ℒ k) = if k ≡ 2 [MOD 12] then k / 12 - 1 else k / 12 := by
  rcases lt_or_ge k 12 with hk | hk
  · -- below weight twelve there are no cusp forms
    rw [finrank_eq_zero_of_rank_eq_zero (rank_eq_zero_of_weight_lt_twelve (by exact_mod_cast hk)),
      Nat.div_eq_of_lt hk]
    simp
  · -- `dim M_k = 1 + dim S_k`, with `dim M_k` given by `ModularForm.dimension_level_one`
    have : FiniteDimensional ℂ (CuspForm 𝒮ℒ k) := .of_injective _ toModularFormₗ_injective
    have hMS := ModularForm.rank_eq_one_add_rank_cuspForm (k := k) (by omega) hk2
    rw [← finrank_eq_rank, ← finrank_eq_rank] at hMS
    norm_cast at hMS
    have hM := finrank_eq_of_rank_eq (ModularForm.dimension_level_one k hk2)
    split_ifs at hM ⊢ <;> omega

end CuspForm
