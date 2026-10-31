/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.ModelTheory.BackAndForth.PureSet
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Data.Set.Finite.Range

/-!
# Regression examples: back-and-forth levels separate finite pure sets from infinite ones

Through public statements only, these examples check for the pure sets `ℕ` and `Fin 3`:

* their empty tuples are back-and-forth equivalent at level `3` but not at level `4`;
* they are not equivalent at level `ω`, although they are at every finite level up to `3`;
* in `ℕ`, a tuple and a tuple with a different equality pattern are inequivalent already at
  level zero, while two injective tuples of the same length are equivalent at every level.
-/

open FirstOrder TauCeti

attribute [local instance] Language.emptyStructure

-- The empty tuples of `ℕ` and `Fin 3` are equivalent at level `3`.
example : BFEquiv (L := Language.empty) ((3 : ℕ) : Ordinal.{0}) 0 (Fin.elim0 : Fin 0 → ℕ)
    (Fin.elim0 : Fin 0 → Fin 3) := by
  rw [bfEquiv_empty_elim0_natCast_iff_le_card, ENat.card_eq_coe_fintype_card, Fintype.card_fin]

-- The empty tuples of `ℕ` and `Fin 3` are not equivalent at level `4`: four rounds exhaust
-- `Fin 3`.
example : ¬ BFEquiv (L := Language.empty) ((4 : ℕ) : Ordinal.{0}) 0 (Fin.elim0 : Fin 0 → ℕ)
    (Fin.elim0 : Fin 0 → Fin 3) := by
  rw [bfEquiv_empty_elim0_natCast_iff_le_card, ENat.card_eq_coe_fintype_card, Fintype.card_fin,
    Nat.cast_le]
  omega

-- The empty tuples of `ℕ` and `Fin 3` are not equivalent at level `ω`.
example : ¬ BFEquiv (L := Language.empty) Ordinal.omega0.{0} 0 (Fin.elim0 : Fin 0 → ℕ)
    (Fin.elim0 : Fin 0 → Fin 3) := by
  rw [bfEquiv_empty_iff_of_omega0_le le_rfl]
  simp

-- A tuple with a repeated entry and an injective tuple are inequivalent at level zero.
example : ¬ BFEquiv (L := Language.empty) ((0 : ℕ) : Ordinal.{0}) 2 ![(0 : ℕ), 0] ![0, 1] := by
  rw [bfEquiv_empty_natCast_iff]
  intro h
  simpa using (h.1 0 1).mp rfl

-- Two injective pairs in `ℕ` are equivalent at every level.
example (α : Ordinal.{0}) : BFEquiv (L := Language.empty) α 2 ![(0 : ℕ), 1] ![5, 7] := by
  apply bfEquiv_empty_of_encard_compl_range_eq
  · intro i j
    fin_cases i <;> fin_cases j <;> simp
  · rw [(Set.finite_range _).infinite_compl.encard_eq,
      (Set.finite_range _).infinite_compl.encard_eq]
