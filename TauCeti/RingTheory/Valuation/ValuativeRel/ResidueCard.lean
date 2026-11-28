/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Basic.ENNReal.Inv
public import Mathlib.Topology.Algebra.Valued.ValuativeRel
import Mathlib.SetTheory.Cardinal.Finite

/-!
# Extended-nonnegative residue-field cardinality factors

Basic nonzero and finiteness lemmas in `ℝ≥0∞` for the residue-field scaling factors `1 - q⁻¹` and
`q ^ (-n) · (1 - q⁻¹)`, where `q = Nat.card 𝓀[K]` is the cardinality of a finite residue field.

## Main results

* `TauCeti.one_sub_inv_natCard_residueField_ne_zero`: `1 - q⁻¹ ≠ 0`.
* `TauCeti.one_div_natCard_residueField_pow_mul_one_sub_ne_zero`: `q ^ (-n) · (1 - q⁻¹) ≠ 0`.
* `TauCeti.one_div_natCard_residueField_pow_mul_one_sub_ne_top`: `q ^ (-n) · (1 - q⁻¹) ≠ ∞`.
-/

public section

open ValuativeRel
open scoped ENNReal

namespace TauCeti

/-- The local convergence factor `1 - q⁻¹` is nonzero when the residue field is finite, since its
residue field has `q > 1` elements. -/
theorem one_sub_inv_natCard_residueField_ne_zero (K : Type*) [Field K] [ValuativeRel K]
    [Finite 𝓀[K]] : 1 - (Nat.card 𝓀[K] : ℝ≥0∞)⁻¹ ≠ 0 :=
  (tsub_pos_iff_lt.2 (ENNReal.inv_lt_one.2 (by exact_mod_cast Finite.one_lt_card))).ne'

variable {K : Type*} [Field K] [ValuativeRel K] [Finite 𝓀[K]]

/-- The scaling factor `q ^ (-n) · (1 - q⁻¹)` is nonzero when the residue field is finite. -/
theorem one_div_natCard_residueField_pow_mul_one_sub_ne_zero {n : ℕ} :
    1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ n * (1 - 1 / (Nat.card 𝓀[K] : ℝ≥0∞)) ≠ 0 :=
  mul_ne_zero
    (ENNReal.div_pos one_ne_zero (ENNReal.pow_ne_top (ENNReal.natCast_ne_top _))).ne'
    (by simpa [one_div] using one_sub_inv_natCard_residueField_ne_zero K)

/-- The scaling factor `q ^ (-n) · (1 - q⁻¹)` is finite when the residue field is finite. -/
theorem one_div_natCard_residueField_pow_mul_one_sub_ne_top {n : ℕ} :
    1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ n * (1 - 1 / (Nat.card 𝓀[K] : ℝ≥0∞)) ≠ ∞ := by
  have hq : (1 : ℝ≥0∞) ≤ Nat.card 𝓀[K] := by exact_mod_cast Nat.card_pos
  refine ENNReal.mul_ne_top (ne_top_of_le_ne_top ENNReal.one_ne_top ?_)
    (ENNReal.sub_ne_top ENNReal.one_ne_top)
  rw [one_div]
  exact ENNReal.inv_le_one.2 (one_le_pow₀ hq)

end TauCeti
