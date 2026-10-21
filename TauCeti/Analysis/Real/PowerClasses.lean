/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.RingTheory.RootsOfUnity.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import TauCeti.Algebra.Order.Ring.Units
import TauCeti.GroupTheory.Index.NSmul

/-!
# The `n`-th power classes of `ℝ`

For `n ≠ 0`, the quotient `ℝˣ ⧸ (ℝˣ)ⁿ` has as many elements as there are `n`-th roots of unity in
`ℝ`: one for odd `n`, two for even `n`. This is the local count at a real place of a number field.

## Main results

* `TauCeti.card_powerClasses_real`: `#(ℝˣ ⧸ (ℝˣ)ⁿ) = #μ_n(ℝ)` for `n ≠ 0`.
-/

public section

namespace TauCeti

/-- **The `n`-th power classes of `ℝ`.** For `n ≠ 0`, the quotient `ℝˣ ⧸ (ℝˣ)ⁿ` has as many
elements as there are `n`-th roots of unity in `ℝ`: one for odd `n`, two for even `n`. -/
theorem card_powerClasses_real {n : ℕ} (hn : n ≠ 0) :
    Nat.card (ℝˣ ⧸ (powMonoidHom n : ℝˣ →* ℝˣ).range) = Nat.card (rootsOfUnity n ℝ) := by
  -- Compare with the positive units, a subgroup of index two on which `x ↦ xⁿ` is bijective.
  have h := Subgroup.index_range_pow_mul_card_ker (Units.posSubgroup ℝ) n
  have hker : (powMonoidHom n : Units.posSubgroup ℝ →* Units.posSubgroup ℝ).ker = ⊥ :=
    (MonoidHom.ker_eq_bot_iff _).2 (pow_left_injective hn)
  have hrange : (powMonoidHom n : Units.posSubgroup ℝ →* Units.posSubgroup ℝ).range = ⊤ := by
    refine MonoidHom.range_eq_top.2 fun x ↦ ?_
    have hx : (0 : ℝ) < ((x : ℝˣ) : ℝ) := (Units.mem_posSubgroup _).1 x.2
    have hy : (0 : ℝ) < ((x : ℝˣ) : ℝ) ^ (n⁻¹ : ℝ) := Real.rpow_pos_of_pos hx _
    refine ⟨⟨Units.mk0 _ hy.ne', (Units.mem_posSubgroup _).2 hy⟩, ?_⟩
    ext
    simp [Real.rpow_inv_natCast_pow hx.le hn]
  have hG : (powMonoidHom n : ℝˣ →* ℝˣ).ker = rootsOfUnity n ℝ := by
    ext
    simp
  rw [hker, hrange, hG, Subgroup.index_top, Subgroup.card_bot, mul_one, mul_one] at h
  rw [← Subgroup.index_eq_card, h]

end TauCeti
