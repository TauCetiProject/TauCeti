/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.FieldTheory.Finite.Basic
import Mathlib.NumberTheory.Padics.RingHoms
import TauCeti.NumberTheory.Padics.Complex.Basic
import TauCeti.RingTheory.Perfectoid.Padic

/-!
# Checks for perfectoid fields

`ℂ_p` is a perfectoid field, so its value group is `p`-divisible: `‖p‖ = p⁻¹` is the `p`-th power
of a norm. `ℚ_p` is not a perfectoid field, although `‖p‖ < 1` and the `p`-th power map on
`ℤ_p ⧸ p = 𝔽_p` is surjective. By the characterisation, the norms of `ℚ_p` therefore do not
accumulate at `1`: the condition that a perfectoid field is not discretely valued cannot be dropped.
In characteristic `p`, the characterisation reduces to perfectness.
-/

open TauCeti.Huber TauCeti.Perfectoid

namespace TauCeti.Examples

variable (p : ℕ) [Fact p.Prime]

example : IsPerfectoidField p ℂ_[p] := inferInstance

-- The norm `p⁻¹` of `p` in `ℂ_p` is the `p`-th power of a norm.
example : ∃ y : ℂ_[p], ‖y‖ ^ p = (p : ℝ)⁻¹ := by
  simpa using IsPerfectoidField.exists_norm_pow_eq (p := p) (p : ℂ_[p])

-- The norms of `ℂ_p` accumulate at `1`.
example : ∃ x : ℂ_[p], 1 < ‖x‖ ∧ ‖x‖ < 1 + (p : ℝ)⁻¹ :=
  IsPerfectoidField.exists_one_lt_norm_lt p
    (lt_add_of_pos_right 1 (inv_pos.mpr (Nat.cast_pos.mpr (Fact.out : p.Prime).pos)))

example : ¬ IsPerfectoidField p ℚ_[p] :=
  fun h ↦ not_isPerfectoidTateRing_padic p h.toIsPerfectoidTateRing

-- `ℚ_p` satisfies conditions (ii) and (iii) of the characterisation (every `x ∈ ℤ_p` has
-- `x ≡ x ^ p` modulo `p`), so it fails (i).
example : ¬ ∀ ε : ℝ, 1 < ε → ∃ x : ℚ_[p], 1 < ‖x‖ ∧ ‖x‖ < ε := by
  intro hacc
  have hs (x : powerBoundedSubring ℚ_[p]) : ∃ y, (p : powerBoundedSubring ℚ_[p]) ∣ x - y ^ p := by
    refine ⟨x, powerBoundedSubring.dvd_iff_norm_le.mpr ?_⟩
    let z : ℤ_[p] := ⟨x, isPowerBounded_iff_norm_le_one.mp (mem_powerBoundedSubring.mp x.2)⟩
    have hz : z - z ^ p ∈ Ideal.span {(p : ℤ_[p]) ^ 1} := by
      rw [pow_one, ← PadicInt.maximalIdeal_eq_span_p, ← PadicInt.ker_toZMod, RingHom.mem_ker,
        map_sub, map_pow, ZMod.pow_card, sub_self]
    have h := (PadicInt.norm_le_pow_iff_mem_span_pow _ 1).mpr hz
    rw [PadicInt.norm_def, PadicInt.coe_sub, PadicInt.coe_pow] at h
    simpa [Padic.norm_p] using h
  exact not_isPerfectoidTateRing_padic p (isPerfectoidField_iff_isPerfectoidTateRing.mp
    (isPerfectoidField_iff.mpr ⟨hacc, Padic.norm_p_lt_one, (surjective_pow_modP_iff _).mpr hs⟩))

-- In characteristic `p` the characterisation reduces to perfectness.
example (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
    [CharP K p] [PerfectRing K p] : IsPerfectoidField p K :=
  isPerfectoidField_iff_perfectRing.mpr inferInstance

end TauCeti.Examples
