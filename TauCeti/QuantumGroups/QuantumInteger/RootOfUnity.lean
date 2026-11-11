/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import TauCeti.QuantumGroups.QuantumInteger.Chebyshev
public import TauCeti.QuantumGroups.QuantumInteger.Laurent.Basic

import TauCeti.Algebra.Ring.Units

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

/-!
# Quantum integers at a loop parameter and roots of unity

The quantum integers `TauCeti.qInt R δ n` are defined at an arbitrary loop parameter `δ`, with no
`q` in sight. At `δ = u + u⁻¹` for a unit `u` they satisfy `(u - u⁻¹) [n] = uⁿ - u⁻ⁿ`
(`TauCeti.sub_inv_mul_qInt_add_inv`, in `TauCeti/QuantumGroups/QuantumInteger/Laurent/Basic.lean`).
This file derives from it the dictionary between the vanishing of quantum integers at `δ` and
`q` being a root of unity.

## Main results

* `TauCeti.pow_two_mul_eq_one_of_qInt_add_inv_eq_zero`: `[n] = 0` at `δ = u + u⁻¹` forces
  `u^(2n) = 1`.
* `TauCeti.qInt_add_inv_eq_zero_iff`: without zero divisors, for a unit `u ≠ ±1`, `[n] = 0` at
  `δ = u + u⁻¹` iff `u^(2n) = 1`.
* `TauCeti.exists_qInt_eq_zero_iff`: over an algebraically closed field of characteristic zero,
  some `[n]` with `n ≥ 1` vanishes iff `δ = ζ + ζ⁻¹` for a root of unity `ζ ≠ ±1`.

## References

* L. H. Kauffman and S. L. Lins, *Temperley–Lieb Recoupling Theory and Invariants of
  3-Manifolds*, Annals of Mathematics Studies 134, Princeton University Press, 1994, for the
  quantum integers as functions of the loop value.
* P. Tingley, *A minus sign that used to annoy me but now I know why it is there*,
  arXiv:1002.0555, for a discussion of the sign choice between `δ = q + q⁻¹` and
  `δ = -(q + q⁻¹)`; this file uses the unsigned convention `δ = q + q⁻¹`.
-/

public section

open Polynomial

namespace TauCeti

section Units

variable {R : Type*} [CommRing R]

/-- If the quantum integer `[n]` vanishes at `δ = u + u⁻¹`, then `u ^ (2 * n) = 1`. For
`n > 0` this makes `u` a root of unity. -/
theorem pow_two_mul_eq_one_of_qInt_add_inv_eq_zero {u : Rˣ} {n : ℕ}
    (h : qInt R (u + ↑u⁻¹) n = 0) : u ^ (2 * n) = 1 := by
  have h' : u ^ n = u⁻¹ ^ n := Units.ext <| by
    push_cast
    simpa [h, sub_eq_zero, eq_comm] using sub_inv_mul_qInt_add_inv u n
  rw [two_mul, pow_add, mul_eq_one_iff_eq_inv, ← inv_pow]
  exact h'

/-- In a ring without zero divisors, for a unit `u ≠ ±1`, the quantum integer `[n]` at
`δ = u + u⁻¹` vanishes exactly when `u ^ (2 * n) = 1`. -/
theorem qInt_add_inv_eq_zero_iff [NoZeroDivisors R] {u : Rˣ} (hu₁ : u ≠ 1) (hu₂ : u ≠ -1)
    (n : ℕ) :
    qInt R (u + ↑u⁻¹) n = 0 ↔ u ^ (2 * n) = 1 := by
  refine ⟨pow_two_mul_eq_one_of_qInt_add_inv_eq_zero, fun h ↦ ?_⟩
  rw [two_mul, pow_add, mul_eq_one_iff_eq_inv, ← inv_pow] at h
  refine (mul_eq_zero.1 ?_).resolve_left (Units.val_sub_val_inv_ne_zero hu₁ hu₂)
  rw [sub_inv_mul_qInt_add_inv, sub_eq_zero]
  exact_mod_cast congrArg Units.val h

/-- Away from `±1`, the vanishing indices are the multiples of the multiplicative order of
`u²`. This includes index zero and units of infinite order (`orderOf (u ^ 2) = 0`). -/
theorem qInt_add_inv_eq_zero_iff_orderOf_sq_dvd [NoZeroDivisors R] {u : Rˣ}
    (hu₁ : u ≠ 1) (hu₂ : u ≠ -1) (n : ℕ) :
    qInt R (u + ↑u⁻¹) n = 0 ↔ orderOf (u ^ 2) ∣ n := by
  rw [qInt_add_inv_eq_zero_iff hu₁ hu₂, orderOf_dvd_iff_pow_eq_one, ← pow_mul]

end Units

/-- **The root-of-unity dictionary.** Over an algebraically closed field of characteristic zero,
some quantum integer `[n]` with `n ≥ 1` vanishes at `δ` iff `δ = ζ + ζ⁻¹` for a root of unity
`ζ ≠ ±1`. The exclusions are needed: `[n] = n` at `δ = 2` and `[n] = (-1)^(n+1) n` at `δ = -2`
(`qInt_two_left`, `qInt_neg_two_left`) never vanish in characteristic zero. -/
theorem exists_qInt_eq_zero_iff (K : Type*) [Field K] [IsAlgClosed K] [CharZero K] (δ : K) :
    (∃ n : ℕ, 1 ≤ n ∧ qInt K δ n = 0) ↔
      ∃ ζ : Kˣ, (∃ m : ℕ, 0 < m ∧ ζ ^ m = 1) ∧ ζ ≠ 1 ∧ ζ ≠ -1 ∧
        δ = (ζ : K) + ((ζ⁻¹ : Kˣ) : K) := by
  constructor
  · rintro ⟨n, hn, h⟩
    -- `δ = ζ + ζ⁻¹` for a root `ζ` of `X² - δ X + 1`, which is nonzero since the roots multiply
    -- to `1`.
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_root (C 1 * X ^ 2 + C (-δ) * X + C 1)
      (by rw [degree_quadratic one_ne_zero]; decide)
    have hz' : z * z - δ * z + 1 = 0 := by
      simp only [IsRoot, eval_add, eval_mul, eval_C, eval_pow, eval_X] at hz
      linear_combination hz
    have hz0 : z ≠ 0 := by
      rintro rfl
      simp at hz'
    set ζ := Units.mk0 z hz0
    have hδ : δ = (ζ : K) + ((ζ⁻¹ : Kˣ) : K) := by
      simp only [ζ, Units.val_mk0, Units.val_inv_eq_inv_val]
      field_simp
      linear_combination -hz'
    have hn0 : (n : K) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
    have hζ₁ : ζ ≠ 1 := by
      rintro hζ
      simp [hζ, one_add_one_eq_two] at hδ
      simp [hδ, hn0] at h
    have hζ₂ : ζ ≠ -1 := by
      rintro hζ
      norm_num [hζ] at hδ
      simp [hδ, hn0] at h
    rw [hδ] at h
    exact ⟨ζ, ⟨2 * n, by omega, pow_two_mul_eq_one_of_qInt_add_inv_eq_zero h⟩, hζ₁, hζ₂, hδ⟩
  · rintro ⟨ζ, ⟨m, hm, hζm⟩, hζ₁, hζ₂, rfl⟩
    exact ⟨m, hm, (qInt_add_inv_eq_zero_iff hζ₁ hζ₂ m).2 (by rw [pow_mul', hζm, one_pow])⟩

end TauCeti
