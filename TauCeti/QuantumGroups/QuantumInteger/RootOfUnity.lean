/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import TauCeti.QuantumGroups.QuantumInteger.Chebyshev
public import TauCeti.QuantumGroups.QuantumInteger.Laurent

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

/-!
# Quantum integers at a loop parameter and roots of unity

The quantum integers `TauCeti.qInt R δ n` are defined at an arbitrary loop parameter `δ`, with no
`q` in sight. This file compares them with the `q`-side quantum integers at `δ = u + u⁻¹` for a
unit `u`: there `[n]` is the value at `u` of the Laurent quantum integer
`TauCeti.laurentQuantumInteger n` (`TauCeti.qInt_add_inv_eq_laurentEval`), so that
`(u - u⁻¹) [n] = uⁿ - u⁻ⁿ`. From this follows the dictionary between the vanishing of quantum
integers at `δ` and `q` being a root of unity.

## Main results

* `TauCeti.sub_inv_mul_qInt_add_inv`: `(u - u⁻¹) [n] = uⁿ - u⁻ⁿ` at `δ = u + u⁻¹`.
* `TauCeti.qInt_add_inv_eq_quantumInteger`: comparison with the field quantum integer
  `TauCeti.quantumInteger`.
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

namespace Units

variable {R : Type*} [Ring R] [NoZeroDivisors R]

/-- In a ring without zero divisors, a unit `u ≠ ±1` satisfies `u - u⁻¹ ≠ 0`. -/
theorem val_sub_val_inv_ne_zero {u : Rˣ} (hu₁ : u ≠ 1) (hu₂ : u ≠ -1) :
    (u : R) - ↑u⁻¹ ≠ 0 := fun h ↦
  ((inv_eq_self_iff u).1 (Units.ext (sub_eq_zero.1 h).symm)).elim hu₁ hu₂

end Units

namespace TauCeti

section Units

variable {R : Type*} [CommRing R]

/-- **The `q`-side characterization of the quantum integers**: at `δ = u + u⁻¹` for a unit `u`,
`(u - u⁻¹) [n] = uⁿ - u⁻ⁿ`. -/
theorem sub_inv_mul_qInt_add_inv (u : Rˣ) (n : ℕ) :
    ((u : R) - ↑u⁻¹) * qInt R (u + ↑u⁻¹) n = (u : R) ^ n - (↑u⁻¹ : R) ^ n := by
  simpa [qInt_add_inv_eq_laurentEval] using sub_inv_mul_laurentEval_laurentQuantumInteger u n

/-- If some quantum integer vanishes at `δ = u + u⁻¹`, then `u` is a root of unity:
`[n] = 0` forces `u ^ (2 * n) = 1`. -/
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

end Units

/-- At a parameter `q` of a field with `q - q⁻¹ ≠ 0`, the quantum integer at `δ = q + q⁻¹` is the
field quantum integer `[n]_q = (qⁿ - q⁻ⁿ) / (q - q⁻¹)`. -/
theorem qInt_add_inv_eq_quantumInteger {K : Type*} [Field K] {q : K} (hq : q - q⁻¹ ≠ 0)
    (n : ℕ) : qInt K (q + q⁻¹) n = quantumInteger q n := by
  have h := qInt_add_inv_eq_laurentEval (Units.mk0 q (ne_zero_of_sub_inv_ne_zero hq)) n
  rw [laurentEval_laurentQuantumInteger (by simpa using hq)] at h
  simpa using h

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
