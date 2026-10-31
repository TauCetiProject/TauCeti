/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import TauCeti.QuantumGroups.QuantumInteger.Basic
public import TauCeti.RingTheory.Polynomial.Chebyshev.Addition

import Mathlib.Tactic

/-!
# Quantum integers at a loop parameter

For an element `δ` of a commutative ring `R`, the quantum integer `[n]` at `δ` is the value at
`δ` of a Chebyshev polynomial: `TauCeti.qInt R δ n` is `(Polynomial.Chebyshev.S R (n - 1)).eval δ`.
Thus `[0] = 0`, `[1] = 1`, `[2] = δ` and `[n + 2] = δ [n + 1] - [n]`. When `δ = q + q⁻¹` for a
unit `q`, this is the symmetric quantum integer `q^(n-1) + q^(n-3) + ⋯ + q^(1-n)`, but `qInt` needs
no square root of anything and makes sense for every `δ`: it is the form in which quantum integers
appear in the Temperley–Lieb algebras and categories, where `δ` is the value of a closed loop.

The integer index of `S` absorbs the shift by one, so that `[0] = S (-1) = 0`. The polynomial
identities behind the basic arithmetic of `[n]` are proved for `Polynomial.Chebyshev.S` in
`TauCeti/RingTheory/Polynomial/Chebyshev/Addition.lean` and only evaluated here.

Since Mathlib's polynomials are noncomputable, so is `qInt`; the evaluator `TauCeti.qIntAux`
computes the same values from the three-term recurrence.

## Main definitions

* `TauCeti.qInt R δ n`: the quantum integer `[n]` at the loop parameter `δ`.
* `TauCeti.qIntAux δ n`: a computable evaluator, equal to `qInt R δ n` by `qIntAux_eq_qInt`.

## Main results

* `TauCeti.qInt_add_add_one`: `[m + n + 1] = [m + 1] [n + 1] - [m] [n]`.
* `TauCeti.qInt_dvd_qInt`: `[d] ∣ [n]` whenever `d ∣ n`.
* `TauCeti.qInt_two_left`, `TauCeti.qInt_neg_two_left`: `[n] = n` at `δ = 2`, and
  `[n] = (-1)^(n+1) n` at `δ = -2`.
* `TauCeti.qInt_add_inv_eq_sum`, `TauCeti.sub_inv_mul_qInt_add_inv`: for a unit `u`,
  `[n] = Σ_{j < n} u^j u^(-(n-1-j))` and `(u - u⁻¹) [n] = uⁿ - u⁻ⁿ` at `δ = u + u⁻¹`.
* `TauCeti.qInt_add_inv_eq_quantumInteger`: comparison with the field quantum integer
  `TauCeti.quantumInteger`.
* `TauCeti.qInt_add_inv_eq_zero_iff`: without zero divisors, for a unit `u ≠ ±1`, `[n] = 0` at
  `δ = u + u⁻¹` iff `u^(2n) = 1`.
* `TauCeti.exists_qInt_eq_zero_iff`: over an algebraically closed field of characteristic zero,
  some `[n]` with `n ≥ 1` vanishes iff `δ = ζ + ζ⁻¹` for a root of unity `ζ ≠ ±1`.

## References

* P. Tingley, *A minus sign that used to annoy me but now I know why it is there*,
  arXiv:1002.0555, for the convention `δ = q + q⁻¹`.
-/

public section

open Polynomial Polynomial.Chebyshev

namespace TauCeti

section CommRing

variable (R : Type*) [CommRing R]

/-- The **quantum integer** `[n]` at the loop parameter `δ`: Mathlib's rescaled Chebyshev
polynomial of the second kind `Polynomial.Chebyshev.S` at the integer index `n - 1`, evaluated at
`δ`. Thus `[0] = 0`, `[1] = 1`, `[2] = δ` and `[n + 2] = δ [n + 1] - [n]`; for a unit `q` with
`δ = q + q⁻¹`, `[n] = q^(n-1) + q^(n-3) + ⋯ + q^(1-n)`. -/
noncomputable def qInt (δ : R) (n : ℕ) : R :=
  (S R ((n : ℤ) - 1)).eval δ

variable {R}

/-- `qInt R δ n` is the Chebyshev polynomial `S R (n - 1)` evaluated at `δ`. -/
theorem qInt_def (δ : R) (n : ℕ) : qInt R δ n = (S R ((n : ℤ) - 1)).eval δ := (rfl)

/-- `[0] = 0`. -/
@[simp]
theorem qInt_zero (δ : R) : qInt R δ 0 = 0 := by
  simp [qInt_def]

/-- `[1] = 1`. -/
@[simp]
theorem qInt_one (δ : R) : qInt R δ 1 = 1 := by
  simp [qInt_def]

/-- `[2] = δ`. -/
@[simp]
theorem qInt_two (δ : R) : qInt R δ 2 = δ := by
  simp [qInt_def, show (2 : ℤ) - 1 = 1 by norm_num]

/-- The three-term recurrence `[n + 2] = δ [n + 1] - [n]`. -/
theorem qInt_add_two (δ : R) (n : ℕ) :
    qInt R δ (n + 2) = δ * qInt R δ (n + 1) - qInt R δ n := by
  simp only [qInt_def]
  rw [show ((n + 2 : ℕ) : ℤ) - 1 = ((n : ℤ) - 1) + 2 by push_cast; ring, S_add_two,
    show ((n + 1 : ℕ) : ℤ) - 1 = ((n : ℤ) - 1) + 1 by push_cast; ring]
  simp

/-- The **addition formula** `[m + n + 1] = [m + 1] [n + 1] - [m] [n]`. -/
theorem qInt_add_add_one (δ : R) (m n : ℕ) :
    qInt R δ (m + n + 1) = qInt R δ (m + 1) * qInt R δ (n + 1) - qInt R δ m * qInt R δ n := by
  simp only [qInt_def]
  rw [show ((m + n + 1 : ℕ) : ℤ) - 1 = (m : ℤ) + n by push_cast; ring, S_add]
  simp

/-- **Divisibility of quantum integers**: `[d] ∣ [n]` whenever `d ∣ n`. -/
theorem qInt_dvd_qInt (δ : R) {d n : ℕ} (h : d ∣ n) : qInt R δ d ∣ qInt R δ n := by
  simp only [qInt_def]
  exact map_dvd (Polynomial.evalRingHom δ) (S_sub_one_dvd_S_sub_one R (Int.natCast_dvd_natCast.2 h))

/-- At `δ = 2` the quantum integer `[n]` is the integer `n`. -/
@[simp]
theorem qInt_two_left (n : ℕ) : qInt R 2 n = n := by
  simp [qInt_def]

/-- At `δ = -2` the quantum integer `[n]` is `(-1)^(n+1) n`. -/
@[simp]
theorem qInt_neg_two_left (n : ℕ) : qInt R (-2) n = (-1) ^ (n + 1) * n := by
  rw [qInt_def, S_eval_neg_two, Int.negOnePow_sub, Int.negOnePow_one, Units.val_mul,
    Int.cast_mul, Int.cast_negOnePow_natCast]
  push_cast
  ring

end CommRing

namespace _root_.RingHom

variable {R R' : Type*} [CommRing R] [CommRing R']

/-- Ring homomorphisms commute with the quantum integers. -/
@[simp]
theorem map_qInt (f : R →+* R') (δ : R) (n : ℕ) : f (qInt R δ n) = qInt R' (f δ) n := by
  simp only [qInt_def, ← Polynomial.eval_map_apply, map_S]

end _root_.RingHom

/-! ### A computable evaluator -/

section Aux

variable {R : Type*} [CommRing R]

/-- A **computable evaluator for the quantum integers**: `qIntAux δ n` iterates
`([k], [k + 1]) ↦ ([k + 1], δ [k + 1] - [k])` starting from `([0], [1]) = (0, 1)`, and so agrees
with the noncomputable `qInt R δ n` (`qIntAux_eq_qInt`). The body is exposed so that values can
be computed by evaluation or by `decide` in other modules. -/
@[expose]
def qIntAux (δ : R) (n : ℕ) : R :=
  ((fun p : R × R ↦ (p.2, δ * p.2 - p.1))^[n] (0, 1)).1

/-- The computable evaluator `qIntAux` computes the quantum integers. -/
@[simp]
theorem qIntAux_eq_qInt (δ : R) (n : ℕ) : qIntAux δ n = qInt R δ n := by
  have key : ∀ n : ℕ, (fun p : R × R ↦ (p.2, δ * p.2 - p.1))^[n] (0, 1) =
      (qInt R δ n, qInt R δ (n + 1)) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [Function.iterate_succ_apply', ih, qInt_add_two]
  rw [qIntAux, key]

end Aux

/-! ### The interface with a unit `u` such that `δ = u + u⁻¹` -/

section Units

variable {R : Type*} [CommRing R]

/-- The first-order recurrence `[n + 1] = u⁻¹ [n] + uⁿ` at `δ = u + u⁻¹`. -/
theorem qInt_add_inv_add_one (u : Rˣ) (n : ℕ) :
    qInt R (u + ↑u⁻¹) (n + 1) = ↑u⁻¹ * qInt R (u + ↑u⁻¹) n + (u : R) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [qInt_add_two]
    linear_combination (u : R) * ih + qInt R (u + ↑u⁻¹) n * u.mul_inv

/-- **The quantum integer as a Laurent sum**: at `δ = u + u⁻¹` for a unit `u`,
`[n] = Σ_{j < n} u^j (u⁻¹)^(n - 1 - j) = u^(n-1) + u^(n-3) + ⋯ + u^(1-n)`. -/
theorem qInt_add_inv_eq_sum (u : Rˣ) (n : ℕ) :
    qInt R (u + ↑u⁻¹) n = ∑ j ∈ Finset.range n, (u : R) ^ j * (↑u⁻¹ : R) ^ (n - 1 - j) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [qInt_add_inv_add_one, ih, Finset.sum_range_succ, Finset.mul_sum]
    congr 1
    · refine Finset.sum_congr rfl fun j hj ↦ ?_
      rw [Finset.mem_range] at hj
      rw [show n + 1 - 1 - j = (n - 1 - j) + 1 by omega, pow_succ]
      ring
    · simp

/-- **The `q`-side characterization of the quantum integers**: at `δ = u + u⁻¹` for a unit `u`,
`(u - u⁻¹) [n] = uⁿ - u⁻ⁿ`. -/
theorem sub_inv_mul_qInt_add_inv (u : Rˣ) (n : ℕ) :
    ((u : R) - ↑u⁻¹) * qInt R (u + ↑u⁻¹) n = (u : R) ^ n - (↑u⁻¹ : R) ^ n := by
  rw [qInt_add_inv_eq_sum, (Commute.all _ _).mul_geom_sum₂]

/-- If some quantum integer vanishes at `δ = u + u⁻¹`, then `u` is a root of unity:
`[n] = 0` forces `u ^ (2 * n) = 1`. -/
theorem pow_two_mul_eq_one_of_qInt_add_inv_eq_zero {u : Rˣ} {n : ℕ}
    (h : qInt R (u + ↑u⁻¹) n = 0) : u ^ (2 * n) = 1 := by
  have h' := sub_inv_mul_qInt_add_inv u n
  rw [h, mul_zero, eq_comm, sub_eq_zero, ← Units.val_pow_eq_pow_val,
    ← Units.val_pow_eq_pow_val, Units.val_inj, inv_pow] at h'
  rw [two_mul, pow_add, mul_eq_one_iff_eq_inv]
  exact h'

/-- In a ring without zero divisors, for a unit `u ≠ ±1`, the quantum integer `[n]` at
`δ = u + u⁻¹` vanishes exactly when `u ^ (2 * n) = 1`. -/
theorem qInt_add_inv_eq_zero_iff [NoZeroDivisors R] {u : Rˣ} (hu₁ : u ≠ 1) (hu₂ : u ≠ -1)
    (n : ℕ) :
    qInt R (u + ↑u⁻¹) n = 0 ↔ u ^ (2 * n) = 1 := by
  refine ⟨pow_two_mul_eq_one_of_qInt_add_inv_eq_zero, fun h ↦ ?_⟩
  have hsub : (u : R) - ↑u⁻¹ ≠ 0 := by
    intro h0
    have hsq : (u : R) * u = 1 := by
      have h1 := u.mul_inv
      rwa [← sub_eq_zero.1 h0] at h1
    rcases mul_self_eq_one_iff.1 hsq with h1 | h1
    · exact hu₁ (Units.val_eq_one.1 h1)
    · exact hu₂ (Units.ext (by simpa using h1))
  have h' := sub_inv_mul_qInt_add_inv u n
  rw [two_mul, pow_add, mul_eq_one_iff_eq_inv, ← inv_pow] at h
  rw [← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val, h, sub_self] at h'
  exact (mul_eq_zero.1 h').resolve_left hsub

end Units

/-- At a parameter `q` of a field with `q - q⁻¹ ≠ 0`, the quantum integer at `δ = q + q⁻¹` is the
field quantum integer `[n]_q = (qⁿ - q⁻ⁿ) / (q - q⁻¹)`. -/
theorem qInt_add_inv_eq_quantumInteger {K : Type*} [Field K] {q : K} (hq : q - q⁻¹ ≠ 0)
    (n : ℕ) : qInt K (q + q⁻¹) n = quantumInteger q n := by
  have h := sub_inv_mul_qInt_add_inv (Units.mk0 q (ne_zero_of_sub_inv_ne_zero hq)) n
  simp only [Units.val_mk0, Units.val_inv_eq_inv_val] at h
  exact mul_left_cancel₀ hq (h.trans (sub_inv_mul_quantumInteger_natCast hq n).symm)

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
      rw [hζ, Units.val_one, inv_one, Units.val_one, one_add_one_eq_two] at hδ
      rw [hδ, qInt_two_left] at h
      exact hn0 h
    have hζ₂ : ζ ≠ -1 := by
      rintro hζ
      rw [hζ, inv_neg, inv_one, Units.val_neg, Units.val_one, ← neg_add, one_add_one_eq_two]
        at hδ
      rw [hδ, qInt_neg_two_left] at h
      exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)) hn0 h
    rw [hδ] at h
    exact ⟨ζ, ⟨2 * n, by omega, pow_two_mul_eq_one_of_qInt_add_inv_eq_zero h⟩, hζ₁, hζ₂, hδ⟩
  · rintro ⟨ζ, ⟨m, hm, hζm⟩, hζ₁, hζ₂, rfl⟩
    exact ⟨m, hm, (qInt_add_inv_eq_zero_iff hζ₁ hζ₂ m).2 (by rw [pow_mul', hζm, one_pow])⟩

end TauCeti
