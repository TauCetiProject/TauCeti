/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Tactic.Ring

/-!
# Lucas sequences of the first and second kinds

For a commutative ring `R` and parameters `P Q : R`, the Lucas sequence of the first kind
`lucasU P Q : ℕ → R` and the Lucas sequence of the second kind `lucasV P Q : ℕ → R` are defined by
the three-term linear recurrence `u (n + 2) = P * u (n + 1) - Q * u n` with initial values
`lucasU P Q 0 = 0`, `lucasU P Q 1 = 1` and `lucasV P Q 0 = 2`, `lucasV P Q 1 = P`.

No coprimality, nonvanishing, or non-degeneracy hypothesis is imposed on `P` or `Q`: degenerate
and repeated-root specializations such as `lucasU 2 1 n = n` and `lucasU 0 1 2 = 0` are retained,
and universal polynomial identities in `P` and `Q` hold in every commutative ring, including
characteristic `2`.

## Main definitions

* `TauCeti.lucasU`: the Lucas sequence of the first kind `Uₙ(P, Q)`.
* `TauCeti.lucasV`: the Lucas sequence of the second kind `Vₙ(P, Q)`.

## Main results

* `TauCeti.map_lucasU`, `TauCeti.map_lucasV`: compatibility with ring homomorphisms.
* `TauCeti.eq_mul_lucasU_succ_sub_of_linearRec₂`: for any sequence satisfying
  `u (n + 2) = P * u (n + 1) - Q * u n`, expands positive-index terms as
  `u (n + 1) = u 1 * lucasU P Q (n + 1) - Q * u 0 * lucasU P Q n`.
* `TauCeti.lucasU_add_add_one`: the addition formula
  `U_{m + n + 1} = U_{m + 1} * U_{n + 1} - Q * U_m * U_n`.
* `TauCeti.lucasU_succ_sq_sub_mul`: Cassini's identity `U_{n + 1} ^ 2 - U_{n + 2} * U_n = Q ^ n`.
* `TauCeti.lucasV_sq_sub_mul_lucasU_sq`: the Lucas discriminant identity
  `V_n ^ 2 - (P ^ 2 - 4 * Q) * U_n ^ 2 = 4 * Q ^ n`.
* `TauCeti.lucasU_two_mul`, `TauCeti.lucasU_two_mul_add_one`, `TauCeti.lucasV_two_mul`,
  `TauCeti.lucasV_two_mul_add_one`: the index-doubling identities `U_{2 n} = U_n * V_n`,
  `U_{2 n + 1} = U_{n + 1} ^ 2 - Q * U_n ^ 2`, `V_{2 n} = V_n ^ 2 - 2 * Q ^ n`, and
  `V_{2 n + 1} = V_{n + 1} * V_n - P * Q ^ n`.
* `TauCeti.lucasU_mul`, `TauCeti.lucasV_mul`: the index-multiplication identities
  `U_{m * n}(P, Q) = U_m(P, Q) * U_n(V_m(P, Q), Q ^ m)` and
  `V_{m * n}(P, Q) = V_n(V_m(P, Q), Q ^ m)`.

## References

* R. D. Carmichael, *On the numerical factors of the arithmetic forms αⁿ ± βⁿ*, Annals of
  Mathematics (2) **15** (1913), 30–48.
* P. Bala, *Divisibility sequences from strong divisibility sequences*, OEIS A238600 note (2014).
-/

public section

namespace TauCeti

section Definitions

variable {R : Type*} [CommRing R]

/-- The Lucas sequence of the first kind `Uₙ(P, Q)` over a commutative ring `R`, defined by
`U₀ = 0`, `U₁ = 1`, and `U_{n + 2} = P * U_{n + 1} - Q * U_n`. -/
def lucasU (P Q : R) : ℕ → R
  | 0 => 0
  | 1 => 1
  | n + 2 => P * lucasU P Q (n + 1) - Q * lucasU P Q n

@[simp, grind =]
theorem lucasU_zero (P Q : R) : lucasU P Q 0 = 0 := (rfl)

@[simp, grind =]
theorem lucasU_one (P Q : R) : lucasU P Q 1 = 1 := (rfl)

@[simp low, grind =]
theorem lucasU_add_two (P Q : R) (n : ℕ) :
    lucasU P Q (n + 2) = P * lucasU P Q (n + 1) - Q * lucasU P Q n := (rfl)

/-- Value of `lucasU` at index `2`: `U₂(P, Q) = P`. -/
theorem lucasU_two (P Q : R) : lucasU P Q 2 = P := by
  simp [lucasU]

/-- Value of `lucasU` at index `3`: `U₃(P, Q) = P ^ 2 - Q`. -/
theorem lucasU_three (P Q : R) : lucasU P Q 3 = P ^ 2 - Q := by
  simp only [lucasU]
  ring

/-- Three-term recurrence for `lucasU` at any index `n ≥ 2`. -/
theorem lucasU_of_two_le (P Q : R) {n : ℕ} (hn : 2 ≤ n) :
    lucasU P Q n = P * lucasU P Q (n - 1) - Q * lucasU P Q (n - 2) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [add_comm]
  exact lucasU_add_two P Q k

/-- The Lucas sequence of the second kind `Vₙ(P, Q)` over a commutative ring `R`, defined by
`V₀ = 2`, `V₁ = P`, and `V_{n + 2} = P * V_{n + 1} - Q * V_n`. -/
def lucasV (P Q : R) : ℕ → R
  | 0 => 2
  | 1 => P
  | n + 2 => P * lucasV P Q (n + 1) - Q * lucasV P Q n

@[simp, grind =]
theorem lucasV_zero (P Q : R) : lucasV P Q 0 = 2 := (rfl)

@[simp, grind =]
theorem lucasV_one (P Q : R) : lucasV P Q 1 = P := (rfl)

@[simp low, grind =]
theorem lucasV_add_two (P Q : R) (n : ℕ) :
    lucasV P Q (n + 2) = P * lucasV P Q (n + 1) - Q * lucasV P Q n := (rfl)

/-- Value of `lucasV` at index `2`: `V₂(P, Q) = P ^ 2 - 2 * Q`. -/
theorem lucasV_two (P Q : R) : lucasV P Q 2 = P ^ 2 - 2 * Q := by
  simp only [lucasV]
  ring

/-- Value of `lucasV` at index `3`: `V₃(P, Q) = P ^ 3 - 3 * P * Q`. -/
theorem lucasV_three (P Q : R) : lucasV P Q 3 = P ^ 3 - 3 * P * Q := by
  simp only [lucasV]
  ring

/-- Three-term recurrence for `lucasV` at any index `n ≥ 2`. -/
theorem lucasV_of_two_le (P Q : R) {n : ℕ} (hn : 2 ≤ n) :
    lucasV P Q n = P * lucasV P Q (n - 1) - Q * lucasV P Q (n - 2) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [add_comm]
  exact lucasV_add_two P Q k

/-- Ring homomorphisms commute with `lucasU`. -/
@[simp, grind =]
theorem map_lucasU {S F : Type*} [CommRing S] [FunLike F R S] [RingHomClass F R S] (f : F)
    (P Q : R) (n : ℕ) : f (lucasU P Q n) = lucasU (f P) (f Q) n := by
  induction n using Nat.twoStepInduction with
  | zero | one => simp
  | more n ih₀ ih₁ => simp [ih₀, ih₁]

/-- Ring homomorphisms commute with `lucasV`. -/
@[simp, grind =]
theorem map_lucasV {S F : Type*} [CommRing S] [FunLike F R S] [RingHomClass F R S] (f : F)
    (P Q : R) (n : ℕ) : f (lucasV P Q n) = lucasV (f P) (f Q) n := by
  induction n using Nat.twoStepInduction with
  | zero => simp [map_ofNat]
  | one => simp
  | more n ih₀ ih₁ => simp [ih₀, ih₁]

/-- Casting an integer `lucasU` term to `R` casts its parameters. -/
@[simp, grind =]
theorem intCast_lucasU (P Q : ℤ) (n : ℕ) : ((lucasU P Q n : ℤ) : R) = lucasU (P : R) (Q : R) n := by
  simpa only [eq_intCast] using map_lucasU (Int.castRingHom R) P Q n

/-- Casting an integer `lucasV` term to `R` casts its parameters. -/
@[simp, grind =]
theorem intCast_lucasV (P Q : ℤ) (n : ℕ) : ((lucasV P Q n : ℤ) : R) = lucasV (P : R) (Q : R) n := by
  simpa only [eq_intCast] using map_lucasV (Int.castRingHom R) P Q n

end Definitions

section Identities

variable {R : Type*} [CommRing R]

/-! ### Vanishing parameters -/

@[simp]
theorem lucasU_zero_right_succ (P : R) (n : ℕ) : lucasU P 0 (n + 1) = P ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [lucasU_add_two, ih, zero_mul, sub_zero, pow_succ']

@[simp]
theorem lucasV_zero_right_succ (P : R) (n : ℕ) : lucasV P 0 (n + 1) = P ^ (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [lucasV_add_two, ih, zero_mul, sub_zero, ← pow_succ']

@[simp]
theorem lucasU_zero_left_two_mul (Q : R) (n : ℕ) : lucasU 0 Q (2 * n) = 0 := by
  induction n with
  | zero => simp
  | succ n ih => simp [Nat.mul_succ, ih]

@[simp]
theorem lucasU_zero_left_two_mul_add_one (Q : R) (n : ℕ) :
    lucasU 0 Q (2 * n + 1) = (-Q) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.mul_succ, add_right_comm, lucasU_add_two, zero_mul, zero_sub, ih, pow_succ']
    ring

@[simp]
theorem lucasV_zero_left_two_mul (Q : R) (n : ℕ) : lucasV 0 Q (2 * n) = 2 * (-Q) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.mul_succ, lucasV_add_two, zero_mul, zero_sub, ih, pow_succ']
    ring

@[simp]
theorem lucasV_zero_left_two_mul_add_one (Q : R) (n : ℕ) : lucasV 0 Q (2 * n + 1) = 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.mul_succ, add_right_comm, lucasV_add_two, zero_mul, ih, mul_zero, sub_self]

/-! ### Recurrence expansion and addition formulas -/

/-- For any sequence satisfying `u (n + 2) = P * u (n + 1) - Q * u n`, expands positive-index terms
as `u (n + 1) = u 1 * lucasU P Q (n + 1) - Q * u 0 * lucasU P Q n`. -/
theorem eq_mul_lucasU_succ_sub_of_linearRec₂ {P Q : R} {u : ℕ → R}
    (hu : ∀ n, u (n + 2) = P * u (n + 1) - Q * u n) (n : ℕ) :
    u (n + 1) = u 1 * lucasU P Q (n + 1) - Q * u 0 * lucasU P Q n := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one =>
    rw [hu 0, lucasU_two, lucasU_one]
    ring
  | more n ih₀ ih₁ =>
    rw [hu (n + 1), ih₁, ih₀, lucasU_add_two P Q (n + 1), lucasU_add_two P Q n]
    ring

/-- **Addition formula for `lucasU`**:
`U_{m + n + 1} = U_{m + 1} * U_{n + 1} - Q * U_m * U_n`. -/
theorem lucasU_add_add_one (P Q : R) (m n : ℕ) :
    lucasU P Q (m + n + 1) =
      lucasU P Q (m + 1) * lucasU P Q (n + 1) - Q * lucasU P Q m * lucasU P Q n := by
  simpa only [add_assoc, add_zero] using
    eq_mul_lucasU_succ_sub_of_linearRec₂ (u := fun k ↦ lucasU P Q (m + k))
      (fun k ↦ by simpa only [add_assoc] using lucasU_add_two P Q (m + k)) n

/-- Mixed addition formula expanding `lucasV` at `m + n + 1` in terms of `lucasU`. -/
theorem lucasV_add_add_one (P Q : R) (m n : ℕ) :
    lucasV P Q (m + n + 1) =
      lucasV P Q (m + 1) * lucasU P Q (n + 1) - Q * lucasV P Q m * lucasU P Q n := by
  simpa only [add_assoc, add_zero] using
    eq_mul_lucasU_succ_sub_of_linearRec₂ (u := fun k ↦ lucasV P Q (m + k))
      (fun k ↦ by simpa only [add_assoc] using lucasV_add_two P Q (m + k)) n

/-! ### Cross-relations, Cassini's identity, and the discriminant identity -/

/-- Expresses `lucasV` in terms of two consecutive terms of `lucasU`:
`V_n = 2 * U_{n + 1} - P * U_n`. -/
theorem lucasV_eq_two_mul_lucasU_succ_sub (P Q : R) (n : ℕ) :
    lucasV P Q n = 2 * lucasU P Q (n + 1) - P * lucasU P Q n := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one =>
    rw [lucasV_one, lucasU_two, lucasU_one]
    ring
  | more n ih₀ ih₁ =>
    rw [lucasV_add_two, ih₁, ih₀, lucasU_add_two (n := n + 1), lucasU_add_two (n := n)]
    ring

/-- Twice `lucasU P Q (n + 1)` equals `P * lucasU P Q n + lucasV P Q n`. -/
theorem two_mul_lucasU_succ_eq (P Q : R) (n : ℕ) :
    2 * lucasU P Q (n + 1) = P * lucasU P Q n + lucasV P Q n := by
  rw [lucasV_eq_two_mul_lucasU_succ_sub]
  ring

/-- Expresses `lucasV P Q (n + 1)` as `lucasU P Q (n + 2) - Q * lucasU P Q n`. -/
theorem lucasV_succ_eq_lucasU_add_two_sub (P Q : R) (n : ℕ) :
    lucasV P Q (n + 1) = lucasU P Q (n + 2) - Q * lucasU P Q n := by
  rw [lucasV_eq_two_mul_lucasU_succ_sub, lucasU_add_two]
  ring

/-- **Cassini's identity for `lucasU`**: `U_{n + 1} ^ 2 - U_{n + 2} * U_n = Q ^ n`. -/
theorem lucasU_succ_sq_sub_mul (P Q : R) (n : ℕ) :
    lucasU P Q (n + 1) ^ 2 - lucasU P Q (n + 2) * lucasU P Q n = Q ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc
      lucasU P Q (n + 2) ^ 2 - lucasU P Q (n + 3) * lucasU P Q (n + 1)
        = Q * (lucasU P Q (n + 1) ^ 2 - lucasU P Q (n + 2) * lucasU P Q n) := by
          rw [lucasU_add_two P Q (n + 1), lucasU_add_two P Q n]
          ring
      _ = Q ^ (n + 1) := by rw [ih, pow_succ']

/-- **Lucas discriminant identity**: `V_n ^ 2 - (P ^ 2 - 4 * Q) * U_n ^ 2 = 4 * Q ^ n`. -/
theorem lucasV_sq_sub_mul_lucasU_sq (P Q : R) (n : ℕ) :
    lucasV P Q n ^ 2 - (P ^ 2 - 4 * Q) * lucasU P Q n ^ 2 = 4 * Q ^ n := by
  rw [lucasV_eq_two_mul_lucasU_succ_sub, ← lucasU_succ_sq_sub_mul P Q n, lucasU_add_two]
  ring

/-! ### Symmetrized addition and doubling formulas -/

/-- Symmetrized addition formula for `lucasU`:
`2 * U_{m + n} = U_m * V_n + U_n * V_m`. -/
theorem two_mul_lucasU_add (P Q : R) (m n : ℕ) :
    2 * lucasU P Q (m + n) = lucasU P Q m * lucasV P Q n + lucasU P Q n * lucasV P Q m := by
  cases n with
  | zero =>
    simp only [add_zero, lucasV_zero, lucasU_zero, zero_mul, add_zero]
    ring
  | succ n =>
    rw [← add_assoc, lucasU_add_add_one, lucasV_eq_two_mul_lucasU_succ_sub P Q m,
      lucasV_eq_two_mul_lucasU_succ_sub P Q (n + 1), lucasU_add_two P Q n]
    ring

/-- Symmetrized addition formula for `lucasV`:
`2 * V_{m + n} = V_m * V_n + (P ^ 2 - 4 * Q) * U_m * U_n`. -/
theorem two_mul_lucasV_add (P Q : R) (m n : ℕ) :
    2 * lucasV P Q (m + n) =
      lucasV P Q m * lucasV P Q n + (P ^ 2 - 4 * Q) * lucasU P Q m * lucasU P Q n := by
  cases n with
  | zero =>
    simp only [add_zero, lucasV_zero, lucasU_zero, mul_zero, add_zero]
    ring
  | succ n =>
    rw [← add_assoc, lucasV_add_add_one, lucasV_eq_two_mul_lucasU_succ_sub P Q (m + 1),
      lucasV_eq_two_mul_lucasU_succ_sub P Q m, lucasV_eq_two_mul_lucasU_succ_sub P Q (n + 1),
      lucasU_add_two P Q m, lucasU_add_two P Q n]
    ring

/-- **Doubling identity for `lucasU`**: `U_{2 n} = U_n * V_n`. -/
theorem lucasU_two_mul (P Q : R) (n : ℕ) :
    lucasU P Q (2 * n) = lucasU P Q n * lucasV P Q n := by
  cases n with
  | zero => simp
  | succ n =>
    have h2 : 2 * (n + 1) = n + (n + 1) + 1 := by ring
    rw [h2, lucasU_add_add_one, lucasV_succ_eq_lucasU_add_two_sub]
    ring

/-- **Odd-index doubling identity for `lucasU`**: `U_{2 n + 1} = U_{n + 1} ^ 2 - Q * U_n ^ 2`. -/
theorem lucasU_two_mul_add_one (P Q : R) (n : ℕ) :
    lucasU P Q (2 * n + 1) = lucasU P Q (n + 1) ^ 2 - Q * lucasU P Q n ^ 2 := by
  rw [two_mul, lucasU_add_add_one]
  ring

/-- Expresses `lucasU P Q (2 * n + 1)` in terms of `lucasV P Q n`, `lucasU P Q (n + 1)`, and
`Q ^ n`. -/
theorem lucasU_two_mul_add_one_eq_lucasV_mul_sub (P Q : R) (n : ℕ) :
    lucasU P Q (2 * n + 1) = lucasV P Q n * lucasU P Q (n + 1) - Q ^ n := by
  rw [lucasU_two_mul_add_one, lucasV_eq_two_mul_lucasU_succ_sub, ← lucasU_succ_sq_sub_mul P Q n,
    lucasU_add_two]
  ring

/-- **Doubling identity for `lucasV`**: `V_{2 n} = V_n ^ 2 - 2 * Q ^ n`. -/
theorem lucasV_two_mul (P Q : R) (n : ℕ) :
    lucasV P Q (2 * n) = lucasV P Q n ^ 2 - 2 * Q ^ n := by
  rw [lucasV_eq_two_mul_lucasU_succ_sub P Q (2 * n), lucasU_two_mul_add_one_eq_lucasV_mul_sub,
    lucasU_two_mul, lucasV_eq_two_mul_lucasU_succ_sub P Q n]
  ring

/-- **Odd-index doubling identity for `lucasV`**: `V_{2 n + 1} = V_{n + 1} * V_n - P * Q ^ n`. -/
theorem lucasV_two_mul_add_one (P Q : R) (n : ℕ) :
    lucasV P Q (2 * n + 1) = lucasV P Q (n + 1) * lucasV P Q n - P * Q ^ n := by
  rw [two_mul, lucasV_add_add_one, lucasV_eq_two_mul_lucasU_succ_sub P Q (n + 1),
    lucasV_eq_two_mul_lucasU_succ_sub P Q n, ← lucasU_succ_sq_sub_mul P Q n, lucasU_add_two]
  ring

/-! ### Multi-step recurrences and index multiplication -/

/-- Stepping the index of `lucasU` by `m` satisfies the three-term recurrence with parameters
`lucasV P Q m` and `Q ^ m`. -/
theorem lucasU_add_two_mul (P Q : R) (k m : ℕ) :
    lucasU P Q (k + 2 * m) = lucasV P Q m * lucasU P Q (k + m) - Q ^ m * lucasU P Q k := by
  induction k using Nat.twoStepInduction with
  | zero =>
    rw [zero_add, zero_add, lucasU_two_mul, lucasU_zero, mul_zero, sub_zero, mul_comm]
  | one =>
    rw [add_comm 1 (2 * m), add_comm 1 m, lucasU_two_mul_add_one_eq_lucasV_mul_sub, lucasU_one,
      mul_one]
  | more k ih₀ ih₁ =>
    have h1 : k + 1 + 2 * m = k + 2 * m + 1 := by ring
    have h2 : k + 2 + 2 * m = k + 2 * m + 2 := by ring
    have hm1 : k + 1 + m = k + m + 1 := by ring
    have hm2 : k + 2 + m = k + m + 2 := by ring
    rw [h2, lucasU_add_two P Q (k + 2 * m), ← h1, ih₁, ih₀, lucasU_add_two P Q k, hm1, hm2,
      lucasU_add_two P Q (k + m)]
    ring

/-- Stepping the index of `lucasV` by `m` satisfies the three-term recurrence with parameters
`lucasV P Q m` and `Q ^ m`. -/
theorem lucasV_add_two_mul (P Q : R) (k m : ℕ) :
    lucasV P Q (k + 2 * m) = lucasV P Q m * lucasV P Q (k + m) - Q ^ m * lucasV P Q k := by
  have hk : k + 2 * m + 1 = k + 1 + 2 * m := by ring
  have hm : k + m + 1 = k + 1 + m := by ring
  rw [lucasV_eq_two_mul_lucasU_succ_sub P Q (k + 2 * m), hk, lucasU_add_two_mul P Q (k + 1) m,
    lucasU_add_two_mul P Q k m, lucasV_eq_two_mul_lucasU_succ_sub P Q (k + m), hm,
    lucasV_eq_two_mul_lucasU_succ_sub P Q k]
  ring

/-- **Index-multiplication formula for `lucasU`**:
`U_{m * n}(P, Q) = U_m(P, Q) * U_n(V_m(P, Q), Q ^ m)`. -/
theorem lucasU_mul (P Q : R) (m n : ℕ) :
    lucasU P Q (m * n) = lucasU P Q m * lucasU (lucasV P Q m) (Q ^ m) n := by
  induction n using Nat.twoStepInduction with
  | zero | one => simp
  | more n ih₀ ih₁ =>
    have hmul : m * (n + 2) = m * n + 2 * m := by ring
    have hmul1 : m * (n + 1) = m * n + m := by ring
    rw [hmul, lucasU_add_two_mul, ← hmul1, ih₁, ih₀, lucasU_add_two]
    ring

/-- **Index-multiplication formula for `lucasV`**:
`V_{m * n}(P, Q) = V_n(V_m(P, Q), Q ^ m)`. -/
theorem lucasV_mul (P Q : R) (m n : ℕ) :
    lucasV P Q (m * n) = lucasV (lucasV P Q m) (Q ^ m) n := by
  induction n using Nat.twoStepInduction with
  | zero | one => simp
  | more n ih₀ ih₁ =>
    have hmul : m * (n + 2) = m * n + 2 * m := by ring
    have hmul1 : m * (n + 1) = m * n + m := by ring
    rw [hmul, lucasV_add_two_mul, ← hmul1, ih₁, ih₀, lucasV_add_two]

end Identities

end TauCeti
