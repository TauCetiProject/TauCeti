/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Data.Nat.ModEq
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.PowerSeries.Expand

/-!
# Congruence parts and Frobenius prime-power congruences of formal power series

For a formal power series `G : PowerSeries R` over a commutative semiring `R` and `i < m`, the
subseries of terms in degrees `≡ i [MOD m]` splits as its leading term `C (coeff i G) * X ^ i`
plus `X ^ (i + m)` times the shifted tail (`TauCeti.mk_congruencePart_eq_C_mul_X_pow_add`).

Over a commutative ring `R` with an element `π ∣ p` for a prime `p`, if a power series `Y` is
congruent modulo `π` to `∑_j X ^ (p ^ 2) ^ j`, then `Y ^ (p + 1)` is congruent modulo `π` to the
product of `∑_{i odd} X ^ (p ^ i)` and `∑_{i even} X ^ (p ^ i)`. Similarly, if `Y` is congruent
modulo `π` to `∑_j X ^ (p ^ j)`, then `Y ^ 2` is congruent modulo `π` to `(∑_i X ^ (p ^ i)) ^ 2`.

## Main results

* `TauCeti.mk_congruencePart_eq_C_mul_X_pow_add`: splitting the `n ≡ i [MOD m]` part of a power
  series at degree `i + m`.
* `TauCeti.C_dvd_sq_sub_primePowerSeries_sq`: congruence for `Y ^ 2` when
  `Y ≡ ∑_j X ^ (p ^ j) [mod π]`.
* `TauCeti.C_dvd_pow_sub_primePowerSeries_odd_mul_even`: Frobenius congruence for `Y ^ (p + 1)`
  when `Y ≡ ∑_j X ^ (p ^ 2) ^ j [mod π]` and `π ∣ p`.

## Provenance

Adapted from `New.exists_congruencePart_eq_smul_X_pow_add`,
`New.C_dvd_pow_sub_primePowerSeries_odd_mul_even`, and
`New.C_dvd_sq_sub_primePowerSeries_univ_sq` in
`grh/src/New/Derivatives/FormalGroup/Exponent.lean` of
[lsernau/grh-lean](https://github.com/lsernau/grh-lean), commit
`72fead102f663d5c7a407964a13dc0cf9d977207` (Apache 2.0, Copyright 2026 Anthropic, PBC).
-/

public section

namespace TauCeti

open PowerSeries

/-- For `i < m`, the subseries of `G` retaining degrees `≡ i [MOD m]` splits as
`C (coeff i G) * X ^ i + X ^ (i + m) * H` where `H` retains the shifted degrees. -/
theorem mk_congruencePart_eq_C_mul_X_pow_add {R : Type*} [CommSemiring R] {m i : ℕ} (hi : i < m)
    (G : PowerSeries R) :
    mk (fun n ↦ if n ≡ i [MOD m] then coeff n G else 0) =
      C (coeff i G) * X ^ i +
        X ^ (i + m) * mk (fun k ↦ if i + m + k ≡ i [MOD m] then coeff (i + m + k) G else 0) := by
  ext n
  simp only [coeff_mk, map_add, coeff_C_mul, coeff_X_pow, coeff_X_pow_mul', mul_ite, mul_one,
    mul_zero]
  by_cases h_large : i + m ≤ n
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h_large
    rw [ite_eq_right (by omega : i + m + k ≠ i), ite_eq_left h_large, Nat.add_sub_cancel_left,
      zero_add]
  · have h_iff : n ≡ i [MOD m] ↔ n = i :=
      ⟨fun h ↦ h.eq_of_abs_lt (abs_lt.mpr (by omega)), fun h ↦ by rw [h]⟩
    simp only [h_iff, ite_eq_right h_large, add_zero]
    split_ifs with h_eq <;> simp [h_eq]

open scoped Classical in
/-- Over a commutative ring `R`, if `Y ≡ ∑_j X ^ (p ^ j)` modulo `π`, then
`Y ^ 2 ≡ (∑_i X ^ (p ^ i)) ^ 2` modulo `π`. -/
theorem C_dvd_sq_sub_primePowerSeries_sq {R : Type*} [CommRing R] {p : ℕ} {π : R}
    {Y : PowerSeries R}
    (hY : ∀ n : ℕ, π ∣ coeff n Y - if ∃ j : ℕ, n = p ^ j then 1 else 0) :
    C π ∣ Y ^ 2 - (mk fun n ↦ if ∃ i : ℕ, n = p ^ i then (1 : R) else 0) ^ 2 := by
  set S : PowerSeries R := mk fun n ↦ if ∃ i : ℕ, n = p ^ i then (1 : R) else 0
  have h_sub : C π ∣ Y - S :=
    ⟨mk fun n ↦ (hY n).choose, by
      ext n
      simpa [S, map_sub, coeff_C_mul] using (hY n).choose_spec⟩
  simpa [sq_sub_sq] using h_sub.mul_left (Y + S)

/-- If `π` is a non-unit dividing a prime `p` in a commutative ring `R`, then
`R ⧸ Ideal.span {π}` has characteristic `p`. -/
theorem charP_quotient_span_of_dvd_prime {R : Type*} [CommRing R] {p : ℕ} (hp : p.Prime)
    {π : R} (hπ : π ∣ (p : R)) (hu : ¬ IsUnit π) : CharP (R ⧸ Ideal.span {π}) p :=
  ⟨fun n ↦ by
    rw [← map_natCast (Ideal.Quotient.mk (Ideal.span {π})), Ideal.Quotient.eq_zero_iff_mem,
      Ideal.mem_span_singleton]
    refine ⟨fun h ↦ by_contra fun hndvd ↦ ?_, fun h ↦ hπ.trans (Nat.cast_dvd_cast h)⟩
    have hgcd := congrArg (Int.cast (R := R)) (Nat.gcd_eq_gcd_ab p n)
    rw [(hp.coprime_iff_not_dvd.mpr hndvd).gcd_eq_one] at hgcd
    push_cast at hgcd
    exact hu (isUnit_of_dvd_one (hgcd ▸ dvd_add (hπ.mul_right _) (h.mul_right _)))⟩

open scoped Classical in
/-- Over a commutative ring `R` with `π ∣ p` for a prime `p`, if
`Y ≡ ∑_j X ^ ((p ^ 2) ^ j)` modulo `π`, then `Y ^ (p + 1)` is congruent modulo `π` to the
product of `∑_{i odd} X ^ (p ^ i)` and `∑_{i even} X ^ (p ^ i)`. -/
theorem C_dvd_pow_sub_primePowerSeries_odd_mul_even {R : Type*} [CommRing R] {p : ℕ}
    (hp : p.Prime) {π : R} (hπ : π ∣ (p : R)) {Y : PowerSeries R}
    (hY : ∀ n : ℕ, π ∣ coeff n Y - if ∃ j : ℕ, n = (p ^ 2) ^ j then 1 else 0) :
    C π ∣ Y ^ (p + 1) -
      (mk fun n ↦ if ∃ i : ℕ, Odd i ∧ n = p ^ i then (1 : R) else 0) *
      (mk fun n ↦ if ∃ i : ℕ, Even i ∧ n = p ^ i then (1 : R) else 0) := by
  by_cases hu : IsUnit π
  · exact (hu.map C).dvd
  have : Fact p.Prime := ⟨hp⟩
  have : CharP (R ⧸ Ideal.span {π}) p := charP_quotient_span_of_dvd_prime hp hπ hu
  let q : R →+* R ⧸ Ideal.span {π} := Ideal.Quotient.mk (Ideal.span {π})
  have hmap : Y.map q =
      mk fun n ↦ if ∃ i : ℕ, Even i ∧ n = p ^ i then (1 : R ⧸ Ideal.span {π}) else 0 := by
    ext n
    have hiff : (∃ j : ℕ, n = (p ^ 2) ^ j) ↔ ∃ i : ℕ, Even i ∧ n = p ^ i :=
      ⟨fun ⟨j, hj⟩ ↦ ⟨2 * j, even_two_mul j, by rwa [pow_mul]⟩,
       fun ⟨i, ⟨j, hj⟩, hn⟩ ↦ ⟨j, by rwa [hj, ← two_mul, pow_mul] at hn⟩⟩
    have hq : q (coeff n Y - if ∃ j : ℕ, n = (p ^ 2) ^ j then 1 else 0) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr (hY n))
    rw [coeff_map, coeff_mk, ← sub_eq_zero]
    simpa [hiff, map_sub, apply_ite q] using hq
  have hpow : (Y.map q) ^ p =
      mk fun n ↦ if ∃ i : ℕ, Odd i ∧ n = p ^ i then (1 : R ⧸ Ideal.span {π}) else 0 := by
    rw [← PowerSeries.map_frobenius_expand (p := p) (hp := hp.ne_zero), hmap]
    ext n; rw [coeff_map, coeff_mk]
    by_cases hdiv : p ∣ n
    · obtain ⟨k, rfl⟩ := hdiv
      rw [PowerSeries.coeff_expand_mul p hp.ne_zero, coeff_mk, apply_ite (frobenius _ p), map_one,
        map_zero]
      refine if_congr ⟨fun ⟨i, ⟨j, hj⟩, hk⟩ ↦ ⟨2 * j + 1, ⟨j, rfl⟩, ?_⟩,
        fun ⟨i, ⟨j, hj⟩, hk⟩ ↦ ⟨2 * j, even_two_mul j, ?_⟩⟩ rfl rfl
      · rw [hj, ← two_mul] at hk; rw [pow_succ', hk]
      · rw [hj, pow_succ'] at hk; exact mul_left_cancel₀ hp.ne_zero hk
    · rw [PowerSeries.coeff_expand_of_not_dvd p hp.ne_zero _ hdiv, map_zero, ite_eq_right]
      rintro ⟨i, ⟨j, rfl⟩, rfl⟩; exact hdiv ⟨p ^ (2 * j), by rw [pow_succ']⟩
  have hzero (n : ℕ) : π ∣ coeff n (Y ^ (p + 1) -
      (mk fun k ↦ if ∃ i : ℕ, Odd i ∧ k = p ^ i then (1 : R) else 0) *
      (mk fun k ↦ if ∃ i : ℕ, Even i ∧ k = p ^ i then (1 : R) else 0)) := by
    rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq_zero_iff_mem]
    change q (coeff n _) = 0
    rw [← coeff_map, map_sub, map_pow, pow_succ, hpow, hmap, map_mul]
    have hmap_ind (P : ℕ → Prop) : (mk fun k ↦ if P k then (1 : R) else 0).map q =
        mk fun k ↦ if P k then (1 : R ⧸ Ideal.span {π}) else 0 := by ext k; simp [apply_ite q]
    rw [hmap_ind, hmap_ind, sub_self, map_zero]
  exact ⟨mk fun n ↦ (hzero n).choose, by ext n; simpa [coeff_C_mul] using (hzero n).choose_spec⟩

end TauCeti
