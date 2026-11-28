/-
Copyright (c) 2026 TauCeti Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RingTheory.PowerSeries.Basic

import Mathlib.Algebra.CharP.Basic
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Algebra.CharP.Quotient
import Mathlib.Algebra.CharP.Subring
import Mathlib.RingTheory.Ideal.Quotient.Basic

/-!
# Artin–Schreier power series expansion

This file proves the telescoping identity and exact coefficient formula for formal power series
satisfying the Artin–Schreier / Frobenius equation `S - S ^ (p ^ e) = X` in prime characteristic
`p`, together with its lifting modulo a non-unit divisor `π ∣ p` in an arbitrary commutative ring.

## Main results

* `TauCeti.eq_sum_pow_of_sub_pow_eq`: in characteristic `p`, `s - s ^ (p ^ e) = x` implies
  `s = ∑ l ∈ range B, x ^ (p ^ (e * l)) + s ^ (p ^ (e * B))`.
* `TauCeti.coeff_eq_of_sub_pow_eq_X`: in prime characteristic `p` with `e ≠ 0`, a power series
  `S` with `S(0) = 0` and `S - S ^ (p ^ e) = X` has `coeff n S = 1` when `n` is a power of `p ^ e`
  and `0` otherwise.
* `TauCeti.dvd_coeff_sub_of_C_dvd_sub_pow_sub_X`: if `π` is a non-unit dividing `p`, `S(0) = 0`,
  and `C π ∣ S - S ^ (p ^ e) - X`, then `coeff n S` is congruent modulo `π` to `1` if `n` is a
  power of `p ^ e` and `0` otherwise.

## Provenance

Adapted from `grh-lean` (`https://github.com/lsernau/grh-lean`, commit
`72fead102f663d5c7a407964a13dc0cf9d977207`), file `src/Lib/CM/FormalGroup/IntegralParameter.lean`
(`New.eq_sum_pow_of_sub_pow_eq`, `New.coeff_eq_of_sub_pow_eq_X`,
`New.dvd_coeff_sub_of_C_dvd_sub_pow_sub_X`).
-/

@[expose] public section

namespace TauCeti

open Finset PowerSeries

/-- In characteristic `p`, if `s - s ^ (p ^ e) = x`, then
`s = ∑ l ∈ range B, x ^ (p ^ (e * l)) + s ^ (p ^ (e * B))` for every `B`. -/
theorem eq_sum_pow_of_sub_pow_eq {p : ℕ} [Fact p.Prime] {R : Type*} [CommRing R] [CharP R p]
    {x s : R} {e : ℕ} (hs : s - s ^ p ^ e = x) (B : ℕ) :
    s = ∑ l ∈ range B, x ^ p ^ (e * l) + s ^ p ^ (e * B) := by
  have h_term (l : ℕ) : x ^ p ^ (e * l) = s ^ p ^ (e * l) - s ^ p ^ (e * (l + 1)) := by
    simp [← hs, sub_pow_char_pow, ← pow_mul, ← pow_add, mul_add, add_comm]
  simp [h_term, sum_range_sub' fun l ↦ s ^ p ^ (e * l)]

open scoped Classical in
/-- In prime characteristic `p`, let `q = p ^ e` with `e ≠ 0`. If `S(0) = 0` and
`S - S ^ q = X`, then `coeff n S` is `1` if `n` is a power of `q` and `0` otherwise. -/
theorem coeff_eq_of_sub_pow_eq_X {p : ℕ} [Fact p.Prime] {R : Type*} [CommRing R] [CharP R p]
    {S : R⟦X⟧} {e : ℕ} (he : e ≠ 0) (hS₀ : constantCoeff S = 0) (hS : S - S ^ p ^ e = X)
    (n : ℕ) :
    coeff n S = if ∃ j : ℕ, n = (p ^ e) ^ j then 1 else 0 := by
  have : CharP R⟦X⟧ p := charP_of_injective_ringHom C_injective p
  have hq : 1 < p ^ e := Nat.one_lt_pow he (Fact.out : p.Prime).one_lt
  have h_tail : coeff n (S ^ (p ^ e) ^ n) = 0 := by
    obtain ⟨T, hT⟩ := pow_dvd_pow_of_dvd (X_dvd_iff.mpr hS₀) ((p ^ e) ^ n)
    rw [hT, coeff_X_pow_mul', ite_eq_right_iff]
    exact fun hle ↦ absurd (Nat.lt_pow_self hq) (not_lt.mpr hle)
  have h_sum : coeff n S = ∑ l ∈ range n, if n = (p ^ e) ^ l then 1 else 0 := by
    conv_lhs => rw [eq_sum_pow_of_sub_pow_eq (p := p) hS n]
    simp [pow_mul p e, coeff_X_pow, h_tail]
  rw [h_sum]
  split_ifs with hn
  · obtain ⟨j, rfl⟩ := hn
    simp [Nat.pow_right_inj hq, Nat.lt_pow_self hq]
  · exact sum_eq_zero fun l _ ↦ ite_eq_right fun hl ↦ hn ⟨l, hl⟩

open scoped Classical in
/-- If `π` is a non-unit dividing `p`, `q = p ^ e` with `e ≠ 0`, `S(0) = 0`, and
`S - S ^ q ≡ X` modulo `π`, then `coeff n S` is congruent modulo `π` to `1` if `n` is a power of
`q` and `0` otherwise. -/
theorem dvd_coeff_sub_of_C_dvd_sub_pow_sub_X {p : ℕ} [Fact p.Prime] {R : Type*} [CommRing R]
    {π : R} (hπ : ¬IsUnit π) (hπp : π ∣ p) {S : R⟦X⟧} {e : ℕ} (he : e ≠ 0)
    (hS₀ : constantCoeff S = 0) (hS : C π ∣ S - S ^ p ^ e - X) (n : ℕ) :
    π ∣ coeff n S - if ∃ j : ℕ, n = (p ^ e) ^ j then 1 else 0 := by
  let φ : R →+* R ⧸ Ideal.span {π} := Ideal.Quotient.mk (Ideal.span {π})
  have hφ {x : R} : φ x = 0 ↔ π ∣ x := Ideal.Quotient.eq_zero_iff_dvd π x
  have : Nontrivial (R ⧸ Ideal.span {π}) :=
    Ideal.Quotient.nontrivial_iff.mpr (mt Ideal.span_singleton_eq_top.mp hπ)
  have : CharP (R ⧸ Ideal.span {π}) p :=
    (CharP.charP_iff_prime_eq_zero Fact.out).mpr (by simpa using hφ.mpr hπp)
  have h_map : S.map φ - S.map φ ^ p ^ e = X := by
    simpa [hφ.mpr dvd_rfl, sub_eq_zero] using map_dvd (PowerSeries.map φ) hS
  have h_coeff : coeff n (S.map φ) = if ∃ j : ℕ, n = (p ^ e) ^ j then 1 else 0 :=
    coeff_eq_of_sub_pow_eq_X (p := p) he (by simp [← coeff_zero_eq_constantCoeff_apply, hS₀])
      h_map n
  rw [← hφ, map_sub, ← coeff_map, h_coeff, apply_ite φ, map_one, map_zero, sub_self]

end TauCeti
