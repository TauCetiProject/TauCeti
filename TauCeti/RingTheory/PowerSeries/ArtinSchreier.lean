/-
Copyright (c) 2026 TauCeti Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RingTheory.PowerSeries.Basic

import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.CharP.Basic
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.RingTheory.Ideal.Quotient.Basic
import TauCeti.Algebra.CharP.ArtinSchreier

/-!
# Artin–Schreier power series expansion

This file proves the exact coefficient formula for formal power series satisfying the
Artin–Schreier / Frobenius equation `S - S ^ (p ^ e) = X` in prime characteristic `p`, together
with the corresponding congruence for power series over a commutative ring satisfying the equation
modulo a divisor `π ∣ p`. The resulting congruence `Y ≡ ∑ z ^ (q ^ j)` modulo `π` is the algebraic
input for analysing the formal parameter of a CM or Lubin–Tate formal group under multiplication by
a uniformiser `π` (Lubin–Tate 1965).

## Main results

* `TauCeti.PowerSeries.coeff_eq_of_sub_pow_eq_X`: in prime characteristic `p`, a power series `S`
  with `S(0) = 0` and `S - S ^ (p ^ e) = X` has `coeff n S = 1` when `n` is a power of `p ^ e` and
  `0` otherwise.
* `TauCeti.PowerSeries.dvd_coeff_sub_of_C_dvd_sub_pow_sub_X`: if `π ∣ p`, `S(0) = 0`, and
  `C π ∣ S - S ^ (p ^ e) - X`, then `coeff n S` is congruent modulo `π` to `1` if `n` is a power
  of `p ^ e` and `0` otherwise.

## Provenance

Adapted from `grh-lean` (`https://github.com/lsernau/grh-lean`, commit
`72fead102f663d5c7a407964a13dc0cf9d977207`, Apache 2.0, Copyright 2026 Anthropic, PBC), file
`src/Lib/CM/FormalGroup/IntegralParameter.lean` (`New.coeff_eq_of_sub_pow_eq_X`,
`New.dvd_coeff_sub_of_C_dvd_sub_pow_sub_X`).
-/

@[expose] public section

namespace TauCeti.PowerSeries

open Finset _root_.PowerSeries

open scoped Classical in
/-- In prime characteristic `p`, let `q = p ^ e`. If `S(0) = 0` and `S - S ^ q = X`, then
`coeff n S` is `1` if `n` is a power of `q` and `0` otherwise. -/
theorem coeff_eq_of_sub_pow_eq_X {p : ℕ} [Fact p.Prime] {R : Type*} [CommRing R] [CharP R p]
    {S : R⟦X⟧} {e : ℕ} (hS₀ : constantCoeff S = 0) (hS : S - S ^ p ^ e = X) (n : ℕ) :
    coeff n S = if ∃ j : ℕ, n = (p ^ e) ^ j then 1 else 0 := by
  have : CharP R⟦X⟧ p := charP_of_injective_ringHom C_injective p
  rcases eq_or_ne e 0 with rfl | he
  · exfalso
    have : Nontrivial R := CharP.nontrivial_of_char_ne_one (Fact.out : p.Prime).ne_one
    have : (0 : R⟦X⟧) = X := by simpa using hS
    exact X_ne_zero this.symm
  have hq : 1 < p ^ e := Nat.one_lt_pow he (Fact.out : p.Prime).one_lt
  have h_tail : coeff n (S ^ (p ^ e) ^ n) = 0 := by
    obtain ⟨T, hT⟩ := pow_dvd_pow_of_dvd (X_dvd_iff.mpr hS₀) ((p ^ e) ^ n)
    simp [hT, coeff_X_pow_mul', (Nat.lt_pow_self hq).not_ge]
  have h_sum : coeff n S = ∑ l ∈ range n, if n = (p ^ e) ^ l then 1 else 0 := by
    conv_lhs => rw [TauCeti.eq_sum_pow_of_sub_pow_eq (p := p) hS n]
    simp [pow_mul p e, coeff_X_pow, h_tail]
  rw [h_sum]
  split_ifs with hn
  · obtain ⟨j, rfl⟩ := hn
    simp [Nat.pow_right_inj hq, Nat.lt_pow_self hq]
  · exact sum_eq_zero fun l _ ↦ ite_eq_right fun hl ↦ hn ⟨l, hl⟩

open scoped Classical in
/-- If `π ∣ p`, `q = p ^ e`, `S(0) = 0`, and `S - S ^ q ≡ X` modulo `π`, then `coeff n S` is
congruent modulo `π` to `1` if `n` is a power of `q` and `0` otherwise. -/
theorem dvd_coeff_sub_of_C_dvd_sub_pow_sub_X {p : ℕ} [Fact p.Prime] {R : Type*} [CommRing R]
    {π : R} (hπp : π ∣ p) {S : R⟦X⟧} {e : ℕ} (hS₀ : constantCoeff S = 0)
    (hS : C π ∣ S - S ^ p ^ e - X) (n : ℕ) :
    π ∣ coeff n S - if ∃ j : ℕ, n = (p ^ e) ^ j then 1 else 0 := by
  by_cases hπ : IsUnit π
  · exact hπ.dvd
  let φ : R →+* R ⧸ Ideal.span {π} := Ideal.Quotient.mk (Ideal.span {π})
  have hφ {x : R} : φ x = 0 ↔ π ∣ x := Ideal.Quotient.eq_zero_iff_dvd π x
  have : Nontrivial (R ⧸ Ideal.span {π}) :=
    Ideal.Quotient.nontrivial_iff.mpr (mt Ideal.span_singleton_eq_top.mp hπ)
  have : CharP (R ⧸ Ideal.span {π}) p :=
    (CharP.charP_iff_prime_eq_zero Fact.out).mpr (by simpa using hφ.mpr hπp)
  have h_map : S.map φ - S.map φ ^ p ^ e = X := by
    simpa [hφ.mpr dvd_rfl, sub_eq_zero] using map_dvd (_root_.PowerSeries.map φ) hS
  have h_coeff : coeff n (S.map φ) = if ∃ j : ℕ, n = (p ^ e) ^ j then 1 else 0 :=
    coeff_eq_of_sub_pow_eq_X (p := p) (by simp [← coeff_zero_eq_constantCoeff_apply, hS₀]) h_map n
  rw [← hφ, map_sub, ← coeff_map, h_coeff]
  split_ifs <;> simp

end TauCeti.PowerSeries
