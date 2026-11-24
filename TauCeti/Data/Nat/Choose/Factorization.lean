/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Nat.Choose.Factorization
import Mathlib.Data.Nat.Choose.Lucas

/-!
# Prime-power multiplicities in binomial coefficients

Rewriting Kummer's carry condition (`Nat.factorization_choose`) at digit `i` as
`n % p ^ i < k % p ^ i` compares binomial coefficients at `p ^ r` and `p ^ r * u` (`¬ p ∣ u`).

## Main results

* `Nat.factorization_choose_eq_card_lt_mod`: `(n.choose k).factorization p` counts `i ∈ Ico 1 b`
  with `n % p ^ i < k % p ^ i`.
* `Nat.factorization_choose_pow_le_choose_pow_mul`: for `¬ p ∣ u` and `p ^ r * u ≤ n`,
  `(n.choose (p ^ r)).factorization p ≤ (n.choose (p ^ r * u)).factorization p`.
* `Nat.not_dvd_choose_pow_factorization` and `Nat.dvd_choose_of_lt_pow_factorization`: divisibility
  of `n.choose i` by `p` at and below `p ^ (n.factorization p)`.

## References

* E. Kummer, *Über die Ergänzungssätze zu den allgemeinen Reciprocitätsgesetzen*, J. Reine Angew.
  Math. 44 (1852), 93–146.
* C. Greve and S. Pauli, *Ramification polygons, splitting fields, and Galois groups of Eisenstein
  polynomials*, Int. J. Number Theory 8 (2012), 1401–1424, Lemma 4.1.
-/

public section

open Finset

namespace Nat

/-- Kummer's theorem in terms of remainders: for `p` prime, `k ≤ n`, and `log p n < b`,
`(n.choose k).factorization p` counts `i ∈ Ico 1 b` with `n % p ^ i < k % p ^ i`. -/
theorem factorization_choose_eq_card_lt_mod {p n k b : ℕ} (hp : p.Prime) (hkn : k ≤ n)
    (hnb : log p n < b) :
    (n.choose k).factorization p = #{i ∈ Ico 1 b | n % p ^ i < k % p ^ i} := by
  rw [factorization_choose hp hkn hnb]
  refine congrArg card (filter_congr fun i _ ↦ ?_)
  set m := p ^ i
  have hm : 0 < m := pow_pos hp.pos i
  have := mod_lt k hm; have := mod_lt (n - k) hm
  have hmod : (k % m + (n - k) % m) % m = n % m := by rw [← add_mod, Nat.add_sub_of_le hkn]
  rcases lt_or_ge (k % m + (n - k) % m) m with hlt | hge
  · rw [mod_eq_of_lt hlt] at hmod; omega
  · rw [mod_eq_sub_mod hge, mod_eq_of_lt (by omega)] at hmod; omega

/-- If `¬ p ∣ u`, then `(p ^ r) % p ^ i ≤ (p ^ r * u) % p ^ i`. -/
theorem pow_mod_pow_le_pow_mul_mod_pow {p r u i : ℕ} (hpu : ¬ p ∣ u) :
    p ^ r % p ^ i ≤ (p ^ r * u) % p ^ i := by
  rcases le_or_gt p 1 with hp1 | hp1
  · interval_cases p
    · simp only [zero_dvd_iff] at hpu
      rcases eq_or_ne r 0 with rfl | hr0 <;> rcases eq_or_ne i 0 with rfl | hi0 <;>
        simp [Nat.one_le_iff_ne_zero.mpr hpu, zero_pow, *]
    · exact absurd (one_dvd u) hpu
  · rcases le_or_gt i r with hir | hri
    · simp [mod_eq_zero_of_dvd (pow_dvd_pow p hir)]
    · obtain ⟨d, hd0, rfl⟩ : ∃ d, 0 < d ∧ i = r + d := ⟨i - r, by omega, by omega⟩
      rw [mod_eq_of_lt (Nat.pow_lt_pow_right hp1 (by omega)), pow_add, mul_mod_mul_left]
      exact Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero fun h0 ↦
        hpu ((dvd_pow_self p hd0.ne').trans (dvd_of_mod_eq_zero h0)))

/-- **Greve–Pauli, Lemma 4.1.** For `¬ p ∣ u` and `p ^ r * u ≤ n`,
`(n.choose (p ^ r)).factorization p ≤ (n.choose (p ^ r * u)).factorization p`. -/
theorem factorization_choose_pow_le_choose_pow_mul {p r u n : ℕ} (hpu : ¬ p ∣ u)
    (hle : p ^ r * u ≤ n) :
    (n.choose (p ^ r)).factorization p ≤ (n.choose (p ^ r * u)).factorization p := by
  by_cases hp : p.Prime
  · have hpr : p ^ r ≤ n := (Nat.le_mul_of_pos_right _
      (Nat.pos_of_ne_zero fun h : u = 0 ↦ hpu (h ▸ dvd_zero p))).trans hle
    rw [factorization_choose_eq_card_lt_mod hp hpr (lt_succ_self _),
      factorization_choose_eq_card_lt_mod hp hle (lt_succ_self _)]
    exact card_le_card fun i hi ↦ by
      rw [mem_filter] at hi ⊢; exact ⟨hi.1, hi.2.trans_le (pow_mod_pow_le_pow_mul_mod_pow hpu)⟩
  · simp [factorization_eq_zero_of_not_prime _ hp]

/-- For `p` prime and `n ≠ 0`, `¬ p ∣ n.choose (p ^ (n.factorization p))`. -/
theorem not_dvd_choose_pow_factorization {p n : ℕ} (hp : p.Prime) (hn : n ≠ 0) :
    ¬ p ∣ n.choose (p ^ (n.factorization p)) := by
  have : Fact p.Prime := ⟨hp⟩
  have hmod := Choose.choose_pow_mul_pow_mul_modEq_choose_nat
    (p := p) (k := n.factorization p) (a := n / p ^ n.factorization p) (b := 1)
  rw [ordProj_mul_ordCompl_eq_self, mul_one, choose_one_right] at hmod
  exact fun hdvd ↦ not_dvd_ordCompl hp hn (hmod.dvd_iff dvd_rfl |>.mp hdvd)

/-- For `1 ≤ i < p ^ (n.factorization p)`, `p ∣ n.choose i`. -/
theorem dvd_choose_of_lt_pow_factorization {p n i : ℕ} (hi0 : 1 ≤ i)
    (hilt : i < p ^ (n.factorization p)) :
    p ∣ n.choose i := by
  by_cases hp : p.Prime
  · rcases eq_or_ne n 0 with rfl | hn0
    · simp at hilt; omega
    have hle : i ≤ n := hilt.le.trans (le_of_dvd (Nat.pos_of_ne_zero hn0) (ordProj_dvd n p))
    have hifac : i.factorization p < n.factorization p := not_le.mp fun hge ↦
      hilt.not_ge (le_of_dvd hi0 ((pow_dvd_pow p hge).trans (ordProj_dvd i p)))
    have := factorization_le_factorization_choose_add (p := p) hle (by omega)
    exact hp.dvd_iff_one_le_factorization (choose_pos hle).ne' |>.mpr (by omega)
  · simp [factorization_eq_zero_of_not_prime _ hp] at hilt; omega

end Nat
