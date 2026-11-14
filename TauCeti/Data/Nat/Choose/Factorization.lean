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

Kummer's theorem (`Nat.factorization_choose`) expresses `(n.choose k).factorization p` as the
number of carries when adding `k` and `n - k` in base `p`. Rewriting the carry condition at digit
position `i` as `n % p ^ i < k % p ^ i` compares binomial coefficients with lower indices `p ^ r`
and `p ^ r * u` (`¬ p ∣ u`): since `(p ^ r) % p ^ i ≤ (p ^ r * u) % p ^ i` for every `i`,
every carry for `p ^ r` is also a carry for `p ^ r * u`.

## Main results

* `Nat.factorization_choose_eq_card_lt_mod`: `(n.choose k).factorization p` counts the indices
  `i ∈ Finset.Ico 1 b` with `n % p ^ i < k % p ^ i`.
* `Nat.factorization_choose_pow_le_choose_pow_mul`: for `p` prime, `¬ p ∣ u`, and
  `p ^ r * u ≤ n`, `(n.choose (p ^ r)).factorization p ≤ (n.choose (p ^ r * u)).factorization p`.
* `Nat.not_dvd_choose_pow_factorization`: for `p` prime and `n ≠ 0`,
  `¬ p ∣ n.choose (p ^ (n.factorization p))`.
* `Nat.dvd_choose_of_lt_pow_factorization`: for `p` prime and `1 ≤ i < p ^ (n.factorization p)`,
  `p ∣ n.choose i`.

## References

* E. Kummer, *Über die Ergänzungssätze zu den allgemeinen Reciprocitätsgesetzen*, Journal für die
  reine und angewandte Mathematik 44 (1852), 93–146.
* C. Greve and S. Pauli, *Ramification polygons, splitting fields, and Galois groups of Eisenstein
  polynomials*, International Journal of Number Theory 8 (2012), 1401–1424, Lemma 4.1.
-/

public section

open Finset

namespace Nat

/-- Kummer's theorem rewritten in terms of remainders: for a prime `p`, `k ≤ n`, and
`log p n < b`, `(n.choose k).factorization p` is the number of `i ∈ Ico 1 b` such that
`n % p ^ i < k % p ^ i`. -/
theorem factorization_choose_eq_card_lt_mod {p n k b : ℕ} (hp : p.Prime) (hkn : k ≤ n)
    (hnb : log p n < b) :
    (n.choose k).factorization p = #{i ∈ Ico 1 b | n % p ^ i < k % p ^ i} := by
  rw [factorization_choose hp hkn hnb]
  refine congrArg card (filter_congr fun i _ ↦ ?_)
  set m := p ^ i
  have hm : 0 < m := pow_pos hp.pos i
  have hklt : k % m < m := mod_lt k hm
  have hrlt : (n - k) % m < m := mod_lt (n - k) hm
  have hmod : (k % m + (n - k) % m) % m = n % m := by
    rw [← add_mod, Nat.add_sub_of_le hkn]
  constructor
  · intro hcarry
    have hdiv : (k % m + (n - k) % m) / m = 1 :=
      le_antisymm (Nat.le_of_lt_succ ((div_lt_iff_lt_mul hm).mpr (by omega)))
        ((le_div_iff_mul_le hm).mpr (by omega))
    have heq := mod_add_div (k % m + (n - k) % m) m
    rw [hmod, hdiv, mul_one] at heq
    omega
  · intro hlt
    by_contra hltm
    push Not at hltm
    rw [mod_eq_of_lt hltm] at hmod
    omega

/-- If `p` is prime and `¬ p ∣ u`, then `(p ^ r) % p ^ i ≤ (p ^ r * u) % p ^ i` for every `r` and
`i`. -/
theorem pow_mod_pow_le_pow_mul_mod_pow {p r u i : ℕ} (hp : p.Prime) (hpu : ¬ p ∣ u) :
    p ^ r % p ^ i ≤ (p ^ r * u) % p ^ i := by
  rcases le_or_gt i r with hir | hri
  · have hdvd : p ^ i ∣ p ^ r := pow_dvd_pow p hir
    rw [mod_eq_zero_of_dvd hdvd]
    exact zero_le _
  · obtain ⟨d, hd0, rfl⟩ : ∃ d, 0 < d ∧ i = r + d := ⟨i - r, by omega, by omega⟩
    have hlt : p ^ r < p ^ (r + d) := Nat.pow_lt_pow_right hp.one_lt (by omega)
    rw [mod_eq_of_lt hlt, pow_add, mul_mod_mul_left]
    have hmod0 : u % p ^ d ≠ 0 := by
      intro h0
      exact hpu ((dvd_pow_self p hd0.ne').trans (dvd_of_mod_eq_zero h0))
    exact Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero hmod0)

/-- **Greve–Pauli, Lemma 4.1.** For a prime `p`, `¬ p ∣ u`, and `p ^ r * u ≤ n`, the `p`-adic
valuation of `n.choose (p ^ r)` does not exceed that of `n.choose (p ^ r * u)`. -/
theorem factorization_choose_pow_le_choose_pow_mul {p r u n : ℕ} (hp : p.Prime) (hpu : ¬ p ∣ u)
    (hle : p ^ r * u ≤ n) :
    (n.choose (p ^ r)).factorization p ≤ (n.choose (p ^ r * u)).factorization p := by
  have hu0 : 0 < u := Nat.pos_of_ne_zero fun h ↦ hpu (h ▸ dvd_zero p)
  have hpr : p ^ r ≤ n := (Nat.le_mul_of_pos_right _ hu0).trans hle
  rw [factorization_choose_eq_card_lt_mod hp hpr (lt_succ_self (log p n)),
    factorization_choose_eq_card_lt_mod hp hle (lt_succ_self (log p n))]
  refine card_le_card fun i hi ↦ ?_
  rw [mem_filter] at hi ⊢
  exact ⟨hi.1, hi.2.trans_le (pow_mod_pow_le_pow_mul_mod_pow hp hpu)⟩

/-- For a prime `p` and `n ≠ 0`, `p` does not divide `n.choose (p ^ (n.factorization p))`. -/
theorem not_dvd_choose_pow_factorization {p n : ℕ} (hp : p.Prime) (hn : n ≠ 0) :
    ¬ p ∣ n.choose (p ^ (n.factorization p)) := by
  have : Fact p.Prime := ⟨hp⟩
  set w := n.factorization p
  set ε := n / p ^ w
  have hn_eq : p ^ w * ε = n := ordProj_mul_ordCompl_eq_self n p
  have hε : ¬ p ∣ ε := not_dvd_ordCompl hp hn
  have hmod := Choose.choose_pow_mul_pow_mul_modEq_choose_nat (p := p) (k := w) (a := ε) (b := 1)
  rw [hn_eq, mul_one, choose_one_right] at hmod
  exact fun hdvd ↦ hε (hmod.dvd_iff dvd_rfl |>.mp hdvd)

/-- For a prime `p` and `1 ≤ i < p ^ (n.factorization p)`, `p` divides `n.choose i`. -/
theorem dvd_choose_of_lt_pow_factorization {p n i : ℕ} (hp : p.Prime) (hi0 : 1 ≤ i)
    (hilt : i < p ^ (n.factorization p)) :
    p ∣ n.choose i := by
  rcases eq_or_ne n 0 with rfl | hn0
  · simp at hilt
    omega
  have hle : i ≤ n := hilt.le.trans (le_of_dvd (Nat.pos_of_ne_zero hn0) (ordProj_dvd n p))
  have hifac : i.factorization p < n.factorization p := by
    by_contra hge
    push Not at hge
    have hdvd : p ^ (n.factorization p) ∣ i :=
      (pow_dvd_pow p hge).trans (ordProj_dvd i p)
    exact hilt.not_ge (le_of_dvd hi0 hdvd)
  have hsum := factorization_le_factorization_choose_add (p := p) hle (by omega)
  have hpos : 0 < (n.choose i).factorization p := by omega
  exact hp.dvd_iff_one_le_factorization (choose_pos hle).ne' |>.mpr hpos

end Nat
