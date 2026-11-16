/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.ZMod.Basic
public import TauCeti.NumberTheory.LocalField.MassFormula.Krasner.Count
public import TauCeti.NumberTheory.LocalField.Padic
public import TauCeti.RingTheory.LaurentSeries.LocalField

/-!
# Specializations and worked examples of Krasner's count

This file specializes the general Krasner count (`TauCeti.krasnerCount`) and Ore realizability
criterion (`TauCeti.IsOreAdmissible`) to the two standard families of nonarchimedean local fields:

* the `p`-adic fields `ℚ_[p]` (mixed characteristic, residue cardinality `q = p`, absolute
  ramification index `e = 1`), and
* the formal Laurent series fields `F⸨X⸩` over a finite field `F` (equal characteristic
  `p = ringChar F`, residue cardinality `q = Nat.card F`).

As worked checks, we deduce the exact total count `#σ_{ℚ_[p]}(p) = p * (p - 1) ^ 2 + p ^ 2` for
every prime `p` (yielding `21` for `ℚ_[3]` of degree `3`), the prime-power count
`#σ_{ℚ_[2]}(4) = 92` (exercising both nontrivial `v_2(j % 4)` obstructions and multi-term ceiling
sums), and the equal-characteristic stratum count
`#{E ∈ σ_{F⸨X⸩}(p) | c(E) = j} = p * (q - 1) * q ^ (j / p)` for `¬ p ∣ j` (yielding `2 ^ m` for
`F = ZMod 2`, degree `2`, and wild exponent `2 * m - 1`).

## Main results

* `TauCeti.isOreAdmissible_padic_iff`: Ore's condition over `ℚ_[p]` in terms of `padicValNat p`.
* `TauCeti.krasnerCount_padic_of_mod_eq_zero`, `TauCeti.krasnerCount_padic_of_mod_pos`: Krasner's
  closed form over `ℚ_[p]`.
* `TauCeti.ncard_totallyRamifiedOfDegree_padic_eq_sum`: `#σ_{ℚ_[p]}(n)` as a finite sum of
  Krasner counts.
* `TauCeti.ncard_totallyRamifiedOfDegree_prime_padic`: `#σ_{ℚ_[p]}(p) = p * (p - 1) ^ 2 + p ^ 2`.
* `TauCeti.ncard_totallyRamifiedOfDegree_three_padicThree`: `#σ_{ℚ_[3]}(3) = 21`.
* `TauCeti.ncard_totallyRamifiedOfDegree_four_padicTwo`: `#σ_{ℚ_[2]}(4) = 92`.
* `TauCeti.isOreAdmissible_laurentSeries_iff`, `TauCeti.krasnerCount_laurentSeries`,
  `TauCeti.ncard_totallyRamifiedOfDegree_wildExponent_eq_laurentSeries`: Ore's condition and
  Krasner's count over `F⸨X⸩` when `ringChar F ∣ n`.
* `TauCeti.ncard_totallyRamifiedOfDegree_ringChar_wildExponent_eq_laurentSeries`: exact stratum
  count for degree `ringChar F` over `F⸨X⸩`.
* `TauCeti.ncard_totallyRamifiedOfDegree_two_laurentSeries_zmodTwo`:
  `#{E ∈ σ_{(ZMod 2)⸨X⸩}(2) | c(E) = 2 * m - 1} = 2 ^ m` for `0 < m`.

## References

* M. Krasner, *Nombre des extensions d'un degré donné d'un corps `𝔭`-adique*, in *Les tendances
  géom. en algèbre et théorie des nombres*, CNRS, Paris (1966), 143–169.
* S. Pauli and X.-F. Roblot, *On the computation of all extensions of a `p`-adic field of a given
  degree*, Math. Comp. **70** (2001), 1641–1659, §6.
-/

public section

open ValuativeRel IsNonarchimedeanLocalField
open scoped LaurentSeries

namespace TauCeti

/-! ### Specialization to `ℚ_[p]` -/

private theorem ringChar_residueField_padic (p : ℕ) [Fact p.Prime] :
    ringChar 𝓀[ℚ_[p]] = p := by
  have hp : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero
  exact (natCastValuation_ne_zero_iff_ringChar_eq ℚ_[p] Fact.out hp).1
    (by rw [Padic.natCastValuation_self]; exact one_ne_zero)

/-- **Ore's realizability condition over `ℚ_[p]`**: for `0 < n`, the pair `(n, j)` is Ore-admissible
over `ℚ_[p]` iff either `n ∣ j` and `j / n = v_p(n)`, or `0 < j % n` and
`v_p(j % n) ≤ j / n < v_p(n)`. -/
theorem isOreAdmissible_padic_iff {p : ℕ} [Fact p.Prime] {n j : ℕ} (hn : 0 < n) :
    IsOreAdmissible ℚ_[p] n j ↔
      (j % n = 0 ∧ j / n = padicValNat p n) ∨
        (0 < j % n ∧ padicValNat p (j % n) ≤ j / n ∧ j / n < padicValNat p n) := by
  have hnK : (n : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
  rcases Nat.eq_zero_or_pos (j % n) with hb | hb
  · rw [isOreAdmissible_iff_of_mod_eq_zero hn hb, IsDiscreteValuationRing.addVal_natCast _ n hnK,
      Padic.natCastValuation_eq_padicValNat, Nat.cast_inj]
    constructor
    · exact fun h ↦ Or.inl ⟨hb, h⟩
    · rintro (⟨_, h⟩ | ⟨hpos, _⟩)
      · exact h
      · omega
  · have hbK : ((j % n : ℕ) : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.2 hb.ne'
    rw [isOreAdmissible_iff_of_mod_pos hn hb, IsDiscreteValuationRing.addVal_natCast _ (j % n) hbK,
      IsDiscreteValuationRing.addVal_natCast _ n hnK, Padic.natCastValuation_eq_padicValNat,
      Padic.natCastValuation_eq_padicValNat, Nat.cast_le, ← Nat.cast_add_one, Nat.cast_le]
    constructor
    · exact fun ⟨h1, h2⟩ ↦ Or.inr ⟨hb, h1, Nat.lt_of_succ_le h2⟩
    · rintro (⟨h0, _⟩ | ⟨_, h1, h2⟩)
      · omega
      · exact ⟨h1, Nat.succ_le_of_lt h2⟩

/-- **Krasner's count over `ℚ_[p]` (`n ∣ j`)**: for an Ore-admissible `(n, j)` with `j % n = 0`,
`krasnerCount ℚ_[p] n j = n * p ^ (∑ i ∈ Finset.Icc 1 (j / n), n / p ^ i)`. -/
theorem krasnerCount_padic_of_mod_eq_zero {p : ℕ} [Fact p.Prime] {n j : ℕ}
    (hO : IsOreAdmissible ℚ_[p] n j) (hb : j % n = 0) :
    krasnerCount ℚ_[p] n j = n * p ^ ∑ i ∈ Finset.Icc 1 (j / n), n / p ^ i := by
  have hrc : ringChar 𝓀[ℚ_[p]] = p := ringChar_residueField_padic p
  have hp : (ringChar 𝓀[ℚ_[p]] : ℚ_[p]) ≠ 0 := by
    rw [hrc]
    exact Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero
  have he : natCastValuation ℚ_[p] (ringChar 𝓀[ℚ_[p]]) hp = 1 := by
    simp only [hrc, Padic.natCastValuation_self]
  rw [krasnerCount_of_mod_eq_zero_of_natCast_ne_zero hp hO hb, Padic.natCard_residueField, he]
  simp only [hrc, Nat.add_sub_cancel, Nat.div_one]

/-- **Krasner's count over `ℚ_[p]` (`¬ n ∣ j`)**: for an Ore-admissible `(n, j)` with `0 < j % n`,
`krasnerCount ℚ_[p] n j = n * (p - 1) * p ^ (∑_{i=1}^{j/n} n / p ^ i + (j % n) / p ^ (j/n + 1))`.
-/
theorem krasnerCount_padic_of_mod_pos {p : ℕ} [Fact p.Prime] {n j : ℕ}
    (hO : IsOreAdmissible ℚ_[p] n j) (hb : 0 < j % n) :
    krasnerCount ℚ_[p] n j =
      n * (p - 1) * p ^ (∑ i ∈ Finset.Icc 1 (j / n), n / p ^ i + (j % n) / p ^ (j / n + 1)) := by
  have hrc : ringChar 𝓀[ℚ_[p]] = p := ringChar_residueField_padic p
  have hp : (ringChar 𝓀[ℚ_[p]] : ℚ_[p]) ≠ 0 := by
    rw [hrc]
    exact Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero
  have he : natCastValuation ℚ_[p] (ringChar 𝓀[ℚ_[p]]) hp = 1 := by
    simp only [hrc, Padic.natCastValuation_self]
  rw [krasnerCount_of_mod_pos_of_natCast_ne_zero hp hO hb, Padic.natCard_residueField, he]
  simp only [hrc, Nat.add_sub_cancel, Nat.div_one]

/-- **Total count of totally ramified degree-`n` extensions of `ℚ_[p]`**:
`#σ_{ℚ_[p]}(n) = ∑_{j = 0}^{n * v_p(n)} krasnerCount ℚ_[p] n j`. -/
theorem ncard_totallyRamifiedOfDegree_padic_eq_sum (p : ℕ) [Fact p.Prime] {n : ℕ} (hn : 0 < n) :
    (totallyRamifiedOfDegree ℚ_[p] n).ncard =
      ∑ j ∈ Finset.range (n * padicValNat p n + 1), krasnerCount ℚ_[p] n j := by
  have hnK : (n : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
  rw [ncard_totallyRamifiedOfDegree_eq_sum hnK, Padic.natCastValuation_eq_padicValNat]

/-- **Totally ramified extensions of `ℚ_[p]` of prime degree `p`**: inside a separable closure of
`ℚ_[p]`, there are `p * (p - 1) ^ 2 + p ^ 2` totally ramified extensions of degree `p`. -/
theorem ncard_totallyRamifiedOfDegree_prime_padic (p : ℕ) [Fact p.Prime] :
    (totallyRamifiedOfDegree ℚ_[p] p).ncard = p * (p - 1) ^ 2 + p ^ 2 := by
  have hp : p.Prime := Fact.out
  have hv : padicValNat p p = 1 := by
    rw [Nat.padicValNat_def, Nat.multiplicity_self hp.one_lt]
  have h0 : krasnerCount ℚ_[p] p 0 = 0 := by
    refine krasnerCount_of_not_isOreAdmissible fun hO ↦ ?_
    rcases (isOreAdmissible_padic_iff hp.pos).1 hO with ⟨_, hdiv⟩ | ⟨hpos, _⟩
    · rw [Nat.zero_div, hv] at hdiv
      omega
    · simp at hpos
  have hp_top : krasnerCount ℚ_[p] p p = p ^ 2 := by
    have hO : IsOreAdmissible ℚ_[p] p p :=
      (isOreAdmissible_padic_iff hp.pos).2
        (Or.inl ⟨Nat.mod_self p, by rw [Nat.div_self hp.pos, hv]⟩)
    rw [krasnerCount_padic_of_mod_eq_zero hO (Nat.mod_self p), Nat.div_self hp.pos]
    simp only [Finset.Icc_self, Finset.sum_singleton, pow_one, Nat.div_self hp.pos, sq]
  have hmid : ∑ k ∈ Finset.range (p - 1), krasnerCount ℚ_[p] p (k + 1) = p * (p - 1) ^ 2 := by
    have hterm : ∀ k ∈ Finset.range (p - 1), krasnerCount ℚ_[p] p (k + 1) = p * (p - 1) := by
      intro k hk
      rw [Finset.mem_range] at hk
      have hlt : k + 1 < p := by omega
      have hmod : (k + 1) % p = k + 1 := Nat.mod_eq_of_lt hlt
      have hdiv : (k + 1) / p = 0 := Nat.div_eq_of_lt hlt
      have hndvd : ¬ p ∣ (k + 1) := Nat.not_dvd_of_pos_of_lt (Nat.succ_pos k) hlt
      have hvk : padicValNat p (k + 1) = 0 := by
        rw [Nat.padicValNat_def]
        exact multiplicity_eq_zero_of_not_dvd hndvd
      have hO : IsOreAdmissible ℚ_[p] p (k + 1) :=
        (isOreAdmissible_padic_iff hp.pos).2
          (Or.inr ⟨by omega, by rw [hmod, hvk, hdiv], by rw [hdiv, hv]; omega⟩)
      rw [krasnerCount_padic_of_mod_pos hO (by omega), hdiv, hmod, pow_one, Nat.div_eq_of_lt hlt]
      simp
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, Finset.card_range, smul_eq_mul]
    ring
  have hsplit : ∑ j ∈ Finset.range p, krasnerCount ℚ_[p] p j =
      ∑ k ∈ Finset.range (p - 1), krasnerCount ℚ_[p] p (k + 1) + krasnerCount ℚ_[p] p 0 := by
    rw [← Finset.sum_range_succ', Nat.sub_add_cancel hp.pos]
  rw [ncard_totallyRamifiedOfDegree_padic_eq_sum p hp.pos, hv, mul_one, Finset.sum_range_succ,
    hsplit, h0, add_zero, hmid, hp_top]

/-! ### Worked numerical checks over `ℚ_[3]` and `ℚ_[2]` -/

/-- Inside a separable closure of `ℚ_[3]`, there are exactly `21` totally ramified cubic
extensions (`6` of wild exponent `1`, `6` of wild exponent `2`, and `9` of wild exponent `3`). -/
theorem ncard_totallyRamifiedOfDegree_three_padicThree :
    (totallyRamifiedOfDegree ℚ_[3] 3).ncard = 21 := by
  rw [ncard_totallyRamifiedOfDegree_prime_padic 3]
  norm_num

/-- Inside a separable closure of `ℚ_[2]`, there are exactly `92` totally ramified quartic
extensions (`4 + 8 + 16 + 16 + 16 + 32 = 92` across wild exponents `1, 3, 5, 6, 7, 8`). -/
theorem ncard_totallyRamifiedOfDegree_four_padicTwo :
    (totallyRamifiedOfDegree ℚ_[2] 4).ncard = 92 := by
  have hv4 : padicValNat 2 4 = 2 := by
    rw [Nat.padicValNat_def, show (4 : ℕ) = 2 ^ 2 by norm_num, Nat.multiplicity_prime_pow]
  have hv2 : padicValNat 2 2 = 1 := by
    rw [Nat.padicValNat_def, Nat.multiplicity_self (by norm_num)]
  have hv1 : padicValNat 2 1 = 0 := by
    rw [Nat.padicValNat_def]
    exact multiplicity_eq_zero_of_not_dvd (by decide)
  have hv3 : padicValNat 2 3 = 0 := by
    rw [Nat.padicValNat_def]
    exact multiplicity_eq_zero_of_not_dvd (by decide)
  have hpos (j : ℕ) (hb : 0 < j % 4) (h1 : padicValNat 2 (j % 4) ≤ j / 4) (h2 : j / 4 < 2) :
      krasnerCount ℚ_[2] 4 j =
        4 * 2 ^ (∑ i ∈ Finset.Icc 1 (j / 4), 4 / 2 ^ i + (j % 4) / 2 ^ (j / 4 + 1)) := by
    have hO : IsOreAdmissible ℚ_[2] 4 j :=
      (isOreAdmissible_padic_iff (by norm_num)).2 (Or.inr ⟨hb, h1, by omega⟩)
    exact krasnerCount_padic_of_mod_pos hO hb
  rw [ncard_totallyRamifiedOfDegree_padic_eq_sum 2 (by norm_num), hv4]
  simp only [show 4 * 2 + 1 = 9 by norm_num, Finset.sum_range_succ, Finset.range_zero,
    Finset.sum_empty, zero_add]
  have hk0 : krasnerCount ℚ_[2] 4 0 = 0 := krasnerCount_of_not_isOreAdmissible fun hO ↦ by
    rcases (isOreAdmissible_padic_iff (by norm_num)).1 hO with ⟨_, h⟩ | ⟨h, _⟩ <;> simp [hv4] at h
  have hk2 : krasnerCount ℚ_[2] 4 2 = 0 := krasnerCount_of_not_isOreAdmissible fun hO ↦ by
    rcases (isOreAdmissible_padic_iff (by norm_num)).1 hO with ⟨h, _⟩ | ⟨_, h, _⟩
    · norm_num at h
    · simp [hv2] at h
  have hk4 : krasnerCount ℚ_[2] 4 4 = 0 := krasnerCount_of_not_isOreAdmissible fun hO ↦ by
    rcases (isOreAdmissible_padic_iff (by norm_num)).1 hO with ⟨_, h⟩ | ⟨h, _⟩ <;> simp [hv4] at h
  have hk8 : krasnerCount ℚ_[2] 4 8 = 32 := by
    have hO : IsOreAdmissible ℚ_[2] 4 8 :=
      (isOreAdmissible_padic_iff (by norm_num)).2 (Or.inl ⟨by norm_num, by simp [hv4]⟩)
    rw [krasnerCount_padic_of_mod_eq_zero hO (by norm_num), show 8 / 4 = 2 by norm_num,
      show Finset.Icc 1 2 = {1, 2} by decide]
    norm_num
  rw [hk0, hk2, hk4, hk8,
    hpos 1 (by norm_num) (by simp [hv1]) (by norm_num),
    hpos 3 (by norm_num) (by simp [hv3]) (by norm_num),
    hpos 5 (by norm_num) (by simp [hv1]) (by norm_num),
    hpos 6 (by norm_num) (by simp [hv2]) (by norm_num),
    hpos 7 (by norm_num) (by simp [hv3]) (by norm_num)]
  norm_num

/-! ### Specialization to `F⸨X⸩` -/

/-- **Ore's realizability condition over `F⸨X⸩`**: for a finite field `F` and `0 < n` divisible by
`ringChar F`, the pair `(n, j)` is Ore-admissible over `F⸨X⸩` iff `ringChar F` does not divide
`j`. -/
theorem isOreAdmissible_laurentSeries_iff (F : Type*) [Field F] [Finite F] {n j : ℕ}
    (hn : 0 < n) (hpn : ringChar F ∣ n) :
    IsOreAdmissible F⸨X⸩ n j ↔ ¬ ringChar F ∣ j := by
  have hnK : (n : F⸨X⸩) = 0 := by
    rw [← map_natCast (algebraMap F F⸨X⸩), (ringChar.spec F n).2 hpn, map_zero]
  rw [isOreAdmissible_iff_of_natCast_eq_zero hn hnK, LaurentSeries.ringChar_residueField]

/-- **Krasner's count over `F⸨X⸩`**: for a finite field `F` with `p = ringChar F`, `0 < n`,
`p ∣ n`, and `¬ p ∣ j`,
`krasnerCount F⸨X⸩ n j = n * (Nat.card F - 1) * Nat.card F ^ ((j / n) * (n / p) + (j % n) / p)`.
-/
theorem krasnerCount_laurentSeries (F : Type*) [Field F] [Finite F] {n j : ℕ}
    (hn : 0 < n) (hpn : ringChar F ∣ n) (hpj : ¬ ringChar F ∣ j) :
    krasnerCount F⸨X⸩ n j =
      n * (Nat.card F - 1) * Nat.card F ^ ((j / n) * (n / ringChar F) + (j % n) / ringChar F) := by
  have hp : (ringChar 𝓀[F⸨X⸩] : F⸨X⸩) = 0 := by
    rw [LaurentSeries.ringChar_residueField, ← map_natCast (algebraMap F F⸨X⸩),
      ringChar.Nat.cast_ringChar, map_zero]
  have hpn' : ringChar 𝓀[F⸨X⸩] ∣ n := by rwa [LaurentSeries.ringChar_residueField]
  have hpj' : ¬ ringChar 𝓀[F⸨X⸩] ∣ j := by rwa [LaurentSeries.ringChar_residueField]
  rw [krasnerCount_of_natCast_ringChar_eq_zero hp hn hpn' hpj',
    LaurentSeries.natCard_residueField, LaurentSeries.ringChar_residueField]

/-- **Discriminant-refined count over `F⸨X⸩`**: although `σ_{F⸨X⸩}(n)` is infinite whenever
`ringChar F ∣ n`, each wild-exponent stratum `c(E) = j` with `¬ ringChar F ∣ j` is finite of
exact cardinality `n * (q - 1) * q ^ ((j / n) * (n / p) + (j % n) / p)`. -/
theorem ncard_totallyRamifiedOfDegree_wildExponent_eq_laurentSeries (F : Type*) [Field F] [Finite F]
    {n j : ℕ} (hn : 0 < n) (hpn : ringChar F ∣ n) (hpj : ¬ ringChar F ∣ j) :
    {E ∈ totallyRamifiedOfDegree F⸨X⸩ n | E.wildExponent = j}.ncard =
      n * (Nat.card F - 1) * Nat.card F ^ ((j / n) * (n / ringChar F) + (j % n) / ringChar F) := by
  rw [ncard_totallyRamifiedOfDegree_wildExponent_eq, krasnerCount_laurentSeries F hn hpn hpj]

/-- **Artin–Schreier stratum count over `F⸨X⸩`**: for a finite field `F` of characteristic `p`,
every wild exponent `j` prime to `p` is realized by exactly `p * (q - 1) * q ^ (j / p)` totally
ramified extensions of degree `p` inside a separable closure of `F⸨X⸩`. -/
theorem ncard_totallyRamifiedOfDegree_ringChar_wildExponent_eq_laurentSeries (F : Type*)
    [Field F] [Finite F] {j : ℕ} (hpj : ¬ ringChar F ∣ j) :
    {E ∈ totallyRamifiedOfDegree F⸨X⸩ (ringChar F) | E.wildExponent = j}.ncard =
      ringChar F * (Nat.card F - 1) * Nat.card F ^ (j / ringChar F) := by
  have hp : 0 < ringChar F := Nat.pos_of_ne_zero (CharP.ringChar_ne_zero_of_finite F)
  rw [ncard_totallyRamifiedOfDegree_wildExponent_eq_laurentSeries F hp dvd_rfl hpj,
    Nat.div_self hp, mul_one, Nat.div_eq_of_lt (Nat.mod_lt j hp), add_zero]

/-- **Worked equal-characteristic check**: for every positive integer `m`, inside a separable
closure of `(ZMod 2)⸨X⸩` there are exactly `2 ^ m` totally ramified quadratic extensions of wild
exponent `2 * m - 1`. -/
theorem ncard_totallyRamifiedOfDegree_two_laurentSeries_zmodTwo {m : ℕ} (hm : 0 < m) :
    {E ∈ totallyRamifiedOfDegree (ZMod 2)⸨X⸩ 2 | E.wildExponent = 2 * m - 1}.ncard = 2 ^ m := by
  have hrc : ringChar (ZMod 2) = 2 := by rw [ZMod.ringChar_zmod_n]
  have hndvd : ¬ ringChar (ZMod 2) ∣ (2 * m - 1) := by
    rw [hrc]
    omega
  have h := ncard_totallyRamifiedOfDegree_ringChar_wildExponent_eq_laurentSeries (ZMod 2) hndvd
  rw [hrc, Nat.card_zmod] at h
  rw [h, show (2 * m - 1) / 2 = m - 1 by omega]
  cases m with
  | zero => omega
  | succ k => simp [pow_succ']

end TauCeti
