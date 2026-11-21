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

Specializes `TauCeti.IsOreAdmissible` and `TauCeti.krasnerCount` to `ℚ_[p]` and `F⸨X⸩` (for a
finite field `F`), deducing `#σ_{ℚ_[p]}(p) = p * (p - 1) ^ 2 + p ^ 2`, `#σ_{ℚ_[3]}(3) = 21`,
`#σ_{ℚ_[2]}(4) = 92`, and wild-exponent stratum counts of degree-`p` extensions over `F⸨X⸩`
(Artin–Schreier when `p = 2`).

## Main results

* `TauCeti.isOreAdmissible_padic_iff`, `TauCeti.krasnerCount_padic_of_mod_eq_zero`,
  `TauCeti.krasnerCount_padic_of_mod_pos`, `TauCeti.ncard_totallyRamifiedOfDegree_padic_eq_sum`:
  Ore admissibility and Krasner's count over `ℚ_[p]`.
* `TauCeti.ncard_totallyRamifiedOfDegree_prime_padic`,
  `TauCeti.ncard_totallyRamifiedOfDegree_three_padicThree`,
  `TauCeti.ncard_totallyRamifiedOfDegree_four_padicTwo`: prime-degree and numerical checks.
* `TauCeti.isOreAdmissible_laurentSeries_iff`, `TauCeti.krasnerCount_laurentSeries`,
  `TauCeti.ncard_totallyRamifiedOfDegree_wildExponent_eq_laurentSeries`,
  `TauCeti.ncard_totallyRamifiedOfDegree_ringChar_wildExponent_eq_laurentSeries`,
  `TauCeti.ncard_totallyRamifiedOfDegree_two_wildExponent_eq_laurentSeries_zmodTwo`:
  equal-characteristic counts.

## References

* M. Krasner, *Nombre des extensions d'un degré donné d'un corps `𝔭`-adique*, CNRS (1966),
  143–169.
* S. Pauli and X.-F. Roblot, *On the computation of all extensions of a `p`-adic field of a given
  degree*, Math. Comp. **70** (2001), 1641–1659, §6.
-/

public section

open ValuativeRel IsNonarchimedeanLocalField
open scoped LaurentSeries

namespace TauCeti

/-! ### Specialization to `ℚ_[p]` -/

/-- **Ore's realizability condition over `ℚ_[p]`**: for `0 < n`, `(n, j)` is Ore-admissible iff
either `n ∣ j` and `j / n = v_p(n)`, or `0 < j % n` and `v_p(j % n) ≤ j / n < v_p(n)`. -/
theorem isOreAdmissible_padic_iff {p : ℕ} [Fact p.Prime] {n j : ℕ} (hn : 0 < n) :
    IsOreAdmissible ℚ_[p] n j ↔
      (j % n = 0 ∧ j / n = padicValNat p n) ∨
        (0 < j % n ∧ padicValNat p (j % n) ≤ j / n ∧ j / n < padicValNat p n) := by
  have hnK : (n : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
  rcases Nat.eq_zero_or_pos (j % n) with hb | hb
  · rw [isOreAdmissible_iff_of_mod_eq_zero hn hb, IsDiscreteValuationRing.addVal_natCast _ n hnK,
      Padic.natCastValuation_eq_padicValNat, Nat.cast_inj]
    exact ⟨fun h ↦ Or.inl ⟨hb, h⟩, fun h ↦ h.elim (·.2) fun ⟨hpos, _⟩ ↦ absurd hb hpos.ne'⟩
  · have hbK : ((j % n : ℕ) : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.2 hb.ne'
    rw [isOreAdmissible_iff_of_mod_pos hn hb, IsDiscreteValuationRing.addVal_natCast _ (j % n) hbK,
      IsDiscreteValuationRing.addVal_natCast _ n hnK, Padic.natCastValuation_eq_padicValNat,
      Padic.natCastValuation_eq_padicValNat, Nat.cast_le, ← Nat.cast_add_one, Nat.cast_le]
    exact ⟨fun ⟨h1, h2⟩ ↦ Or.inr ⟨hb, h1, Nat.lt_of_succ_le h2⟩,
      fun h ↦ h.elim (fun ⟨h0, _⟩ ↦ absurd h0 hb.ne') fun ⟨_, h1, h2⟩ ↦ ⟨h1, Nat.succ_le_of_lt h2⟩⟩

/-- **Krasner's count over `ℚ_[p]` (`n ∣ j`)**: for an Ore-admissible `(n, j)` with `j % n = 0`,
`krasnerCount ℚ_[p] n j = n * p ^ (∑ i ∈ Finset.Icc 1 (j / n), n / p ^ i)`. -/
theorem krasnerCount_padic_of_mod_eq_zero {p : ℕ} [Fact p.Prime] {n j : ℕ}
    (hO : IsOreAdmissible ℚ_[p] n j) (hb : j % n = 0) :
    krasnerCount ℚ_[p] n j = n * p ^ ∑ i ∈ Finset.Icc 1 (j / n), n / p ^ i := by
  rw [krasnerCount_of_mod_eq_zero_of_natCast_ne_zero
      (Padic.natCast_ringChar_residueField_ne_zero p) hO hb,
    Padic.natCard_residueField, Padic.natCastValuation_ringChar_residueField]
  simp only [Padic.ringChar_residueField p, Nat.add_sub_cancel, Nat.div_one]

/-- **Krasner's count over `ℚ_[p]` (`¬ n ∣ j`)**: for an Ore-admissible `(n, j)` with `0 < j % n`,
`krasnerCount ℚ_[p] n j = n * (p - 1) * p ^ (∑_{i=1}^{j/n} n / p ^ i + (j % n) / p ^ (j/n + 1))`.
-/
theorem krasnerCount_padic_of_mod_pos {p : ℕ} [Fact p.Prime] {n j : ℕ}
    (hO : IsOreAdmissible ℚ_[p] n j) (hb : 0 < j % n) :
    krasnerCount ℚ_[p] n j =
      n * (p - 1) * p ^ (∑ i ∈ Finset.Icc 1 (j / n), n / p ^ i + (j % n) / p ^ (j / n + 1)) := by
  rw [krasnerCount_of_mod_pos_of_natCast_ne_zero
      (Padic.natCast_ringChar_residueField_ne_zero p) hO hb,
    Padic.natCard_residueField, Padic.natCastValuation_ringChar_residueField]
  simp only [Padic.ringChar_residueField p, Nat.add_sub_cancel, Nat.div_one]

/-- **Total count of totally ramified degree-`n` extensions of `ℚ_[p]`**:
`#σ_{ℚ_[p]}(n) = ∑_{j = 0}^{n * v_p(n)} krasnerCount ℚ_[p] n j`. -/
theorem ncard_totallyRamifiedOfDegree_padic_eq_sum (p : ℕ) [Fact p.Prime] {n : ℕ} (hn : 0 < n) :
    (totallyRamifiedOfDegree ℚ_[p] n).ncard =
      ∑ j ∈ Finset.range (n * padicValNat p n + 1), krasnerCount ℚ_[p] n j := by
  rw [ncard_totallyRamifiedOfDegree_eq_sum (Nat.cast_ne_zero.2 hn.ne'),
    Padic.natCastValuation_eq_padicValNat]

/-- **Totally ramified extensions of `ℚ_[p]` of prime degree `p`**: inside a separable closure of
`ℚ_[p]`, there are `p * (p - 1) ^ 2 + p ^ 2` totally ramified extensions of degree `p`. -/
theorem ncard_totallyRamifiedOfDegree_prime_padic (p : ℕ) [Fact p.Prime] :
    (totallyRamifiedOfDegree ℚ_[p] p).ncard = p * (p - 1) ^ 2 + p ^ 2 := by
  have hp : p.Prime := Fact.out
  have hv : padicValNat p p = 1 := by rw [Nat.padicValNat_def, Nat.multiplicity_self hp.one_lt]
  have h0 : krasnerCount ℚ_[p] p 0 = 0 := krasnerCount_of_not_isOreAdmissible fun hO ↦ by
    rcases (isOreAdmissible_padic_iff hp.pos).1 hO with ⟨_, hdiv⟩ | ⟨hpos, _⟩
    · rw [Nat.zero_div, hv] at hdiv; omega
    · simp at hpos
  have hp_top : krasnerCount ℚ_[p] p p = p ^ 2 := by
    rw [krasnerCount_padic_of_mod_eq_zero ((isOreAdmissible_padic_iff hp.pos).2
      (Or.inl ⟨Nat.mod_self p, by rw [Nat.div_self hp.pos, hv]⟩)) (Nat.mod_self p),
      Nat.div_self hp.pos]
    simp only [Finset.Icc_self, Finset.sum_singleton, pow_one, Nat.div_self hp.pos, sq]
  have hmid : ∑ k ∈ Finset.range (p - 1), krasnerCount ℚ_[p] p (k + 1) = p * (p - 1) ^ 2 := by
    have hterm : ∀ k ∈ Finset.range (p - 1), krasnerCount ℚ_[p] p (k + 1) = p * (p - 1) := by
      intro k hk
      have hlt : k + 1 < p := by rw [Finset.mem_range] at hk; omega
      have hmod : (k + 1) % p = k + 1 := Nat.mod_eq_of_lt hlt
      have hdiv : (k + 1) / p = 0 := Nat.div_eq_of_lt hlt
      have hvk : padicValNat p (k + 1) = 0 := by
        rw [Nat.padicValNat_def]
        exact multiplicity_eq_zero_of_not_dvd (Nat.not_dvd_of_pos_of_lt (Nat.succ_pos k) hlt)
      have hO : IsOreAdmissible ℚ_[p] p (k + 1) := (isOreAdmissible_padic_iff hp.pos).2
        (Or.inr ⟨by omega, by rw [hmod, hvk, hdiv], by rw [hdiv, hv]; omega⟩)
      rw [krasnerCount_padic_of_mod_pos hO (by omega), hdiv, hmod, pow_one, Nat.div_eq_of_lt hlt]
      simp
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, Finset.card_range, smul_eq_mul]; ring
  rw [ncard_totallyRamifiedOfDegree_padic_eq_sum p hp.pos, hv, mul_one, Finset.sum_range_succ,
    show ∑ j ∈ Finset.range p, krasnerCount ℚ_[p] p j =
        ∑ k ∈ Finset.range (p - 1), krasnerCount ℚ_[p] p (k + 1) + krasnerCount ℚ_[p] p 0 by
      rw [← Finset.sum_range_succ', Nat.sub_add_cancel hp.pos],
    h0, add_zero, hmid, hp_top]

/-! ### Worked numerical checks over `ℚ_[3]` and `ℚ_[2]` -/

/-- Inside a separable closure of `ℚ_[3]`, there are exactly `21` totally ramified cubic
extensions (`6` of wild exponent `1`, `6` of wild exponent `2`, and `9` of wild exponent `3`). -/
theorem ncard_totallyRamifiedOfDegree_three_padicThree :
    (totallyRamifiedOfDegree ℚ_[3] 3).ncard = 21 := by
  rw [ncard_totallyRamifiedOfDegree_prime_padic 3]; norm_num

/-- Inside a separable closure of `ℚ_[2]`, there are exactly `92` totally ramified quartic
extensions (`4 + 8 + 16 + 16 + 16 + 32 = 92` across wild exponents `1, 3, 5, 6, 7, 8`). -/
theorem ncard_totallyRamifiedOfDegree_four_padicTwo :
    (totallyRamifiedOfDegree ℚ_[2] 4).ncard = 92 := by
  have hv4 : padicValNat 2 4 = 2 := by
    rw [Nat.padicValNat_def, show (4 : ℕ) = 2 ^ 2 by rfl, Nat.multiplicity_prime_pow]
  have hv2 : padicValNat 2 2 = 1 := by rw [Nat.padicValNat_def, Nat.multiplicity_self (by decide)]
  have hnd (m : ℕ) (h : ¬ 2 ∣ m) : padicValNat 2 m = 0 := by
    rw [Nat.padicValNat_def]; exact multiplicity_eq_zero_of_not_dvd h
  have hv1 := hnd 1 (by decide); have hv3 := hnd 3 (by decide)
  have hpos (j : ℕ) (hb : 0 < j % 4) (h1 : padicValNat 2 (j % 4) ≤ j / 4) (h2 : j / 4 < 2) :
      krasnerCount ℚ_[2] 4 j =
        4 * 2 ^ (∑ i ∈ Finset.Icc 1 (j / 4), 4 / 2 ^ i + (j % 4) / 2 ^ (j / 4 + 1)) :=
    krasnerCount_padic_of_mod_pos
      ((isOreAdmissible_padic_iff (by norm_num)).2 (Or.inr ⟨hb, h1, by omega⟩)) hb
  have hzero (j : ℕ) (h : ¬((j % 4 = 0 ∧ j / 4 = 2) ∨
      (0 < j % 4 ∧ padicValNat 2 (j % 4) ≤ j / 4 ∧ j / 4 < 2))) : krasnerCount ℚ_[2] 4 j = 0 :=
    krasnerCount_of_not_isOreAdmissible (by rwa [isOreAdmissible_padic_iff (by norm_num), hv4])
  have hk8 : krasnerCount ℚ_[2] 4 8 = 32 := by
    rw [krasnerCount_padic_of_mod_eq_zero
      ((isOreAdmissible_padic_iff (by norm_num)).2 (Or.inl ⟨by norm_num, by simp [hv4]⟩))
      (by norm_num), show 8 / 4 = 2 by rfl, show Finset.Icc 1 2 = {1, 2} by decide]; norm_num
  rw [ncard_totallyRamifiedOfDegree_padic_eq_sum 2 (by norm_num), hv4]
  simp only [show 4 * 2 + 1 = 9 by rfl, Finset.sum_range_succ, Finset.range_zero,
    Finset.sum_empty, zero_add]
  rw [hzero 0 (by simp), hzero 2 (by simp [hv2]), hzero 4 (by simp), hk8,
    hpos 1 (by norm_num) (by simp [hv1]) (by norm_num), hpos 3 (by norm_num) (by simp [hv3])
    (by norm_num), hpos 5 (by norm_num) (by simp [hv1]) (by norm_num), hpos 6 (by norm_num)
    (by simp [hv2]) (by norm_num), hpos 7 (by norm_num) (by simp [hv3]) (by norm_num)]; norm_num

/-! ### Specialization to `F⸨X⸩` -/

/-- **Ore's realizability condition over `F⸨X⸩`**: for a finite field `F` and `0 < n` divisible by
`ringChar F`, `(n, j)` is Ore-admissible over `F⸨X⸩` iff `¬ ringChar F ∣ j`. -/
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
  rw [krasnerCount_of_natCast_ringChar_eq_zero hp hn (by rwa [LaurentSeries.ringChar_residueField])
    (by rwa [LaurentSeries.ringChar_residueField]),
    LaurentSeries.natCard_residueField, LaurentSeries.ringChar_residueField]

/-- **Discriminant-refined count over `F⸨X⸩`**: for `0 < n` with `ringChar F ∣ n` and
`¬ ringChar F ∣ j`, the wild-exponent stratum `c(E) = j` has cardinality
`n * (q - 1) * q ^ ((j / n) * (n / p) + (j % n) / p)`. -/
theorem ncard_totallyRamifiedOfDegree_wildExponent_eq_laurentSeries (F : Type*) [Field F] [Finite F]
    {n j : ℕ} (hn : 0 < n) (hpn : ringChar F ∣ n) (hpj : ¬ ringChar F ∣ j) :
    {E ∈ totallyRamifiedOfDegree F⸨X⸩ n | E.wildExponent = j}.ncard =
      n * (Nat.card F - 1) * Nat.card F ^ ((j / n) * (n / ringChar F) + (j % n) / ringChar F) := by
  rw [ncard_totallyRamifiedOfDegree_wildExponent_eq, krasnerCount_laurentSeries F hn hpn hpj]

/-- **Wild-exponent stratum count of degree-`p` extensions over `F⸨X⸩`** (Artin–Schreier when
`p = 2`): for a finite field `F` of characteristic `p`, every wild exponent `j` prime to `p` is
realized by `p * (q - 1) * q ^ (j / p)` degree-`p` totally ramified extensions of `F⸨X⸩`. -/
theorem ncard_totallyRamifiedOfDegree_ringChar_wildExponent_eq_laurentSeries (F : Type*)
    [Field F] [Finite F] {j : ℕ} (hpj : ¬ ringChar F ∣ j) :
    {E ∈ totallyRamifiedOfDegree F⸨X⸩ (ringChar F) | E.wildExponent = j}.ncard =
      ringChar F * (Nat.card F - 1) * Nat.card F ^ (j / ringChar F) := by
  have hp : 0 < ringChar F := Nat.pos_of_ne_zero (CharP.ringChar_ne_zero_of_finite F)
  rw [ncard_totallyRamifiedOfDegree_wildExponent_eq_laurentSeries F hp dvd_rfl hpj,
    Nat.div_self hp, mul_one, Nat.div_eq_of_lt (Nat.mod_lt j hp), add_zero]

/-- **Worked equal-characteristic check**: for `0 < m`, inside a separable closure of
`(ZMod 2)⸨X⸩` there are `2 ^ m` totally ramified quadratic extensions of wild exponent `2 * m - 1`.
-/
theorem ncard_totallyRamifiedOfDegree_two_wildExponent_eq_laurentSeries_zmodTwo {m : ℕ}
    (hm : 0 < m) :
    {E ∈ totallyRamifiedOfDegree (ZMod 2)⸨X⸩ 2 | E.wildExponent = 2 * m - 1}.ncard = 2 ^ m := by
  have h := ncard_totallyRamifiedOfDegree_ringChar_wildExponent_eq_laurentSeries (ZMod 2)
    (j := 2 * m - 1) (by rw [ZMod.ringChar_zmod_n]; omega)
  rw [ZMod.ringChar_zmod_n, Nat.card_zmod, show (2 * m - 1) / 2 = m - 1 by omega] at h
  rw [h]; rcases m with _ | k <;> [omega; simp [pow_succ']]

end TauCeti
