/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.MassFormula.Krasner.Basic
public import TauCeti.NumberTheory.LocalField.Padic
import TauCeti.Data.Nat.Factorization.Basic

/-!
# Closed-form Krasner counts over `ℚ_[p]`

Over `ℚ_[p]`, every positive integer has finite `p`-adic valuation `padicValNat p h`. Ore's
admissibility condition reduces to `min(v_p(j % n) * n, v_p(n) * n) ≤ j ≤ v_p(n) * n`
(`TauCeti.isOreAdmissible_padic_iff`), and the sum of Ore coefficient depths
`∑_{1 ≤ h < n} oreCoefficientDepth ℚ_[p] n j h` can be evaluated in closed form by double counting
prime powers `p ^ i` dividing `1, …, n - 1` via `Nat.Ico_filter_not_dvd_card_add_div_of_dvd` and
`Nat.Ico_filter_not_dvd_card_add_div_of_not_dvd`. Substituting this
closed form into `TauCeti.ncard_mem_totallyRamifiedOfDegree_wildExponent_eq_mul_pow` yields Pauli
and Roblot's closed-form `ℕ` expression for `#{E ∈ σ_{ℚ_[p]}(n) | E.wildExponent = j}` and for
`#σ_{ℚ_[p]}(n)` — matching `#σ_{ℚ_[2]}(2) = 2 + 4 = 6`
(`TauCeti.encard_totallyRamifiedOfDegree_two_padicTwo`) and giving `#σ_{ℚ_[3]}(3) = 21` and
`#σ_{ℚ_[2]}(4) = 92`.

## Main definitions

* `TauCeti.krasnerCountPadic p n j`: executable `ℕ` closed form for the number of totally ramified
  degree-`n` extensions of `ℚ_[p]` with wild exponent `j`.

## Main results

* `TauCeti.isOreAdmissible_padic_iff`: Ore's inequality characterizing admissible wild exponents
  over `ℚ_[p]` (Pauli–Roblot, Proposition 3.1).
* `TauCeti.sum_oreCoefficientDepth_padic_of_mod_eq_zero`,
  `TauCeti.sum_oreCoefficientDepth_padic_of_mod_pos`: closed-form identities for the sum of Ore
  coefficient depths over `ℚ_[p]`.
* `TauCeti.ncard_mem_totallyRamifiedOfDegree_wildExponent_eq_eq_krasnerCountPadic`: closed-form `ℕ`
  count of totally ramified degree-`n` extensions of `ℚ_[p]` of wild exponent `j` (Pauli–Roblot,
  Theorem 6.1).
* `TauCeti.ncard_totallyRamifiedOfDegree_padic`: total count `#σ_{ℚ_[p]}(n)` as a finite sum of
  `krasnerCountPadic p n j` over `0 ≤ j ≤ n * v_p(n)`.
* `TauCeti.ncard_totallyRamifiedOfDegree_three_padicThree`,
  `TauCeti.ncard_totallyRamifiedOfDegree_four_padicTwo`: `#σ_{ℚ_[3]}(3) = 21` and
  `#σ_{ℚ_[2]}(4) = 92`.

## References

* M. Krasner, *Nombre des extensions d'un degré donné d'un corps p-adique*, Colloques
  Internationaux du CNRS **143**, Paris, 1966, 143–169.
* S. Pauli and X.-F. Roblot, *On the computation of all extensions of a p-adic field of a given
  degree*, Math. Comp. **70** (2001), 1641–1659, Proposition 3.1, Theorem 6.1, and Table 1.
-/

public section

open ValuativeRel IsDiscreteValuationRing

namespace TauCeti

/-- **Krasner's count over `ℚ_[p]`** (Pauli–Roblot, Theorem 6.1): executable `ℕ` formula for the
number of totally ramified degree-`n` extensions of `ℚ_[p]` with wild exponent `j`, returning `0`
unless `0 < n` and `j` satisfies Ore's inequality (`TauCeti.isOreAdmissible_padic_iff`). -/
def krasnerCountPadic (p n j : ℕ) : ℕ :=
  if 0 < n ∧
      (if j % n = 0 then padicValNat p n * n
        else min (padicValNat p (j % n) * n) (padicValNat p n * n)) ≤ j ∧
      j ≤ padicValNat p n * n then
    if j % n = 0 then n * p ^ (∑ i ∈ Finset.Icc 1 (j / n), n / p ^ i)
    else n * (p - 1) *
      p ^ (∑ i ∈ Finset.Icc 1 (j / n), n / p ^ i + (j % n) / p ^ (j / n + 1))
  else 0

noncomputable section

/-- **Ore's inequality over `ℚ_[p]`** (Pauli–Roblot, Proposition 3.1): a wild exponent `j` is
Ore-admissible for degree `n` over `ℚ_[p]` if and only if `0 < n` and
`min(v_p(j % n) * n, v_p(n) * n) ≤ j ≤ v_p(n) * n`, with `v_p(0)` read as `∞` so that `n ∣ j`
requires `j = v_p(n) * n`. -/
theorem isOreAdmissible_padic_iff (p : ℕ) [Fact p.Prime] {n j : ℕ} :
    IsOreAdmissible ℚ_[p] n j ↔
      0 < n ∧
        (if j % n = 0 then padicValNat p n * n
          else min (padicValNat p (j % n) * n) (padicValNat p n * n)) ≤ j ∧
          j ≤ padicValNat p n * n := by
  rcases n.eq_zero_or_pos with rfl | hn
  · simp
  have hn0 : (n : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hvn : addVal 𝒪[ℚ_[p]] (n : 𝒪[ℚ_[p]]) = (padicValNat p n : ℕ∞) := by
    rw [TauCeti.IsDiscreteValuationRing.addVal_natCast ℚ_[p] n hn0,
      _root_.Padic.natCastValuation_eq_padicValNat]
  have hdiv := Nat.div_add_mod j n
  have hlt := Nat.mod_lt j hn
  rcases Nat.eq_zero_or_pos (j % n) with hmod | hmod
  · rw [isOreAdmissible_iff_of_mod_eq_zero hmod, ite_eq_left hmod, hvn]
    simp only [hn, true_and, ENat.natCast_inj]
    rw [hmod, add_zero, Nat.mul_comm n (j / n)] at hdiv
    rw [← hdiv, ← le_antisymm_iff, Nat.mul_div_cancel _ hn, Nat.mul_left_inj hn.ne', eq_comm]
  · have hb0 : ((j % n : ℕ) : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr hmod.ne'
    have hvb : addVal 𝒪[ℚ_[p]] ((j % n : ℕ) : 𝒪[ℚ_[p]]) = (padicValNat p (j % n) : ℕ∞) := by
      rw [TauCeti.IsDiscreteValuationRing.addVal_natCast ℚ_[p] (j % n) hb0,
        _root_.Padic.natCastValuation_eq_padicValNat]
    rw [isOreAdmissible_iff_of_mod_pos hmod, ite_eq_right hmod.ne', hvn, hvb]
    simp only [hn, true_and]
    norm_cast
    rw [Nat.mul_comm n (j / n)] at hdiv
    refine ⟨fun ⟨h1, h2⟩ ↦ ?_, fun ⟨h1, h2⟩ ↦ ?_⟩
    · have hm1 := Nat.mul_le_mul_right n h1
      have hm2 := Nat.mul_le_mul_right n h2
      rw [Nat.add_one_mul] at hm2
      exact ⟨(min_le_left _ _).trans (by omega), by omega⟩
    · have hj_ne : j ≠ padicValNat p n * n := fun heq ↦ hmod.ne' (by rw [heq, Nat.mul_mod_left])
      have hdiv_lt : j / n + 1 ≤ padicValNat p n :=
        Nat.lt_of_mul_lt_mul_right (by omega : (j / n) * n < padicValNat p n * n)
      rcases min_le_iff.mp h1 with hmin | hmin
      · have hm_lt : padicValNat p (j % n) * n < (j / n + 1) * n := by rw [Nat.add_one_mul]; omega
        exact ⟨Nat.lt_succ_iff.mp (Nat.lt_of_mul_lt_mul_right hm_lt), hdiv_lt⟩
      · exact absurd (le_antisymm h2 hmin) hj_ne

/-- Double-counting evaluation of the base Ore depth sum `∑_{1 ≤ h < n} (j / n - v_p(h))` for an
Ore-admissible pair `(n, j)` over `ℚ_[p]`, using `Nat.Ico_filter_not_dvd_card_add_div_of_dvd`. -/
private theorem sum_Ico_div_sub_padicValNat_of_isOreAdmissible (p : ℕ) [Fact p.Prime] {n j : ℕ}
    (hadm : IsOreAdmissible ℚ_[p] n j) :
    (∑ h ∈ Finset.Ico 1 n, (j / n - padicValNat p h)) +
      ∑ i ∈ Finset.Icc 1 (j / n), n / p ^ i = (j / n) * n := by
  have hn := hadm.pos
  have ha_le : j / n ≤ padicValNat p n := by
    have h := hadm.div_le_addVal
    rw [TauCeti.IsDiscreteValuationRing.addVal_natCast ℚ_[p] n (Nat.cast_ne_zero.mpr hn.ne'),
      _root_.Padic.natCastValuation_eq_padicValNat] at h
    exact_mod_cast h
  have hterm : ∀ h ∈ Finset.Ico 1 n,
      j / n - padicValNat p h = ∑ i ∈ Finset.Icc 1 (j / n), if ¬ p ^ i ∣ h then 1 else 0 := by
    intro h hh
    rw [Finset.mem_Ico] at hh
    rw [Finset.sum_boole, Nat.cast_id]
    have hfilt : {i ∈ Finset.Icc 1 (j / n) | ¬ p ^ i ∣ h} =
        Finset.Icc (padicValNat p h + 1) (j / n) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_Icc, Nat.padicValNat_def,
        multiplicity_dvd_iff_le (by omega : h ≠ 0)]
      omega
    rw [hfilt, Nat.card_Icc]
    omega
  rw [Finset.sum_congr rfl hterm, Finset.sum_comm, ← Finset.sum_add_distrib]
  have hinner : ∀ i ∈ Finset.Icc 1 (j / n),
      (∑ h ∈ Finset.Ico 1 n, if ¬ p ^ i ∣ h then 1 else 0) + n / p ^ i = n := by
    intro i hi
    rw [Finset.mem_Icc] at hi
    rw [Nat.padicValNat_def] at ha_le
    have hdvd : p ^ i ∣ n := (multiplicity_dvd_iff_le hn.ne').mpr (hi.2.trans ha_le)
    rw [Finset.sum_boole, Nat.cast_id]
    exact Nat.Ico_filter_not_dvd_card_add_div_of_dvd hdvd
  rw [Finset.sum_congr rfl hinner, Finset.sum_const, Nat.card_Icc, smul_eq_mul,
    Nat.add_sub_cancel]

/-- **Sum of Ore coefficient depths over `ℚ_[p]` when `n ∣ j`**: for an Ore-admissible pair `(n, j)`
with `j % n = 0`, `(∑_{1 ≤ h < n} ν_h) + ∑_{1 ≤ i ≤ j / n} n / p ^ i = n + j - 1`. -/
theorem sum_oreCoefficientDepth_padic_of_mod_eq_zero (p : ℕ) [Fact p.Prime] {n j : ℕ}
    (hadm : IsOreAdmissible ℚ_[p] n j) (hmod : j % n = 0) :
    (∑ h ∈ Finset.Ico 1 n, oreCoefficientDepth ℚ_[p] n j h) +
      ∑ i ∈ Finset.Icc 1 (j / n), n / p ^ i = n + j - 1 := by
  have hn := hadm.pos
  have hdepth : ∀ h ∈ Finset.Ico 1 n,
      oreCoefficientDepth ℚ_[p] n j h = 1 + (j / n - padicValNat p h) := by
    intro h hh
    rw [Finset.mem_Ico] at hh
    rw [oreCoefficientDepth_of_natCast_ne_zero ℚ_[p] n j (Nat.cast_ne_zero.mpr (by omega)),
      _root_.Padic.natCastValuation_eq_padicValNat, hmod]
    simp only [not_lt_zero, ↓reduceIte, add_zero]
    omega
  have hj : (j / n) * n = j := by
    have := Nat.div_add_mod j n
    rwa [hmod, add_zero, Nat.mul_comm] at this
  rw [Finset.sum_congr rfl hdepth, Finset.sum_add_distrib, Finset.sum_const, Nat.card_Ico,
    smul_eq_mul, mul_one, add_assoc, sum_Ico_div_sub_padicValNat_of_isOreAdmissible p hadm, hj]
  omega

/-- **Sum of Ore coefficient depths over `ℚ_[p]` when `0 < j % n`**: for an Ore-admissible pair
`(n, j)` with `0 < j % n`,
`(∑_{1 ≤ h < n} ν_h) + (∑_{1 ≤ i ≤ j / n} n / p ^ i + (j % n) / p ^ (j / n + 1)) = n + j - 2`. -/
theorem sum_oreCoefficientDepth_padic_of_mod_pos (p : ℕ) [Fact p.Prime] {n j : ℕ}
    (hadm : IsOreAdmissible ℚ_[p] n j) (hmod : 0 < j % n) :
    (∑ h ∈ Finset.Ico 1 n, oreCoefficientDepth ℚ_[p] n j h) +
      (∑ i ∈ Finset.Icc 1 (j / n), n / p ^ i + (j % n) / p ^ (j / n + 1)) = n + j - 2 := by
  have hn := hadm.pos
  obtain ⟨hvb, -⟩ := (isOreAdmissible_iff_of_mod_pos hmod).mp hadm |>.2
  rw [TauCeti.IsDiscreteValuationRing.addVal_natCast ℚ_[p] (j % n)
    (Nat.cast_ne_zero.mpr hmod.ne'), _root_.Padic.natCastValuation_eq_padicValNat] at hvb
  have hvb_le : padicValNat p (j % n) ≤ j / n := by exact_mod_cast hvb
  have hlt_b : j % n < n := Nat.mod_lt j hn
  have hdepth : ∀ h ∈ Finset.Ico 1 n,
      oreCoefficientDepth ℚ_[p] n j h =
        1 + (j / n - padicValNat p h) +
          if h < j % n then (if ¬ p ^ (j / n + 1) ∣ h then 1 else 0) else 0 := by
    intro h hh
    rw [Finset.mem_Ico] at hh
    rw [oreCoefficientDepth_of_natCast_ne_zero ℚ_[p] n j (Nat.cast_ne_zero.mpr (by omega)),
      _root_.Padic.natCastValuation_eq_padicValNat]
    by_cases hlt : h < j % n
    · rw [ite_eq_left hlt, ite_eq_left hlt]
      have hdvd : p ^ (j / n + 1) ∣ h ↔ j / n + 1 ≤ padicValNat p h := by
        rw [Nat.padicValNat_def, multiplicity_dvd_iff_le (by omega)]
      by_cases hle : j / n + 1 ≤ padicValNat p h
      · rw [ite_eq_right (not_not.mpr (hdvd.mpr hle))]; omega
      · rw [ite_eq_left (mt hdvd.mp hle)]; omega
    · rw [ite_eq_right hlt, ite_eq_right hlt]; omega
  have hndvd : ¬ p ^ (j / n + 1) ∣ j % n := by
    rw [Nat.padicValNat_def] at hvb_le
    rw [multiplicity_dvd_iff_le hmod.ne']
    omega
  have hextra :
      (∑ h ∈ Finset.Ico 1 n,
        if h < j % n then (if ¬ p ^ (j / n + 1) ∣ h then 1 else 0) else 0) +
        (j % n) / p ^ (j / n + 1) = j % n - 1 := by
    rw [← Finset.sum_filter, Finset.Ico_filter_lt_of_le_right hlt_b.le, Finset.sum_boole,
      Nat.cast_id]
    exact Nat.Ico_filter_not_dvd_card_add_div_of_not_dvd hndvd
  have := Nat.div_add_mod j n
  have hbase := sum_Ico_div_sub_padicValNat_of_isOreAdmissible p hadm
  rw [Nat.mul_comm (j / n) n] at hbase
  rw [Finset.sum_congr rfl hdepth, Finset.sum_add_distrib, Finset.sum_add_distrib,
    Finset.sum_const, Nat.card_Ico, smul_eq_mul, mul_one]
  omega

/-- **Krasner's count over `ℚ_[p]`, closed form** (Pauli–Roblot, Theorem 6.1): for all `n` and `j`,
`{E ∈ σ_{ℚ_[p]}(n) | E.wildExponent = j}.ncard` equals `krasnerCountPadic p n j`. -/
theorem ncard_mem_totallyRamifiedOfDegree_wildExponent_eq_eq_krasnerCountPadic (p : ℕ)
    [Fact p.Prime] (n j : ℕ) :
    {E ∈ totallyRamifiedOfDegree ℚ_[p] n | E.wildExponent = j}.ncard =
      krasnerCountPadic p n j := by
  rw [krasnerCountPadic]
  by_cases hadm : IsOreAdmissible ℚ_[p] n j
  · rw [ite_eq_left ((isOreAdmissible_padic_iff p).mp hadm)]
    have hn := hadm.pos
    have hp_pos : 0 < p := (Fact.out : p.Prime).pos
    have hnat := ncard_mem_totallyRamifiedOfDegree_wildExponent_eq_mul_pow hadm
    rw [_root_.Padic.natCard_residueField p] at hnat
    set S := ∑ h ∈ Finset.Ico 1 n, oreCoefficientDepth ℚ_[p] n j h
    rcases Nat.eq_zero_or_pos (j % n) with hmod | hmod
    · rw [ite_eq_left hmod] at hnat ⊢
      set E := ∑ i ∈ Finset.Icc 1 (j / n), n / p ^ i
      have hSE : S + E = n + j - 1 := sum_oreCoefficientDepth_padic_of_mod_eq_zero p hadm hmod
      have hrhs : n * p ^ (n + j) * p = (n * p ^ E) * p ^ (2 + S) := by
        rw [mul_assoc, ← pow_succ, (by omega : (n + j) + 1 = E + (2 + S)), pow_add, ← mul_assoc]
      exact Nat.eq_of_mul_eq_mul_right (pow_pos hp_pos (2 + S)) (hnat.trans hrhs)
    · rw [ite_eq_right hmod.ne'] at hnat ⊢
      set E := ∑ i ∈ Finset.Icc 1 (j / n), n / p ^ i + (j % n) / p ^ (j / n + 1)
      have hSE : S + E = n + j - 2 := sum_oreCoefficientDepth_padic_of_mod_pos p hadm hmod
      have := Nat.mod_lt j hn
      have hrhs : n * p ^ (n + j) * (p - 1) = (n * (p - 1) * p ^ E) * p ^ (2 + S) := by
        rw [(by omega : n + j = E + (2 + S)), pow_add]; ring
      exact Nat.eq_of_mul_eq_mul_right (pow_pos hp_pos (2 + S)) (hnat.trans hrhs)
  · rw [setOf_mem_totallyRamifiedOfDegree_wildExponent_eq_eq_empty_iff.mpr hadm,
      Set.ncard_empty, ite_eq_right fun h ↦ hadm ((isOreAdmissible_padic_iff p).mpr h)]

/-- **Total number of totally ramified degree-`n` extensions of `ℚ_[p]`** as a finite sum of
`krasnerCountPadic p n j` over `0 ≤ j ≤ n * v_p(n)`. -/
theorem ncard_totallyRamifiedOfDegree_padic (p : ℕ) [Fact p.Prime] {n : ℕ} (hn : 0 < n) :
    (totallyRamifiedOfDegree ℚ_[p] n).ncard =
      ∑ j ∈ Finset.range (n * padicValNat p n + 1), krasnerCountPadic p n j := by
  rw [ncard_totallyRamifiedOfDegree_eq_sum (Nat.cast_ne_zero.mpr hn.ne'),
    _root_.Padic.natCastValuation_eq_padicValNat]
  exact Finset.sum_congr rfl fun j _ ↦
    ncard_mem_totallyRamifiedOfDegree_wildExponent_eq_eq_krasnerCountPadic p n j

/-- `ℚ_[3]` has `21` totally ramified cubic extensions inside `SeparableClosure ℚ_[3]` (`6` of wild
exponent `1`, `6` of wild exponent `2`, and `9` of wild exponent `3`). -/
theorem ncard_totallyRamifiedOfDegree_three_padicThree :
    (totallyRamifiedOfDegree ℚ_[3] 3).ncard = 21 := by
  rw [ncard_totallyRamifiedOfDegree_padic 3 (by decide)]
  simp only [krasnerCountPadic, Nat.padicValNat_def, Nat.multiplicity_self (by decide : 1 < 3),
    Finset.sum_range_succ, Finset.sum_range_zero,
    multiplicity_eq_zero_of_not_dvd (by decide : ¬ 3 ∣ 1),
    multiplicity_eq_zero_of_not_dvd (by decide : ¬ 3 ∣ 2)]
  norm_num

/-- `ℚ_[2]` has `92` totally ramified quartic extensions inside `SeparableClosure ℚ_[2]`. -/
theorem ncard_totallyRamifiedOfDegree_four_padicTwo :
    (totallyRamifiedOfDegree ℚ_[2] 4).ncard = 92 := by
  have hm4 : multiplicity 2 4 = 2 :=
    multiplicity_eq_of_dvd_of_not_dvd (by decide) (by decide)
  have hIcc2 : (∑ i ∈ Finset.Icc 1 2, 4 / 2 ^ i) = 3 := by
    rw [Finset.sum_Icc_succ_top (by decide : 1 ≤ 2), Finset.Icc_self]
    norm_num
  rw [ncard_totallyRamifiedOfDegree_padic 2 (by decide)]
  simp only [krasnerCountPadic, Nat.padicValNat_def, hm4, Finset.sum_range_succ,
    Finset.sum_range_zero, multiplicity_eq_zero_of_not_dvd (by decide : ¬ 2 ∣ 1),
    Nat.multiplicity_self (by decide : 1 < 2),
    multiplicity_eq_zero_of_not_dvd (by decide : ¬ 2 ∣ 3), hIcc2]
  norm_num

end

end TauCeti
