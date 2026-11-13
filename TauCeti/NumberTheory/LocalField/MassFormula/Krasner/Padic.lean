/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.MassFormula.Krasner.Basic
import Mathlib.Data.Nat.Factorization.Basic

/-!
# Closed-form Krasner counts over `ℚ_[p]`

Over `ℚ_[p]`, every positive integer has finite `p`-adic valuation `padicValNat p h`, so the sum of
Ore coefficient depths `∑_{1 ≤ h < n} oreCoefficientDepth ℚ_[p] n j h` can be evaluated in closed
form by double counting prime powers `p ^ i` dividing `1, …, n - 1` via
`Nat.Ioc_filter_dvd_card_eq_div`. Substituting this closed form into
`TauCeti.ncard_mem_totallyRamifiedOfDegree_wildExponent_eq_mul_pow` yields Pauli and Roblot's
closed-form `ℕ` expression for `#{E ∈ σ_{ℚ_[p]}(n) | E.wildExponent = j}` and for `#σ_{ℚ_[p]}(n)`,
including `#σ_{ℚ_[2]}(2) = 6`, `#σ_{ℚ_[3]}(3) = 21`, and `#σ_{ℚ_[2]}(4) = 92`.

## Main results

* `TauCeti.sum_oreCoefficientDepth_padic_of_mod_eq_zero`,
  `TauCeti.sum_oreCoefficientDepth_padic_of_mod_pos`: closed-form identities for the sum of Ore
  coefficient depths over `ℚ_[p]`.
* `TauCeti.ncard_mem_totallyRamifiedOfDegree_wildExponent_eq_padic`: closed-form `ℕ` count of
  totally ramified degree-`n` extensions of `ℚ_[p]` of wild exponent `j` (Pauli–Roblot, Theorem
  6.1).
* `TauCeti.ncard_totallyRamifiedOfDegree_padic`: total count `#σ_{ℚ_[p]}(n)` as a finite sum over
  `0 ≤ j ≤ n * padicValNat p n`.
* `TauCeti.ncard_totallyRamifiedOfDegree_two_padicTwo`,
  `TauCeti.ncard_totallyRamifiedOfDegree_three_padicThree`,
  `TauCeti.ncard_totallyRamifiedOfDegree_four_padicTwo`: `#σ_{ℚ_[2]}(2) = 6`,
  `#σ_{ℚ_[3]}(3) = 21`, and `#σ_{ℚ_[2]}(4) = 92`.

## References

* M. Krasner, *Nombre des extensions d'un degré donné d'un corps p-adique*, Colloques
  Internationaux du CNRS **143**, Paris, 1966, 143–169.
* S. Pauli and X.-F. Roblot, *On the computation of all extensions of a p-adic field of a given
  degree*, Math. Comp. **70** (2001), 1641–1659, Theorem 6.1 and Table 1.
-/

public section
noncomputable section

namespace TauCeti

/-- Double-counting evaluation of the base Ore depth sum `∑_{1 ≤ h < n} (j / n - v_p(h))` for an
Ore-admissible pair `(n, j)` over `ℚ_[p]`, using `Nat.Ioc_filter_dvd_card_eq_div`. -/
private theorem sum_Ico_div_sub_padicValNat_of_isOreAdmissible (p : ℕ) [Fact p.Prime] {n j : ℕ}
    (hadm : IsOreAdmissible ℚ_[p] n j) :
    (∑ h ∈ Finset.Ico 1 n, (j / n - padicValNat p h)) +
      ∑ i ∈ Finset.Icc 1 (j / n), n / p ^ i = (j / n) * n := by
  have hn := hadm.pos
  have hp_pos : 0 < p := (Fact.out : p.Prime).pos
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
    have hd_pos : 0 < p ^ i := pow_pos hp_pos i
    rw [Nat.padicValNat_def] at ha_le
    obtain ⟨k, hk⟩ := (multiplicity_dvd_iff_le hn.ne').mpr (hi.2.trans ha_le)
    have hk_pos : 0 < k := Nat.pos_of_ne_zero fun hk0 ↦ by simp [hk0] at hk; omega
    have hIco : Finset.Ico 1 n = Finset.Ioc 0 (n - 1) := by
      ext h; simp only [Finset.mem_Ico, Finset.mem_Ioc]; omega
    have hpart := Finset.card_filter_add_card_filter_not (s := Finset.Ioc 0 (n - 1))
      (fun h ↦ p ^ i ∣ h)
    rw [Nat.Ioc_filter_dvd_card_eq_div, Nat.card_Ioc, Nat.sub_zero] at hpart
    have hmul : p ^ i * (k - 1) + p ^ i = n := by
      rw [← Nat.mul_add_one, Nat.sub_add_cancel hk_pos, hk]
    have hdecomp : (p ^ i - 1) + p ^ i * (k - 1) = n - 1 := by omega
    have hdiv_sub : (n - 1) / p ^ i = k - 1 := by
      rw [← hdecomp, Nat.add_mul_div_left _ _ hd_pos, Nat.div_eq_of_lt (by omega), zero_add]
    have hdiv_n : n / p ^ i = k := by rw [hk, Nat.mul_div_right _ hd_pos]
    rw [hdiv_sub] at hpart
    rw [hIco, Finset.sum_boole, Nat.cast_id, hdiv_n]
    omega
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

/-- Sub-remainder prime-power count `∑_{1 ≤ h < b} [¬ p ^ (a + 1) ∣ h] + b / p ^ (a + 1) = b - 1`
when `v_p(b) ≤ a`. -/
private theorem sum_Ico_lt_mod_not_dvd_add_div (p : ℕ) [Fact p.Prime] {n b a : ℕ}
    (hb : 0 < b) (hbn : b < n) (hvb : padicValNat p b ≤ a) :
    (∑ h ∈ Finset.Ico 1 n,
      if h < b then (if ¬ p ^ (a + 1) ∣ h then 1 else 0) else 0) +
      b / p ^ (a + 1) = b - 1 := by
  have hsplit :
      (∑ h ∈ Finset.Ico 1 n, if h < b then (if ¬ p ^ (a + 1) ∣ h then 1 else 0) else 0) =
      ∑ h ∈ Finset.Ioc 0 (b - 1), if ¬ p ^ (a + 1) ∣ h then 1 else 0 := by
    rw [← Finset.sum_filter]
    refine Finset.sum_congr ?_ fun _ _ ↦ rfl
    ext h; simp only [Finset.mem_filter, Finset.mem_Ico, Finset.mem_Ioc]; omega
  have hd_pos : 0 < p ^ (a + 1) := pow_pos (Fact.out : p.Prime).pos _
  have hndvd_b : ¬ p ^ (a + 1) ∣ b := by
    rw [Nat.padicValNat_def] at hvb
    rw [multiplicity_dvd_iff_le hb.ne']; omega
  have hdecomp : (b % p ^ (a + 1) - 1) + p ^ (a + 1) * (b / p ^ (a + 1)) = b - 1 := by
    have := Nat.pos_of_ne_zero (mt Nat.dvd_iff_mod_eq_zero.mpr hndvd_b)
    have := Nat.div_add_mod b (p ^ (a + 1))
    omega
  have hdiv_b : (b - 1) / p ^ (a + 1) = b / p ^ (a + 1) := by
    have := Nat.mod_lt b hd_pos
    rw [← hdecomp, Nat.add_mul_div_left _ _ hd_pos, Nat.div_eq_of_lt (by omega), zero_add]
  have hpart := Finset.card_filter_add_card_filter_not (s := Finset.Ioc 0 (b - 1))
    (fun h ↦ p ^ (a + 1) ∣ h)
  rw [Nat.Ioc_filter_dvd_card_eq_div, hdiv_b, Nat.card_Ioc, Nat.sub_zero] at hpart
  rw [hsplit, Finset.sum_boole, Nat.cast_id]
  omega

/-- **Sum of Ore coefficient depths over `ℚ_[p]` when `0 < j % n`**: for an Ore-admissible pair
`(n, j)` with `0 < j % n`,
`(∑_{1 ≤ h < n} ν_h) + (∑_{1 ≤ i ≤ j / n} n / p ^ i + (j % n) / p ^ (j / n + 1)) = n + j - 2`. -/
theorem sum_oreCoefficientDepth_padic_of_mod_pos (p : ℕ) [Fact p.Prime] {n j : ℕ}
    (hadm : IsOreAdmissible ℚ_[p] n j) (hmod : 0 < j % n) :
    (∑ h ∈ Finset.Ico 1 n, oreCoefficientDepth ℚ_[p] n j h) +
      (∑ i ∈ Finset.Icc 1 (j / n), n / p ^ i + (j % n) / p ^ (j / n + 1)) = n + j - 2 := by
  have hn := hadm.pos
  obtain ⟨hvb, -⟩ := (isOreAdmissible_of_mod_pos hmod).mp hadm |>.2
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
  have hextra := sum_Ico_lt_mod_not_dvd_add_div p hmod hlt_b hvb_le
  have := Nat.div_add_mod j n
  have hbase := sum_Ico_div_sub_padicValNat_of_isOreAdmissible p hadm
  rw [Nat.mul_comm (j / n) n] at hbase
  rw [Finset.sum_congr rfl hdepth, Finset.sum_add_distrib, Finset.sum_add_distrib,
    Finset.sum_const, Nat.card_Ico, smul_eq_mul, mul_one]
  omega

/-- **Krasner's count over `ℚ_[p]`, closed form** (Pauli–Roblot, Theorem 6.1): for an
Ore-admissible wild exponent `j = a * n + b` (`a = j / n`, `b = j % n`), the number of totally
ramified degree-`n` extensions of `ℚ_[p]` inside `SeparableClosure ℚ_[p]` of wild exponent `j` is
`n * p ^ (∑_{1 ≤ i ≤ a} n / p ^ i)` when `b = 0`, and
`n * (p - 1) * p ^ (∑_{1 ≤ i ≤ a} n / p ^ i + b / p ^ (a + 1))` when `0 < b`. -/
theorem ncard_mem_totallyRamifiedOfDegree_wildExponent_eq_padic (p : ℕ) [Fact p.Prime]
    {n j : ℕ} (hadm : IsOreAdmissible ℚ_[p] n j) :
    {E ∈ totallyRamifiedOfDegree ℚ_[p] n | E.wildExponent = j}.ncard =
      if j % n = 0 then n * p ^ (∑ i ∈ Finset.Icc 1 (j / n), n / p ^ i)
      else n * (p - 1) *
        p ^ (∑ i ∈ Finset.Icc 1 (j / n), n / p ^ i + (j % n) / p ^ (j / n + 1)) := by
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

/-- **Total number of totally ramified degree-`n` extensions of `ℚ_[p]`** as a finite sum over
Ore-admissible wild exponents `0 ≤ j ≤ n * v_p(n)`. -/
theorem ncard_totallyRamifiedOfDegree_padic (p : ℕ) [Fact p.Prime] {n : ℕ} (hn : 0 < n) :
    (totallyRamifiedOfDegree ℚ_[p] n).ncard =
      ∑ j ∈ Finset.range (n * padicValNat p n + 1),
        if (if j % n = 0 then padicValNat p n * n
            else min (padicValNat p (j % n) * n) (padicValNat p n * n)) ≤ j ∧
            j ≤ padicValNat p n * n then
          if j % n = 0 then n * p ^ (∑ i ∈ Finset.Icc 1 (j / n), n / p ^ i)
          else n * (p - 1) *
            p ^ (∑ i ∈ Finset.Icc 1 (j / n), n / p ^ i + (j % n) / p ^ (j / n + 1))
        else 0 := by
  rw [ncard_totallyRamifiedOfDegree_eq_sum (Nat.cast_ne_zero.mpr hn.ne'),
    _root_.Padic.natCastValuation_eq_padicValNat]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  by_cases hadm : IsOreAdmissible ℚ_[p] n j
  · rw [ite_eq_left (((isOreAdmissible_padic_iff p).mp hadm).2),
      ncard_mem_totallyRamifiedOfDegree_wildExponent_eq_padic p hadm]
  · rw [ite_eq_right fun h ↦ hadm ((isOreAdmissible_padic_iff p).mpr ⟨hn, h⟩)]
    have hempty : {E ∈ totallyRamifiedOfDegree ℚ_[p] n | E.wildExponent = j} = ∅ := by
      ext E
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
      exact fun hE hEj ↦ hadm (ore_realizability.mp ⟨E, hE, hEj⟩)
    rw [hempty, Set.ncard_empty]

/-- `ℚ_[2]` has `6` ramified quadratic extensions inside `SeparableClosure ℚ_[2]` (`2` of wild
exponent `1` and `4` of wild exponent `2`). -/
theorem ncard_totallyRamifiedOfDegree_two_padicTwo :
    (totallyRamifiedOfDegree ℚ_[2] 2).ncard = 6 := by
  rw [ncard_totallyRamifiedOfDegree_padic 2 (by decide)]
  simp only [Nat.padicValNat_def, Nat.multiplicity_self (by decide : 1 < 2),
    Finset.sum_range_succ, Finset.sum_range_zero,
    multiplicity_eq_zero_of_not_dvd (by decide : ¬ 2 ∣ 1)]
  norm_num

/-- `ℚ_[3]` has `21` totally ramified cubic extensions inside `SeparableClosure ℚ_[3]` (`6` of wild
exponent `1`, `6` of wild exponent `2`, and `9` of wild exponent `3`). -/
theorem ncard_totallyRamifiedOfDegree_three_padicThree :
    (totallyRamifiedOfDegree ℚ_[3] 3).ncard = 21 := by
  rw [ncard_totallyRamifiedOfDegree_padic 3 (by decide)]
  simp only [Nat.padicValNat_def, Nat.multiplicity_self (by decide : 1 < 3),
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
  simp only [Nat.padicValNat_def, hm4, Finset.sum_range_succ, Finset.sum_range_zero,
    multiplicity_eq_zero_of_not_dvd (by decide : ¬ 2 ∣ 1),
    Nat.multiplicity_self (by decide : 1 < 2),
    multiplicity_eq_zero_of_not_dvd (by decide : ¬ 2 ∣ 3), hIcc2]
  norm_num

end TauCeti
