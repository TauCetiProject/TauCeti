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
import Mathlib.Data.Nat.Factorization.Basic
import TauCeti.Algebra.CharP.LocalRing
import TauCeti.RingTheory.Valuation.ValuativeRel.Basic

/-!
# Closed forms and explicit evaluations of Krasner's count

This file evaluates `TauCeti.krasnerCount K n j` in two principal regimes where the sum of
coefficient depths `∑_{1 ≤ h < n} oreCoefficientDepth K n j h` simplifies into an elementary
arithmetic formula, and records concrete evaluations over `ℚ_p` and `𝔽_q((X))`.

## Main results

### Equal-characteristic closed form
For a discretely valued field `K` of prime characteristic `p` and a degree `n > 0` divisible by `p`:
* `TauCeti.isOreAdmissible_iff_not_dvd_of_ringChar_ne_zero`: `IsOreAdmissible K n j ↔ ¬ p ∣ j`.
* `TauCeti.krasnerCount_eq_of_ringChar_ne_zero`: whenever `¬ p ∣ j`,
  `krasnerCount K n j = n * (q - 1) * q ^ (j / p)`.
* `TauCeti.encard_totallyRamifiedOfDegree_wildExponent_eq_laurentSeries_of_not_dvd` and
  `TauCeti.encard_totallyRamifiedOfDegree_wildExponent_eq_laurentSeries_of_dvd`: exact stratum
  counts over `F⸨X⸩` for a finite field `F`, with the Artin–Schreier example
  `TauCeti.encard_totallyRamifiedOfDegree_two_wildExponent_eq_laurentSeries_zmodTwo` giving
  `2 ^ (m + 1)` totally ramified quadratic extensions of `𝔽_2((X))` of wild exponent `2m + 1`.

### Unramified mixed-characteristic closed form (Pauli–Roblot)
For a nonarchimedean local field `K` with absolute ramification index `e_K = v_K(p) = 1`:
* `TauCeti.isOreAdmissible_iff_of_natCastValuation_ringChar_eq_one`: characterization of Ore
  admissibility via `padicValNat p`.
* `TauCeti.krasnerCount_eq_of_natCastValuation_ringChar_eq_one_of_mod_eq_zero` and
  `TauCeti.krasnerCount_eq_of_natCastValuation_ringChar_eq_one_of_mod_ne_zero`: writing `a = j / n`
  and `b = j % n`,
  - when `b = 0`: `krasnerCount K n j = n * q ^ (∑ i ∈ Icc 1 a, n / p ^ i)`;
  - when `b > 0`:
    `krasnerCount K n j = n * (q - 1) * q ^ (∑ i ∈ Icc 1 a, n / p ^ i + b / p ^ (a + 1))`.

### `ℚ_p` specialization and concrete values
* `TauCeti.krasnerCount_padic`: computable closed form for `krasnerCount ℚ_[p] n j`.
* `TauCeti.encard_totallyRamifiedOfDegree_padic_eq_sum`: total count `#σ_{ℚ_p}(n)` as a finite
  sum up to `n * padicValNat p n`.
* Concrete counts: the strata of `σ_{ℚ_2}(2)` (`2` at `j = 1`, `4` at `j = 2`), the total count
  `#σ_{ℚ_3}(3) = 21`, and the total count `#σ_{ℚ_2}(4) = 92`.

## References

* M. Krasner, *Nombre des extensions d'un degré donné d'un corps `𝔭`-adique*, in *Les tendances
  géométriques en algèbre et théorie des nombres*, Colloq. Internat. CNRS **143** (1966),
  143–169.
* S. Pauli and X.-F. Roblot, *On the computation of all extensions of a `p`-adic field of a given
  degree*, Math. Comp. **70** (2001), no. 236, 1641–1659, Proposition 2.2.
-/

public section
noncomputable section

open ValuativeRel IsDiscreteValuationRing
open scoped LaurentSeries

namespace TauCeti

/-! ### Elementary counting helpers -/

private theorem pred_mul_succ_add {n a : ℕ} (hn : 0 < n) :
    (n - 1) * (a + 1) + a + 1 = n * a + n := by
  calc (n - 1) * (a + 1) + a + 1
      = (n - 1 + 1) * (a + 1) := by ring
    _ = n * (a + 1) := by rw [Nat.sub_add_cancel hn]
    _ = n * a + n := by ring

private theorem div_pred_of_dvd {n d : ℕ} (hn : 0 < n) (hd : 0 < d) (hdvd : d ∣ n) :
    (n - 1) / d + 1 = n / d := by
  obtain ⟨k, rfl⟩ := hdvd
  cases k with
  | zero => simp at hn
  | succ k =>
    have hsub : d * (k + 1) - 1 = d * k + (d - 1) := by rw [mul_add_one]; omega
    rw [hsub, Nat.mul_add_div hd, Nat.div_eq_of_lt (a := d - 1) (by omega), add_zero,
      Nat.mul_div_cancel_left _ hd]

private theorem div_pred_of_not_dvd {n d : ℕ} (hd : 0 < d) (hndvd : ¬ d ∣ n) :
    (n - 1) / d = n / d := by
  have : 0 < n % d := Nat.pos_of_ne_zero fun h ↦ hndvd (Nat.dvd_of_mod_eq_zero h)
  have hlt : n % d < d := Nat.mod_lt n hd
  have hdiv := Nat.div_add_mod n d
  have hsub : n - 1 = d * (n / d) + (n % d - 1) := by omega
  rw [hsub, Nat.mul_add_div hd, Nat.div_eq_of_lt (a := n % d - 1) (by omega), add_zero]

private theorem card_filter_Ico_one_dvd (n d : ℕ) :
    ((Finset.Ico 1 n).filter (d ∣ ·)).card = (n - 1) / d := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have hIco : Finset.Ico 1 n = Finset.Ioc 0 (n - 1) := by
      ext x
      simp only [Finset.mem_Ico, Finset.mem_Ioc]
      omega
    rw [hIco, Nat.Ioc_filter_dvd_card_eq_div]

private theorem sum_min_multiplicity {p : ℕ} (hp : 1 < p) (n a : ℕ) :
    ∑ h ∈ Finset.Ico 1 n, min a (multiplicity p h) =
      ∑ i ∈ Finset.Icc 1 a, (n - 1) / p ^ i := by
  have hterm : ∀ h ∈ Finset.Ico 1 n,
      min a (multiplicity p h) = ∑ i ∈ Finset.Icc 1 a, if p ^ i ∣ h then 1 else 0 := by
    intro h hh
    have hh0 : h ≠ 0 := by
      have := (Finset.mem_Ico.1 hh).1
      omega
    have hfilt : (Finset.Icc 1 a).filter (fun i ↦ p ^ i ∣ h) =
        Finset.Icc 1 (min a (multiplicity p h)) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_Icc,
        Nat.pow_dvd_iff_le_multiplicity hp.ne' hh0, le_min_iff]
      tauto
    rw [Finset.sum_boole, Nat.cast_id, hfilt, Nat.card_Icc]
    omega
  calc ∑ h ∈ Finset.Ico 1 n, min a (multiplicity p h)
      = ∑ h ∈ Finset.Ico 1 n, ∑ i ∈ Finset.Icc 1 a, if p ^ i ∣ h then 1 else 0 :=
        Finset.sum_congr rfl hterm
    _ = ∑ i ∈ Finset.Icc 1 a, ∑ h ∈ Finset.Ico 1 n, if p ^ i ∣ h then 1 else 0 :=
        Finset.sum_comm
    _ = ∑ i ∈ Finset.Icc 1 a, (n - 1) / p ^ i := by
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        rw [Finset.sum_boole, Nat.cast_id, card_filter_Ico_one_dvd]

/-! ### Equal-characteristic closed form -/

section EqualChar

variable {K : Type*} [Field K] [ValuativeRel K] [IsDiscreteValuationRing 𝒪[K]]

private theorem ringChar_residueField_eq_of_ringChar_ne_zero (hchar : ringChar K ≠ 0) :
    ringChar 𝓀[K] = ringChar K := by
  have : CharP 𝒪[K] (ringChar K) := (Subring.subtype 𝒪[K]).charP Subtype.val_injective _
  have hO : ringChar 𝒪[K] = ringChar K := ringChar.eq _ _
  rw [← hO]
  exact IsLocalRing.ringChar_residueField_of_prime_ringChar
    (hO ▸ CharP.char_prime_of_ne_zero K hchar)

private theorem addVal_natCast_eq_top_of_dvd {m : ℕ}
    (hdvd : ringChar K ∣ m) : addVal 𝒪[K] (m : 𝒪[K]) = ⊤ := by
  have : CharP 𝒪[K] (ringChar K) := (Subring.subtype 𝒪[K]).charP Subtype.val_injective _
  have hm0 : (m : 𝒪[K]) = 0 := (CharP.cast_eq_zero_iff 𝒪[K] (ringChar K) m).2 hdvd
  rw [hm0, addVal_zero]

private theorem addVal_natCast_eq_zero_of_not_dvd (hchar : ringChar K ≠ 0) {m : ℕ}
    (hndvd : ¬ ringChar K ∣ m) : addVal 𝒪[K] (m : 𝒪[K]) = 0 := by
  rw [addVal_eq_zero_iff, IsLocalRing.isUnit_natCast_iff_not_dvd,
    ringChar_residueField_eq_of_ringChar_ne_zero hchar]
  exact hndvd

/-- **Ore's admissibility in equal characteristic**: when `ringChar K = p ≠ 0` and `p ∣ n` with
`0 < n`, a wild exponent `j` is Ore-admissible if and only if `p ∤ j`. -/
theorem isOreAdmissible_iff_not_dvd_of_ringChar_ne_zero (hchar : ringChar K ≠ 0) {n j : ℕ}
    (hn : 0 < n) (hdvd : ringChar K ∣ n) :
    IsOreAdmissible K n j ↔ ¬ ringChar K ∣ j := by
  have hvn : addVal 𝒪[K] (n : 𝒪[K]) = ⊤ := addVal_natCast_eq_top_of_dvd hdvd
  have hmod_dvd : ringChar K ∣ j % n ↔ ringChar K ∣ j := by
    have hdiv := Nat.div_add_mod j n
    refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
    · rw [← hdiv]
      exact dvd_add (dvd_mul_of_dvd_left hdvd _) h
    · exact (Nat.dvd_add_right (dvd_mul_of_dvd_left hdvd (j / n))).1 (hdiv.symm ▸ h)
  rw [isOreAdmissible_def, hvn]
  constructor
  · rintro ⟨-, ⟨-, htop⟩ | ⟨-, hvb, -⟩⟩
    · exact absurd htop (ENat.natCast_ne_top _)
    · intro hj
      rw [addVal_natCast_eq_top_of_dvd (hmod_dvd.2 hj)] at hvb
      exact ENat.natCast_ne_top _ (top_le_iff.1 hvb)
  · intro hj
    have hb_ndvd : ¬ ringChar K ∣ j % n := fun h ↦ hj (hmod_dvd.1 h)
    have hb_pos : 0 < j % n := Nat.pos_of_ne_zero fun h ↦ hb_ndvd (h ▸ dvd_zero _)
    refine ⟨hn, Or.inr ⟨hb_pos, ?_, le_top⟩⟩
    rw [addVal_natCast_eq_zero_of_not_dvd hchar hb_ndvd]
    exact zero_le

/-- In equal characteristic `p = ringChar K ≠ 0` with `p ∣ n` and `p ∤ j`, the sum of Ore
coefficient depths satisfies `∑_{1 ≤ h < n} ν_h + j / p = n + j - 2`. -/
theorem sum_oreCoefficientDepth_add_div_eq_of_ringChar_ne_zero (hchar : ringChar K ≠ 0)
    {n j : ℕ} (hn : 0 < n) (hdvd : ringChar K ∣ n) (hj : ¬ ringChar K ∣ j) :
    ∑ h ∈ Finset.Ico 1 n, oreCoefficientDepth K n j h + j / ringChar K = n + j - 2 := by
  set p := ringChar K
  have hp : p.Prime := CharP.char_prime_of_ne_zero K hchar
  set a := j / n
  set b := j % n
  have hmod_dvd : p ∣ b ↔ p ∣ j := by
    have hdiv := Nat.div_add_mod j n
    exact ⟨fun h ↦ hdiv ▸ dvd_add (dvd_mul_of_dvd_left hdvd _) h,
      fun h ↦ (Nat.dvd_add_right (dvd_mul_of_dvd_left hdvd a)).1 (hdiv.symm ▸ h)⟩
  have hb_ndvd : ¬ p ∣ b := fun h ↦ hj (hmod_dvd.1 h)
  have hb_pos : 0 < b := Nat.pos_of_ne_zero fun h ↦ hb_ndvd (h ▸ dvd_zero _)
  have hb_lt : b < n := Nat.mod_lt j hn
  -- Pointwise identity on `h ∈ Ico 1 n`.
  have hpt : ∀ h ∈ Finset.Ico 1 n,
      oreCoefficientDepth K n j h + (if p ∣ h then a else 0) +
          (if h < b ∧ p ∣ h then 1 else 0) =
        a + 1 + (if h < b then 1 else 0) := fun h _ ↦ by
    by_cases hh : p ∣ h
    · have hdepth : oreCoefficientDepth K n j h = 1 := by
        rw [oreCoefficientDepth_def, addVal_natCast_eq_top_of_dvd hh]
        simp
      rw [hdepth]
      by_cases hlt : h < b <;> simp only [hh, hlt, and_self, false_and, ↓reduceIte] <;> omega
    · have hdepth : oreCoefficientDepth K n j h = a + 1 + (if h < b then 1 else 0) := by
        rw [oreCoefficientDepth_def, addVal_natCast_eq_zero_of_not_dvd hchar hh, tsub_zero,
          ENat.toNat_natCast]
        change max 1 (a + 1 + (if h < b then 1 else 0)) = _
        exact max_eq_right (Nat.le_add_right_of_le (Nat.le_add_left 1 _))
      rw [hdepth]
      simp only [hh, and_false, ↓reduceIte, add_zero]
  have hsum := Finset.sum_congr rfl hpt
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib] at hsum
  have hfilt_lt : (Finset.Ico 1 n).filter (· < b) = Finset.Ico 1 b := by
    ext h
    simp only [Finset.mem_filter, Finset.mem_Ico]
    omega
  have hfilt_both : (Finset.Ico 1 n).filter (fun h ↦ h < b ∧ p ∣ h) =
      (Finset.Ico 1 b).filter (p ∣ ·) := by
    ext h
    simp only [Finset.mem_filter, Finset.mem_Ico]
    omega
  have h1 : ∑ h ∈ Finset.Ico 1 n, (if p ∣ h then a else 0) = ((n - 1) / p) * a := by
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, smul_eq_mul,
      card_filter_Ico_one_dvd]
  have h2 : ∑ h ∈ Finset.Ico 1 n, (if h < b ∧ p ∣ h then 1 else 0) = (b - 1) / p := by
    rw [Finset.sum_boole, Nat.cast_id, hfilt_both, card_filter_Ico_one_dvd]
  have h3 : ∑ h ∈ Finset.Ico 1 n, (if h < b then 1 else 0) = b - 1 := by
    rw [Finset.sum_boole, Nat.cast_id, hfilt_lt, Nat.card_Ico]
  rw [h1, h2, h3, Finset.sum_const, Nat.card_Ico, smul_eq_mul] at hsum
  have hn_div : (n - 1) / p + 1 = n / p := div_pred_of_dvd hn hp.pos hdvd
  have hb_div : (b - 1) / p = b / p := div_pred_of_not_dvd hp.pos hb_ndvd
  have hj_div : j / p = (n / p) * a + b / p := by
    have hj_eq : j = p * ((n / p) * a) + b := by
      have hnp : p * (n / p) = n := Nat.mul_div_cancel' hdvd
      have hdiv : n * a + b = j := Nat.div_add_mod j n
      calc j = n * a + b := hdiv.symm
        _ = (p * (n / p)) * a + b := by rw [hnp]
        _ = p * ((n / p) * a) + b := by rw [mul_assoc]
    rw [hj_eq, Nat.mul_add_div hp.pos]
  have hlin : (n - 1) * (a + 1) + a + 1 = n * a + n := pred_mul_succ_add hn
  have hdiv_mod : n * a + b = j := Nat.div_add_mod j n
  have ha_mul : ((n - 1) / p) * a + a = (n / p) * a := by
    rw [← add_one_mul, hn_div]
  omega

/-- **Equal-characteristic closed form for Krasner's count**: when `ringChar K = p ≠ 0`, `0 < n`,
`p ∣ n`, and `p ∤ j`,
`krasnerCount K n j = n * (q - 1) * q ^ (j / p)`. -/
theorem krasnerCount_eq_of_ringChar_ne_zero (hchar : ringChar K ≠ 0) {n j : ℕ} (hn : 0 < n)
    (hdvd : ringChar K ∣ n) (hj : ¬ ringChar K ∣ j) :
    krasnerCount K n j =
      n * (Nat.card 𝓀[K] - 1) * Nat.card 𝓀[K] ^ (j / ringChar K) := by
  have hadm : IsOreAdmissible K n j :=
    (isOreAdmissible_iff_not_dvd_of_ringChar_ne_zero hchar hn hdvd).2 hj
  have hmod : j % n ≠ 0 := fun h0 ↦ hj (dvd_trans hdvd (Nat.dvd_of_mod_eq_zero h0))
  rw [krasnerCount_of_isOreAdmissible_of_mod_ne_zero hadm hmod]
  congr 2
  have hsum := sum_oreCoefficientDepth_add_div_eq_of_ringChar_ne_zero (K := K) hchar hn hdvd hj
  rw [← hsum, Nat.add_sub_cancel_left]

end EqualChar

section LaurentSeries

variable {F : Type*} [Field F] [Finite F]

omit [Finite F] in
private theorem ringChar_laurentSeries : ringChar F⸨X⸩ = ringChar F :=
  have := charP_of_injective_ringHom (algebraMap F F⸨X⸩).injective (ringChar F)
  ringChar.eq F⸨X⸩ (ringChar F)

/-- Ore admissibility over `F⸨X⸩` when `char F ∣ n` and `0 < n`: `j` is Ore-admissible iff
`char F ∤ j`. -/
theorem isOreAdmissible_laurentSeries_iff {n j : ℕ} (hn : 0 < n) (hdvd : ringChar F ∣ n) :
    IsOreAdmissible F⸨X⸩ n j ↔ ¬ ringChar F ∣ j := by
  have hchar : ringChar F⸨X⸩ ≠ 0 := by
    rw [ringChar_laurentSeries]
    exact CharP.ringChar_ne_zero_of_finite F
  simpa only [ringChar_laurentSeries] using
    isOreAdmissible_iff_not_dvd_of_ringChar_ne_zero (K := F⸨X⸩) hchar hn
      (by rwa [ringChar_laurentSeries])

/-- Closed form for `krasnerCount F⸨X⸩ n j` when `0 < n`, `char F ∣ n`, and `char F ∤ j`. -/
theorem krasnerCount_laurentSeries_of_not_dvd {n j : ℕ} (hn : 0 < n) (hdvd : ringChar F ∣ n)
    (hj : ¬ ringChar F ∣ j) :
    krasnerCount F⸨X⸩ n j = n * (Nat.card F - 1) * Nat.card F ^ (j / ringChar F) := by
  have hchar : ringChar F⸨X⸩ ≠ 0 := by
    rw [ringChar_laurentSeries]
    exact CharP.ringChar_ne_zero_of_finite F
  simpa only [ringChar_laurentSeries, LaurentSeries.natCard_residueField] using
    krasnerCount_eq_of_ringChar_ne_zero (K := F⸨X⸩) hchar hn
      (by rwa [ringChar_laurentSeries]) (by rwa [ringChar_laurentSeries])

/-- Exact stratum count over `𝔽_q((X))`: when `0 < n`, `char F ∣ n`, and `char F ∤ j`, there
are `n * (q - 1) * q ^ (j / p)` totally ramified degree-`n` subextensions of wild exponent `j`. -/
theorem encard_totallyRamifiedOfDegree_wildExponent_eq_laurentSeries_of_not_dvd {n j : ℕ}
    (hn : 0 < n) (hdvd : ringChar F ∣ n) (hj : ¬ ringChar F ∣ j) :
    {E ∈ totallyRamifiedOfDegree F⸨X⸩ n | E.wildExponent = j}.encard =
      (n * (Nat.card F - 1) * Nat.card F ^ (j / ringChar F) : ℕ) := by
  rw [encard_totallyRamifiedOfDegree_wildExponent_eq,
    krasnerCount_laurentSeries_of_not_dvd hn hdvd hj]

/-- When `0 < n`, `char F ∣ n`, and `char F ∣ j`, no member of `σ_{F⸨X⸩}(n)` has wild
exponent `j`. -/
theorem encard_totallyRamifiedOfDegree_wildExponent_eq_laurentSeries_of_dvd {n j : ℕ}
    (hn : 0 < n) (hdvd : ringChar F ∣ n) (hj : ringChar F ∣ j) :
    {E ∈ totallyRamifiedOfDegree F⸨X⸩ n | E.wildExponent = j}.encard = 0 := by
  rw [encard_totallyRamifiedOfDegree_wildExponent_eq,
    krasnerCount_of_not_isOreAdmissible
      (mt (isOreAdmissible_laurentSeries_iff hn hdvd).1 (not_not.2 hj)),
    Nat.cast_zero]

/-- Concrete Artin–Schreier example: for every `m : ℕ`, `𝔽_2((X))` has exactly `2 ^ (m + 1)`
totally ramified quadratic subextensions of wild exponent `2 * m + 1`. -/
theorem encard_totallyRamifiedOfDegree_two_wildExponent_eq_laurentSeries_zmodTwo (m : ℕ) :
    {E ∈ totallyRamifiedOfDegree (ZMod 2)⸨X⸩ 2 | E.wildExponent = 2 * m + 1}.encard =
      (2 ^ (m + 1) : ℕ) := by
  have hchar : ringChar (ZMod 2) = 2 := ZMod.ringChar_zmod_n 2
  have hcard : Nat.card (ZMod 2) = 2 := by rw [Nat.card_eq_fintype_card, ZMod.card]
  have hndvd : ¬ ringChar (ZMod 2) ∣ 2 * m + 1 := by
    rw [hchar]
    rintro ⟨k, hk⟩
    omega
  have h := encard_totallyRamifiedOfDegree_wildExponent_eq_laurentSeries_of_not_dvd
    (F := ZMod 2) two_pos (by rw [hchar]) hndvd
  rw [h, hchar, hcard]
  congr 1
  have hdiv : (2 * m + 1) / 2 = m := by omega
  rw [hdiv]
  ring

end LaurentSeries

/-! ### Unramified mixed-characteristic closed form (Pauli–Roblot) -/

section PauliRoblot

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

private theorem natCast_ne_zero_of_ringChar_residueField_ne_zero
    (hp : (ringChar 𝓀[K] : K) ≠ 0) {m : ℕ} (hm : m ≠ 0) : (m : K) ≠ 0 := by
  intro h0
  have heq := ((natCast_eq_zero_iff_ringChar_eq_ringChar_residueField_and_dvd
    (Nat.pos_of_ne_zero hm)).1 h0).1
  exact hp ((ringChar.spec K _).2 (heq ▸ dvd_rfl))

private theorem addVal_natCast_eq_padicValNat_of_eq_one
    (hp : (ringChar 𝓀[K] : K) ≠ 0) (he : natCastValuation K (ringChar 𝓀[K]) hp = 1)
    {m : ℕ} (hm : m ≠ 0) :
    addVal 𝒪[K] (m : 𝒪[K]) = (padicValNat (ringChar 𝓀[K]) m : ℕ∞) := by
  have hmK : (m : K) ≠ 0 := natCast_ne_zero_of_ringChar_residueField_ne_zero hp hm
  rw [IsDiscreteValuationRing.addVal_natCast K m hmK,
    natCastValuation_eq_padicValNat_mul K hmK hp, he, mul_one]

/-- **Ore's conditions for an unramified mixed-characteristic local field (`e_K = 1`)**:
`(n, j)` is Ore-admissible iff `0 < n` and either `j = n * v_p(n)`, or `b = j % n > 0` with
`v_p(b) ≤ j / n` and `j / n + 1 ≤ v_p(n)`. -/
theorem isOreAdmissible_iff_of_natCastValuation_ringChar_eq_one
    (hp : (ringChar 𝓀[K] : K) ≠ 0) (he : natCastValuation K (ringChar 𝓀[K]) hp = 1)
    {n j : ℕ} :
    IsOreAdmissible K n j ↔
      0 < n ∧
        ((j % n = 0 ∧ j / n = padicValNat (ringChar 𝓀[K]) n) ∨
          (0 < j % n ∧ padicValNat (ringChar 𝓀[K]) (j % n) ≤ j / n ∧
            j / n + 1 ≤ padicValNat (ringChar 𝓀[K]) n)) := by
  rw [isOreAdmissible_def]
  refine and_congr_right fun hn ↦ ?_
  rw [addVal_natCast_eq_padicValNat_of_eq_one hp he hn.ne']
  refine or_congr (and_congr_right fun _ ↦ by norm_cast) (and_congr_right fun hb ↦ ?_)
  rw [addVal_natCast_eq_padicValNat_of_eq_one hp he hb.ne']
  norm_cast

private theorem sum_div_pred_pow_add {p n a : ℕ} (hp : p.Prime) (hn : 0 < n)
    (ha : a ≤ padicValNat p n) :
    ∑ i ∈ Finset.Icc 1 a, (n - 1) / p ^ i + a = ∑ i ∈ Finset.Icc 1 a, n / p ^ i := by
  have hcard : a = ∑ _i ∈ Finset.Icc 1 a, 1 := by simp
  conv_lhs => arg 2; rw [hcard]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  have hi_le : i ≤ multiplicity p n := by
    rw [← Nat.padicValNat_def]
    exact (Finset.mem_Icc.1 hi).2.trans ha
  exact div_pred_of_dvd hn (pow_pos hp.pos i)
    ((Nat.pow_dvd_iff_le_multiplicity hp.ne_one hn.ne').2 hi_le)

/-- **Pauli–Roblot closed form** (`j % n = 0` case): for a nonarchimedean local field `K` with
absolute ramification index `e_K = v_K(p) = 1`, if `(n, j)` is Ore-admissible and `n ∣ j`, then
`krasnerCount K n j = n * q ^ (∑ i ∈ Icc 1 (j / n), n / p ^ i)`. -/
theorem krasnerCount_eq_of_natCastValuation_ringChar_eq_one_of_mod_eq_zero
    (hp : (ringChar 𝓀[K] : K) ≠ 0) (he : natCastValuation K (ringChar 𝓀[K]) hp = 1)
    {n j : ℕ} (hadm : IsOreAdmissible K n j) (hmod : j % n = 0) :
    krasnerCount K n j =
      n * Nat.card 𝓀[K] ^ (∑ i ∈ Finset.Icc 1 (j / n), n / ringChar 𝓀[K] ^ i) := by
  rw [krasnerCount_of_isOreAdmissible_of_mod_eq_zero hadm hmod]
  congr 2
  set p := ringChar 𝓀[K]
  have hp' : p.Prime := CharP.char_is_prime 𝓀[K] _
  set a := j / n
  obtain ⟨hn, ⟨-, ha_eq⟩ | ⟨hb, -, -⟩⟩ :=
    (isOreAdmissible_iff_of_natCastValuation_ringChar_eq_one hp he).1 hadm
  · have hpt : ∀ h ∈ Finset.Ico 1 n,
        oreCoefficientDepth K n j h + min a (multiplicity p h) = a + 1 := fun h hh ↦ by
      have hh0 : h ≠ 0 := by have := (Finset.mem_Ico.1 hh).1; omega
      have hhK : (h : K) ≠ 0 := natCast_ne_zero_of_ringChar_residueField_ne_zero hp hh0
      rw [oreCoefficientDepth_eq_of_natCast_ne_zero hhK,
        natCastValuation_eq_padicValNat_mul K hhK hp, he, mul_one, Nat.padicValNat_def,
        hmod, ite_eq_right (Nat.not_lt_zero h), add_zero]
      change max 1 (a + 1 - multiplicity p h) + min a (multiplicity p h) = a + 1
      omega
    have hsum := Finset.sum_congr rfl hpt
    rw [Finset.sum_add_distrib, sum_min_multiplicity hp'.one_lt,
      Finset.sum_const, Nat.card_Ico, smul_eq_mul] at hsum
    have hshift := sum_div_pred_pow_add hp' hn (a := a) ha_eq.le
    have hlin : (n - 1) * (a + 1) + a + 1 = n * a + n := pred_mul_succ_add hn
    have hdiv_mod : n * a + j % n = j := Nat.div_add_mod j n
    have hexp : ∑ h ∈ Finset.Ico 1 n, oreCoefficientDepth K n j h +
        ∑ i ∈ Finset.Icc 1 a, n / p ^ i = n + j - 1 := by omega
    rw [← hexp, Nat.add_sub_cancel_left]
  · omega

/-- **Pauli–Roblot closed form** (`j % n ≠ 0` case): for a nonarchimedean local field `K` with
absolute ramification index `e_K = v_K(p) = 1`, if `(n, j)` is Ore-admissible and `n ∤ j`, then
`krasnerCount K n j = n * (q - 1) * q ^ (∑ i ∈ Icc 1 a, n / p ^ i + b / p ^ (a + 1))`, where
`a = j / n` and `b = j % n`. -/
theorem krasnerCount_eq_of_natCastValuation_ringChar_eq_one_of_mod_ne_zero
    (hp : (ringChar 𝓀[K] : K) ≠ 0) (he : natCastValuation K (ringChar 𝓀[K]) hp = 1)
    {n j : ℕ} (hadm : IsOreAdmissible K n j) (hmod : j % n ≠ 0) :
    krasnerCount K n j =
      n * (Nat.card 𝓀[K] - 1) *
        Nat.card 𝓀[K] ^
          (∑ i ∈ Finset.Icc 1 (j / n), n / ringChar 𝓀[K] ^ i +
            j % n / ringChar 𝓀[K] ^ (j / n + 1)) := by
  rw [krasnerCount_of_isOreAdmissible_of_mod_ne_zero hadm hmod]
  congr 2
  set p := ringChar 𝓀[K]
  have hp' : p.Prime := CharP.char_is_prime 𝓀[K] _
  set a := j / n
  set b := j % n
  obtain ⟨hn, ⟨h0, -⟩ | ⟨hb_pos, hvb, hvn⟩⟩ :=
    (isOreAdmissible_iff_of_natCastValuation_ringChar_eq_one hp he).1 hadm
  · exact absurd h0 hmod
  · have hb_lt : b < n := Nat.mod_lt j hn
    have hpt : ∀ h ∈ Finset.Ico 1 n,
        oreCoefficientDepth K n j h + min a (multiplicity p h) +
            (if h < b ∧ a + 1 ≤ multiplicity p h then 1 else 0) =
          a + 1 + (if h < b then 1 else 0) := fun h hh ↦ by
      have hh0 : h ≠ 0 := by have := (Finset.mem_Ico.1 hh).1; omega
      have hhK : (h : K) ≠ 0 := natCast_ne_zero_of_ringChar_residueField_ne_zero hp hh0
      rw [oreCoefficientDepth_eq_of_natCast_ne_zero hhK,
        natCastValuation_eq_padicValNat_mul K hhK hp, he, mul_one, Nat.padicValNat_def]
      change max 1 (a + 1 + (if h < b then 1 else 0) - multiplicity p h) +
          min a (multiplicity p h) + (if h < b ∧ a + 1 ≤ multiplicity p h then 1 else 0) =
        a + 1 + (if h < b then 1 else 0)
      by_cases hlt : h < b <;> by_cases hle : a + 1 ≤ multiplicity p h <;>
        simp only [hlt, hle, and_self, and_false, false_and, ↓reduceIte] <;> omega
    have hsum := Finset.sum_congr rfl hpt
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
      sum_min_multiplicity hp'.one_lt, Finset.sum_const, Nat.card_Ico, smul_eq_mul] at hsum
    have hfilt_lt : (Finset.Ico 1 n).filter (· < b) = Finset.Ico 1 b := by
      ext h
      simp only [Finset.mem_filter, Finset.mem_Ico]
      omega
    have hfilt_rem : (Finset.Ico 1 n).filter (fun h ↦ h < b ∧ a + 1 ≤ multiplicity p h) =
        (Finset.Ico 1 b).filter (p ^ (a + 1) ∣ ·) := by
      ext h
      simp only [Finset.mem_filter, Finset.mem_Ico]
      constructor
      · rintro ⟨⟨h1, _⟩, hlt, hle⟩
        exact ⟨⟨h1, hlt⟩,
          (Nat.pow_dvd_iff_le_multiplicity hp'.ne_one (by omega)).2 hle⟩
      · rintro ⟨⟨h1, hlt⟩, hdvd⟩
        exact ⟨⟨h1, hlt.trans hb_lt⟩, hlt,
          (Nat.pow_dvd_iff_le_multiplicity hp'.ne_one (by omega)).1 hdvd⟩
    have hrem : ∑ h ∈ Finset.Ico 1 n, (if h < b ∧ a + 1 ≤ multiplicity p h then 1 else 0) =
        b / p ^ (a + 1) := by
      rw [Finset.sum_boole, Nat.cast_id, hfilt_rem, card_filter_Ico_one_dvd]
      have hndvd : ¬ p ^ (a + 1) ∣ b := by
        rw [Nat.pow_dvd_iff_le_multiplicity hp'.ne_one hb_pos.ne', ← Nat.padicValNat_def]
        exact Nat.not_le_of_lt (Nat.lt_succ_of_le hvb)
      exact div_pred_of_not_dvd (pow_pos hp'.pos _) hndvd
    have hlt_card : ∑ h ∈ Finset.Ico 1 n, (if h < b then 1 else 0) = b - 1 := by
      rw [Finset.sum_boole, Nat.cast_id, hfilt_lt, Nat.card_Ico]
    rw [hrem, hlt_card] at hsum
    have hshift := sum_div_pred_pow_add hp' hn (a := a) (Nat.le_of_succ_le hvn)
    have hlin : (n - 1) * (a + 1) + a + 1 = n * a + n := pred_mul_succ_add hn
    have hdiv_mod : n * a + b = j := Nat.div_add_mod j n
    have hexp : ∑ h ∈ Finset.Ico 1 n, oreCoefficientDepth K n j h +
        (∑ i ∈ Finset.Icc 1 a, n / p ^ i + b / p ^ (a + 1)) = n + j - 2 := by omega
    rw [← hexp, Nat.add_sub_cancel_left]

end PauliRoblot

/-! ### Specialization to `ℚ_p` and concrete evaluations -/

section Padic

variable {p : ℕ} [Fact p.Prime]

private theorem ringChar_residueField_padic : ringChar 𝓀[ℚ_[p]] = p := by
  have hp' : (ringChar 𝓀[ℚ_[p]]).Prime := CharP.char_is_prime 𝓀[ℚ_[p]] _
  have hdvd : ringChar 𝓀[ℚ_[p]] ∣ p := by
    by_contra h
    have h0 := (natCastValuation_eq_zero_iff_not_dvd ℚ_[p] p
      (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero)).2 h
    rw [Padic.natCastValuation_self p] at h0
    exact one_ne_zero h0
  exact (Nat.prime_dvd_prime_iff_eq hp' Fact.out).1 hdvd

private theorem natCastValuation_ringChar_padic :
    natCastValuation ℚ_[p] (ringChar 𝓀[ℚ_[p]])
      (natCast_ringChar_residueField_ne_zero ℚ_[p]) = 1 := by
  simp [ringChar_residueField_padic, Nat.padicValNat_def, (Fact.out : p.Prime).one_lt]

/-- Ore's admissibility conditions over `ℚ_[p]`. -/
theorem isOreAdmissible_padic_iff {n j : ℕ} :
    IsOreAdmissible ℚ_[p] n j ↔
      0 < n ∧
        ((j % n = 0 ∧ j / n = padicValNat p n) ∨
          (0 < j % n ∧ padicValNat p (j % n) ≤ j / n ∧ j / n + 1 ≤ padicValNat p n)) := by
  simpa only [ringChar_residueField_padic] using
    isOreAdmissible_iff_of_natCastValuation_ringChar_eq_one
      (natCast_ringChar_residueField_ne_zero ℚ_[p]) (natCastValuation_ringChar_padic (p := p))
      (n := n) (j := j)

/-- Pauli–Roblot closed form over `ℚ_[p]` when `n ∣ j`. -/
theorem krasnerCount_padic_of_mod_eq_zero {n j : ℕ} (hadm : IsOreAdmissible ℚ_[p] n j)
    (hmod : j % n = 0) :
    krasnerCount ℚ_[p] n j = n * p ^ (∑ i ∈ Finset.Icc 1 (j / n), n / p ^ i) := by
  simpa only [ringChar_residueField_padic, Padic.natCard_residueField] using
    krasnerCount_eq_of_natCastValuation_ringChar_eq_one_of_mod_eq_zero
      (natCast_ringChar_residueField_ne_zero ℚ_[p]) (natCastValuation_ringChar_padic (p := p))
      hadm hmod

/-- Pauli–Roblot closed form over `ℚ_[p]` when `n ∤ j`. -/
theorem krasnerCount_padic_of_mod_ne_zero {n j : ℕ} (hadm : IsOreAdmissible ℚ_[p] n j)
    (hmod : j % n ≠ 0) :
    krasnerCount ℚ_[p] n j =
      n * (p - 1) * p ^ (∑ i ∈ Finset.Icc 1 (j / n), n / p ^ i + j % n / p ^ (j / n + 1)) := by
  simpa only [ringChar_residueField_padic, Padic.natCard_residueField] using
    krasnerCount_eq_of_natCastValuation_ringChar_eq_one_of_mod_ne_zero
      (natCast_ringChar_residueField_ne_zero ℚ_[p]) (natCastValuation_ringChar_padic (p := p))
      hadm hmod

/-- Explicit closed form for `krasnerCount ℚ_[p] n j` valid for all `n, j : ℕ`. -/
theorem krasnerCount_padic (n j : ℕ) :
    krasnerCount ℚ_[p] n j =
      if 0 < n then
        if j % n = 0 then
          if j / n = padicValNat p n then
            n * p ^ (∑ i ∈ Finset.Icc 1 (j / n), n / p ^ i)
          else 0
        else
          if padicValNat p (j % n) ≤ j / n ∧ j / n + 1 ≤ padicValNat p n then
            n * (p - 1) *
              p ^ (∑ i ∈ Finset.Icc 1 (j / n), n / p ^ i + j % n / p ^ (j / n + 1))
          else 0
      else 0 := by
  by_cases hn : 0 < n
  · rw [ite_eq_left hn]
    by_cases hmod : j % n = 0
    · rw [ite_eq_left hmod]
      by_cases hdiv : j / n = padicValNat p n
      · rw [ite_eq_left hdiv]
        exact krasnerCount_padic_of_mod_eq_zero
          (isOreAdmissible_padic_iff.2 ⟨hn, Or.inl ⟨hmod, hdiv⟩⟩) hmod
      · rw [ite_eq_right hdiv]
        refine krasnerCount_of_not_isOreAdmissible fun hadm ↦ ?_
        obtain ⟨-, ⟨-, h⟩ | ⟨hb, -, -⟩⟩ := isOreAdmissible_padic_iff.1 hadm
        · exact hdiv h
        · omega
    · rw [ite_eq_right hmod]
      by_cases hcond : padicValNat p (j % n) ≤ j / n ∧ j / n + 1 ≤ padicValNat p n
      · rw [ite_eq_left hcond]
        exact krasnerCount_padic_of_mod_ne_zero
          (isOreAdmissible_padic_iff.2
            ⟨hn, Or.inr ⟨Nat.pos_of_ne_zero hmod, hcond.1, hcond.2⟩⟩) hmod
      · rw [ite_eq_right hcond]
        refine krasnerCount_of_not_isOreAdmissible fun hadm ↦ ?_
        obtain ⟨-, ⟨h0, -⟩ | ⟨-, h1, h2⟩⟩ := isOreAdmissible_padic_iff.1 hadm
        · exact hmod h0
        · exact hcond ⟨h1, h2⟩
  · rw [ite_eq_right hn]
    have hn0 : n = 0 := by omega
    rw [hn0, krasnerCount_zero_left]

/-- **Krasner's total count over `ℚ_[p]`**: for `0 < n`, `#σ_{ℚ_[p]}(n)` is the finite sum of
`krasnerCount ℚ_[p] n j` over `0 ≤ j ≤ n * padicValNat p n`. -/
theorem encard_totallyRamifiedOfDegree_padic_eq_sum {n : ℕ} (hn : 0 < n) :
    (totallyRamifiedOfDegree ℚ_[p] n).encard =
      ∑ j ∈ Finset.range (n * padicValNat p n + 1), krasnerCount ℚ_[p] n j := by
  have hnK : (n : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
  rw [encard_totallyRamifiedOfDegree_eq_sum hnK, Padic.natCastValuation_eq_padicValNat]

end Padic

/-! ### Concrete evaluations over `ℚ_2` and `ℚ_3` -/

/-- `ℚ_2` has exactly `2` totally ramified quadratic subextensions of wild exponent `1`
(discriminant exponent `2`). -/
theorem encard_totallyRamifiedOfDegree_two_wildExponent_one_padicTwo :
    {E ∈ totallyRamifiedOfDegree ℚ_[2] 2 | E.wildExponent = 1}.encard = 2 := by
  have h2 : padicValNat 2 2 = 1 := by simp [Nat.padicValNat_def]
  have h1 : padicValNat 2 1 = 0 := by simp [Nat.padicValNat_def]
  rw [encard_totallyRamifiedOfDegree_wildExponent_eq]
  norm_cast
  simp [krasnerCount_padic, h1, h2]

/-- `ℚ_2` has exactly `4` totally ramified quadratic subextensions of wild exponent `2`
(discriminant exponent `3`). -/
theorem encard_totallyRamifiedOfDegree_two_wildExponent_two_padicTwo :
    {E ∈ totallyRamifiedOfDegree ℚ_[2] 2 | E.wildExponent = 2}.encard = 4 := by
  have h2 : padicValNat 2 2 = 1 := by simp [Nat.padicValNat_def]
  rw [encard_totallyRamifiedOfDegree_wildExponent_eq]
  norm_cast
  simp [krasnerCount_padic, h2]

/-- `ℚ_3` has `6`, `6`, and `9` totally ramified cubic subextensions of wild exponents `1`, `2`,
and `3` respectively, for a total of `21`. -/
theorem encard_totallyRamifiedOfDegree_three_padicThree :
    (totallyRamifiedOfDegree ℚ_[3] 3).encard = 21 := by
  have h1 : padicValNat 3 1 = 0 := by simp [Nat.padicValNat_def]
  have h2 : padicValNat 3 2 = 0 := by
    rw [Nat.padicValNat_def]
    exact multiplicity_eq_zero_of_not_dvd (by decide)
  have h3 : padicValNat 3 3 = 1 := by simp [Nat.padicValNat_def]
  rw [encard_totallyRamifiedOfDegree_padic_eq_sum (by norm_num : 0 < 3), h3]
  norm_cast
  simp [Finset.sum_range_succ, krasnerCount_padic, h1, h2, h3]

/-- `ℚ_2` has exactly `92` totally ramified quartic subextensions inside a separable closure
(distributed as `4, 0, 8, 0, 16, 16, 16, 32` across wild exponents `1` through `8`). -/
theorem encard_totallyRamifiedOfDegree_four_padicTwo :
    (totallyRamifiedOfDegree ℚ_[2] 4).encard = 92 := by
  have h1 : padicValNat 2 1 = 0 := by simp [Nat.padicValNat_def]
  have h2 : padicValNat 2 2 = 1 := by simp [Nat.padicValNat_def]
  have h3 : padicValNat 2 3 = 0 := by
    rw [Nat.padicValNat_def]
    exact multiplicity_eq_zero_of_not_dvd (by decide)
  have h4 : padicValNat 2 4 = 2 := by
    simpa [Nat.padicValNat_def] using multiplicity_base_pow (p := 2) (by decide) 2
  rw [encard_totallyRamifiedOfDegree_padic_eq_sum (by norm_num : 0 < 4), h4]
  norm_cast
  simp [Finset.sum_range_succ, Finset.sum_Icc_succ_top, krasnerCount_padic, h1, h2, h3, h4]

end TauCeti
