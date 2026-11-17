/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.MassFormula.Krasner.Count
public import TauCeti.NumberTheory.LocalField.Unramified.IntermediateField
import Mathlib.Data.ENat.BigOperators
import Mathlib.Data.Set.Card.Arithmetic
import Mathlib.NumberTheory.Divisors
import TauCeti.FieldTheory.IntermediateField.Map
import TauCeti.FieldTheory.IntermediateField.ScalarTower
import TauCeti.FieldTheory.IsSepClosed

/-!
# Total counts of extensions of a local field of given degree

Let `K` be a nonarchimedean local field and `n : ℕ`. Summing Krasner's discriminant-stratified
counts from `TauCeti.NumberTheory.LocalField.MassFormula.Krasner.Count` over all wild exponents `j`
yields the total count of totally ramified degree-`n` subextensions `σ_K(n)` of `SeparableClosure K`
and, via the canonical unramified-ramified tower decomposition, the total count of all degree-`n`
subextensions of `SeparableClosure K`.

## Main results

* `TauCeti.encard_totallyRamifiedOfDegree_eq_tsum` and
  `TauCeti.encard_totallyRamifiedOfDegree_eq_tsum_isOreAdmissible`:
  `(#σ_K(n) : ℝ≥0∞) = ∑' j, #{L ∈ σ_K(n) | L.wildExponent = j}` (valid in both mixed and equal
  characteristic, including when `#σ_K(n) = ∞`).
* `TauCeti.finite_totallyRamifiedOfDegree_of_natCast_ne_zero`,
  `TauCeti.ncard_totallyRamifiedOfDegree_eq_sum`, and
  `TauCeti.natCast_ncard_totallyRamifiedOfDegree_eq_sum_krasnerCount`:
  when `(n : K) ≠ 0`, `σ_K(n)` is finite and its cardinality is the finite sum of Krasner's counts
  for `0 ≤ j ≤ n * v_K(n)`.
* Concrete evaluations over `ℚ_[p]`:
  * `#σ_{ℚ_2}(2) = 6` (`2` at wild exponent `1`, `4` at wild exponent `2`);
  * `#σ_{ℚ_3}(3) = 21` (`6` at `j = 1`, `6` at `j = 2`, `9` at `j = 3`);
  * `#σ_{ℚ_2}(4) = 92`.
* `TauCeti.encard_finrank_and_inertiaDegree_eq`: the subextensions of `SeparableClosure K` of
  degree `f * e` and residue degree `f ≥ 1` are in bijection with `σ_{K_f}(e)`, where `K_f` is the
  unique degree-`f` unramified subextension of `SeparableClosure K`.
* `TauCeti.encard_finrank_eq_sum_divisors` and `TauCeti.ncard_finrank_eq_sum_divisors`: the number
  of all degree-`n` subextensions of `SeparableClosure K` equals `∑_{f ∣ n} #σ_{K_f}(n / f)`.
* `TauCeti.infinite_finrank_eq_iff`: for `0 < n`, there are infinitely many degree-`n` subextensions
  of `SeparableClosure K` if and only if `K` has equal characteristic `p` with `p ∣ n`.

## References

* M. Krasner, *Nombre des extensions d'un degré donné d'un corps 𝔭-adique*, in *Les tendances
  géométriques en algèbre et théorie des nombres*, CNRS, Paris, 1966, 143–169.
* S. Pauli and X.-F. Roblot, *On the computation of all extensions of a p-adic field of a given
  degree*, Math. Comp. **70** (2001), 1641–1659.
-/

public section
noncomputable section

open ValuativeRel IntermediateField
open scoped ENNReal

namespace TauCeti

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-! ### Total count of totally ramified extensions -/

/-- **Krasner's total count in `ℝ≥0∞`**: in both mixed and equal characteristic (including when
`σ_K(n)` is infinite), `(#σ_K(n) : ℝ≥0∞)` is the sum over `j : ℕ` of the finite stratum counts
`#{L ∈ σ_K(n) | L.wildExponent = j}`. -/
theorem encard_totallyRamifiedOfDegree_eq_tsum (n : ℕ) :
    ((totallyRamifiedOfDegree K n).encard : ℝ≥0∞) =
      ∑' j : ℕ, ({L ∈ totallyRamifiedOfDegree K n | L.wildExponent = j}.ncard : ℝ≥0∞) := by
  let e : totallyRamifiedOfDegree K n ≃
      Σ j : ℕ, {L ∈ totallyRamifiedOfDegree K n | L.wildExponent = j} :=
    { toFun L := ⟨L.1.wildExponent, L.1, L.2, rfl⟩
      invFun x := ⟨x.2.1, x.2.2.1⟩
      left_inv _ := rfl
      right_inv := fun ⟨_, _, _, hj⟩ ↦ by subst hj; rfl }
  have h1 : ((totallyRamifiedOfDegree K n).encard : ℝ≥0∞) =
      ∑' _ : totallyRamifiedOfDegree K n, (1 : ℝ≥0∞) := by rw [ENNReal.tsum_set_one]
  rw [h1, e.tsum_eq fun _ ↦ (1 : ℝ≥0∞), tsum_sigma']
  refine tsum_congr fun j ↦ ?_
  have hfin := finite_totallyRamifiedOfDegree_wildExponent_eq (K := K) n j
  rw [ENNReal.tsum_set_one, ← hfin.cast_ncard_eq, ENat.toENNReal_coe]

/-- **Krasner's total count over Ore-admissible wild exponents**: restricting the sum in
`encard_totallyRamifiedOfDegree_eq_tsum` to `{j : ℕ // IsOreAdmissible K n j}`. -/
theorem encard_totallyRamifiedOfDegree_eq_tsum_isOreAdmissible (n : ℕ) :
    ((totallyRamifiedOfDegree K n).encard : ℝ≥0∞) =
      ∑' j : {j : ℕ // IsOreAdmissible K n j},
        ({L ∈ totallyRamifiedOfDegree K n | L.wildExponent = j.1}.ncard : ℝ≥0∞) := by
  rw [encard_totallyRamifiedOfDegree_eq_tsum]
  have hsupp : Function.support
      (fun j : ℕ ↦ ({L ∈ totallyRamifiedOfDegree K n | L.wildExponent = j}.ncard : ℝ≥0∞)) ⊆
      {j : ℕ | IsOreAdmissible K n j} := fun j hj ↦ by
    by_contra hnot
    have hnot' : ¬ IsOreAdmissible K n j := hnot
    exact hj (by
      dsimp only
      rw [ncard_totallyRamifiedOfDegree_wildExponent_eq_of_not_isOreAdmissible hnot',
        Nat.cast_zero])
  exact (tsum_subtype_eq_of_support_subset hsupp).symm

/-- Away from equal characteristic `p ∣ n`, `σ_K(n)` is finite. -/
theorem finite_totallyRamifiedOfDegree_of_natCast_ne_zero {n : ℕ} (hnK : (n : K) ≠ 0) :
    (totallyRamifiedOfDegree K n).Finite := by
  refine (finite_totallyRamifiedOfDegree_wildExponent_le (K := K) n
    (n * natCastValuation K n hnK)).subset fun L hL ↦
      ⟨hL, IntermediateField.wildExponent_le_mul_natCastValuation hL hnK⟩

/-- **Krasner's finite total count**: when `(n : K) ≠ 0`, `#σ_K(n)` is the finite sum of the
discriminant-stratum counts over `0 ≤ j ≤ n * v_K(n)`. -/
theorem ncard_totallyRamifiedOfDegree_eq_sum {n : ℕ} (hnK : (n : K) ≠ 0) :
    (totallyRamifiedOfDegree K n).ncard =
      ∑ j ∈ Finset.range (n * natCastValuation K n hnK + 1),
        {L ∈ totallyRamifiedOfDegree K n | L.wildExponent = j}.ncard := by
  have hfin := finite_totallyRamifiedOfDegree_of_natCast_ne_zero hnK
  have htsum := encard_totallyRamifiedOfDegree_eq_tsum (K := K) n
  rw [← hfin.cast_ncard_eq, ENat.toENNReal_coe] at htsum
  rw [tsum_eq_sum (s := Finset.range (n * natCastValuation K n hnK + 1))] at htsum
  · exact_mod_cast htsum
  · intro j hj
    rw [Finset.mem_range, not_lt] at hj
    have hempty : {L ∈ totallyRamifiedOfDegree K n | L.wildExponent = j} = ∅ :=
      Set.eq_empty_of_forall_notMem fun L ⟨hL, hLj⟩ ↦ by
        have hle := IntermediateField.wildExponent_le_mul_natCastValuation hL hnK
        omega
    rw [hempty, Set.ncard_empty, Nat.cast_zero]

/-- **Krasner's finite total count in terms of `krasnerCount`**: when `(n : K) ≠ 0`,
`(#σ_K(n) : ℚ) = ∑ j ∈ Finset.range (n * v_K(n) + 1), krasnerCount K n j`. -/
theorem natCast_ncard_totallyRamifiedOfDegree_eq_sum_krasnerCount {n : ℕ} (hnK : (n : K) ≠ 0) :
    ((totallyRamifiedOfDegree K n).ncard : ℚ) =
      ∑ j ∈ Finset.range (n * natCastValuation K n hnK + 1), krasnerCount K n j := by
  rw [ncard_totallyRamifiedOfDegree_eq_sum hnK, Nat.cast_sum]
  exact Finset.sum_congr rfl fun j _ ↦ (krasner_refined_count (K := K) n j).2

/-! ### Concrete total counts over `ℚ_p` -/

/-- Over `ℚ_[p]`, for any `0 < n`, `#σ_{ℚ_p}(n)` is the finite sum of discriminant-stratum counts
over `0 ≤ j ≤ n * v_p(n)`. -/
theorem ncard_totallyRamifiedOfDegree_padic_eq_sum (p : ℕ) [Fact p.Prime] {n : ℕ} (hn : 0 < n) :
    (totallyRamifiedOfDegree ℚ_[p] n).ncard =
      ∑ j ∈ Finset.range (n * padicValNat p n + 1),
        {L ∈ totallyRamifiedOfDegree ℚ_[p] n | L.wildExponent = j}.ncard := by
  have hnK : (n : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
  simpa only [Padic.natCastValuation_eq_padicValNat] using
    ncard_totallyRamifiedOfDegree_eq_sum (K := ℚ_[p]) hnK

-- Helpers for evaluating `padicValNat` on small concrete numbers.
private theorem padicValNat_eq_zero_of_not_dvd' {p a : ℕ} (h : ¬ p ∣ a) : padicValNat p a = 0 := by
  rw [Nat.padicValNat_def]
  exact multiplicity_eq_zero_of_not_dvd h

private theorem padicValNat_self' {p : ℕ} (hp : 1 < p) : padicValNat p p = 1 := by
  rw [Nat.padicValNat_def]
  exact Nat.multiplicity_self hp

private theorem padicValNat_prime_pow' {p : ℕ} [Fact p.Prime] (k : ℕ) :
    padicValNat p (p ^ k) = k := by
  rw [Nat.padicValNat_def]
  exact Nat.multiplicity_prime_pow k

/-- Over `ℚ_[2]`, the degree-`2` wild-exponent strata have sizes `2, 4` at `j = 1, 2`. -/
theorem ncard_totallyRamifiedOfDegree_two_wildExponent_padicTwo :
    {L ∈ totallyRamifiedOfDegree ℚ_[2] 2 | L.wildExponent = 1}.ncard = 2 ∧
      {L ∈ totallyRamifiedOfDegree ℚ_[2] 2 | L.wildExponent = 2}.ncard = 4 := by
  have hv1 : padicValNat 2 1 = 0 := padicValNat_eq_zero_of_not_dvd' (by decide)
  have hv2 : padicValNat 2 2 = 1 := padicValNat_self' (by decide)
  have hadm1 : IsOreAdmissible ℚ_[2] 2 1 := by
    rw [isOreAdmissible_padic_iff]
    exact ⟨by decide, Or.inr ⟨by decide, by simp [hv1], by simp [hv2]⟩⟩
  have hadm2 : IsOreAdmissible ℚ_[2] 2 2 := by
    rw [isOreAdmissible_padic_iff]
    exact ⟨by decide, Or.inl ⟨by decide, by simp [hv2]⟩⟩
  refine ⟨?_, ?_⟩
  · rw [ncard_totallyRamifiedOfDegree_wildExponent_eq_padic_of_mod_pos 2 hadm1 (by decide)]
    decide
  · rw [ncard_totallyRamifiedOfDegree_wildExponent_eq_padic_of_dvd 2 hadm2 (by decide)]
    decide

/-- **`#σ_{ℚ_2}(2) = 6`** as a natural number, computed via Krasner's formula. -/
theorem ncard_totallyRamifiedOfDegree_two_padicTwo :
    (totallyRamifiedOfDegree ℚ_[2] 2).ncard = 6 := by
  have hv2 : padicValNat 2 2 = 1 := padicValNat_self' (by decide)
  have hnot0 : ¬ IsOreAdmissible ℚ_[2] 2 0 := by
    rw [isOreAdmissible_padic_iff]
    simp [hv2]
  rw [ncard_totallyRamifiedOfDegree_padic_eq_sum 2 (by decide), hv2,
    Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one,
    ncard_totallyRamifiedOfDegree_wildExponent_eq_of_not_isOreAdmissible hnot0,
    ncard_totallyRamifiedOfDegree_two_wildExponent_padicTwo.1,
    ncard_totallyRamifiedOfDegree_two_wildExponent_padicTwo.2]

/-- Over `ℚ_[3]`, the degree-`3` wild-exponent strata have sizes `6, 6, 9` at `j = 1, 2, 3`. -/
theorem ncard_totallyRamifiedOfDegree_three_wildExponent_padicThree :
    {L ∈ totallyRamifiedOfDegree ℚ_[3] 3 | L.wildExponent = 1}.ncard = 6 ∧
      {L ∈ totallyRamifiedOfDegree ℚ_[3] 3 | L.wildExponent = 2}.ncard = 6 ∧
      {L ∈ totallyRamifiedOfDegree ℚ_[3] 3 | L.wildExponent = 3}.ncard = 9 := by
  have hv1 : padicValNat 3 1 = 0 := padicValNat_eq_zero_of_not_dvd' (by decide)
  have hv2 : padicValNat 3 2 = 0 := padicValNat_eq_zero_of_not_dvd' (by decide)
  have hv3 : padicValNat 3 3 = 1 := padicValNat_self' (by decide)
  have hadm1 : IsOreAdmissible ℚ_[3] 3 1 := by
    rw [isOreAdmissible_padic_iff]
    exact ⟨by decide, Or.inr ⟨by decide, by simp [hv1], by simp [hv3]⟩⟩
  have hadm2 : IsOreAdmissible ℚ_[3] 3 2 := by
    rw [isOreAdmissible_padic_iff]
    exact ⟨by decide, Or.inr ⟨by decide, by simp [hv2], by simp [hv3]⟩⟩
  have hadm3 : IsOreAdmissible ℚ_[3] 3 3 := by
    rw [isOreAdmissible_padic_iff]
    exact ⟨by decide, Or.inl ⟨by decide, by simp [hv3]⟩⟩
  refine ⟨?_, ?_, ?_⟩
  · rw [ncard_totallyRamifiedOfDegree_wildExponent_eq_padic_of_mod_pos 3 hadm1 (by decide)]
    decide
  · rw [ncard_totallyRamifiedOfDegree_wildExponent_eq_padic_of_mod_pos 3 hadm2 (by decide)]
    decide
  · rw [ncard_totallyRamifiedOfDegree_wildExponent_eq_padic_of_dvd 3 hadm3 (by decide)]
    decide

/-- **`#σ_{ℚ_3}(3) = 21`**: there are exactly `21` totally ramified cubic subextensions of
`SeparableClosure ℚ_[3]`. -/
theorem ncard_totallyRamifiedOfDegree_three_padicThree :
    (totallyRamifiedOfDegree ℚ_[3] 3).ncard = 21 := by
  have hv3 : padicValNat 3 3 = 1 := padicValNat_self' (by decide)
  have hnot0 : ¬ IsOreAdmissible ℚ_[3] 3 0 := by
    rw [isOreAdmissible_padic_iff]
    simp [hv3]
  have ⟨h1, h2, h3⟩ := ncard_totallyRamifiedOfDegree_three_wildExponent_padicThree
  rw [ncard_totallyRamifiedOfDegree_padic_eq_sum 3 (by decide), hv3,
    Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one,
    ncard_totallyRamifiedOfDegree_wildExponent_eq_of_not_isOreAdmissible hnot0, h1, h2, h3]

/-- **`#σ_{ℚ_3}(3) = 21`** as an extended natural number. -/
theorem encard_totallyRamifiedOfDegree_three_padicThree :
    (totallyRamifiedOfDegree ℚ_[3] 3).encard = 21 := by
  have hfin := finite_totallyRamifiedOfDegree_of_natCast_ne_zero (K := ℚ_[3]) (n := 3)
    (Nat.cast_ne_zero.2 (by decide))
  rw [← hfin.cast_ncard_eq, ncard_totallyRamifiedOfDegree_three_padicThree]
  rfl

/-- Helper: stratum counts for totally ramified quartic extensions of `ℚ_[2]` at
`j = 0, 1, 2, 3, 4, 5, 6, 7, 8`. -/
private theorem ncard_totallyRamifiedOfDegree_four_strata_padicTwo :
    {L ∈ totallyRamifiedOfDegree ℚ_[2] 4 | L.wildExponent = 0}.ncard = 0 ∧
      {L ∈ totallyRamifiedOfDegree ℚ_[2] 4 | L.wildExponent = 1}.ncard = 4 ∧
      {L ∈ totallyRamifiedOfDegree ℚ_[2] 4 | L.wildExponent = 2}.ncard = 0 ∧
      {L ∈ totallyRamifiedOfDegree ℚ_[2] 4 | L.wildExponent = 3}.ncard = 8 ∧
      {L ∈ totallyRamifiedOfDegree ℚ_[2] 4 | L.wildExponent = 4}.ncard = 0 ∧
      {L ∈ totallyRamifiedOfDegree ℚ_[2] 4 | L.wildExponent = 5}.ncard = 16 ∧
      {L ∈ totallyRamifiedOfDegree ℚ_[2] 4 | L.wildExponent = 6}.ncard = 16 ∧
      {L ∈ totallyRamifiedOfDegree ℚ_[2] 4 | L.wildExponent = 7}.ncard = 16 ∧
      {L ∈ totallyRamifiedOfDegree ℚ_[2] 4 | L.wildExponent = 8}.ncard = 32 := by
  have hv1 : padicValNat 2 1 = 0 := padicValNat_eq_zero_of_not_dvd' (by decide)
  have hv2 : padicValNat 2 2 = 1 := padicValNat_self' (by decide)
  have hv3 : padicValNat 2 3 = 0 := padicValNat_eq_zero_of_not_dvd' (by decide)
  have hv4 : padicValNat 2 4 = 2 := by
    rw [show (4 : ℕ) = 2 ^ 2 by decide]
    exact padicValNat_prime_pow' 2
  have hnot0 : ¬ IsOreAdmissible ℚ_[2] 4 0 := by rw [isOreAdmissible_padic_iff]; simp [hv4]
  have hnot2 : ¬ IsOreAdmissible ℚ_[2] 4 2 := by rw [isOreAdmissible_padic_iff]; simp [hv2, hv4]
  have hnot4 : ¬ IsOreAdmissible ℚ_[2] 4 4 := by rw [isOreAdmissible_padic_iff]; simp [hv4]
  have hadm1 : IsOreAdmissible ℚ_[2] 4 1 := by
    rw [isOreAdmissible_padic_iff]
    exact ⟨by decide, Or.inr ⟨by decide, by simp [hv1], by simp [hv4]⟩⟩
  have hadm3 : IsOreAdmissible ℚ_[2] 4 3 := by
    rw [isOreAdmissible_padic_iff]
    exact ⟨by decide, Or.inr ⟨by decide, by simp [hv3], by simp [hv4]⟩⟩
  have hadm5 : IsOreAdmissible ℚ_[2] 4 5 := by
    rw [isOreAdmissible_padic_iff]
    exact ⟨by decide, Or.inr ⟨by decide, by simp [hv1], by simp [hv4]⟩⟩
  have hadm6 : IsOreAdmissible ℚ_[2] 4 6 := by
    rw [isOreAdmissible_padic_iff]
    exact ⟨by decide, Or.inr ⟨by decide, by simp [hv2], by simp [hv4]⟩⟩
  have hadm7 : IsOreAdmissible ℚ_[2] 4 7 := by
    rw [isOreAdmissible_padic_iff]
    exact ⟨by decide, Or.inr ⟨by decide, by simp [hv3], by simp [hv4]⟩⟩
  have hadm8 : IsOreAdmissible ℚ_[2] 4 8 := by
    rw [isOreAdmissible_padic_iff]; exact ⟨by decide, Or.inl ⟨by decide, by simp [hv4]⟩⟩
  refine ⟨ncard_totallyRamifiedOfDegree_wildExponent_eq_of_not_isOreAdmissible hnot0, ?_,
    ncard_totallyRamifiedOfDegree_wildExponent_eq_of_not_isOreAdmissible hnot2, ?_,
    ncard_totallyRamifiedOfDegree_wildExponent_eq_of_not_isOreAdmissible hnot4, ?_, ?_, ?_, ?_⟩
  · rw [ncard_totallyRamifiedOfDegree_wildExponent_eq_padic_of_mod_pos 2 hadm1 (by decide)]; decide
  · rw [ncard_totallyRamifiedOfDegree_wildExponent_eq_padic_of_mod_pos 2 hadm3 (by decide)]; decide
  · rw [ncard_totallyRamifiedOfDegree_wildExponent_eq_padic_of_mod_pos 2 hadm5 (by decide)]; decide
  · rw [ncard_totallyRamifiedOfDegree_wildExponent_eq_padic_of_mod_pos 2 hadm6 (by decide)]; decide
  · rw [ncard_totallyRamifiedOfDegree_wildExponent_eq_padic_of_mod_pos 2 hadm7 (by decide)]; decide
  · rw [ncard_totallyRamifiedOfDegree_wildExponent_eq_padic_of_dvd 2 hadm8 (by decide)]; decide

/-- **`#σ_{ℚ_2}(4) = 92`**: there are exactly `92` totally ramified quartic subextensions of
`SeparableClosure ℚ_[2]`. -/
theorem ncard_totallyRamifiedOfDegree_four_padicTwo :
    (totallyRamifiedOfDegree ℚ_[2] 4).ncard = 92 := by
  have hv4 : padicValNat 2 4 = 2 := by
    rw [show (4 : ℕ) = 2 ^ 2 by decide]
    exact padicValNat_prime_pow' 2
  have ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩ := ncard_totallyRamifiedOfDegree_four_strata_padicTwo
  rw [ncard_totallyRamifiedOfDegree_padic_eq_sum 2 (by decide), hv4]
  simp only [show 4 * 2 + 1 = 9 by decide, Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  rw [h0, h1, h2, h3, h4, h5, h6, h7, h8]

/-- **`#σ_{ℚ_2}(4) = 92`** as an extended natural number. -/
theorem encard_totallyRamifiedOfDegree_four_padicTwo :
    (totallyRamifiedOfDegree ℚ_[2] 4).encard = 92 := by
  have hfin := finite_totallyRamifiedOfDegree_of_natCast_ne_zero (K := ℚ_[2]) (n := 4)
    (Nat.cast_ne_zero.2 (by decide))
  rw [← hfin.cast_ncard_eq, ncard_totallyRamifiedOfDegree_four_padicTwo]
  rfl

/-! ### Total count of all degree-`n` extensions via the canonical unramified tower -/

section TowerTransport

variable (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [Algebra K F] [ValuativeExtension K F] [Algebra F (SeparableClosure K)]
  [IsScalarTower K F (SeparableClosure K)] (Φ : SeparableClosure F ≃ₐ[F] SeparableClosure K)
  (E : IntermediateField F (SeparableClosure K))

/-- Multiplicativity of the residue degree along the tower `K ⊆ F ⊆ E` after transporting `E` to
`SeparableClosure F`. -/
private theorem inertiaDegree_restrictScalars_eq_mul
    (hE : Module.Finite F (E.map Φ.symm.toAlgHom)) :
    (E.restrictScalars K).inertiaDegree =
      inertiaDegree K F * (E.map Φ.symm.toAlgHom).inertiaDegree := by
  let e₁ := restrictScalarsAlgEquiv K E
  let e₂ : E ≃ₐ[F] E.map Φ.symm.toAlgHom := intermediateFieldMap Φ.symm E
  have : Module.Finite K F := finite_of_valuativeExtension K F
  have : Module.Finite F E := Module.Finite.equiv e₂.symm.toLinearEquiv
  have : Module.Finite K E := Module.Finite.trans F E
  have : Module.Finite K (E.restrictScalars K) := Module.Finite.equiv e₁.symm.toLinearEquiv
  rw [IntermediateField.inertiaDegree_eq, IntermediateField.inertiaDegree_eq]
  let _ := finiteIntermediateFieldValuativeRel K (SeparableClosure K) (E.restrictScalars K)
  let _ := finiteIntermediateFieldTopology K (SeparableClosure K) (E.restrictScalars K)
  have := finiteIntermediateField_isNonarchimedeanLocalField K (SeparableClosure K)
    (E.restrictScalars K)
  have := finiteIntermediateField_valuativeExtension K (SeparableClosure K) (E.restrictScalars K)
  let _ := finiteIntermediateFieldValuativeRel F (SeparableClosure F) (E.map Φ.symm.toAlgHom)
  let _ := finiteIntermediateFieldTopology F (SeparableClosure F) (E.map Φ.symm.toAlgHom)
  have := finiteIntermediateField_isNonarchimedeanLocalField F (SeparableClosure F)
    (E.map Φ.symm.toAlgHom)
  have := finiteIntermediateField_valuativeExtension F (SeparableClosure F) (E.map Φ.symm.toAlgHom)
  let _ := finiteIntermediateFieldValuativeRel F (SeparableClosure K) E
  let _ := finiteIntermediateFieldTopology F (SeparableClosure K) E
  have := finiteIntermediateField_isNonarchimedeanLocalField F (SeparableClosure K) E
  have := finiteIntermediateField_valuativeExtension F (SeparableClosure K) E
  have : ValuativeExtension K E := ValuativeExtension.trans K F E
  rw [TauCeti.inertiaDegree_eq_of_algEquiv K _ E e₁, TauCeti.inertiaDegree_tower K F E,
    TauCeti.inertiaDegree_eq_of_algEquiv F E _ e₂]

/-- An intermediate field `E` of `SeparableClosure K / F` transports into `σ_F(e)` if and only if
`E.restrictScalars K` has degree `[F : K] * e` and residue degree `f(F / K)` over `K`. -/
private theorem map_mem_totallyRamifiedOfDegree_iff (e : ℕ) :
    E.map Φ.symm.toAlgHom ∈ totallyRamifiedOfDegree F e ↔
      Module.finrank K (E.restrictScalars K) = Module.finrank K F * e ∧
        (E.restrictScalars K).inertiaDegree = inertiaDegree K F := by
  let e₁ := restrictScalarsAlgEquiv K E
  let e₂ : E ≃ₐ[F] E.map Φ.symm.toAlgHom := intermediateFieldMap Φ.symm E
  have : Module.Finite K F := finite_of_valuativeExtension K F
  have hrank : Module.finrank K (E.restrictScalars K) =
      Module.finrank K F * Module.finrank F (E.map Φ.symm.toAlgHom) := by
    rw [e₁.toLinearEquiv.finrank_eq, ← e₂.toLinearEquiv.finrank_eq, Module.finrank_mul_finrank]
  have hf : 0 < inertiaDegree K F := inertiaDegree_pos
  rw [mem_totallyRamifiedOfDegree_iff, hrank,
    IntermediateField.isTotallyRamified_iff_inertiaDegree_eq_one]
  constructor
  · rintro ⟨he, hM⟩
    have : Module.Finite F (E.map Φ.symm.toAlgHom) := by
      by_contra h
      rw [← inertiaDegree_eq_zero_iff] at h
      omega
    rw [he, inertiaDegree_restrictScalars_eq_mul F Φ E this, hM, mul_one]
    exact ⟨rfl, rfl⟩
  · rintro ⟨he, hi⟩
    have : Module.Finite K (E.restrictScalars K) := by
      by_contra h
      rw [← inertiaDegree_eq_zero_iff] at h
      omega
    have : Module.Finite K E := Module.Finite.equiv e₁.toLinearEquiv
    have : Module.Finite F E := Module.Finite.of_restrictScalars_finite K F E
    have : Module.Finite F (E.map Φ.symm.toAlgHom) := Module.Finite.equiv e₂.toLinearEquiv
    rw [inertiaDegree_restrictScalars_eq_mul F Φ E this] at hi
    exact ⟨Nat.eq_of_mul_eq_mul_left Module.finrank_pos he,
      Nat.eq_of_mul_eq_mul_left hf (hi.trans (mul_one _).symm)⟩

end TowerTransport

/-- **Canonical tower bijection**: for `f ≠ 0`, the subextensions of `SeparableClosure K` of
degree `f * e` and residue degree `f` are in bijection with `σ_{K_f}(e)`, where `K_f` is the
unramified degree-`f` subextension `unramifiedExtension K (SeparableClosure K) f`. -/
private def equivTotallyRamifiedOfDegreeUnramified {f : ℕ} (hf : f ≠ 0) (e : ℕ) :
    let U := unramifiedExtension K (SeparableClosure K) f
    letI := finiteIntermediateFieldValuativeRel K (SeparableClosure K) U
    letI := finiteIntermediateFieldTopology K (SeparableClosure K) U
    haveI := finiteIntermediateField_isNonarchimedeanLocalField K (SeparableClosure K) U
    {L : IntermediateField K (SeparableClosure K) //
        Module.finrank K L = f * e ∧ L.inertiaDegree = f} ≃
      totallyRamifiedOfDegree U e := by
  let U := unramifiedExtension K (SeparableClosure K) f
  letI := finiteIntermediateFieldValuativeRel K (SeparableClosure K) U
  letI := finiteIntermediateFieldTopology K (SeparableClosure K) U
  haveI := finiteIntermediateField_isNonarchimedeanLocalField K (SeparableClosure K) U
  haveI := finiteIntermediateField_valuativeExtension K (SeparableClosure K) U
  haveI : IsUnramified K U := isUnramified_unramifiedExtension
  have hUfr : Module.finrank K U = f := finrank_unramifiedExtension hf
  have hUf : inertiaDegree K U = f := by
    rw [IsUnramified.inertiaDegree_eq_finrank, hUfr]
  haveI := isSepClosure_tower_top K U (SeparableClosure K)
  let Φ := IsSepClosure.equiv U (SeparableClosure U) (SeparableClosure K)
  have hle : ∀ {L : IntermediateField K (SeparableClosure K)}, L.inertiaDegree = f → U ≤ L := by
    intro L hL
    have : Module.Finite K L := by
      by_contra h
      rw [← inertiaDegree_eq_zero_iff] at h
      omega
    simpa [U, hL] using L.unramifiedExtension_inertiaDegree_le
  let τ : {L : IntermediateField K (SeparableClosure K) //
      Module.finrank K L = f * e ∧ L.inertiaDegree = f} ≃
      {L : IntermediateField K (SeparableClosure K) //
        (∀ x : U, algebraMap U (SeparableClosure K) x ∈ L) ∧
          Module.finrank K L = f * e ∧ L.inertiaDegree = f} :=
    Equiv.subtypeEquivRight fun L ↦ ⟨fun h ↦ ⟨fun x ↦ hle h.2 x.2, h⟩, And.right⟩
  let ρ : IntermediateField U (SeparableClosure K) ≃
      {L : IntermediateField K (SeparableClosure K) //
        ∀ x : U, algebraMap U (SeparableClosure K) x ∈ L} :=
    { toFun E := ⟨E.restrictScalars K, E.algebraMap_mem⟩
      invFun L := L.1.toSubfield.toIntermediateField L.2
      left_inv _ := rfl
      right_inv _ := rfl }
  exact τ.trans <| (Equiv.subtypeSubtypeEquivSubtypeInter _ _).symm.trans <|
    Equiv.subtypeEquiv (ρ.symm.trans (orderIsoMapComap Φ.symm).toEquiv) fun L ↦ by
      rw [Equiv.trans_apply, OrderIso.coe_toEquiv, orderIsoMapComap_apply,
        map_mem_totallyRamifiedOfDegree_iff U Φ (ρ.symm L) e, hUfr, hUf]
      rfl

/-- **Count of extensions with fixed degree and residue degree**: for `f ≠ 0`, the subextensions
of `SeparableClosure K` of degree `f * e` and residue degree `f` have the same cardinality as
`σ_{K_f}(e)`. -/
theorem encard_finrank_and_inertiaDegree_eq {f : ℕ} (hf : f ≠ 0) (e : ℕ) :
    {L : IntermediateField K (SeparableClosure K) |
        Module.finrank K L = f * e ∧ L.inertiaDegree = f}.encard =
      (let U := unramifiedExtension K (SeparableClosure K) f
      letI := finiteIntermediateFieldValuativeRel K (SeparableClosure K) U
      letI := finiteIntermediateFieldTopology K (SeparableClosure K) U
      haveI := finiteIntermediateField_isNonarchimedeanLocalField K (SeparableClosure K) U
      (totallyRamifiedOfDegree U e).encard) := by
  let U := unramifiedExtension K (SeparableClosure K) f
  let _ := finiteIntermediateFieldValuativeRel K (SeparableClosure K) U
  let _ := finiteIntermediateFieldTopology K (SeparableClosure K) U
  have := finiteIntermediateField_isNonarchimedeanLocalField K (SeparableClosure K) U
  exact Set.encard_congr (equivTotallyRamifiedOfDegreeUnramified hf e)

/-- Helper: every finite subextension of degree `n > 0` has residue degree dividing `n`. -/
private theorem inertiaDegree_mem_divisors_of_finrank_eq {n : ℕ} (hn : 0 < n)
    {L : IntermediateField K (SeparableClosure K)} (hL : Module.finrank K L = n) :
    L.inertiaDegree ∈ n.divisors := by
  have : Module.Finite K L := Module.finite_of_finrank_pos (hL ▸ hn)
  rw [Nat.mem_divisors]
  refine ⟨?_, hn.ne'⟩
  rw [IntermediateField.inertiaDegree_eq]
  let _ := finiteIntermediateFieldValuativeRel K (SeparableClosure K) L
  let _ := finiteIntermediateFieldTopology K (SeparableClosure K) L
  have := finiteIntermediateField_isNonarchimedeanLocalField K (SeparableClosure K) L
  have := finiteIntermediateField_valuativeExtension K (SeparableClosure K) L
  exact ⟨ramificationIndex K L, by rw [← hL, mul_comm, ramificationIndex_mul_inertiaDegree]⟩

/-- **Total count of all degree-`n` extensions inside `SeparableClosure K` (in `ℕ∞`)**: for
`0 < n`, partitioning degree-`n` subextensions by their residue degree `f ∣ n` gives
`#{L | [L : K] = n} = ∑_{f ∣ n} #σ_{K_f}(n / f)`. -/
theorem encard_finrank_eq_sum_divisors {n : ℕ} (hn : 0 < n) :
    {L : IntermediateField K (SeparableClosure K) | Module.finrank K L = n}.encard =
      ∑ f ∈ n.divisors,
        (let U := unramifiedExtension K (SeparableClosure K) f
        letI := finiteIntermediateFieldValuativeRel K (SeparableClosure K) U
        letI := finiteIntermediateFieldTopology K (SeparableClosure K) U
        haveI := finiteIntermediateField_isNonarchimedeanLocalField K (SeparableClosure K) U
        (totallyRamifiedOfDegree U (n / f)).encard) := by
  have hunion : {L : IntermediateField K (SeparableClosure K) | Module.finrank K L = n} =
      ⋃ f ∈ n.divisors,
        {L : IntermediateField K (SeparableClosure K) |
          Module.finrank K L = f * (n / f) ∧ L.inertiaDegree = f} := by
    ext L
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
    refine ⟨fun hL ↦ ⟨L.inertiaDegree, inertiaDegree_mem_divisors_of_finrank_eq hn hL, ?_, rfl⟩,
      fun ⟨f, hf, hL, _⟩ ↦ by rw [hL, Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hf)]⟩
    rw [hL, Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors
      (inertiaDegree_mem_divisors_of_finrank_eq hn hL))]
  have hdisj : Set.PairwiseDisjoint (n.divisors : Set ℕ) fun f ↦
      {L : IntermediateField K (SeparableClosure K) |
        Module.finrank K L = f * (n / f) ∧ L.inertiaDegree = f} := by
    intro f₁ _ f₂ _ hne
    exact Set.disjoint_left.2 fun L h₁ h₂ ↦ hne (h₁.2.symm.trans h₂.2)
  have hbi := (Finset.finite_toSet n.divisors).encard_biUnion hdisj
  rw [finsum_mem_coe_finset] at hbi
  rw [hunion, show (⋃ f ∈ n.divisors,
      {L : IntermediateField K (SeparableClosure K) |
        Module.finrank K L = f * (n / f) ∧ L.inertiaDegree = f}) =
      ⋃ f ∈ (n.divisors : Set ℕ),
      {L : IntermediateField K (SeparableClosure K) |
        Module.finrank K L = f * (n / f) ∧ L.inertiaDegree = f} from rfl, hbi]
  refine Finset.sum_congr rfl fun f hf ↦ ?_
  exact encard_finrank_and_inertiaDegree_eq (Nat.ne_of_gt (Nat.pos_of_mem_divisors hf)) (n / f)

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
/-- Helper: if `(n : K) ≠ 0` and `f ∣ n`, then `(n / f : U) ≠ 0` in any `K`-algebra field `U`. -/
private theorem natCast_div_ne_zero_in_algebra {U : Type*} [Field U] [Algebra K U]
    {n f : ℕ} (hnK : (n : K) ≠ 0) (hf : f ∈ n.divisors) : ((n / f : ℕ) : U) ≠ 0 := by
  intro h0
  have heK : ((n / f : ℕ) : K) = 0 := (algebraMap K U).injective (by simpa using h0)
  have hmul : (f : K) * ((n / f : ℕ) : K) = (n : K) := by
    rw [← Nat.cast_mul, Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hf)]
  exact hnK (by rw [← hmul, heK, mul_zero])

/-- **Finiteness dichotomy for all degree-`n` extensions**: for `0 < n`, `SeparableClosure K` has
infinitely many degree-`n` subextensions if and only if `K` has equal characteristic `p` with
`p ∣ n`. -/
theorem infinite_finrank_eq_iff {n : ℕ} (hn : 0 < n) :
    {L : IntermediateField K (SeparableClosure K) | Module.finrank K L = n}.Infinite ↔
      ringChar K = ringChar 𝓀[K] ∧ ringChar 𝓀[K] ∣ n := by
  constructor
  · intro hinf
    by_contra hnot
    have hnK : (n : K) ≠ 0 :=
      fun h0 ↦ hnot ((natCast_eq_zero_iff_ringChar_eq_ringChar_residueField_and_dvd hn).1 h0)
    have hlt : {L : IntermediateField K (SeparableClosure K) |
        Module.finrank K L = n}.encard < ⊤ := by
      rw [encard_finrank_eq_sum_divisors hn]
      refine ENat.sum_lt_top.2 fun f hf ↦ ?_
      let U := unramifiedExtension K (SeparableClosure K) f
      let _ := finiteIntermediateFieldValuativeRel K (SeparableClosure K) U
      let _ := finiteIntermediateFieldTopology K (SeparableClosure K) U
      have := finiteIntermediateField_isNonarchimedeanLocalField K (SeparableClosure K) U
      exact (finite_totallyRamifiedOfDegree_of_natCast_ne_zero
        (natCast_div_ne_zero_in_algebra (U := U) hnK hf)).encard_lt_top
    exact hinf (Set.encard_lt_top_iff.1 hlt)
  · intro h
    exact ((infinite_totallyRamifiedOfDegree_iff (K := K) hn).2 h).mono fun _ hL ↦
      (mem_totallyRamifiedOfDegree_iff.1 hL).1

/-- Away from equal characteristic `p ∣ n`, there are finitely many degree-`n` subextensions of
`SeparableClosure K`. -/
theorem finite_finrank_eq_of_natCast_ne_zero {n : ℕ} (hnK : (n : K) ≠ 0) :
    {L : IntermediateField K (SeparableClosure K) | Module.finrank K L = n}.Finite := by
  have hn : 0 < n := Nat.pos_of_ne_zero fun h0 ↦ hnK (by simp [h0])
  by_contra hinf
  have ⟨heq, hdvd⟩ := (infinite_finrank_eq_iff (K := K) hn).1 hinf
  exact hnK ((ringChar.spec K n).2 (heq ▸ hdvd))

/-- **Total count of all degree-`n` extensions inside `SeparableClosure K` (in `ℕ`)**: when
`(n : K) ≠ 0`, `#{L | [L : K] = n} = ∑_{f ∣ n} #σ_{K_f}(n / f)`. -/
theorem ncard_finrank_eq_sum_divisors {n : ℕ} (hnK : (n : K) ≠ 0) :
    {L : IntermediateField K (SeparableClosure K) | Module.finrank K L = n}.ncard =
      ∑ f ∈ n.divisors,
        (let U := unramifiedExtension K (SeparableClosure K) f
        letI := finiteIntermediateFieldValuativeRel K (SeparableClosure K) U
        letI := finiteIntermediateFieldTopology K (SeparableClosure K) U
        haveI := finiteIntermediateField_isNonarchimedeanLocalField K (SeparableClosure K) U
        (totallyRamifiedOfDegree U (n / f)).ncard) := by
  have hn : 0 < n := Nat.pos_of_ne_zero fun h0 ↦ hnK (by simp [h0])
  have hfin := finite_finrank_eq_of_natCast_ne_zero (K := K) hnK
  have henc := encard_finrank_eq_sum_divisors (K := K) hn
  rw [← hfin.cast_ncard_eq] at henc
  have hterm (f : ℕ) (hf : f ∈ n.divisors) :
      (let U := unramifiedExtension K (SeparableClosure K) f
      letI := finiteIntermediateFieldValuativeRel K (SeparableClosure K) U
      letI := finiteIntermediateFieldTopology K (SeparableClosure K) U
      haveI := finiteIntermediateField_isNonarchimedeanLocalField K (SeparableClosure K) U
      (totallyRamifiedOfDegree U (n / f)).encard) =
      ((let U := unramifiedExtension K (SeparableClosure K) f
      letI := finiteIntermediateFieldValuativeRel K (SeparableClosure K) U
      letI := finiteIntermediateFieldTopology K (SeparableClosure K) U
      haveI := finiteIntermediateField_isNonarchimedeanLocalField K (SeparableClosure K) U
      (totallyRamifiedOfDegree U (n / f)).ncard : ℕ) : ℕ∞) := by
    let U := unramifiedExtension K (SeparableClosure K) f
    let _ := finiteIntermediateFieldValuativeRel K (SeparableClosure K) U
    let _ := finiteIntermediateFieldTopology K (SeparableClosure K) U
    have := finiteIntermediateField_isNonarchimedeanLocalField K (SeparableClosure K) U
    exact (finite_totallyRamifiedOfDegree_of_natCast_ne_zero
      (natCast_div_ne_zero_in_algebra (U := U) hnK hf)).cast_ncard_eq.symm
  rw [Finset.sum_congr rfl hterm, ← Nat.cast_sum] at henc
  exact_mod_cast henc

end TauCeti
