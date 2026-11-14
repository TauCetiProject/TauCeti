/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Lp.PiLp
public import Mathlib.Data.Set.Card

import Mathlib.Algebra.GroupWithZero.Units.Fintype
import Mathlib.Data.Set.Card.Arithmetic

/-!
# Lévy's reflection inequality and Rademacher tail iteration

For a finite sequence `x : Fin n → E` in a real normed space, **Lévy's reflection inequality**
bounds the upper tail of the maximal partial signed sum by twice the upper tail of the full signed
sum:
`P(∃ k : Fin n, t < ‖∑ j ≤ k, εⱼ xⱼ‖) ≤ 2 P(t < ‖∑ j, εⱼ xⱼ‖)`.
The sign cube is partitioned according to the first index `k` at which `‖S_k(ε)‖ > t`; reflecting
all signs strictly after `k` preserves that first-passage event and adds to `S_n(ε)` to produce
`2 S_k(ε)`, forcing at least one of the two sign patterns into `{t < ‖S_n‖}`.

Combining Lévy's reflection inequality with the independence of prefix and suffix signs yields the
Hoffmann–Jørgensen bound on the sign cube
`P(2 t + ‖x‖_∞ < ‖S‖) ≤ 4 P(t < ‖S‖)²` and the unconditional **Rademacher tail iteration**
`P(3 t < ‖S‖) ≤ 4 P(t < ‖S‖)²`, which iterates to doubly-exponential tail decay at thresholds
`3 ^ k * t`.

All statements are proved without measure-theoretic machinery as exact `Set.ncard` bounds on the
sign cube, together with their normalized probability forms.

## Main declarations

* `TauCeti.ncard_exists_lt_norm_sum_Iic_le`, `TauCeti.ncard_exists_lt_norm_sum_Iic_div_le`:
  Lévy's reflection inequality on `Fin n → ℤˣ` in counting and probability forms.
* `TauCeti.ncard_lt_norm_sum_two_mul_add_norm_toLp_top_le`,
  `TauCeti.ncard_lt_norm_sum_two_mul_add_norm_toLp_top_div_le`: Hoffmann–Jørgensen tail bound on
  `ι → ℤˣ`.
* `TauCeti.ncard_lt_norm_sum_three_mul_le`, `TauCeti.ncard_lt_norm_sum_three_mul_div_le`:
  unconditional Rademacher tail iteration `P(3 t < ‖S‖) ≤ 4 P(t < ‖S‖)²`.
* `TauCeti.ncard_lt_norm_sum_three_pow_mul_div_le`: iterated doubly-exponential bound
  `4 P(3 ^ k * t < ‖S‖) ≤ (4 P(t < ‖S‖)) ^ (2 ^ k)`.

## References

* P. Lévy, *Théorie de l'addition des variables aléatoires*, Gauthier-Villars, 1937.
* J. Hoffmann-Jørgensen, *Sums of independent Banach space valued random variables*, Studia Math.
  52 (1974), 159–186.
* M. Ledoux and M. Talagrand, *Probability in Banach Spaces*, Proposition 2.3 and Lemma 4.6.
-/

public section

noncomputable section

open Finset
open scoped BigOperators ENNReal

namespace TauCeti

section Fin

variable {n : ℕ} {E : Type*} [SeminormedAddCommGroup E]

/-- The first-passage event at `k : Fin n`: `‖S_k(ε)‖ > t` while `‖S_m(ε)‖ ≤ t` for all `m < k`. -/
private def firstExceedance (x : Fin n → E) (t : ℝ) (k : Fin n) : Set (Fin n → ℤˣ) :=
  {ε | t < ‖∑ j ∈ Iic k, ε j • x j‖ ∧ ∀ m < k, ‖∑ j ∈ Iic m, ε j • x j‖ ≤ t}

private theorem pairwiseDisjoint_firstExceedance (x : Fin n → E) (t : ℝ) :
    Pairwise fun k₁ k₂ ↦ Disjoint (firstExceedance x t k₁) (firstExceedance x t k₂) := by
  intro k₁ k₂ hne
  rw [Set.disjoint_left]
  intro ε h₁ h₂
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact not_lt_of_ge (h₂.2 k₁ hlt) h₁.1
  · exact not_lt_of_ge (h₁.2 k₂ hgt) h₂.1

private theorem iUnion_firstExceedance (x : Fin n → E) (t : ℝ) :
    (⋃ k : Fin n, firstExceedance x t k) =
      {ε : Fin n → ℤˣ | ∃ k : Fin n, t < ‖∑ j ∈ Iic k, ε j • x j‖} := by
  classical
  ext ε
  simp only [Set.mem_iUnion, Set.mem_ofPred_eq, firstExceedance]
  constructor
  · rintro ⟨k, hk, _⟩
    exact ⟨k, hk⟩
  · rintro ⟨k, hk⟩
    let S := univ.filter fun m : Fin n ↦ t < ‖∑ j ∈ Iic m, ε j • x j‖
    have hS : S.Nonempty := ⟨k, mem_filter.2 ⟨mem_univ k, hk⟩⟩
    refine ⟨S.min' hS, (mem_filter.1 (min'_mem S hS)).2, fun m hm ↦ ?_⟩
    by_contra hlt
    exact not_lt_of_ge (min'_le S m (mem_filter.2 ⟨mem_univ m, not_le.1 hlt⟩)) hm

/-- Sign reflection strictly after index `k`, leaving coordinates `j ≤ k` unchanged. -/
private def reflectAfter (k : Fin n) : (Fin n → ℤˣ) ≃ (Fin n → ℤˣ) :=
  Equiv.mulLeft (fun j ↦ if j ≤ k then 1 else -1)

private theorem reflectAfter_mem_firstExceedance (x : Fin n → E) (t : ℝ) (k : Fin n)
    (ε : Fin n → ℤˣ) :
    reflectAfter k ε ∈ firstExceedance x t k ↔ ε ∈ firstExceedance x t k := by
  have hsum (m : Fin n) (hm : m ≤ k) :
      ∑ j ∈ Iic m, reflectAfter k ε j • x j = ∑ j ∈ Iic m, ε j • x j :=
    sum_congr rfl fun j hj ↦ by simp [reflectAfter, (mem_Iic.1 hj).trans hm]
  simp only [firstExceedance, Set.mem_ofPred_eq, hsum k le_rfl]
  exact and_congr_right fun _ ↦ forall₂_congr fun m hm ↦ by rw [hsum m hm.le]

private theorem sum_add_sum_reflectAfter [NormedSpace ℝ E] (x : Fin n → E) (k : Fin n)
    (ε : Fin n → ℤˣ) :
    (∑ j, ε j • x j) + (∑ j, reflectAfter k ε j • x j) =
      (2 : ℝ) • ∑ j ∈ Iic k, ε j • x j := by
  have hfilter : univ.filter (fun j : Fin n ↦ j ≤ k) = Iic k := by ext j; simp
  rw [← sum_filter_add_sum_filter_not univ (fun j : Fin n ↦ j ≤ k),
    ← sum_filter_add_sum_filter_not univ (fun j : Fin n ↦ j ≤ k)
      (fun j ↦ reflectAfter k ε j • x j), hfilter]
  have hle : ∑ j ∈ Iic k, reflectAfter k ε j • x j = ∑ j ∈ Iic k, ε j • x j :=
    sum_congr rfl fun j hj ↦ by simp [reflectAfter, mem_Iic.1 hj]
  have hgt : ∑ j ∈ univ.filter (fun j : Fin n ↦ ¬ j ≤ k), reflectAfter k ε j • x j =
      -∑ j ∈ univ.filter (fun j : Fin n ↦ ¬ j ≤ k), ε j • x j := by
    rw [← sum_neg_distrib]
    exact sum_congr rfl fun j hj ↦ by simp [reflectAfter, (mem_filter.1 hj).2, Units.smul_def]
  rw [hle, hgt, two_smul]
  abel

/-- **Lévy's reflection inequality** on the sign cube (counting form): the number of sign patterns
for which some partial sum `∑ j ≤ k, εⱼ xⱼ` exceeds `t` in norm is at most twice the number of sign
patterns for which the full sum exceeds `t` in norm. -/
theorem ncard_exists_lt_norm_sum_Iic_le [NormedSpace ℝ E] (x : Fin n → E) (t : ℝ) :
    {ε : Fin n → ℤˣ | ∃ k : Fin n, t < ‖∑ j ∈ Iic k, ε j • x j‖}.ncard ≤
      2 * {ε : Fin n → ℤˣ | t < ‖∑ j, ε j • x j‖}.ncard := by
  let B : Set (Fin n → ℤˣ) := {ε | t < ‖∑ j, ε j • x j‖}
  have hstep (k : Fin n) :
      (firstExceedance x t k).ncard ≤ 2 * (firstExceedance x t k ∩ B).ncard := by
    have hsub : firstExceedance x t k ⊆
        (firstExceedance x t k ∩ B) ∪ (reflectAfter k) '' (firstExceedance x t k ∩ B) := by
      intro ε hε
      by_cases hB : ε ∈ B
      · exact Or.inl ⟨hε, hB⟩
      · right
        refine ⟨reflectAfter k ε, ⟨(reflectAfter_mem_firstExceedance x t k ε).2 hε, ?_⟩, ?_⟩
        · dsimp [B] at hB ⊢
          have hnorm := norm_add_le (∑ j, ε j • x j) (∑ j, reflectAfter k ε j • x j)
          rw [sum_add_sum_reflectAfter, norm_smul, Real.norm_ofNat] at hnorm
          linarith [hε.1, not_lt.1 hB]
        · ext j; by_cases hj : j ≤ k <;> simp [reflectAfter, hj]
    calc (firstExceedance x t k).ncard
        ≤ ((firstExceedance x t k ∩ B) ∪
            (reflectAfter k) '' (firstExceedance x t k ∩ B)).ncard := Set.ncard_le_ncard hsub
      _ ≤ (firstExceedance x t k ∩ B).ncard +
            ((reflectAfter k) '' (firstExceedance x t k ∩ B)).ncard := Set.ncard_union_le _ _
      _ = 2 * (firstExceedance x t k ∩ B).ncard := by
            rw [Set.ncard_image_of_injective _ (reflectAfter k).injective, two_mul]
  have hdisjB : Pairwise fun k₁ k₂ ↦
      Disjoint (firstExceedance x t k₁ ∩ B) (firstExceedance x t k₂ ∩ B) := fun k₁ k₂ hne ↦
    (pairwiseDisjoint_firstExceedance x t hne).mono Set.inter_subset_left Set.inter_subset_left
  rw [← iUnion_firstExceedance]
  calc (⋃ k : Fin n, firstExceedance x t k).ncard
      ≤ ∑ k : Fin n, (firstExceedance x t k).ncard := Set.ncard_iUnion_le_of_fintype _
    _ ≤ ∑ k : Fin n, 2 * (firstExceedance x t k ∩ B).ncard := sum_le_sum fun k _ ↦ hstep k
    _ = 2 * (⋃ k : Fin n, firstExceedance x t k ∩ B).ncard := by
        rw [← mul_sum, Set.ncard_iUnion_of_finite (fun _ ↦ Set.toFinite _) hdisjB,
          finsum_eq_sum_of_fintype]
    _ ≤ 2 * B.ncard :=
        Nat.mul_le_mul_left 2
          (Set.ncard_le_ncard (Set.iUnion_subset fun _ ↦ Set.inter_subset_right))

/-- **Lévy's reflection inequality** on the sign cube (probability form). -/
theorem ncard_exists_lt_norm_sum_Iic_div_le [NormedSpace ℝ E] (x : Fin n → E) (t : ℝ) :
    ({ε : Fin n → ℤˣ | ∃ k : Fin n, t < ‖∑ j ∈ Iic k, ε j • x j‖}.ncard : ℝ) / 2 ^ n ≤
      2 * (({ε : Fin n → ℤˣ | t < ‖∑ j, ε j • x j‖}.ncard : ℝ) / 2 ^ n) := by
  rw [← mul_div_assoc]
  exact div_le_div_of_nonneg_right (by exact_mod_cast ncard_exists_lt_norm_sum_Iic_le x t)
    (by positivity)

/-! ### Independence of prefix and suffix events and Hoffmann–Jørgensen -/

/-- Product cardinality identity for `firstExceedance x t k` (depending only on `j ≤ k`) and a
tail event depending only on `j > k`. -/
private theorem two_pow_mul_ncard_firstExceedance_inter (x : Fin n → E) (t : ℝ) (k : Fin n) :
    let D : Set (Fin n → ℤˣ) :=
      {ε | t < ‖∑ j ∈ univ.filter (fun j : Fin n ↦ ¬ j ≤ k), ε j • x j‖}
    2 ^ n * (firstExceedance x t k ∩ D).ncard = (firstExceedance x t k).ncard * D.ncard := by
  intro D
  let e := Equiv.piEquivPiSubtypeProd (fun j : Fin n ↦ j ≤ k) (fun _ ↦ ℤˣ)
  let U : Set ({j : Fin n // j ≤ k} → ℤˣ) := {u | e.symm (u, 1) ∈ firstExceedance x t k}
  let V : Set ({j : Fin n // ¬ j ≤ k} → ℤˣ) := {v | e.symm (1, v) ∈ D}
  have hA : e '' firstExceedance x t k = U ×ˢ Set.univ := by
    ext ⟨u, v⟩
    simp only [Set.mem_image, ← e.eq_symm_apply, exists_eq_right, Set.mem_prod,
      Set.mem_univ, and_true, U, firstExceedance, Set.mem_ofPred_eq]
    have hsum (m : Fin n) (hm : m ≤ k) :
        ∑ j ∈ Iic m, e.symm (u, v) j • x j = ∑ j ∈ Iic m, e.symm (u, 1) j • x j :=
      sum_congr rfl fun j hj ↦ by simp [e, (mem_Iic.1 hj).trans hm]
    rw [hsum k le_rfl]
    exact and_congr_right fun _ ↦ forall₂_congr fun m hm ↦ by rw [hsum m hm.le]
  have hD : e '' D = Set.univ ×ˢ V := by
    ext ⟨u, v⟩
    simp only [Set.mem_image, ← e.eq_symm_apply, exists_eq_right, Set.mem_prod,
      Set.mem_univ, true_and, V, D, Set.mem_ofPred_eq]
    have hsum : ∑ j ∈ univ.filter (fun j : Fin n ↦ ¬ j ≤ k), e.symm (u, v) j • x j =
        ∑ j ∈ univ.filter (fun j : Fin n ↦ ¬ j ≤ k), e.symm (1, v) j • x j :=
      sum_congr rfl fun j hj ↦ by simp [e, (mem_filter.1 hj).2]
    rw [hsum]
  have hAD : e '' (firstExceedance x t k ∩ D) = U ×ˢ V := by
    rw [Set.image_inter e.injective, hA, hD, Set.prod_inter_prod, Set.inter_univ, Set.univ_inter]
  have huniv : (Set.univ : Set (Fin n → ℤˣ)).ncard = 2 ^ n := by simp
  have hprod_univ : 2 ^ n = (Set.univ : Set ({j : Fin n // j ≤ k} → ℤˣ)).ncard *
      (Set.univ : Set ({j : Fin n // ¬ j ≤ k} → ℤˣ)).ncard := by
    rw [← huniv, ← Set.ncard_image_of_injective _ e.injective, Set.image_univ,
      Equiv.range_eq_univ, ← Set.univ_prod_univ, Set.ncard_prod]
  have nA : (firstExceedance x t k).ncard =
      U.ncard * (Set.univ : Set ({j : Fin n // ¬ j ≤ k} → ℤˣ)).ncard := by
    rw [← Set.ncard_image_of_injective _ e.injective, hA, Set.ncard_prod]
  have nD : D.ncard =
      (Set.univ : Set ({j : Fin n // j ≤ k} → ℤˣ)).ncard * V.ncard := by
    rw [← Set.ncard_image_of_injective _ e.injective, hD, Set.ncard_prod]
  have nAD : (firstExceedance x t k ∩ D).ncard = U.ncard * V.ncard := by
    rw [← Set.ncard_image_of_injective _ e.injective, hAD, Set.ncard_prod]
  rw [hprod_univ, nA, nD, nAD]
  ring

/-- Reflecting the prefix signs `j ≤ k` bounds the upper tail of the suffix sum by twice the upper
tail of the full sum. -/
private theorem ncard_lt_norm_sum_compl_Iic_le [NormedSpace ℝ E] (x : Fin n → E) (t : ℝ)
    (k : Fin n) :
    {ε : Fin n → ℤˣ |
      t < ‖∑ j ∈ univ.filter (fun j : Fin n ↦ ¬ j ≤ k), ε j • x j‖}.ncard ≤
      2 * {ε : Fin n → ℤˣ | t < ‖∑ j, ε j • x j‖}.ncard := by
  let B : Set (Fin n → ℤˣ) := {ε | t < ‖∑ j, ε j • x j‖}
  let D : Set (Fin n → ℤˣ) := {ε | t < ‖∑ j ∈ univ.filter (fun j : Fin n ↦ ¬ j ≤ k), ε j • x j‖}
  let φ : (Fin n → ℤˣ) ≃ (Fin n → ℤˣ) := Equiv.mulLeft (fun j ↦ if j ≤ k then -1 else 1)
  have hsub : D ⊆ B ∪ φ '' B := by
    intro ε hε
    by_cases hB : ε ∈ B
    · exact Or.inl hB
    · right
      refine ⟨φ ε, ?_, by ext j; by_cases hj : j ≤ k <;> simp [φ, hj]⟩
      have hadd : (∑ j, ε j • x j) + (∑ j, φ ε j • x j) =
          (2 : ℝ) • ∑ j ∈ univ.filter (fun j : Fin n ↦ ¬ j ≤ k), ε j • x j := by
        rw [← sum_filter_add_sum_filter_not univ (fun j : Fin n ↦ j ≤ k),
          ← sum_filter_add_sum_filter_not univ (fun j : Fin n ↦ j ≤ k) (fun j ↦ φ ε j • x j)]
        have hle : ∑ j ∈ univ.filter (fun j : Fin n ↦ j ≤ k), φ ε j • x j =
            -∑ j ∈ univ.filter (fun j : Fin n ↦ j ≤ k), ε j • x j := by
          rw [← sum_neg_distrib]
          exact sum_congr rfl fun j hj ↦ by simp [φ, (mem_filter.1 hj).2, Units.smul_def]
        have hgt : ∑ j ∈ univ.filter (fun j : Fin n ↦ ¬ j ≤ k), φ ε j • x j =
            ∑ j ∈ univ.filter (fun j : Fin n ↦ ¬ j ≤ k), ε j • x j :=
          sum_congr rfl fun j hj ↦ by simp [φ, (mem_filter.1 hj).2]
        rw [hle, hgt, two_smul]
        abel
      dsimp [B, D] at hε hB ⊢
      have hnorm := norm_add_le (∑ j, ε j • x j) (∑ j, φ ε j • x j)
      rw [hadd, norm_smul, Real.norm_ofNat] at hnorm
      linarith [not_lt.1 hB]
  calc D.ncard ≤ (B ∪ φ '' B).ncard := Set.ncard_le_ncard hsub
    _ ≤ B.ncard + (φ '' B).ncard := Set.ncard_union_le _ _
    _ = 2 * B.ncard := by rw [Set.ncard_image_of_injective _ φ.injective, two_mul]

/-- Deterministic inclusion behind Hoffmann–Jørgensen: if `0 < n`, `0 ≤ s`, `0 ≤ t`, and every
summand has norm at most `s`, then `2 * t + s < ‖S_n(ε)‖` forces `t < ‖S_n(ε) - S_k(ε)‖` at the
first index `k` where `t < ‖S_k(ε)‖`. -/
private theorem subset_iUnion_firstExceedance_inter (hn : 0 < n) (x : Fin n → E) {s : ℝ}
    (hs₀ : 0 ≤ s) (hs : ∀ j, ‖x j‖ ≤ s) {t : ℝ} (ht : 0 ≤ t) :
    {ε : Fin n → ℤˣ | 2 * t + s < ‖∑ j, ε j • x j‖} ⊆
      ⋃ k : Fin n, firstExceedance x t k ∩
        {ε | t < ‖∑ j ∈ univ.filter (fun j : Fin n ↦ ¬ j ≤ k), ε j • x j‖} := by
  intro ε hε
  rw [Set.mem_ofPred_eq] at hε
  let k_max : Fin n := ⟨n - 1, Nat.sub_lt hn zero_lt_one⟩
  have hmax : Iic k_max = univ := by ext j; simp [Fin.le_def, k_max]; omega
  have hex : ε ∈ ⋃ k : Fin n, firstExceedance x t k := by
    rw [iUnion_firstExceedance]
    exact ⟨k_max, by rw [hmax]; linarith⟩
  obtain ⟨k, hεk⟩ := Set.mem_iUnion.1 hex
  refine Set.mem_iUnion.2 ⟨k, hεk, ?_⟩
  have hprev : ‖∑ j ∈ (Iic k).erase k, ε j • x j‖ ≤ t := by
    rcases Nat.eq_zero_or_pos k.1 with hk0 | hkpos
    · have hempty : (Iic k).erase k = ∅ := by ext j; simp [Fin.le_def, hk0]
      rw [hempty, sum_empty, norm_zero]
      exact ht
    · let k' : Fin n := ⟨k.1 - 1, by omega⟩
      have hk' : k' < k := Fin.lt_def.2 (by dsimp [k']; omega)
      have herase : (Iic k).erase k = Iic k' := by ext j; simp [Fin.le_def, k']; omega
      rw [herase]
      exact hεk.2 k' hk'
  have hpref : ‖∑ j ∈ Iic k, ε j • x j‖ ≤ t + s := by
    rw [← add_sum_erase _ _ (mem_Iic.2 le_rfl)]
    have hnorm := norm_add_le (ε k • x k) (∑ j ∈ (Iic k).erase k, ε j • x j)
    rw [norm_units_zsmul] at hnorm
    linarith [hs k]
  have hfilter : univ.filter (fun j : Fin n ↦ j ≤ k) = Iic k := by ext j; simp
  have hfull := norm_add_le (∑ j ∈ univ.filter (fun j : Fin n ↦ j ≤ k), ε j • x j)
    (∑ j ∈ univ.filter (fun j : Fin n ↦ ¬ j ≤ k), ε j • x j)
  rw [sum_filter_add_sum_filter_not, hfilter] at hfull
  rw [Set.mem_ofPred_eq]
  linarith

/-- Hoffmann–Jørgensen bound on `Fin n → ℤˣ` when `0 ≤ s` and every summand has norm at most `s`. -/
private theorem ncard_lt_norm_sum_two_mul_add_le_fin [NormedSpace ℝ E] (x : Fin n → E)
    {s : ℝ} (hs₀ : 0 ≤ s) (hs : ∀ j, ‖x j‖ ≤ s) (t : ℝ) :
    2 ^ n * {ε : Fin n → ℤˣ | 2 * t + s < ‖∑ j, ε j • x j‖}.ncard ≤
      4 * {ε : Fin n → ℤˣ | t < ‖∑ j, ε j • x j‖}.ncard ^ 2 := by
  rcases lt_or_ge t 0 with ht | ht
  · have hB : {ε : Fin n → ℤˣ | t < ‖∑ j, ε j • x j‖} = Set.univ :=
      Set.eq_univ_of_forall fun ε ↦ ht.trans_le (norm_nonneg _)
    have hC : {ε : Fin n → ℤˣ | 2 * t + s < ‖∑ j, ε j • x j‖}.ncard ≤ 2 ^ n :=
      (Set.ncard_le_ncard (Set.subset_univ _)).trans_eq (by simp)
    rw [hB, Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_units_int,
      Fintype.card_fin]
    nlinarith [Nat.zero_le (2 ^ n)]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have hC : {ε : Fin 0 → ℤˣ | 2 * t + s < ‖∑ j, ε j • x j‖} = ∅ := by
      ext ε
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_lt,
        univ_eq_empty, sum_empty, norm_zero]
      linarith
    rw [hC, Set.ncard_empty, mul_zero]
    exact Nat.zero_le _
  let B : Set (Fin n → ℤˣ) := {ε | t < ‖∑ j, ε j • x j‖}
  let C : Set (Fin n → ℤˣ) := {ε | 2 * t + s < ‖∑ j, ε j • x j‖}
  let D (k : Fin n) : Set (Fin n → ℤˣ) :=
    {ε | t < ‖∑ j ∈ univ.filter (fun j : Fin n ↦ ¬ j ≤ k), ε j • x j‖}
  have hsumA : ∑ k : Fin n, (firstExceedance x t k).ncard =
      {ε : Fin n → ℤˣ | ∃ k : Fin n, t < ‖∑ j ∈ Iic k, ε j • x j‖}.ncard := by
    rw [← finsum_eq_sum_of_fintype,
      ← Set.ncard_iUnion_of_finite (fun _ ↦ Set.toFinite _) (pairwiseDisjoint_firstExceedance x t),
      iUnion_firstExceedance]
  calc 2 ^ n * C.ncard
      ≤ 2 ^ n * (⋃ k : Fin n, firstExceedance x t k ∩ D k).ncard :=
        Nat.mul_le_mul_left _
          (Set.ncard_le_ncard (subset_iUnion_firstExceedance_inter hn x hs₀ hs ht))
    _ ≤ 2 ^ n * ∑ k : Fin n, (firstExceedance x t k ∩ D k).ncard :=
        Nat.mul_le_mul_left _ (Set.ncard_iUnion_le_of_fintype _)
    _ = ∑ k : Fin n, (firstExceedance x t k).ncard * (D k).ncard := by
        rw [mul_sum]
        exact sum_congr rfl fun k _ ↦ two_pow_mul_ncard_firstExceedance_inter x t k
    _ ≤ ∑ k : Fin n, (firstExceedance x t k).ncard * (2 * B.ncard) :=
        sum_le_sum fun k _ ↦ Nat.mul_le_mul_left _ (ncard_lt_norm_sum_compl_Iic_le x t k)
    _ = (∑ k : Fin n, (firstExceedance x t k).ncard) * (2 * B.ncard) := (sum_mul _ _ _).symm
    _ ≤ (2 * B.ncard) * (2 * B.ncard) := by
        rw [hsumA]
        exact Nat.mul_le_mul_right _ (ncard_exists_lt_norm_sum_Iic_le x t)
    _ = 4 * B.ncard ^ 2 := by ring

end Fin

/-! ### General finite index types and `3 ^ k` tail iteration -/

section Fintype

variable {ι E : Type*} [Fintype ι] [SeminormedAddCommGroup E]

/-- Reindexing a family along a bijection preserves the exceedance count of its Rademacher sum. -/
theorem ncard_lt_norm_sum_comp_equiv {κ : Type*} [Fintype κ] (e : κ ≃ ι) (x : ι → E) (r : ℝ) :
    {δ : κ → ℤˣ | r < ‖∑ k, δ k • x (e k)‖}.ncard =
      {ε : ι → ℤˣ | r < ‖∑ i, ε i • x i‖}.ncard := by
  let φ : (ι → ℤˣ) ≃ (κ → ℤˣ) := e.symm.arrowCongr (Equiv.refl ℤˣ)
  have himg : φ '' {ε : ι → ℤˣ | r < ‖∑ i, ε i • x i‖} =
      {δ : κ → ℤˣ | r < ‖∑ k, δ k • x (e k)‖} := by
    ext δ
    simp only [Set.mem_image, ← φ.eq_symm_apply, exists_eq_right, Set.mem_ofPred_eq]
    rw [← e.sum_comp (fun i ↦ φ.symm δ i • x i)]
    simp [φ]
  rw [← himg, Set.ncard_image_of_injective _ φ.injective]

/-- **Hoffmann–Jørgensen inequality** for Rademacher sums (counting form): on the sign cube
`ι → ℤˣ`, the exceedance count above `2 * t + ‖WithLp.toLp ∞ x‖` is bounded quadratically by the
exceedance count above `t`. -/
theorem ncard_lt_norm_sum_two_mul_add_norm_toLp_top_le [NormedSpace ℝ E] (x : ι → E) (t : ℝ) :
    2 ^ Fintype.card ι *
        {ε : ι → ℤˣ | 2 * t + ‖WithLp.toLp ∞ x‖ < ‖∑ i, ε i • x i‖}.ncard ≤
      4 * {ε : ι → ℤˣ | t < ‖∑ i, ε i • x i‖}.ncard ^ 2 := by
  classical
  let e := (Fintype.equivFin ι).symm
  rw [← ncard_lt_norm_sum_comp_equiv e x, ← ncard_lt_norm_sum_comp_equiv e x]
  exact ncard_lt_norm_sum_two_mul_add_le_fin (x ∘ e) (norm_nonneg _)
    (fun j ↦ PiLp.norm_apply_le (WithLp.toLp ∞ x) (e j)) t

/-- **Hoffmann–Jørgensen inequality** for Rademacher sums (probability form). -/
theorem ncard_lt_norm_sum_two_mul_add_norm_toLp_top_div_le [NormedSpace ℝ E] (x : ι → E)
    (t : ℝ) :
    ({ε : ι → ℤˣ | 2 * t + ‖WithLp.toLp ∞ x‖ < ‖∑ i, ε i • x i‖}.ncard : ℝ) /
        2 ^ Fintype.card ι ≤
      4 * (({ε : ι → ℤˣ | t < ‖∑ i, ε i • x i‖}.ncard : ℝ) / 2 ^ Fintype.card ι) ^ 2 := by
  have h : (2 : ℝ) ^ Fintype.card ι *
      {ε : ι → ℤˣ | 2 * t + ‖WithLp.toLp ∞ x‖ < ‖∑ i, ε i • x i‖}.ncard ≤
    4 * ({ε : ι → ℤˣ | t < ‖∑ i, ε i • x i‖}.ncard : ℝ) ^ 2 := by
    exact_mod_cast ncard_lt_norm_sum_two_mul_add_norm_toLp_top_le x t
  rw [div_pow, ← mul_div_assoc, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [pow_pos (two_pos : (0 : ℝ) < 2) (Fintype.card ι)]

/-- **Rademacher tail iteration** (counting form): unconditionally in any real normed space,
`2 ^ card ι * #{3 * t < ‖S‖} ≤ 4 * #{t < ‖S‖} ^ 2`. -/
theorem ncard_lt_norm_sum_three_mul_le [NormedSpace ℝ E] (x : ι → E) (t : ℝ) :
    2 ^ Fintype.card ι * {ε : ι → ℤˣ | 3 * t < ‖∑ i, ε i • x i‖}.ncard ≤
      4 * {ε : ι → ℤˣ | t < ‖∑ i, ε i • x i‖}.ncard ^ 2 := by
  classical
  set B := {ε : ι → ℤˣ | t < ‖∑ i, ε i • x i‖}
  set C := {ε : ι → ℤˣ | 3 * t < ‖∑ i, ε i • x i‖}
  have huniv : (Set.univ : Set (ι → ℤˣ)).ncard = 2 ^ Fintype.card ι := by simp
  have hC : C.ncard ≤ 2 ^ Fintype.card ι :=
    (Set.ncard_le_ncard (Set.subset_univ C)).trans_eq huniv
  rcases lt_or_ge t 0 with ht | ht
  · have hB : B = Set.univ := Set.eq_univ_of_forall fun ε ↦ ht.trans_le (norm_nonneg _)
    rw [hB, huniv]
    nlinarith [Nat.zero_le (2 ^ Fintype.card ι)]
  by_cases hmax : ∀ i : ι, ‖x i‖ ≤ t
  · let e := (Fintype.equivFin ι).symm
    have h3 : 3 * t = 2 * t + t := by ring
    dsimp only [B, C]
    rw [h3, ← ncard_lt_norm_sum_comp_equiv e x, ← ncard_lt_norm_sum_comp_equiv e x]
    exact ncard_lt_norm_sum_two_mul_add_le_fin (x ∘ e) ht (fun j ↦ hmax (e j)) t
  · push Not at hmax
    obtain ⟨i₀, hi₀⟩ := hmax
    let σ : (ι → ℤˣ) ≃ (ι → ℤˣ) := Equiv.mulLeft (Pi.mulSingle i₀ (-1))
    have hcov : (Set.univ : Set (ι → ℤˣ)) ⊆ B ∪ σ '' B := by
      intro ε _
      by_cases hB : ε ∈ B
      · exact Or.inl hB
      · right
        refine ⟨σ ε, ?_, by ext j; by_cases hj : j = i₀ <;> simp [σ, hj]⟩
        have hsub : (∑ j, ε j • x j) - (∑ j, σ ε j • x j) = (2 : ℤ) • ε i₀ • x i₀ := by
          rw [← sum_sub_distrib, ← Fintype.sum_ite_eq' i₀ fun j ↦ (2 : ℤ) • ε j • x j]
          refine sum_congr rfl fun j _ ↦ ?_
          by_cases hj : j = i₀
          · subst hj; simp [σ, Units.smul_def, two_zsmul]
          · simp [σ, hj]
        have h2 : ‖(2 : ℤ) • ε i₀ • x i₀‖ = 2 * ‖x i₀‖ := by
          rw [norm_zsmul ℝ, norm_units_zsmul]; norm_num
        have hnorm := norm_sub_le (∑ j, ε j • x j) (∑ j, σ ε j • x j)
        rw [hsub, h2] at hnorm
        dsimp [B] at hB ⊢
        linarith [not_lt.1 hB]
    have h2B : 2 ^ Fintype.card ι ≤ 2 * B.ncard := calc
      2 ^ Fintype.card ι = (Set.univ : Set (ι → ℤˣ)).ncard := huniv.symm
      _ ≤ (B ∪ σ '' B).ncard := Set.ncard_le_ncard hcov
      _ ≤ B.ncard + (σ '' B).ncard := Set.ncard_union_le _ _
      _ = 2 * B.ncard := by rw [Set.ncard_image_of_injective _ σ.injective, two_mul]
    nlinarith

/-- **Rademacher tail iteration** (probability form):
`P(3 * t < ‖S‖) ≤ 4 * P(t < ‖S‖) ^ 2`. -/
theorem ncard_lt_norm_sum_three_mul_div_le [NormedSpace ℝ E] (x : ι → E) (t : ℝ) :
    ({ε : ι → ℤˣ | 3 * t < ‖∑ i, ε i • x i‖}.ncard : ℝ) / 2 ^ Fintype.card ι ≤
      4 * (({ε : ι → ℤˣ | t < ‖∑ i, ε i • x i‖}.ncard : ℝ) / 2 ^ Fintype.card ι) ^ 2 := by
  have h : (2 : ℝ) ^ Fintype.card ι * {ε : ι → ℤˣ | 3 * t < ‖∑ i, ε i • x i‖}.ncard ≤
      4 * ({ε : ι → ℤˣ | t < ‖∑ i, ε i • x i‖}.ncard : ℝ) ^ 2 := by
    exact_mod_cast ncard_lt_norm_sum_three_mul_le x t
  rw [div_pow, ← mul_div_assoc, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [pow_pos (two_pos : (0 : ℝ) < 2) (Fintype.card ι)]

/-- **Iterated doubly-exponential Rademacher tail bound**: for every `k : ℕ`,
`4 * P(3 ^ k * t < ‖S‖) ≤ (4 * P(t < ‖S‖)) ^ (2 ^ k)`. -/
theorem ncard_lt_norm_sum_three_pow_mul_div_le [NormedSpace ℝ E] (x : ι → E) (t : ℝ) (k : ℕ) :
    4 * (({ε : ι → ℤˣ | 3 ^ k * t < ‖∑ i, ε i • x i‖}.ncard : ℝ) / 2 ^ Fintype.card ι) ≤
      (4 * (({ε : ι → ℤˣ | t < ‖∑ i, ε i • x i‖}.ncard : ℝ) / 2 ^ Fintype.card ι)) ^
        (2 ^ k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hstep := ncard_lt_norm_sum_three_mul_div_le x (3 ^ k * t)
    have h3 : (3 : ℝ) ^ (k + 1) * t = 3 * (3 ^ k * t) := by ring
    rw [h3]
    calc 4 * (({ε : ι → ℤˣ | 3 * (3 ^ k * t) < ‖∑ i, ε i • x i‖}.ncard : ℝ) /
            2 ^ Fintype.card ι)
        ≤ (4 * (({ε : ι → ℤˣ | 3 ^ k * t < ‖∑ i, ε i • x i‖}.ncard : ℝ) /
            2 ^ Fintype.card ι)) ^ 2 := by linarith
      _ ≤ ((4 * (({ε : ι → ℤˣ | t < ‖∑ i, ε i • x i‖}.ncard : ℝ) /
            2 ^ Fintype.card ι)) ^ (2 ^ k)) ^ 2 :=
          pow_le_pow_left₀ (by positivity) ih 2
      _ = (4 * (({ε : ι → ℤˣ | t < ‖∑ i, ε i • x i‖}.ncard : ℝ) /
            2 ^ Fintype.card ι)) ^ (2 ^ (k + 1)) := by
          rw [← pow_mul, ← pow_succ]

end Fintype

end TauCeti
