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
import Mathlib.Order.Interval.Finset.Fin

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
* `TauCeti.two_pow_card_mul_ncard_two_mul_add_norm_toLp_top_lt_norm_sum_le`,
  `TauCeti.ncard_two_mul_add_norm_toLp_top_lt_norm_sum_div_le`: Hoffmann–Jørgensen tail bound on
  `ι → ℤˣ`.
* `TauCeti.two_pow_card_mul_ncard_three_mul_lt_norm_sum_le`,
  `TauCeti.ncard_three_mul_lt_norm_sum_div_le`: unconditional Rademacher tail iteration
  `P(3 t < ‖S‖) ≤ 4 P(t < ‖S‖)²`.
* `TauCeti.four_mul_ncard_three_pow_mul_lt_norm_sum_div_le`: iterated doubly-exponential bound
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

section Aux

private theorem ncard_le_two_mul_of_subset_union_image {α : Type*} [Finite α] {A B : Set α}
    {φ : α → α} (hφ : Function.Injective φ) (h : A ⊆ B ∪ φ '' B) :
    A.ncard ≤ 2 * B.ncard := calc
  A.ncard ≤ (B ∪ φ '' B).ncard := Set.ncard_le_ncard h
  _ ≤ B.ncard + (φ '' B).ncard := Set.ncard_union_le _ _
  _ = 2 * B.ncard := by rw [Set.ncard_image_of_injective _ hφ, two_mul]

private theorem div_two_pow_le_four_mul_sq {N a b : ℕ} (h : 2 ^ N * a ≤ 4 * b ^ 2) :
    (a : ℝ) / 2 ^ N ≤ 4 * ((b : ℝ) / 2 ^ N) ^ 2 := by
  have h' : (2 : ℝ) ^ N * a ≤ 4 * (b : ℝ) ^ 2 := by exact_mod_cast h
  rw [div_pow, ← mul_div_assoc, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [pow_pos (two_pos : (0 : ℝ) < 2) N]

end Aux

section Reflection

variable {ι : Type*}

/-- Sign reflection outside `s : Finset ι`, leaving coordinates in `s` unchanged and negating
coordinates outside `s`. -/
private def signFlipCompl (s : Finset ι) : (ι → ℤˣ) ≃ (ι → ℤˣ) :=
  open Classical in Equiv.mulLeft (fun j ↦ if j ∈ s then 1 else -1)

@[simp]
private theorem signFlipCompl_signFlipCompl (s : Finset ι) (ε : ι → ℤˣ) :
    signFlipCompl s (signFlipCompl s ε) = ε := by
  classical
  ext j
  by_cases hj : j ∈ s <;> simp [signFlipCompl, hj]

private theorem signFlipCompl_apply_of_mem {s : Finset ι} {j : ι} (hj : j ∈ s) (ε : ι → ℤˣ) :
    signFlipCompl s ε j = ε j := by
  classical
  simp [signFlipCompl, hj]

variable {E : Type*} [Fintype ι] [SeminormedAddCommGroup E]

private theorem sum_add_sum_signFlipCompl [NormedSpace ℝ E] (x : ι → E) (s : Finset ι)
    (ε : ι → ℤˣ) :
    (∑ j, ε j • x j) + (∑ j, signFlipCompl s ε j • x j) =
      (2 : ℝ) • ∑ j ∈ s, ε j • x j := by
  classical
  have hfilter : univ.filter (fun j : ι ↦ j ∈ s) = s := by ext j; simp
  rw [← sum_filter_add_sum_filter_not univ (fun j : ι ↦ j ∈ s),
    ← sum_filter_add_sum_filter_not univ (fun j : ι ↦ j ∈ s)
      (fun j ↦ signFlipCompl s ε j • x j), hfilter]
  have hmem : ∑ j ∈ s, signFlipCompl s ε j • x j = ∑ j ∈ s, ε j • x j :=
    sum_congr rfl fun j hj ↦ by rw [signFlipCompl_apply_of_mem hj]
  have hnot : ∑ j ∈ univ.filter (fun j : ι ↦ ¬ j ∈ s), signFlipCompl s ε j • x j =
      -∑ j ∈ univ.filter (fun j : ι ↦ ¬ j ∈ s), ε j • x j := by
    rw [← sum_neg_distrib]
    exact sum_congr rfl fun j hj ↦ by simp [signFlipCompl, (mem_filter.1 hj).2, Units.smul_def]
  rw [hmem, hnot, two_smul]
  abel

/-- Any `signFlipCompl s`-invariant set `A` on which `t < ‖∑ j ∈ s, ε j • x j‖` has cardinality at
most twice the cardinality of `A ∩ {ε | t < ‖∑ j, ε j • x j‖}`. -/
private theorem ncard_le_two_mul_ncard_inter_of_signFlipCompl [NormedSpace ℝ E] (x : ι → E)
    (s : Finset ι) (t : ℝ) {A : Set (ι → ℤˣ)} (hA_inv : ∀ ε ∈ A, signFlipCompl s ε ∈ A)
    (hA_lt : ∀ ε ∈ A, t < ‖∑ j ∈ s, ε j • x j‖) :
    A.ncard ≤ 2 * (A ∩ {ε | t < ‖∑ j, ε j • x j‖}).ncard := by
  refine ncard_le_two_mul_of_subset_union_image (signFlipCompl s).injective fun ε hε ↦ ?_
  by_cases hB : t < ‖∑ j, ε j • x j‖
  · exact Or.inl ⟨hε, hB⟩
  · refine Or.inr ⟨signFlipCompl s ε, ⟨hA_inv ε hε, ?_⟩, signFlipCompl_signFlipCompl s ε⟩
    rw [Set.mem_ofPred_eq]
    have hnorm := norm_add_le (∑ j, ε j • x j) (∑ j, signFlipCompl s ε j • x j)
    rw [sum_add_sum_signFlipCompl, norm_smul, Real.norm_ofNat] at hnorm
    linarith [hA_lt ε hε, not_lt.1 hB]

/-- Reflecting coordinates outside `s : Finset ι` bounds the upper tail of the sub-sum over `s` by
twice the upper tail of the full signed sum. -/
private theorem ncard_lt_norm_sum_finset_le [NormedSpace ℝ E] (x : ι → E) (s : Finset ι) (t : ℝ) :
    {ε : ι → ℤˣ | t < ‖∑ j ∈ s, ε j • x j‖}.ncard ≤
      2 * {ε : ι → ℤˣ | t < ‖∑ j, ε j • x j‖}.ncard := by
  refine (ncard_le_two_mul_ncard_inter_of_signFlipCompl x s t (fun ε hε ↦ ?_) fun _ hε ↦ hε).trans
    (Nat.mul_le_mul_left 2 (Set.ncard_le_ncard Set.inter_subset_right))
  have hsum : ∑ j ∈ s, signFlipCompl s ε j • x j = ∑ j ∈ s, ε j • x j :=
    sum_congr rfl fun j hj ↦ by rw [signFlipCompl_apply_of_mem hj]
  simpa only [Set.mem_ofPred_eq, hsum] using hε

end Reflection

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

/-- **Lévy's reflection inequality** on the sign cube (counting form): the number of sign patterns
for which some partial sum `∑ j ≤ k, εⱼ xⱼ` exceeds `t` in norm is at most twice the number of sign
patterns for which the full sum exceeds `t` in norm. -/
theorem ncard_exists_lt_norm_sum_Iic_le [NormedSpace ℝ E] (x : Fin n → E) (t : ℝ) :
    {ε : Fin n → ℤˣ | ∃ k : Fin n, t < ‖∑ j ∈ Iic k, ε j • x j‖}.ncard ≤
      2 * {ε : Fin n → ℤˣ | t < ‖∑ j, ε j • x j‖}.ncard := by
  let B : Set (Fin n → ℤˣ) := {ε | t < ‖∑ j, ε j • x j‖}
  have hstep (k : Fin n) :
      (firstExceedance x t k).ncard ≤ 2 * (firstExceedance x t k ∩ B).ncard := by
    refine ncard_le_two_mul_ncard_inter_of_signFlipCompl x (Iic k) t (fun ε hε ↦ ?_) fun _ hε ↦ hε.1
    have hsum (m : Fin n) (hm : m ≤ k) :
        ∑ j ∈ Iic m, signFlipCompl (Iic k) ε j • x j = ∑ j ∈ Iic m, ε j • x j :=
      sum_congr rfl fun j hj ↦ by
        rw [signFlipCompl_apply_of_mem (mem_Iic.2 ((mem_Iic.1 hj).trans hm))]
    exact ⟨by simpa only [hsum k le_rfl] using hε.1,
      fun m hm ↦ by simpa only [hsum m hm.le] using hε.2 m hm⟩
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

/-- Deterministic inclusion behind Hoffmann–Jørgensen: if `0 ≤ s`, `0 ≤ t`, and every summand has
norm at most `s`, then `2 * t + s < ‖S_n(ε)‖` forces `t < ‖S_n(ε) - S_k(ε)‖` at the first index `k`
where `t < ‖S_k(ε)‖`. -/
private theorem subset_iUnion_firstExceedance_inter (x : Fin n → E) {s : ℝ} (hs₀ : 0 ≤ s)
    (hs : ∀ j, ‖x j‖ ≤ s) {t : ℝ} (ht : 0 ≤ t) :
    {ε : Fin n → ℤˣ | 2 * t + s < ‖∑ j, ε j • x j‖} ⊆
      ⋃ k : Fin n, firstExceedance x t k ∩
        {ε | t < ‖∑ j ∈ univ.filter (fun j : Fin n ↦ ¬ j ≤ k), ε j • x j‖} := by
  intro ε hε
  rw [Set.mem_ofPred_eq] at hε
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [univ_eq_empty, sum_empty, norm_zero] at hε
    linarith [hs₀, ht]
  have : NeZero n := ⟨hn.ne'⟩
  have hex : ε ∈ ⋃ k : Fin n, firstExceedance x t k := by
    rw [iUnion_firstExceedance]
    exact ⟨⊤, by rw [Iic_top]; linarith⟩
  obtain ⟨k, hεk⟩ := Set.mem_iUnion.1 hex
  refine Set.mem_iUnion.2 ⟨k, hεk, ?_⟩
  have hprev : ‖∑ j ∈ (Iic k).erase k, ε j • x j‖ ≤ t := by
    rw [Iic_erase]
    rcases eq_bot_or_bot_lt k with rfl | hk
    · rw [Iio_bot, sum_empty, norm_zero]
      exact ht
    · have hk0 : (0 : Fin n) < k := hk
      have hklt : k - 1 < k :=
        Fin.lt_def.2 (by rw [Fin.val_sub_one_of_ne_zero hk0.ne']; exact Nat.sub_lt hk0 Nat.one_pos)
      rw [← Fin.Iic_sub_one_eq_Iio hk0]
      exact hεk.2 (k - 1) hklt
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
private theorem two_pow_mul_ncard_two_mul_add_lt_norm_sum_le_fin [NormedSpace ℝ E] (x : Fin n → E)
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
          (Set.ncard_le_ncard (subset_iUnion_firstExceedance_inter x hs₀ hs ht))
    _ ≤ 2 ^ n * ∑ k : Fin n, (firstExceedance x t k ∩ D k).ncard :=
        Nat.mul_le_mul_left _ (Set.ncard_iUnion_le_of_fintype _)
    _ = ∑ k : Fin n, (firstExceedance x t k).ncard * (D k).ncard := by
        rw [mul_sum]
        exact sum_congr rfl fun k _ ↦ two_pow_mul_ncard_firstExceedance_inter x t k
    _ ≤ ∑ k : Fin n, (firstExceedance x t k).ncard * (2 * B.ncard) :=
        sum_le_sum fun k _ ↦ Nat.mul_le_mul_left _
          (ncard_lt_norm_sum_finset_le x (univ.filter fun j : Fin n ↦ ¬ j ≤ k) t)
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
theorem two_pow_card_mul_ncard_two_mul_add_norm_toLp_top_lt_norm_sum_le [NormedSpace ℝ E]
    (x : ι → E) (t : ℝ) :
    2 ^ Fintype.card ι *
        {ε : ι → ℤˣ | 2 * t + ‖WithLp.toLp ∞ x‖ < ‖∑ i, ε i • x i‖}.ncard ≤
      4 * {ε : ι → ℤˣ | t < ‖∑ i, ε i • x i‖}.ncard ^ 2 := by
  classical
  let e := (Fintype.equivFin ι).symm
  rw [← ncard_lt_norm_sum_comp_equiv e x, ← ncard_lt_norm_sum_comp_equiv e x]
  exact two_pow_mul_ncard_two_mul_add_lt_norm_sum_le_fin (x ∘ e) (norm_nonneg _)
    (fun j ↦ PiLp.norm_apply_le (WithLp.toLp ∞ x) (e j)) t

/-- **Hoffmann–Jørgensen inequality** for Rademacher sums (probability form). -/
theorem ncard_two_mul_add_norm_toLp_top_lt_norm_sum_div_le [NormedSpace ℝ E] (x : ι → E)
    (t : ℝ) :
    ({ε : ι → ℤˣ | 2 * t + ‖WithLp.toLp ∞ x‖ < ‖∑ i, ε i • x i‖}.ncard : ℝ) /
        2 ^ Fintype.card ι ≤
      4 * (({ε : ι → ℤˣ | t < ‖∑ i, ε i • x i‖}.ncard : ℝ) / 2 ^ Fintype.card ι) ^ 2 :=
  div_two_pow_le_four_mul_sq (two_pow_card_mul_ncard_two_mul_add_norm_toLp_top_lt_norm_sum_le x t)

/-- **Rademacher tail iteration** (counting form): unconditionally in any real normed space,
`2 ^ card ι * #{3 * t < ‖S‖} ≤ 4 * #{t < ‖S‖} ^ 2`. -/
theorem two_pow_card_mul_ncard_three_mul_lt_norm_sum_le [NormedSpace ℝ E] (x : ι → E) (t : ℝ) :
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
    exact two_pow_mul_ncard_two_mul_add_lt_norm_sum_le_fin (x ∘ e) ht (fun j ↦ hmax (e j)) t
  · push Not at hmax
    obtain ⟨i₀, hi₀⟩ := hmax
    have h2B : 2 ^ Fintype.card ι ≤ 2 * B.ncard := by
      simpa [norm_units_zsmul, hi₀, B] using ncard_lt_norm_sum_finset_le x ({i₀} : Finset ι) t
    nlinarith

/-- **Rademacher tail iteration** (probability form):
`P(3 * t < ‖S‖) ≤ 4 * P(t < ‖S‖) ^ 2`. -/
theorem ncard_three_mul_lt_norm_sum_div_le [NormedSpace ℝ E] (x : ι → E) (t : ℝ) :
    ({ε : ι → ℤˣ | 3 * t < ‖∑ i, ε i • x i‖}.ncard : ℝ) / 2 ^ Fintype.card ι ≤
      4 * (({ε : ι → ℤˣ | t < ‖∑ i, ε i • x i‖}.ncard : ℝ) / 2 ^ Fintype.card ι) ^ 2 :=
  div_two_pow_le_four_mul_sq (two_pow_card_mul_ncard_three_mul_lt_norm_sum_le x t)

/-- **Iterated doubly-exponential Rademacher tail bound**: for every `k : ℕ`,
`4 * P(3 ^ k * t < ‖S‖) ≤ (4 * P(t < ‖S‖)) ^ (2 ^ k)`. -/
theorem four_mul_ncard_three_pow_mul_lt_norm_sum_div_le [NormedSpace ℝ E] (x : ι → E) (t : ℝ)
    (k : ℕ) :
    4 * (({ε : ι → ℤˣ | 3 ^ k * t < ‖∑ i, ε i • x i‖}.ncard : ℝ) / 2 ^ Fintype.card ι) ≤
      (4 * (({ε : ι → ℤˣ | t < ‖∑ i, ε i • x i‖}.ncard : ℝ) / 2 ^ Fintype.card ι)) ^
        (2 ^ k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hstep := ncard_three_mul_lt_norm_sum_div_le x (3 ^ k * t)
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
