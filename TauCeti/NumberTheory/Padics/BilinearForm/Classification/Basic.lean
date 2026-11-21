/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
public import TauCeti.NumberTheory.Padics.BilinearForm.JordanGaussSum
import TauCeti.Analysis.SpecialFunctions.Complex.CircleAddChar
import TauCeti.LinearAlgebra.BilinearForm.JordanSplitting.Parity
import TauCeti.LinearAlgebra.BilinearForm.Orthogonal
import TauCeti.NumberTheory.Padics.BilinearForm.Classification.Compartment
import TauCeti.NumberTheory.Padics.BilinearForm.Classification.NoAdjacentOdd
import TauCeti.NumberTheory.Padics.BilinearForm.SignWalking
import TauCeti.NumberTheory.Padics.PadicIntegers
import TauCeti.NumberTheory.Padics.SerreSigns
import TauCeti.Order.Interval.Finset.Basic

/-!
# Classification of symmetric bilinear forms over `ℤ_[2]`

Two symmetric bilinear forms `B` and `B'` on finite free `ℤ_[2]`-modules with Jordan splittings
`N` and `N'` with respect to `2` are isometric if and only if:

1. `N i` and `N' i` have equal rank at every scale `i`;
2. `N i` and `N' i` have the same parity type (type I or type II) at every scale `i`;
3. at every scale `j` where `N (j + 1)` is of type II (including `N (j + 1) = ⊥`), the partial
   residue invariant `LinearMap.BilinForm.IsJordanSplitting.partialOddity` modulo `8` (equivalently,
   its `stdAddChar` image) agrees for `B` and `B'`.

## Main results

* `LinearMap.BilinForm.IsJordanSplitting.exists_constituentSign_and_oddity_eq`: normalizing signs
  and oddities across all scales simultaneously.
* `LinearMap.BilinForm.IsJordanSplitting.equivalent_iff_partialOddity_eq`:
  complete classification of symmetric bilinear forms over `ℤ_[2]` via partial oddities modulo `8`.
* `LinearMap.BilinForm.IsJordanSplitting.equivalent_iff_stdAddChar_partialOddity_eq`:
  the Gauss-sum formulation obtained by applying `ZMod.stdAddChar`.

## References

* O. T. O'Meara, *Introduction to Quadratic Forms*, §93.
* J. W. S. Cassels, *Rational Quadratic Forms*, Chapter 8, §4.
* J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, Chapter 15, §7.
-/

public section

open Module ZMod
open LinearMap (BilinForm)

namespace LinearMap.BilinForm

/-! ### Compartment sums and boundary invariants -/

section PartialInvariants

private def compSum (s : ℕ → ℤ) (t : ℕ → ZMod (2 ^ 3)) (c d : ℕ) : ZMod (2 ^ 3) :=
  ∑ i ∈ Finset.Icc c d, (t i + if Odd (d + 1 - i) ∧ s i = -1 then 4 else 0)

private theorem partialOddity_eq_sum_Iio_add_compSum
    {M : Type*} [AddCommGroup M] [Module ℤ_[2] M] [Module.Free ℤ_[2] M]
    [Module.Finite ℤ_[2] M] {B : BilinForm ℤ_[2] M} {N : ℕ → Submodule ℤ_[2] M}
    (h : B.IsJordanSplitting 2 N) (hB : B.IsSymm) {c d : ℕ} (hcd : c ≤ d) :
    h.partialOddity hB d =
      (∑ i ∈ Finset.Iio c, (h.constituentOddity hB i +
        if Odd (d + 1 - i) ∧ h.constituentSign i = -1 then 4 else 0)) +
      compSum h.constituentSign (h.constituentOddity hB) c d := by
  rw [h.partialOddity_def, compSum, ← Finset.sum_union (Finset.Iio_disjoint_Icc le_rfl),
    Finset.Iio_union_Icc_eq_Iic hcd]

private theorem partialOddity_succ_sub_partialOddity_of_eq_bot
    {M : Type*} [AddCommGroup M] [Module ℤ_[2] M] [Module.Free ℤ_[2] M]
    [Module.Finite ℤ_[2] M] {B : BilinForm ℤ_[2] M} {N : ℕ → Submodule ℤ_[2] M}
    (h : B.IsJordanSplitting 2 N) (hB : B.IsSymm) {j : ℕ} (hbot : N (j + 1) = ⊥) :
    h.partialOddity hB (j + 1) - h.partialOddity hB j =
      ∑ i ∈ Finset.Iic j, if h.constituentSign i = -1 then (4 : ZMod (2 ^ 3)) else 0 := by
  rw [h.partialOddity_def, h.partialOddity_def]
  have hIic : Finset.Iic (j + 1) = insert (j + 1) (Finset.Iic j) := by
    rw [Finset.Iic_eq_Icc, Finset.Iic_eq_Icc, ← Order.succ_eq_add_one,
      Finset.insert_Icc_right_eq_Icc_succ bot_le]
  have hnotMem : j + 1 ∉ Finset.Iic j := by simp [Finset.mem_Iic]
  have h1m1 : (1 : ℤ) ≠ -1 := by decide
  have hm4 : -(4 : ZMod (2 ^ 3)) = 4 := by decide
  rw [hIic, Finset.sum_insert hnotMem, h.constituentSign_of_eq_bot hbot,
    h.constituentOddity_of_eq_bot hB hbot]
  simp only [h1m1, and_false, ↓reduceIte, add_zero, zero_add, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  have hij : i ≤ j := Finset.mem_Iic.mp hi
  have hsub : j + 1 + 1 - i = (j + 1 - i) + 1 := by omega
  have hpar : Odd (j + 1 + 1 - i) ↔ ¬Odd (j + 1 - i) := by rw [hsub, Nat.odd_add_one]
  by_cases hsi : h.constituentSign i = -1
  · by_cases ho : Odd (j + 1 - i)
    · simp only [hsi, ho, hpar.not.mpr (not_not.mpr ho), and_true, ↓reduceIte, add_zero,
        sub_add_eq_sub_sub, sub_self, zero_sub, hm4]
    · simp only [hsi, ho, hpar.mpr ho, and_true, ↓reduceIte, add_zero, add_sub_cancel_left]
  · simp [hsi]

private theorem prod_constituentSign_eq_of_eq_bot_of_even
    {M M' : Type*} [AddCommGroup M] [Module ℤ_[2] M] [Module.Free ℤ_[2] M]
    [Module.Finite ℤ_[2] M] [AddCommGroup M'] [Module ℤ_[2] M'] [Module.Free ℤ_[2] M']
    [Module.Finite ℤ_[2] M'] {B : BilinForm ℤ_[2] M} {B' : BilinForm ℤ_[2] M'}
    {N : ℕ → Submodule ℤ_[2] M} {N' : ℕ → Submodule ℤ_[2] M'}
    (h : B.IsJordanSplitting 2 N) (h' : B'.IsJordanSplitting 2 N')
    (hB : B.IsSymm) (hB' : B'.IsSymm) {k d : ℕ} (hkd : k ≤ d)
    (hmatch : ∀ i < k, h.constituentSign i = h'.constituentSign i)
    (hbot : N (d + 1) = ⊥) (hbot' : N' (d + 1) = ⊥)
    (hGd : h.partialOddity hB d = h'.partialOddity hB' d)
    (hGd1 : h.partialOddity hB (d + 1) = h'.partialOddity hB' (d + 1)) :
    ∏ i ∈ Finset.Icc k d, h.constituentSign i = ∏ i ∈ Finset.Icc k d, h'.constituentSign i := by
  have hdiff : (∑ i ∈ Finset.Iic d,
        if h.constituentSign i = -1 then (4 : ZMod (2 ^ 3)) else 0) =
      ∑ i ∈ Finset.Iic d,
        if h'.constituentSign i = -1 then (4 : ZMod (2 ^ 3)) else 0 := by
    rw [← partialOddity_succ_sub_partialOddity_of_eq_bot h hB hbot,
      ← partialOddity_succ_sub_partialOddity_of_eq_bot h' hB' hbot', hGd, hGd1]
  rw [← Finset.Iio_union_Icc_eq_Iic hkd, Finset.sum_union (Finset.Iio_disjoint_Icc le_rfl),
    Finset.sum_union (Finset.Iio_disjoint_Icc le_rfl)] at hdiff
  have hpre : ∑ i ∈ Finset.Iio k,
        (if h.constituentSign i = -1 then (4 : ZMod (2 ^ 3)) else 0) =
      ∑ i ∈ Finset.Iio k,
        (if h'.constituentSign i = -1 then (4 : ZMod (2 ^ 3)) else 0) :=
    Finset.sum_congr rfl fun i hi ↦ by rw [hmatch i (Finset.mem_Iio.mp hi)]
  rw [hpre] at hdiff
  rw [h.prod_constituentSign_eq_ite, h'.prod_constituentSign_eq_ite, add_left_cancel hdiff]

private theorem flip_end_Icc {s s1 : ℕ → ℤ} {t t1 : ℕ → ZMod (2 ^ 3)} {k d : ℕ}
    (hkd : k ≤ d) (hsd_pm : s d = 1 ∨ s d = -1) (hlt : ∀ i < d, s1 i = s i ∧ t1 i = t i)
    (hsd : s1 d = -s d) (htd : t1 d = t d + 4) :
    compSum s1 t1 k d = compSum s t k d ∧
    ∏ i ∈ Finset.Icc k d, s1 i = -(∏ i ∈ Finset.Icc k d, s i) := by
  have hd_mem := Finset.mem_Icc.mpr ⟨hkd, le_rfl⟩
  have hlt' : ∀ i ∈ (Finset.Icc k d).erase d, s1 i = s i ∧ t1 i = t i := fun i hi ↦ by
    rw [Finset.mem_erase, Finset.mem_Icc] at hi; exact hlt i (by omega)
  have h1m1 : (1 : ℤ) ≠ -1 := by decide
  have h44 : (4 : ZMod (2 ^ 3)) + 4 = 0 := by decide
  refine ⟨?_, ?_⟩
  · unfold compSum
    rw [← Finset.add_sum_erase _ _ hd_mem, ← Finset.add_sum_erase _ _ hd_mem,
      Finset.sum_congr rfl fun i hi ↦ by rw [(hlt' i hi).1, (hlt' i hi).2], hsd, htd,
      Nat.add_sub_cancel_left]
    congr 1
    rcases hsd_pm with h | h <;> rw [h] <;>
      simp only [odd_one, true_and, neg_neg, h1m1, ↓reduceIte, add_zero]
    rw [add_assoc, h44, add_zero]
  · rw [← Finset.mul_prod_erase _ _ hd_mem, ← Finset.mul_prod_erase _ _ hd_mem,
      Finset.prod_congr rfl fun i hi ↦ (hlt' i hi).1, hsd, neg_mul]

end PartialInvariants

/-! ### Left-to-right sweep and Jordan splitting normalization -/

section Normalization

variable {M : Type*} [AddCommGroup M] [Module ℤ_[2] M] [Module.Free ℤ_[2] M]
  [Module.Finite ℤ_[2] M] {B : BilinForm ℤ_[2] M} {N : ℕ → Submodule ℤ_[2] M}

private theorem constituentSign_eq_neg_of_isSquare_five {N' : ℕ → Submodule ℤ_[2] M}
    (h : B.IsJordanSplitting 2 N) (h' : B.IsJordanSplitting 2 N') {k : ℕ}
    (hdk : ∀ (n : ℕ) (d : Basis (Fin n) ℤ_[2] (N k)) (d' : Basis (Fin n) ℤ_[2] (N' k)),
      IsSquare (5 * ((B.restrict (N k)).toMatrix d).det * ((B.restrict (N' k)).toMatrix d').det)) :
    h'.constituentSign k = -h.constituentSign k := by
  have hsk := h.constituentSign_eq_mul_of_isSquare_det h' TauCeti.isUnit_five_padicInt hdk
  have hχ5 : χ₈ (PadicInt.toZModPow 3 (5 : ℤ_[2])) = -1 := by rw [map_ofNat]; decide
  rwa [hχ5, neg_one_mul] at hsk

/-- **Left-to-right sweep.** For every `k`, there exists a Jordan splitting of `B` matching the
signs and oddities of `h'` at every index `i < k`. -/
private theorem exists_isJordanSplitting_matching_below
    {M' : Type*} [AddCommGroup M'] [Module ℤ_[2] M'] [Module.Free ℤ_[2] M']
    [Module.Finite ℤ_[2] M'] {B' : BilinForm ℤ_[2] M'} {N' : ℕ → Submodule ℤ_[2] M'}
    (h : B.IsJordanSplitting 2 N) (h' : B'.IsJordanSplitting 2 N')
    (hB : B.IsSymm) (hB' : B'.IsSymm)
    (hrank : ∀ i, finrank ℤ_[2] (N i) = finrank ℤ_[2] (N' i))
    (hpar : ∀ i, (∀ v ∈ N i, 2 * 2 ^ i ∣ B v v) ↔ ∀ v ∈ N' i, 2 * 2 ^ i ∣ B' v v)
    (hinv : ∀ j, (∀ v ∈ N (j + 1), 2 * 2 ^ (j + 1) ∣ B v v) →
      h.partialOddity hB j = h'.partialOddity hB' j) :
    ∀ k : ℕ, ∃ N'' : ℕ → Submodule ℤ_[2] M, ∃ h'' : B.IsJordanSplitting 2 N'',
      ∀ i < k, h''.constituentSign i = h'.constituentSign i ∧
        h''.constituentOddity hB i = h'.constituentOddity hB' i := by
  intro k
  induction k with
  | zero => exact ⟨N, h, fun i hi ↦ absurd hi (Nat.not_lt_zero i)⟩
  | succ k ih =>
    obtain ⟨Nk, hk, hmatch⟩ := ih
    have h2nz : (2 : ℤ_[2]) ∈ nonZeroDivisors ℤ_[2] := mem_nonZeroDivisors_of_ne_zero two_ne_zero
    have hrank_k (i) := (hk.finrank_eq h two_ne_zero PadicInt.not_isUnit_two i).trans (hrank i)
    have hpar_k (i) :=
      (hk.forall_two_mul_pow_dvd_iff_of_isJordanSplitting h h2nz dvd_rfl i).trans (hpar i)
    have hbot_iff (i) : Nk i = ⊥ ↔ N' i = ⊥ := by
      have := hk.finite i; have := h'.finite i
      rw [← Submodule.finrank_eq_zero, ← Submodule.finrank_eq_zero, hrank_k i]
    have hinv_k (j) (hj : ∀ v ∈ Nk (j + 1), 2 * 2 ^ (j + 1) ∣ B v v) :
        hk.partialOddity hB j = h'.partialOddity hB' j :=
      have hjN := (hk.forall_two_mul_pow_dvd_iff_of_isJordanSplitting h h2nz dvd_rfl (j + 1)).mp hj
      (h.partialOddity_eq_of_isJordanSplitting hk hB hjN).symm.trans (hinv j hjN)
    have hIcc_eq (d) (hkd : k ≤ d) (heven_d1 : ∀ v ∈ Nk (d + 1), 2 * 2 ^ (d + 1) ∣ B v v) :
        compSum hk.constituentSign (hk.constituentOddity hB) k d =
          compSum h'.constituentSign (h'.constituentOddity hB') k d := by
      have hGd := hinv_k d heven_d1
      rw [partialOddity_eq_sum_Iio_add_compSum hk hB hkd,
        partialOddity_eq_sum_Iio_add_compSum h' hB' hkd] at hGd
      have hpre : ∑ i ∈ Finset.Iio k, (hk.constituentOddity hB i +
            if Odd (d + 1 - i) ∧ hk.constituentSign i = -1 then 4 else 0) =
          ∑ i ∈ Finset.Iio k, (h'.constituentOddity hB' i +
            if Odd (d + 1 - i) ∧ h'.constituentSign i = -1 then 4 else 0) :=
        Finset.sum_congr rfl fun i hi ↦ by
          obtain ⟨hs, ht⟩ := hmatch i (Finset.mem_Iio.mp hi); rw [hs, ht]
      exact add_left_cancel (hpre ▸ hGd)
    have hsucc_of_eq {N1 : ℕ → Submodule ℤ_[2] M} (h1 : B.IsJordanSplitting 2 N1)
        (hlt : ∀ i < k, N1 i = Nk i)
        (hk_eq : h1.constituentSign k = h'.constituentSign k ∧
          h1.constituentOddity hB k = h'.constituentOddity hB' k) :
        ∃ N'' : ℕ → Submodule ℤ_[2] M, ∃ h'' : B.IsJordanSplitting 2 N'',
          ∀ i < k + 1, h''.constituentSign i = h'.constituentSign i ∧
            h''.constituentOddity hB i = h'.constituentOddity hB' i := by
      refine ⟨N1, h1, fun i hi ↦ ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
      · exact ⟨(hk.constituentSign_eq_of_eq h1 (hlt i hi)).trans (hmatch i hi).1,
          (hk.constituentOddity_eq_of_eq h1 hB (hlt i hi)).trans (hmatch i hi).2⟩
      · exact hk_eq
    by_cases heven_k : ∀ v ∈ Nk k, 2 * 2 ^ k ∣ B v v
    · -- Case 1: `Nk k` is of type II.
      have htk := hk.constituentOddity_of_even hB heven_k
      have ht'k := h'.constituentOddity_of_even hB' ((hpar_k k).mp heven_k)
      by_cases hbot_k : Nk k = ⊥
      · exact hsucc_of_eq hk (fun _ _ ↦ rfl)
          ⟨(hk.constituentSign_of_eq_bot hbot_k).trans
            (h'.constituentSign_of_eq_bot ((hbot_iff k).mp hbot_k)).symm, htk.trans ht'k.symm⟩
      · by_cases heven_next : ∀ v ∈ Nk (k + 1), 2 * 2 ^ (k + 1) ∣ B v v
        · have hcomp := hIcc_eq k le_rfl heven_next
          simp only [compSum, Finset.Icc_self, Finset.sum_singleton, Nat.add_sub_cancel_left,
            odd_one, true_and, htk, ht'k, zero_add] at hcomp
          have hsk : hk.constituentSign k = h'.constituentSign k := by
            rcases hk.constituentSign_eq_one_or_neg_one k with h1 | h1 <;>
              rcases h'.constituentSign_eq_one_or_neg_one k with h2 | h2 <;>
              rw [h1, h2] at hcomp ⊢ <;> exact absurd hcomp (by decide)
          exact hsucc_of_eq hk (fun _ _ ↦ rfl) ⟨hsk, htk.trans ht'k.symm⟩
        · by_cases hsk : hk.constituentSign k = h'.constituentSign k
          · exact hsucc_of_eq hk (fun _ _ ↦ rfl) ⟨hsk, htk.trans ht'k.symm⟩
          · obtain ⟨N1, h1, hagree1, hdk, -, -⟩ :=
              hk.exists_signWalk_succ_of_even_of_odd hB heven_k hbot_k heven_next
            have hs1k := constituentSign_eq_neg_of_isSquare_five hk h1 hdk
            have heven1 :=
              (hk.forall_two_mul_pow_dvd_iff_of_isJordanSplitting h1 h2nz dvd_rfl k).mp heven_k
            have hpm1 := hk.constituentSign_eq_one_or_neg_one k
            have hpm2 := h'.constituentSign_eq_one_or_neg_one k
            exact hsucc_of_eq h1 (fun i hi ↦ hagree1 i (by omega) (by omega))
              ⟨by omega, (h1.constituentOddity_of_even hB heven1).trans ht'k.symm⟩
    · -- Case 2: `Nk k` is of type I. Find the end `d ≥ k` of its type-I compartment.
      classical
      have hex : ∃ d, k ≤ d ∧ ∀ v ∈ Nk (d + 1), 2 * 2 ^ (d + 1) ∣ B v v := by
        obtain ⟨m, hm⟩ := hk.hasFiniteSupport.bddAbove
        refine ⟨max k m, le_max_left k m, fun v hv ↦ ?_⟩
        have hbot : Nk (max k m + 1) = ⊥ := by by_contra hne; have := hm hne; omega
        rw [hbot, Submodule.mem_bot] at hv; simp [hv]
      let d := Nat.find hex
      have hkd : k ≤ d := (Nat.find_spec hex).1
      have heven_d1 := (Nat.find_spec hex).2
      have hodd_block : ∀ i ∈ Finset.Icc k d, ¬∀ v ∈ Nk i, 2 * 2 ^ i ∣ B v v :=
        fun i hi ↦ by
          rw [Finset.mem_Icc] at hi
          rcases eq_or_lt_of_le hi.1 with rfl | hki
          · exact heven_k
          · have him1 : i - 1 < d := by omega
            have hge : k ≤ i - 1 := by omega
            have hsucc : i - 1 + 1 = i := by omega
            exact fun he ↦ Nat.find_min hex him1 ⟨hge, by simpa only [hsucc] using he⟩
      have hTd := hIcc_eq d hkd heven_d1
      -- Align the compartment sign product on `[k, d]` without disturbing `i < k` or `hTd`.
      obtain ⟨N1, h1, hagree1, hT1, hS1⟩ : ∃ N1, ∃ h1 : B.IsJordanSplitting 2 N1,
          (∀ i < k, N1 i = Nk i) ∧
          compSum h1.constituentSign (h1.constituentOddity hB) k d =
            compSum h'.constituentSign (h'.constituentOddity hB') k d ∧
          ∏ i ∈ Finset.Icc k d, h1.constituentSign i =
            ∏ i ∈ Finset.Icc k d, h'.constituentSign i := by
        by_cases hSd : ∏ i ∈ Finset.Icc k d, hk.constituentSign i =
            ∏ i ∈ Finset.Icc k d, h'.constituentSign i
        · exact ⟨Nk, hk, fun _ _ ↦ rfl, hTd, hSd⟩
        · have hodd_d := hodd_block d (Finset.mem_Icc.mpr ⟨hkd, le_rfl⟩)
          obtain ⟨N1, h1, hlt, hsd, htd⟩ : ∃ N1, ∃ h1 : B.IsJordanSplitting 2 N1,
              (∀ i < d, N1 i = Nk i) ∧
              h1.constituentSign d = -hk.constituentSign d ∧
              h1.constituentOddity hB d = hk.constituentOddity hB d + 4 := by
            by_cases hbot_d1 : Nk (d + 1) = ⊥
            · by_cases heven_d2 : ∀ v ∈ Nk (d + 2), 2 * 2 ^ (d + 2) ∣ B v v
              · exact absurd (prod_constituentSign_eq_of_eq_bot_of_even hk h' hB hB' hkd
                    (fun i hi ↦ (hmatch i hi).1) hbot_d1 ((hbot_iff (d + 1)).mp hbot_d1)
                    (hinv_k d heven_d1) (hinv_k (d + 1) heven_d2))
                  hSd
              · obtain ⟨N1, h1, ha, hdk, -, hok, -⟩ :=
                  hk.exists_signWalk_add_two_of_odd_of_odd hB hodd_d heven_d2
                exact ⟨N1, h1, fun i hi ↦ ha i (by omega) (by omega),
                  constituentSign_eq_neg_of_isSquare_five hk h1 hdk,
                  by simpa [map_ofNat] using hk.constituentOddity_eq_add_of_eight_dvd h1 hB
                        (δ := 4) hok⟩
            · obtain ⟨N1, h1, ha, hdk, -, hok⟩ :=
                hk.exists_signWalk_succ_of_odd_of_even hB hodd_d heven_d1 hbot_d1
              exact ⟨N1, h1, fun i hi ↦ ha i (by omega) (by omega),
                constituentSign_eq_neg_of_isSquare_five hk h1 hdk,
                by simpa [map_ofNat] using hk.constituentOddity_eq_add_of_eight_dvd h1 hB
                      (δ := 4) hok⟩
          obtain ⟨hT1, hP1⟩ := flip_end_Icc hkd (hk.constituentSign_eq_one_or_neg_one d)
            (fun i hi ↦ ⟨hk.constituentSign_eq_of_eq h1 (hlt i hi),
              hk.constituentOddity_eq_of_eq h1 hB (hlt i hi)⟩) hsd htd
          have := hk.prod_constituentSign_eq_ite (Finset.Icc k d)
          have := h'.prod_constituentSign_eq_ite (Finset.Icc k d)
          refine ⟨N1, h1, fun i hi ↦ hlt i (by omega), hT1.trans hTd, ?_⟩
          split_ifs at * <;> omega
      obtain ⟨N2, h2, hagree2, hmatch2⟩ :=
        h1.exists_constituentSign_and_oddity_eq_on_Icc h' hB hB'
          (fun i _ ↦ (h1.finrank_eq hk two_ne_zero PadicInt.not_isUnit_two i).trans (hrank_k i))
          (fun i hi ↦ by
            rw [h1.forall_two_mul_pow_dvd_iff_of_isJordanSplitting hk h2nz dvd_rfl i]
            exact hodd_block i hi)
          (fun i hi ↦ by rw [← hpar_k i]; exact hodd_block i hi) hT1 hS1
      exact hsucc_of_eq h2
        (fun i hi ↦ (hagree2 i (by simp only [Finset.mem_Icc]; omega)).trans (hagree1 i hi))
        (hmatch2 k (Finset.mem_Icc.mpr ⟨le_rfl, hkd⟩))

/-- **Jordan splitting normalization over `ℤ_[2]`.** If Jordan splittings `N` and `N'` of
symmetric forms `B` and `B'` over `ℤ_[2]` have the same constituent ranks, parity types, and
partial invariants at every scale followed by a type-II constituent, then `B` admits a Jordan
splitting `N''` whose constituent signs and oddities match those of `N'` at every scale. -/
theorem IsJordanSplitting.exists_constituentSign_and_oddity_eq
    {M' : Type*} [AddCommGroup M'] [Module ℤ_[2] M'] [Module.Free ℤ_[2] M']
    [Module.Finite ℤ_[2] M'] {B' : BilinForm ℤ_[2] M'} {N' : ℕ → Submodule ℤ_[2] M'}
    (h : B.IsJordanSplitting 2 N) (h' : B'.IsJordanSplitting 2 N')
    (hB : B.IsSymm) (hB' : B'.IsSymm)
    (hrank : ∀ i, finrank ℤ_[2] (N i) = finrank ℤ_[2] (N' i))
    (hpar : ∀ i, (∀ v ∈ N i, 2 * 2 ^ i ∣ B v v) ↔ ∀ v ∈ N' i, 2 * 2 ^ i ∣ B' v v)
    (hinv : ∀ j, (∀ v ∈ N (j + 1), 2 * 2 ^ (j + 1) ∣ B v v) →
      h.partialOddity hB j = h'.partialOddity hB' j) :
    ∃ N'' : ℕ → Submodule ℤ_[2] M, ∃ h'' : B.IsJordanSplitting 2 N'',
      ∀ i, h''.constituentSign i = h'.constituentSign i ∧
        h''.constituentOddity hB i = h'.constituentOddity hB' i := by
  obtain ⟨b, hb⟩ := h.hasFiniteSupport.bddAbove
  obtain ⟨N'', h'', hmatch⟩ :=
    exists_isJordanSplitting_matching_below h h' hB hB' hrank hpar hinv (b + 1)
  refine ⟨N'', h'', fun i ↦ ?_⟩
  by_cases him : i < b + 1
  · exact hmatch i him
  · have hbotN : N i = ⊥ := by by_contra hne; have := hb hne; omega
    have := h''.finite i; have := h'.finite i
    have hbotN'' : N'' i = ⊥ := Submodule.finrank_eq_zero.mp
      (by rw [h''.finrank_eq h two_ne_zero PadicInt.not_isUnit_two i, hbotN, finrank_bot])
    have hbotN' : N' i = ⊥ :=
      Submodule.finrank_eq_zero.mp (by rw [← hrank i, hbotN, finrank_bot])
    exact ⟨(h''.constituentSign_of_eq_bot hbotN'').trans
        (h'.constituentSign_of_eq_bot hbotN').symm,
      (h''.constituentOddity_of_eq_bot hB hbotN'').trans
        (h'.constituentOddity_of_eq_bot hB' hbotN').symm⟩

end Normalization

/-! ### Complete classification of symmetric bilinear forms over `ℤ_[2]` -/

section Classification

variable {M : Type*} [AddCommGroup M] [Module ℤ_[2] M] [Module.Free ℤ_[2] M]
  [Module.Finite ℤ_[2] M] {B : BilinForm ℤ_[2] M} {N : ℕ → Submodule ℤ_[2] M}

/-- **Classification of symmetric bilinear forms over `ℤ_[2]` via Jordan splittings (`ZMod 8`
partial residue form).** Symmetric forms `B` and `B'` on finite free `ℤ_[2]`-modules with Jordan
splittings `N` and `N'` with respect to `2` are isometric if and only if their constituents have
equal ranks and parity types at every scale, and their partial residues
`LinearMap.BilinForm.IsJordanSplitting.partialOddity` agree modulo `8` at every scale `j` with
`N (j + 1)` of type II. -/
theorem IsJordanSplitting.equivalent_iff_partialOddity_eq
    {M' : Type*} [AddCommGroup M'] [Module ℤ_[2] M'] [Module.Free ℤ_[2] M']
    [Module.Finite ℤ_[2] M'] {B' : BilinForm ℤ_[2] M'} {N' : ℕ → Submodule ℤ_[2] M'}
    (h : B.IsJordanSplitting 2 N) (h' : B'.IsJordanSplitting 2 N')
    (hB : B.IsSymm) (hB' : B'.IsSymm) :
    B.Equivalent B' ↔
      (∀ i, finrank ℤ_[2] (N i) = finrank ℤ_[2] (N' i)) ∧
      (∀ i, (∀ v ∈ N i, 2 * 2 ^ i ∣ B v v) ↔ ∀ v ∈ N' i, 2 * 2 ^ i ∣ B' v v) ∧
      ∀ j, (∀ v ∈ N (j + 1), 2 * 2 ^ (j + 1) ∣ B v v) →
        h.partialOddity hB j = h'.partialOddity hB' j := by
  have h2nz : (2 : ℤ_[2]) ∈ nonZeroDivisors ℤ_[2] := mem_nonZeroDivisors_of_ne_zero two_ne_zero
  refine ⟨fun ⟨ε⟩ ↦ ?_, ?_⟩
  · exact ⟨fun i ↦ h.finrank_eq_of_equivalent h' ⟨ε⟩ two_ne_zero PadicInt.not_isUnit_two i,
      fun i ↦ ⟨fun he ↦ h.forall_two_mul_pow_dvd_of_equivalent h' ⟨ε⟩ h2nz dvd_rfl he,
        fun he ↦ h'.forall_two_mul_pow_dvd_of_equivalent h ⟨ε.symm⟩ h2nz dvd_rfl he⟩,
      fun j hj ↦ h.partialOddity_eq_of_equivalent h' hB hB' ⟨ε⟩ hj⟩
  rintro ⟨hrank, hpar, hinv⟩
  obtain ⟨N'', h'', hmatch⟩ := h.exists_constituentSign_and_oddity_eq h' hB hB' hrank hpar hinv
  refine equivalent_of_isInternal h''.isInternal h'.isInternal h''.apply_eq_zero h'.apply_eq_zero
    fun i ↦ ?_
  have := h''.free i; have := h''.finite i; have := h'.free i; have := h'.finite i
  have hcard : Fintype.card (Fin (finrank ℤ_[2] (N'' i))) =
      Fintype.card (Fin (finrank ℤ_[2] (N' i))) := by
    simp [h''.finrank_eq h two_ne_zero PadicInt.not_isUnit_two i, hrank i]
  rw [h''.equivalent_restrict_iff h' hB hB'
    (h''.two_pow_smul_constituentForm i) (h'.two_pow_smul_constituentForm i)
    (Module.finBasis ℤ_[2] (N'' i)) (Module.finBasis ℤ_[2] (N' i)) hcard
    (h''.isCharacteristic_constituentCharVec hB i)
    (h'.isCharacteristic_constituentCharVec hB' i)]
  obtain ⟨hsign_i, hodd_i⟩ := hmatch i
  rw [h''.constituentSign_eq (h''.two_pow_smul_constituentForm i) (Module.finBasis ℤ_[2] (N'' i)),
    h'.constituentSign_eq (h'.two_pow_smul_constituentForm i)
      (Module.finBasis ℤ_[2] (N' i))] at hsign_i
  rw [h''.constituentOddity_eq hB (h''.two_pow_smul_constituentForm i)
      (h''.isCharacteristic_constituentCharVec hB i),
    h'.constituentOddity_eq hB' (h'.two_pow_smul_constituentForm i)
      (h'.isCharacteristic_constituentCharVec hB' i)] at hodd_i
  exact ⟨(h''.forall_two_mul_pow_dvd_iff_of_isJordanSplitting h h2nz dvd_rfl i).trans (hpar i),
    hsign_i, hodd_i⟩

/-- **Classification of symmetric bilinear forms over `ℤ_[2]` via Jordan splittings (Gauss-sum
form).** Obtained from `IsJordanSplitting.equivalent_iff_partialOddity_eq` by applying the standard
additive character `ZMod.stdAddChar`. -/
theorem IsJordanSplitting.equivalent_iff_stdAddChar_partialOddity_eq
    {M' : Type*} [AddCommGroup M'] [Module ℤ_[2] M'] [Module.Free ℤ_[2] M']
    [Module.Finite ℤ_[2] M'] {B' : BilinForm ℤ_[2] M'} {N' : ℕ → Submodule ℤ_[2] M'}
    (h : B.IsJordanSplitting 2 N) (h' : B'.IsJordanSplitting 2 N')
    (hB : B.IsSymm) (hB' : B'.IsSymm) :
    B.Equivalent B' ↔
      (∀ i, finrank ℤ_[2] (N i) = finrank ℤ_[2] (N' i)) ∧
      (∀ i, (∀ v ∈ N i, 2 * 2 ^ i ∣ B v v) ↔ ∀ v ∈ N' i, 2 * 2 ^ i ∣ B' v v) ∧
      ∀ j, (∀ v ∈ N (j + 1), 2 * 2 ^ (j + 1) ∣ B v v) →
        stdAddChar (h.partialOddity hB j) = stdAddChar (h'.partialOddity hB' j) := by
  rw [h.equivalent_iff_partialOddity_eq h' hB hB']
  simp only [injective_stdAddChar.eq_iff]

end Classification

end LinearMap.BilinForm
