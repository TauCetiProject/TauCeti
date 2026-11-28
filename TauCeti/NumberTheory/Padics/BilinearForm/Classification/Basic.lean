/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
public import TauCeti.NumberTheory.Padics.BilinearForm.Classification.PartialOddity
import TauCeti.Algebra.BigOperators.Ring.Finset
import TauCeti.Algebra.Group.Basic
import TauCeti.LinearAlgebra.BilinearForm.JordanSplitting.Parity
import TauCeti.LinearAlgebra.BilinearForm.Orthogonal
import TauCeti.NumberTheory.Padics.BilinearForm.Classification.Compartment
import TauCeti.NumberTheory.Padics.BilinearForm.Classification.NoAdjacentOdd
import TauCeti.NumberTheory.Padics.BilinearForm.SignWalking
import TauCeti.NumberTheory.Padics.PadicIntegers
import TauCeti.Order.Interval.Finset.Basic

/-!
# Classification of symmetric bilinear forms over `ℤ_[2]`

Two symmetric bilinear forms `B` and `B'` on finite free `ℤ_[2]`-modules with Jordan splittings
`N` and `N'` with respect to `2` are isometric if and only if:

1. `N i` and `N' i` have equal rank at every scale `i`;
2. `N i` and `N' i` have the same parity type (type I or type II) at every scale `i`;
3. at every scale `j` where `N (j + 1)` is of type II (including `N (j + 1) = ⊥`), the partial
   signed oddity invariant `LinearMap.BilinForm.IsJordanSplitting.partialSignedOddity` modulo `8`
   (equivalently, its `stdAddChar` image) agrees for `B` and `B'`.

## Main results

* `LinearMap.BilinForm.IsJordanSplitting.exists_constituentSign_and_oddity_eq`: normalizing signs
  and oddities across all scales simultaneously.
* `LinearMap.BilinForm.IsJordanSplitting.equivalent_iff_partialSignedOddity_eq`:
  complete classification of symmetric bilinear forms over `ℤ_[2]` via partial signed oddities
  modulo `8`.
* `LinearMap.BilinForm.IsJordanSplitting.equivalent_iff_stdAddChar_partialSignedOddity_eq`:
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

private theorem partialSignedOddity_eq_sum_Iio_add_compartmentSignedOddity
    {M : Type*} [AddCommGroup M] [Module ℤ_[2] M] [Module.Free ℤ_[2] M]
    [Module.Finite ℤ_[2] M] {B : BilinForm ℤ_[2] M} {N : ℕ → Submodule ℤ_[2] M}
    (h : B.IsJordanSplitting 2 N) (hB : B.IsSymm) {c d : ℕ} (hcd : c ≤ d) :
    h.partialSignedOddity hB d =
      (∑ i ∈ Finset.Iio c, (h.constituentOddity hB i +
        if Odd (d + 1 - i) ∧ h.constituentSign i = -1 then 4 else 0)) +
      compartmentSignedOddity h.constituentSignBool (h.constituentOddity hB) c d := by
  rw [h.partialSignedOddity_def, compartmentSignedOddity_constituentSignBool,
    ← Finset.sum_union (Finset.Iio_disjoint_Icc le_rfl), Finset.Iio_union_Icc_eq_Iic hcd]

private theorem prod_constituentSign_eq_of_eq_bot_of_even
    {M M' : Type*} [AddCommGroup M] [Module ℤ_[2] M] [Module.Free ℤ_[2] M]
    [Module.Finite ℤ_[2] M] [AddCommGroup M'] [Module ℤ_[2] M'] [Module.Free ℤ_[2] M']
    [Module.Finite ℤ_[2] M'] {B : BilinForm ℤ_[2] M} {B' : BilinForm ℤ_[2] M'}
    {N : ℕ → Submodule ℤ_[2] M} {N' : ℕ → Submodule ℤ_[2] M'}
    (h : B.IsJordanSplitting 2 N) (h' : B'.IsJordanSplitting 2 N')
    (hB : B.IsSymm) (hB' : B'.IsSymm) {k d : ℕ} (hkd : k ≤ d)
    (hmatch : ∀ i < k, h.constituentSign i = h'.constituentSign i)
    (hbot : N (d + 1) = ⊥) (hbot' : N' (d + 1) = ⊥)
    (hGd : h.partialSignedOddity hB d = h'.partialSignedOddity hB' d)
    (hGd1 : h.partialSignedOddity hB (d + 1) = h'.partialSignedOddity hB' (d + 1)) :
    ∏ i ∈ Finset.Icc k d, h.constituentSign i = ∏ i ∈ Finset.Icc k d, h'.constituentSign i := by
  have hdiff : (∑ i ∈ Finset.Iic d,
        if h.constituentSign i = -1 then (4 : ZMod (2 ^ 3)) else 0) =
      ∑ i ∈ Finset.Iic d,
        if h'.constituentSign i = -1 then (4 : ZMod (2 ^ 3)) else 0 := by
    rw [← h.partialSignedOddity_succ_sub_partialSignedOddity_of_eq_bot hB hbot,
      ← h'.partialSignedOddity_succ_sub_partialSignedOddity_of_eq_bot hB' hbot', hGd, hGd1]
  rw [← Finset.Iio_union_Icc_eq_Iic hkd, Finset.sum_union (Finset.Iio_disjoint_Icc le_rfl),
    Finset.sum_union (Finset.Iio_disjoint_Icc le_rfl)] at hdiff
  have hpre : ∑ i ∈ Finset.Iio k,
        (if h.constituentSign i = -1 then (4 : ZMod (2 ^ 3)) else 0) =
      ∑ i ∈ Finset.Iio k,
        (if h'.constituentSign i = -1 then (4 : ZMod (2 ^ 3)) else 0) :=
    Finset.sum_congr rfl fun i hi ↦ by rw [hmatch i (Finset.mem_Iio.mp hi)]
  rw [hpre] at hdiff
  rw [h.prod_constituentSign_eq_ite, h'.prod_constituentSign_eq_ite, add_left_cancel hdiff]

private theorem flip_end_Icc {M : Type*} [AddCommGroup M] [Module ℤ_[2] M]
    [Module.Free ℤ_[2] M] [Module.Finite ℤ_[2] M] {B : BilinForm ℤ_[2] M}
    {Nk N1 : ℕ → Submodule ℤ_[2] M} (hk : B.IsJordanSplitting 2 Nk)
    (h1 : B.IsJordanSplitting 2 N1) (hB : B.IsSymm) {k d : ℕ} (hkd : k ≤ d)
    (hlt : ∀ i < d, N1 i = Nk i) (hsd : h1.constituentSign d = -hk.constituentSign d)
    (htd : h1.constituentOddity hB d = hk.constituentOddity hB d + 4) :
    compartmentSignedOddity h1.constituentSignBool (h1.constituentOddity hB) k d =
      compartmentSignedOddity hk.constituentSignBool (hk.constituentOddity hB) k d ∧
    ∏ i ∈ Finset.Icc k d, h1.constituentSign i =
      -(∏ i ∈ Finset.Icc k d, hk.constituentSign i) := by
  have hd_mem := Finset.mem_Icc.mpr ⟨hkd, le_rfl⟩
  refine ⟨compartmentSignedOddity_eq_of_flip_right
    (fun i hi ↦ ⟨hk.constituentSignBool_eq_of_eq h1 (hlt i hi),
      hk.constituentOddity_eq_of_eq h1 hB (hlt i hi)⟩)
    (hk.constituentSignBool_eq_not_of_constituentSign_eq_neg h1 hsd) htd, ?_⟩
  rw [← Finset.mul_prod_erase _ _ hd_mem, ← Finset.mul_prod_erase _ _ hd_mem, hsd, neg_mul]
  congr 2
  refine Finset.prod_congr rfl fun i hi ↦ ?_
  rw [Finset.mem_erase, Finset.mem_Icc] at hi
  exact hk.constituentSign_eq_of_eq h1 (hlt i (lt_of_le_of_ne hi.2.2 hi.1))

end PartialInvariants

/-! ### Left-to-right sweep and Jordan splitting normalization -/

section Normalization

variable {M : Type*} [AddCommGroup M] [Module ℤ_[2] M] [Module.Free ℤ_[2] M]
  [Module.Finite ℤ_[2] M] {B : BilinForm ℤ_[2] M}

private theorem compartmentSignedOddity_eq_of_match_below
    {M' : Type*} [AddCommGroup M'] [Module ℤ_[2] M'] [Module.Free ℤ_[2] M']
    [Module.Finite ℤ_[2] M'] {B' : BilinForm ℤ_[2] M'} {Nk : ℕ → Submodule ℤ_[2] M}
    {N' : ℕ → Submodule ℤ_[2] M'} (hk : B.IsJordanSplitting 2 Nk)
    (h' : B'.IsJordanSplitting 2 N') (hB : B.IsSymm) (hB' : B'.IsSymm) {k d : ℕ}
    (hkd : k ≤ d)
    (hmatch : ∀ i < k, hk.constituentSign i = h'.constituentSign i ∧
      hk.constituentOddity hB i = h'.constituentOddity hB' i)
    (hGd : hk.partialSignedOddity hB d = h'.partialSignedOddity hB' d) :
    compartmentSignedOddity hk.constituentSignBool (hk.constituentOddity hB) k d =
      compartmentSignedOddity h'.constituentSignBool (h'.constituentOddity hB') k d := by
  rw [partialSignedOddity_eq_sum_Iio_add_compartmentSignedOddity hk hB hkd,
    partialSignedOddity_eq_sum_Iio_add_compartmentSignedOddity h' hB' hkd] at hGd
  have hpre : ∑ i ∈ Finset.Iio k, (hk.constituentOddity hB i +
        if Odd (d + 1 - i) ∧ hk.constituentSign i = -1 then 4 else 0) =
      ∑ i ∈ Finset.Iio k, (h'.constituentOddity hB' i +
        if Odd (d + 1 - i) ∧ h'.constituentSign i = -1 then 4 else 0) :=
    Finset.sum_congr rfl fun i hi ↦ by
      obtain ⟨hs, ht⟩ := hmatch i (Finset.mem_Iio.mp hi); rw [hs, ht]
  exact add_left_cancel (hpre ▸ hGd)

private theorem exists_matching_succ_of_eq
    {M' : Type*} [AddCommGroup M'] [Module ℤ_[2] M'] [Module.Free ℤ_[2] M']
    [Module.Finite ℤ_[2] M'] {B' : BilinForm ℤ_[2] M'} {Nk N1 : ℕ → Submodule ℤ_[2] M}
    {N' : ℕ → Submodule ℤ_[2] M'} (hk : B.IsJordanSplitting 2 Nk)
    (h' : B'.IsJordanSplitting 2 N') (hB : B.IsSymm) (hB' : B'.IsSymm) {k : ℕ}
    (hmatch : ∀ i < k, hk.constituentSign i = h'.constituentSign i ∧
      hk.constituentOddity hB i = h'.constituentOddity hB' i)
    (h1 : B.IsJordanSplitting 2 N1) (hlt : ∀ i < k, N1 i = Nk i)
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

/-- Type-II sweep step `k → k + 1`: when `Nk k` is even, its oddity is already `0`, and its sign
either is trivial (`Nk k = ⊥`), is forced by `partialSignedOddity k` when `Nk (k + 1)` is also even,
already matches, or is flipped by a sign walk onto the odd constituent `Nk (k + 1)`. -/
private theorem exists_matching_succ_of_even
    {M' : Type*} [AddCommGroup M'] [Module ℤ_[2] M'] [Module.Free ℤ_[2] M']
    [Module.Finite ℤ_[2] M'] {B' : BilinForm ℤ_[2] M'} {Nk : ℕ → Submodule ℤ_[2] M}
    {N' : ℕ → Submodule ℤ_[2] M'} (hk : B.IsJordanSplitting 2 Nk)
    (h' : B'.IsJordanSplitting 2 N') (hB : B.IsSymm) (hB' : B'.IsSymm) {k : ℕ}
    (hmatch : ∀ i < k, hk.constituentSign i = h'.constituentSign i ∧
      hk.constituentOddity hB i = h'.constituentOddity hB' i)
    (hbot_k : Nk k = ⊥ ↔ N' k = ⊥)
    (hpar_k : (∀ v ∈ Nk k, 2 * 2 ^ k ∣ B v v) ↔ ∀ v ∈ N' k, 2 * 2 ^ k ∣ B' v v)
    (hinv_k : (∀ v ∈ Nk (k + 1), 2 * 2 ^ (k + 1) ∣ B v v) →
      hk.partialSignedOddity hB k = h'.partialSignedOddity hB' k)
    (heven_k : ∀ v ∈ Nk k, 2 * 2 ^ k ∣ B v v) :
    ∃ N'' : ℕ → Submodule ℤ_[2] M, ∃ h'' : B.IsJordanSplitting 2 N'',
      ∀ i < k + 1, h''.constituentSign i = h'.constituentSign i ∧
        h''.constituentOddity hB i = h'.constituentOddity hB' i := by
  have htk := hk.constituentOddity_of_even hB heven_k
  have ht'k := h'.constituentOddity_of_even hB' (hpar_k.mp heven_k)
  by_cases hbot : Nk k = ⊥
  · exact exists_matching_succ_of_eq hk h' hB hB' hmatch hk (fun _ _ ↦ rfl)
      ⟨(hk.constituentSign_of_eq_bot hbot).trans
        (h'.constituentSign_of_eq_bot (hbot_k.mp hbot)).symm, htk.trans ht'k.symm⟩
  · by_cases heven_next : ∀ v ∈ Nk (k + 1), 2 * 2 ^ (k + 1) ∣ B v v
    · have hcomp := compartmentSignedOddity_eq_of_match_below hk h' hB hB' le_rfl hmatch
        (hinv_k heven_next)
      simp only [compartmentSignedOddity_def, Finset.Icc_self, Finset.sum_singleton,
        Nat.add_sub_cancel_left, odd_one, true_and, htk, ht'k, zero_add,
        IsJordanSplitting.constituentSignBool_eq_true_iff] at hcomp
      have hsk : hk.constituentSign k = h'.constituentSign k := by
        rcases hk.constituentSign_eq_one_or_neg_one k with h1 | h1 <;>
          rcases h'.constituentSign_eq_one_or_neg_one k with h2 | h2 <;>
          rw [h1, h2] at hcomp ⊢ <;> exact absurd hcomp (by decide)
      exact exists_matching_succ_of_eq hk h' hB hB' hmatch hk (fun _ _ ↦ rfl)
        ⟨hsk, htk.trans ht'k.symm⟩
    · by_cases hsk : hk.constituentSign k = h'.constituentSign k
      · exact exists_matching_succ_of_eq hk h' hB hB' hmatch hk (fun _ _ ↦ rfl)
          ⟨hsk, htk.trans ht'k.symm⟩
      · obtain ⟨N1, h1, hagree1, hdk, -, -⟩ :=
          hk.exists_signWalk_succ_of_even_of_odd hB heven_k hbot heven_next
        have hs1k := TauCeti.eq_of_eq_neg_of_ne_of_eq_one_or_neg_one
          (hk.constituentSign_eq_one_or_neg_one k) (h'.constituentSign_eq_one_or_neg_one k)
          (hk.constituentSign_eq_neg_of_isSquare_five_mul_det h1 hdk) hsk
        have heven1 := (hk.forall_two_mul_pow_dvd_iff_of_isJordanSplitting_two h1 k).mp heven_k
        exact exists_matching_succ_of_eq hk h' hB hB' hmatch h1
          (fun i hi ↦ hagree1 i (by omega) (by omega))
          ⟨hs1k, (h1.constituentOddity_of_even hB heven1).trans ht'k.symm⟩

omit [Module.Free ℤ_[2] M] in
/-- Locate the first type-II (or zero) constituent after `k`, returning the right endpoint `d ≥ k`
of the maximal type-I compartment `[k, d]`. -/
private theorem exists_compartment_end {Nk : ℕ → Submodule ℤ_[2] M}
    (hk : B.IsJordanSplitting 2 Nk) {k : ℕ} (hodd_k : ¬∀ v ∈ Nk k, 2 * 2 ^ k ∣ B v v) :
    ∃ d : ℕ, k ≤ d ∧ (∀ i ∈ Finset.Icc k d, ¬∀ v ∈ Nk i, 2 * 2 ^ i ∣ B v v) ∧
      ∀ v ∈ Nk (d + 1), 2 * 2 ^ (d + 1) ∣ B v v := by
  classical
  have hex : ∃ d, k ≤ d ∧ ∀ v ∈ Nk (d + 1), 2 * 2 ^ (d + 1) ∣ B v v := by
    obtain ⟨m, hm⟩ := hk.hasFiniteSupport.bddAbove
    refine ⟨max k m, le_max_left k m, fun v hv ↦ ?_⟩
    have hbot : Nk (max k m + 1) = ⊥ := by by_contra hne; have := hm hne; omega
    rw [hbot, Submodule.mem_bot] at hv; simp [hv]
  let d := Nat.find hex
  refine ⟨d, (Nat.find_spec hex).1, fun i hi ↦ ?_, (Nat.find_spec hex).2⟩
  rw [Finset.mem_Icc] at hi
  rcases eq_or_lt_of_le hi.1 with rfl | hki
  · exact hodd_k
  · have him1 : i - 1 < d := by omega
    have hpred : i - 1 + 1 = i := Nat.sub_add_cancel (by omega)
    exact fun he ↦ Nat.find_min hex him1 ⟨by omega, by simpa only [hpred] using he⟩

private theorem exists_flip_end_of_compartment
    {M' : Type*} [AddCommGroup M'] [Module ℤ_[2] M'] [Module.Free ℤ_[2] M']
    [Module.Finite ℤ_[2] M'] {B' : BilinForm ℤ_[2] M'} {Nk : ℕ → Submodule ℤ_[2] M}
    {N' : ℕ → Submodule ℤ_[2] M'} (hk : B.IsJordanSplitting 2 Nk)
    (h' : B'.IsJordanSplitting 2 N') (hB : B.IsSymm) (hB' : B'.IsSymm) {k d : ℕ}
    (hkd : k ≤ d) (hmatch : ∀ i < k, hk.constituentSign i = h'.constituentSign i)
    (hbot_d1 : Nk (d + 1) = ⊥ ↔ N' (d + 1) = ⊥)
    (hinv_d : hk.partialSignedOddity hB d = h'.partialSignedOddity hB' d)
    (hinv_d1 : (∀ v ∈ Nk (d + 2), 2 * 2 ^ (d + 2) ∣ B v v) →
      hk.partialSignedOddity hB (d + 1) = h'.partialSignedOddity hB' (d + 1))
    (hodd_d : ¬∀ v ∈ Nk d, 2 * 2 ^ d ∣ B v v)
    (heven_d1 : ∀ v ∈ Nk (d + 1), 2 * 2 ^ (d + 1) ∣ B v v)
    (hSd : ∏ i ∈ Finset.Icc k d, hk.constituentSign i ≠
      ∏ i ∈ Finset.Icc k d, h'.constituentSign i) :
    ∃ N1 : ℕ → Submodule ℤ_[2] M, ∃ h1 : B.IsJordanSplitting 2 N1,
      (∀ i < d, N1 i = Nk i) ∧
      h1.constituentSign d = -hk.constituentSign d ∧
      h1.constituentOddity hB d = hk.constituentOddity hB d + 4 := by
  by_cases hbot : Nk (d + 1) = ⊥
  · by_cases heven_d2 : ∀ v ∈ Nk (d + 2), 2 * 2 ^ (d + 2) ∣ B v v
    · exact absurd (prod_constituentSign_eq_of_eq_bot_of_even hk h' hB hB' hkd hmatch
          hbot (hbot_d1.mp hbot) hinv_d (hinv_d1 heven_d2))
        hSd
    · obtain ⟨N1, h1, ha, hdk, -, hok, -⟩ :=
        hk.exists_signWalk_add_two_of_odd_of_odd hB hodd_d heven_d2
      exact ⟨N1, h1, fun i hi ↦ ha i (by omega) (by omega),
        hk.constituentSign_eq_neg_of_isSquare_five_mul_det h1 hdk,
        by simpa [map_ofNat] using hk.constituentOddity_eq_add_of_eight_dvd h1 hB (δ := 4) hok⟩
  · obtain ⟨N1, h1, ha, hdk, -, hok⟩ :=
      hk.exists_signWalk_succ_of_odd_of_even hB hodd_d heven_d1 hbot
    exact ⟨N1, h1, fun i hi ↦ ha i (by omega) (by omega),
      hk.constituentSign_eq_neg_of_isSquare_five_mul_det h1 hdk,
      by simpa [map_ofNat] using hk.constituentOddity_eq_add_of_eight_dvd h1 hB (δ := 4) hok⟩

/-- Align the compartment invariants `(compartmentSignedOddity, ∏ constituentSign)` on `[k, d]`
without disturbing constituents `i < k`. -/
private theorem exists_aligned_compartment
    {M' : Type*} [AddCommGroup M'] [Module ℤ_[2] M'] [Module.Free ℤ_[2] M']
    [Module.Finite ℤ_[2] M'] {B' : BilinForm ℤ_[2] M'} {Nk : ℕ → Submodule ℤ_[2] M}
    {N' : ℕ → Submodule ℤ_[2] M'} (hk : B.IsJordanSplitting 2 Nk)
    (h' : B'.IsJordanSplitting 2 N') (hB : B.IsSymm) (hB' : B'.IsSymm) {k d : ℕ}
    (hkd : k ≤ d)
    (hmatch : ∀ i < k, hk.constituentSign i = h'.constituentSign i ∧
      hk.constituentOddity hB i = h'.constituentOddity hB' i)
    (hbot_d1 : Nk (d + 1) = ⊥ ↔ N' (d + 1) = ⊥)
    (hinv_d : hk.partialSignedOddity hB d = h'.partialSignedOddity hB' d)
    (hinv_d1 : (∀ v ∈ Nk (d + 2), 2 * 2 ^ (d + 2) ∣ B v v) →
      hk.partialSignedOddity hB (d + 1) = h'.partialSignedOddity hB' (d + 1))
    (hodd_d : ¬∀ v ∈ Nk d, 2 * 2 ^ d ∣ B v v)
    (heven_d1 : ∀ v ∈ Nk (d + 1), 2 * 2 ^ (d + 1) ∣ B v v) :
    ∃ N1 : ℕ → Submodule ℤ_[2] M, ∃ h1 : B.IsJordanSplitting 2 N1,
      (∀ i < k, N1 i = Nk i) ∧
      compartmentSignedOddity h1.constituentSignBool (h1.constituentOddity hB) k d =
        compartmentSignedOddity h'.constituentSignBool (h'.constituentOddity hB') k d ∧
      ∏ i ∈ Finset.Icc k d, h1.constituentSign i =
        ∏ i ∈ Finset.Icc k d, h'.constituentSign i := by
  have hTd := compartmentSignedOddity_eq_of_match_below hk h' hB hB' hkd hmatch hinv_d
  by_cases hSd : ∏ i ∈ Finset.Icc k d, hk.constituentSign i =
      ∏ i ∈ Finset.Icc k d, h'.constituentSign i
  · exact ⟨Nk, hk, fun _ _ ↦ rfl, hTd, hSd⟩
  · obtain ⟨N1, h1, hlt, hsd, htd⟩ := exists_flip_end_of_compartment hk h' hB hB' hkd
      (fun i hi ↦ (hmatch i hi).1) hbot_d1 hinv_d hinv_d1 hodd_d heven_d1 hSd
    obtain ⟨hT1, hP1⟩ := flip_end_Icc hk h1 hB hkd hlt hsd htd
    have hS1 := TauCeti.eq_of_eq_neg_of_ne_of_eq_one_or_neg_one
      (Finset.prod_eq_one_or_neg_one _ fun i _ ↦ hk.constituentSign_eq_one_or_neg_one i)
      (Finset.prod_eq_one_or_neg_one _ fun i _ ↦ h'.constituentSign_eq_one_or_neg_one i) hP1 hSd
    exact ⟨N1, h1, fun i hi ↦ hlt i (by omega), hT1.trans hTd, hS1⟩

/-- **Left-to-right sweep.** For every `k`, there exists a Jordan splitting of `B` matching the
signs and oddities of `h'` at every index `i < k`. -/
private theorem exists_isJordanSplitting_matching_below
    {M' : Type*} [AddCommGroup M'] [Module ℤ_[2] M'] [Module.Free ℤ_[2] M']
    [Module.Finite ℤ_[2] M'] {B' : BilinForm ℤ_[2] M'} {N : ℕ → Submodule ℤ_[2] M}
    {N' : ℕ → Submodule ℤ_[2] M'}
    (h : B.IsJordanSplitting 2 N) (h' : B'.IsJordanSplitting 2 N')
    (hB : B.IsSymm) (hB' : B'.IsSymm)
    (hrank : ∀ i, finrank ℤ_[2] (N i) = finrank ℤ_[2] (N' i))
    (hpar : ∀ i, (∀ v ∈ N i, 2 * 2 ^ i ∣ B v v) ↔ ∀ v ∈ N' i, 2 * 2 ^ i ∣ B' v v)
    (hinv : ∀ j, (∀ v ∈ N (j + 1), 2 * 2 ^ (j + 1) ∣ B v v) →
      h.partialSignedOddity hB j = h'.partialSignedOddity hB' j) :
    ∀ k : ℕ, ∃ N'' : ℕ → Submodule ℤ_[2] M, ∃ h'' : B.IsJordanSplitting 2 N'',
      ∀ i < k, h''.constituentSign i = h'.constituentSign i ∧
        h''.constituentOddity hB i = h'.constituentOddity hB' i := by
  intro k
  induction k with
  | zero => exact ⟨N, h, fun i hi ↦ absurd hi (Nat.not_lt_zero i)⟩
  | succ k ih =>
    obtain ⟨Nk, hk, hmatch⟩ := ih
    have hrank_k (i) := (hk.finrank_eq_of_isJordanSplitting_two h i).trans (hrank i)
    have hpar_k (i) := (hk.forall_two_mul_pow_dvd_iff_of_isJordanSplitting_two h i).trans (hpar i)
    have hbot_iff (i) : Nk i = ⊥ ↔ N' i = ⊥ := by
      have := hk.finite i; have := h'.finite i
      rw [← Submodule.finrank_eq_zero, ← Submodule.finrank_eq_zero, hrank_k i]
    have hinv_k (j) (hj : ∀ v ∈ Nk (j + 1), 2 * 2 ^ (j + 1) ∣ B v v) :
        hk.partialSignedOddity hB j = h'.partialSignedOddity hB' j :=
      have hjN := (hk.forall_two_mul_pow_dvd_iff_of_isJordanSplitting_two h (j + 1)).mp hj
      (h.partialSignedOddity_eq_of_isJordanSplitting hk hB hjN).symm.trans (hinv j hjN)
    by_cases heven_k : ∀ v ∈ Nk k, 2 * 2 ^ k ∣ B v v
    · exact exists_matching_succ_of_even hk h' hB hB' hmatch (hbot_iff k) (hpar_k k)
        (hinv_k k) heven_k
    · obtain ⟨d, hkd, hodd_block, heven_d1⟩ := exists_compartment_end hk heven_k
      obtain ⟨N1, h1, hagree1, hT1, hS1⟩ := exists_aligned_compartment hk h' hB hB' hkd hmatch
        (hbot_iff (d + 1)) (hinv_k d heven_d1) (hinv_k (d + 1))
        (hodd_block d (Finset.mem_Icc.mpr ⟨hkd, le_rfl⟩)) heven_d1
      obtain ⟨N2, h2, hagree2, hmatch2⟩ :=
        h1.exists_constituentSign_and_oddity_eq_on_Icc h' hB hB'
          (fun i _ ↦ (h1.finrank_eq_of_isJordanSplitting_two hk i).trans (hrank_k i))
          (fun i hi ↦ by
            rw [h1.forall_two_mul_pow_dvd_iff_of_isJordanSplitting_two hk i]
            exact hodd_block i hi)
          (fun i hi ↦ by rw [← hpar_k i]; exact hodd_block i hi)
          (by simpa only [compartmentSignedOddity_constituentSignBool] using hT1) hS1
      exact exists_matching_succ_of_eq hk h' hB hB' hmatch h2
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
      h.partialSignedOddity hB j = h'.partialSignedOddity hB' j) :
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
      (by rw [h''.finrank_eq_of_isJordanSplitting_two h i, hbotN, finrank_bot])
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
partial signed oddity form).** Symmetric forms `B` and `B'` on finite free `ℤ_[2]`-modules with
Jordan splittings `N` and `N'` with respect to `2` are isometric if and only if their constituents
have equal ranks and parity types at every scale, and their partial signed oddities
`LinearMap.BilinForm.IsJordanSplitting.partialSignedOddity` agree modulo `8` at every scale `j`
with `N (j + 1)` of type II. -/
theorem IsJordanSplitting.equivalent_iff_partialSignedOddity_eq
    {M' : Type*} [AddCommGroup M'] [Module ℤ_[2] M'] [Module.Free ℤ_[2] M']
    [Module.Finite ℤ_[2] M'] {B' : BilinForm ℤ_[2] M'} {N' : ℕ → Submodule ℤ_[2] M'}
    (h : B.IsJordanSplitting 2 N) (h' : B'.IsJordanSplitting 2 N')
    (hB : B.IsSymm) (hB' : B'.IsSymm) :
    B.Equivalent B' ↔
      (∀ i, finrank ℤ_[2] (N i) = finrank ℤ_[2] (N' i)) ∧
      (∀ i, (∀ v ∈ N i, 2 * 2 ^ i ∣ B v v) ↔ ∀ v ∈ N' i, 2 * 2 ^ i ∣ B' v v) ∧
      ∀ j, (∀ v ∈ N (j + 1), 2 * 2 ^ (j + 1) ∣ B v v) →
        h.partialSignedOddity hB j = h'.partialSignedOddity hB' j := by
  refine ⟨fun ⟨ε⟩ ↦ ?_, ?_⟩
  · exact ⟨fun i ↦ h.finrank_eq_of_equivalent h' ⟨ε⟩ two_ne_zero PadicInt.not_isUnit_two i,
      fun i ↦ ⟨fun he ↦ h.forall_two_mul_pow_dvd_of_equivalent h' ⟨ε⟩
          (mem_nonZeroDivisors_of_ne_zero two_ne_zero) dvd_rfl he,
        fun he ↦ h'.forall_two_mul_pow_dvd_of_equivalent h ⟨ε.symm⟩
          (mem_nonZeroDivisors_of_ne_zero two_ne_zero) dvd_rfl he⟩,
      fun j hj ↦ h.partialSignedOddity_eq_of_equivalent h' hB hB' ⟨ε⟩ hj⟩
  rintro ⟨hrank, hpar, hinv⟩
  obtain ⟨N'', h'', hmatch⟩ := h.exists_constituentSign_and_oddity_eq h' hB hB' hrank hpar hinv
  refine equivalent_of_isInternal h''.isInternal h'.isInternal h''.apply_eq_zero h'.apply_eq_zero
    fun i ↦ ?_
  have := h''.free i; have := h''.finite i; have := h'.free i; have := h'.finite i
  have hcard : Fintype.card (Fin (finrank ℤ_[2] (N'' i))) =
      Fintype.card (Fin (finrank ℤ_[2] (N' i))) := by
    simp [h''.finrank_eq_of_isJordanSplitting_two h i, hrank i]
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
  exact ⟨(h''.forall_two_mul_pow_dvd_iff_of_isJordanSplitting_two h i).trans (hpar i),
    hsign_i, hodd_i⟩

/-- **Classification of symmetric bilinear forms over `ℤ_[2]` via Jordan splittings (Gauss-sum
form).** Obtained from `IsJordanSplitting.equivalent_iff_partialSignedOddity_eq` by applying
the standard additive character `ZMod.stdAddChar`. -/
theorem IsJordanSplitting.equivalent_iff_stdAddChar_partialSignedOddity_eq
    {M' : Type*} [AddCommGroup M'] [Module ℤ_[2] M'] [Module.Free ℤ_[2] M']
    [Module.Finite ℤ_[2] M'] {B' : BilinForm ℤ_[2] M'} {N' : ℕ → Submodule ℤ_[2] M'}
    (h : B.IsJordanSplitting 2 N) (h' : B'.IsJordanSplitting 2 N')
    (hB : B.IsSymm) (hB' : B'.IsSymm) :
    B.Equivalent B' ↔
      (∀ i, finrank ℤ_[2] (N i) = finrank ℤ_[2] (N' i)) ∧
      (∀ i, (∀ v ∈ N i, 2 * 2 ^ i ∣ B v v) ↔ ∀ v ∈ N' i, 2 * 2 ^ i ∣ B' v v) ∧
      ∀ j, (∀ v ∈ N (j + 1), 2 * 2 ^ (j + 1) ∣ B v v) →
        stdAddChar (h.partialSignedOddity hB j) = stdAddChar (h'.partialSignedOddity hB' j) := by
  rw [h.equivalent_iff_partialSignedOddity_eq h' hB hB']
  simp only [injective_stdAddChar.eq_iff]

end Classification

end LinearMap.BilinForm
