/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import Mathlib.Order.Interval.Finset.Nat
public import TauCeti.LinearAlgebra.BilinearForm.JordanSplitting.Basic
public import TauCeti.NumberTheory.Padics.BilinearForm.Classification.Invariants
import Mathlib.Data.ZMod.Basic
import TauCeti.Algebra.Group.AddChar
import TauCeti.LinearAlgebra.BilinearForm.Isometry.Basic
import TauCeti.LinearAlgebra.BilinearForm.JordanSplitting.Parity
import TauCeti.LinearAlgebra.BilinearForm.Orthogonal
import TauCeti.LinearAlgebra.PerfectPairing.Basis
import TauCeti.NumberTheory.Padics.BilinearForm.Classification.Compartment
import TauCeti.NumberTheory.Padics.BilinearForm.JordanGaussSum
import TauCeti.NumberTheory.Padics.BilinearForm.SignWalking
import TauCeti.NumberTheory.Padics.BilinearForm.Unimodular
import TauCeti.NumberTheory.Padics.PadicIntegers
import TauCeti.NumberTheory.Padics.RingHoms
import TauCeti.NumberTheory.Padics.SerreSigns

/-!
# Classification of symmetric bilinear forms over `ℤ_[2]`

Two symmetric bilinear forms `B` and `B'` on finite free `ℤ_[2]`-modules with Jordan splittings
`N` and `N'` with respect to `2` are isometric if and only if:

1. `N i` and `N' i` have equal rank at every scale `i`;
2. `N i` and `N' i` have the same parity type (type I or type II) at every scale `i`;
3. at every scale `j` where `N (j + 1)` is of type II (including `N (j + 1) = ⊥`), the partial
   Gauss-sum invariant (equivalently, its `ZMod 8` residue) agrees for `B` and `B'`.

## Main results

* `LinearMap.BilinForm.IsJordanSplitting.exists_constituentSign_and_oddity_eq`: normalizing signs
  and oddities across all scales simultaneously.
* `LinearMap.BilinForm.IsJordanSplitting.equivalent_iff_prod_χ₈_pow_mul_stdAddChar_sum_eq`:
  complete classification of symmetric bilinear forms over `ℤ_[2]` in Gauss-sum form.
* `LinearMap.BilinForm.IsJordanSplitting.equivalent_iff_toZModPow_sum_add_eq`: the purely algebraic
  `ZMod 8` formulation of the classification.
* `TauCeti.not_equivalent_toBilin'_diagonal_two_neg_two_two_smul_hyperbolic`:
  `⟨2, -2⟩` and `2 • U` are not isometric over `ℤ_[2]`.

## References

* O. T. O'Meara, *Introduction to Quadratic Forms*, §93.
* J. W. S. Cassels, *Rational Quadratic Forms*, Chapter 8, §4.
* J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, Chapter 15, §7.
-/

public section

open Module ZMod
open LinearMap (BilinForm)

namespace LinearMap.BilinForm

/-! ### Partial `ZMod 8` invariants and their dictionary with Gauss sums -/

section PartialInvariants

private def gaussInv (s : ℕ → ℤ) (t : ℕ → ZMod (2 ^ 3)) (j : ℕ) : ZMod (2 ^ 3) :=
  ∑ i ∈ Finset.Iic j, (t i + if Odd (j + 1 - i) ∧ s i = -1 then 4 else 0)

private def compSum (s : ℕ → ℤ) (t : ℕ → ZMod (2 ^ 3)) (c d : ℕ) : ZMod (2 ^ 3) :=
  ∑ i ∈ Finset.Icc c d, (t i + if Odd (d + 1 - i) ∧ s i = -1 then 4 else 0)

private theorem stdAddChar_four_eq_neg_one : stdAddChar (4 : ZMod (2 ^ 3)) = -1 := by
  have hsq : stdAddChar (4 : ZMod (2 ^ 3)) ^ 2 = 1 := by
    rw [sq, ← AddChar.map_add_eq_mul, show (4 : ZMod (2 ^ 3)) + 4 = 0 by decide,
      AddChar.map_zero_eq_one]
  refine (sq_eq_one_iff.mp hsq).resolve_left fun h ↦ ?_
  rw [← (stdAddChar (N := 2 ^ 3)).map_zero_eq_one, injective_stdAddChar.eq_iff] at h
  exact absurd h (by decide)

private theorem stdAddChar_gaussInv {s : ℕ → ℤ} {j : ℕ}
    (hs : ∀ i ∈ Finset.Iic j, s i = 1 ∨ s i = -1) (t : ℕ → ZMod (2 ^ 3)) :
    stdAddChar (gaussInv s t j) =
      (∏ i ∈ Finset.Iic j, (s i : ℂ) ^ (j + 1 - i)) *
        stdAddChar (∑ i ∈ Finset.Iic j, t i) := by
  unfold gaussInv
  rw [Finset.sum_add_distrib, AddChar.map_add_eq_mul, mul_comm, AddChar.map_sum_eq_prod]
  congr 1
  refine Finset.prod_congr rfl fun i hi ↦ ?_
  rcases hs i hi with hsi | hsi
  · simp [hsi]
  · rcases Nat.even_or_odd (j + 1 - i) with hm | hm
    · simp [hsi, hm.neg_one_pow, Nat.not_odd_iff_even.mpr hm]
    · simp only [hsi, hm, hm.neg_one_pow, and_self, ↓reduceIte, Int.cast_neg, Int.cast_one]
      exact stdAddChar_four_eq_neg_one

private theorem prod_pow_mul_stdAddChar_eq_stdAddChar_add_ite {u : Finset ℕ} {s : ℕ → ℤ}
    (hs : ∀ i ∈ u, s i = 1 ∨ s i = -1) (t : ℕ → ZMod (2 ^ 3)) (e : ℕ → ℕ) :
    (∏ i ∈ u, (s i : ℂ) ^ e i) * stdAddChar (∑ i ∈ u, t i) =
      stdAddChar ((∑ i ∈ u, t i) +
        if ∏ i ∈ u, s i ^ e i = -1 then (4 : ZMod (2 ^ 3)) else 0) := by
  have hprod_pm : (∏ i ∈ u, s i ^ e i) = 1 ∨ (∏ i ∈ u, s i ^ e i) = -1 := by
    refine Finset.prod_induction _ (fun x ↦ x = 1 ∨ x = -1)
      (fun _ _ ha hb ↦ by rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> norm_num)
      (Or.inl rfl) fun i hi ↦ ?_
    rcases hs i hi with h | h
    · exact Or.inl (by rw [h, one_pow])
    · rw [h]; rcases Nat.even_or_odd (e i) with he | he <;> simp [he.neg_one_pow]
  have hcast : (∏ i ∈ u, (s i : ℂ) ^ e i) = ((∏ i ∈ u, s i ^ e i : ℤ) : ℂ) := by
    push_cast; rfl
  rw [hcast]
  rcases hprod_pm with h | h
  · simp [h]
  · simp only [h, ↓reduceIte, Int.cast_neg, Int.cast_one, neg_one_mul, AddChar.map_add_eq_mul,
      stdAddChar_four_eq_neg_one, mul_neg_one]

private theorem Iio_union_Icc_eq_Iic {c d : ℕ} (hcd : c ≤ d) :
    Finset.Iio c ∪ Finset.Icc c d = Finset.Iic d := by
  ext i; simp only [Finset.mem_union, Finset.mem_Iio, Finset.mem_Icc, Finset.mem_Iic]; omega

private theorem disjoint_Iio_Icc (c d : ℕ) : Disjoint (Finset.Iio c) (Finset.Icc c d) :=
  Finset.disjoint_left.mpr fun i h1 h2 ↦ by
    simp only [Finset.mem_Iio, Finset.mem_Icc] at h1 h2; omega

private theorem gaussInv_eq_sum_Iio_add_compSum (s : ℕ → ℤ) (t : ℕ → ZMod (2 ^ 3))
    {c d : ℕ} (hcd : c ≤ d) :
    gaussInv s t d =
      (∑ i ∈ Finset.Iio c, (t i + if Odd (d + 1 - i) ∧ s i = -1 then 4 else 0)) +
      compSum s t c d := by
  unfold gaussInv compSum
  rw [← Finset.sum_union (disjoint_Iio_Icc c d), Iio_union_Icc_eq_Iic hcd]

private theorem gaussInv_succ_sub_gaussInv {s : ℕ → ℤ} {t : ℕ → ZMod (2 ^ 3)} {j : ℕ}
    (hs : s (j + 1) = 1) (ht : t (j + 1) = 0) :
    gaussInv s t (j + 1) - gaussInv s t j =
      ∑ i ∈ Finset.Iic j, if s i = -1 then (4 : ZMod (2 ^ 3)) else 0 := by
  unfold gaussInv
  have hIic : Finset.Iic (j + 1) = insert (j + 1) (Finset.Iic j) := by
    ext i; simp only [Finset.mem_Iic, Finset.mem_insert]; omega
  rw [hIic, Finset.sum_insert (by simp), hs, ht]
  simp only [show (1 : ℤ) ≠ -1 by decide, and_false, ↓reduceIte, add_zero, zero_add,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  have hij := Finset.mem_Iic.mp hi
  have hpar : Odd (j + 1 + 1 - i) ↔ ¬Odd (j + 1 - i) := by
    rw [show j + 1 + 1 - i = (j + 1 - i) + 1 by omega, Nat.odd_add_one]
  by_cases hsi : s i = -1
  · by_cases ho : Odd (j + 1 - i)
    · simp only [hsi, ho, hpar.not.mpr (not_not.mpr ho), and_true, ↓reduceIte, add_zero,
        sub_add_eq_sub_sub, sub_self, zero_sub]
      decide
    · simp only [hsi, ho, hpar.mpr ho, and_true, ↓reduceIte, add_zero, add_sub_cancel_left]
  · simp [hsi]

private theorem flip_end_Icc {s s1 : ℕ → ℤ} {t t1 : ℕ → ZMod (2 ^ 3)} {k d : ℕ}
    (hkd : k ≤ d) (hsd_pm : s d = 1 ∨ s d = -1) (hlt : ∀ i < d, s1 i = s i ∧ t1 i = t i)
    (hsd : s1 d = -s d) (htd : t1 d = t d + 4) :
    compSum s1 t1 k d = compSum s t k d ∧
    ∏ i ∈ Finset.Icc k d, s1 i = -(∏ i ∈ Finset.Icc k d, s i) := by
  have hd_mem := Finset.mem_Icc.mpr ⟨hkd, le_rfl⟩
  have hlt' : ∀ i ∈ (Finset.Icc k d).erase d, s1 i = s i ∧ t1 i = t i := fun i hi ↦ by
    rw [Finset.mem_erase, Finset.mem_Icc] at hi; exact hlt i (by omega)
  refine ⟨?_, ?_⟩
  · unfold compSum
    rw [← Finset.add_sum_erase _ _ hd_mem, ← Finset.add_sum_erase _ _ hd_mem,
      Finset.sum_congr rfl fun i hi ↦ by rw [(hlt' i hi).1, (hlt' i hi).2], hsd, htd,
      Nat.add_sub_cancel_left]
    congr 1
    rcases hsd_pm with h | h <;> rw [h] <;>
      simp only [odd_one, true_and, neg_neg, show (1 : ℤ) ≠ -1 by decide, ↓reduceIte,
        add_zero]
    rw [add_assoc, show (4 : ZMod (2 ^ 3)) + 4 = 0 by decide, add_zero]
  · rw [← Finset.mul_prod_erase _ _ hd_mem, ← Finset.mul_prod_erase _ _ hd_mem,
      Finset.prod_congr rfl fun i hi ↦ (hlt' i hi).1, hsd, neg_mul]

end PartialInvariants

/-! ### Left-to-right sweep and Jordan splitting normalization -/

section Normalization

variable {M : Type*} [AddCommGroup M] [Module ℤ_[2] M] [Module.Free ℤ_[2] M]
  [Module.Finite ℤ_[2] M] {B : BilinForm ℤ_[2] M} {N : ℕ → Submodule ℤ_[2] M}

private theorem stdAddChar_gaussInv_constituent (h : B.IsJordanSplitting 2 N) (hB : B.IsSymm)
    {α : ℕ → Type*} [∀ i, Fintype (α i)] [∀ i, DecidableEq (α i)]
    (C : ∀ i, BilinForm ℤ_[2] (N i)) (hC : ∀ i, (2 : ℤ_[2]) ^ i • C i = B.restrict (N i))
    (d : ∀ i, Basis (α i) ℤ_[2] (N i)) (w : ∀ i, N i)
    (hw : ∀ i, (C i).IsCharacteristic (w i)) (j : ℕ) :
    stdAddChar (gaussInv h.constituentSign (h.constituentOddity hB) j) =
      (∏ i ∈ Finset.Iic j,
          ((χ₈ (PadicInt.toZModPow 3 ((C i).toMatrix (d i)).det) : ℤ) : ℂ) ^ (j + 1 - i)) *
        stdAddChar (PadicInt.toZModPow 3 (∑ i ∈ Finset.Iic j, C i (w i) (w i))) := by
  rw [stdAddChar_gaussInv (fun i _ ↦ h.constituentSign_eq_one_or_neg_one i)]
  simp only [fun i ↦ h.constituentSign_eq (hC i) (d i),
    fun i ↦ h.constituentOddity_eq hB (hC i) (hw i), ← map_sum]

private theorem gaussInv_eq_of_isJordanSplitting {N' : ℕ → Submodule ℤ_[2] M}
    (h : B.IsJordanSplitting 2 N) (h' : B.IsJordanSplitting 2 N') (hB : B.IsSymm) {j : ℕ}
    (hj : ∀ v ∈ N (j + 1), 2 * 2 ^ (j + 1) ∣ B v v) :
    gaussInv h'.constituentSign (h'.constituentOddity hB) j =
      gaussInv h.constituentSign (h.constituentOddity hB) j := by
  have := h.free; have := h.finite; have := h'.free; have := h'.finite
  let C (i : ℕ) := (isModular_def.mp (h.isModular i)).choose
  let C' (i : ℕ) := (isModular_def.mp (h'.isModular i)).choose
  have hC (i) := (isModular_def.mp (h.isModular i)).choose_spec.1
  have hC' (i) := (isModular_def.mp (h'.isModular i)).choose_spec.1
  have hw_ex {N₀ : ℕ → Submodule ℤ_[2] M} (h₀ : B.IsJordanSplitting 2 N₀) (i : ℕ) :
      ∃ w : N₀ i, (isModular_def.mp (h₀.isModular i)).choose.IsCharacteristic w := by
    have := h₀.free i; have := (isModular_def.mp (h₀.isModular i)).choose_spec.2
    exact (IsSymm.of_smul (mem_nonZeroDivisors_of_ne_zero (pow_ne_zero i two_ne_zero))
      ((isModular_def.mp (h₀.isModular i)).choose_spec.1.symm ▸
        hB.restrict (N₀ i))).exists_isCharacteristic PadicInt.two_dvd_sq_sub_self
  apply injective_stdAddChar
  rw [stdAddChar_gaussInv_constituent h' hB C' hC' (fun i ↦ Module.finBasis ℤ_[2] (N' i))
      (fun i ↦ (hw_ex h' i).choose) (fun i ↦ (hw_ex h' i).choose_spec) j,
    stdAddChar_gaussInv_constituent h hB C hC (fun i ↦ Module.finBasis ℤ_[2] (N i))
      (fun i ↦ (hw_ex h i).choose) (fun i ↦ (hw_ex h i).choose_spec) j]
  exact (h.prod_χ₈_pow_mul_stdAddChar_sum_eq_of_equivalent h' hB (Equivalent.refl B) hj
    C (fun i _ ↦ hC i) (fun i ↦ Module.finBasis ℤ_[2] (N i)) (fun i ↦ (hw_ex h i).choose)
    (fun i _ ↦ (hw_ex h i).choose_spec) C' (fun i _ ↦ hC' i)
    (fun i ↦ Module.finBasis ℤ_[2] (N' i)) (fun i ↦ (hw_ex h' i).choose)
    (fun i _ ↦ (hw_ex h' i).choose_spec)).symm

private theorem constituentSign_eq_neg_of_isSquare_five {N' : ℕ → Submodule ℤ_[2] M}
    (h : B.IsJordanSplitting 2 N) (h' : B.IsJordanSplitting 2 N') {k : ℕ}
    (hdk : ∀ (n : ℕ) (d : Basis (Fin n) ℤ_[2] (N k)) (d' : Basis (Fin n) ℤ_[2] (N' k)),
      IsSquare (5 * ((B.restrict (N k)).toMatrix d).det * ((B.restrict (N' k)).toMatrix d').det)) :
    h'.constituentSign k = -h.constituentSign k := by
  have hsk := h.constituentSign_eq_mul_of_isSquare_det h' TauCeti.isUnit_five_padicInt hdk
  rwa [show χ₈ (PadicInt.toZModPow 3 (5 : ℤ_[2])) = -1 by rw [map_ofNat]; decide,
    neg_one_mul] at hsk

/-- **Left-to-right sweep.** For every `k`, there exists a Jordan splitting of `B` matching the
signs and oddities of `h'` at every index `i < k`. -/
private theorem exists_isJordanSplitting_matching_below
    {M' : Type*} [AddCommGroup M'] [Module ℤ_[2] M'] [Module.Free ℤ_[2] M']
    [Module.Finite ℤ_[2] M'] {B' : BilinForm ℤ_[2] M'} {N' : ℕ → Submodule ℤ_[2] M'}
    (h : B.IsJordanSplitting 2 N) (h' : B'.IsJordanSplitting 2 N')
    (hB : B.IsSymm) (hB' : B'.IsSymm)
    (hrank : ∀ i, finrank ℤ_[2] (N i) = finrank ℤ_[2] (N' i))
    (hpar : ∀ i, (∀ v ∈ N i, 2 * 2 ^ i ∣ B v v) ↔ ∀ v ∈ N' i, 2 * 2 ^ i ∣ B' v v)
    (hgauss : ∀ j, (∀ v ∈ N (j + 1), 2 * 2 ^ (j + 1) ∣ B v v) →
      gaussInv h.constituentSign (h.constituentOddity hB) j =
        gaussInv h'.constituentSign (h'.constituentOddity hB') j) :
    ∀ k : ℕ, ∃ N'' : ℕ → Submodule ℤ_[2] M, ∃ h'' : B.IsJordanSplitting 2 N'',
      ∀ i < k, h''.constituentSign i = h'.constituentSign i ∧
        h''.constituentOddity hB i = h'.constituentOddity hB' i := by
  intro k
  induction k with
  | zero => exact ⟨N, h, fun i hi ↦ absurd hi (Nat.not_lt_zero i)⟩
  | succ k ih =>
    obtain ⟨Nk, hk, hmatch⟩ := ih
    have hrank_k (i) := (hk.finrank_eq h two_ne_zero PadicInt.not_isUnit_two i).trans (hrank i)
    have hpar_k (i) := (hk.forall_two_mul_pow_dvd_iff_of_isJordanSplitting h i).trans (hpar i)
    have hbot_iff (i) : Nk i = ⊥ ↔ N' i = ⊥ := by
      have := hk.finite i; have := h'.finite i
      rw [← Submodule.finrank_eq_zero, ← Submodule.finrank_eq_zero, hrank_k i]
    have hgauss_k (j) (hj : ∀ v ∈ Nk (j + 1), 2 * 2 ^ (j + 1) ∣ B v v) :
        gaussInv hk.constituentSign (hk.constituentOddity hB) j =
          gaussInv h'.constituentSign (h'.constituentOddity hB') j :=
      have hjN := (hk.forall_two_mul_pow_dvd_iff_of_isJordanSplitting h (j + 1)).mp hj
      (gaussInv_eq_of_isJordanSplitting h hk hB hjN).trans (hgauss j hjN)
    have hIcc_eq (d) (hkd : k ≤ d) (heven_d1 : ∀ v ∈ Nk (d + 1), 2 * 2 ^ (d + 1) ∣ B v v) :
        compSum hk.constituentSign (hk.constituentOddity hB) k d =
          compSum h'.constituentSign (h'.constituentOddity hB') k d := by
      have hGd := hgauss_k d heven_d1
      rw [gaussInv_eq_sum_Iio_add_compSum _ _ hkd,
        gaussInv_eq_sum_Iio_add_compSum _ _ hkd] at hGd
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
            have heven1 := (hk.forall_two_mul_pow_dvd_iff_of_isJordanSplitting h1 k).mp heven_k
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
          · exact fun he ↦ Nat.find_min hex (show i - 1 < d by omega)
              ⟨by omega, by simpa only [show i - 1 + 1 = i by omega] using he⟩
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
              · exfalso
                have hdiff : (∑ i ∈ Finset.Iic d,
                      if hk.constituentSign i = -1 then (4 : ZMod (2 ^ 3)) else 0) =
                    ∑ i ∈ Finset.Iic d,
                      if h'.constituentSign i = -1 then (4 : ZMod (2 ^ 3)) else 0 := by
                  rw [← gaussInv_succ_sub_gaussInv (hk.constituentSign_of_eq_bot hbot_d1)
                      (hk.constituentOddity_of_eq_bot hB hbot_d1),
                    ← gaussInv_succ_sub_gaussInv
                      (h'.constituentSign_of_eq_bot ((hbot_iff (d + 1)).mp hbot_d1))
                      (h'.constituentOddity_of_eq_bot hB' ((hbot_iff (d + 1)).mp hbot_d1)),
                    hgauss_k d heven_d1, hgauss_k (d + 1) heven_d2]
                rw [← Iio_union_Icc_eq_Iic hkd, Finset.sum_union (disjoint_Iio_Icc k d),
                  Finset.sum_union (disjoint_Iio_Icc k d)] at hdiff
                have hpre : ∑ i ∈ Finset.Iio k,
                      (if hk.constituentSign i = -1 then (4 : ZMod (2 ^ 3)) else 0) =
                    ∑ i ∈ Finset.Iio k,
                      (if h'.constituentSign i = -1 then (4 : ZMod (2 ^ 3)) else 0) :=
                  Finset.sum_congr rfl fun i hi ↦ by rw [(hmatch i (Finset.mem_Iio.mp hi)).1]
                rw [hpre] at hdiff
                apply hSd
                rw [hk.prod_constituentSign_eq_ite, h'.prod_constituentSign_eq_ite,
                  add_left_cancel hdiff]
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
            rw [h1.forall_two_mul_pow_dvd_iff_of_isJordanSplitting hk i]; exact hodd_block i hi)
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
      ∑ i ∈ Finset.Iic j,
        (h.constituentOddity hB i + if Odd (j + 1 - i) ∧ h.constituentSign i = -1 then 4 else 0) =
      ∑ i ∈ Finset.Iic j,
        (h'.constituentOddity hB' i +
          if Odd (j + 1 - i) ∧ h'.constituentSign i = -1 then 4 else 0)) :
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

variable {M : Type*} [AddCommGroup M] [Module ℤ_[2] M] {B : BilinForm ℤ_[2] M}
  {N : ℕ → Submodule ℤ_[2] M}

private theorem forall_two_dvd_iff_forall_two_mul_pow_dvd {P : Submodule ℤ_[2] M} {i : ℕ}
    {C : BilinForm ℤ_[2] P} (hC : (2 : ℤ_[2]) ^ i • C = B.restrict P) :
    (∀ x : P, (2 : ℤ_[2]) ∣ C x x) ↔ ∀ v ∈ P, 2 * 2 ^ i ∣ B v v := by
  have h2i := mem_nonZeroDivisors_of_ne_zero (pow_ne_zero i (two_ne_zero (α := ℤ_[2])))
  have hBC (x : P) : (2 : ℤ_[2]) ^ i * C x x = B x x := by
    simpa using LinearMap.congr_fun₂ hC x x
  refine ⟨fun he v hv ↦ ?_, fun he x ↦ ?_⟩
  · obtain ⟨c, hc⟩ := he ⟨v, hv⟩; exact ⟨c, by rw [← hBC ⟨v, hv⟩, hc]; ring⟩
  · obtain ⟨c, hc⟩ := he x x.2
    exact ⟨c, (mul_cancel_left_mem_nonZeroDivisors h2i).mp (by rw [hBC]; linear_combination hc)⟩

private theorem free_and_finite_of_isJordanSplitting {M' : Type*} [AddCommGroup M']
    [Module ℤ_[2] M'] {B' : BilinForm ℤ_[2] M'} {N' : ℕ → Submodule ℤ_[2] M'}
    {α' : ℕ → Type*} [∀ i, Finite (α' i)]
    (h' : B'.IsJordanSplitting 2 N') (d' : ∀ i, Basis (α' i) ℤ_[2] (N' i))
    {m : ℕ} (hm : ∀ i ≥ m, N' i = ⊥) :
    Module.Free ℤ_[2] M' ∧ Module.Finite ℤ_[2] M' := by
  have : ∀ i : Fin m, Module.Free ℤ_[2] (N' i) := fun i ↦ .of_basis (d' i)
  have : ∀ i : Fin m, Module.Finite ℤ_[2] (N' i) := fun i ↦ .of_basis (d' i)
  have hsup : ⨆ i : Fin m, N' i = ⊤ := by
    rw [eq_top_iff, ← h'.isInternal.submodule_iSup_eq_top]
    refine iSup_le fun i ↦ ?_
    by_cases hi : i < m
    · exact le_iSup (fun j : Fin m ↦ N' j) ⟨i, hi⟩
    · rw [hm i (by omega)]; exact bot_le
  have hint : DirectSum.IsInternal (fun i : Fin m ↦ N' i) :=
    (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top _).mpr
      ⟨((DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top _).mp h'.isInternal).1.comp
        Fin.val_injective, hsup⟩
  let e : (∀ i : Fin m, N' i) ≃ₗ[ℤ_[2]] M' :=
    (DirectSum.linearEquivFunOnFintype ℤ_[2] (Fin m) (fun i : Fin m ↦ N' i)).symm.trans
      (LinearEquiv.ofBijective (DirectSum.coeLinearMap (fun i : Fin m ↦ N' i)) hint)
  exact ⟨Module.Free.of_equiv e, Module.Finite.equiv e⟩

/-- **Classification of symmetric bilinear forms over `ℤ_[2]` via Jordan splittings (Gauss-sum
form).** Symmetric forms `B` and `B'` over `ℤ_[2]` with Jordan splittings `N` and `N'`, unimodular
rescalings `C i` and `C' i`, bases `d i` and `d' i`, and characteristic vectors `w i` and `w' i`
are isometric if and only if their constituents have equal ranks and parity types at every scale,
and the partial Gauss-sum invariants agree at every scale `j` with `N (j + 1)` of type II. -/
theorem IsJordanSplitting.equivalent_iff_prod_χ₈_pow_mul_stdAddChar_sum_eq
    [Module.Free ℤ_[2] M] [Module.Finite ℤ_[2] M]
    {M' : Type*} [AddCommGroup M'] [Module ℤ_[2] M']
    {B' : BilinForm ℤ_[2] M'} {N' : ℕ → Submodule ℤ_[2] M'}
    {α α' : ℕ → Type*} [∀ i, Fintype (α i)] [∀ i, DecidableEq (α i)]
    [∀ i, Fintype (α' i)] [∀ i, DecidableEq (α' i)]
    (h : B.IsJordanSplitting 2 N) (h' : B'.IsJordanSplitting 2 N')
    (hB : B.IsSymm) (hB' : B'.IsSymm)
    (C : ∀ i, BilinForm ℤ_[2] (N i)) (hC : ∀ i, (2 : ℤ_[2]) ^ i • C i = B.restrict (N i))
    (d : ∀ i, Basis (α i) ℤ_[2] (N i)) (w : ∀ i, N i)
    (hw : ∀ i, (C i).IsCharacteristic (w i))
    (C' : ∀ i, BilinForm ℤ_[2] (N' i))
    (hC' : ∀ i, (2 : ℤ_[2]) ^ i • C' i = B'.restrict (N' i))
    (d' : ∀ i, Basis (α' i) ℤ_[2] (N' i)) (w' : ∀ i, N' i)
    (hw' : ∀ i, (C' i).IsCharacteristic (w' i)) :
    B.Equivalent B' ↔
      (∀ i, finrank ℤ_[2] (N i) = finrank ℤ_[2] (N' i)) ∧
      (∀ i, (∀ v ∈ N i, 2 * 2 ^ i ∣ B v v) ↔ ∀ v ∈ N' i, 2 * 2 ^ i ∣ B' v v) ∧
      ∀ j, (∀ v ∈ N (j + 1), 2 * 2 ^ (j + 1) ∣ B v v) →
        (∏ i ∈ Finset.Iic j,
          ((χ₈ (PadicInt.toZModPow 3 ((C i).toMatrix (d i)).det) : ℤ) : ℂ) ^ (j + 1 - i)) *
            stdAddChar (PadicInt.toZModPow 3 (∑ i ∈ Finset.Iic j, C i (w i) (w i))) =
        (∏ i ∈ Finset.Iic j,
          ((χ₈ (PadicInt.toZModPow 3 ((C' i).toMatrix (d' i)).det) : ℤ) : ℂ) ^ (j + 1 - i)) *
            stdAddChar (PadicInt.toZModPow 3 (∑ i ∈ Finset.Iic j, C' i (w' i) (w' i))) := by
  refine ⟨fun ⟨ε⟩ ↦ ?_, ?_⟩
  · have := Module.Free.of_equiv ε.toLinearEquiv
    have := Module.Finite.equiv ε.toLinearEquiv
    exact ⟨fun i ↦ h.finrank_eq_of_equivalent h' ⟨ε⟩ two_ne_zero PadicInt.not_isUnit_two i,
      fun i ↦ ⟨fun he ↦ h.forall_two_mul_pow_dvd_of_equivalent h' ⟨ε⟩
          (mem_nonZeroDivisors_of_ne_zero two_ne_zero) dvd_rfl he,
        fun he ↦ h'.forall_two_mul_pow_dvd_of_equivalent h ⟨ε.symm⟩
          (mem_nonZeroDivisors_of_ne_zero two_ne_zero) dvd_rfl he⟩,
      fun j hj ↦ h.prod_χ₈_pow_mul_stdAddChar_sum_eq_of_equivalent h' hB ⟨ε⟩ hj
        C (fun i _ ↦ hC i) d w (fun i _ ↦ hw i)
        C' (fun i _ ↦ hC' i) d' w' (fun i _ ↦ hw' i)⟩
  rintro ⟨hrank, hpar, hG⟩
  obtain ⟨b, hb⟩ := h.hasFiniteSupport.bddAbove
  have hm : ∀ i ≥ b + 1, N' i = ⊥ := fun i hi ↦ by
    have hbotN : N i = ⊥ := by by_contra hne; have := hb hne; omega
    have : IsEmpty (α' i) := Fintype.card_eq_zero_iff.mp
      (by rw [← finrank_eq_card_basis (d' i), ← hrank i, hbotN, finrank_bot])
    rw [Submodule.eq_bot_iff]; intro x hx
    exact congrArg Subtype.val
      ((d' i).repr.injective (Subsingleton.elim ((d' i).repr ⟨x, hx⟩) ((d' i).repr 0)))
  obtain ⟨_, _⟩ := free_and_finite_of_isJordanSplitting h' d' hm
  have hinv : ∀ j, (∀ v ∈ N (j + 1), 2 * 2 ^ (j + 1) ∣ B v v) →
      gaussInv h.constituentSign (h.constituentOddity hB) j =
        gaussInv h'.constituentSign (h'.constituentOddity hB') j := fun j hj ↦
    injective_stdAddChar (by
      rw [stdAddChar_gaussInv_constituent h hB C hC d w hw j,
        stdAddChar_gaussInv_constituent h' hB' C' hC' d' w' hw' j]
      exact hG j hj)
  obtain ⟨N'', h'', hmatch⟩ := h.exists_constituentSign_and_oddity_eq h' hB hB' hrank hpar hinv
  refine equivalent_of_isInternal h''.isInternal h'.isInternal h''.apply_eq_zero h'.apply_eq_zero
    fun i ↦ ?_
  have h2i := mem_nonZeroDivisors_of_ne_zero (pow_ne_zero i (two_ne_zero (α := ℤ_[2])))
  have := h''.free i; have := h''.finite i
  obtain ⟨C'', hC'', hC''p⟩ := isModular_def.mp (h''.isModular i)
  have hC''s : C''.IsSymm := IsSymm.of_smul h2i (hC'' ▸ hB.restrict (N'' i))
  have hC's : (C' i).IsSymm := IsSymm.of_smul h2i (hC' i ▸ hB'.restrict (N' i))
  let d'' := Module.finBasis ℤ_[2] (N'' i)
  obtain ⟨w'', hw''⟩ := hC''s.exists_isCharacteristic PadicInt.two_dvd_sq_sub_self
  obtain ⟨hsign_i, hodd_i⟩ := hmatch i
  rw [h''.constituentSign_eq hC'' d'', h'.constituentSign_eq (hC' i) (d' i)] at hsign_i
  rw [h''.constituentOddity_eq hB hC'' hw'', h'.constituentOddity_eq hB' (hC' i) (hw' i)] at hodd_i
  rw [← hC'', ← hC' i, equivalent_smul_iff h2i,
    hC''s.equivalent_iff_card_eq_and_two_dvd_iff_and_χ₈_det_eq_and_eight_dvd hC's d'' (d' i)
      (d''.isUnit_det_of_isPerfPair d'' C'' hC''p)
      ((d' i).isUnit_det_of_isPerfPair (d' i) (C' i) ((h'.isModular i).isPerfPair_of_smul_eq h2i
        (hC' i))) hw'' (hw' i)]
  refine ⟨by rw [Fintype.card_fin, h''.finrank_eq h two_ne_zero PadicInt.not_isUnit_two i,
      hrank i, finrank_eq_card_basis (d' i)],
    (forall_two_dvd_iff_forall_two_mul_pow_dvd hC'').trans
      (((h''.forall_two_mul_pow_dvd_iff_of_isJordanSplitting h i).trans (hpar i)).trans
        (forall_two_dvd_iff_forall_two_mul_pow_dvd (hC' i)).symm),
    hsign_i, PadicInt.eight_dvd_sub_iff_toZModPow_three_eq.mpr hodd_i⟩

/-- **Classification of symmetric bilinear forms over `ℤ_[2]` via Jordan splittings (`ZMod 8`
form).** Purely algebraic formulation of
`LinearMap.BilinForm.IsJordanSplitting.equivalent_iff_prod_χ₈_pow_mul_stdAddChar_sum_eq`
without complex exponentials. -/
theorem IsJordanSplitting.equivalent_iff_toZModPow_sum_add_eq
    [Module.Free ℤ_[2] M] [Module.Finite ℤ_[2] M]
    {M' : Type*} [AddCommGroup M'] [Module ℤ_[2] M']
    {B' : BilinForm ℤ_[2] M'} {N' : ℕ → Submodule ℤ_[2] M'}
    {α α' : ℕ → Type*} [∀ i, Fintype (α i)] [∀ i, DecidableEq (α i)]
    [∀ i, Fintype (α' i)] [∀ i, DecidableEq (α' i)]
    (h : B.IsJordanSplitting 2 N) (h' : B'.IsJordanSplitting 2 N')
    (hB : B.IsSymm) (hB' : B'.IsSymm)
    (C : ∀ i, BilinForm ℤ_[2] (N i)) (hC : ∀ i, (2 : ℤ_[2]) ^ i • C i = B.restrict (N i))
    (d : ∀ i, Basis (α i) ℤ_[2] (N i)) (w : ∀ i, N i)
    (hw : ∀ i, (C i).IsCharacteristic (w i))
    (C' : ∀ i, BilinForm ℤ_[2] (N' i))
    (hC' : ∀ i, (2 : ℤ_[2]) ^ i • C' i = B'.restrict (N' i))
    (d' : ∀ i, Basis (α' i) ℤ_[2] (N' i)) (w' : ∀ i, N' i)
    (hw' : ∀ i, (C' i).IsCharacteristic (w' i)) :
    B.Equivalent B' ↔
      (∀ i, finrank ℤ_[2] (N i) = finrank ℤ_[2] (N' i)) ∧
      (∀ i, (∀ v ∈ N i, 2 * 2 ^ i ∣ B v v) ↔ ∀ v ∈ N' i, 2 * 2 ^ i ∣ B' v v) ∧
      ∀ j, (∀ v ∈ N (j + 1), 2 * 2 ^ (j + 1) ∣ B v v) →
        PadicInt.toZModPow 3 (∑ i ∈ Finset.Iic j, C i (w i) (w i)) +
          (if ∏ i ∈ Finset.Iic j,
              χ₈ (PadicInt.toZModPow 3 ((C i).toMatrix (d i)).det) ^ (j + 1 - i) = -1
            then 4 else 0) =
        PadicInt.toZModPow 3 (∑ i ∈ Finset.Iic j, C' i (w' i) (w' i)) +
          (if ∏ i ∈ Finset.Iic j,
              χ₈ (PadicInt.toZModPow 3 ((C' i).toMatrix (d' i)).det) ^ (j + 1 - i) = -1
            then 4 else 0) := by
  rw [h.equivalent_iff_prod_χ₈_pow_mul_stdAddChar_sum_eq h' hB hB' C hC d w hw C' hC' d' w' hw']
  have h2i (i : ℕ) := mem_nonZeroDivisors_of_ne_zero (pow_ne_zero i (two_ne_zero (α := ℤ_[2])))
  have hpm : ∀ x : ZMod (2 ^ 3), x * x = 1 → χ₈ x = 1 ∨ χ₈ x = -1 := by decide
  have hsC (i : ℕ) : χ₈ (PadicInt.toZModPow 3 ((C i).toMatrix (d i)).det) = 1 ∨
      χ₈ (PadicInt.toZModPow 3 ((C i).toMatrix (d i)).det) = -1 :=
    hpm _ (PadicInt.isUnit_iff_toZModPow_three_mul_self.mp ((d i).isUnit_det_of_isPerfPair (d i)
      (C i) ((h.isModular i).isPerfPair_of_smul_eq (h2i i) (hC i))))
  have hsC' (i : ℕ) : χ₈ (PadicInt.toZModPow 3 ((C' i).toMatrix (d' i)).det) = 1 ∨
      χ₈ (PadicInt.toZModPow 3 ((C' i).toMatrix (d' i)).det) = -1 :=
    hpm _ (PadicInt.isUnit_iff_toZModPow_three_mul_self.mp ((d' i).isUnit_det_of_isPerfPair (d' i)
      (C' i) ((h'.isModular i).isPerfPair_of_smul_eq (h2i i) (hC' i))))
  refine and_congr_right fun _ ↦ and_congr_right fun _ ↦ forall₂_congr fun j _ ↦ ?_
  rw [map_sum (PadicInt.toZModPow 3), map_sum (PadicInt.toZModPow 3),
    prod_pow_mul_stdAddChar_eq_stdAddChar_add_ite (fun i _ ↦ hsC i),
    prod_pow_mul_stdAddChar_eq_stdAddChar_add_ite (fun i _ ↦ hsC' i),
    injective_stdAddChar.eq_iff]

end Classification

end LinearMap.BilinForm

namespace TauCeti

/-- The forms `⟨2, -2⟩` and `2 • U` are not isometric over `ℤ_[2]`: both have scale `2`,
rank `2`, determinant `-4`, and oddity `0`, yet `2 • U` takes values in `4 ℤ_[2]` while
`⟨2, -2⟩` represents `2`. -/
theorem not_equivalent_toBilin'_diagonal_two_neg_two_two_smul_hyperbolic :
    ¬(Matrix.toBilin' (Matrix.diagonal ![2, -2] : Matrix (Fin 2) (Fin 2) ℤ_[2])).Equivalent
      (Matrix.toBilin' ((2 : ℤ_[2]) • !![0, 1; 1, 0])) := by
  rintro ⟨e⟩
  have h4 : (4 : ℤ_[2]) ∣
      Matrix.toBilin' ((2 : ℤ_[2]) • !![0, 1; 1, 0]) (e ![1, 0]) (e ![1, 0]) :=
    ⟨e ![1, 0] 0 * e ![1, 0] 1, by
      simp only [Matrix.toBilin'_apply', Matrix.mulVec, dotProduct, Fin.sum_univ_two,
        Matrix.smul_apply, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_fin_one, smul_eq_mul]; ring⟩
  rw [e.map_app, show Matrix.toBilin' (Matrix.diagonal ![2, -2] : Matrix (Fin 2) (Fin 2) ℤ_[2])
    ![1, 0] ![1, 0] = 2 by
      simp [Matrix.toBilin'_apply', Matrix.mulVec_diagonal, dotProduct, Fin.sum_univ_two]] at h4
  obtain ⟨r, hr⟩ := h4
  exact PadicInt.not_isUnit_two (isUnit_iff_exists_inv.mpr ⟨r,
    mul_left_cancel₀ (two_ne_zero (α := ℤ_[2])) (by linear_combination -hr)⟩)

end TauCeti
