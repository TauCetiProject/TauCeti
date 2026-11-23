/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.Interval.Finset.Nat
public import TauCeti.NumberTheory.Padics.BilinearForm.Classification.Invariants
public import TauCeti.NumberTheory.Padics.BilinearForm.JordanGaussSum
import TauCeti.Analysis.SpecialFunctions.Complex.CircleAddChar
import TauCeti.Order.Interval.Finset.Basic

/-!
# Algebraic partial residue invariants of dyadic Jordan splittings

For a symmetric bilinear form `B` on a finite free `ℤ_[2]`-module with a Jordan splitting `N` with
respect to `2`, the partial residue modulo `8` at scale `j` is

```text
partialOddity j = ∑ i ≤ j, (t i + if Odd (j + 1 - i) ∧ ε i = -1 then 4 else 0),
```

where `ε i` and `t i` are the constituent signs and oddities. Under `ZMod.stdAddChar`, this equals
the normalized Gauss-sum invariant `∏_{i ≤ j} ε i^{j + 1 - i} · e((∑_{i ≤ j} t i) / 8)` from
`TauCeti.NumberTheory.Padics.BilinearForm.JordanGaussSum`. Consequently, whenever `N (j + 1)` is of
type II, `partialOddity j` is an isometry invariant and independent of the Jordan splitting.

## Main definitions and results

* `LinearMap.BilinForm.IsJordanSplitting.partialOddity`: the partial residue modulo `8` at scale
  `j`.
* `LinearMap.BilinForm.IsJordanSplitting.partialOddity_def`, `partialOddity_eq`,
  `partialOddity_eq_sum_add_ite`: expansion and evaluation formulas.
* `LinearMap.BilinForm.IsJordanSplitting.stdAddChar_partialOddity`,
  `stdAddChar_partialOddity_eq`: conversion to the Gauss-sum invariant.
* `LinearMap.BilinForm.IsJordanSplitting.partialOddity_eq_of_equivalent`,
  `partialOddity_eq_of_isJordanSplitting`: invariance under isometry and change of splitting when
  `N (j + 1)` is of type II.
* `LinearMap.BilinForm.IsJordanSplitting.partialOddity_succ_sub_partialOddity_of_eq_bot`: step
  formula across a zero constituent `N (j + 1) = ⊥`.

## References

* J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, Chapter 15, §7.
* O. T. O'Meara, *Introduction to Quadratic Forms*, §93.
-/

public section

open Module ZMod
open LinearMap (BilinForm)

namespace LinearMap.BilinForm

variable {M : Type*} [AddCommGroup M] [Module ℤ_[2] M] {B : BilinForm ℤ_[2] M}
  {N : ℕ → Submodule ℤ_[2] M} {α : ℕ → Type*} [∀ i, Fintype (α i)] [∀ i, DecidableEq (α i)]

variable [Module.Free ℤ_[2] M] [Module.Finite ℤ_[2] M]

/-- The partial residue invariant modulo `8` at scale `j` of a dyadic Jordan splitting: the sum
of the constituent oddities `t i` up to `j`, shifted by `4` for each index `i ≤ j` with
`j + 1 - i` odd and sign `-1`. When `N (j + 1)` is of type II, this residue is an isometry
invariant (`IsJordanSplitting.partialOddity_eq_of_equivalent`). -/
noncomputable def IsJordanSplitting.partialOddity
    (h : B.IsJordanSplitting 2 N) (hB : B.IsSymm) (j : ℕ) : ZMod (2 ^ 3) :=
  ∑ i ∈ Finset.Iic j,
    (h.constituentOddity hB i + if Odd (j + 1 - i) ∧ h.constituentSign i = -1 then 4 else 0)

/-- Formula expanding `IsJordanSplitting.partialOddity` as a sum over `Finset.Iic j`. -/
theorem IsJordanSplitting.partialOddity_def (h : B.IsJordanSplitting 2 N) (hB : B.IsSymm)
    (j : ℕ) :
    h.partialOddity hB j = ∑ i ∈ Finset.Iic j,
      (h.constituentOddity hB i + if Odd (j + 1 - i) ∧ h.constituentSign i = -1 then 4 else 0) :=
  (rfl)

/-- Evaluation of `IsJordanSplitting.partialOddity` from explicit unimodular rescalings, finite
bases, and characteristic vectors on `i ≤ j`. -/
theorem IsJordanSplitting.partialOddity_eq (h : B.IsJordanSplitting 2 N) (hB : B.IsSymm) {j : ℕ}
    (C : ∀ i, BilinForm ℤ_[2] (N i)) (hC : ∀ i ≤ j, (2 : ℤ_[2]) ^ i • C i = B.restrict (N i))
    (d : ∀ i, Basis (α i) ℤ_[2] (N i)) (w : ∀ i, N i)
    (hw : ∀ i ≤ j, (C i).IsCharacteristic (w i)) :
    h.partialOddity hB j = ∑ i ∈ Finset.Iic j, (PadicInt.toZModPow 3 (C i (w i) (w i)) +
      if Odd (j + 1 - i) ∧ χ₈ (PadicInt.toZModPow 3 ((C i).toMatrix (d i)).det) = -1
      then 4 else 0) := by
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  have hij := Finset.mem_Iic.mp hi
  rw [h.constituentOddity_eq hB (hC i hij) (hw i hij), h.constituentSign_eq (hC i hij) (d i)]

/-- Applying `stdAddChar` to `h.partialOddity hB j` yields the partial Gauss-sum invariant of
constituent signs and oddities. -/
theorem IsJordanSplitting.stdAddChar_partialOddity (h : B.IsJordanSplitting 2 N) (hB : B.IsSymm)
    (j : ℕ) :
    stdAddChar (h.partialOddity hB j) =
      (∏ i ∈ Finset.Iic j, (h.constituentSign i : ℂ) ^ (j + 1 - i)) *
        stdAddChar (∑ i ∈ Finset.Iic j, h.constituentOddity hB i) :=
  ZMod.stdAddChar_sum_add_ite_eq_prod_pow_mul_stdAddChar (n := 4)
    (fun i _ ↦ h.constituentSign_eq_one_or_neg_one i) (h.constituentOddity hB) (fun i ↦ j + 1 - i)

/-- Evaluation of `stdAddChar (h.partialOddity hB j)` from explicit unimodular rescalings, finite
bases, and characteristic vectors on `i ≤ j`. -/
theorem IsJordanSplitting.stdAddChar_partialOddity_eq (h : B.IsJordanSplitting 2 N)
    (hB : B.IsSymm) {j : ℕ}
    (C : ∀ i, BilinForm ℤ_[2] (N i)) (hC : ∀ i ≤ j, (2 : ℤ_[2]) ^ i • C i = B.restrict (N i))
    (d : ∀ i, Basis (α i) ℤ_[2] (N i)) (w : ∀ i, N i)
    (hw : ∀ i ≤ j, (C i).IsCharacteristic (w i)) :
    stdAddChar (h.partialOddity hB j) =
      (∏ i ∈ Finset.Iic j,
          ((χ₈ (PadicInt.toZModPow 3 ((C i).toMatrix (d i)).det) : ℤ) : ℂ) ^ (j + 1 - i)) *
        stdAddChar (PadicInt.toZModPow 3 (∑ i ∈ Finset.Iic j, C i (w i) (w i))) := by
  rw [h.stdAddChar_partialOddity hB j, map_sum (PadicInt.toZModPow 3)]
  congr 1
  · refine Finset.prod_congr rfl fun i hi ↦ ?_
    rw [h.constituentSign_eq (hC i (Finset.mem_Iic.mp hi)) (d i)]
  · congr 1
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    exact h.constituentOddity_eq hB (hC i (Finset.mem_Iic.mp hi)) (hw i (Finset.mem_Iic.mp hi))

/-- Alternative form of `IsJordanSplitting.partialOddity` shifting the sum of constituent oddities
by `4` when the product of the sign powers is `-1`. -/
theorem IsJordanSplitting.partialOddity_eq_sum_add_ite (h : B.IsJordanSplitting 2 N)
    (hB : B.IsSymm) (j : ℕ) :
    h.partialOddity hB j = (∑ i ∈ Finset.Iic j, h.constituentOddity hB i) +
      if ∏ i ∈ Finset.Iic j, h.constituentSign i ^ (j + 1 - i) = -1 then 4 else 0 :=
  injective_stdAddChar ((h.stdAddChar_partialOddity hB j).trans
    (ZMod.prod_pow_mul_stdAddChar_eq_stdAddChar_add_ite (n := 4)
      (fun i _ ↦ h.constituentSign_eq_one_or_neg_one i) _ _))

/-- When `N (j + 1)` is of type II, `IsJordanSplitting.partialOddity` is an isometry invariant. -/
theorem IsJordanSplitting.partialOddity_eq_of_equivalent
    {M' : Type*} [AddCommGroup M'] [Module ℤ_[2] M'] [Module.Free ℤ_[2] M']
    [Module.Finite ℤ_[2] M'] {B' : BilinForm ℤ_[2] M'} {N' : ℕ → Submodule ℤ_[2] M'}
    (h : B.IsJordanSplitting 2 N) (h' : B'.IsJordanSplitting 2 N')
    (hB : B.IsSymm) (hB' : B'.IsSymm) (hBB' : B.Equivalent B') {j : ℕ}
    (hnext : ∀ v ∈ N (j + 1), 2 * 2 ^ (j + 1) ∣ B v v) :
    h.partialOddity hB j = h'.partialOddity hB' j := by
  have := h.free; have := h.finite; have := h'.free; have := h'.finite
  apply injective_stdAddChar
  rw [h.stdAddChar_partialOddity_eq hB (h.constituentForm)
      (fun i _ ↦ h.two_pow_smul_constituentForm i)
      (fun i ↦ Module.finBasis ℤ_[2] (N i)) (h.constituentCharVec hB)
      (fun i _ ↦ h.isCharacteristic_constituentCharVec hB i),
    h'.stdAddChar_partialOddity_eq hB' (h'.constituentForm)
      (fun i _ ↦ h'.two_pow_smul_constituentForm i)
      (fun i ↦ Module.finBasis ℤ_[2] (N' i)) (h'.constituentCharVec hB')
      (fun i _ ↦ h'.isCharacteristic_constituentCharVec hB' i)]
  exact h.prod_χ₈_pow_mul_stdAddChar_sum_eq_of_equivalent h' hB hBB' hnext
    (h.constituentForm) (fun i _ ↦ h.two_pow_smul_constituentForm i)
    (fun i ↦ Module.finBasis ℤ_[2] (N i)) (h.constituentCharVec hB)
    (fun i _ ↦ h.isCharacteristic_constituentCharVec hB i)
    (h'.constituentForm) (fun i _ ↦ h'.two_pow_smul_constituentForm i)
    (fun i ↦ Module.finBasis ℤ_[2] (N' i)) (h'.constituentCharVec hB')
    (fun i _ ↦ h'.isCharacteristic_constituentCharVec hB' i)

/-- When `N (j + 1)` is of type II, `IsJordanSplitting.partialOddity` is independent of the choice
of Jordan splitting. -/
theorem IsJordanSplitting.partialOddity_eq_of_isJordanSplitting
    {N' : ℕ → Submodule ℤ_[2] M} (h : B.IsJordanSplitting 2 N) (h' : B.IsJordanSplitting 2 N')
    (hB : B.IsSymm) {j : ℕ} (hnext : ∀ v ∈ N (j + 1), 2 * 2 ^ (j + 1) ∣ B v v) :
    h.partialOddity hB j = h'.partialOddity hB j :=
  h.partialOddity_eq_of_equivalent h' hB hB (.refl B) hnext

/-- Crossing a zero constituent `N (j + 1) = ⊥` shifts `partialOddity` by `4` for each prior
constituent of sign `-1`. -/
theorem IsJordanSplitting.partialOddity_succ_sub_partialOddity_of_eq_bot
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

end LinearMap.BilinForm
