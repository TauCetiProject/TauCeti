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

/-!
# Classification of symmetric bilinear forms over `ℤ_[2]`

Let `B` and `B'` be symmetric bilinear forms on finite free `ℤ_[2]`-modules, with Jordan splittings
`N` and `N'` with respect to `2`, so that `B` restricted to `N i` is `2 ^ i • C i` for a unimodular
form `C i`, and similarly for `B'`. Unlike at odd primes, the individual constituents `N i` are not
isometry invariants: sign walking and oddity fusion move signs and oddities between nearby scales.

This file proves the complete classification of symmetric bilinear forms over `ℤ_[2]` in terms of
any Jordan splittings `N` and `N'`. Two forms `B` and `B'` are isometric if and only if:

1. the constituents have equal rank at every scale `i`;
2. the constituents have the same parity type (type I or type II) at every scale `i`;
3. at every scale `j` where `N (j + 1)` is of type II (including empty constituents), the partial
   Gauss-sum invariant
   ```text
   ∏_{i ≤ j} χ₈(det C i)^{j + 1 - i} · e((∑_{i ≤ j} C i (w i) (w i)) / 8)
   ```
   agrees for `B` and `B'`, where `w i` is a characteristic vector of `C i`.

Equivalently, without complex exponentials, the invariant at `j` is the residue modulo `8` of
`∑_{i ≤ j} C i (w i) (w i) + (if ∏_{i ≤ j} χ₈(det C i)^{j + 1 - i} = -1 then 4 else 0)`.

The parity condition cannot be dropped even at scale `2`: `⟨2, -2⟩` and `2 • U` both have scale
`2`, rank `2`, determinant `-4`, and oddity `0`, yet are not isometric
(`TauCeti.not_equivalent_toBilin'_diagonal_two_neg_two_two_smul_hyperbolic`).

## Main results

* `LinearMap.BilinForm.IsJordanSplitting.exists_constituentSign_and_oddity_eq`: two forms with the
  same constituent ranks, parity types, and partial invariants admit a Jordan splitting of the first
  whose constituent signs and oddities match those of the second at every scale.
* `LinearMap.BilinForm.IsJordanSplitting.equivalent_iff_prod_χ₈_pow_mul_stdAddChar_sum_eq`:
  complete classification of symmetric bilinear forms over `ℤ_[2]` via the Gauss-sum invariants of
  Jordan splittings.
* `LinearMap.BilinForm.IsJordanSplitting.equivalent_iff_toZModPow_sum_add_eq`: the purely algebraic
  `ZMod 8` formulation of the classification.
* `TauCeti.not_equivalent_toBilin'_diagonal_two_neg_two_two_smul_hyperbolic`: `⟨2, -2⟩` and `2 • U`
  are not isometric over `ℤ_[2]`.

## Implementation notes

To prove sufficiency, we sweep through the scales `k = 0, 1, 2, …` by induction, modifying `N` by
elementary moves until the constituent signs and oddities match those of `N'` at every scale
`i < k`. At a type-II scale `k`, either the partial invariant at `k` already forces the sign to
match, or `N (k + 1)` is of type I and a single sign walk on `(k, k + 1)` aligns it. At a maximal
type-I compartment `[k, d]`, a boundary sign walk on `(d, d + 1)` or `(d, d + 2)` aligns the
compartment sign product without changing the partial invariant at `d`, and compartment
normalization (`IsJordanSplitting.exists_constituentSign_and_oddity_eq_on_Icc`) aligns all signs
and oddities in `[k, d]`. Once all signs and oddities match, the unimodular classification yields
an isometry at every scale.

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

/-- The partial Gauss-sum invariant at scale `j` as an element of `ZMod 8`. -/
private def gaussInv (s : ℕ → ℤ) (t : ℕ → ZMod (2 ^ 3)) (j : ℕ) : ZMod (2 ^ 3) :=
  ∑ i ∈ Finset.Iic j, (t i + if Odd (j + 1 - i) ∧ s i = -1 then 4 else 0)

/-- `stdAddChar` sends `4 : ZMod 8` to `-1`. -/
private theorem stdAddChar_four_eq_neg_one : stdAddChar (4 : ZMod (2 ^ 3)) = -1 := by
  have hsq : stdAddChar (4 : ZMod (2 ^ 3)) ^ 2 = 1 := by
    rw [sq, ← AddChar.map_add_eq_mul, show (4 : ZMod (2 ^ 3)) + 4 = 0 by decide,
      AddChar.map_zero_eq_one]
  have hne : stdAddChar (4 : ZMod (2 ^ 3)) ≠ 1 := fun h ↦ by
    rw [← (stdAddChar (N := 2 ^ 3)).map_zero_eq_one, injective_stdAddChar.eq_iff] at h
    exact absurd h (by decide)
  exact (sq_eq_one_iff.mp hsq).resolve_left hne

/-- The `stdAddChar` image of `gaussInv s t j` equals the complex Gauss-sum product. -/
private theorem stdAddChar_gaussInv {s : ℕ → ℤ} {j : ℕ}
    (hs : ∀ i ∈ Finset.Iic j, s i = 1 ∨ s i = -1) (t : ℕ → ZMod (2 ^ 3)) :
    stdAddChar (gaussInv s t j) =
      (∏ i ∈ Finset.Iic j, (s i : ℂ) ^ (j + 1 - i)) * stdAddChar (∑ i ∈ Finset.Iic j, t i) := by
  unfold gaussInv
  rw [Finset.sum_add_distrib, AddChar.map_add_eq_mul, mul_comm, AddChar.map_sum_eq_prod]
  congr 1
  refine Finset.prod_congr rfl fun i hi ↦ ?_
  rcases hs i hi with hsi | hsi
  · simp [hsi]
  · rcases Nat.even_or_odd (j + 1 - i) with hm | hm
    · have hno : ¬Odd (j + 1 - i) := Nat.not_odd_iff_even.mpr hm
      simp [hsi, hm.neg_one_pow, hno]
    · simp only [hsi, hm, and_true, ↓reduceIte, Int.cast_neg, Int.cast_one]
      rw [hm.neg_one_pow, stdAddChar_four_eq_neg_one]

/-- Equivalence between the complex Gauss-sum product and the grouped `ZMod 8` invariant. -/
private theorem prod_pow_mul_stdAddChar_eq_stdAddChar_add_ite {u : Finset ℕ} {s : ℕ → ℤ}
    (hs : ∀ i ∈ u, s i = 1 ∨ s i = -1) (t : ℕ → ZMod (2 ^ 3)) (e : ℕ → ℕ) :
    (∏ i ∈ u, (s i : ℂ) ^ e i) * stdAddChar (∑ i ∈ u, t i) =
      stdAddChar ((∑ i ∈ u, t i) +
        if ∏ i ∈ u, s i ^ e i = -1 then (4 : ZMod (2 ^ 3)) else 0) := by
  have hprod_pm : (∏ i ∈ u, s i ^ e i) = 1 ∨ (∏ i ∈ u, s i ^ e i) = -1 := by
    classical
    induction u using Finset.induction_on with
    | empty => left; simp
    | insert a v ha ih =>
      rw [Finset.prod_insert ha]
      have hpow : s a ^ e a = 1 ∨ s a ^ e a = -1 := by
        rcases hs a (Finset.mem_insert_self a v) with h | h
        · left; rw [h, one_pow]
        · rw [h]
          rcases Nat.even_or_odd (e a) with he | he
          · left; exact he.neg_one_pow
          · right; exact he.neg_one_pow
      rcases hpow with h | h <;>
        rcases ih (fun i hi ↦ hs i (Finset.mem_insert_of_mem hi)) with h2 | h2 <;>
        rw [h, h2] <;> norm_num
  have hcast : (∏ i ∈ u, (s i : ℂ) ^ e i) = ((∏ i ∈ u, s i ^ e i : ℤ) : ℂ) := by
    push_cast
    rfl
  rw [hcast]
  rcases hprod_pm with h | h
  · rw [h]; simp
  · rw [h]
    simp only [Int.cast_neg, Int.cast_one, neg_one_mul, ↓reduceIte, AddChar.map_add_eq_mul,
      stdAddChar_four_eq_neg_one, mul_neg_one]

private theorem Iio_union_Icc_eq_Iic {c d : ℕ} (hcd : c ≤ d) :
    Finset.Iio c ∪ Finset.Icc c d = Finset.Iic d := by
  ext i
  simp only [Finset.mem_union, Finset.mem_Iio, Finset.mem_Icc, Finset.mem_Iic]
  omega

private theorem disjoint_Iio_Icc (c d : ℕ) : Disjoint (Finset.Iio c) (Finset.Icc c d) := by
  rw [Finset.disjoint_left]
  intro i hi1 hi2
  simp only [Finset.mem_Iio] at hi1
  simp only [Finset.mem_Icc] at hi2
  omega

/-- Splitting `gaussInv` at `c ≤ d` into `< c` and `[c, d]`. -/
private theorem gaussInv_eq_sum_Iio_add_Icc (s : ℕ → ℤ) (t : ℕ → ZMod (2 ^ 3))
    {c d : ℕ} (hcd : c ≤ d) :
    gaussInv s t d =
      (∑ i ∈ Finset.Iio c, (t i + if Odd (d + 1 - i) ∧ s i = -1 then 4 else 0)) +
      ∑ i ∈ Finset.Icc c d, (t i + if Odd (d + 1 - i) ∧ s i = -1 then 4 else 0) := by
  unfold gaussInv
  rw [← Finset.sum_union (disjoint_Iio_Icc c d), Iio_union_Icc_eq_Iic hcd]

/-- The difference `gaussInv s t (j + 1) - gaussInv s t j` when `s (j + 1) = 1` and
`t (j + 1) = 0` is the sign parity sum up to `j`. -/
private theorem gaussInv_succ_sub_gaussInv {s : ℕ → ℤ} {t : ℕ → ZMod (2 ^ 3)} {j : ℕ}
    (hs : s (j + 1) = 1) (ht : t (j + 1) = 0) :
    gaussInv s t (j + 1) - gaussInv s t j =
      ∑ i ∈ Finset.Iic j, if s i = -1 then (4 : ZMod (2 ^ 3)) else 0 := by
  unfold gaussInv
  have hIic : Finset.Iic (j + 1) = insert (j + 1) (Finset.Iic j) := by
    ext i
    simp only [Finset.mem_Iic, Finset.mem_insert]
    omega
  rw [hIic, Finset.sum_insert (by simp), hs, ht]
  simp only [show (1 : ℤ) ≠ -1 by decide, and_false, ↓reduceIte, add_zero, zero_add,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  have hij : i ≤ j := Finset.mem_Iic.mp hi
  have hpar : Odd (j + 1 + 1 - i) ↔ ¬Odd (j + 1 - i) := by
    rw [show j + 1 + 1 - i = (j + 1 - i) + 1 by omega, Nat.odd_add_one]
  by_cases hsi : s i = -1
  · by_cases ho : Odd (j + 1 - i)
    · have ho' : ¬Odd (j + 1 + 1 - i) := fun h ↦ hpar.mp h ho
      simp only [hsi, ho, ho', and_true, ↓reduceIte, add_zero, sub_add_eq_sub_sub,
        sub_self, zero_sub]
      decide
    · have ho' : Odd (j + 1 + 1 - i) := hpar.mpr ho
      simp only [hsi, ho, ho', and_true, ↓reduceIte, add_zero, add_sub_cancel_left]
  · simp [hsi]

/-- Flipping `(s d, t d)` to `(-s d, t d + 4)` at the right endpoint `d` of `[k, d]` preserves the
weighted compartment sum and negates the compartment sign product. -/
private theorem flip_end_Icc {s s1 : ℕ → ℤ} {t t1 : ℕ → ZMod (2 ^ 3)} {k d : ℕ} (hkd : k ≤ d)
    (hsd_pm : s d = 1 ∨ s d = -1) (hlt : ∀ i < d, s1 i = s i ∧ t1 i = t i)
    (hsd : s1 d = -s d) (htd : t1 d = t d + 4) :
    (∑ i ∈ Finset.Icc k d, (t1 i + if Odd (d + 1 - i) ∧ s1 i = -1 then 4 else 0)) =
      (∑ i ∈ Finset.Icc k d, (t i + if Odd (d + 1 - i) ∧ s i = -1 then 4 else 0)) ∧
    ∏ i ∈ Finset.Icc k d, s1 i = -(∏ i ∈ Finset.Icc k d, s i) := by
  have hd_mem : d ∈ Finset.Icc k d := Finset.mem_Icc.mpr ⟨hkd, le_rfl⟩
  have hrestT :
      ∑ i ∈ (Finset.Icc k d).erase d, (t1 i + if Odd (d + 1 - i) ∧ s1 i = -1 then 4 else 0) =
      ∑ i ∈ (Finset.Icc k d).erase d, (t i + if Odd (d + 1 - i) ∧ s i = -1 then 4 else 0) := by
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    rw [Finset.mem_erase, Finset.mem_Icc] at hi
    obtain ⟨hs, ht⟩ := hlt i (by omega)
    rw [hs, ht]
  have hrestP : ∏ i ∈ (Finset.Icc k d).erase d, s1 i = ∏ i ∈ (Finset.Icc k d).erase d, s i := by
    refine Finset.prod_congr rfl fun i hi ↦ ?_
    rw [Finset.mem_erase, Finset.mem_Icc] at hi
    exact (hlt i (by omega)).1
  refine ⟨?_, ?_⟩
  · rw [← Finset.add_sum_erase _ _ hd_mem, ← Finset.add_sum_erase _ _ hd_mem, hrestT, hsd, htd,
      Nat.add_sub_cancel_left]
    congr 1
    rcases hsd_pm with h | h <;> rw [h]
    · simp only [odd_one, true_and, show (1 : ℤ) ≠ -1 by decide, ↓reduceIte, add_zero]
      rw [add_assoc, show (4 : ZMod (2 ^ 3)) + 4 = 0 by decide, add_zero]
    · simp only [odd_one, true_and, neg_neg, show (1 : ℤ) ≠ -1 by decide, ↓reduceIte, add_zero]
  · rw [← Finset.mul_prod_erase _ _ hd_mem, ← Finset.mul_prod_erase _ _ hd_mem, hrestP, hsd,
      neg_mul]

end PartialInvariants

/-! ### Left-to-right sweep and Jordan splitting normalization -/

section Normalization

variable {M : Type*} [AddCommGroup M] [Module ℤ_[2] M] {B : BilinForm ℤ_[2] M}
  {N : ℕ → Submodule ℤ_[2] M}

/-- Relating `stdAddChar (gaussInv ...)` to the complex product from `JordanGaussSum`. -/
private theorem stdAddChar_gaussInv_constituent [Module.Free ℤ_[2] M] [Module.Finite ℤ_[2] M]
    (h : B.IsJordanSplitting 2 N) (hB : B.IsSymm)
    {α : ℕ → Type*} [∀ i, Fintype (α i)] [∀ i, DecidableEq (α i)]
    (C : ∀ i, BilinForm ℤ_[2] (N i)) (hC : ∀ i, (2 : ℤ_[2]) ^ i • C i = B.restrict (N i))
    (d : ∀ i, Basis (α i) ℤ_[2] (N i)) (w : ∀ i, N i)
    (hw : ∀ i, (C i).IsCharacteristic (w i)) (j : ℕ) :
    stdAddChar (gaussInv h.constituentSign (h.constituentOddity hB) j) =
      (∏ i ∈ Finset.Iic j, ((χ₈ (PadicInt.toZModPow 3 ((C i).toMatrix (d i)).det) : ℤ) : ℂ) ^
          (j + 1 - i)) *
        stdAddChar (PadicInt.toZModPow 3 (∑ i ∈ Finset.Iic j, C i (w i) (w i))) := by
  rw [stdAddChar_gaussInv (fun i _ ↦ h.constituentSign_eq_one_or_neg_one i)]
  have hdet (i : ℕ) : h.constituentSign i = χ₈ (PadicInt.toZModPow 3 ((C i).toMatrix (d i)).det) :=
    h.constituentSign_eq (hC i) (d i)
  have hodd (i : ℕ) : h.constituentOddity hB i = PadicInt.toZModPow 3 (C i (w i) (w i)) :=
    h.constituentOddity_eq hB (hC i) (hw i)
  simp only [hdet, hodd, ← map_sum]

/-- Two Jordan splittings of `B` have the same `gaussInv` at every scale followed by a type-II
constituent. -/
private theorem gaussInv_eq_of_isJordanSplitting [Module.Free ℤ_[2] M] [Module.Finite ℤ_[2] M]
    {N' : ℕ → Submodule ℤ_[2] M} (h : B.IsJordanSplitting 2 N) (h' : B.IsJordanSplitting 2 N')
    (hB : B.IsSymm) {j : ℕ} (hj : ∀ v ∈ N (j + 1), 2 * 2 ^ (j + 1) ∣ B v v) :
    gaussInv h'.constituentSign (h'.constituentOddity hB) j =
      gaussInv h.constituentSign (h.constituentOddity hB) j := by
  apply injective_stdAddChar
  have : ∀ i, Module.Free ℤ_[2] (N i) := fun i ↦ h.free i
  have : ∀ i, Module.Finite ℤ_[2] (N i) := fun i ↦ h.finite i
  have : ∀ i, Module.Free ℤ_[2] (N' i) := fun i ↦ h'.free i
  have : ∀ i, Module.Finite ℤ_[2] (N' i) := fun i ↦ h'.finite i
  let C (i : ℕ) := (isModular_def.mp (h.isModular i)).choose
  let C' (i : ℕ) := (isModular_def.mp (h'.isModular i)).choose
  have hC (i : ℕ) : (2 : ℤ_[2]) ^ i • C i = B.restrict (N i) :=
    (isModular_def.mp (h.isModular i)).choose_spec.1
  have hC' (i : ℕ) : (2 : ℤ_[2]) ^ i • C' i = B.restrict (N' i) :=
    (isModular_def.mp (h'.isModular i)).choose_spec.1
  have hCp (i : ℕ) : (C i).IsPerfPair := (isModular_def.mp (h.isModular i)).choose_spec.2
  have hC'p (i : ℕ) : (C' i).IsPerfPair := (isModular_def.mp (h'.isModular i)).choose_spec.2
  have h2i (i : ℕ) : (2 : ℤ_[2]) ^ i ∈ nonZeroDivisors ℤ_[2] :=
    mem_nonZeroDivisors_of_ne_zero (pow_ne_zero i two_ne_zero)
  have hCs (i : ℕ) : (C i).IsSymm := IsSymm.of_smul (h2i i) (hC i ▸ hB.restrict (N i))
  have hC's (i : ℕ) : (C' i).IsSymm := IsSymm.of_smul (h2i i) (hC' i ▸ hB.restrict (N' i))
  let w (i : ℕ) : N i :=
    have := hCp i
    ((hCs i).exists_isCharacteristic PadicInt.two_dvd_sq_sub_self).choose
  let w' (i : ℕ) : N' i :=
    have := hC'p i
    ((hC's i).exists_isCharacteristic PadicInt.two_dvd_sq_sub_self).choose
  have hw (i : ℕ) : (C i).IsCharacteristic (w i) :=
    have := hCp i
    ((hCs i).exists_isCharacteristic PadicInt.two_dvd_sq_sub_self).choose_spec
  have hw' (i : ℕ) : (C' i).IsCharacteristic (w' i) :=
    have := hC'p i
    ((hC's i).exists_isCharacteristic PadicInt.two_dvd_sq_sub_self).choose_spec
  rw [stdAddChar_gaussInv_constituent h' hB C' hC' (fun i ↦ Module.finBasis ℤ_[2] (N' i)) w' hw' j,
    stdAddChar_gaussInv_constituent h hB C hC (fun i ↦ Module.finBasis ℤ_[2] (N i)) w hw j]
  exact (h.prod_χ₈_pow_mul_stdAddChar_sum_eq_of_equivalent h' hB (Equivalent.refl B) hj
    C (fun i _ ↦ hC i) (fun i ↦ Module.finBasis ℤ_[2] (N i)) w (fun i _ ↦ hw i)
    C' (fun i _ ↦ hC' i) (fun i ↦ Module.finBasis ℤ_[2] (N' i)) w' (fun i _ ↦ hw' i)).symm

/-- Sign walk between type I at `k` and nonzero type II at `k + 1`. -/
private theorem exists_move_odd_even [Module.Free ℤ_[2] M] [Module.Finite ℤ_[2] M]
    (h : B.IsJordanSplitting 2 N) (hB : B.IsSymm) {k : ℕ}
    (hodd : ¬∀ x ∈ N k, 2 * 2 ^ k ∣ B x x) (heven : ∀ x ∈ N (k + 1), 2 * 2 ^ (k + 1) ∣ B x x)
    (hne : N (k + 1) ≠ ⊥) :
    ∃ N' : ℕ → Submodule ℤ_[2] M, ∃ h' : B.IsJordanSplitting 2 N',
      (∀ i, i ≠ k → i ≠ k + 1 → N' i = N i) ∧
      h'.constituentSign k = -h.constituentSign k ∧
      h'.constituentOddity hB k = h.constituentOddity hB k + 4 := by
  obtain ⟨N', h', hagree, hdk, -, hok⟩ := h.exists_signWalk_succ_of_odd_of_even hB hodd heven hne
  have h5 : IsUnit (5 : ℤ_[2]) :=
    PadicInt.isUnit_iff_toZModPow_three_mul_self.mpr (by rw [map_ofNat]; decide)
  have hχ5 : χ₈ (PadicInt.toZModPow 3 (5 : ℤ_[2])) = -1 := by rw [map_ofNat]; decide
  have hsk := h.constituentSign_eq_mul_of_isSquare_det h' h5 hdk
  rw [hχ5, neg_one_mul] at hsk
  have htk := h.constituentOddity_eq_add_of_eight_dvd h' hB (δ := 4) hok
  rw [map_ofNat] at htk
  exact ⟨N', h', hagree, hsk, htk⟩

/-- Sign walk between nonzero type II at `k` and type I at `k + 1`. -/
private theorem exists_move_even_odd [Module.Free ℤ_[2] M] [Module.Finite ℤ_[2] M]
    (h : B.IsJordanSplitting 2 N) (hB : B.IsSymm) {k : ℕ}
    (heven : ∀ x ∈ N k, 2 * 2 ^ k ∣ B x x) (hne : N k ≠ ⊥)
    (hodd : ¬∀ x ∈ N (k + 1), 2 * 2 ^ (k + 1) ∣ B x x) :
    ∃ N' : ℕ → Submodule ℤ_[2] M, ∃ h' : B.IsJordanSplitting 2 N',
      (∀ i, i ≠ k → i ≠ k + 1 → N' i = N i) ∧
      h'.constituentSign k = -h.constituentSign k := by
  obtain ⟨N', h', hagree, hdk, -, -⟩ := h.exists_signWalk_succ_of_even_of_odd hB heven hne hodd
  have h5 : IsUnit (5 : ℤ_[2]) :=
    PadicInt.isUnit_iff_toZModPow_three_mul_self.mpr (by rw [map_ofNat]; decide)
  have hχ5 : χ₈ (PadicInt.toZModPow 3 (5 : ℤ_[2])) = -1 := by rw [map_ofNat]; decide
  have hsk := h.constituentSign_eq_mul_of_isSquare_det h' h5 hdk
  rw [hχ5, neg_one_mul] at hsk
  exact ⟨N', h', hagree, hsk⟩

/-- Sign walk between type I at `k` and type I at `k + 2`. -/
private theorem exists_move_odd_add_two_odd [Module.Free ℤ_[2] M] [Module.Finite ℤ_[2] M]
    (h : B.IsJordanSplitting 2 N) (hB : B.IsSymm) {k : ℕ}
    (hodd : ¬∀ x ∈ N k, 2 * 2 ^ k ∣ B x x)
    (hodd' : ¬∀ x ∈ N (k + 2), 2 * 2 ^ (k + 2) ∣ B x x) :
    ∃ N' : ℕ → Submodule ℤ_[2] M, ∃ h' : B.IsJordanSplitting 2 N',
      (∀ i, i ≠ k → i ≠ k + 2 → N' i = N i) ∧
      h'.constituentSign k = -h.constituentSign k ∧
      h'.constituentOddity hB k = h.constituentOddity hB k + 4 := by
  obtain ⟨N', h', hagree, hdk, -, hok, -⟩ := h.exists_signWalk_add_two_of_odd_of_odd hB hodd hodd'
  have h5 : IsUnit (5 : ℤ_[2]) :=
    PadicInt.isUnit_iff_toZModPow_three_mul_self.mpr (by rw [map_ofNat]; decide)
  have hχ5 : χ₈ (PadicInt.toZModPow 3 (5 : ℤ_[2])) = -1 := by rw [map_ofNat]; decide
  have hsk := h.constituentSign_eq_mul_of_isSquare_det h' h5 hdk
  rw [hχ5, neg_one_mul] at hsk
  have htk := h.constituentOddity_eq_add_of_eight_dvd h' hB (δ := 4) hok
  rw [map_ofNat] at htk
  exact ⟨N', h', hagree, hsk, htk⟩

/-- **Left-to-right sweep.** Given Jordan splittings `h` of `B` and `h'` of `B'` with equal
constituent ranks, parity types, and partial `gaussInv` invariants at every scale followed by a
type-II constituent, for every `k` there exists a Jordan splitting of `B` matching the signs and
oddities of `h'` at every index `i < k`. -/
private theorem exists_isJordanSplitting_matching_below [Module.Free ℤ_[2] M]
    [Module.Finite ℤ_[2] M] {M' : Type*} [AddCommGroup M'] [Module ℤ_[2] M']
    [Module.Free ℤ_[2] M'] [Module.Finite ℤ_[2] M'] {B' : BilinForm ℤ_[2] M'}
    {N' : ℕ → Submodule ℤ_[2] M'} (h : B.IsJordanSplitting 2 N) (h' : B'.IsJordanSplitting 2 N')
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
    have hrank_k (i : ℕ) : finrank ℤ_[2] (Nk i) = finrank ℤ_[2] (N' i) :=
      (hk.finrank_eq h two_ne_zero PadicInt.not_isUnit_two i).trans (hrank i)
    have hpar_k (i : ℕ) : (∀ v ∈ Nk i, 2 * 2 ^ i ∣ B v v) ↔ ∀ v ∈ N' i, 2 * 2 ^ i ∣ B' v v :=
      ⟨fun he ↦ (hpar i).mp (hk.forall_two_mul_pow_dvd_of_equivalent h (Equivalent.refl B)
          (mem_nonZeroDivisors_of_ne_zero two_ne_zero) dvd_rfl he),
        fun he ↦ h.forall_two_mul_pow_dvd_of_equivalent hk (Equivalent.refl B)
          (mem_nonZeroDivisors_of_ne_zero two_ne_zero) dvd_rfl ((hpar i).mpr he)⟩
    have hbot_iff (i : ℕ) : Nk i = ⊥ ↔ N' i = ⊥ := by
      have := hk.finite i; have := h'.finite i
      rw [← Submodule.finrank_eq_zero, ← Submodule.finrank_eq_zero, hrank_k i]
    have hgauss_k (j : ℕ) (hj : ∀ v ∈ Nk (j + 1), 2 * 2 ^ (j + 1) ∣ B v v) :
        gaussInv hk.constituentSign (hk.constituentOddity hB) j =
          gaussInv h'.constituentSign (h'.constituentOddity hB') j := by
      have hjN : ∀ v ∈ N (j + 1), 2 * 2 ^ (j + 1) ∣ B v v := (hpar (j + 1)).mpr ((hpar_k _).mp hj)
      exact (gaussInv_eq_of_isJordanSplitting h hk hB hjN).trans (hgauss j hjN)
    by_cases heven_k : ∀ v ∈ Nk k, 2 * 2 ^ k ∣ B v v
    · -- Case 1: `Nk k` is of type II.
      have htk : hk.constituentOddity hB k = 0 := hk.constituentOddity_of_even hB heven_k
      have ht'k : h'.constituentOddity hB' k = 0 :=
        h'.constituentOddity_of_even hB' ((hpar_k k).mp heven_k)
      by_cases hbot_k : Nk k = ⊥
      · refine ⟨Nk, hk, fun i hi ↦ ?_⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
        · exact hmatch i hi
        · exact ⟨(hk.constituentSign_of_eq_bot hbot_k).trans
            (h'.constituentSign_of_eq_bot ((hbot_iff i).mp hbot_k)).symm, htk.trans ht'k.symm⟩
      · by_cases heven_next : ∀ v ∈ Nk (k + 1), 2 * 2 ^ (k + 1) ∣ B v v
        · -- Subcase 1b: `Nk (k + 1)` is also of type II; `gaussInv` at `k` forces signs to match.
          have hGk := hgauss_k k heven_next
          rw [gaussInv_eq_sum_Iio_add_Icc _ _ le_rfl,
            gaussInv_eq_sum_Iio_add_Icc _ _ le_rfl] at hGk
          have hpre :
              ∑ i ∈ Finset.Iio k, (hk.constituentOddity hB i +
                if Odd (k + 1 - i) ∧ hk.constituentSign i = -1 then 4 else 0) =
              ∑ i ∈ Finset.Iio k, (h'.constituentOddity hB' i +
                if Odd (k + 1 - i) ∧ h'.constituentSign i = -1 then 4 else 0) :=
            Finset.sum_congr rfl fun i hi ↦ by
              obtain ⟨hs, ht⟩ := hmatch i (Finset.mem_Iio.mp hi); rw [hs, ht]
          rw [hpre] at hGk
          have hcomp := add_left_cancel hGk
          simp only [Finset.Icc_self, Finset.sum_singleton, Nat.add_sub_cancel_left,
            odd_one, true_and, htk, ht'k, zero_add] at hcomp
          have hsk : hk.constituentSign k = h'.constituentSign k := by
            rcases hk.constituentSign_eq_one_or_neg_one k with h1 | h1 <;>
              rcases h'.constituentSign_eq_one_or_neg_one k with h2 | h2 <;>
              rw [h1, h2] at hcomp ⊢ <;>
              exact absurd hcomp (by decide)
          refine ⟨Nk, hk, fun i hi ↦ ?_⟩
          rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
          · exact hmatch i hi
          · exact ⟨hsk, htk.trans ht'k.symm⟩
        · -- Subcase 1c: `Nk (k + 1)` is of type I; sign-walk on `(k, k + 1)` if needed.
          by_cases hsk : hk.constituentSign k = h'.constituentSign k
          · refine ⟨Nk, hk, fun i hi ↦ ?_⟩
            rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
            · exact hmatch i hi
            · exact ⟨hsk, htk.trans ht'k.symm⟩
          · obtain ⟨N1, h1, hagree1, hs1k⟩ :=
              exists_move_even_odd hk hB heven_k hbot_k heven_next
            have heven1 : ∀ v ∈ N1 k, 2 * 2 ^ k ∣ B v v :=
              hk.forall_two_mul_pow_dvd_of_equivalent h1 (Equivalent.refl B)
                (mem_nonZeroDivisors_of_ne_zero two_ne_zero) dvd_rfl heven_k
            refine ⟨N1, h1, fun i hi ↦ ?_⟩
            rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
            · have hEq := hagree1 i (by omega) (by omega)
              exact ⟨(hk.constituentSign_eq_of_eq h1 hEq).trans (hmatch i hi).1,
                (hk.constituentOddity_eq_of_eq h1 hB hEq).trans (hmatch i hi).2⟩
            · refine ⟨?_, (h1.constituentOddity_of_even hB heven1).trans ht'k.symm⟩
              rw [hs1k]
              rcases hk.constituentSign_eq_one_or_neg_one i with h1' | h1' <;>
                rcases h'.constituentSign_eq_one_or_neg_one i with h2' | h2'
              · exact absurd (h1'.trans h2'.symm) hsk
              · rw [h1', h2']
              · rw [h1', h2']; norm_num
              · exact absurd (h1'.trans h2'.symm) hsk
    · -- Case 2: `Nk k` is of type I. Find the end `d ≥ k` of its type-I compartment.
      classical
      have hex : ∃ d, k ≤ d ∧ ∀ v ∈ Nk (d + 1), 2 * 2 ^ (d + 1) ∣ B v v := by
        obtain ⟨m, hm⟩ := hk.hasFiniteSupport.bddAbove
        refine ⟨max k m, le_max_left k m, fun v hv ↦ ?_⟩
        have hbot : Nk (max k m + 1) = ⊥ := by
          by_contra hne; have := hm hne; omega
        rw [hbot, Submodule.mem_bot] at hv; simp [hv]
      let d := Nat.find hex
      have hkd : k ≤ d := (Nat.find_spec hex).1
      have heven_d1 : ∀ v ∈ Nk (d + 1), 2 * 2 ^ (d + 1) ∣ B v v := (Nat.find_spec hex).2
      have hodd_block : ∀ i ∈ Finset.Icc k d, ¬∀ v ∈ Nk i, 2 * 2 ^ i ∣ B v v := by
        intro i hi
        rw [Finset.mem_Icc] at hi
        rcases eq_or_lt_of_le hi.1 with rfl | hki
        · exact heven_k
        · intro heven_i
          exact Nat.find_min hex (show i - 1 < d by omega)
            ⟨by omega, by simpa only [show i - 1 + 1 = i by omega] using heven_i⟩
      have hTd :
          (∑ i ∈ Finset.Icc k d,
            (hk.constituentOddity hB i +
              if Odd (d + 1 - i) ∧ hk.constituentSign i = -1 then 4 else 0)) =
          ∑ i ∈ Finset.Icc k d,
            (h'.constituentOddity hB' i +
              if Odd (d + 1 - i) ∧ h'.constituentSign i = -1 then 4 else 0) := by
        have hGd := hgauss_k d heven_d1
        rw [gaussInv_eq_sum_Iio_add_Icc _ _ hkd, gaussInv_eq_sum_Iio_add_Icc _ _ hkd] at hGd
        have hpre :
            ∑ i ∈ Finset.Iio k, (hk.constituentOddity hB i +
              if Odd (d + 1 - i) ∧ hk.constituentSign i = -1 then 4 else 0) =
            ∑ i ∈ Finset.Iio k, (h'.constituentOddity hB' i +
              if Odd (d + 1 - i) ∧ h'.constituentSign i = -1 then 4 else 0) :=
          Finset.sum_congr rfl fun i hi ↦ by
            obtain ⟨hs, ht⟩ := hmatch i (Finset.mem_Iio.mp hi); rw [hs, ht]
        rw [hpre] at hGd
        exact add_left_cancel hGd
      -- Align the compartment sign product on `[k, d]` without disturbing `i < k` or `hTd`.
      have hstepS : ∃ N1 : ℕ → Submodule ℤ_[2] M, ∃ h1 : B.IsJordanSplitting 2 N1,
          (∀ i < k, N1 i = Nk i) ∧
          (∑ i ∈ Finset.Icc k d,
            (h1.constituentOddity hB i +
              if Odd (d + 1 - i) ∧ h1.constituentSign i = -1 then 4 else 0)) =
          (∑ i ∈ Finset.Icc k d,
            (h'.constituentOddity hB' i +
              if Odd (d + 1 - i) ∧ h'.constituentSign i = -1 then 4 else 0)) ∧
          ∏ i ∈ Finset.Icc k d, h1.constituentSign i =
            ∏ i ∈ Finset.Icc k d, h'.constituentSign i := by
        by_cases hSd : ∏ i ∈ Finset.Icc k d, hk.constituentSign i =
            ∏ i ∈ Finset.Icc k d, h'.constituentSign i
        · exact ⟨Nk, hk, fun _ _ ↦ rfl, hTd, hSd⟩
        · have hodd_d : ¬∀ v ∈ Nk d, 2 * 2 ^ d ∣ B v v :=
            hodd_block d (Finset.mem_Icc.mpr ⟨hkd, le_rfl⟩)
          have hprod_hk : (∏ i ∈ Finset.Icc k d, hk.constituentSign i) = 1 ∨
              (∏ i ∈ Finset.Icc k d, hk.constituentSign i) = -1 := by
            rw [hk.prod_constituentSign_eq_ite]; split_ifs <;> simp
          have hprod_h' : (∏ i ∈ Finset.Icc k d, h'.constituentSign i) = 1 ∨
              (∏ i ∈ Finset.Icc k d, h'.constituentSign i) = -1 := by
            rw [h'.prod_constituentSign_eq_ite]; split_ifs <;> simp
          have hflip_step : ∀ (N1 : ℕ → Submodule ℤ_[2] M) (h1 : B.IsJordanSplitting 2 N1),
              (∀ i, i < d → N1 i = Nk i) →
              h1.constituentSign d = -hk.constituentSign d →
              h1.constituentOddity hB d = hk.constituentOddity hB d + 4 →
              (∑ i ∈ Finset.Icc k d,
                (h1.constituentOddity hB i +
                  if Odd (d + 1 - i) ∧ h1.constituentSign i = -1 then 4 else 0)) =
              (∑ i ∈ Finset.Icc k d,
                (h'.constituentOddity hB' i +
                  if Odd (d + 1 - i) ∧ h'.constituentSign i = -1 then 4 else 0)) ∧
              ∏ i ∈ Finset.Icc k d, h1.constituentSign i =
                ∏ i ∈ Finset.Icc k d, h'.constituentSign i := by
            intro N1 h1 hlt hsd htd
            obtain ⟨hT1, hP1⟩ := flip_end_Icc hkd (hk.constituentSign_eq_one_or_neg_one d)
              (fun i hi ↦ ⟨hk.constituentSign_eq_of_eq h1 (hlt i hi),
                hk.constituentOddity_eq_of_eq h1 hB (hlt i hi)⟩) hsd htd
            refine ⟨hT1.trans hTd, ?_⟩
            rw [hP1]
            rcases hprod_hk with h1' | h1' <;> rcases hprod_h' with h2' | h2'
            · exact absurd (h1'.trans h2'.symm) hSd
            · rw [h1', h2']
            · rw [h1', h2']; norm_num
            · exact absurd (h1'.trans h2'.symm) hSd
          by_cases hbot_d1 : Nk (d + 1) = ⊥
          · by_cases heven_d2 : ∀ v ∈ Nk (d + 2), 2 * 2 ^ (d + 2) ∣ B v v
            · exfalso
              have hGd := hgauss_k d heven_d1
              have hGd1 := hgauss_k (d + 1) heven_d2
              have hs_d1 : hk.constituentSign (d + 1) = 1 := hk.constituentSign_of_eq_bot hbot_d1
              have ht_d1 : hk.constituentOddity hB (d + 1) = 0 :=
                hk.constituentOddity_of_eq_bot hB hbot_d1
              have hs'_d1 : h'.constituentSign (d + 1) = 1 :=
                h'.constituentSign_of_eq_bot ((hbot_iff (d + 1)).mp hbot_d1)
              have ht'_d1 : h'.constituentOddity hB' (d + 1) = 0 :=
                h'.constituentOddity_of_eq_bot hB' ((hbot_iff (d + 1)).mp hbot_d1)
              have hdiff :
                  (∑ i ∈ Finset.Iic d,
                    if hk.constituentSign i = -1 then (4 : ZMod (2 ^ 3)) else 0) =
                  ∑ i ∈ Finset.Iic d,
                    if h'.constituentSign i = -1 then (4 : ZMod (2 ^ 3)) else 0 := by
                rw [← gaussInv_succ_sub_gaussInv hs_d1 ht_d1,
                  ← gaussInv_succ_sub_gaussInv hs'_d1 ht'_d1, hGd, hGd1]
              rw [← Iio_union_Icc_eq_Iic hkd, Finset.sum_union (disjoint_Iio_Icc k d),
                Finset.sum_union (disjoint_Iio_Icc k d)] at hdiff
              have hpre :
                  ∑ i ∈ Finset.Iio k,
                    (if hk.constituentSign i = -1 then (4 : ZMod (2 ^ 3)) else 0) =
                  ∑ i ∈ Finset.Iio k,
                    (if h'.constituentSign i = -1 then (4 : ZMod (2 ^ 3)) else 0) :=
                Finset.sum_congr rfl fun i hi ↦ by rw [(hmatch i (Finset.mem_Iio.mp hi)).1]
              rw [hpre] at hdiff
              have hsum_eq := add_left_cancel hdiff
              apply hSd
              rw [hk.prod_constituentSign_eq_ite, h'.prod_constituentSign_eq_ite, hsum_eq]
            · obtain ⟨N1, h1, hagree1, hsd, htd⟩ :=
                exists_move_odd_add_two_odd hk hB hodd_d heven_d2
              have hlt : ∀ i, i < d → N1 i = Nk i := fun i hi ↦ hagree1 i (by omega) (by omega)
              have hTS := hflip_step N1 h1 hlt hsd htd
              exact ⟨N1, h1, fun i hi ↦ hlt i (by omega), hTS.1, hTS.2⟩
          · obtain ⟨N1, h1, hagree1, hsd, htd⟩ :=
              exists_move_odd_even hk hB hodd_d heven_d1 hbot_d1
            have hlt : ∀ i, i < d → N1 i = Nk i := fun i hi ↦ hagree1 i (by omega) (by omega)
            have hTS := hflip_step N1 h1 hlt hsd htd
            exact ⟨N1, h1, fun i hi ↦ hlt i (by omega), hTS.1, hTS.2⟩
      obtain ⟨N1, h1, hagree1, hT1, hS1⟩ := hstepS
      have hrank1 (i : ℕ) : finrank ℤ_[2] (N1 i) = finrank ℤ_[2] (N' i) :=
        (h1.finrank_eq hk two_ne_zero PadicInt.not_isUnit_two i).trans (hrank_k i)
      have hpar1 (i : ℕ) : (∀ v ∈ N1 i, 2 * 2 ^ i ∣ B v v) ↔ ∀ v ∈ Nk i, 2 * 2 ^ i ∣ B v v :=
        ⟨fun he ↦ h1.forall_two_mul_pow_dvd_of_equivalent hk (Equivalent.refl B)
            (mem_nonZeroDivisors_of_ne_zero two_ne_zero) dvd_rfl he,
          fun he ↦ hk.forall_two_mul_pow_dvd_of_equivalent h1 (Equivalent.refl B)
            (mem_nonZeroDivisors_of_ne_zero two_ne_zero) dvd_rfl he⟩
      have hodd1 : ∀ i ∈ Finset.Icc k d, ¬∀ v ∈ N1 i, 2 * 2 ^ i ∣ B v v := fun i hi ↦ by
        rw [hpar1 i]; exact hodd_block i hi
      have hodd' : ∀ i ∈ Finset.Icc k d, ¬∀ v ∈ N' i, 2 * 2 ^ i ∣ B' v v := fun i hi ↦ by
        rw [← hpar_k i]; exact hodd_block i hi
      obtain ⟨N2, h2, hagree2, hmatch2⟩ := h1.exists_constituentSign_and_oddity_eq_on_Icc h' hB hB'
        (fun i _ ↦ hrank1 i) hodd1 hodd' hT1 hS1
      refine ⟨N2, h2, fun i hi ↦ ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
      · have hi_notMem : i ∉ Finset.Icc k d := by simp only [Finset.mem_Icc]; omega
        have hEq2 := hagree2 i hi_notMem
        have hEq1 := hagree1 i hi
        exact ⟨(h1.constituentSign_eq_of_eq h2 hEq2).trans
            ((hk.constituentSign_eq_of_eq h1 hEq1).trans (hmatch i hi).1),
          (h1.constituentOddity_eq_of_eq h2 hB hEq2).trans
            ((hk.constituentOddity_eq_of_eq h1 hB hEq1).trans (hmatch i hi).2)⟩
      · exact hmatch2 i (Finset.mem_Icc.mpr ⟨le_rfl, hkd⟩)

/-- **Jordan splitting normalization over `ℤ_[2]`.** Let `B` and `B'` be symmetric bilinear forms
on finite free `ℤ_[2]`-modules with Jordan splittings `N` and `N'` with respect to `2`. If `N` and
`N'` have the same constituent ranks, the same parity types at every scale, and the same partial
invariants at every scale followed by a type-II constituent, then `B` admits a Jordan splitting
`N''` whose constituent signs and oddities match those of `N'` at every scale. -/
theorem IsJordanSplitting.exists_constituentSign_and_oddity_eq
    [Module.Free ℤ_[2] M] [Module.Finite ℤ_[2] M]
    {M' : Type*} [AddCommGroup M'] [Module ℤ_[2] M'] [Module.Free ℤ_[2] M'] [Module.Finite ℤ_[2] M']
    {B' : BilinForm ℤ_[2] M'} {N' : ℕ → Submodule ℤ_[2] M'}
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
  obtain ⟨m, hm⟩ : ∃ m, ∀ i ≥ m, N i = ⊥ := by
    obtain ⟨b, hb⟩ := h.hasFiniteSupport.bddAbove
    exact ⟨b + 1, fun i hi ↦ by by_contra hne; have := hb hne; omega⟩
  obtain ⟨N'', h'', hmatch⟩ :=
    exists_isJordanSplitting_matching_below h h' hB hB' hrank hpar hinv m
  refine ⟨N'', h'', fun i ↦ ?_⟩
  by_cases him : i < m
  · exact hmatch i him
  · have hbotN : N i = ⊥ := hm i (by omega)
    have := h''.finite i; have := h'.finite i
    have hbotN'' : N'' i = ⊥ := Submodule.finrank_eq_zero.mp
      (by rw [h''.finrank_eq h two_ne_zero PadicInt.not_isUnit_two i, hbotN, finrank_bot])
    have hbotN' : N' i = ⊥ := Submodule.finrank_eq_zero.mp (by rw [← hrank i, hbotN, finrank_bot])
    exact ⟨(h''.constituentSign_of_eq_bot hbotN'').trans (h'.constituentSign_of_eq_bot hbotN').symm,
      (h''.constituentOddity_of_eq_bot hB hbotN'').trans
        (h'.constituentOddity_of_eq_bot hB' hbotN').symm⟩

end Normalization

/-! ### Complete classification of symmetric bilinear forms over `ℤ_[2]` -/

section Classification

variable {M : Type*} [AddCommGroup M] [Module ℤ_[2] M] {B : BilinForm ℤ_[2] M}
  {N : ℕ → Submodule ℤ_[2] M}

/-- A unimodular rescaling `C` of a Jordan constituent `N i` is even iff `2 * 2 ^ i` divides
`B v v` for all `v ∈ N i`. -/
private theorem forall_two_dvd_iff_forall_two_mul_pow_dvd {P : Submodule ℤ_[2] M} {i : ℕ}
    {C : BilinForm ℤ_[2] P} (hC : (2 : ℤ_[2]) ^ i • C = B.restrict P) :
    (∀ x : P, (2 : ℤ_[2]) ∣ C x x) ↔ ∀ v ∈ P, 2 * 2 ^ i ∣ B v v := by
  have h2i : (2 : ℤ_[2]) ^ i ∈ nonZeroDivisors ℤ_[2] :=
    mem_nonZeroDivisors_of_ne_zero (pow_ne_zero i two_ne_zero)
  refine ⟨fun he v hv ↦ ?_, fun he x ↦ ?_⟩
  · obtain ⟨c, hc⟩ := he ⟨v, hv⟩
    have hBC : (2 : ℤ_[2]) ^ i * C ⟨v, hv⟩ ⟨v, hv⟩ = B v v := by
      simpa using LinearMap.congr_fun₂ hC ⟨v, hv⟩ ⟨v, hv⟩
    exact ⟨c, by rw [← hBC, hc]; ring⟩
  · obtain ⟨c, hc⟩ := he x x.2
    have hBC : (2 : ℤ_[2]) ^ i * C x x = B x x := by
      simpa using LinearMap.congr_fun₂ hC x x
    exact ⟨c, (mul_cancel_left_mem_nonZeroDivisors h2i).mp (by rw [hBC]; linear_combination hc)⟩

/-- A module with a finitely supported Jordan splitting whose constituents have finite bases is
finite and free. -/
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
  have hindep : iSupIndep (fun i : Fin m ↦ N' i) :=
    ((DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top _).mp h'.isInternal).1.comp
      Fin.val_injective
  have hint : DirectSum.IsInternal (fun i : Fin m ↦ N' i) :=
    (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top _).mpr ⟨hindep, hsup⟩
  let e : (∀ i : Fin m, N' i) ≃ₗ[ℤ_[2]] M' :=
    (DirectSum.linearEquivFunOnFintype ℤ_[2] (Fin m) (fun i : Fin m ↦ N' i)).symm.trans
      (LinearEquiv.ofBijective (DirectSum.coeLinearMap (fun i : Fin m ↦ N' i)) hint)
  exact ⟨Module.Free.of_equiv e, Module.Finite.equiv e⟩

/-- **Classification of symmetric bilinear forms over `ℤ_[2]` via Jordan splittings (Gauss-sum
form).** Let `B` and `B'` be symmetric bilinear forms over `ℤ_[2]` with `M` finite free, and let
`N` and `N'` be Jordan splittings of `B` and `B'` with respect to `2`. For each `i`, let `C i` and
`C' i` be the unimodular rescalings of `N i` and `N' i`, with bases `d i`, `d' i` and
characteristic vectors `w i`, `w' i`. Then `B` and `B'` are isometric if and only if:

1. `N i` and `N' i` have the same rank for every `i`,
2. `N i` is of type II if and only if `N' i` is of type II for every `i`, and
3. for every `j` such that `N (j + 1)` is of type II (including `N (j + 1) = ⊥`), the partial
   Gauss-sum invariants agree:
   ```text
   ∏_{i ≤ j} χ₈(det C i)^{j + 1 - i} · e((∑_{i ≤ j} C i (w i) (w i)) / 8)
     = ∏_{i ≤ j} χ₈(det C' i)^{j + 1 - i} · e((∑_{i ≤ j} C' i (w' i) (w' i)) / 8).
   ```

This is the converse and complete characterization extending
`LinearMap.BilinForm.IsJordanSplitting.prod_χ₈_pow_mul_stdAddChar_sum_eq_of_equivalent`. -/
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
    (C' : ∀ i, BilinForm ℤ_[2] (N' i)) (hC' : ∀ i, (2 : ℤ_[2]) ^ i • C' i = B'.restrict (N' i))
    (d' : ∀ i, Basis (α' i) ℤ_[2] (N' i)) (w' : ∀ i, N' i)
    (hw' : ∀ i, (C' i).IsCharacteristic (w' i)) :
    B.Equivalent B' ↔
      (∀ i, finrank ℤ_[2] (N i) = finrank ℤ_[2] (N' i)) ∧
      (∀ i, (∀ v ∈ N i, 2 * 2 ^ i ∣ B v v) ↔ ∀ v ∈ N' i, 2 * 2 ^ i ∣ B' v v) ∧
      ∀ j, (∀ v ∈ N (j + 1), 2 * 2 ^ (j + 1) ∣ B v v) →
        (∏ i ∈ Finset.Iic j, ((χ₈ (PadicInt.toZModPow 3 ((C i).toMatrix (d i)).det) : ℤ) : ℂ) ^
            (j + 1 - i)) *
          stdAddChar (PadicInt.toZModPow 3 (∑ i ∈ Finset.Iic j, C i (w i) (w i))) =
        (∏ i ∈ Finset.Iic j, ((χ₈ (PadicInt.toZModPow 3 ((C' i).toMatrix (d' i)).det) : ℤ) : ℂ) ^
            (j + 1 - i)) *
          stdAddChar (PadicInt.toZModPow 3 (∑ i ∈ Finset.Iic j, C' i (w' i) (w' i))) := by
  refine ⟨fun hBB' ↦ ?_, ?_⟩
  · obtain ⟨ε⟩ := hBB'
    have : Module.Free ℤ_[2] M' := Module.Free.of_equiv ε.toLinearEquiv
    have : Module.Finite ℤ_[2] M' := Module.Finite.equiv ε.toLinearEquiv
    exact ⟨fun i ↦ h.finrank_eq_of_equivalent h' ⟨ε⟩ two_ne_zero PadicInt.not_isUnit_two i,
      fun i ↦ ⟨fun he ↦ h.forall_two_mul_pow_dvd_of_equivalent h' ⟨ε⟩
          (mem_nonZeroDivisors_of_ne_zero two_ne_zero) dvd_rfl he,
        fun he ↦ h'.forall_two_mul_pow_dvd_of_equivalent h ⟨ε.symm⟩
          (mem_nonZeroDivisors_of_ne_zero two_ne_zero) dvd_rfl he⟩,
      fun j hj ↦ h.prod_χ₈_pow_mul_stdAddChar_sum_eq_of_equivalent h' hB ⟨ε⟩ hj
        C (fun i _ ↦ hC i) d w (fun i _ ↦ hw i)
        C' (fun i _ ↦ hC' i) d' w' (fun i _ ↦ hw' i)⟩
  rintro ⟨hrank, hpar, hG⟩
  -- Deduce `Module.Free ℤ_[2] M'` and `Module.Finite ℤ_[2] M'` from `d'` and `hrank`.
  obtain ⟨m, hm⟩ : ∃ m, ∀ i ≥ m, N' i = ⊥ := by
    obtain ⟨b, hb⟩ := h.hasFiniteSupport.bddAbove
    refine ⟨b + 1, fun i hi ↦ ?_⟩
    have hbotN : N i = ⊥ := by by_contra hne; have := hb hne; omega
    have hcard : Fintype.card (α' i) = 0 := by
      rw [← finrank_eq_card_basis (d' i), ← hrank i, hbotN, finrank_bot]
    have : IsEmpty (α' i) := Fintype.card_eq_zero_iff.mp hcard
    rw [Submodule.eq_bot_iff]
    intro x hx
    exact congrArg Subtype.val
      ((d' i).repr.injective (Subsingleton.elim ((d' i).repr ⟨x, hx⟩) ((d' i).repr 0)))
  obtain ⟨_, _⟩ := free_and_finite_of_isJordanSplitting h' d' hm
  have hinv : ∀ j, (∀ v ∈ N (j + 1), 2 * 2 ^ (j + 1) ∣ B v v) →
      gaussInv h.constituentSign (h.constituentOddity hB) j =
        gaussInv h'.constituentSign (h'.constituentOddity hB') j := fun j hj ↦ by
    apply injective_stdAddChar
    rw [stdAddChar_gaussInv_constituent h hB C hC d w hw j,
      stdAddChar_gaussInv_constituent h' hB' C' hC' d' w' hw' j]
    exact hG j hj
  -- Normalize `N` to a Jordan splitting `N''` matching all signs and oddities of `N'`.
  obtain ⟨N'', h'', hmatch⟩ :=
    h.exists_constituentSign_and_oddity_eq h' hB hB' hrank hpar hinv
  -- Compare each constituent `N'' i` with `N' i` via the unimodular classification.
  refine equivalent_of_isInternal h''.isInternal h'.isInternal h''.apply_eq_zero h'.apply_eq_zero
    fun i ↦ ?_
  have h2i : (2 : ℤ_[2]) ^ i ∈ nonZeroDivisors ℤ_[2] :=
    mem_nonZeroDivisors_of_ne_zero (pow_ne_zero i two_ne_zero)
  have := h''.free i
  have := h''.finite i
  obtain ⟨C'', hC'', hC''p⟩ := isModular_def.mp (h''.isModular i)
  have hC''s : C''.IsSymm := IsSymm.of_smul h2i (hC'' ▸ hB.restrict (N'' i))
  have hC's : (C' i).IsSymm := IsSymm.of_smul h2i (hC' i ▸ hB'.restrict (N' i))
  have hC'p : (C' i).IsPerfPair := (h'.isModular i).isPerfPair_of_smul_eq h2i (hC' i)
  let d'' := Module.finBasis ℤ_[2] (N'' i)
  have hC''det : IsUnit (C''.toMatrix d'').det := d''.isUnit_det_of_isPerfPair d'' C'' hC''p
  have hC'det : IsUnit ((C' i).toMatrix (d' i)).det :=
    (d' i).isUnit_det_of_isPerfPair (d' i) (C' i) hC'p
  obtain ⟨w'', hw''⟩ := hC''s.exists_isCharacteristic PadicInt.two_dvd_sq_sub_self
  obtain ⟨hsign_i, hodd_i⟩ := hmatch i
  rw [h''.constituentSign_eq hC'' d'', h'.constituentSign_eq (hC' i) (d' i)] at hsign_i
  rw [h''.constituentOddity_eq hB hC'' hw'',
    h'.constituentOddity_eq hB' (hC' i) (hw' i)] at hodd_i
  have hpar'' : (∀ v ∈ N'' i, 2 * 2 ^ i ∣ B v v) ↔ ∀ v ∈ N' i, 2 * 2 ^ i ∣ B' v v :=
    ⟨fun he ↦ (hpar i).mp (h''.forall_two_mul_pow_dvd_of_equivalent h (Equivalent.refl B)
        (mem_nonZeroDivisors_of_ne_zero two_ne_zero) dvd_rfl he),
      fun he ↦ h.forall_two_mul_pow_dvd_of_equivalent h'' (Equivalent.refl B)
        (mem_nonZeroDivisors_of_ne_zero two_ne_zero) dvd_rfl ((hpar i).mpr he)⟩
  have hC_equiv : C''.Equivalent (C' i) := by
    rw [hC''s.equivalent_iff_card_eq_and_two_dvd_iff_and_χ₈_det_eq_and_eight_dvd hC's d''
      (d' i) hC''det hC'det hw'' (hw' i)]
    refine ⟨?_, ?_, hsign_i, PadicInt.eight_dvd_sub_iff_toZModPow_three_eq.mpr hodd_i⟩
    · rw [Fintype.card_fin, h''.finrank_eq h two_ne_zero PadicInt.not_isUnit_two i, hrank i,
        finrank_eq_card_basis (d' i)]
    · exact (forall_two_dvd_iff_forall_two_mul_pow_dvd hC'').trans
        (hpar''.trans (forall_two_dvd_iff_forall_two_mul_pow_dvd (hC' i)).symm)
  rw [← hC'', ← hC' i]
  exact (equivalent_smul_iff h2i).mpr hC_equiv

/-- **Classification of symmetric bilinear forms over `ℤ_[2]` via Jordan splittings (`ZMod 8`
form).** Purely algebraic formulation of
`LinearMap.BilinForm.IsJordanSplitting.equivalent_iff_prod_χ₈_pow_mul_stdAddChar_sum_eq`
without complex exponentials: two symmetric forms `B` and `B'` over `ℤ_[2]` with Jordan splittings
`N` and `N'` are isometric if and only if their constituents have equal ranks and parity types at
every scale, and for every `j` such that `N (j + 1)` is of type II,
```text
∑_{i ≤ j} C i (w i) (w i) + (if ∏_{i ≤ j} χ₈(det C i)^{j + 1 - i} = -1 then 4 else 0)
```
agrees modulo `8` for `B` and `B'`. -/
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
    (C' : ∀ i, BilinForm ℤ_[2] (N' i)) (hC' : ∀ i, (2 : ℤ_[2]) ^ i • C' i = B'.restrict (N' i))
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
  rw [h.equivalent_iff_prod_χ₈_pow_mul_stdAddChar_sum_eq h' hB hB'
    C hC d w hw C' hC' d' w' hw']
  have h2i (i : ℕ) : (2 : ℤ_[2]) ^ i ∈ nonZeroDivisors ℤ_[2] :=
    mem_nonZeroDivisors_of_ne_zero (pow_ne_zero i two_ne_zero)
  have hpm : ∀ x : ZMod (2 ^ 3), x * x = 1 → χ₈ x = 1 ∨ χ₈ x = -1 := by decide
  have hsC (i : ℕ) :
      χ₈ (PadicInt.toZModPow 3 ((C i).toMatrix (d i)).det) = 1 ∨
        χ₈ (PadicInt.toZModPow 3 ((C i).toMatrix (d i)).det) = -1 :=
    hpm _ (PadicInt.isUnit_iff_toZModPow_three_mul_self.mp
      ((d i).isUnit_det_of_isPerfPair (d i) (C i)
        ((h.isModular i).isPerfPair_of_smul_eq (h2i i) (hC i))))
  have hsC' (i : ℕ) :
      χ₈ (PadicInt.toZModPow 3 ((C' i).toMatrix (d' i)).det) = 1 ∨
        χ₈ (PadicInt.toZModPow 3 ((C' i).toMatrix (d' i)).det) = -1 :=
    hpm _ (PadicInt.isUnit_iff_toZModPow_three_mul_self.mp
      ((d' i).isUnit_det_of_isPerfPair (d' i) (C' i)
        ((h'.isModular i).isPerfPair_of_smul_eq (h2i i) (hC' i))))
  refine and_congr_right fun _ ↦ and_congr_right fun _ ↦ forall₂_congr fun j _ ↦ ?_
  rw [map_sum (PadicInt.toZModPow 3), map_sum (PadicInt.toZModPow 3),
    prod_pow_mul_stdAddChar_eq_stdAddChar_add_ite (fun i _ ↦ hsC i),
    prod_pow_mul_stdAddChar_eq_stdAddChar_add_ite (fun i _ ↦ hsC' i),
    injective_stdAddChar.eq_iff]

end Classification

end LinearMap.BilinForm

namespace TauCeti

/-- The forms `⟨2, -2⟩` and `2 • U` are not isometric over `ℤ_[2]`: both have scale `2`, rank `2`,
determinant `-4`, and oddity `0`, but every value of `2 • U` is divisible by `4` while `⟨2, -2⟩`
represents `2`. -/
theorem not_equivalent_toBilin'_diagonal_two_neg_two_two_smul_hyperbolic :
    ¬(Matrix.toBilin' (Matrix.diagonal ![2, -2] : Matrix (Fin 2) (Fin 2) ℤ_[2])).Equivalent
      (Matrix.toBilin' ((2 : ℤ_[2]) • !![0, 1; 1, 0])) := by
  rintro ⟨e⟩
  have h4 : (4 : ℤ_[2]) ∣ Matrix.toBilin' ((2 : ℤ_[2]) • !![0, 1; 1, 0]) (e ![1, 0]) (e ![1, 0]) :=
    ⟨e ![1, 0] 0 * e ![1, 0] 1, by
      simp only [Matrix.toBilin'_apply', Matrix.mulVec, dotProduct, Fin.sum_univ_two,
        Matrix.smul_apply, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_fin_one, smul_eq_mul]
      ring⟩
  rw [e.map_app] at h4
  have hval : Matrix.toBilin' (Matrix.diagonal ![2, -2] : Matrix (Fin 2) (Fin 2) ℤ_[2])
      ![1, 0] ![1, 0] = 2 := by
    simp [Matrix.toBilin'_apply', Matrix.mulVec_diagonal, dotProduct, Fin.sum_univ_two]
  rw [hval] at h4
  obtain ⟨r, hr⟩ := h4
  have h1 : (2 : ℤ_[2]) * r = 1 :=
    mul_left_cancel₀ (two_ne_zero (α := ℤ_[2])) (by linear_combination -hr)
  exact PadicInt.not_isUnit_two (isUnit_iff_exists_inv.mpr ⟨r, h1⟩)

end TauCeti
