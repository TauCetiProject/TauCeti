/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.CyclicCohomology.Normalized.Chains
import TauCeti.Data.Fin.Basic
import Mathlib.Data.Nat.Factorial.Basic

/-!
# Odd periodic Chern chains

For a unit `u`, the degree `2k + 1` component of its periodic Chern chain is
`(-1)^k k! (u⁻¹ ⊗ bar u ⊗ bar u⁻¹ ⊗ ⋯ ⊗ bar u)`.
The components satisfy the mixed-boundary equation `b ch₍₂ₖ₊₃₎ + B ch₍₂ₖ₊₁₎ = 0`,
and the lowest component is a Hochschild cycle. Thus an infinite chain family can be
paired with finitely supported periodic cochains; no finite-support assertion about
this chain family, or descent to K-theory, is made here.

The construction works over any commutative base ring, including for matrix algebras.
We also give its evaluation against normalized cochains and its unit normalization.

## References

* J.-L. Loday, *Cyclic Homology*, §8.3.
* A. Connes, *Noncommutative Geometry*, Chapter III, §1.
-/

public section

noncomputable section

namespace TauCeti
namespace normalizedHochschildChains

variable (R : Type*) {A : Type*} [CommRing R] [Ring A] [Module R A]

private def word (u : Aˣ) (n : ℕ) : Fin (n + 1) → A :=
  fun i ↦ if Even (i : ℕ) then ↑u⁻¹ else ↑u

private theorem word_adjacent (u : Aˣ) {n : ℕ} (i : Fin (n + 1)) :
    word u (n + 1) i.castSucc * word u (n + 1) i.succ = 1 := by
  by_cases hi : Even (i : ℕ) <;> simp [word, hi, Nat.even_add_one]

section Boundary

variable [IsScalarTower R A A] [SMulCommClass R A A]

private theorem b_word (u : Aˣ) (k : ℕ) :
    b R A (2 * k + 2) (tensor R A (2 * k + 3) (word u (2 * k + 3))) =
      tensor R A (2 * k + 2) (Fin.cons 1 (word u (2 * k + 1))) -
        tensor R A (2 * k + 2) (Fin.cons 1 (word u⁻¹ (2 * k + 1))) := by
  have hfirst : hochschildFace (0 : Fin (2 * k + 4)) (word u (2 * k + 3)) =
      Fin.cons 1 (word u (2 * k + 1)) := by
    rw [← Fin.castSucc_zero, hochschildFace_castSucc]
    funext i
    cases i using Fin.cases with
    | zero => simp [Fin.contractNth, word]
    | succ i =>
      simp [Fin.contractNth, word, Nat.even_add_one]
  have hlast : hochschildFace (Fin.last (2 * k + 3)) (word u (2 * k + 3)) =
      Fin.cons 1 (word u⁻¹ (2 * k + 1)) := by
    rw [hochschildFace_last]
    funext i
    cases i using Fin.cases with
    | zero => simp [word, Nat.even_add_one]
    | succ i =>
      by_cases hi : Even (i : ℕ) <;> simp [word, hi, Nat.even_add_one]
  have hodd : Odd (2 * k + 3) := ⟨k + 1, by omega⟩
  have hsign : (-1 : ℤ) ^ (2 * k + 3) = -1 := hodd.neg_one_pow
  have hmiddle (i : Fin (2 * k + 3)) (hi : i ≠ 0) :
      tensor R A (2 * k + 2) (hochschildFace i.castSucc (word u (2 * k + 3))) = 0 := by
    apply tensor_eq_zero R A _ i hi
    rw [hochschildFace_castSucc, Fin.contractNth_apply_of_eq _ _ _ _ rfl]
    exact word_adjacent u i
  rw [b_tensor, Fin.sum_univ_castSucc, Finset.sum_eq_single 0]
  · simp only [Fin.val_zero, pow_zero, one_smul, Fin.castSucc_zero, hfirst,
      Fin.val_last, hlast, hsign, neg_one_zsmul, sub_eq_add_neg]
  · intro i _ hi
    rw [hmiddle i hi, zsmul_zero]
  · simp

end Boundary

private theorem rotate_word (u : Aˣ) (k j : ℕ) :
    word u (2 * k + 1) ∘ (finRotate (2 * k + 2) ^ j).symm =
      if Even j then word u (2 * k + 1) else word u⁻¹ (2 * k + 1) := by
  have heven : Even (2 * k + 2) := ⟨k + 1, by omega⟩
  have hrot (v : Aˣ) : word v (2 * k + 1) ∘ (finRotate (2 * k + 2)).symm =
      word v⁻¹ (2 * k + 1) := by
    funext i
    simpa [word, Function.comp_apply] using congrFun
      (Fin.ite_even_comp_finRotate_symm heven (↑v⁻¹ : A) ↑v) i
  induction j with
  | zero => simp [← Equiv.Perm.inv_def]
  | succ j ih =>
    rw [← Equiv.Perm.inv_def] at ih
    rw [pow_succ', ← Equiv.Perm.inv_def, mul_inv_rev, Equiv.Perm.coe_mul,
      ← Function.comp_assoc, ih]
    by_cases hj : Even j <;> simp [hj, Nat.even_add_one, Equiv.Perm.inv_def, hrot]

private theorem B_word (u : Aˣ) (k : ℕ) :
    B R A (2 * k + 1) (tensor R A (2 * k + 1) (word u (2 * k + 1))) =
      (k + 1) • (tensor R A (2 * k + 2) (Fin.cons 1 (word u (2 * k + 1))) -
        tensor R A (2 * k + 2) (Fin.cons 1 (word u⁻¹ (2 * k + 1)))) := by
  let X := tensor R A (2 * k + 2) (Fin.cons 1 (word u (2 * k + 1)))
  let Y := tensor R A (2 * k + 2) (Fin.cons 1 (word u⁻¹ (2 * k + 1)))
  have hterm (j : ℕ) : (-1 : ℤ) ^ ((2 * k + 1) * j) •
      tensor R A (2 * k + 2)
        (Fin.cons 1 (word u (2 * k + 1) ∘ (finRotate (2 * k + 2) ^ j).symm)) =
      if Even j then X else -Y := by
    rw [rotate_word, pow_mul, (odd_two_mul_add_one k).neg_one_pow]
    by_cases hj : Even j
    · simp [hj, hj.neg_one_pow, X]
    · simp [hj, (Nat.not_even_iff_odd.1 hj).neg_one_pow, Y]
  have hsum (m : ℕ) : (∑ j ∈ Finset.range (2 * m), if Even j then X else -Y) =
      m • (X - Y) := by
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Nat.mul_succ, Finset.sum_range_add, ih]
      simp [Finset.sum_range_succ, add_nsmul, sub_eq_add_neg]
  rw [B_tensor]
  simp_rw [hterm]
  exact hsum (k + 1)

/-- The degree `2k + 1` component of the odd periodic Chern chain of a unit. -/
def oddChernChain (u : Aˣ) (k : ℕ) : normalizedHochschildChains R A (2 * k + 1) :=
  ((-1 : ℤ) ^ k * k.factorial) •
    tensor R A (2 * k + 1) (word u (2 * k + 1))

/-- The tensor formula for the odd Chern component, including its integral coefficient. -/
theorem oddChernChain_def (u : Aˣ) (k : ℕ) :
    oddChernChain R u k = ((-1 : ℤ) ^ k * k.factorial) •
      tensor R A (2 * k + 1) (fun i ↦ if Even (i : ℕ) then ↑u⁻¹ else ↑u) := (rfl)

/-- The lowest odd Chern component is `u⁻¹ ⊗ bar u`. -/
theorem oddChernChain_zero (u : Aˣ) :
    oddChernChain R u 0 = tensor R A 1 ![↑u⁻¹, ↑u] := by
  have hword : word u 1 = ![↑u⁻¹, ↑u] := by
    ext i
    fin_cases i <;> simp [word]
  simp [oddChernChain, hword]

/-- The unit represents the zero odd Chern chain in every degree. -/
@[simp]
theorem oddChernChain_one (k : ℕ) : oddChernChain R (1 : Aˣ) k = 0 := by
  have hword : tensor R A (2 * k + 1) (word (1 : Aˣ) (2 * k + 1)) = 0 := by
    apply tensor_eq_zero R A _ (1 : Fin (2 * k + 2)) (by simp)
    simp [word]
  rw [oddChernChain, hword, zsmul_zero]

/-- Evaluating an odd Chern component on a normalized cochain gives the alternating
invertible/inverse formula with coefficient `(-1)^k k!`. -/
@[simp]
theorem lift_oddChernChain {M : Type*} [AddCommGroup M] [Module R M]
    (u : Aˣ) (k : ℕ) (φ : normalizedHochschildCochains R A M (2 * k + 1)) :
    lift φ (oddChernChain R u k) = ((-1 : ℤ) ^ k * k.factorial) •
      φ.val (fun i ↦ if Even (i : ℕ) then ↑u⁻¹ else ↑u) := by
  rw [oddChernChain_def, map_zsmul, lift_tensor]

section Boundary

variable [IsScalarTower R A A] [SMulCommClass R A A]

/-- The lowest odd Chern component is a Hochschild cycle. -/
@[simp]
theorem b_oddChernChain_zero (u : Aˣ) : b R A 0 (oddChernChain R u 0) = 0 := by
  rw [oddChernChain_zero, b_tensor, Fin.sum_univ_castSucc, Fin.sum_univ_one,
    hochschildFace_castSucc, hochschildFace_last]
  apply (zeroEquiv R A).injective
  simp [Fin.contractNth]

/-- Successive odd Chern components satisfy the periodic mixed-boundary equation.
Together with `b_oddChernChain_zero`, this is `(b + B) ch(u) = 0`. -/
theorem b_oddChernChain_succ_add_B_oddChernChain (u : Aˣ) (k : ℕ) :
    b R A (2 * k + 2) (oddChernChain R u (k + 1)) +
      B R A (2 * k + 1) (oddChernChain R u k) = 0 := by
  have hcoeff : (-1 : ℤ) ^ (k + 1) * (k + 1).factorial +
      ((-1 : ℤ) ^ k * k.factorial) * (↑(k + 1) : ℤ) = 0 := by
    simp only [pow_succ, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    ring
  -- Multiplication by two makes the successor component's degree definitionally
  -- equal to `2 * k + 3`; record the boundary formula in the successor indexing.
  have hb : b R A (2 * k + 2)
      (tensor R A (2 * (k + 1) + 1) (word u (2 * (k + 1) + 1))) =
      tensor R A (2 * k + 2) (Fin.cons 1 (word u (2 * k + 1))) -
        tensor R A (2 * k + 2) (Fin.cons 1 (word u⁻¹ (2 * k + 1))) := b_word R u k
  simp only [oddChernChain, map_zsmul]
  rw [hb, B_word, ← Nat.cast_smul_eq_nsmul ℤ, smul_smul, ← add_smul, hcoeff, zero_smul]

end Boundary

end normalizedHochschildChains
end TauCeti
