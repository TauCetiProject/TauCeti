/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
public import TauCeti.Data.List.OneDegenerateOrder
public import TauCeti.LinearAlgebra.Matrix.Cartan.Coxeter.Basic
import TauCeti.Data.Fin.Basic
import TauCeti.Data.Matrix.Mul
import TauCeti.GroupTheory.OrderOfElement.Basic
import TauCeti.GroupTheory.Perm.Coxeter
import TauCeti.LinearAlgebra.Charpoly.Permutation
import TauCeti.LinearAlgebra.Matrix.Adjugate.Basic
import TauCeti.LinearAlgebra.Matrix.Permutation
import TauCeti.LinearAlgebra.Matrix.Polynomial

/-!
# Coxeter elements of the classical Cartan matrices

This file computes the order and the characteristic polynomial of the Coxeter element
`c = s₁ s₂ ⋯ sₙ` (`Matrix.coxeterElement`) of each classical Cartan matrix `CartanMatrix.A n`,
`CartanMatrix.B n`, `CartanMatrix.C n`, and `CartanMatrix.D n`, together with the one-degenerate
order of the Bourbaki node numbering `List.finRange n`:

| type | rank condition | `orderOf` | `charpoly` |
|---|---|---|---|
| `Aₙ` | `0 < n` (`charpoly` for all `n`) | `n + 1` | `∑ k < n + 1, X ^ k` |
| `Bₙ` | `0 < n` | `2 * n` | `X ^ n + 1` |
| `Cₙ` | `0 < n` | `2 * n` | `X ^ n + 1` |
| `Dₙ` | `2 ≤ n` | `2 * (n - 1)` | `(X ^ (n - 1) + 1) * (X + 1)` |

Rather than expanding `c` entry by entry, each family is intertwined with its coordinate model:

* In **type `Aₙ`**, the unit lower-triangular basis `ε₀ - ε₁, …, εₙ₋₁ - εₙ, εₙ` of `ℤⁿ⁺¹` turns
  the adjacent transpositions into upper block-triangular matrices with `(1, 1)` block
  `reflMatrix (CartanMatrix.A n) i` and `(2, 2)` block `1`. Their product is `finRotate (n + 1)`
  (`TauCeti.permCoxeterSystem_wordProd_finRange`), whose characteristic polynomial `X ^ (n + 1) - 1`
  factors as `(∑ k < n + 1, X ^ k) * (X - 1)`.
* In **type `Bₙ`** (`n = m + 1`), the same unimodular matrix `ε₀ - ε₁, …, εₘ₋₁ - εₘ, εₘ` conjugates
  `coxB (m + 1)` over `ℤ` to the negacyclic shift `ε₀ ↦ ε₁ ↦ ⋯ ↦ εₘ ↦ -ε₀`, which satisfies
  `N ^ n = -1` and has cyclic vector `ε₀`, giving `charpoly = X ^ n + 1` and `orderOf = 2 * n`.
* **Type `Cₙ`** is intertwined with type `Bₙ` by `diagonal (1, …, 1, 2)`, so `coxC n` and `coxB n`
  have the same order and characteristic polynomial for every `n`.
* In **type `Dₙ`** (`n = m + 2`), the root columns `ε₀ - ε₁, …, εₘ - εₘ₊₁, εₘ + εₘ₊₁` have integer
  quasi-inverse of determinant factor `2` and intertwine `coxD (m + 2)` with the block-diagonal
  matrix `fromBlocks (negShift (m + 1)) 0 0 (-1)` for all `2 ≤ n` (including the reducible `D₂` and
  the `A₃` coincidence `D₃`).

## Main definitions

* `TauCeti.Coxeter.coxA`, `coxB`, `coxC`, `coxD`: the Coxeter elements of the classical Cartan
  matrices.

## Main results

* `TauCeti.Coxeter.isOneDegenerateOrder_A`, `_B`, `_C`, `_D`: `List.finRange n` is a one-degenerate
  order of each classical diagram.
* `TauCeti.Coxeter.orderOf_coxA`, `orderOf_coxB`, `orderOf_coxC`, `orderOf_coxD`: the orders of the
  classical Coxeter elements.
* `TauCeti.Coxeter.charpoly_coxA`, `charpoly_coxB`, `charpoly_coxC`, `charpoly_coxD`: their
  characteristic polynomials over `ℤ`.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Ch. V, §6, and Plates I--IV.
* J. E. Humphreys, *Reflection Groups and Coxeter Groups*, Cambridge University Press (1990),
  §§ 3.16–3.20.
-/

public section

open Matrix Polynomial

namespace TauCeti.Coxeter

/-! ### Coxeter elements of the classical Cartan matrices -/

/-- The Coxeter element of `CartanMatrix.A n`. -/
def coxA (n : ℕ) : Matrix (Fin n) (Fin n) ℤ := coxeterElement (CartanMatrix.A n)

/-- `coxA n` unfolds to `coxeterElement (CartanMatrix.A n)`. -/
theorem coxA_def (n : ℕ) : coxA n = coxeterElement (CartanMatrix.A n) := (rfl)

/-- The Coxeter element of `CartanMatrix.B n`. -/
def coxB (n : ℕ) : Matrix (Fin n) (Fin n) ℤ := coxeterElement (CartanMatrix.B n)

/-- `coxB n` unfolds to `coxeterElement (CartanMatrix.B n)`. -/
theorem coxB_def (n : ℕ) : coxB n = coxeterElement (CartanMatrix.B n) := (rfl)

/-- The Coxeter element of `CartanMatrix.C n`. -/
def coxC (n : ℕ) : Matrix (Fin n) (Fin n) ℤ := coxeterElement (CartanMatrix.C n)

/-- `coxC n` unfolds to `coxeterElement (CartanMatrix.C n)`. -/
theorem coxC_def (n : ℕ) : coxC n = coxeterElement (CartanMatrix.C n) := (rfl)

/-- The Coxeter element of `CartanMatrix.D n`. -/
def coxD (n : ℕ) : Matrix (Fin n) (Fin n) ℤ := coxeterElement (CartanMatrix.D n)

/-- `coxD n` unfolds to `coxeterElement (CartanMatrix.D n)`. -/
theorem coxD_def (n : ℕ) : coxD n = coxeterElement (CartanMatrix.D n) := (rfl)

/-! ### One-degenerate orders of the classical diagrams -/

private theorem isOneDegenerateOrder_finRange {n : ℕ} {adj : Fin n → Fin n → Prop}
    (h : ∀ z x y : Fin n, x < z → y < z → adj z x → adj z y → x = y) :
    List.IsOneDegenerateOrder adj (List.finRange n) := by
  rw [List.isOneDegenerateOrder_iff]
  intro S₁ z S₂ hS x hx y hy hzx hzy
  have hp := List.pairwise_lt_finRange n
  rw [hS, List.pairwise_append] at hp
  exact h z x y (hp.2.2 x hx z List.mem_cons_self) (hp.2.2 y hy z List.mem_cons_self) hzx hzy

/-- `List.finRange n` is a one-degenerate order of the Dynkin diagram of `CartanMatrix.A n`. -/
theorem isOneDegenerateOrder_A (n : ℕ) :
    List.IsOneDegenerateOrder (fun i j : Fin n => CartanMatrix.A n i j ≠ 0) (List.finRange n) := by
  refine isOneDegenerateOrder_finRange fun z x y hxz hyz h1 h2 => Fin.ext ?_
  rw [Fin.lt_def] at hxz hyz
  simp only [CartanMatrix.A, Matrix.of_apply, Fin.ext_iff] at h1 h2
  split_ifs at h1 h2 <;> omega

/-- `List.finRange n` is a one-degenerate order of the Dynkin diagram of `CartanMatrix.B n`. -/
theorem isOneDegenerateOrder_B (n : ℕ) :
    List.IsOneDegenerateOrder (fun i j : Fin n => CartanMatrix.B n i j ≠ 0) (List.finRange n) := by
  refine isOneDegenerateOrder_finRange fun z x y hxz hyz h1 h2 => Fin.ext ?_
  rw [Fin.lt_def] at hxz hyz
  simp only [CartanMatrix.B, Matrix.of_apply, Fin.ext_iff] at h1 h2
  split_ifs at h1 h2 <;> omega

/-- `List.finRange n` is a one-degenerate order of the Dynkin diagram of `CartanMatrix.C n`. -/
theorem isOneDegenerateOrder_C (n : ℕ) :
    List.IsOneDegenerateOrder (fun i j : Fin n => CartanMatrix.C n i j ≠ 0) (List.finRange n) := by
  refine isOneDegenerateOrder_finRange fun z x y hxz hyz h1 h2 => Fin.ext ?_
  rw [Fin.lt_def] at hxz hyz
  simp only [CartanMatrix.C, Matrix.of_apply, Fin.ext_iff] at h1 h2
  split_ifs at h1 h2 <;> omega

/-- `List.finRange n` is a one-degenerate order of the Dynkin diagram of `CartanMatrix.D n`. -/
theorem isOneDegenerateOrder_D (n : ℕ) :
    List.IsOneDegenerateOrder (fun i j : Fin n => CartanMatrix.D n i j ≠ 0) (List.finRange n) := by
  refine isOneDegenerateOrder_finRange fun z x y hxz hyz h1 h2 => Fin.ext ?_
  have _ := z.isLt; rw [Fin.lt_def] at hxz hyz
  simp only [CartanMatrix.D, Matrix.of_apply, Fin.ext_iff] at h1 h2
  split_ifs at h1 h2 <;> omega

/-! ### Shared matrix helpers: unimodular difference basis and shifts -/

/-- Unit lower-triangular basis `ε₀ - ε₁, …, ε_{m-2} - ε_{m-1}, ε_{m-1}` of `ℤᵐ`. -/
private def diffBasis (m : ℕ) : Matrix (Fin m) (Fin m) ℤ :=
  Matrix.of fun p q => if p = q then 1 else if p.val = q.val + 1 then -1 else 0

/-- Explicit inverse of `diffBasis m`: lower-triangular matrix of ones. -/
private def sumBasis (m : ℕ) : Matrix (Fin m) (Fin m) ℤ :=
  Matrix.of fun r p => if p.val ≤ r.val then 1 else 0

private theorem sumBasis_mul_diffBasis (m : ℕ) : sumBasis m * diffBasis m = 1 := by
  ext r q; rw [Matrix.mul_apply]
  rcases lt_or_ge (q.val + 1) m with hq | hq
  · let q' : Fin m := ⟨q.val + 1, hq⟩
    have hqq' : q ≠ q' := fun h => by have := congrArg Fin.val h; dsimp [q'] at this; omega
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ q),
      ← Finset.add_sum_erase _ _ (Finset.mem_erase.mpr ⟨hqq'.symm, Finset.mem_univ q'⟩),
      Finset.sum_eq_zero]
    · simp only [sumBasis, diffBasis, Matrix.of_apply, Matrix.one_apply, ↓reduceIte,
        Fin.ext_iff, q']
      split_ifs <;> omega
    · intro p hp
      have hpq : p ≠ q := (Finset.mem_erase.mp (Finset.mem_erase.mp hp).2).1
      have hpq' : p.val ≠ q.val + 1 := fun h => (Finset.mem_erase.mp hp).1 (Fin.ext h)
      simp [diffBasis, hpq, hpq']
  · rw [Finset.sum_eq_single q]
    · have _ := r.isLt
      simp only [sumBasis, diffBasis, Matrix.of_apply, Matrix.one_apply, ↓reduceIte, Fin.ext_iff]
      split_ifs <;> omega
    · intro p _ hp
      have hpq' : p.val ≠ q.val + 1 := by have := p.isLt; omega
      simp [diffBasis, hp, hpq']
    · exact fun h => absurd (Finset.mem_univ _) h

private theorem isLeftRegular_det_diffBasis (m : ℕ) : IsLeftRegular (diffBasis m).det :=
  isLeftRegular_det_right_of_mul_eq_smul_one isRegular_one.left (by
    rw [sumBasis_mul_diffBasis, one_smul])

/-! ### Cyclic and negacyclic shift matrices -/

private theorem permMatrixHom_finRotate_mul_eq {m k : ℕ}
    (U : Matrix (Fin (m + 1)) (Fin k) ℤ) (g : Fin m → Matrix (Fin k) (Fin k) ℤ)
    (h : ∀ i : Fin m, permMatrixHom (BraidGroup.transposition (n := m + 1) i) * U = U * g i) :
    permMatrixHom (finRotate (m + 1)) * U = U * ((List.finRange m).map g).prod := by
  have hprod := list_prod_map_mul_eq_mul_list_prod_map (List.finRange m) U
    (permMatrixHom (R := ℤ) ∘ BraidGroup.transposition (n := m + 1)) g (fun i _ => h i)
  have hrot : (permCoxeterSystem (m + 1)).wordProd (List.finRange m) = finRotate (m + 1) :=
    permCoxeterSystem_wordProd_finRange (n := m + 1)
  rwa [← List.map_map, ← map_list_prod, ← permCoxeterSystem_wordProd (n := m + 1), hrot] at hprod

/-- Negacyclic shift matrix on `Fin n`: `ε₀ ↦ ε₁ ↦ ⋯ ↦ ε_{n-1} ↦ -ε₀`. -/
private def negShift (n : ℕ) : Matrix (Fin n) (Fin n) ℤ :=
  Matrix.of fun p q =>
    if q.val + 1 < n then (if p.val = q.val + 1 then 1 else 0)
    else (if p.val = 0 then -1 else 0)

private theorem negShift_mulVec_single {n : ℕ} (hn : 0 < n) (q : Fin n) :
    negShift n *ᵥ Pi.single q 1 =
      (if q.val + 1 < n then (1 : ℤ) else -1) •
        Pi.single ⟨(q.val + 1) % n, Nat.mod_lt _ hn⟩ 1 := by
  rw [Matrix.mulVec_single_one]; ext p
  by_cases hlt : q.val + 1 < n
  · simp [Matrix.col_apply, negShift, hlt, Nat.mod_eq_of_lt hlt, Pi.single_apply, Fin.ext_iff]
  · have hqn : q.val + 1 = n := by have := q.isLt; omega
    simp [Matrix.col_apply, negShift, hqn, Pi.single_apply, Fin.ext_iff]

private theorem negShift_pow_mulVec_single {n : ℕ} (hn : 0 < n) {k : ℕ} (hk : k ≤ n) (q : Fin n) :
    (negShift n ^ k) *ᵥ Pi.single q 1 =
      (if q.val + k < n then (1 : ℤ) else -1) •
        Pi.single ⟨(q.val + k) % n, Nat.mod_lt _ hn⟩ 1 := by
  induction k with
  | zero => rw [pow_zero, Matrix.one_mulVec]; ext p; simp [q.isLt, Nat.mod_eq_of_lt q.isLt]
  | succ k ih =>
    rw [pow_succ', ← Matrix.mulVec_mulVec, ih (by omega), Matrix.mulVec_smul,
      negShift_mulVec_single hn]
    have hq := q.isLt
    have hmod : ((q.val + k) % n + 1) % n = (q.val + (k + 1)) % n := by
      rw [← Nat.add_assoc, ← Nat.mod_add_mod (q.val + k) n 1]
    ext p
    simp only [Pi.smul_apply, Pi.single_apply, Fin.ext_iff, smul_eq_mul, hmod]
    by_cases h1 : q.val + k < n
    · simp only [Nat.mod_eq_of_lt h1]; split_ifs <;> omega
    · have hrem : (q.val + k) % n = q.val + k - n :=
        (Nat.mod_eq_sub_mod (by omega)).trans (Nat.mod_eq_of_lt (by omega))
      simp only [hrem]; split_ifs <;> omega

private theorem negShift_pow_self {n : ℕ} (hn : 0 < n) : negShift n ^ n = -1 := by
  ext p q
  have hv := congrFun (negShift_pow_mulVec_single hn le_rfl q) p
  rw [Matrix.mulVec_single_one, Matrix.col_apply] at hv
  simp only [hv, ite_eq_right (by omega : ¬ q.val + n < n), Pi.smul_apply, Pi.single_apply,
    Fin.ext_iff, Nat.add_mod_right, Nat.mod_eq_of_lt q.isLt, smul_eq_mul, Matrix.neg_apply,
    Matrix.one_apply]
  split_ifs <;> omega

private theorem charpoly_negShift {n : ℕ} (hn : 0 < n) :
    (negShift n).charpoly = X ^ n + 1 := by
  have hmon : (X ^ n + 1 : ℤ[X]).IsMonicOfDegree n :=
    (isMonicOfDegree_iff _ _).mpr
      ⟨(natDegree_add_le _ _).trans (max_le (natDegree_X_pow_le n) (by simp)),
        by simp [coeff_one, hn.ne']⟩
  have hdeg := IsMonicOfDegree.natDegree_sub_lt hn.ne'
    ⟨by rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin], Matrix.charpoly_monic (negShift n)⟩
    hmon
  have h0 : aeval (negShift n) ((negShift n).charpoly - (X ^ n + 1)) = 0 := by
    simp [Matrix.aeval_self_charpoly, negShift_pow_self hn]
  rw [← sub_eq_zero]; ext j; rw [coeff_zero]
  rcases lt_or_ge j n with hj | hj
  · have hv := congrFun (congrArg (· *ᵥ Pi.single ⟨0, hn⟩ 1) h0) ⟨j, hj⟩
    rw [aeval_eq_sum_range' hdeg, Matrix.sum_mulVec] at hv
    simp only [Matrix.zero_mulVec, Pi.zero_apply, Finset.sum_apply, Matrix.smul_mulVec,
      Pi.smul_apply, smul_eq_mul] at hv
    rw [Finset.sum_eq_single_of_mem j (Finset.mem_range.mpr hj)] at hv
    · rw [negShift_pow_mulVec_single hn hj.le] at hv
      simpa [hj, Nat.mod_eq_of_lt hj] using hv
    · intro i hi hij
      have hi' := Finset.mem_range.mp hi
      rw [negShift_pow_mulVec_single hn hi'.le]
      simp [hi', Nat.mod_eq_of_lt hi', Fin.ext_iff, hij]
  · exact coeff_eq_zero_of_natDegree_lt (hdeg.trans_le hj)

private theorem orderOf_negShift {n : ℕ} (hn : 0 < n) : orderOf (negShift n) = 2 * n := by
  have h0 {k : ℕ} (hk0 : 0 < k) (hk : k < n) :
      (negShift n ^ k *ᵥ Pi.single ⟨0, hn⟩ 1) ⟨0, hn⟩ = 0 := by
    have h := congrFun (negShift_pow_mulVec_single hn hk.le ⟨0, hn⟩) ⟨0, hn⟩
    simp only [zero_add, ite_eq_left hk, one_smul, Pi.single_apply, Fin.ext_iff,
      Nat.mod_eq_of_lt hk] at h
    omega
  refine (orderOf_eq_iff (by omega)).mpr ⟨?_, fun m hm hpos hm1 => ?_⟩
  · rw [mul_comm, pow_mul, negShift_pow_self hn, neg_one_sq]
  · have hv := congrFun (congrArg (· *ᵥ Pi.single ⟨0, hn⟩ 1) hm1) ⟨0, hn⟩
    simp only [Matrix.one_mulVec, Pi.single_eq_same] at hv
    rcases lt_trichotomy m n with hlt | rfl | hgt
    · linarith [h0 hpos hlt]
    · rw [negShift_pow_self hn] at hv; simp at hv
    · obtain ⟨k, rfl⟩ : ∃ k, m = n + k := ⟨m - n, by omega⟩
      rw [pow_add, negShift_pow_self hn, neg_one_mul, Matrix.neg_mulVec, Pi.neg_apply,
        h0 (by omega) (by omega)] at hv
      omega

/-! ### Type `A` -/

/-- Upper block-triangular matrix on `Fin (n + 1)` extending `reflMatrix (CartanMatrix.A n) i`. -/
private def extReflA {n : ℕ} (i : Fin n) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ :=
  reindex (finSumFinEquiv (m := n) (n := 1)) (finSumFinEquiv (m := n) (n := 1))
    (fromBlocks (reflMatrix (CartanMatrix.A n) i)
      (Matrix.of fun k _ => if k = i ∧ i.val + 1 = n then 1 else 0) 0 1)

private theorem permMatrixHom_transposition_mul_diffBasis {n : ℕ} (i : Fin n) :
    permMatrixHom (BraidGroup.transposition (n := n + 1) i) * diffBasis (n + 1) =
      diffBasis (n + 1) * extReflA i := by
  ext p q
  rw [permMatrixHom_mul_apply, BraidGroup.symm_transposition]
  have hp := p.isLt; have hq := q.isLt; have hi := i.isLt
  rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hq) with hqlt | hqlast
  · let jq : Fin n := ⟨q.val, hqlt⟩
    have hqe : q = finSumFinEquiv (m := n) (n := 1) (Sum.inl jq) := Fin.ext rfl
    have hsum : (diffBasis (n + 1) * extReflA i) p q =
        diffBasis (n + 1) p (finSumFinEquiv (Sum.inl jq)) -
          diffBasis (n + 1) p (finSumFinEquiv (Sum.inl i)) * CartanMatrix.A n jq i := by
      rw [Matrix.mul_apply, ← (finSumFinEquiv (m := n) (n := 1)).sum_comp]
      simp only [Fintype.sum_sum_type, Fintype.sum_unique, hqe, extReflA, reindex_apply,
        submatrix_apply, Equiv.symm_apply_apply, fromBlocks_apply₁₁, fromBlocks_apply₂₁,
        Matrix.zero_apply, mul_zero, add_zero, reflMatrix_apply, mul_sub, mul_ite, mul_one,
        Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
    rw [hsum]
    simp only [diffBasis, CartanMatrix.A, Matrix.of_apply, Fin.ext_iff, finSumFinEquiv_apply_left,
      Fin.val_castAdd, BraidGroup.val_transposition_apply, jq]
    split_ifs <;> omega
  · have hqe : q = finSumFinEquiv (m := n) (n := 1) (Sum.inr 0) := Fin.ext (by simpa using hqlast)
    rw [Matrix.mul_apply, ← (finSumFinEquiv (m := n) (n := 1)).sum_comp]
    simp only [Fintype.sum_sum_type, Fintype.sum_unique, Fin.default_eq_zero, hqe, extReflA,
      reindex_apply, submatrix_apply, Equiv.symm_apply_apply, fromBlocks_apply₁₂,
      fromBlocks_apply₂₂, Matrix.of_apply, Matrix.one_apply, ↓reduceIte, mul_one, mul_ite,
      mul_zero]
    rw [Finset.sum_eq_single i (fun k _ hki => by simp [hki])
      (fun h => absurd (Finset.mem_univ _) h), ← hqe]
    simp only [true_and, diffBasis, Matrix.of_apply, Fin.ext_iff,
      finSumFinEquiv_apply_left, Fin.val_castAdd, BraidGroup.val_transposition_apply, hqlast]
    split_ifs <;> omega

private theorem list_prod_extReflA {n : ℕ} (L : List (Fin n)) :
    ∃ B : Matrix (Fin n) (Fin 1) ℤ,
      ((L.map extReflA).prod).submatrix (finSumFinEquiv (m := n) (n := 1))
          (finSumFinEquiv (m := n) (n := 1)) =
        fromBlocks ((L.map (reflMatrix (CartanMatrix.A n))).prod) B 0 1 := by
  induction L with
  | nil => exact ⟨0, by simp [fromBlocks_one, Matrix.submatrix_one_equiv]⟩
  | cons a t ih =>
    obtain ⟨B, hB⟩ := ih
    refine ⟨reflMatrix (CartanMatrix.A n) a * B +
        Matrix.of (fun k _ => if k = a ∧ a.val + 1 = n then 1 else 0), ?_⟩
    rw [List.map_cons, List.prod_cons,
      ← Matrix.submatrix_mul_equiv _ _ _ (finSumFinEquiv (m := n) (n := 1)), hB]
    simp [extReflA, fromBlocks_multiply, List.map_cons, List.prod_cons]

private theorem permMatrixHom_finRotate_mul_diffBasis (n : ℕ) :
    permMatrixHom (finRotate (n + 1)) * diffBasis (n + 1) =
      diffBasis (n + 1) * ((List.finRange n).map extReflA).prod :=
  permMatrixHom_finRotate_mul_eq (diffBasis (n + 1)) extReflA
    permMatrixHom_transposition_mul_diffBasis

/-- **Characteristic polynomial of the type `A` Coxeter element**: `1 + X + ⋯ + X ^ n` for every
rank `n` (including `n = 0`). -/
theorem charpoly_coxA (n : ℕ) :
    (coxA n).charpoly = ∑ k ∈ Finset.range (n + 1), X ^ k := by
  obtain ⟨B, hB⟩ := list_prod_extReflA (List.finRange n)
  have hc := (Matrix.charpoly_eq_of_mul_eq_mul (isLeftRegular_det_diffBasis (n + 1)).ne_zero
    (permMatrixHom_finRotate_mul_diffBasis n)).symm.trans
    (Matrix.charpoly_permMatrixHom_finRotate (Nat.succ_ne_zero n))
  rw [← charpoly_reindex (finSumFinEquiv (m := n) (n := 1)).symm, reindex_apply,
    Equiv.symm_symm, hB, charpoly_fromBlocks_zero₂₁] at hc
  have h1 : (1 : Matrix (Fin 1) (Fin 1) ℤ).charpoly = X - 1 := by
    rw [Matrix.charpoly, Matrix.det_fin_one]; simp
  rw [h1, ← geom_sum_mul X (n + 1)] at hc
  exact mul_right_cancel₀ (by simpa using X_sub_C_ne_zero (1 : ℤ)) hc

/-- The empty type `A₀` Coxeter element has order `1`. -/
@[simp]
theorem orderOf_coxA_zero : orderOf (coxA 0) = 1 := by
  rw [Subsingleton.elim (coxA 0) 1, orderOf_one]

/-- **The Coxeter number of `Aₙ` (`0 < n`) is `n + 1`**: the Coxeter element of `CartanMatrix.A n`
has order `n + 1`. -/
theorem orderOf_coxA {n : ℕ} (hn : 0 < n) : orderOf (coxA n) = n + 1 := by
  have hint := permMatrixHom_finRotate_mul_diffBasis n
  obtain ⟨B, hB⟩ := list_prod_extReflA (List.finRange n)
  let U : Matrix (Fin (n + 1)) (Fin n) ℤ :=
    (diffBasis (n + 1)).submatrix id (finSumFinEquiv (m := n) (n := 1) ∘ Sum.inl)
  have hSU : permMatrixHom (finRotate (n + 1)) * U = U * coxA n := by
    ext p j
    have hj := congrFun₂ hint p (finSumFinEquiv (Sum.inl j))
    have hentry (r : Fin n ⊕ Fin 1) :
        ((List.finRange n).map extReflA).prod (finSumFinEquiv r) (finSumFinEquiv (Sum.inl j)) =
          fromBlocks (coxA n) B 0 1 r (Sum.inl j) := by
      simpa [coxA, coxeterElement] using congrFun₂ hB r (Sum.inl j)
    simp only [U, Matrix.mul_apply, submatrix_apply, id_eq, Function.comp_apply] at hj ⊢
    rw [hj, ← (finSumFinEquiv (m := n) (n := 1)).sum_comp]
    simp_rw [hentry]; simp [Fintype.sum_sum_type]
  refine (orderOf_eq_iff (by omega)).mpr ⟨?_, fun m hm hpos hm1 => ?_⟩
  · have hch : aeval (coxA n) (X ^ (n + 1) - 1 : ℤ[X]) = 0 := by
      rw [← geom_sum_mul, map_mul, ← charpoly_coxA, Matrix.aeval_self_charpoly, zero_mul]
    simpa [sub_eq_zero] using hch
  · have hpow : permMatrixHom (finRotate (n + 1)) ^ m * U = U * coxA n ^ m := by
      simpa using Matrix.aeval_mul_eq_mul_aeval hSU (Polynomial.X ^ m : ℤ[X])
    rw [hm1, Matrix.mul_one, ← map_pow] at hpow
    have h0 := congrFun₂ hpow ((finRotate (n + 1) ^ m) 0) ⟨0, hn⟩
    rw [permMatrixHom_mul_apply, Equiv.symm_apply_apply] at h0
    have hval : ((finRotate (n + 1) ^ m) 0 : ℕ) = m := by
      rw [Fin.coe_finRotate_pow, Fin.val_zero, zero_add, Nat.mod_eq_of_lt hm]
    simp only [U, submatrix_apply, id_eq, Function.comp_apply, finSumFinEquiv_apply_left,
      diffBasis, Matrix.of_apply, Fin.ext_iff, Fin.val_castAdd, Fin.val_zero, hval] at h0
    split_ifs at h0 <;> omega

/-! ### Type `B` -/

/-- Sign-flip matrix negating the last coordinate `Fin.last m` of `ℤ^{m+1}`. -/
private def lastFlip (m : ℕ) : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ :=
  diagonal fun p => if p = Fin.last m then -1 else 1

private theorem permMatrixHom_transposition_mul_diffBasis_B {m : ℕ} (i : Fin m) :
    permMatrixHom (BraidGroup.transposition (n := m + 1) i) * diffBasis (m + 1) =
      diffBasis (m + 1) * reflMatrix (CartanMatrix.B (m + 1)) i.castSucc := by
  ext p q
  rw [permMatrixHom_mul_apply, BraidGroup.symm_transposition, mul_reflMatrix_apply]
  have _ := i.isLt
  simp only [diffBasis, CartanMatrix.B, Matrix.of_apply, Fin.ext_iff, Fin.val_castSucc,
    BraidGroup.val_transposition_apply, Nat.add_sub_cancel]
  split_ifs <;> omega

private theorem lastFlip_mul_diffBasis (m : ℕ) :
    lastFlip m * diffBasis (m + 1) =
      diffBasis (m + 1) * reflMatrix (CartanMatrix.B (m + 1)) (Fin.last m) := by
  ext p q
  rw [lastFlip, diagonal_mul, mul_reflMatrix_apply]
  have _ := p.isLt; have _ := q.isLt
  simp only [diffBasis, CartanMatrix.B, Matrix.of_apply, Fin.ext_iff, Fin.val_last,
    Nat.add_sub_cancel]
  split_ifs <;> omega

private theorem permMatrixHom_finRotate_mul_lastFlip (m : ℕ) :
    permMatrixHom (finRotate (m + 1)) * lastFlip m = negShift (m + 1) := by
  ext p q
  rw [permMatrixHom_mul_apply, lastFlip, diagonal_apply, negShift, Matrix.of_apply]
  set s := (finRotate (m + 1)).symm p
  have _ := s.isLt; have _ := q.isLt
  have hrot : p.val = if s.val = m then 0 else s.val + 1 := by
    have h := coe_finRotate s; rw [Equiv.apply_symm_apply] at h
    simpa [Fin.ext_iff, Fin.val_last] using h
  simp only [Fin.ext_iff, Fin.val_last] at hrot ⊢
  split_ifs at hrot ⊢ <;> omega

private theorem negShift_mul_diffBasis_eq_diffBasis_mul_coxB (m : ℕ) :
    negShift (m + 1) * diffBasis (m + 1) = diffBasis (m + 1) * coxB (m + 1) := by
  have h1 := permMatrixHom_finRotate_mul_eq (diffBasis (m + 1))
    (fun i => reflMatrix (CartanMatrix.B (m + 1)) i.castSucc)
    permMatrixHom_transposition_mul_diffBasis_B
  rw [← permMatrixHom_finRotate_mul_lastFlip, mul_assoc, lastFlip_mul_diffBasis, ← mul_assoc, h1,
    mul_assoc, coxB, coxeterElement, List.finRange_succ_last, List.map_append, List.prod_append,
    List.map_singleton, List.prod_singleton, List.map_map]
  rfl

/-- The empty type `B₀` Coxeter element has characteristic polynomial `1`. -/
theorem charpoly_coxB_zero : (coxB 0).charpoly = 1 := by simp

/-- **Characteristic polynomial of the type `B` Coxeter element** (`0 < n`): `X ^ n + 1`. -/
theorem charpoly_coxB {n : ℕ} (hn : 0 < n) : (coxB n).charpoly = X ^ n + 1 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  exact (Matrix.charpoly_eq_of_mul_eq_mul (isLeftRegular_det_diffBasis (m + 1)).ne_zero
    (negShift_mul_diffBasis_eq_diffBasis_mul_coxB m)).symm.trans
    (charpoly_negShift (Nat.succ_pos m))

/-- The empty type `B₀` Coxeter element has order `1`. -/
@[simp]
theorem orderOf_coxB_zero : orderOf (coxB 0) = 1 := by
  rw [Subsingleton.elim (coxB 0) 1, orderOf_one]

/-- **The Coxeter number of `Bₙ` (`0 < n`) is `2 * n`**: the Coxeter element of `CartanMatrix.B n`
has order `2 * n`. -/
theorem orderOf_coxB {n : ℕ} (hn : 0 < n) : orderOf (coxB n) = 2 * n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  exact (SemiconjBy.orderOf_eq_of_isRegular
    (isRegular_of_isLeftRegular_det (isLeftRegular_det_diffBasis (m + 1)))
    (negShift_mul_diffBasis_eq_diffBasis_mul_coxB m).symm).trans
    (orderOf_negShift (Nat.succ_pos m))

/-! ### Type `C` -/

/-- Diagonal matrix `diag(1, …, 1, 2)` intertwining `CartanMatrix.C n` and `CartanMatrix.B n`. -/
private def diagBC (n : ℕ) : Matrix (Fin n) (Fin n) ℤ :=
  diagonal fun i => if i.val + 1 = n then 2 else 1

private theorem diagBC_mul_coxC (n : ℕ) : diagBC n * coxC n = coxB n * diagBC n := by
  have hrefl (i : Fin n) :
      reflMatrix (CartanMatrix.B n) i * diagBC n = diagBC n * reflMatrix (CartanMatrix.C n) i := by
    ext k j; rw [diagBC, diagonal_mul, mul_diagonal]
    have _ := k.isLt; have _ := j.isLt; have _ := i.isLt
    simp only [reflMatrix_apply, CartanMatrix.B, CartanMatrix.C, Matrix.of_apply, Fin.ext_iff]
    split_ifs <;> omega
  simpa [coxC, coxB, coxeterElement] using
    (list_prod_map_mul_eq_mul_list_prod_map (List.finRange n) (diagBC n)
      (reflMatrix (CartanMatrix.B n)) (reflMatrix (CartanMatrix.C n)) fun i _ => hrefl i).symm

private theorem det_diagBC_ne_zero (n : ℕ) : (diagBC n).det ≠ 0 := by
  rw [diagBC, det_diagonal, Finset.prod_ne_zero_iff]
  intro i _
  split_ifs <;> norm_num

/-- The Coxeter elements of `CartanMatrix.C n` and `CartanMatrix.B n` have the same order for every
`n`. -/
theorem orderOf_coxC_eq_orderOf_coxB (n : ℕ) : orderOf (coxC n) = orderOf (coxB n) :=
  SemiconjBy.orderOf_eq_of_isRegular
    (isRegular_of_isLeftRegular_det (IsRegular.of_ne_zero' (det_diagBC_ne_zero n)).left)
    (diagBC_mul_coxC n)

/-- The Coxeter elements of `CartanMatrix.C n` and `CartanMatrix.B n` have the same characteristic
polynomial for every `n`. -/
theorem charpoly_coxC_eq_charpoly_coxB (n : ℕ) : (coxC n).charpoly = (coxB n).charpoly :=
  (Matrix.charpoly_eq_of_mul_eq_mul (det_diagBC_ne_zero n) (diagBC_mul_coxC n).symm).symm

/-- The empty type `C₀` Coxeter element has order `1`. -/
@[simp]
theorem orderOf_coxC_zero : orderOf (coxC 0) = 1 := by
  rw [orderOf_coxC_eq_orderOf_coxB, orderOf_coxB_zero]

/-- **The Coxeter number of `Cₙ` (`0 < n`) is `2 * n`**: the Coxeter element of `CartanMatrix.C n`
has order `2 * n`. -/
theorem orderOf_coxC {n : ℕ} (hn : 0 < n) : orderOf (coxC n) = 2 * n :=
  (orderOf_coxC_eq_orderOf_coxB n).trans (orderOf_coxB hn)

/-- The empty type `C₀` Coxeter element has characteristic polynomial `1`. -/
theorem charpoly_coxC_zero : (coxC 0).charpoly = 1 := by simp

/-- **Characteristic polynomial of the type `C` Coxeter element** (`0 < n`): `X ^ n + 1`. -/
theorem charpoly_coxC {n : ℕ} (hn : 0 < n) : (coxC n).charpoly = X ^ n + 1 :=
  (charpoly_coxC_eq_charpoly_coxB n).trans (charpoly_coxB hn)

/-! ### Type `D` -/

/-- Simple-root columns `ε₀ - ε₁, …, εₘ - ε_{m+1}, εₘ + ε_{m+1}` of `D_{m+2}` in `ℤ^{m+2}`. -/
private def basisD (m : ℕ) : Matrix (Fin (m + 2)) (Fin (m + 2)) ℤ :=
  diffBasis (m + 2) *
    Matrix.of fun p q =>
      if p = q then (if q.val = m + 1 then 2 else 1)
      else if p.val = m ∧ q.val = m + 1 then 1 else 0

/-- Integer quasi-inverse of `basisD m`, satisfying `adjBasisD m * basisD m = 2 • 1`. -/
private def adjBasisD (m : ℕ) : Matrix (Fin (m + 2)) (Fin (m + 2)) ℤ :=
  (Matrix.of fun p q =>
    if p = q then (if q.val = m + 1 then 1 else 2)
    else if p.val = m ∧ q.val = m + 1 then -1 else 0) * sumBasis (m + 2)

private theorem basisD_apply (m : ℕ) (p q : Fin (m + 2)) :
    basisD m p q =
      if q.val < m + 1 then (if p = q then 1 else if p.val = q.val + 1 then -1 else 0)
      else (if p.val = m ∨ p.val = m + 1 then 1 else 0) := by
  rw [basisD, Matrix.mul_apply]
  have _ := p.isLt; have hq := q.isLt
  rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hq) with hqlt | hqlast
  · rw [Finset.sum_eq_single q]
    · simp only [diffBasis, Matrix.of_apply, ↓reduceIte, hqlt]; split_ifs <;> omega
    · intro r _ hr
      have hrm : ¬ (r.val = m ∧ q.val = m + 1) := by omega
      simp [hr, hrm]
    · exact fun h => absurd (Finset.mem_univ _) h
  · let r0 : Fin (m + 2) := ⟨m, by omega⟩
    let r1 : Fin (m + 2) := ⟨m + 1, by omega⟩
    have hr01 : r0 ≠ r1 := fun h => by have := congrArg Fin.val h; dsimp [r0, r1] at this; omega
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ r0),
      ← Finset.add_sum_erase _ _ (Finset.mem_erase.mpr ⟨hr01.symm, Finset.mem_univ r1⟩),
      Finset.sum_eq_zero]
    · clear hr01; simp [diffBasis, Fin.ext_iff, hqlast, r0, r1]; split_ifs <;> omega
    · intro r hr
      have hr0 : r ≠ r0 := (Finset.mem_erase.mp (Finset.mem_erase.mp hr).2).1
      have hr1 : r ≠ r1 := (Finset.mem_erase.mp hr).1
      have hrq : r ≠ q := fun h => hr1 (Fin.ext (h ▸ hqlast))
      have hrm : ¬ (r.val = m ∧ q.val = m + 1) := fun h => hr0 (Fin.ext h.1)
      simp [hrq, hrm]

private theorem adjBasisD_mul_basisD (m : ℕ) : adjBasisD m * basisD m = (2 : ℤ) • 1 := by
  rw [adjBasisD, basisD, mul_assoc, ← mul_assoc (sumBasis (m + 2)), sumBasis_mul_diffBasis, one_mul]
  let r0 : Fin (m + 2) := ⟨m, Nat.lt_succ_of_lt (Nat.lt_succ_self m)⟩
  let r1 : Fin (m + 2) := ⟨m + 1, Nat.lt_succ_self (m + 1)⟩
  have hr01 : r0 ≠ r1 := fun h => by have := congrArg Fin.val h; simp [r0, r1] at this
  ext p q; rw [Matrix.mul_apply]; have hp := p.isLt
  by_cases hp0 : p = r0
  · rw [hp0, ← Finset.add_sum_erase _ _ (Finset.mem_univ r0),
      ← Finset.add_sum_erase _ _ (Finset.mem_erase.mpr ⟨hr01.symm, Finset.mem_univ r1⟩),
      Finset.sum_eq_zero]
    · clear hr01 hp0 hp; simp [Fin.ext_iff, Matrix.one_apply, r0, r1]; split_ifs <;> omega
    · intro r hr
      have hr0 : r0 ≠ r := fun h => (Finset.mem_erase.mp (Finset.mem_erase.mp hr).2).1 h.symm
      have hr1 : r.val ≠ m + 1 := fun h => (Finset.mem_erase.mp hr).1 (Fin.ext h)
      simp [hr0, hr1]
  · have hpm : p.val ≠ m := fun h => hp0 (Fin.ext h)
    clear hp0 hr01
    rw [Finset.sum_eq_single p]
    · simp only [Matrix.of_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, ↓reduceIte,
        Fin.ext_iff]
      split_ifs <;> omega
    · intro r _ hr; simp [hr.symm, hpm]
    · exact fun h => absurd (Finset.mem_univ _) h

private theorem isLeftRegular_det_basisD (m : ℕ) : IsLeftRegular (basisD m).det :=
  isLeftRegular_det_right_of_mul_eq_smul_one (IsRegular.of_ne_zero' two_ne_zero).left
    (adjBasisD_mul_basisD m)

private theorem cartanMatrix_D_apply_succ_succ (m : ℕ) (i j : Fin (m + 2)) :
    CartanMatrix.D (m + 2) i j =
      if i = j then 2
      else if m = 0 then 0
      else if (i.val + 1 = j.val ∧ j.val < m) ∨ (j.val + 1 = i.val ∧ i.val < m) ∨
        (i.val + 1 = m ∧ (j.val = m ∨ j.val = m + 1)) ∨
        (j.val + 1 = m ∧ (i.val = m ∨ i.val = m + 1))
      then -1 else 0 := by
  have _ := i.isLt; have _ := j.isLt
  simp only [CartanMatrix.D, Matrix.of_apply]; split_ifs <;> omega

/-- Reflection across `(εₘ + ε_{m+1})⊥` in `ℤ^{m+2}`: fixes `εₖ` (`k < m`) and sends
`εₘ ↦ -ε_{m+1}`, `ε_{m+1} ↦ -εₘ`. -/
private def forkFlip (m : ℕ) : Matrix (Fin (m + 2)) (Fin (m + 2)) ℤ :=
  Matrix.of fun p q =>
    if p.val < m then (if p = q then 1 else 0)
    else if p.val = m then (if q.val = m + 1 then -1 else 0)
    else (if q.val = m then -1 else 0)

private theorem permMatrixHom_transposition_mul_basisD {m : ℕ} (i : Fin (m + 1)) :
    permMatrixHom (BraidGroup.transposition (n := m + 2) i) * basisD m =
      basisD m * reflMatrix (CartanMatrix.D (m + 2)) i.castSucc := by
  ext p q
  rw [permMatrixHom_mul_apply, BraidGroup.symm_transposition, mul_reflMatrix_apply]
  have _ := p.isLt; have _ := q.isLt; have hi := i.isLt
  have hicv : (i.castSucc : Fin (m + 2)).val = i.val := rfl
  have hD : CartanMatrix.D (m + 2) q i.castSucc =
      if q.val = i.val then 2
      else if (q.val < m + 1 ∧ (q.val + 1 = i.val ∨ i.val + 1 = q.val)) ∨
        (q.val = m + 1 ∧ i.val + 1 = m) then -1 else 0 := by
    rw [cartanMatrix_D_apply_succ_succ]; simp only [Fin.ext_iff, hicv]; split_ifs <;> omega
  set sp := BraidGroup.transposition (n := m + 2) i p
  have hsp := BraidGroup.val_transposition_apply (n := m + 2) i p
  rw [hD]; simp only [basisD_apply, Fin.ext_iff, hicv, hi]
  split_ifs at hsp ⊢ <;> omega

private theorem forkFlip_mul_apply {m k : ℕ} (M : Matrix (Fin (m + 2)) (Fin k) ℤ)
    (p : Fin (m + 2)) (q : Fin k) :
    (forkFlip m * M) p q =
      if p.val < m then M p q
      else if p.val = m then -M (Fin.last (m + 1)) q
      else -M (Fin.last m).castSucc q := by
  rw [Matrix.mul_apply]; split_ifs with hp1 hp2
  · rw [Finset.sum_eq_single p (fun r _ hr => by simp [forkFlip, hp1, hr.symm]) (by simp)]
    simp [forkFlip, hp1]
  · rw [Finset.sum_eq_single (Fin.last (m + 1))
      (fun r _ hr => by simp [forkFlip, hp2, show r.val ≠ m + 1 from fun h => hr (Fin.ext h)])
      (by simp)]; simp [forkFlip, hp2]
  · rw [Finset.sum_eq_single (Fin.last m).castSucc
      (fun r _ hr => by simp [forkFlip, hp1, hp2, show r.val ≠ m from fun h => hr (Fin.ext h)])
      (by simp)]; simp [forkFlip, hp1, hp2]

private theorem forkFlip_mul_basisD (m : ℕ) :
    forkFlip m * basisD m =
      basisD m * reflMatrix (CartanMatrix.D (m + 2)) (Fin.last (m + 1)) := by
  ext p q; rw [forkFlip_mul_apply, mul_reflMatrix_apply]
  have _ := p.isLt; have hq := q.isLt
  have hD : CartanMatrix.D (m + 2) q (Fin.last (m + 1)) =
      if q.val = m + 1 then 2 else if q.val + 1 = m then -1 else 0 := by
    rw [cartanMatrix_D_apply_succ_succ]; simp [Fin.ext_iff]; split_ifs <;> omega
  rw [hD]; rcases eq_or_ne q.val (m + 1) with hq1 | hq1
  · simp [hq1, basisD_apply]; split_ifs <;> omega
  · simp [hq1, show q.val < m + 1 by omega, basisD_apply, Fin.ext_iff]; split_ifs <;> omega

/-- Block-diagonal model `fromBlocks (negShift (m + 1)) 0 0 (-1)` of `coxD (m + 2)`. -/
private def modelD (m : ℕ) : Matrix (Fin (m + 2)) (Fin (m + 2)) ℤ :=
  reindex (finSumFinEquiv (m := m + 1) (n := 1)) (finSumFinEquiv (m := m + 1) (n := 1))
    (fromBlocks (negShift (m + 1)) 0 0 (-1 : Matrix (Fin 1) (Fin 1) ℤ))

private theorem permMatrixHom_finRotate_mul_forkFlip (m : ℕ) :
    permMatrixHom (finRotate (m + 2)) * forkFlip m = modelD m := by
  ext p q; rw [permMatrixHom_mul_apply]
  set s := (finRotate (m + 2)).symm p; have _ := s.isLt
  have hrot : p.val = if s.val = m + 1 then 0 else s.val + 1 := by
    have h := coe_finRotate s; rw [Equiv.apply_symm_apply] at h
    simpa [Fin.ext_iff, Fin.val_last] using h
  obtain ⟨ip | ip, rfl⟩ := (finSumFinEquiv (m := m + 1) (n := 1)).surjective p <;>
    obtain ⟨iq | iq, rfl⟩ := (finSumFinEquiv (m := m + 1) (n := 1)).surjective q <;>
    rw [modelD, reindex_apply, submatrix_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  · have _ := ip.isLt; have _ := iq.isLt
    simp only [fromBlocks_apply₁₁, forkFlip, negShift, Matrix.of_apply, finSumFinEquiv_apply_left,
      Fin.val_castAdd, Fin.ext_iff] at hrot ⊢; split_ifs at hrot ⊢ <;> omega
  · fin_cases iq; have _ := ip.isLt
    simp [forkFlip, Fin.ext_iff] at hrot ⊢; split_ifs at hrot ⊢ <;> omega
  · fin_cases ip; have _ := iq.isLt
    simp [forkFlip, Fin.ext_iff] at hrot ⊢; split_ifs at hrot ⊢ <;> omega
  · fin_cases ip; fin_cases iq; simp [forkFlip] at hrot ⊢; split_ifs at hrot ⊢ <;> omega

private theorem modelD_mul_basisD_eq_basisD_mul_coxD (m : ℕ) :
    modelD m * basisD m = basisD m * coxD (m + 2) := by
  have h1 := permMatrixHom_finRotate_mul_eq (basisD m)
    (fun i => reflMatrix (CartanMatrix.D (m + 2)) i.castSucc)
    permMatrixHom_transposition_mul_basisD
  rw [← permMatrixHom_finRotate_mul_forkFlip, mul_assoc, forkFlip_mul_basisD, ← mul_assoc, h1,
    mul_assoc, coxD, coxeterElement, List.finRange_succ_last (n := m + 1), List.map_append,
    List.prod_append, List.map_singleton, List.prod_singleton, List.map_map]
  rfl

/-- The empty type `D₀` Coxeter element has characteristic polynomial `1`. -/
theorem charpoly_coxD_zero : (coxD 0).charpoly = 1 := by simp

/-- The degenerate rank-`1` type `D₁` Coxeter element (`-1`) has characteristic polynomial
`X + 1`. -/
@[simp]
theorem charpoly_coxD_one : (coxD 1).charpoly = X + 1 := by
  have h1 : coxD 1 = -1 := by decide
  rw [h1, Matrix.charpoly, Matrix.det_fin_one]
  simp [sub_neg_eq_add]

/-- **Characteristic polynomial of the type `D` Coxeter element** (`2 ≤ n`):
`(X ^ (n - 1) + 1) * (X + 1)`. Holds for `D₂ = A₁ × A₁` and `D₃ = A₃` as well as `n ≥ 4`. -/
theorem charpoly_coxD {n : ℕ} (hn : 2 ≤ n) :
    (coxD n).charpoly = (X ^ (n - 1) + 1) * (X + 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have hsub : m + 2 - 1 = m + 1 := rfl
  rw [hsub,
    (Matrix.charpoly_eq_of_mul_eq_mul (isLeftRegular_det_basisD m).ne_zero
      (modelD_mul_basisD_eq_basisD_mul_coxD m)).symm,
    modelD, charpoly_reindex, charpoly_fromBlocks_zero₂₁, charpoly_negShift (Nat.succ_pos m)]
  congr 1
  rw [Matrix.charpoly, Matrix.det_fin_one]; simp [sub_neg_eq_add]

/-- The empty type `D₀` Coxeter element has order `1`. -/
@[simp]
theorem orderOf_coxD_zero : orderOf (coxD 0) = 1 := by
  rw [Subsingleton.elim (coxD 0) 1, orderOf_one]

/-- The degenerate rank-`1` type `D₁` Coxeter element (`-1`) has order `2`. -/
@[simp]
theorem orderOf_coxD_one : orderOf (coxD 1) = 2 :=
  (orderOf_eq_iff (by norm_num)).mpr ⟨by decide +kernel, by decide +kernel⟩

private theorem orderOf_modelD (m : ℕ) : orderOf (modelD m) = 2 * (m + 1) := by
  let e := finSumFinEquiv (m := m + 1) (n := 1)
  have hre : modelD m = (reindexAlgEquiv ℤ ℤ e).toRingEquiv.toMulEquiv
      (fromBlocks (negShift (m + 1)) 0 0 (-1 : Matrix (Fin 1) (Fin 1) ℤ)) := rfl
  rw [hre, MulEquiv.orderOf_eq]
  refine (orderOf_eq_iff (by omega)).mpr ⟨?_, fun k hk hpos hk1 => ?_⟩
  · rw [fromBlocks_diagonal_pow, ← orderOf_negShift (Nat.succ_pos m), pow_orderOf_eq_one,
      orderOf_negShift (Nat.succ_pos m), pow_mul, neg_one_sq, one_pow, fromBlocks_one]
  · rw [fromBlocks_diagonal_pow] at hk1
    have h11 : negShift (m + 1) ^ k = 1 := by
      ext i j; simpa [Matrix.one_apply] using congrFun₂ hk1 (Sum.inl i) (Sum.inl j)
    have hle := orderOf_le_of_pow_eq_one hpos h11
    rw [orderOf_negShift (Nat.succ_pos m)] at hle; omega

/-- **The Coxeter number of `Dₙ` (`2 ≤ n`) is `2 * (n - 1)`**: the Coxeter element of
`CartanMatrix.D n` has order `2 * (n - 1)`. -/
theorem orderOf_coxD {n : ℕ} (hn : 2 ≤ n) : orderOf (coxD n) = 2 * (n - 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have hsub : m + 2 - 1 = m + 1 := rfl
  rw [hsub,
    SemiconjBy.orderOf_eq_of_isRegular
      (isRegular_of_isLeftRegular_det (isLeftRegular_det_basisD m))
      (modelD_mul_basisD_eq_basisD_mul_coxD m).symm, orderOf_modelD]

end TauCeti.Coxeter

end
