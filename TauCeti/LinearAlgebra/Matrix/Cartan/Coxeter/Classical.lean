/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
public import TauCeti.Data.List.OneDegenerateOrder
public import TauCeti.LinearAlgebra.Matrix.Cartan.Coxeter.Basic
import TauCeti.Data.Fin.Basic
import TauCeti.GroupTheory.Perm.Fin
import TauCeti.GroupTheory.Perm.OrbitCount.FinRotate
import TauCeti.LinearAlgebra.Matrix.Charpoly.Cyclic
import TauCeti.LinearAlgebra.Matrix.Intertwine
import TauCeti.LinearAlgebra.Matrix.Permutation

/-!
# Coxeter elements of the classical Cartan matrices

Computes the order and characteristic polynomial of the standard Coxeter element `c = s₁ ⋯ sₙ`
(`Matrix.coxeterElement`) of `CartanMatrix.A n`, `B n`, `C n`, `D n`, and shows `List.finRange n`
is a one-degenerate order (`List.IsOneDegenerateOrder`) of each Dynkin diagram:

| type | rank bound | `h` | characteristic polynomial |
|---|---|---|---|
| `Aₙ` | all `n` | `n + 1` | `∑_{k=0}^n X^k` |
| `Bₙ`, `Cₙ` | `1 ≤ n` | `2 n` | `X^n + 1` |
| `Dₙ` | `2 ≤ n` | `2 (n - 1)` | `(X^{n-1} + 1)(X + 1)` |

Each family reduces by explicit integral intertwining to a cycle (`Aₙ`), signed cycle (`Bₙ`, and
`Cₙ` via diagonal conjugation to `Bₙ`), or block-diagonal signed `(n - 1)`-cycle plus `-1` (`Dₙ`).

## Main results

* `TauCeti.Coxeter.isOneDegenerateOrder_A` (`B`, `C`, `D`): one-degeneracy of `List.finRange n`.
* `TauCeti.Coxeter.orderOf_coxeterElement_A` (`B`, `C`, `D`) and
  `TauCeti.Coxeter.charpoly_coxeterElement_A` (`B`, `C`, `D`): Coxeter order and characteristic
  polynomial for each classical family.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Ch. V, §6, and Plates I--IV.
* J. E. Humphreys, *Reflection Groups and Coxeter Groups*, Cambridge (1990), §§ 3.16--3.20.
-/

public section

open Matrix Polynomial

namespace TauCeti.Coxeter

/-! ### One-degenerate orders of the classical diagrams -/

/-- The Bourbaki numbering `List.finRange n` is a one-degenerate order of the Dynkin diagram of
type `Aₙ`. -/
theorem isOneDegenerateOrder_A (n : ℕ) :
    List.IsOneDegenerateOrder (fun i j : Fin n => CartanMatrix.A n i j ≠ 0) (List.finRange n) :=
  List.isOneDegenerateOrder_finRange fun _ _ _ hxz hyz hzx hzy => by
    simp only [CartanMatrix.A, Matrix.of_apply] at hzx hzy
    exact Fin.ext (by split_ifs at hzx hzy <;> omega)

/-- The Bourbaki numbering `List.finRange n` is a one-degenerate order of the Dynkin diagram of
type `Bₙ`. -/
theorem isOneDegenerateOrder_B (n : ℕ) :
    List.IsOneDegenerateOrder (fun i j : Fin n => CartanMatrix.B n i j ≠ 0) (List.finRange n) :=
  List.isOneDegenerateOrder_finRange fun _ _ _ hxz hyz hzx hzy => by
    simp only [CartanMatrix.B, Matrix.of_apply] at hzx hzy
    exact Fin.ext (by split_ifs at hzx hzy <;> omega)

/-- The Bourbaki numbering `List.finRange n` is a one-degenerate order of the Dynkin diagram of
type `Cₙ`. -/
theorem isOneDegenerateOrder_C (n : ℕ) :
    List.IsOneDegenerateOrder (fun i j : Fin n => CartanMatrix.C n i j ≠ 0) (List.finRange n) :=
  List.isOneDegenerateOrder_finRange fun _ _ _ hxz hyz hzx hzy => by
    simp only [CartanMatrix.C, Matrix.of_apply] at hzx hzy
    exact Fin.ext (by split_ifs at hzx hzy <;> omega)

/-- The Bourbaki numbering `List.finRange n` is a one-degenerate order of the Dynkin diagram of
type `Dₙ`: every node `z` is adjacent to at most one node of smaller index (`z - 1` on the stem
and on the first prong, and the branch node `n - 3` on the second prong `n - 1`). -/
theorem isOneDegenerateOrder_D (n : ℕ) :
    List.IsOneDegenerateOrder (fun i j : Fin n => CartanMatrix.D n i j ≠ 0) (List.finRange n) :=
  List.isOneDegenerateOrder_finRange fun _ _ _ hxz hyz hzx hzy => by
    simp only [CartanMatrix.D, Matrix.of_apply] at hzx hzy
    exact Fin.ext (by split_ifs at hzx hzy <;> omega)

/-! ### Type `Aₙ`: root-difference embedding into the `(n + 1)`-cycle -/

/-- The `(n + 1) × n` integer matrix whose `j`-th column is `eⱼ - eⱼ₊₁`. -/
private def matPA (n : ℕ) : Matrix (Fin (n + 1)) (Fin n) ℤ :=
  Matrix.of fun r j =>
    (if r.val = j.val then 1 else 0) - (if r.val = j.val + 1 then 1 else 0)

private lemma matPA_mulVec_single (n : ℕ) (j : Fin n) :
    matPA n *ᵥ Pi.single j 1 =
      Pi.single ⟨j.val, by omega⟩ 1 - Pi.single ⟨j.val + 1, by omega⟩ 1 := by
  ext r; simp [Matrix.mulVec_single, matPA, Pi.single_apply, Fin.ext_iff, eq_comm]

/-- Explicit left inverse of `matPA n`: summing rows `0, …, i` recovers the `i`-th coordinate. -/
private def leftInvPA (n : ℕ) : Matrix (Fin n) (Fin (n + 1)) ℤ :=
  Matrix.of fun i r => if r.val ≤ i.val then 1 else 0

private lemma leftInvPA_mul_matPA (n : ℕ) : leftInvPA n * matPA n = 1 := by
  ext i j
  have hsum : ∀ k : Fin (n + 1),
      (∑ r : Fin (n + 1), (if r.val ≤ i.val then (1 : ℤ) else 0) *
        (if r.val = k.val then 1 else 0)) = if k.val ≤ i.val then 1 else 0 := fun k => by
    rw [Finset.sum_eq_single k]
    · simp
    · intro r _ hr; simp [Fin.val_ne_of_ne hr]
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [Matrix.mul_apply]
  simp only [leftInvPA, matPA, Matrix.of_apply, mul_sub, Finset.sum_sub_distrib,
    hsum ⟨j.val, by omega⟩, hsum ⟨j.val + 1, by omega⟩, Matrix.one_apply, Fin.ext_iff]
  split_ifs <;> omega

private lemma matPA_mul_reflMatrix (n : ℕ) (i : Fin n) :
    matPA n * reflMatrix (CartanMatrix.A n) i =
      permMatrixHom (Equiv.swap (⟨i.val, by omega⟩ : Fin (n + 1)) ⟨i.val + 1, by omega⟩) *
        matPA n := by
  ext r j
  rw [mul_reflMatrix_apply, permMatrixHom_swap_mul_apply, Equiv.swap_apply_def]
  have := r.isLt; have := j.isLt; have := i.isLt
  simp only [matPA, CartanMatrix.A, Matrix.of_apply, apply_ite Fin.val, Fin.ext_iff]
  split_ifs <;> omega

private lemma matPA_mul_coxeterElement (n : ℕ) :
    matPA n * coxeterElement (CartanMatrix.A n) =
      permMatrixHom (finRotate (n + 1)) * matPA n := by
  rw [mul_coxeterElement (matPA n) (CartanMatrix.A n) _ (matPA_mul_reflMatrix n)]
  congr 1
  rw [← Fin.cycleRange_last n]
  exact prod_finRange_permMatrixHom_adjSwap n (Nat.lt_succ_self n)

private lemma coxeterElement_A_pow_mulVec_single_zero {n : ℕ} (hn : 0 < n) (m : ℕ)
    (hm : m < n) :
    coxeterElement (CartanMatrix.A n) ^ m *ᵥ Pi.single ⟨0, hn⟩ 1 = Pi.single ⟨m, hm⟩ 1 := by
  have hcol : (matPA n * coxeterElement (CartanMatrix.A n) ^ m) *ᵥ Pi.single ⟨0, hn⟩ 1 =
      matPA n *ᵥ Pi.single ⟨m, hm⟩ 1 := by
    rw [(pow_mul_eq_mul_pow (matPA_mul_coxeterElement n).symm m).symm, ← Matrix.mulVec_mulVec,
      matPA_mulVec_single, matPA_mulVec_single, Matrix.mulVec_sub, ← map_pow,
      permMatrixHom_mulVec_single, permMatrixHom_mulVec_single]
    congr 1
    · congr 1; exact Fin.ext (by
        simp [Fin.coe_finRotate_pow, Nat.mod_eq_of_lt (by omega : m < n + 1)])
    · congr 1; exact Fin.ext (by simp [Fin.coe_finRotate_pow, Nat.add_comm 1 m,
        Nat.mod_eq_of_lt (by omega : m + 1 < n + 1)])
  have h1 := congrArg (leftInvPA n *ᵥ ·) hcol
  rwa [Matrix.mulVec_mulVec, ← Matrix.mul_assoc, leftInvPA_mul_matPA, Matrix.one_mul,
    Matrix.mulVec_mulVec, leftInvPA_mul_matPA, Matrix.one_mulVec] at h1

private lemma sum_coxeterElement_A_pow_eq_zero (n : ℕ) :
    (∑ m ∈ Finset.range (n + 1), coxeterElement (CartanMatrix.A n) ^ m) = 0 := by
  apply Matrix.mul_right_injective_of_inv _ _ (leftInvPA_mul_matPA n)
  dsimp only
  rw [Matrix.mul_zero, Matrix.mul_sum]
  simp_rw [← (pow_mul_eq_mul_pow (matPA_mul_coxeterElement n).symm _), ← Matrix.sum_mul]
  set C : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ := permMatrixHom (finRotate (n + 1))
  have hrot_pow : finRotate (n + 1) ^ (n + 1) = 1 := by
    simpa [TauCeti.orderOf_finRotate (by omega : n + 1 ≠ 0)] using
      pow_orderOf_eq_one (finRotate (n + 1))
  have hpow : C ^ (n + 1) = 1 := by
    dsimp [C]
    rw [← map_pow, hrot_pow, map_one]
  have hgeom : (∑ m ∈ Finset.range (n + 1), C ^ m) * (1 - C) = 0 := by
    rw [geom_sum_mul_neg, hpow, sub_self]
  apply Matrix.ext_of_mulVec_single
  intro j
  have hcol : matPA n *ᵥ Pi.single j 1 = (1 - C) *ᵥ Pi.single ⟨j.val, by omega⟩ 1 := by
    rw [matPA_mulVec_single, Matrix.sub_mulVec, Matrix.one_mulVec, permMatrixHom_mulVec_single]
    congr 2; ext
    simp [finRotate_apply, Fin.val_add, Nat.mod_eq_of_lt (by omega : j.val + 1 < n + 1)]
  rw [← Matrix.mulVec_mulVec, hcol, Matrix.mulVec_mulVec, hgeom, Matrix.zero_mulVec,
    Matrix.zero_mulVec]

/-- **The characteristic polynomial of the `Aₙ` Coxeter element is `1 + X + ⋯ + X^n`.** -/
theorem charpoly_coxeterElement_A (n : ℕ) :
    (coxeterElement (CartanMatrix.A n)).charpoly = ∑ k ∈ Finset.range (n + 1), X ^ k := by
  rcases n.eq_zero_or_pos with rfl | hn
  · simp
  · have hmon : (∑ k ∈ Finset.range (n + 1), (X : ℤ[X]) ^ k).IsMonicOfDegree n := by
      rw [Finset.sum_range_succ, add_comm]
      refine (isMonicOfDegree_X_pow ℤ n).add_right ?_
      by_cases hp0 : (∑ k ∈ Finset.range n, (X : ℤ[X]) ^ k) = 0
      · rw [hp0, natDegree_zero]; exact hn
      · rw [natDegree_lt_iff_degree_lt hp0]
        refine (Polynomial.degree_sum_le (Finset.range n) _).trans_lt ?_
        refine (Finset.sup_lt_iff (WithBot.bot_lt_coe n)).mpr fun k hk => ?_
        rw [degree_X_pow]
        exact WithBot.coe_lt_coe.2 (Finset.mem_range.mp hk)
    exact charpoly_eq_of_isMonicOfDegree_of_aeval_eq_zero_of_pow_mulVec_single hn hmon
      (by simpa using sum_coxeterElement_A_pow_eq_zero n)
      (coxeterElement_A_pow_mulVec_single_zero hn)

/-- **The Coxeter number of `Aₙ` is `n + 1`**: the Coxeter element of type `Aₙ` has order
`n + 1`. -/
theorem orderOf_coxeterElement_A (n : ℕ) :
    orderOf (coxeterElement (CartanMatrix.A n)) = n + 1 := by
  rcases n.eq_zero_or_pos with rfl | hn
  · exact orderOf_eq_one_iff.mpr (Subsingleton.elim _ _)
  · have hpow : coxeterElement (CartanMatrix.A n) ^ (n + 1) = 1 := by
      have hgeom := geom_sum_mul (coxeterElement (CartanMatrix.A n)) (n + 1)
      rw [sum_coxeterElement_A_pow_eq_zero, zero_mul] at hgeom
      exact sub_eq_zero.mp hgeom.symm
    refine (orderOf_eq_iff (Nat.succ_pos n)).mpr ⟨hpow, fun m hm hpos h1 => ?_⟩
    rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hm) with hmn | hmn
    · have hv := congrFun (coxeterElement_A_pow_mulVec_single_zero hn m hmn) ⟨0, hn⟩
      simp [h1, Fin.ext_iff, hpos.ne'] at hv
    · rw [hmn] at h1
      have hc1 : coxeterElement (CartanMatrix.A n) = 1 := by
        simpa [pow_succ, h1] using hpow
      have hsum := congrFun₂ (sum_coxeterElement_A_pow_eq_zero n) ⟨0, hn⟩ ⟨0, hn⟩
      simp [hc1] at hsum
      omega

/-! ### Type `Bₙ`: lower-unitriangular conjugation to the signed `n`-cycle -/

/-- The `n × n` lower-unitriangular matrix with columns `e₀ - e₁, …, eₙ₋₂ - eₙ₋₁, eₙ₋₁`. -/
private def matPB (n : ℕ) : Matrix (Fin n) (Fin n) ℤ :=
  Matrix.of fun r j =>
    if j.val + 1 < n then
      (if r.val = j.val then 1 else 0) - (if r.val = j.val + 1 then 1 else 0)
    else
      if r = j then 1 else 0

private lemma det_matPB (n : ℕ) : (matPB n).det = 1 := by
  have htri : (matPB n).IsLowerTriangular := fun i j hij => by
    have hlt : i.val < j.val := Fin.lt_def.mp hij
    simp only [matPB, Matrix.of_apply, Fin.ext_iff]; split_ifs <;> omega
  rw [Matrix.det_of_isLowerTriangular _ htri]
  refine Finset.prod_eq_one fun i _ => ?_
  simp only [matPB, Matrix.of_apply]; split_ifs <;> omega

/-- Coordinate simple reflections of type `Bₙ`: adjacent swaps for `i < n - 1`, and negation of the
last coordinate for `i = n - 1`. -/
private def reflCoordB (n : ℕ) (i : Fin n) : Matrix (Fin n) (Fin n) ℤ :=
  if hi : i.val + 1 < n then permMatrixHom (Equiv.swap i ⟨i.val + 1, hi⟩)
  else Matrix.diagonal fun r : Fin n => if r.val + 1 = n then -1 else 1

private lemma matPB_mul_reflMatrix (n : ℕ) (i : Fin n) :
    matPB n * reflMatrix (CartanMatrix.B n) i = reflCoordB n i * matPB n := by
  ext r j
  rw [mul_reflMatrix_apply]
  have := r.isLt; have := j.isLt; have := i.isLt
  by_cases hi : i.val + 1 < n
  · rw [reflCoordB, dite_eq_left_of_eq_true (eq_true hi), permMatrixHom_swap_mul_apply,
      Equiv.swap_apply_def]
    simp only [matPB, CartanMatrix.B, Matrix.of_apply, apply_ite Fin.val, Fin.ext_iff]
    split_ifs <;> omega
  · rw [reflCoordB, dite_eq_right_of_eq_false (eq_false hi), Matrix.diagonal_mul]
    simp only [matPB, CartanMatrix.B, Matrix.of_apply, Fin.ext_iff]
    split_ifs <;> omega

private lemma matPB_mul_coxeterElement {n : ℕ} (hn : 1 ≤ n) :
    matPB n * coxeterElement (CartanMatrix.B n) = negCycleMatrix n * matPB n := by
  rw [mul_coxeterElement (matPB n) (CartanMatrix.B n) (reflCoordB n) (matPB_mul_reflMatrix n)]
  congr 1
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [prod_finRange_succ_adjSwap (reflCoordB (m + 1)) fun i => by
    simp [reflCoordB, Nat.add_lt_add_right i.isLt 1]; rfl]
  ext r j
  rw [permMatrixHom_mul_apply]
  rcases eq_or_ne r 0 with rfl | hr
  · rw [Fin.finRotate_symm_zero]
    have := j.isLt
    simp only [reflCoordB, Fin.val_last, lt_self_iff_false, ↓reduceDIte, Matrix.diagonal_apply,
      negCycleMatrix_apply, Fin.ext_iff, Fin.val_zero, ↓reduceIte]
    split_ifs <;> first | contradiction | omega
  · have hsub := coe_finRotate_symm_of_ne_zero hr
    have := r.isLt; have := j.isLt
    have hr0 : r.val ≠ 0 := Fin.val_ne_zero_iff.mpr hr
    simp only [reflCoordB, Fin.val_last, lt_self_iff_false, ↓reduceDIte, Matrix.diagonal_apply,
      negCycleMatrix_apply, Fin.ext_iff, hsub]
    split_ifs <;> omega

/-- **The characteristic polynomial of the `Bₙ` Coxeter element is `X^n + 1`** (`1 ≤ n`). -/
theorem charpoly_coxeterElement_B {n : ℕ} (hn : 1 ≤ n) :
    (coxeterElement (CartanMatrix.B n)).charpoly = X ^ n + 1 :=
  (Matrix.charpoly_eq_of_mul_eq_mul (by rw [det_matPB]; norm_num)
    (matPB_mul_coxeterElement hn).symm).symm.trans (charpoly_negCycleMatrix hn)

/-- **The Coxeter number of `Bₙ` is `2 n`** (`1 ≤ n`): the Coxeter element of type `Bₙ` has order
`2 n`. -/
theorem orderOf_coxeterElement_B {n : ℕ} (hn : 1 ≤ n) :
    orderOf (coxeterElement (CartanMatrix.B n)) = 2 * n :=
  (Matrix.orderOf_eq_of_mul_eq_mul (by rw [det_matPB]; norm_num)
    (matPB_mul_coxeterElement hn).symm).symm.trans (orderOf_negCycleMatrix hn)

/-! ### Type `Cₙ`: diagonal conjugation to type `Bₙ` -/

/-- The diagonal matrix `diag(1, …, 1, 2)` intertwining `coxeterElement (CartanMatrix.C n)` with
`coxeterElement (CartanMatrix.B n)`. -/
private def diagBC (n : ℕ) : Matrix (Fin n) (Fin n) ℤ :=
  Matrix.diagonal fun k : Fin n => if k.val + 1 = n then 2 else 1

private lemma det_diagBC_ne_zero (n : ℕ) : (diagBC n).det ≠ 0 := by
  rw [diagBC, Matrix.det_diagonal]
  exact Finset.prod_ne_zero_iff.mpr fun k _ => by split_ifs <;> norm_num

private lemma diagBC_mul_reflMatrix (n : ℕ) (i : Fin n) :
    diagBC n * reflMatrix (CartanMatrix.C n) i = reflMatrix (CartanMatrix.B n) i * diagBC n := by
  ext r j
  rw [diagBC, Matrix.diagonal_mul, Matrix.mul_diagonal]
  have := r.isLt; have := j.isLt; have := i.isLt
  simp only [reflMatrix_apply, CartanMatrix.B, CartanMatrix.C, Matrix.of_apply, Fin.ext_iff]
  split_ifs <;> omega

private lemma diagBC_mul_coxeterElement (n : ℕ) :
    diagBC n * coxeterElement (CartanMatrix.C n) =
      coxeterElement (CartanMatrix.B n) * diagBC n :=
  mul_coxeterElement (diagBC n) (CartanMatrix.C n) (reflMatrix (CartanMatrix.B n))
    (diagBC_mul_reflMatrix n)

/-- **The characteristic polynomial of the `Cₙ` Coxeter element is `X^n + 1`** (`1 ≤ n`). -/
theorem charpoly_coxeterElement_C {n : ℕ} (hn : 1 ≤ n) :
    (coxeterElement (CartanMatrix.C n)).charpoly = X ^ n + 1 :=
  (Matrix.charpoly_eq_of_mul_eq_mul (det_diagBC_ne_zero n)
    (diagBC_mul_coxeterElement n).symm).symm.trans (charpoly_coxeterElement_B hn)

/-- **The Coxeter number of `Cₙ` is `2 n`** (`1 ≤ n`): the Coxeter element of type `Cₙ` has order
`2 n`. -/
theorem orderOf_coxeterElement_C {n : ℕ} (hn : 1 ≤ n) :
    orderOf (coxeterElement (CartanMatrix.C n)) = 2 * n :=
  (Matrix.orderOf_eq_of_mul_eq_mul (det_diagBC_ne_zero n)
    (diagBC_mul_coxeterElement n).symm).symm.trans (orderOf_coxeterElement_B hn)

/-! ### Type `Dₙ`: block-diagonal conjugation to a signed `(n - 1)`-cycle and `-1` -/

/-- The `n × n` integer matrix with columns `e₀ - e₁, …, eₙ₋₂ - eₙ₋₁, eₙ₋₂ + eₙ₋₁`. -/
private def matPD (n : ℕ) : Matrix (Fin n) (Fin n) ℤ :=
  Matrix.of fun r j =>
    if j.val + 1 < n then
      (if r.val = j.val then 1 else 0) - (if r.val = j.val + 1 then 1 else 0)
    else
      (if r.val + 2 = n then 1 else 0) + (if r.val + 1 = n then 1 else 0)

/-- Upper-triangular column operation `col_{n-1} ↦ col_{n-2} + 2 col_{n-1}` relating `matPB n` to
`matPD n`. -/
private def upperUD (n : ℕ) : Matrix (Fin n) (Fin n) ℤ :=
  Matrix.of fun k j =>
    if j.val + 1 < n then if k = j then 1 else 0
    else (if k.val + 2 = n then 1 else 0) + (if k.val + 1 = n then 2 else 0)

private lemma matPB_mul_upperUD {n : ℕ} (hn : 2 ≤ n) : matPB n * upperUD n = matPD n := by
  ext r j
  rw [Matrix.mul_apply]
  by_cases hj : j.val + 1 < n
  · rw [Finset.sum_eq_single j]
    · simp [matPB, upperUD, matPD, hj]
    · intro k _ hkj; simp [upperUD, hj, hkj]
    · intro h; exact absurd (Finset.mem_univ _) h
  · have h1 : ∀ k : Fin n, (k.val + 2 = n) ↔ k = ⟨n - 2, by omega⟩ := fun k => by
      simp only [Fin.ext_iff]; omega
    have h2 : ∀ k : Fin n, (k.val + 1 = n) ↔ k = ⟨n - 1, by omega⟩ := fun k => by
      simp only [Fin.ext_iff]; omega
    simp only [upperUD, Matrix.of_apply, hj, ↓reduceIte, mul_add, Finset.sum_add_distrib,
      h1, h2, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ]
    have := r.isLt; have := j.isLt
    simp only [matPB, matPD, Matrix.of_apply, hj, ↓reduceIte, Fin.ext_iff]
    split_ifs <;> omega

private lemma det_matPD {n : ℕ} (hn : 2 ≤ n) : (matPD n).det = 2 := by
  rw [← matPB_mul_upperUD hn, Matrix.det_mul, det_matPB, one_mul]
  have htri : (upperUD n).IsUpperTriangular := fun i j hij => by
    have hlt : j.val < i.val := Fin.lt_def.mp hij
    have := i.isLt
    simp only [upperUD, Matrix.of_apply, Fin.ext_iff]; split_ifs <;> omega
  rw [Matrix.det_of_isUpperTriangular htri]
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [Fin.prod_univ_castSucc, Finset.prod_eq_one fun i _ => by simp [upperUD], one_mul]
  simp only [upperUD, Matrix.of_apply, Fin.val_last]; split_ifs <;> omega

private lemma cartanMatrixD_apply_of_lt {n : ℕ} {i : Fin n} (hi : i.val + 1 < n) (j : Fin n) :
    CartanMatrix.D n j i =
      if j = i then 2
      else if n ≤ 2 then 0
      else if j.val + 1 < n then
        if j.val + 1 = i.val ∨ (i.val + 1 = j.val ∧ i.val + 2 < n) then -1 else 0
      else
        if i.val + 3 = n then -1 else 0 := by
  have := j.isLt
  simp only [CartanMatrix.D, Matrix.of_apply, Fin.ext_iff]; split_ifs <;> omega

private lemma cartanMatrixD_apply_of_not_lt {n : ℕ} {i : Fin n} (hi : ¬ i.val + 1 < n)
    (j : Fin n) :
    CartanMatrix.D n j i =
      if j = i then 2 else if n ≤ 2 then 0 else if j.val + 3 = n then -1 else 0 := by
  have := i.isLt; have := j.isLt
  simp only [CartanMatrix.D, Matrix.of_apply, Fin.ext_iff]; split_ifs <;> omega

/-- Diagonal sign matrix negating the last two coordinates `n - 2` and `n - 1`. -/
private def negLastTwo (n : ℕ) : Matrix (Fin n) (Fin n) ℤ :=
  Matrix.diagonal fun r : Fin n => if n ≤ r.val + 2 then -1 else 1

/-- The last reflection of `Dₙ` in standard coordinates sends `eₙ₋₂ ↦ -eₙ₋₁`, `eₙ₋₁ ↦ -eₙ₋₂`, and
fixes `eᵣ` for `r < n - 2`. -/
private def lastReflD {n : ℕ} (hn : 2 ≤ n) : Matrix (Fin n) (Fin n) ℤ :=
  negLastTwo n * permMatrixHom (Equiv.swap ⟨n - 2, by omega⟩ ⟨n - 1, by omega⟩)

private lemma lastReflD_mul_apply {n : ℕ} (hn : 2 ≤ n) {κ : Type*} (M : Matrix (Fin n) κ ℤ)
    (r : Fin n) (j : κ) :
    (lastReflD hn * M) r j =
      if r.val + 1 = n then -M ⟨n - 2, by omega⟩ j
      else if r.val + 2 = n then -M ⟨n - 1, by omega⟩ j
      else M r j := by
  rw [lastReflD, Matrix.mul_assoc, negLastTwo, Matrix.diagonal_mul,
    permMatrixHom_swap_mul_apply, Equiv.swap_apply_def]
  have := r.isLt
  simp only [Fin.ext_iff]
  split_ifs <;> simp <;> omega

private lemma lastReflD_eq_swap_mul_diag {n : ℕ} (hn : 2 ≤ n) :
    lastReflD hn =
      permMatrixHom (Equiv.swap ⟨n - 2, by omega⟩ ⟨n - 1, by omega⟩) * negLastTwo n := by
  ext r j
  rw [lastReflD, negLastTwo, Matrix.diagonal_mul, permMatrixHom_swap_mul_apply,
    ← Matrix.mul_one (permMatrixHom (Equiv.swap _ _)), permMatrixHom_swap_mul_apply,
    Equiv.swap_apply_def, Matrix.diagonal_apply]
  have := r.isLt; have := j.isLt
  simp only [Matrix.one_apply, apply_ite Fin.val, Fin.ext_iff]
  split_ifs <;> omega

/-- Coordinate simple reflections of type `Dₙ`. -/
private def reflCoordD {n : ℕ} (hn : 2 ≤ n) (i : Fin n) : Matrix (Fin n) (Fin n) ℤ :=
  if hi : i.val + 1 < n then permMatrixHom (Equiv.swap i ⟨i.val + 1, hi⟩) else lastReflD hn

private lemma matPD_mul_reflMatrix {n : ℕ} (hn : 2 ≤ n) (i : Fin n) :
    matPD n * reflMatrix (CartanMatrix.D n) i = reflCoordD hn i * matPD n := by
  ext r j
  rw [mul_reflMatrix_apply]
  have := r.isLt; have := j.isLt; have := i.isLt
  by_cases hi : i.val + 1 < n
  · rw [reflCoordD, dite_eq_left_of_eq_true (eq_true hi), permMatrixHom_swap_mul_apply,
      Equiv.swap_apply_def, cartanMatrixD_apply_of_lt hi j]
    by_cases hj : j.val + 1 < n
    · rcases eq_or_ne j i with rfl | hji
      · simp only [↓reduceIte, matPD, Matrix.of_apply, hi, apply_ite Fin.val, Fin.ext_iff]
        split_ifs <;> omega
      · simp only [hji, hj, hi, ↓reduceIte, matPD, Matrix.of_apply, apply_ite Fin.val, Fin.ext_iff]
        split_ifs <;> omega
    · have hji : j ≠ i := fun h => hj (h ▸ hi)
      simp only [hji, hj, hi, ↓reduceIte, matPD, Matrix.of_apply, apply_ite Fin.val, Fin.ext_iff]
      split_ifs <;> omega
  · rw [reflCoordD, dite_eq_right_of_eq_false (eq_false hi), lastReflD_mul_apply hn,
      cartanMatrixD_apply_of_not_lt hi j]
    by_cases hj : j.val + 1 < n
    · have hji : j ≠ i := fun h => hi (h ▸ hj)
      simp only [hji, hj, hi, ↓reduceIte, matPD, Matrix.of_apply]
      split_ifs <;> omega
    · have hji : j = i := Fin.ext (by omega)
      simp only [hji, hi, ↓reduceIte, matPD, Matrix.of_apply]
      split_ifs <;> omega

/-- Block-diagonal model of `coxeterElement (CartanMatrix.D (m + 1))`: `negCycleMatrix m` on
`Fin m` and `-1` on `Fin 1`. -/
private def blockModelD (m : ℕ) : Matrix (Fin m ⊕ Fin 1) (Fin m ⊕ Fin 1) ℤ :=
  Matrix.fromBlocks (negCycleMatrix m) 0 0 (-1)

/-- `blockModelD m` transported to `Fin (m + 1)` along `finSumFinEquiv`. -/
private def modelDSucc (m : ℕ) : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ :=
  (blockModelD m).reindex (finSumFinEquiv : Fin m ⊕ Fin 1 ≃ Fin (m + 1))
    (finSumFinEquiv : Fin m ⊕ Fin 1 ≃ Fin (m + 1))

private lemma permMatrixHom_finRotate_mul_lastReflD {m : ℕ} (hm : 1 ≤ m) :
    permMatrixHom (finRotate (m + 1)) * lastReflD (n := m + 1) (by omega) = modelDSucc m := by
  have hrot (x : Fin (m + 1)) :
      ((finRotate (m + 1)).symm x : ℕ) = if x = 0 then m else x.val - 1 := by
    split_ifs with hx
    · subst hx; rw [Fin.finRotate_symm_zero, Fin.val_last]
    · exact coe_finRotate_symm_of_ne_zero hx
  rw [lastReflD_eq_swap_mul_diag]
  ext r j
  rw [permMatrixHom_mul_apply, permMatrixHom_swap_mul_apply, Equiv.swap_apply_def,
    negLastTwo, Matrix.diagonal_apply]
  refine Fin.lastCases ?_ (fun r₀ => ?_) r <;> refine Fin.lastCases ?_ (fun j₀ => ?_) j <;>
    simp only [modelDSucc, Matrix.reindex_apply, Matrix.submatrix_apply, blockModelD,
      finSumFinEquiv_symm_last, finSumFinEquiv_symm_apply_castSucc,
      Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
      Matrix.fromBlocks_apply₂₂, Matrix.neg_apply, Matrix.one_apply_eq, Matrix.zero_apply,
      negCycleMatrix_apply, apply_ite Fin.val, Fin.ext_iff, Fin.val_last,
      Fin.val_castSucc, Fin.val_zero, hrot] <;>
    (try have := r₀.isLt) <;> (try have := j₀.isLt) <;> split_ifs <;> omega

private lemma matPD_mul_coxeterElement_D_succ {m : ℕ} (hm : 1 ≤ m) :
    matPD (m + 1) * coxeterElement (CartanMatrix.D (m + 1)) = modelDSucc m * matPD (m + 1) := by
  rw [mul_coxeterElement (matPD (m + 1)) (CartanMatrix.D (m + 1))
    (reflCoordD (by omega)) (matPD_mul_reflMatrix (by omega))]
  congr 1
  rw [prod_finRange_succ_adjSwap (reflCoordD (by omega)) fun i => by
    simp [reflCoordD, Nat.add_lt_add_right i.isLt 1]; rfl]
  simpa [reflCoordD] using permMatrixHom_finRotate_mul_lastReflD hm

private lemma charpoly_modelDSucc {m : ℕ} (hm : 1 ≤ m) :
    (modelDSucc m).charpoly = (X ^ m + 1) * (X + 1) := by
  rw [modelDSucc, Matrix.charpoly_reindex, blockModelD, Matrix.charpoly_fromBlocks_zero₁₂,
    charpoly_negCycleMatrix hm]
  congr 1
  rw [Matrix.charpoly, Matrix.charmatrix, Matrix.det_fin_one]
  simp [sub_neg_eq_add]

private lemma orderOf_modelDSucc {m : ℕ} (hm : 1 ≤ m) :
    orderOf (modelDSucc m) = 2 * m := by
  let e : Fin m ⊕ Fin 1 ≃ Fin (m + 1) := finSumFinEquiv
  have he : orderOf (modelDSucc m) = orderOf (blockModelD m) :=
    (Matrix.reindexAlgEquiv ℤ ℤ e).toMulEquiv.orderOf_eq (blockModelD m)
  rw [he]
  refine (orderOf_eq_iff (by omega)).2 ⟨?_, fun k hk hpos h1 => ?_⟩
  · rw [blockModelD, Matrix.fromBlocks_diagonal_pow, pow_mul' (negCycleMatrix m),
      negCycleMatrix_pow_self hm, neg_one_sq, pow_mul (-1 : Matrix (Fin 1) (Fin 1) ℤ),
      neg_one_sq, one_pow, Matrix.fromBlocks_one]
  · rw [blockModelD, Matrix.fromBlocks_diagonal_pow, ← Matrix.fromBlocks_one,
      Matrix.fromBlocks_inj] at h1
    exact pow_ne_one_of_lt_orderOf hpos.ne' (by rwa [orderOf_negCycleMatrix hm]) h1.1

/-- **The characteristic polynomial of the `Dₙ` Coxeter element is `(X^{n-1} + 1)(X + 1)`**
(`2 ≤ n`). -/
theorem charpoly_coxeterElement_D {n : ℕ} (hn : 2 ≤ n) :
    (coxeterElement (CartanMatrix.D n)).charpoly = (X ^ (n - 1) + 1) * (X + 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hm : 1 ≤ m := by omega
  have h := Matrix.charpoly_eq_of_mul_eq_mul (by rw [det_matPD hn]; norm_num)
    (matPD_mul_coxeterElement_D_succ hm).symm
  simpa using h.symm.trans (charpoly_modelDSucc hm)

/-- **The Coxeter number of `Dₙ` is `2 (n - 1)`** (`2 ≤ n`): the Coxeter element of type `Dₙ` has
order `2 (n - 1)`. -/
theorem orderOf_coxeterElement_D {n : ℕ} (hn : 2 ≤ n) :
    orderOf (coxeterElement (CartanMatrix.D n)) = 2 * (n - 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hm : 1 ≤ m := by omega
  have h := Matrix.orderOf_eq_of_mul_eq_mul (by rw [det_matPD hn]; norm_num)
    (matPD_mul_coxeterElement_D_succ hm).symm
  simpa using h.symm.trans (orderOf_modelDSucc hm)

end TauCeti.Coxeter

end
