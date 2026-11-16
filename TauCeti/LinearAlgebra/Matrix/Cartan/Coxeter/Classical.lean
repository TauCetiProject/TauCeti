/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Data.List.OneDegenerateOrder
public import TauCeti.LinearAlgebra.Matrix.Cartan.Coxeter.Basic
public import TauCeti.LinearAlgebra.Matrix.NegacyclicShift
public import TauCeti.LinearAlgebra.RootSystem.Classical.TypeB
public import TauCeti.LinearAlgebra.RootSystem.Classical.TypeD
import Mathlib.Data.List.Sort
import Mathlib.Data.Matrix.Block
import TauCeti.LinearAlgebra.Matrix.Adjugate.Basic
import TauCeti.LinearAlgebra.Matrix.OneSubVecMulVec

/-!
# Coxeter elements of the classical types `B`, `C` and `D`

The Coxeter element `c = s₀ s₁ ⋯ s_{n-1}` of the classical Cartan matrices, in Mathlib's
numbering, has the following order `h`, the Coxeter number, and characteristic polynomial on the
simple roots:

| type | `h` | characteristic polynomial |
|---|---|---|
| `Bₙ`, `Cₙ` (`n ≥ 1`) | `2n` | `X ^ n + 1` |
| `Dₙ` (`n ≥ 4`) | `2n - 2` | `(X ^ (n - 1) + 1) (X + 1)` |

Over `ℂ` the roots of these polynomials are the `exp (2πi e / h)` with `e = 1, 3, …, 2n - 1` in
types `B` and `C`, and `e = 1, 3, …, 2n - 3` together with `e = n - 1` in type `D`; this file
computes the polynomials, not their roots.

Unlike the exceptional types, the rank is a variable, so the matrices cannot be evaluated by the
kernel. Instead the computation moves to the classical lattice `ℤ ^ n` with standard basis
`e₀, …, e_{n-1}`, where the simple roots of type `Bₙ` are `eᵢ - eᵢ₊₁` and `e_{n-1}`, with coroots
`eᵢ - eᵢ₊₁` and `2 e_{n-1}` (`TauCeti.DynkinType.typeBSimpleRoot`,
`TauCeti.DynkinType.typeBSimpleCoroot`). The roots and coroots of `Cₙ` are the coroots and roots
of `Bₙ`, and those of `Dₙ` are `eᵢ - eᵢ₊₁` and `e_{n-2} + e_{n-1}`
(`TauCeti.DynkinType.typeDSimpleRoot`). There the simple reflections are signed permutations of
the coordinates, and their product, in the numbering order, is

* in types `B` and `C`, the negacyclic shift `eⱼ ↦ eⱼ₊₁`, `e_{n-1} ↦ -e₀`
  (`TauCeti.negacyclicShift`), the companion matrix of `X ^ n + 1`;
* in type `D`, the negacyclic shift of `e₀, …, e_{n-2}` together with `e_{n-1} ↦ -e_{n-1}`.

The matrix whose columns are the simple roots has nonzero determinant and intertwines this
product with the Coxeter element (`Matrix.prod_map_one_sub_vecMulVec_mul_eq_mul_coxeterElement`),
so the two have the same order and characteristic polynomial.

## Main results

* `TauCeti.Coxeter.orderOf_coxeterElement_B`, `TauCeti.Coxeter.charpoly_coxeterElement_B` and
  their `C` counterparts: the Coxeter element of `Bₙ` or `Cₙ` has order `2n` and characteristic
  polynomial `X ^ n + 1`.
* `TauCeti.Coxeter.orderOf_coxeterElement_D`, `TauCeti.Coxeter.charpoly_coxeterElement_D`: the
  Coxeter element of `Dₙ` has order `2n - 2` and characteristic polynomial
  `(X ^ (n - 1) + 1) (X + 1)`.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Ch. V, §6, and Plates II--IV.
* J. E. Humphreys, *Reflection Groups and Coxeter Groups*, Cambridge University Press (1990),
  §§ 3.16–3.18.
-/

public section

open Matrix Polynomial

namespace TauCeti.Coxeter

open DynkinType

variable {n : ℕ}

/-! ### The product of the ambient reflections -/

/-- The product, in order, of the ambient reflections in the first `m` chain roots
`e₀ - e₁, …, e_{m-1} - eₘ` is the cycle `e₀ ↦ e₁ ↦ ⋯ ↦ eₘ ↦ e₀`. -/
private theorem prod_take_map_finRange_apply {T : Fin n → Matrix (Fin n) (Fin n) ℤ}
    (hT : ∀ (i : Fin n) (h : (i : ℕ) + 1 < n),
      T i = 1 - vecMulVec (Pi.single i 1 - Pi.single ⟨(i : ℕ) + 1, h⟩ 1)
        (Pi.single i 1 - Pi.single ⟨(i : ℕ) + 1, h⟩ 1))
    {m : ℕ} (hm : m < n) (k j : Fin n) :
    (((List.finRange n).map T).take m).prod k j =
      if (j : ℕ) < m then (if (k : ℕ) = j + 1 then 1 else 0)
      else if (j : ℕ) = m then (if (k : ℕ) = 0 then 1 else 0)
      else if (k : ℕ) = j then 1 else 0 := by
  induction m generalizing k j with
  | zero =>
    simp only [List.take_zero, List.prod_nil, Matrix.one_apply, Fin.ext_iff]
    split_ifs <;> omega
  | succ m ih =>
    rw [List.prod_take_succ _ _ (by simp; omega), List.getElem_map, List.getElem_finRange,
      hT _ (by simp; omega), mul_one_sub_vecMulVec_apply]
    simp [ih (by omega), mulVec_sub, Pi.single_apply, Fin.ext_iff]
    grind

/-- The cycle `e₀ ↦ e₁ ↦ ⋯ ↦ eₘ ↦ e₀` of `prod_take_map_finRange_apply` shifts the coordinates of
a vector cyclically: coordinate `k` of the image is coordinate `k - 1`, and coordinate `0` is the
last one. -/
private theorem prod_take_map_finRange_mulVec_apply {m : ℕ}
    {T : Fin (m + 1) → Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ}
    (hT : ∀ (i : Fin (m + 1)) (h : (i : ℕ) + 1 < m + 1),
      T i = 1 - vecMulVec (Pi.single i 1 - Pi.single ⟨(i : ℕ) + 1, h⟩ 1)
        (Pi.single i 1 - Pi.single ⟨(i : ℕ) + 1, h⟩ 1))
    (u : Fin (m + 1) → ℤ) (k : Fin (m + 1)) :
    ((((List.finRange (m + 1)).map T).take m).prod *ᵥ u) k =
      if (k : ℕ) = 0 then u (Fin.last m) else u ⟨k - 1, by omega⟩ := by
  have hP := prod_take_map_finRange_apply hT (Nat.lt_succ_self m)
  -- Row `k` of the cycle has a single nonzero entry, a `1` in column `k - 1` (cyclically).
  let l₀ : Fin (m + 1) := if (k : ℕ) = 0 then Fin.last m else ⟨k - 1, by omega⟩
  have hrow (l : Fin (m + 1)) :
      (((List.finRange (m + 1)).map T).take m).prod k l = if l = l₀ then 1 else 0 := by
    simp only [hP, l₀, Fin.ext_iff]
    split_ifs <;> grind
  simp only [mulVec, dotProduct, hrow, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true, l₀]
  split_ifs <;> rfl

/-- If the last of `m + 1` ambient reflections is `1 - vecMulVec u v` and the others are the
reflections in the chain roots, then the product is the cycle `e₀ ↦ e₁ ↦ ⋯ ↦ eₘ ↦ e₀` of
`prod_take_map_finRange_apply` followed by `1 - vecMulVec u v`. -/
private theorem prod_map_finRange_apply {m : ℕ}
    {T : Fin (m + 1) → Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ}
    (hT : ∀ (i : Fin (m + 1)) (h : (i : ℕ) + 1 < m + 1),
      T i = 1 - vecMulVec (Pi.single i 1 - Pi.single ⟨(i : ℕ) + 1, h⟩ 1)
        (Pi.single i 1 - Pi.single ⟨(i : ℕ) + 1, h⟩ 1))
    {u v : Fin (m + 1) → ℤ} (hlast : T (Fin.last m) = 1 - vecMulVec u v) (k j : Fin (m + 1)) :
    ((List.finRange (m + 1)).map T).prod k j =
      (if (j : ℕ) < m then (if (k : ℕ) = j + 1 then 1 else 0) else if (k : ℕ) = 0 then 1 else 0) -
        (if (k : ℕ) = 0 then u (Fin.last m) else u ⟨k - 1, by omega⟩) * v j := by
  have hmap : ((List.finRange (m + 1)).map T)[m]'(by simp) = T (Fin.last m) := by
    rw [List.getElem_map, List.getElem_finRange]
    exact congrArg T (Fin.ext (Fin.val_last m).symm)
  rw [← List.take_length (l := (List.finRange (m + 1)).map T), List.length_map,
    List.length_finRange, List.prod_take_succ _ _ (by simp), hmap, hlast,
    mul_one_sub_vecMulVec_apply, prod_take_map_finRange_mulVec_apply hT,
    prod_take_map_finRange_apply hT (Nat.lt_succ_self m)]
  congr 1
  split_ifs <;> omega

/-- The product, in order, of the ambient reflections of the simple roots of type `Bₙ` is the
negacyclic shift. -/
private theorem prod_map_typeB (hn : 0 < n) :
    ((List.finRange n).map fun i =>
      1 - vecMulVec (typeBSimpleRoot n i) (typeBSimpleCoroot n i)).prod = negacyclicShift ℤ n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  ext k j
  rw [prod_map_finRange_apply (fun i h => by simp [h]) (by
      rw [typeBSimpleRoot_of_not_add_one_lt (by simp),
        typeBSimpleCoroot_of_not_add_one_lt (by simp)]),
    negacyclicShift_apply]
  simp only [Pi.single_apply, Fin.ext_iff, Fin.val_last]
  grind

/-! ### One-degenerate orders of the classical diagrams -/

/-- The numbering order is a one-degenerate order of the Dynkin diagram of type `Bₙ`. -/
theorem isOneDegenerateOrder_B (n : ℕ) :
    List.IsOneDegenerateOrder (fun i j : Fin n => CartanMatrix.B n i j ≠ 0) (List.finRange n) :=
  List.isOneDegenerateOrder_of_pairwise (List.sortedLT_finRange n).pairwise fun x y z hx hy => by
    simp only [CartanMatrix.B, of_apply, Fin.ext_iff]
    split_ifs <;> grind

/-- The numbering order is a one-degenerate order of the Dynkin diagram of type `Cₙ`. -/
theorem isOneDegenerateOrder_C (n : ℕ) :
    List.IsOneDegenerateOrder (fun i j : Fin n => CartanMatrix.C n i j ≠ 0) (List.finRange n) :=
  List.isOneDegenerateOrder_of_pairwise (List.sortedLT_finRange n).pairwise fun x y z hx hy => by
    simp only [CartanMatrix.C, of_apply, Fin.ext_iff]
    split_ifs <;> grind

/-- The numbering order is a one-degenerate order of the Dynkin diagram of type `Dₙ`. -/
theorem isOneDegenerateOrder_D (n : ℕ) :
    List.IsOneDegenerateOrder (fun i j : Fin n => CartanMatrix.D n i j ≠ 0) (List.finRange n) :=
  List.isOneDegenerateOrder_of_pairwise (List.sortedLT_finRange n).pairwise fun x y z hx hy => by
    simp only [CartanMatrix.D, of_apply, Fin.ext_iff]
    split_ifs <;> grind

/-! ### Types `B` and `C` -/

/-- The matrix with the simple roots of type `Bₙ` as columns has nonzero determinant. -/
private theorem det_typeBSimpleRoot_ne_zero : (Matrix.of (typeBSimpleRoot n))ᵀ.det ≠ 0 := by
  rw [det_transpose, det_typeBSimpleRoot_eq_one]
  exact one_ne_zero

/-- The matrix with the simple coroots of type `Bₙ` as columns has nonzero determinant. -/
private theorem det_typeBSimpleCoroot_ne_zero (hn : 0 < n) :
    (Matrix.of (typeBSimpleCoroot n))ᵀ.det ≠ 0 := by
  rw [det_transpose, det_typeBSimpleCoroot_eq_two hn]
  exact two_ne_zero

/-- The roots realize `CartanMatrix.B n` against the coroots, so the negacyclic shift is
intertwined with its Coxeter element. -/
private theorem negacyclicShift_mul_typeBSimpleRoot (hn : 0 < n) :
    negacyclicShift ℤ n * (Matrix.of (typeBSimpleRoot n))ᵀ =
      (Matrix.of (typeBSimpleRoot n))ᵀ * coxeterElement (CartanMatrix.B n) := by
  have key := prod_map_one_sub_vecMulVec_mul_eq_mul_coxeterElement
    (Matrix.of (typeBSimpleRoot n))ᵀ (Matrix.of (typeBSimpleCoroot n))ᵀ
  simp only [col_transpose, row_of, transpose_transpose,
    typeBSimpleRoot_mul_transpose_typeBSimpleCoroot] at key
  rwa [← prod_map_typeB hn]

/-- The coroots of type `Bₙ` realize `CartanMatrix.C n` against the roots, so the negacyclic shift
is intertwined with the Coxeter element of type `Cₙ`. -/
private theorem negacyclicShift_mul_typeBSimpleCoroot (hn : 0 < n) :
    negacyclicShift ℤ n * (Matrix.of (typeBSimpleCoroot n))ᵀ =
      (Matrix.of (typeBSimpleCoroot n))ᵀ * coxeterElement (CartanMatrix.C n) := by
  have key := prod_map_one_sub_vecMulVec_mul_eq_mul_coxeterElement
    (Matrix.of (typeBSimpleCoroot n))ᵀ (Matrix.of (typeBSimpleRoot n))ᵀ
  simp only [col_transpose, row_of, transpose_transpose,
    vecMulVec_typeBSimpleCoroot_typeBSimpleRoot] at key
  rwa [typeBSimpleCoroot_mul_transpose_typeBSimpleRoot, prod_map_typeB hn] at key

/-- **The Coxeter number of `Bₙ` is `2n`**: the Coxeter element has order `2n`. -/
theorem orderOf_coxeterElement_B (hn : 0 < n) :
    orderOf (coxeterElement (CartanMatrix.B n)) = 2 * n := by
  rw [← orderOf_eq_of_mul_eq_mul (det_typeBSimpleRoot_ne_zero)
    (negacyclicShift_mul_typeBSimpleRoot hn), orderOf_negacyclicShift hn]

/-- The characteristic polynomial of the Coxeter element of `Bₙ` is `X ^ n + 1`. -/
theorem charpoly_coxeterElement_B (hn : 0 < n) :
    (coxeterElement (CartanMatrix.B n)).charpoly = X ^ n + 1 := by
  rw [← charpoly_eq_of_mul_eq_mul (det_typeBSimpleRoot_ne_zero)
    (negacyclicShift_mul_typeBSimpleRoot hn), charpoly_negacyclicShift hn]

/-- **The Coxeter number of `Cₙ` is `2n`**: the Coxeter element has order `2n`. -/
theorem orderOf_coxeterElement_C (hn : 0 < n) :
    orderOf (coxeterElement (CartanMatrix.C n)) = 2 * n := by
  rw [← orderOf_eq_of_mul_eq_mul (det_typeBSimpleCoroot_ne_zero hn)
    (negacyclicShift_mul_typeBSimpleCoroot hn), orderOf_negacyclicShift hn]

/-- The characteristic polynomial of the Coxeter element of `Cₙ` is `X ^ n + 1`. -/
theorem charpoly_coxeterElement_C (hn : 0 < n) :
    (coxeterElement (CartanMatrix.C n)).charpoly = X ^ n + 1 := by
  rw [← charpoly_eq_of_mul_eq_mul (det_typeBSimpleCoroot_ne_zero hn)
    (negacyclicShift_mul_typeBSimpleCoroot hn), charpoly_negacyclicShift hn]

/-! ### Type `D` -/

/-- The product, in order, of the ambient reflections of the simple roots of type `Dₙ` is the
negacyclic shift of `e₀, …, e_{n-2}` together with `e_{n-1} ↦ -e_{n-1}`. -/
private theorem prod_map_typeD_apply (hn : 4 ≤ n) (k j : Fin n) :
    ((List.finRange n).map fun i =>
      1 - vecMulVec (typeDSimpleRoot n hn i) (typeDSimpleRoot n hn i)).prod k j =
      if (j : ℕ) + 2 < n then (if (k : ℕ) = j + 1 then 1 else 0)
      else if (j : ℕ) + 2 = n then (if (k : ℕ) = 0 then -1 else 0)
      else if (k : ℕ) + 1 = n then -1 else 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hT : ∀ (i : Fin (m + 1)) (h : (i : ℕ) + 1 < m + 1), 1 - vecMulVec
      (typeDSimpleRoot (m + 1) hn i) (typeDSimpleRoot (m + 1) hn i) =
        1 - vecMulVec (Pi.single i 1 - Pi.single ⟨(i : ℕ) + 1, h⟩ 1)
          (Pi.single i 1 - Pi.single ⟨(i : ℕ) + 1, h⟩ 1) := fun i h => by
    rw [typeDSimpleRoot_of_add_one_lt hn h]
  rw [prod_map_finRange_apply hT (by rw [typeDSimpleRoot_of_not_add_one_lt hn (by simp)])]
  simp only [Pi.add_apply, Pi.single_apply, Fin.ext_iff, Fin.val_last]
  grind

/-- The product of the ambient reflections of type `Dₙ₊₁` is block diagonal, with the negacyclic
shift of size `n` and the `1 × 1` block `-1`. -/
private theorem prod_map_typeD (hn : 4 ≤ n + 1) :
    ((List.finRange (n + 1)).map fun i =>
      1 - vecMulVec (typeDSimpleRoot (n + 1) hn i) (typeDSimpleRoot (n + 1) hn i)).prod =
      reindex finSumFinEquiv finSumFinEquiv (fromBlocks (negacyclicShift ℤ n) 0 0 (-1)) := by
  ext k j
  rw [prod_map_typeD_apply, reindex_apply, submatrix_apply]
  induction k using Fin.addCases <;> induction j using Fin.addCases <;>
    simp [fromBlocks, negacyclicShift_apply, Subsingleton.elim _ (0 : Fin 1)] <;>
    omega

/-- The block-diagonal matrix with blocks the negacyclic shift of size `n` and `-1` has order
`2 * n`. -/
private theorem orderOf_fromBlocks_negacyclicShift (hn : 0 < n) :
    orderOf (fromBlocks (negacyclicShift ℤ n) 0 0 (-1 : Matrix (Fin 1) (Fin 1) ℤ)) = 2 * n := by
  refine (orderOf_eq_iff (by omega)).2 ⟨?_, fun d hd hd0 h => ?_⟩
  · rw [fromBlocks_diagonal_pow, pow_mul', negacyclicShift_pow_self, pow_mul]
    simp
  · rw [fromBlocks_diagonal_pow, ← fromBlocks_one, fromBlocks_inj] at h
    exact pow_ne_one_of_lt_orderOf hd0.ne' (by rwa [orderOf_negacyclicShift hn]) h.1

/-- The matrix with the simple roots of type `Dₙ` as columns realizes `CartanMatrix.D n` against
itself, so it intertwines the product of the ambient reflections with the Coxeter element. -/
private theorem prod_map_typeD_mul (hn : 4 ≤ n) :
    ((List.finRange n).map fun i =>
      1 - vecMulVec (typeDSimpleRoot n hn i) (typeDSimpleRoot n hn i)).prod *
        (Matrix.of (typeDSimpleRoot n hn))ᵀ =
      (Matrix.of (typeDSimpleRoot n hn))ᵀ * coxeterElement (CartanMatrix.D n) := by
  have key := prod_map_one_sub_vecMulVec_mul_eq_mul_coxeterElement
    (Matrix.of (typeDSimpleRoot n hn))ᵀ (Matrix.of (typeDSimpleRoot n hn))ᵀ
  simpa only [col_transpose, row_of, transpose_transpose,
    typeDSimpleRoot_mul_transpose_self] using key

/-- The matrix with the simple roots of type `Dₙ` as columns has nonzero determinant. -/
private theorem det_typeDSimpleRoot_ne_zero (hn : 4 ≤ n) :
    (Matrix.of (typeDSimpleRoot n hn))ᵀ.det ≠ 0 := by
  rw [det_transpose, det_typeDSimpleRoot_eq_two]
  exact two_ne_zero

/-- **The Coxeter number of `Dₙ` is `2n - 2`**: the Coxeter element has order `2 (n - 1)`. -/
theorem orderOf_coxeterElement_D (hn : 4 ≤ n) :
    orderOf (coxeterElement (CartanMatrix.D n)) = 2 * (n - 1) := by
  rw [← orderOf_eq_of_mul_eq_mul (det_typeDSimpleRoot_ne_zero hn) (prod_map_typeD_mul hn)]
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [prod_map_typeD, ← coe_reindexAlgEquiv ℤ ℤ, Nat.add_sub_cancel,
    ← orderOf_fromBlocks_negacyclicShift (by omega)]
  exact MulEquiv.orderOf_eq (reindexAlgEquiv ℤ ℤ finSumFinEquiv).toMulEquiv _

/-- The characteristic polynomial of the Coxeter element of `Dₙ` is `(X ^ (n - 1) + 1) (X + 1)`. -/
theorem charpoly_coxeterElement_D (hn : 4 ≤ n) :
    (coxeterElement (CartanMatrix.D n)).charpoly = (X ^ (n - 1) + 1) * (X + 1) := by
  rw [← charpoly_eq_of_mul_eq_mul (det_typeDSimpleRoot_ne_zero hn) (prod_map_typeD_mul hn)]
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [prod_map_typeD, charpoly_reindex, charpoly_fromBlocks_zero₁₂,
    charpoly_negacyclicShift (by omega), Nat.add_sub_cancel]
  congr 1
  simp [charpoly, charmatrix, det_unique]

end TauCeti.Coxeter
