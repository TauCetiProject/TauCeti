/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Data.List.OneDegenerateOrder
public import TauCeti.LinearAlgebra.Matrix.Cartan.Coxeter.Basic
public import TauCeti.LinearAlgebra.Matrix.NegacyclicShift
public import TauCeti.LinearAlgebra.RootSystem.ClassicalTypeD
import Mathlib.Data.List.Sort
import Mathlib.Data.Matrix.Block
import TauCeti.GroupTheory.OrderOfElement.Basic
import TauCeti.LinearAlgebra.Matrix.Cartan.Classical

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
`eᵢ - eᵢ₊₁` and `2 e_{n-1}`. The roots and coroots of `Cₙ` are the coroots and roots of `Bₙ`, and
those of `Dₙ` are `eᵢ - eᵢ₊₁` and `e_{n-2} + e_{n-1}`
(`TauCeti.DynkinType.typeDSimpleRoot`). There the simple reflections are signed permutations of
the coordinates, and their product, in the numbering order, is

* in types `B` and `C`, the negacyclic shift `eⱼ ↦ eⱼ₊₁`, `e_{n-1} ↦ -e₀`
  (`TauCeti.negacyclicShift`), the companion matrix of `X ^ n + 1`;
* in type `D`, the negacyclic shift of `e₀, …, e_{n-2}` together with `e_{n-1} ↦ -e_{n-1}`.

The matrix whose columns are the simple roots has nonzero determinant and intertwines this
product with the Coxeter element (`Matrix.prod_map_one_sub_vecMulVec_mul_eq_mul_coxeterElement`),
so the two have the same order and characteristic polynomial.

## Main definitions

* `TauCeti.DynkinType.typeBSimpleRoot`, `TauCeti.DynkinType.typeBSimpleCoroot`: the simple roots
  and coroots of type `Bₙ` in classical coordinates.

## Main results

* `TauCeti.DynkinType.typeBSimpleRoot_dotProduct_typeBSimpleCoroot`: they pair to the Cartan
  matrix `CartanMatrix.B n`.
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

namespace TauCeti.DynkinType

variable {n : ℕ}

/-! ### The simple roots and coroots of type `Bₙ` -/

/-- The Bourbaki-numbered simple roots of type `Bₙ` in classical orthogonal coordinates: the
chain roots `eᵢ - eᵢ₊₁` and the short root `e_{n-1}`. -/
def typeBSimpleRoot (n : ℕ) (i : Fin n) : Fin n → ℤ :=
  if h : (i : ℕ) + 1 < n then Pi.single i 1 - Pi.single ⟨(i : ℕ) + 1, h⟩ 1 else Pi.single i 1

/-- The simple coroots of type `Bₙ` in classical orthogonal coordinates: the chain coroots
`eᵢ - eᵢ₊₁` and the coroot `2 e_{n-1}` of the short root. They are the simple roots of type
`Cₙ`. -/
def typeBSimpleCoroot (n : ℕ) (i : Fin n) : Fin n → ℤ :=
  if h : (i : ℕ) + 1 < n then Pi.single i 1 - Pi.single ⟨(i : ℕ) + 1, h⟩ 1 else Pi.single i 2

/-- The chain simple roots of type `Bₙ` are `eᵢ - eᵢ₊₁`. -/
@[simp] theorem typeBSimpleRoot_of_add_one_lt {i : Fin n} (hi : (i : ℕ) + 1 < n) :
    typeBSimpleRoot n i = Pi.single i 1 - Pi.single ⟨(i : ℕ) + 1, hi⟩ 1 :=
  dite_eq_left hi

/-- The last simple root of type `Bₙ` is the short root `e_{n-1}`. -/
@[simp] theorem typeBSimpleRoot_of_not_add_one_lt {i : Fin n} (hi : ¬(i : ℕ) + 1 < n) :
    typeBSimpleRoot n i = Pi.single i 1 :=
  dite_eq_right hi

/-- The chain simple coroots of type `Bₙ` are `eᵢ - eᵢ₊₁`. -/
@[simp] theorem typeBSimpleCoroot_of_add_one_lt {i : Fin n} (hi : (i : ℕ) + 1 < n) :
    typeBSimpleCoroot n i = Pi.single i 1 - Pi.single ⟨(i : ℕ) + 1, hi⟩ 1 :=
  dite_eq_left hi

/-- The last simple coroot of type `Bₙ` is `2 e_{n-1}`. -/
@[simp] theorem typeBSimpleCoroot_of_not_add_one_lt {i : Fin n} (hi : ¬(i : ℕ) + 1 < n) :
    typeBSimpleCoroot n i = Pi.single i 2 :=
  dite_eq_right hi

/-- **The simple roots and coroots of type `Bₙ` pair to the Cartan matrix**:
`⟨αᵢ, αⱼ^∨⟩ = CartanMatrix.B n i j`. -/
@[simp]
theorem typeBSimpleRoot_dotProduct_typeBSimpleCoroot (i j : Fin n) :
    typeBSimpleRoot n i ⬝ᵥ typeBSimpleCoroot n j = CartanMatrix.B n i j := by
  by_cases hi : (i : ℕ) + 1 < n <;> by_cases hj : (j : ℕ) + 1 < n <;>
    simp [hi, hj, Pi.single_apply, Fin.ext_iff, CartanMatrix.B] <;> grind

/-- The Cartan matrix of type `Bₙ` is the matrix of pairings of the simple roots with the simple
coroots. -/
theorem typeBSimpleRoot_mul_transpose_typeBSimpleCoroot :
    Matrix.of (typeBSimpleRoot n) * (Matrix.of (typeBSimpleCoroot n))ᵀ = CartanMatrix.B n := by
  ext i j
  rw [Matrix.mul_apply, ← typeBSimpleRoot_dotProduct_typeBSimpleCoroot i j]
  simp [dotProduct]

/-- The ambient reflections in a simple root of type `Bₙ` and in its coroot coincide:
`vecMulVec α^∨ α = vecMulVec α α^∨`. This is why the Weyl groups of types `Bₙ` and `Cₙ` act on
`ℤ ^ n` by the same signed permutations. -/
theorem vecMulVec_typeBSimpleCoroot_typeBSimpleRoot (i : Fin n) :
    vecMulVec (typeBSimpleCoroot n i) (typeBSimpleRoot n i) =
      vecMulVec (typeBSimpleRoot n i) (typeBSimpleCoroot n i) := by
  by_cases hi : (i : ℕ) + 1 < n
  · simp [hi]
  · ext k l
    simp only [hi, not_false_eq_true, typeBSimpleCoroot_of_not_add_one_lt,
      typeBSimpleRoot_of_not_add_one_lt, vecMulVec_apply, Pi.single_apply]
    split_ifs <;> simp

end TauCeti.DynkinType

namespace TauCeti.Coxeter

open DynkinType

variable {n : ℕ}

/-! ### The product of the ambient reflections -/

/-- The product, in order, of the ambient reflections in the first `m` chain roots
`e₀ - e₁, …, e_{m-1} - eₘ` is the cycle `e₀ ↦ e₁ ↦ ⋯ ↦ eₘ ↦ e₀`. -/
private theorem prod_map_take_finRange_apply {T : Fin n → Matrix (Fin n) (Fin n) ℤ}
    (hT : ∀ (i : Fin n) (h : (i : ℕ) + 1 < n),
      T i = 1 - vecMulVec (Pi.single i 1 - Pi.single ⟨(i : ℕ) + 1, h⟩ 1)
        (Pi.single i 1 - Pi.single ⟨(i : ℕ) + 1, h⟩ 1))
    {m : ℕ} (hm : m < n) (k j : Fin n) :
    (((List.finRange n).take m).map T).prod k j =
      if (j : ℕ) < m then (if (k : ℕ) = j + 1 then 1 else 0)
      else if (j : ℕ) = m then (if (k : ℕ) = 0 then 1 else 0)
      else if (k : ℕ) = j then 1 else 0 := by
  induction m generalizing k j with
  | zero =>
    simp only [List.take_zero, List.map_nil, List.prod_nil, Matrix.one_apply, Fin.ext_iff]
    split_ifs <;> first | rfl | omega
  | succ m ih =>
    rw [List.take_add_one, List.getElem?_eq_getElem (by simp; omega)]
    simp only [List.getElem_finRange, Option.toList_some, List.map_append, List.map_cons,
      List.map_nil, List.prod_append, List.prod_cons, List.prod_nil, Matrix.mul_one]
    rw [hT _ (by simp; omega), Matrix.mul_sub, Matrix.mul_one, mul_vecMulVec, Matrix.sub_apply,
      vecMulVec_apply, mulVec_sub, mulVec_single_one, mulVec_single_one, Pi.sub_apply,
      col_apply, col_apply, Pi.sub_apply, ih (by omega), ih (by omega), ih (by omega)]
    simp only [Pi.single_apply, Fin.cast_mk, Fin.eq_mk_iff_val_eq, lt_self_iff_false,
      ite_false, ite_true, show ¬m + 1 < m by omega, show m + 1 ≠ m by omega]
    rcases lt_trichotomy (j : ℕ) m with hj | hj | hj
    · simp only [hj, ite_true, show (j : ℕ) ≠ m by omega, show (j : ℕ) ≠ m + 1 by omega,
        show (j : ℕ) < m + 1 by omega, ite_false, sub_zero, mul_zero]
    · simp only [hj, lt_self_iff_false, ite_true, ite_false, show m ≠ m + 1 by omega,
        show m < m + 1 by omega, sub_zero, mul_one]
      split_ifs <;> omega
    · rcases eq_or_lt_of_le (Nat.succ_le_of_lt hj) with hj' | hj'
      · simp only [← hj', show ¬(m + 1 < m) by omega, show (m + 1) ≠ m by omega,
          lt_self_iff_false, ite_true, ite_false, zero_sub, mul_neg, mul_one, sub_neg_eq_add]
        split_ifs <;> omega
      · simp only [show ¬(j : ℕ) < m by omega, show (j : ℕ) ≠ m by omega,
          show (j : ℕ) ≠ m + 1 by omega, show ¬(j : ℕ) < m + 1 by omega, ite_false, sub_zero,
          mul_zero]

/-- The list of indices `0, …, n - 1` ends with `n - 1`. -/
private theorem finRange_eq_take_append (hn : 0 < n) :
    List.finRange n = (List.finRange n).take (n - 1) ++ [⟨n - 1, by omega⟩] := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  nth_rewrite 1 [← List.take_length (l := List.finRange (m + 1))]
  rw [List.length_finRange, List.take_add_one, List.getElem?_eq_getElem (by simp)]
  simp

/-- The product, in order, of the ambient reflections of the simple roots of type `Bₙ` is the
negacyclic shift. -/
private theorem prod_map_typeB (hn : 0 < n) :
    ((List.finRange n).map fun i =>
      1 - vecMulVec (typeBSimpleRoot n i) (typeBSimpleCoroot n i)).prod = negacyclicShift ℤ n := by
  rw [finRange_eq_take_append hn, List.map_append, List.prod_append]
  ext k j
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, Matrix.mul_one]
  rw [typeBSimpleRoot_of_not_add_one_lt (by simp; omega),
    typeBSimpleCoroot_of_not_add_one_lt (by simp; omega), Matrix.mul_sub, Matrix.mul_one,
    mul_vecMulVec, Matrix.sub_apply, vecMulVec_apply, mulVec_single_one, col_apply,
    prod_map_take_finRange_apply (fun i h => by simp [h]) (by omega),
    prod_map_take_finRange_apply (fun i h => by simp [h]) (by omega), negacyclicShift_apply]
  simp only [Pi.single_apply, Fin.ext_iff]
  split_ifs <;> omega

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
private theorem det_typeBSimpleRoot_ne_zero (hn : 0 < n) :
    (Matrix.of (typeBSimpleRoot n))ᵀ.det ≠ 0 := by
  rw [det_transpose]
  intro h
  have := congrArg det (typeBSimpleRoot_mul_transpose_typeBSimpleCoroot (n := n))
  rw [det_mul, h, zero_mul, CartanMatrix.B_det hn] at this
  exact two_ne_zero this.symm

/-- The matrix with the simple coroots of type `Bₙ` as columns has nonzero determinant. -/
private theorem det_typeBSimpleCoroot_ne_zero (hn : 0 < n) :
    (Matrix.of (typeBSimpleCoroot n))ᵀ.det ≠ 0 := by
  intro h
  have := congrArg det (typeBSimpleRoot_mul_transpose_typeBSimpleCoroot (n := n))
  rw [det_mul, h, mul_zero, CartanMatrix.B_det hn] at this
  exact two_ne_zero this.symm

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
  rwa [show Matrix.of (typeBSimpleCoroot n) * (Matrix.of (typeBSimpleRoot n))ᵀ = CartanMatrix.C n by
    rw [← CartanMatrix.B_transpose, ← typeBSimpleRoot_mul_transpose_typeBSimpleCoroot,
      transpose_mul, transpose_transpose], prod_map_typeB hn] at key

/-- **The Coxeter number of `Bₙ` is `2n`**: the Coxeter element has order `2n`. -/
theorem orderOf_coxeterElement_B (hn : 0 < n) :
    orderOf (coxeterElement (CartanMatrix.B n)) = 2 * n := by
  rw [SemiconjBy.orderOf_eq_of_isRegular (negacyclicShift_mul_typeBSimpleRoot hn).symm
    (isRegular_of_isLeftRegular_det (IsRegular.of_ne_zero (det_typeBSimpleRoot_ne_zero hn)).left),
    orderOf_negacyclicShift hn]

/-- The characteristic polynomial of the Coxeter element of `Bₙ` is `X ^ n + 1`. -/
theorem charpoly_coxeterElement_B (hn : 0 < n) :
    (coxeterElement (CartanMatrix.B n)).charpoly = X ^ n + 1 := by
  rw [← charpoly_eq_of_mul_eq_mul (det_typeBSimpleRoot_ne_zero hn)
    (negacyclicShift_mul_typeBSimpleRoot hn), charpoly_negacyclicShift hn]

/-- **The Coxeter number of `Cₙ` is `2n`**: the Coxeter element has order `2n`. -/
theorem orderOf_coxeterElement_C (hn : 0 < n) :
    orderOf (coxeterElement (CartanMatrix.C n)) = 2 * n := by
  rw [SemiconjBy.orderOf_eq_of_isRegular (negacyclicShift_mul_typeBSimpleCoroot hn).symm
    (isRegular_of_isLeftRegular_det
      (IsRegular.of_ne_zero (det_typeBSimpleCoroot_ne_zero hn)).left),
    orderOf_negacyclicShift hn]

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
  rw [finRange_eq_take_append (by omega), List.map_append, List.prod_append]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, Matrix.mul_one]
  have hT : ∀ (i : Fin n) (h : (i : ℕ) + 1 < n), 1 - vecMulVec (typeDSimpleRoot n hn i)
      (typeDSimpleRoot n hn i) = 1 - vecMulVec (Pi.single i 1 - Pi.single ⟨(i : ℕ) + 1, h⟩ 1)
        (Pi.single i 1 - Pi.single ⟨(i : ℕ) + 1, h⟩ 1) := fun i h => by
    rw [typeDSimpleRoot_of_add_one_lt hn h]
  rw [typeDSimpleRoot_of_not_add_one_lt hn (by simp; omega), Matrix.mul_sub, Matrix.mul_one,
    mul_vecMulVec, Matrix.sub_apply, vecMulVec_apply, mulVec_add, mulVec_single_one,
    mulVec_single_one, Pi.add_apply, col_apply, col_apply,
    prod_map_take_finRange_apply hT (by omega), prod_map_take_finRange_apply hT (by omega),
    prod_map_take_finRange_apply hT (by omega)]
  simp only [Pi.add_apply, Pi.single_apply, Fin.eq_mk_iff_val_eq, show n - 2 < n - 1 by omega,
    lt_self_iff_false, ite_true, ite_false]
  obtain hj | hj | hj : (j : ℕ) + 2 < n ∨ (j : ℕ) + 2 = n ∨ (j : ℕ) + 1 = n := by omega
  · simp only [hj, ite_true, show (j : ℕ) < n - 1 by omega, show (j : ℕ) ≠ n - 2 by omega,
      show (j : ℕ) ≠ n - 1 by omega, ite_false, add_zero, mul_zero, sub_zero]
  all_goals split_ifs <;> omega

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
  · rw [fromBlocks_diagonal_pow, ← orderOf_negacyclicShift (R := ℤ) hn, pow_orderOf_eq_one,
      orderOf_negacyclicShift hn, pow_mul, neg_one_sq, one_pow, fromBlocks_one]
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
  rw [SemiconjBy.orderOf_eq_of_isRegular (prod_map_typeD_mul hn).symm
    (isRegular_of_isLeftRegular_det (IsRegular.of_ne_zero (det_typeDSimpleRoot_ne_zero hn)).left)]
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have := MulEquiv.orderOf_eq (reindexAlgEquiv ℤ ℤ (finSumFinEquiv (m := m) (n := 1))).toMulEquiv
    (fromBlocks (negacyclicShift ℤ m) 0 0 (-1))
  simp only [MulEquiv.coe_mk, AlgEquiv.toEquiv_eq_coe, toEquiv_reindexAlgEquiv,
    reindex_apply] at this
  rw [prod_map_typeD, reindex_apply, this, orderOf_fromBlocks_negacyclicShift (by omega),
    Nat.add_sub_cancel]

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
