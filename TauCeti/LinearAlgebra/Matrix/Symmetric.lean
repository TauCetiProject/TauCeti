/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Even
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.Symmetric
public import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Algebra.Ring.Int.Parity
import Mathlib.Data.Sym.Card
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import TauCeti.Algebra.BigOperators.Finset.OffDiagonal

/-!
# Quadratic forms, idempotents, and the number of symmetric matrices

For a symmetric matrix `A` over a commutative ring, the quadratic form `x ↦ xᵀ A x` satisfies
the polarization identities `(x ± y)ᵀ A (x ± y) = xᵀ A x + yᵀ A y ± 2 xᵀ A y`.

For a symmetric integer matrix `A` and an integer vector `m`, the quadratic form
`mᵀ A m = ∑ᵢⱼ mᵢ mⱼ aᵢⱼ` agrees modulo two with `∑ᵢ mᵢ aᵢᵢ`: its off-diagonal part is even
because the summand is symmetric under swapping the indices, and `mᵢ² ≡ mᵢ` modulo two. In
particular `∑ᵢ mᵢ aᵢᵢ` is even whenever `mᵀ A m = 0`, for instance whenever `A m = 0`.

A symmetric idempotent matrix fixes each of its rows, since each row is also a column.

If a symmetric matrix over an ordered ring has nonpositive off-diagonal entries and constant row
sums `d` on a block `O`, the Laplacian identity
`∑_{i, i' ∈ O} A i i' (sᵢ - sᵢ')² = 2 (d ∑ sᵢ² - ∑_{i, i' ∈ O} sᵢ A i i' sᵢ')` bounds the quadratic
form on `O` below by `d ∑ sᵢ²`.

A symmetric matrix whose entries are divisible by `c` and whose diagonal entries are divisible by
`2 * c` is `c • (D + Dᵀ)`, the shape in which even forms enter Hensel-type arguments when `2` is
not a unit. The inverse of an invertible symmetric matrix with even diagonal has even diagonal.

A symmetric `n × n` matrix is determined by its entries on and above the diagonal, that is by a
function on the unordered pairs `Sym2 n`, so there are `#R ^ (n (n + 1) / 2)` of them.

## Main results

* `Matrix.IsSymm.add_dotProduct_mulVec_add` and `Matrix.IsSymm.sub_dotProduct_mulVec_sub`: the
  polarization identities for a symmetric matrix.
* `Matrix.IsSymm.even_sum_mul_diag_iff_even_dotProduct_mulVec`: if `A` is a symmetric integer
  matrix then `∑ᵢ mᵢ aᵢᵢ` is even if and only if `mᵀ A m` is.
* `Matrix.IsSymm.even_sum_mul_diag_of_dotProduct_mulVec_eq_zero`: if `A` is a symmetric integer
  matrix and `mᵀ A m = 0`, then `∑ᵢ mᵢ aᵢᵢ` is even.
* `Matrix.IsSymm.mulVec_row_of_isIdempotentElem`: a symmetric idempotent matrix fixes its rows.
* `Matrix.IsSymm.mul_sum_sq_le`: with nonpositive off-diagonal entries and constant row sums `d`
  on a block `O`, `d ∑_{i ∈ O} sᵢ² ≤ ∑_{i, i' ∈ O} sᵢ A i i' sᵢ'`.
* `Matrix.IsSymm.exists_eq_smul_add_transpose`: a symmetric matrix with entries divisible by `c`
  and diagonal entries divisible by `2 * c` is `c • (D + Dᵀ)`.
* `Matrix.IsSymm.two_dvd_inv_apply_self`: the inverse of an invertible symmetric matrix with even
  diagonal has even diagonal.
* `Matrix.natCard_isSymm`: the number of symmetric `n × n` matrices over `R` is
  `Nat.card R ^ (n + 1).choose 2`.
-/

public section

namespace Matrix

open Finset

/-- Expanding the quadratic form of a symmetric matrix at a sum. -/
theorem IsSymm.add_dotProduct_mulVec_add {ι R : Type*} [Fintype ι] [CommSemiring R]
    {A : Matrix ι ι R} (hA : A.IsSymm) (x y : ι → R) :
    (x + y) ⬝ᵥ A *ᵥ (x + y) = x ⬝ᵥ A *ᵥ x + y ⬝ᵥ A *ᵥ y + 2 * (x ⬝ᵥ A *ᵥ y) := by
  rw [mulVec_add, add_dotProduct, dotProduct_add, dotProduct_add,
    hA.dotProduct_mulVec_comm (x := y) (y := x)]
  ring

/-- Expanding the quadratic form of a symmetric matrix at a difference. -/
theorem IsSymm.sub_dotProduct_mulVec_sub {ι R : Type*} [Fintype ι] [CommRing R]
    {A : Matrix ι ι R} (hA : A.IsSymm) (x y : ι → R) :
    (x - y) ⬝ᵥ A *ᵥ (x - y) = x ⬝ᵥ A *ᵥ x + y ⬝ᵥ A *ᵥ y - 2 * (x ⬝ᵥ A *ᵥ y) := by
  rw [sub_eq_add_neg, hA.add_dotProduct_mulVec_add, mulVec_neg, neg_dotProduct, dotProduct_neg,
    dotProduct_neg, neg_neg]
  ring

/-- If `A` is a symmetric integer matrix and `m` is an integer vector, then `∑ᵢ mᵢ aᵢᵢ` has the
same parity as the quadratic form `mᵀ A m`. The individual terms `mᵢ aᵢᵢ` need not be even. -/
theorem IsSymm.even_sum_mul_diag_iff_even_dotProduct_mulVec {ι : Type*} [Fintype ι]
    {A : Matrix ι ι ℤ} (hA : A.IsSymm) (m : ι → ℤ) :
    Even (∑ i, m i * A i i) ↔ Even (m ⬝ᵥ A *ᵥ m) := by
  classical
  have hoff : Even (∑ i, ∑ j ∈ univ.erase i, m i * m j * A i j) :=
    univ.even_sum_sum_erase fun i _ j _ ↦ by rw [hA.apply i j]; ring
  have hcorr : Even (∑ i, (m i * m i * A i i - m i * A i i)) := by
    rw [even_iff_two_dvd]
    refine Finset.dvd_sum fun i _ ↦ ?_
    obtain ⟨c, hc⟩ := (Int.even_mul_pred_self (m i)).two_dvd
    exact ⟨c * A i i, by linear_combination A i i * hc⟩
  have htotal : m ⬝ᵥ A *ᵥ m = ∑ i, ∑ j, m i * m j * A i j := by
    simp only [dotProduct, mulVec, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ by ring
  -- Splitting off the diagonal, `mᵀ A m` is `∑ᵢ mᵢ aᵢᵢ` plus the two even sums above.
  have hsum : m ⬝ᵥ A *ᵥ m = (∑ i, m i * A i i) +
      ((∑ i, (m i * m i * A i i - m i * A i i)) +
        ∑ i, ∑ j ∈ univ.erase i, m i * m j * A i j) := by
    have hrow (i : ι) : ∑ j, m i * m j * A i j = m i * A i i +
        ((m i * m i * A i i - m i * A i i) + ∑ j ∈ univ.erase i, m i * m j * A i j) := by
      rw [← Finset.add_sum_erase univ (fun j ↦ m i * m j * A i j) (mem_univ i)]
      ring
    rw [htotal, Finset.sum_congr rfl fun i _ ↦ hrow i, Finset.sum_add_distrib,
      Finset.sum_add_distrib]
  rw [hsum, Int.even_add]
  exact ⟨fun h ↦ iff_of_true h (hcorr.add hoff), fun h ↦ h.mpr (hcorr.add hoff)⟩

/-- If `A` is a symmetric integer matrix and `m` is an integer vector with `mᵀ A m = 0`, then
`∑ᵢ mᵢ aᵢᵢ` is even. The individual terms `mᵢ aᵢᵢ` need not be even. -/
theorem IsSymm.even_sum_mul_diag_of_dotProduct_mulVec_eq_zero {ι : Type*} [Fintype ι]
    {A : Matrix ι ι ℤ} (hA : A.IsSymm) {m : ι → ℤ} (hm : m ⬝ᵥ A *ᵥ m = 0) :
    Even (∑ i, m i * A i i) :=
  (hA.even_sum_mul_diag_iff_even_dotProduct_mulVec m).2 (hm ▸ Even.zero)

/-- A symmetric idempotent matrix fixes each of its rows, since the row `A i` is also the column
`A *ᵥ Pi.single i 1`. -/
theorem IsSymm.mulVec_row_of_isIdempotentElem {ι R : Type*} [Fintype ι] [Semiring R]
    {A : Matrix ι ι R} (hS : A.IsSymm) (hI : IsIdempotentElem A) (i : ι) : A *ᵥ A i = A i := by
  classical
  have hcol : A *ᵥ Pi.single i 1 = A i := by
    ext j
    rw [mulVec_single_one, col_apply, hS.apply]
  rw [← hcol, mulVec_mulVec, hI.eq]

/-- **A Laplacian bound on a block with constant row sums.** If a symmetric matrix `A` over an
ordered commutative ring has nonpositive off-diagonal entries and constant row sums `d` on a
finite set `O` of indices, then `d ∑_{i ∈ O} sᵢ² ≤ ∑_{i, i' ∈ O} sᵢ A i i' sᵢ'`. Twice the
difference is `-∑_{i, i' ∈ O} A i i' (sᵢ - sᵢ')²`. -/
theorem IsSymm.mul_sum_sq_le {ι R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
    {A : Matrix ι ι R} (hA : A.IsSymm) (hoff : ∀ i j, i ≠ j → A i j ≤ 0) {O : Finset ι}
    {d : R} (hrow : ∀ i ∈ O, ∑ i' ∈ O, A i i' = d) (s : ι → R) :
    d * ∑ i ∈ O, s i ^ 2 ≤ ∑ i ∈ O, ∑ i' ∈ O, s i * A i i' * s i' := by
  have h1 : ∑ i ∈ O, ∑ i' ∈ O, A i i' * s i ^ 2 = d * ∑ i ∈ O, s i ^ 2 := by
    rw [mul_sum]
    exact sum_congr rfl fun i hi ↦ by rw [← sum_mul, hrow i hi]
  have h2 : ∑ i ∈ O, ∑ i' ∈ O, A i i' * s i' ^ 2 = d * ∑ i ∈ O, s i ^ 2 := by
    rw [sum_comm, mul_sum]
    refine sum_congr rfl fun i' hi' ↦ ?_
    rw [← sum_mul, ← hrow i' hi']
    exact congrArg (· * _) (sum_congr rfl fun i _ ↦ hA.apply i' i)
  have hexp : ∑ i ∈ O, ∑ i' ∈ O, A i i' * (s i - s i') ^ 2 =
      2 * (d * ∑ i ∈ O, s i ^ 2) - 2 * ∑ i ∈ O, ∑ i' ∈ O, s i * A i i' * s i' := by
    calc _ = ∑ i ∈ O, ∑ i' ∈ O,
          (A i i' * s i ^ 2 + A i i' * s i' ^ 2 - 2 * (s i * A i i' * s i')) :=
          sum_congr rfl fun i _ ↦ sum_congr rfl fun i' _ ↦ by ring
      _ = _ := by simp only [sum_sub_distrib, sum_add_distrib, ← mul_sum, h1, h2]; ring
  have hnonpos : ∑ i ∈ O, ∑ i' ∈ O, A i i' * (s i - s i') ^ 2 ≤ 0 :=
    sum_nonpos fun i _ ↦ sum_nonpos fun i' _ ↦ by
      rcases eq_or_ne i i' with rfl | h
      · simp
      · exact mul_nonpos_of_nonpos_of_nonneg (hoff i i' h) (sq_nonneg _)
  linarith

/-- A symmetric matrix all of whose entries are divisible by `c`, and whose diagonal entries are
divisible by `2 * c`, is `c • (D + Dᵀ)` for some matrix `D`. -/
theorem IsSymm.exists_eq_smul_add_transpose {n R : Type*} [CommRing R] {E : Matrix n n R}
    (hE : E.IsSymm) (c : R) (h₁ : ∀ i i', c ∣ E i i') (h₂ : ∀ i, 2 * c ∣ E i i) :
    ∃ D : Matrix n n R, E = c • (D + Dᵀ) := by
  let : LinearOrder n := IsWellOrder.linearOrder WellOrderingRel
  choose e he using h₁
  choose f hf using h₂
  refine ⟨Matrix.of fun i i' ↦ if i < i' then e i i' else if i = i' then f i else 0, ?_⟩
  ext i i'
  simp only [smul_apply, add_apply, transpose_apply, of_apply, smul_eq_mul]
  rcases lt_trichotomy i i' with h | rfl | h
  · simp [h, h.ne', not_lt_of_gt h, he]
  · simp [hf, mul_comm 2 c, mul_assoc, two_mul]
  · have hsymm := congrFun (congrFun hE.eq i) i'
    rw [transpose_apply] at hsymm
    simp [not_lt_of_gt h, h.ne', h, ← hsymm, he]

/-- The inverse of an invertible symmetric matrix with even diagonal has even diagonal. -/
theorem IsSymm.two_dvd_inv_apply_self {n R : Type*} [Fintype n] [DecidableEq n] [CommRing R]
    {U : Matrix n n R} (hU : U.IsSymm) (hdet : IsUnit U.det) (hd : ∀ i, 2 ∣ U i i) (i : n) :
    2 ∣ U⁻¹ i i := by
  obtain ⟨K, hK⟩ := hU.exists_eq_smul_add_transpose 1 (fun _ _ ↦ one_dvd _) (by simpa using hd)
  rw [one_smul] at hK
  have hinv : (U⁻¹)ᵀ = U⁻¹ := by rw [transpose_nonsing_inv, hU.eq]
  -- `U⁻¹ = U⁻¹ * U * U⁻¹ = W + Wᵀ` with `W = U⁻¹ * K * U⁻¹`.
  have : U⁻¹ = U⁻¹ * K * U⁻¹ + (U⁻¹ * K * U⁻¹)ᵀ := by
    rw [transpose_mul, transpose_mul, hinv, Matrix.mul_assoc, ← Matrix.mul_add,
      ← Matrix.add_mul, ← hK, mul_nonsing_inv _ hdet, Matrix.mul_one]
  rw [this, add_apply, transpose_apply, ← two_mul]
  exact dvd_mul_right _ _

/-- **The number of symmetric matrices**: a symmetric `n × n` matrix over `R` is a function on the
unordered pairs of indices, so there are `Nat.card R ^ (n + 1).choose 2` of them. -/
theorem natCard_isSymm (n R : Type*) [Fintype n] :
    Nat.card {M : Matrix n n R // M.IsSymm} = Nat.card R ^ (Fintype.card n + 1).choose 2 := by
  classical
  rw [← Sym2.card, ← Nat.card_eq_fintype_card, ← Nat.card_fun]
  refine Nat.card_congr <| (Equiv.subtypeEquiv (of.symm : Matrix n n R ≃ (n → n → R))
    fun M => ?_).trans (Sym2.lift (α := n) (β := R))
  rw [IsSymm.ext_iff]
  exact ⟨fun h a b => h b a, fun h a b => h b a⟩

end Matrix
