/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.Block

/-!
# Block `LDU` factorization

Let `M` be a square matrix over a commutative ring whose indices are ranked by a map `b` into a
linear order, so that the indices fall into consecutive blocks `{i | b i = c}`. A *block `LDU`
factorization* of `M` is an equation `M = L * D * U` in which `L` is block lower unitriangular,
`D` is block diagonal and `U` is block upper unitriangular for `b`. When `b` is injective the blocks
are single indices and this is the usual `LDU` factorization.

The *leading blocks* of `M` are its square blocks on the initial segments `{j | b j ≤ b i}`, and
their determinants are the *leading block minors*. This file proves that `M` has a block `LDU`
factorization with invertible middle factor exactly when every leading block minor is a unit, and
that this factorization is then unique. The leading blocks of `L * D * U` are the products of the
leading blocks of the factors, so its leading block minors are those of `D`; this is the
direction from a factorization to the minors. Conversely, if the leading blocks on the strict
initial segments `{j | b j < b i}` have unit determinants, row reduction by a block lower
unitriangular matrix makes `M` block upper triangular, the same reduction applied to the columns
makes it block lower triangular, and what is left in the middle is block diagonal. Uniqueness holds
because a matrix that is at once block lower triangular with identity diagonal blocks after a
block diagonal factor, and block upper triangular, is that block diagonal factor.

On points this describes the *big cell* of `GLₙ` attached to the ranking: the matrices whose
leading block minors are invertible are exactly the products of a block lower unitriangular, an
invertible block diagonal and a block upper unitriangular matrix, and the three factors are
unique. Ring homomorphisms preserve all three shapes (`Matrix.BlockUnitriangular.map` and
`Matrix.BlockTriangular.map`), so by uniqueness the factorization commutes with any change of the
coefficient ring. The leading blocks of a product `L * g * U` with `L` block lower triangular and
`U` block upper triangular are the products of the leading blocks of the three factors
(`Matrix.BlockTriangular.toSquareBlockProp_mul_of_toDual` and
`Matrix.BlockTriangular.toSquareBlockProp_mul`, in `TauCeti.LinearAlgebra.Matrix.Block`), which is
how membership in the big cell is read off a Bruhat normal form.

## Main definitions

* `Matrix.BlockUnitriangular`: block triangular with identity diagonal blocks, characterized by
  `Matrix.blockUnitriangular_iff`.

## Main results

* `Matrix.BlockUnitriangular.det_eq_one`, `Matrix.BlockUnitriangular.mul` and
  `Matrix.BlockUnitriangular.inv`: block unitriangular matrices have determinant one and are
  closed under products and inverses.
* `Matrix.mul_eq_of_blockUnitriangular_toDual`: a block diagonal matrix multiplied on the left by
  a block lower unitriangular matrix is unchanged once the product is block upper triangular.
* `Matrix.det_toSquareBlockProp_blockLDU`: the leading block minors of `L * D * U` are those of
  `D`.
* `Matrix.exists_blockUnitriangular_mul_blockTriangular`: block row reduction.
* `Matrix.exists_blockLDU`: a block `LDU` factorization exists when the leading blocks on the
  strict initial segments have unit determinants.
* `Matrix.eq_of_blockLDU_eq`: uniqueness of the factorization with invertible middle factor.
* `Matrix.exists_blockLDU_iff`: a block `LDU` factorization with invertible middle factor exists
  exactly when all leading block minors are units.

## References

* R. A. Horn and C. R. Johnson, *Matrix Analysis*, second edition, Cambridge University Press,
  2013, §3.5.
* R. Steinberg, *Lectures on Chevalley Groups*, AMS University Lecture Series 66 (2016),
  Chapter 5, Theorem 7.
* J. C. Jantzen, *Representations of Algebraic Groups*, second edition, AMS (2003), Part II,
  Chapter 1.
-/

public section

open OrderDual

namespace Matrix

variable {m R α : Type*} [DecidableEq m]

section Defs

variable [Zero R] [One R] [LT α] {M : Matrix m m R} {b : m → α}

/-- A square matrix is *block unitriangular* for a ranking `b` of its indices when it is block
triangular for `b` (`Matrix.BlockTriangular`) and each of its diagonal blocks is the identity: its
entry at `(i, j)` is that of the identity matrix whenever `b i = b j`. Ranking by `toDual ∘ b`
instead of `b` gives the block lower unitriangular matrices. -/
def BlockUnitriangular (M : Matrix m m R) (b : m → α) : Prop :=
  M.BlockTriangular b ∧ ∀ ⦃i j⦄, b i = b j → M i j = (1 : Matrix m m R) i j

/-- A matrix is block unitriangular exactly when it is block triangular and agrees with the
identity matrix on its diagonal blocks. -/
theorem blockUnitriangular_iff : M.BlockUnitriangular b ↔
    M.BlockTriangular b ∧ ∀ ⦃i j⦄, b i = b j → M i j = (1 : Matrix m m R) i j :=
  Iff.rfl

theorem BlockUnitriangular.blockTriangular (h : M.BlockUnitriangular b) : M.BlockTriangular b :=
  h.1

theorem BlockUnitriangular.apply_of_eq (h : M.BlockUnitriangular b) {i j : m} (hij : b i = b j) :
    M i j = (1 : Matrix m m R) i j :=
  h.2 hij

@[simp]
theorem blockUnitriangular_one {α : Type*} [Preorder α] {b : m → α} :
    (1 : Matrix m m R).BlockUnitriangular b :=
  ⟨blockTriangular_one, fun _ _ _ => rfl⟩

/-- A matrix is block unitriangular if its entries agree with the identity whenever the row's
block does not strictly precede the column's block. -/
theorem blockUnitriangular_of_apply_eq_one_apply_of_not_lt {α : Type*} [Preorder α]
    {b : m → α} (h : ∀ r s, ¬ b r < b s → M r s = (1 : Matrix m m R) r s) :
    M.BlockUnitriangular b := by
  refine ⟨fun r s hsr => ?_, fun r s hrs => h r s (by rw [hrs]; exact lt_irrefl _)⟩
  rw [h r s (not_lt_of_gt hsr), Matrix.one_apply_ne]
  exact fun hrs => (ne_of_lt hsr) (congrArg b hrs.symm)

/-- Restricting a block unitriangular matrix along an injective map of indices keeps it block
unitriangular for the restricted ranking. -/
theorem BlockUnitriangular.submatrix {n : Type*} [DecidableEq n] (h : M.BlockUnitriangular b)
    {f : n → m} (hf : Function.Injective f) : (M.submatrix f f).BlockUnitriangular (b ∘ f) :=
  ⟨h.1.submatrix, fun i j hij => by
    rw [submatrix_apply, h.2 hij, ← submatrix_one f hf, submatrix_apply]⟩

/-- A square block of a block unitriangular matrix is block unitriangular for the restricted
ranking. -/
theorem BlockUnitriangular.toSquareBlockProp (h : M.BlockUnitriangular b) (p : m → Prop) :
    (M.toSquareBlockProp p).BlockUnitriangular (b ∘ Subtype.val) :=
  h.submatrix Subtype.val_injective

/-- Applying a map of coefficients that preserves `0` and `1`, such as a ring homomorphism,
entrywise keeps a matrix block unitriangular. -/
theorem BlockUnitriangular.map {S F : Type*} [Zero S] [One S] [FunLike F R S] [ZeroHomClass F R S]
    [OneHomClass F R S] (f : F) (h : M.BlockUnitriangular b) : (M.map f).BlockUnitriangular b :=
  ⟨h.1.map f, fun i j hij => by
    rw [map_apply, h.2 hij, ← Matrix.map_one f (map_zero f) (map_one f), map_apply]⟩

/-- The transpose of a block unitriangular matrix is block unitriangular for the reversed
ranking: transposition exchanges block upper and block lower unitriangular matrices. -/
@[simp]
theorem blockUnitriangular_transpose_iff :
    Mᵀ.BlockUnitriangular (toDual ∘ b) ↔ M.BlockUnitriangular b := by
  refine ⟨fun h => ⟨fun i j hij => h.1 (i := j) (j := i) (toDual_lt_toDual.mpr hij),
    fun i j hij => ?_⟩, fun h => ⟨fun i j hij => h.1 (i := j) (j := i) (toDual_lt_toDual.mp hij),
    fun i j hij => ?_⟩⟩
  · have hji := h.2 (i := j) (j := i) (congrArg toDual hij.symm)
    rw [transpose_apply] at hji
    rw [hji]
    exact congrFun (congrFun (transpose_one : (1 : Matrix m m R)ᵀ = 1) i) j
  · rw [transpose_apply, h.2 (toDual_inj.mp hij).symm]
    exact congrFun (congrFun (transpose_one : (1 : Matrix m m R)ᵀ = 1) i) j

end Defs

section Mul

variable [Fintype m] [NonAssocSemiring R] [LinearOrder α] {A B : Matrix m m R} {b : m → α}

/-- On a diagonal block, multiplying a block triangular matrix on the left by a block
unitriangular one leaves its entries unchanged. -/
theorem BlockUnitriangular.mul_apply_of_eq (hA : A.BlockUnitriangular b)
    (hB : B.BlockTriangular b) {i j : m} (hij : b i = b j) : (A * B) i j = B i j := by
  rw [Matrix.mul_apply, Finset.sum_eq_single i]
  · rw [hA.2 rfl, one_apply_eq, one_mul]
  · intro k _ hki
    by_cases hk : b k < b i
    · rw [hA.1 hk, zero_mul]
    by_cases hk' : b j < b k
    · rw [hB hk', mul_zero]
    have hki' : b i = b k :=
      le_antisymm (not_lt.mp hk) ((not_lt.mp hk').trans hij.ge)
    rw [hA.2 hki', one_apply_ne (Ne.symm hki), zero_mul]
  · simp

/-- Block unitriangular matrices are closed under multiplication. -/
theorem BlockUnitriangular.mul (hA : A.BlockUnitriangular b) (hB : B.BlockUnitriangular b) :
    (A * B).BlockUnitriangular b :=
  ⟨hA.1.mul hB.1, fun _ _ hij => (hA.mul_apply_of_eq hB.1 hij).trans (hB.2 hij)⟩

/-- A block diagonal matrix `D`, multiplied on the left by a block lower unitriangular matrix, is
unchanged as soon as the product is block upper triangular. -/
theorem mul_eq_of_blockUnitriangular_toDual {Z D : Matrix m m R}
    (hZ : Z.BlockUnitriangular (toDual ∘ b)) (hD : D.BlockTriangular b)
    (hD' : D.BlockTriangular (toDual ∘ b)) (hZD : (Z * D).BlockTriangular b) : Z * D = D := by
  ext i j
  rcases lt_trichotomy (b i) (b j) with hij | hij | hij
  · rw [(hZ.1.mul hD') (toDual_lt_toDual.mpr hij), hD' (toDual_lt_toDual.mpr hij)]
  · exact hZ.mul_apply_of_eq hD' (congrArg toDual hij)
  · rw [hZD hij, hD hij]

end Mul

section CommRing

variable [Fintype m] [CommRing R] [LinearOrder α] {M : Matrix m m R} {b : m → α}

/-- A block unitriangular matrix has determinant one. -/
theorem BlockUnitriangular.det_eq_one (h : M.BlockUnitriangular b) : M.det = 1 := by
  rw [h.1.det]
  refine Finset.prod_eq_one fun a _ => ?_
  have : M.toSquareBlock b a = 1 := by
    ext i j
    rw [toSquareBlock_def, of_apply, h.2 (i.2.trans j.2.symm)]
    by_cases hij : i = j
    · subst hij
      simp
    · rw [one_apply_ne hij, one_apply_ne fun h => hij (Subtype.ext h)]
  rw [this, det_one]

theorem BlockUnitriangular.isUnit_det (h : M.BlockUnitriangular b) : IsUnit M.det :=
  h.det_eq_one ▸ isUnit_one

/-- The inverse of a block unitriangular matrix is block unitriangular. -/
theorem BlockUnitriangular.inv (h : M.BlockUnitriangular b) : M⁻¹.BlockUnitriangular b := by
  let := M.invertibleOfIsUnitDet h.isUnit_det
  have hinv : M⁻¹.BlockTriangular b := blockTriangular_inv_of_blockTriangular h.1
  refine ⟨hinv, fun i j hij => ?_⟩
  rw [← h.mul_apply_of_eq hinv hij, mul_nonsing_inv M h.isUnit_det]

/-! ### Row reduction and existence -/

/-- The multipliers of block row reduction: row `i` holds, on the columns of rank below `b i`, the
coefficients expressing minus row `i` of `M` on those columns through the rows of rank below
`b i`, and vanishes elsewhere. -/
private noncomputable def rowMultiplier (b : m → α) (M : Matrix m m R) : Matrix m m R :=
  of fun i k => if h : b k < b i then
    -((fun j : {j // b j < b i} => M i j) ᵥ* (M.toSquareBlockProp fun j => b j < b i)⁻¹) ⟨k, h⟩
    else 0

private theorem rowMultiplier_apply_of_lt (M : Matrix m m R) {i k : m} (h : b k < b i) :
    rowMultiplier b M i k =
      -((fun j : {j // b j < b i} => M i j) ᵥ* (M.toSquareBlockProp fun j => b j < b i)⁻¹)
        ⟨k, h⟩ := by
  rw [rowMultiplier, of_apply, dite_eq_left h]

private theorem rowMultiplier_apply_of_not_lt (M : Matrix m m R) {i k : m} (h : ¬b k < b i) :
    rowMultiplier b M i k = 0 := by
  rw [rowMultiplier, of_apply, dite_eq_right h]

private theorem blockUnitriangular_one_add_rowMultiplier (M : Matrix m m R) :
    (1 + rowMultiplier b M).BlockUnitriangular (toDual ∘ b) := by
  refine ⟨fun i k hik => ?_, fun i k hik => ?_⟩
  · have hik' : b i < b k := toDual_lt_toDual.mp hik
    rw [Matrix.add_apply, rowMultiplier_apply_of_not_lt M hik'.not_gt, add_zero,
      one_apply_ne fun h => hik'.ne (congrArg b h)]
  · rw [Matrix.add_apply, rowMultiplier_apply_of_not_lt M (toDual_inj.mp hik).symm.not_lt, add_zero]

private theorem blockTriangular_one_add_rowMultiplier_mul (M : Matrix m m R)
    (hM : ∀ i, IsUnit (M.toSquareBlockProp fun j => b j < b i).det) :
    ((1 + rowMultiplier b M) * M).BlockTriangular b := by
  intro i j hij
  -- On the columns of rank below `b i`, the multipliers of row `i` combine the rows of the
  -- leading block `N` into minus row `i` of `M`.
  have hx : (-((fun k : {k // b k < b i} => M i k) ᵥ*
      (M.toSquareBlockProp fun k => b k < b i)⁻¹)) ᵥ* (M.toSquareBlockProp fun k => b k < b i) =
      -fun k : {k // b k < b i} => M i k := by
    rw [neg_vecMul, vecMul_vecMul, nonsing_inv_mul _ (hM i), vecMul_one]
  have hN : ∀ k : {k // b k < b i},
      (M.toSquareBlockProp fun k => b k < b i) k ⟨j, hij⟩ = M k j := fun _ => rfl
  have hsum := congrFun hx ⟨j, hij⟩
  rw [vecMul, dotProduct, Pi.neg_apply] at hsum
  simp only [hN, Pi.neg_apply] at hsum
  rw [Matrix.add_mul, Matrix.one_mul, Matrix.add_apply, Matrix.mul_apply,
    ← Fintype.sum_subtype_add_sum_subtype fun k => b k < b i,
    Fintype.sum_eq_zero (fun k : {k // ¬b k < b i} => rowMultiplier b M i k * M k j) fun k => by
      rw [rowMultiplier_apply_of_not_lt M k.2, zero_mul], add_zero,
    Finset.sum_congr rfl fun (k : {k // b k < b i}) _ => by
      rw [rowMultiplier_apply_of_lt M k.2, Subtype.coe_eta], hsum, add_neg_cancel]

/-- **Block row reduction.** If, for every index `i`, the leading block of `M` on the indices of
rank strictly below `b i` has a unit determinant, then some block lower unitriangular matrix `P`
makes `P * M` block upper triangular. -/
theorem exists_blockUnitriangular_mul_blockTriangular (M : Matrix m m R)
    (hM : ∀ i, IsUnit (M.toSquareBlockProp fun j => b j < b i).det) :
    ∃ P : Matrix m m R, P.BlockUnitriangular (toDual ∘ b) ∧ (P * M).BlockTriangular b :=
  ⟨1 + rowMultiplier b M, blockUnitriangular_one_add_rowMultiplier M,
    blockTriangular_one_add_rowMultiplier_mul M hM⟩

/-- **Existence of a block `LDU` factorization.** If, for every index `i`, the leading block of `M`
on the indices of rank strictly below `b i` has a unit determinant, then `M = L * D * U` with `L`
block lower unitriangular, `D` block diagonal and `U` block upper unitriangular for `b`. -/
theorem exists_blockLDU (M : Matrix m m R)
    (hM : ∀ i, IsUnit (M.toSquareBlockProp fun j => b j < b i).det) :
    ∃ L D U : Matrix m m R, L.BlockUnitriangular (toDual ∘ b) ∧ D.BlockTriangular b ∧
      D.BlockTriangular (toDual ∘ b) ∧ U.BlockUnitriangular b ∧ M = L * D * U := by
  obtain ⟨P, hP, hPM⟩ := exists_blockUnitriangular_mul_blockTriangular M hM
  obtain ⟨Q, hQ, hQM⟩ := exists_blockUnitriangular_mul_blockTriangular Mᵀ fun i => by
    -- A square block of `Mᵀ` is the transpose of the corresponding square block of `M`.
    have hblock : (Mᵀ.toSquareBlockProp fun j => b j < b i) =
        (M.toSquareBlockProp fun j => b j < b i)ᵀ := by
      ext
      simp only [toSquareBlockProp_def, of_apply, transpose_apply]
    rw [hblock, det_transpose]
    exact hM i
  have hQt : Qᵀ.BlockUnitriangular b :=
    blockUnitriangular_transpose_iff.mp (by rwa [transpose_transpose])
  refine ⟨P⁻¹, P * M * Qᵀ, Qᵀ⁻¹, hP.inv, hPM.mul hQt.1, ?_, hQt.inv, ?_⟩
  · have hMQ : (M * Qᵀ).BlockTriangular (toDual ∘ b) := by
      simpa only [transpose_mul, transpose_transpose] using hQM.transpose
    rw [Matrix.mul_assoc]
    exact hP.1.mul hMQ
  · rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, nonsing_inv_mul P hP.isUnit_det, Matrix.one_mul,
      mul_nonsing_inv_cancel_right _ _ hQt.isUnit_det]

/-! ### Uniqueness -/

/-- **Uniqueness of the block `LDU` factorization.** Two block `LDU` factorizations of the same
matrix with invertible middle factor coincide. -/
theorem eq_of_blockLDU_eq {L D U L' D' U' : Matrix m m R}
    (hL : L.BlockUnitriangular (toDual ∘ b)) (hD : D.BlockTriangular b)
    (hD₁ : D.BlockTriangular (toDual ∘ b)) (hU : U.BlockUnitriangular b)
    (hL' : L'.BlockUnitriangular (toDual ∘ b)) (hD' : D'.BlockTriangular b)
    (hD'₁ : D'.BlockTriangular (toDual ∘ b)) (hU' : U'.BlockUnitriangular b)
    (hDdet : IsUnit D.det) (h : L * D * U = L' * D' * U') : L = L' ∧ D = D' ∧ U = U' := by
  have hLL : (L'⁻¹ * L).BlockUnitriangular (toDual ∘ b) := hL'.inv.mul hL
  have hUU : (U' * U⁻¹).BlockUnitriangular b := hU'.mul hU.inv
  -- Both sides of `L'⁻¹ * L * D = D' * (U' * U⁻¹)` are block upper and block lower triangular.
  have hY : L'⁻¹ * L * D = D' * (U' * U⁻¹) := by
    calc L'⁻¹ * L * D = L'⁻¹ * (L * D * U) * U⁻¹ := by
          rw [Matrix.mul_assoc L'⁻¹ (L * D * U), mul_nonsing_inv_cancel_right U _ hU.isUnit_det,
            Matrix.mul_assoc]
      _ = D' * (U' * U⁻¹) := by
          rw [h, Matrix.mul_assoc L' D' U', nonsing_inv_mul_cancel_left L' _ hL'.isUnit_det,
            Matrix.mul_assoc]
  have hupper : (L'⁻¹ * L * D).BlockTriangular b := hY ▸ hD'.mul hUU.1
  have hlower : (D' * (U' * U⁻¹)).BlockTriangular (toDual ∘ b) := hY ▸ hLL.1.mul hD₁
  have hYD : L'⁻¹ * L * D = D := mul_eq_of_blockUnitriangular_toDual hLL hD hD₁ hupper
  -- Transposing reduces the right-hand side to the same statement.
  have hYD' : D' * (U' * U⁻¹) = D' := by
    have := mul_eq_of_blockUnitriangular_toDual (Z := (U' * U⁻¹)ᵀ) (D := D'ᵀ)
      (blockUnitriangular_transpose_iff.mpr hUU)
      (fun i j hij => hD'₁ (i := j) (j := i) (toDual_lt_toDual.mpr hij)) hD'.transpose
      (by
        rw [← transpose_mul]
        exact fun i j hij => hlower (i := j) (j := i) (toDual_lt_toDual.mpr hij))
    simpa only [← transpose_mul, transpose_inj] using this
  have hDD : D = D' := hYD.symm.trans (hY.trans hYD')
  subst hDD
  refine ⟨?_, rfl, ?_⟩
  · have h1 : L'⁻¹ * L = 1 := by
      rw [← mul_nonsing_inv_cancel_right D (L'⁻¹ * L) hDdet, hYD, mul_nonsing_inv D hDdet]
    rw [← mul_nonsing_inv_cancel_left L' L hL'.isUnit_det, h1, Matrix.mul_one]
  · have h1 : U' * U⁻¹ = 1 := by
      rw [← nonsing_inv_mul_cancel_left D (U' * U⁻¹) hDdet, hYD', nonsing_inv_mul D hDdet]
    rw [← nonsing_inv_mul_cancel_right U U' hU.isUnit_det, h1, Matrix.one_mul]

/-! ### Leading block minors -/

/-- **Leading block minors of a block `LDU` product.** On a set of indices that is down-closed for
`b`, the square block of `L * D * U` has the same determinant as that of `D`. -/
theorem det_toSquareBlockProp_blockLDU {L D U : Matrix m m R}
    (hL : L.BlockUnitriangular (toDual ∘ b)) (hU : U.BlockUnitriangular b) {p : m → Prop}
    [DecidablePred p] (hp : ∀ ⦃i j⦄, b j ≤ b i → p i → p j) :
    ((L * D * U).toSquareBlockProp p).det = (D.toSquareBlockProp p).det := by
  rw [hU.1.toSquareBlockProp_mul hp, hL.1.toSquareBlockProp_mul_of_toDual hp, det_mul, det_mul,
    (hL.toSquareBlockProp p).det_eq_one, (hU.toSquareBlockProp p).det_eq_one, one_mul, mul_one]

/-- **Block `LDU` factorization and leading block minors.** A square matrix has a block `LDU`
factorization with invertible middle factor if and only if each of its leading block minors, the
determinants of its square blocks on the initial segments `{j | b j ≤ b i}`, is a unit. -/
theorem exists_blockLDU_iff (M : Matrix m m R) :
    (∀ i, IsUnit (M.toSquareBlockProp fun j => b j ≤ b i).det) ↔
      ∃ L D U : Matrix m m R, L.BlockUnitriangular (toDual ∘ b) ∧ D.BlockTriangular b ∧
        D.BlockTriangular (toDual ∘ b) ∧ U.BlockUnitriangular b ∧ IsUnit D.det ∧
          M = L * D * U := by
  constructor
  · intro hM
    obtain ⟨L, D, U, hL, hD, hD', hU, rfl⟩ :=
      exists_blockLDU M (isUnit_det_toSquareBlockProp_lt M hM)
    refine ⟨L, D, U, hL, hD, hD', hU, ?_, rfl⟩
    -- The determinant of `L * D * U`, which is that of `D`, is the leading block minor of the
    -- top rank.
    have hfull : IsUnit (L * D * U).det := by
      cases isEmpty_or_nonempty m
      · rw [det_isEmpty]
        exact isUnit_one
      obtain ⟨k, -, hk⟩ := Finset.exists_max_image Finset.univ b Finset.univ_nonempty
      have htop : ((L * D * U).toSquareBlockProp fun _ => True).det = (L * D * U).det :=
        det_submatrix_equiv_self (Equiv.subtypeUnivEquiv fun _ => trivial) _
      rw [← htop, ← equiv_block_det _ (p := fun j => b j ≤ b k) (q := fun _ => True)
        fun j => ⟨fun _ => hk j (Finset.mem_univ j), fun _ => trivial⟩]
      exact hM k
    rwa [det_mul, det_mul, hL.det_eq_one, hU.det_eq_one, one_mul, mul_one] at hfull
  · rintro ⟨L, D, U, hL, hD, hD', hU, hDdet, rfl⟩ i
    have hp : ∀ ⦃j k⦄, b k ≤ b j → b j ≤ b i → b k ≤ b i := fun _ _ h₁ h₂ => h₁.trans h₂
    rw [det_toSquareBlockProp_blockLDU hL hU hp]
    -- `D` is block triangular for the split into the leading segment and its complement.
    rw [twoBlockTriangular_det D (fun j => b j ≤ b i)
      fun j hj k hk => hD (lt_of_le_of_lt hk (not_le.mp hj))] at hDdet
    exact isUnit_of_mul_isUnit_left hDdet

end CommRing

end Matrix
