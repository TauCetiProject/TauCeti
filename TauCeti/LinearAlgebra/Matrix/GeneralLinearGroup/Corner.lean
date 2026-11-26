/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.ColumnRowFixing

/-!
# The overlapping corner matrices of `GL (n + 1)`

For a possibly noncommutative ring `A`, an invertible matrix `a` of size `n`, a column `y` and a
row `p` of length `n`, the **corner matrices** of size `n + 1` are

  `L(a, y) = [[a, y], [0, 1]]` and `R(b, p) = [[1, p], [0, b]]`.

The block `a` of `L(a, y)` occupies the first `n` coordinates, with `y` in the last column, while
the block `b` of `R(b, p)` occupies the last `n` coordinates, with `p` in the first row; for
`n ≥ 2` the two corners overlap. They multiply by

  `L(a, y) L(b, z) = L(a b, a z + y)` and `R(a, p) R(b, q) = R(a b, q + p b)`,

and each family is a subgroup of `GL (n + 1) A`: the matrices `L(a, y)` are exactly the
invertible matrices whose last row is the last standard row, and the matrices `R(b, p)` exactly
those whose first column is the first standard column.

These matrices are the building blocks of the standard forms `L(a, y) e_{n,0}(t) R(b, p)` of
Bass, Milnor and Serre, through which a homomorphism on `GL n` satisfying their extension
conditions is extended to `GL (n + 1)`, one size at a time. The lower left entry of a standard
form is the parameter `t` of its elementary factor.

Applying a ring homomorphism `f` entrywise sends `L(a, y)` to `L(f a, f y)` and `R(b, p)` to
`R(f b, f p)`, so `L(a, y)` is congruent to the identity modulo an ideal `I` exactly when `a` is
and `y` has entries in `I` (`TauCeti.unitsMap_mapMatrix_leftCornerGL_eq_one_iff`).

## Main definitions

* `TauCeti.leftCornerGL a y`: the matrix `L(a, y) = [[a, y], [0, 1]]`.
* `TauCeti.rightCornerGL b p`: the matrix `R(b, p) = [[1, p], [0, b]]`.

## Main results

* `TauCeti.leftCornerGL_mul_leftCornerGL`, `TauCeti.rightCornerGL_mul_rightCornerGL`: the product
  formulas, and `TauCeti.leftCornerGL_inv`, `TauCeti.rightCornerGL_inv`: the inverse formulas.
* `TauCeti.leftCornerGL_inj`, `TauCeti.rightCornerGL_inj`: the blocks are determined by the
  matrix.
* `TauCeti.range_uncurry_leftCornerGL`, `TauCeti.range_uncurry_rightCornerGL`: the corner matrices
  are the invertible matrices fixing the last standard row, respectively the first standard
  column.
* `TauCeti.leftCornerGL_zero`: `L(a, 0)` is the stabilization `a ⊕ 1`.
* `TauCeti.leftCornerGL_mem_elementarySubgroup`, `TauCeti.rightCornerGL_mem_elementarySubgroup`:
  corner matrices with an elementary block are elementary.
* `TauCeti.leftCornerGL_map`, `TauCeti.rightCornerGL_map`: compatibility with ring
  homomorphisms, and `TauCeti.unitsMap_mapMatrix_leftCornerGL_eq_one_iff`,
  `TauCeti.unitsMap_mapMatrix_rightCornerGL_eq_one_iff`: the congruence conditions.
* `TauCeti.det_leftCornerGL`, `TauCeti.det_rightCornerGL`: over a commutative ring the
  determinant of a corner matrix is that of its block.
* `TauCeti.coe_leftCornerGL_mul_transvectionUnit_mul_rightCornerGL_last_zero`: the lower left
  entry of `L(a, y) e_{n,0}(t) R(b, p)` is `t`.

## References

* H. Bass, J. Milnor, J.-P. Serre, *Solution of the congruence subgroup problem for `SLₙ`
  (`n ≥ 3`) and `Sp₂ₙ` (`n ≥ 2`)*, Publ. Math. IHÉS **33** (1967), §8, Lemma 8.9.
-/

public section

open Matrix

namespace TauCeti

variable {A : Type*} [Ring A] {n : ℕ}

/-- `Fin (n + 1) ≃ Fin n ⊕ Unit`, sending the last index to the `Unit` summand. -/
private abbrev lastSplit (n : ℕ) : Fin (n + 1) ≃ Fin n ⊕ Unit :=
  finSuccEquivLast.trans (Equiv.optionEquivSumPUnit (Fin n))

/-- `Fin (n + 1) ≃ Fin n ⊕ Unit`, sending the first index to the `Unit` summand. -/
private abbrev firstSplit (n : ℕ) : Fin (n + 1) ≃ Fin n ⊕ Unit :=
  (finSuccEquiv n).trans (Equiv.optionEquivSumPUnit (Fin n))

/-! ## The left corner matrices `L(a, y)` -/

/-- The **left corner matrix** `L(a, y) = [[a, y], [0, 1]]` of size `n + 1`: the invertible
matrix `a` occupies the first `n` rows and columns, the column `y` the first `n` entries of the
last column, and the last row is the last standard row. -/
def leftCornerGL (a : GL (Fin n) A) (y : Fin n → A) : GL (Fin (n + 1)) A :=
  (lastSplit n).symm.reindexGL A (upperBlockGL (replicateCol Unit y) * fromBlocksGL (a, 1))

/-- The matrix underlying `L(a, y)`, as the block matrix `[[a, y], [0, 1]]` along the splitting
of the last index. -/
private theorem coe_leftCornerGL (a : GL (Fin n) A) (y : Fin n → A) :
    (leftCornerGL a y : Matrix (Fin (n + 1)) (Fin (n + 1)) A) =
      (fromBlocks (a : Matrix (Fin n) (Fin n) A) (replicateCol Unit y) 0 1).submatrix
        (lastSplit n) (lastSplit n) := by
  rw [leftCornerGL, Equiv.coe_reindexGL, Units.val_mul, coe_upperBlockGL, coe_fromBlocksGL,
    fromBlocks_multiply]
  simp

/-- The upper left `n × n` block of `L(a, y)` is `a`. -/
@[simp]
theorem coe_leftCornerGL_castSucc_castSucc (a : GL (Fin n) A) (y : Fin n → A) (i j : Fin n) :
    (leftCornerGL a y : Matrix (Fin (n + 1)) (Fin (n + 1)) A) i.castSucc j.castSucc =
      (a : Matrix (Fin n) (Fin n) A) i j := by
  simp [coe_leftCornerGL]

/-- The last column of `L(a, y)` starts with `y`. -/
@[simp]
theorem coe_leftCornerGL_castSucc_last (a : GL (Fin n) A) (y : Fin n → A) (i : Fin n) :
    (leftCornerGL a y : Matrix (Fin (n + 1)) (Fin (n + 1)) A) i.castSucc (Fin.last n) = y i := by
  simp [coe_leftCornerGL]

/-- The last row of `L(a, y)` vanishes off the diagonal. -/
@[simp]
theorem coe_leftCornerGL_last_castSucc (a : GL (Fin n) A) (y : Fin n → A) (j : Fin n) :
    (leftCornerGL a y : Matrix (Fin (n + 1)) (Fin (n + 1)) A) (Fin.last n) j.castSucc = 0 := by
  simp [coe_leftCornerGL]

/-- The last diagonal entry of `L(a, y)` is `1`. -/
@[simp]
theorem coe_leftCornerGL_last_last (a : GL (Fin n) A) (y : Fin n → A) :
    (leftCornerGL a y : Matrix (Fin (n + 1)) (Fin (n + 1)) A) (Fin.last n) (Fin.last n) = 1 := by
  simp [coe_leftCornerGL]

/-- The identity is the left corner matrix `L(1, 0)`. -/
@[simp]
theorem leftCornerGL_one_zero : leftCornerGL (1 : GL (Fin n) A) 0 = 1 := by
  simp [leftCornerGL, Prod.mk_one_one]

/-- **Product of left corner matrices:** `L(a, y) L(b, z) = L(a b, a z + y)`. -/
@[simp]
theorem leftCornerGL_mul_leftCornerGL (a b : GL (Fin n) A) (y z : Fin n → A) :
    leftCornerGL a y * leftCornerGL b z =
      leftCornerGL (a * b) ((a : Matrix (Fin n) (Fin n) A) *ᵥ z + y) := by
  rw [leftCornerGL, leftCornerGL, leftCornerGL, ← map_mul]
  congr 1
  ext : 1
  simp [fromBlocks_multiply, replicateCol_mulVec, replicateCol_add, add_comm]

/-- **Inverse of a left corner matrix:** `L(a, y)⁻¹ = L(a⁻¹, -a⁻¹ y)`. -/
@[simp]
theorem leftCornerGL_inv (a : GL (Fin n) A) (y : Fin n → A) :
    (leftCornerGL a y)⁻¹ =
      leftCornerGL a⁻¹ (-((↑a⁻¹ : Matrix (Fin n) (Fin n) A) *ᵥ y)) := by
  refine inv_eq_of_mul_eq_one_right ?_
  simp [mulVec_neg, mulVec_mulVec]

/-- The blocks of a left corner matrix are determined by the matrix. -/
@[simp]
theorem leftCornerGL_inj {a b : GL (Fin n) A} {y z : Fin n → A} :
    leftCornerGL a y = leftCornerGL b z ↔ a = b ∧ y = z := by
  refine ⟨fun h ↦ ⟨?_, ?_⟩, fun ⟨hab, hyz⟩ ↦ hab ▸ hyz ▸ rfl⟩
  · ext i j
    simpa using congr(($h : Matrix (Fin (n + 1)) (Fin (n + 1)) A) i.castSucc j.castSucc)
  · ext i
    simpa using congr(($h : Matrix (Fin (n + 1)) (Fin (n + 1)) A) i.castSucc (Fin.last n))

/-- The left corner matrix `L(a, 0)` is the stabilization `a ⊕ 1`. -/
theorem leftCornerGL_zero (a : GL (Fin n) A) :
    leftCornerGL a 0 = stabilizeGL A (Nat.le_succ n) a := by
  ext i j
  induction i using Fin.lastCases <;> induction j using Fin.lastCases <;>
    simp [coe_stabilizeGL_apply, Matrix.one_apply, Fin.ext_iff, Fin.val_last] <;> omega

/-- A left corner matrix with an elementary block is elementary. -/
theorem leftCornerGL_mem_elementarySubgroup {a : GL (Fin n) A}
    (ha : a ∈ elementarySubgroup (Fin n) A) (y : Fin n → A) :
    leftCornerGL a y ∈ elementarySubgroup (Fin (n + 1)) A := by
  rw [leftCornerGL, Equiv.reindexGL_mem_elementarySubgroup_iff]
  exact mul_mem (upperBlockGL_mem_elementarySubgroup _)
    (map_elementarySubgroup_le_elementarySubgroup ⟨a, ha, rfl⟩)

/-- The left corner matrices are exactly the invertible matrices whose last row is the last
standard row. -/
theorem range_uncurry_leftCornerGL :
    Set.range (Function.uncurry (leftCornerGL : GL (Fin n) A → (Fin n → A) → _)) =
      columnRowFixingSubgroup A ∅ ({Fin.last n} : Set (Fin (n + 1))) := by
  ext g
  rw [SetLike.mem_coe, mem_columnRowFixingSubgroup_iff]
  simp only [Set.mem_range, Prod.exists, Function.uncurry_apply_pair, Set.mem_empty_iff_false,
    false_imp_iff, implies_true, Set.mem_singleton_iff, forall_eq, true_and]
  constructor
  · rintro ⟨a, y, rfl⟩ j
    induction j using Fin.lastCases <;> simp [(Fin.castSucc_ne_last _).symm]
  · intro hg
    set g' := (lastSplit n).reindexGL A g
    have hg' : (g' : Matrix (Fin n ⊕ Unit) (Fin n ⊕ Unit) A).toBlocks₂₁ = 0 ∧
        (g' : Matrix (Fin n ⊕ Unit) (Fin n ⊕ Unit) A).toBlocks₂₂ = 1 := by
      constructor <;> ext i j <;>
        simp [g', toBlocks₂₁, toBlocks₂₂, hg, (Fin.castSucc_ne_last _).symm]
    refine ⟨g'.toBlocks₁₁GL hg'.1 hg'.2, fun i ↦
      (g : Matrix (Fin (n + 1)) (Fin (n + 1)) A) i.castSucc (Fin.last n), ?_⟩
    ext i j
    induction i using Fin.lastCases <;> induction j using Fin.lastCases <;>
      simp [g', toBlocks₁₁, hg, (Fin.castSucc_ne_last _).symm]

/-! ## The right corner matrices `R(b, p)` -/

/-- The **right corner matrix** `R(b, p) = [[1, p], [0, b]]` of size `n + 1`: the invertible
matrix `b` occupies the last `n` rows and columns, the row `p` the last `n` entries of the first
row, and the first column is the first standard column. -/
def rightCornerGL (b : GL (Fin n) A) (p : Fin n → A) : GL (Fin (n + 1)) A :=
  (firstSplit n).symm.reindexGL A (fromBlocksGL (b, 1) * lowerBlockGL (replicateRow Unit p))

/-- The matrix underlying `R(b, p)`, as a block matrix along the splitting of the first index. -/
private theorem coe_rightCornerGL (b : GL (Fin n) A) (p : Fin n → A) :
    (rightCornerGL b p : Matrix (Fin (n + 1)) (Fin (n + 1)) A) =
      (fromBlocks (b : Matrix (Fin n) (Fin n) A) 0 (replicateRow Unit p) 1).submatrix
        (firstSplit n) (firstSplit n) := by
  rw [rightCornerGL, Equiv.coe_reindexGL, Units.val_mul, coe_lowerBlockGL, coe_fromBlocksGL,
    fromBlocks_multiply]
  simp

/-- The first diagonal entry of `R(b, p)` is `1`. -/
@[simp]
theorem coe_rightCornerGL_zero_zero (b : GL (Fin n) A) (p : Fin n → A) :
    (rightCornerGL b p : Matrix (Fin (n + 1)) (Fin (n + 1)) A) 0 0 = 1 := by
  simp [coe_rightCornerGL]

/-- The first row of `R(b, p)` ends with `p`. -/
@[simp]
theorem coe_rightCornerGL_zero_succ (b : GL (Fin n) A) (p : Fin n → A) (j : Fin n) :
    (rightCornerGL b p : Matrix (Fin (n + 1)) (Fin (n + 1)) A) 0 j.succ = p j := by
  simp [coe_rightCornerGL]

/-- The first column of `R(b, p)` vanishes off the diagonal. -/
@[simp]
theorem coe_rightCornerGL_succ_zero (b : GL (Fin n) A) (p : Fin n → A) (i : Fin n) :
    (rightCornerGL b p : Matrix (Fin (n + 1)) (Fin (n + 1)) A) i.succ 0 = 0 := by
  simp [coe_rightCornerGL]

/-- The lower right `n × n` block of `R(b, p)` is `b`. -/
@[simp]
theorem coe_rightCornerGL_succ_succ (b : GL (Fin n) A) (p : Fin n → A) (i j : Fin n) :
    (rightCornerGL b p : Matrix (Fin (n + 1)) (Fin (n + 1)) A) i.succ j.succ =
      (b : Matrix (Fin n) (Fin n) A) i j := by
  simp [coe_rightCornerGL]

/-- The identity is the right corner matrix `R(1, 0)`. -/
@[simp]
theorem rightCornerGL_one_zero : rightCornerGL (1 : GL (Fin n) A) 0 = 1 := by
  simp [rightCornerGL, Prod.mk_one_one]

/-- **Product of right corner matrices:** `R(a, p) R(b, q) = R(a b, q + p b)`. -/
@[simp]
theorem rightCornerGL_mul_rightCornerGL (a b : GL (Fin n) A) (p q : Fin n → A) :
    rightCornerGL a p * rightCornerGL b q =
      rightCornerGL (a * b) (q + p ᵥ* (b : Matrix (Fin n) (Fin n) A)) := by
  rw [rightCornerGL, rightCornerGL, rightCornerGL, ← map_mul]
  congr 1
  ext : 1
  simp [fromBlocks_multiply, replicateRow_vecMul, replicateRow_add, add_comm]

/-- **Inverse of a right corner matrix:** `R(b, p)⁻¹ = R(b⁻¹, -p b⁻¹)`. -/
@[simp]
theorem rightCornerGL_inv (b : GL (Fin n) A) (p : Fin n → A) :
    (rightCornerGL b p)⁻¹ =
      rightCornerGL b⁻¹ (-(p ᵥ* (↑b⁻¹ : Matrix (Fin n) (Fin n) A))) := by
  refine inv_eq_of_mul_eq_one_right ?_
  rw [rightCornerGL_mul_rightCornerGL, neg_add_cancel, mul_inv_cancel, rightCornerGL_one_zero]

/-- The blocks of a right corner matrix are determined by the matrix. -/
@[simp]
theorem rightCornerGL_inj {a b : GL (Fin n) A} {p q : Fin n → A} :
    rightCornerGL a p = rightCornerGL b q ↔ a = b ∧ p = q := by
  refine ⟨fun h ↦ ⟨?_, ?_⟩, fun ⟨hab, hpq⟩ ↦ hab ▸ hpq ▸ rfl⟩
  · ext i j
    simpa using congr(($h : Matrix (Fin (n + 1)) (Fin (n + 1)) A) i.succ j.succ)
  · ext j
    simpa using congr(($h : Matrix (Fin (n + 1)) (Fin (n + 1)) A) 0 j.succ)

/-- A right corner matrix with an elementary block is elementary. -/
theorem rightCornerGL_mem_elementarySubgroup {b : GL (Fin n) A}
    (hb : b ∈ elementarySubgroup (Fin n) A) (p : Fin n → A) :
    rightCornerGL b p ∈ elementarySubgroup (Fin (n + 1)) A := by
  rw [rightCornerGL, Equiv.reindexGL_mem_elementarySubgroup_iff]
  exact mul_mem (map_elementarySubgroup_le_elementarySubgroup ⟨b, hb, rfl⟩)
    (lowerBlockGL_mem_elementarySubgroup _)

/-- The right corner matrices are exactly the invertible matrices whose first column is the first
standard column. -/
theorem range_uncurry_rightCornerGL :
    Set.range (Function.uncurry (rightCornerGL : GL (Fin n) A → (Fin n → A) → _)) =
      columnRowFixingSubgroup A ({0} : Set (Fin (n + 1))) ∅ := by
  ext g
  rw [SetLike.mem_coe, mem_columnRowFixingSubgroup_iff]
  simp only [Set.mem_range, Prod.exists, Function.uncurry_apply_pair, Set.mem_empty_iff_false,
    false_imp_iff, implies_true, Set.mem_singleton_iff, forall_eq, and_true]
  constructor
  · rintro ⟨b, p, rfl⟩ i
    induction i using Fin.cases <;> simp [Fin.succ_ne_zero]
  · intro hg
    set g' := (firstSplit n).reindexGL A g
    have hg' : (g' : Matrix (Fin n ⊕ Unit) (Fin n ⊕ Unit) A).toBlocks₁₂ = 0 ∧
        (g' : Matrix (Fin n ⊕ Unit) (Fin n ⊕ Unit) A).toBlocks₂₂ = 1 := by
      constructor <;> ext i j <;> simp [g', toBlocks₁₂, toBlocks₂₂, hg, Fin.succ_ne_zero]
    refine ⟨affineProjection A (Fin n) Unit ⟨g', mem_affineGroup_iff.2 hg'⟩, fun j ↦
      (g : Matrix (Fin (n + 1)) (Fin (n + 1)) A) 0 j.succ, ?_⟩
    ext i j
    induction i using Fin.cases <;> induction j using Fin.cases <;>
      simp [g', toBlocks₁₁, hg, Fin.succ_ne_zero]

/-! ## Products with corner matrices and standard forms -/

/-- Multiplying on the left by a left corner matrix does not change the last row. -/
@[simp]
theorem coe_leftCornerGL_mul_apply_last (a : GL (Fin n) A) (y : Fin n → A)
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) A) (j : Fin (n + 1)) :
    ((leftCornerGL a y : Matrix (Fin (n + 1)) (Fin (n + 1)) A) * M) (Fin.last n) j =
      M (Fin.last n) j := by
  simp [Matrix.mul_apply, Fin.sum_univ_castSucc]

/-- Multiplying on the right by a right corner matrix does not change the first column. -/
@[simp]
theorem coe_mul_rightCornerGL_apply_zero (M : Matrix (Fin (n + 1)) (Fin (n + 1)) A)
    (b : GL (Fin n) A) (p : Fin n → A) (i : Fin (n + 1)) :
    (M * (rightCornerGL b p : Matrix (Fin (n + 1)) (Fin (n + 1)) A)) i 0 = M i 0 := by
  simp [Matrix.mul_apply, Fin.sum_univ_succ]

/-- The lower left entry of the standard form `L(a, y) e_{n,0}(t) R(b, p)` is `t`. -/
theorem coe_leftCornerGL_mul_transvectionUnit_mul_rightCornerGL_last_zero (a : GL (Fin n) A)
    (y : Fin n → A) (hn : Fin.last n ≠ 0) (t : A) (b : GL (Fin n) A) (p : Fin n → A) :
    ((leftCornerGL a y * transvectionUnit hn t * rightCornerGL b p : GL (Fin (n + 1)) A) :
        Matrix (Fin (n + 1)) (Fin (n + 1)) A) (Fin.last n) 0 = t := by
  rw [Units.val_mul, Units.val_mul, coe_mul_rightCornerGL_apply_zero,
    coe_leftCornerGL_mul_apply_last]
  simp [coe_transvectionUnit_eq_one_add_single, hn]

/-! ## Change of rings -/

section Map

variable {B : Type*} [Ring B]

/-- Applying a ring homomorphism to the entries of `L(a, y)` gives `L(f a, f y)`. -/
theorem leftCornerGL_map (f : A →+* B) (a : GL (Fin n) A) (y : Fin n → A) :
    leftCornerGL (Units.map (f.mapMatrix (m := Fin n)).toMonoidHom a) (f ∘ y) =
      Units.map (f.mapMatrix (m := Fin (n + 1))).toMonoidHom (leftCornerGL a y) := by
  ext i j
  induction i using Fin.lastCases <;> induction j using Fin.lastCases <;> simp

/-- Applying a ring homomorphism to the entries of `R(b, p)` gives `R(f b, f p)`. -/
theorem rightCornerGL_map (f : A →+* B) (b : GL (Fin n) A) (p : Fin n → A) :
    rightCornerGL (Units.map (f.mapMatrix (m := Fin n)).toMonoidHom b) (f ∘ p) =
      Units.map (f.mapMatrix (m := Fin (n + 1))).toMonoidHom (rightCornerGL b p) := by
  ext i j
  induction i using Fin.cases <;> induction j using Fin.cases <;> simp

/-- `L(a, y)` is sent to the identity by a ring homomorphism `f` exactly when `a` is and `f`
kills the entries of `y`. For the quotient map by an ideal `I`, this says that `L(a, y)` is
congruent to the identity modulo `I` exactly when `a` is and `y` has entries in `I`. -/
theorem unitsMap_mapMatrix_leftCornerGL_eq_one_iff (f : A →+* B) (a : GL (Fin n) A)
    (y : Fin n → A) :
    Units.map (f.mapMatrix (m := Fin (n + 1))).toMonoidHom (leftCornerGL a y) = 1 ↔
      Units.map (f.mapMatrix (m := Fin n)).toMonoidHom a = 1 ∧ ∀ i, f (y i) = 0 := by
  rw [← leftCornerGL_map, ← leftCornerGL_one_zero, leftCornerGL_inj, funext_iff]
  simp only [Function.comp_apply, Pi.zero_apply]

/-- `R(b, p)` is sent to the identity by a ring homomorphism `f` exactly when `b` is and `f`
kills the entries of `p`. For the quotient map by an ideal `I`, this says that `R(b, p)` is
congruent to the identity modulo `I` exactly when `b` is and `p` has entries in `I`. -/
theorem unitsMap_mapMatrix_rightCornerGL_eq_one_iff (f : A →+* B) (b : GL (Fin n) A)
    (p : Fin n → A) :
    Units.map (f.mapMatrix (m := Fin (n + 1))).toMonoidHom (rightCornerGL b p) = 1 ↔
      Units.map (f.mapMatrix (m := Fin n)).toMonoidHom b = 1 ∧ ∀ j, f (p j) = 0 := by
  rw [← rightCornerGL_map, ← rightCornerGL_one_zero, rightCornerGL_inj, funext_iff]
  simp only [Function.comp_apply, Pi.zero_apply]

end Map

/-! ## Determinants -/

section CommRing

variable {R : Type*} [CommRing R]

/-- The determinant of `L(a, y)` is the determinant of `a`. -/
@[simp]
theorem det_leftCornerGL (a : GL (Fin n) R) (y : Fin n → R) :
    GeneralLinearGroup.det (leftCornerGL a y) = GeneralLinearGroup.det a := by
  ext
  rw [GeneralLinearGroup.val_det_apply, GeneralLinearGroup.val_det_apply, coe_leftCornerGL,
    det_submatrix_equiv_self, det_fromBlocks_zero₂₁]
  simp

/-- The determinant of `R(b, p)` is the determinant of `b`. -/
@[simp]
theorem det_rightCornerGL (b : GL (Fin n) R) (p : Fin n → R) :
    GeneralLinearGroup.det (rightCornerGL b p) = GeneralLinearGroup.det b := by
  ext
  rw [GeneralLinearGroup.val_det_apply, GeneralLinearGroup.val_det_apply, coe_rightCornerGL,
    det_submatrix_equiv_self, det_fromBlocks_zero₁₂]
  simp

end CommRing

end TauCeti
