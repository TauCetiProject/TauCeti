/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Matrix.Block
public import Mathlib.Data.Matrix.ColumnRowPartitioned
public import Mathlib.LinearAlgebra.Projection
public import Mathlib.RingTheory.Finiteness.Projective
public import TauCeti.Algebra.Module.Projective.Complement
public import TauCeti.Data.Matrix.Block
public import TauCeti.Data.Matrix.Mul
public import TauCeti.LinearAlgebra.Matrix.Range
public import TauCeti.LinearAlgebra.Matrix.ToLin

/-!
# Finitely generated projective modules from idempotent matrices

Let `A` be a semiring, not necessarily commutative. An idempotent matrix `e : Matrix ι ι A` acts on
row vectors `ι → A` on the right, and this action is linear for the left `A`-module structure.
Its range, the row vectors fixed by `e`, is a direct summand of `ι → A`, hence a finitely
generated projective left `A`-module. This file proves the two facts that make idempotent
matrices a presentation of finitely generated projective modules, the stable-idempotent
description of algebraic `K₀`:

* every finitely generated projective module is isomorphic to such a range;
* two such ranges are isomorphic exactly when the idempotents are *equivalent*
  (`Matrix.IdempotentEquivalent`): `e = x * y` and `f = y * x` for rectangular matrices `x` and
  `y` with `e * x = x = x * f` and `f * y = y = y * e`. For idempotent `e` and `f` the side
  conditions can always be arranged.

Equivalence of idempotents is an equivalence relation, preserved by relabelling indices,
conjugation, block sums and ring homomorphisms. The range for the block-diagonal matrix
`Matrix.fromBlocks e 0 0 f` is the product of the ranges, so direct sums of modules correspond to
block sums of idempotents, and `f ⊕ (1 - f)` is equivalent to the identity matrix.

Right modules are left modules over the opposite ring. The image of the action `v ↦ e *ᵥ v` of a
matrix `e` on column vectors, a right `A`-module, is identified with the range of the row action
of the transpose of `e` with entries in `Aᵐᵒᵖ`, and transposition preserves equivalence of
idempotents. So the images of two idempotent matrices acting on columns are isomorphic right
modules exactly when the matrices are equivalent.

## Main results

* `Matrix.IdempotentEquivalent`: equivalence of idempotent matrices of possibly different sizes,
  with `refl`, `symm` and `trans`.
* `Matrix.idempotentEquivalent_iff_exists_mul_eq`: for idempotents, `e ∼ f` if and only if
  `e = x * y` and `f = y * x` for some rectangular `x` and `y`.
* `Matrix.idempotentEquivalent_submatrix`, `Matrix.idempotentEquivalent_conj`,
  `Matrix.IdempotentEquivalent.fromBlocks`, `Matrix.IdempotentEquivalent.map`: invariance under
  relabelling, conjugation, block sums and ring homomorphisms.
* `Matrix.idempotentEquivalent_zero_iff`,
  `IsIdempotentElem.idempotentEquivalent_fromBlocks_zero_right`,
  `IsIdempotentElem.idempotentEquivalent_fromBlocks_zero_left`,
  `Matrix.idempotentEquivalent_self_iff`, `Matrix.idempotentEquivalent_single_one`,
  `Matrix.idempotentEquivalent_fromBlocks_one_sub`: zero matrices, zero-block padding,
  self-equivalence, diagonal matrix units, and `f ⊕ (1 - f) ∼ 1`.
* `IsIdempotentElem.mem_range_vecMulLinear_iff`: the range of an idempotent matrix consists of its
  fixed row vectors.
* `IsIdempotentElem.projective_range_vecMulLinear`: this range is a projective module.
* `IsIdempotentElem.linearMap_apply_eq_vecMul`: a linear map out of this range is right
  multiplication by the matrix of its values on the rows.
* `Matrix.linearEquivRangeVecMulLinearOfMulEq`,
  `Matrix.nonempty_linearEquiv_range_vecMulLinear_iff`: the ranges of two idempotent matrices are
  isomorphic if and only if the matrices are equivalent idempotents, via explicit maps from
  witnesses `x * y = e` and `y * x = f`.
* `Module.Finite.exists_linearEquiv_range_vecMulLinear`: a finitely generated projective module is
  isomorphic to the range of an idempotent matrix.
* `Matrix.nonempty_linearEquiv_range_mulVecBilin_iff`: the images of two idempotent matrices acting
  on column vectors are isomorphic right modules if and only if the matrices are equivalent
  idempotents.

## References

* J. Rosenberg, *Algebraic K-Theory and Its Applications*, §1.2.
* C. Weibel, *The K-book*, Chapter II, §2.
-/

public section

open LinearMap Matrix

section NonUnitalNonAssocSemiring

variable {A B : Type*} [NonUnitalNonAssocSemiring A] [NonUnitalNonAssocSemiring B]
  {ι : Type*} [Fintype ι] {F : Type*} [FunLike F A B] [NonUnitalRingHomClass F A B]

/-- The entrywise image of an idempotent matrix under a (possibly nonunital) ring homomorphism is
idempotent. -/
theorem IsIdempotentElem.matrix_map {e : Matrix ι ι A}
    (he : IsIdempotentElem e) (f : F) : IsIdempotentElem (e.map f) := by
  rw [IsIdempotentElem, ← Matrix.map_mul, he.eq]

end NonUnitalNonAssocSemiring

section Idempotent

variable {A : Type*} [Semiring A] {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- Right multiplication of row vectors by an idempotent matrix is an idempotent endomorphism. -/
theorem IsIdempotentElem.vecMulLinear {e : Matrix ι ι A} (he : IsIdempotentElem e) :
    IsIdempotentElem e.vecMulLinear := by
  ext v : 1
  simp [mul_apply_eq_comp, Matrix.vecMul_vecMul, he.eq]

/-- The range of right multiplication by an idempotent matrix is a direct summand of the row
vectors, hence a projective module. -/
theorem IsIdempotentElem.projective_range_vecMulLinear {e : Matrix ι ι A}
    (he : IsIdempotentElem e) : Module.Projective A (range e.vecMulLinear) :=
  he.vecMulLinear.projective_range

/-- The range of right multiplication by an idempotent matrix `e` consists of the row vectors
fixed by `e`. -/
theorem IsIdempotentElem.mem_range_vecMulLinear_iff {e : Matrix ι ι A} (he : IsIdempotentElem e)
    {v : ι → A} : v ∈ range e.vecMulLinear ↔ v ᵥ* e = v :=
  he.vecMulLinear.mem_range_iff

/-- A vector `v` in the range of an idempotent matrix `e` is the combination `∑ i, vᵢ • eᵢ` of
the rows `eᵢ` of `e`. -/
theorem IsIdempotentElem.eq_sum_smul_row {e : Matrix ι ι A} (he : IsIdempotentElem e)
    (v : range e.vecMulLinear) :
    v = ∑ i, (v : ι → A) i • (⟨e i, e.row_mem_range_vecMulLinear i⟩ : range e.vecMulLinear) := by
  ext1
  rw [Submodule.coe_sum]
  simp only [Submodule.coe_smul, ← vecMul_eq_sum]
  exact (he.mem_range_vecMulLinear_iff.1 v.property).symm

omit [Fintype ι] in
/-- A linear map from the range of an idempotent matrix `f` to row vectors is right multiplication
by the matrix of its values on the rows of `f`. -/
theorem IsIdempotentElem.linearMap_apply_eq_vecMul {f : Matrix κ κ A} (hf : IsIdempotentElem f)
    (g : range f.vecMulLinear →ₗ[A] (ι → A)) {w : κ → A} (hw : w ∈ range f.vecMulLinear) :
    g ⟨w, hw⟩ = w ᵥ* .of fun j ↦ g ⟨f j, f.row_mem_range_vecMulLinear j⟩ := by
  have hsum : (⟨w, hw⟩ : range f.vecMulLinear) =
      ∑ j, w j • ⟨f j, f.row_mem_range_vecMulLinear j⟩ := by
    ext1
    rw [Submodule.coe_sum]
    simp only [Submodule.coe_smul, ← vecMul_eq_sum]
    exact ((hf.mem_range_vecMulLinear_iff).1 hw).symm
  rw [hsum, map_sum]
  simp only [map_smul]
  ext k
  simp [vecMul_eq_sum]

namespace Matrix

section IdempotentEquivalent

section MulAddCommMonoid

variable {A : Type*} [Mul A] [AddCommMonoid A] {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- Square matrices `e` and `f`, possibly of different sizes, are *equivalent idempotents* when
`e = x * y` and `f = y * x` for rectangular matrices `x` and `y` with `e * x = x = x * f` and
`f * y = y = y * e`. The side conditions make right multiplication by `x` and by `y` mutually
inverse maps between the ranges of `e` and of `f`, and they force `e` and `f` to be idempotent. -/
def IdempotentEquivalent (e : Matrix ι ι A) (f : Matrix κ κ A) : Prop :=
  ∃ (x : Matrix ι κ A) (y : Matrix κ ι A), x * y = e ∧ y * x = f ∧ e * x = x ∧ x * f = x ∧
    f * y = y ∧ y * e = y

/-- Unfolding `Matrix.IdempotentEquivalent`. -/
theorem idempotentEquivalent_iff {e : Matrix ι ι A} {f : Matrix κ κ A} :
    IdempotentEquivalent e f ↔ ∃ (x : Matrix ι κ A) (y : Matrix κ ι A), x * y = e ∧ y * x = f ∧
      e * x = x ∧ x * f = x ∧ f * y = y ∧ y * e = y :=
  Iff.rfl

namespace IdempotentEquivalent

variable {e : Matrix ι ι A} {f : Matrix κ κ A}

/-- An idempotent is equivalent to itself, through `x = y = e`. -/
protected theorem refl (he : IsIdempotentElem e) : IdempotentEquivalent e e :=
  ⟨e, e, he.eq, he.eq, he.eq, he.eq, he.eq, he.eq⟩

/-- Equivalence of idempotents is symmetric, by exchanging `x` and `y`. -/
protected theorem symm (h : IdempotentEquivalent e f) : IdempotentEquivalent f e := by
  obtain ⟨x, y, hxy, hyx, hex, hxf, hfy, hye⟩ := h
  exact ⟨y, x, hyx, hxy, hfy, hye, hex, hxf⟩

/-- **Opposite rings.** Equivalent idempotents stay equivalent after transposing and passing to
the opposite ring, which turns the column action of `e` into the row action of `eᵀ` over `Aᵐᵒᵖ`.
-/
theorem transpose_map_op (h : IdempotentEquivalent e f) :
    IdempotentEquivalent (eᵀ.map MulOpposite.op) (fᵀ.map MulOpposite.op) := by
  obtain ⟨x, y, hxy, hyx, hex, hxf, hfy, hye⟩ := h
  refine ⟨yᵀ.map MulOpposite.op, xᵀ.map MulOpposite.op, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    rw [← transpose_mul_map_op] <;> simp only [*]

/-- **Opposite rings.** Equivalent idempotents over `Aᵐᵒᵖ` stay equivalent after transposing and
passing back to `A`. -/
theorem transpose_map_unop {e : Matrix ι ι Aᵐᵒᵖ} {f : Matrix κ κ Aᵐᵒᵖ}
    (h : IdempotentEquivalent e f) :
    IdempotentEquivalent (eᵀ.map MulOpposite.unop) (fᵀ.map MulOpposite.unop) := by
  obtain ⟨x, y, hxy, hyx, hex, hxf, hfy, hye⟩ := h
  refine ⟨yᵀ.map MulOpposite.unop, xᵀ.map MulOpposite.unop, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    rw [← transpose_mul_map_unop] <;> simp only [*]

/-- Simultaneous row-and-column submatrix relabelling preserves equivalence of idempotents. -/
theorem submatrix {ι' κ' : Type*} [Fintype ι'] [Fintype κ'] (h : IdempotentEquivalent e f)
    (σ : ι' ≃ ι) (τ : κ' ≃ κ) :
    IdempotentEquivalent (e.submatrix σ σ) (f.submatrix τ τ) := by
  obtain ⟨x, y, hxy, hyx, hex, hxf, hfy, hye⟩ := h
  refine ⟨x.submatrix σ τ, y.submatrix τ σ, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [submatrix_mul_equiv, *]

end IdempotentEquivalent

/-- **Relabelling.** An idempotent matrix is equivalent to its relabelling along any bijection of
index types. -/
theorem idempotentEquivalent_submatrix {e : Matrix ι ι A} (he : IsIdempotentElem e) (σ : κ ≃ ι) :
    IdempotentEquivalent e (e.submatrix σ σ) := by
  simpa using (IdempotentEquivalent.refl he).submatrix (Equiv.refl ι) σ

/-- The transpose of an idempotent matrix, with entries in the opposite ring, is idempotent. -/
theorem _root_.IsIdempotentElem.matrix_transpose_map_op {e : Matrix ι ι A}
    (he : IsIdempotentElem e) : IsIdempotentElem (eᵀ.map MulOpposite.op) := by
  rw [IsIdempotentElem, ← transpose_mul_map_op, he.eq]

/-- The transpose of an idempotent matrix over the opposite ring, with entries in the ring, is
idempotent. -/
theorem _root_.IsIdempotentElem.matrix_transpose_map_unop {e : Matrix ι ι Aᵐᵒᵖ}
    (he : IsIdempotentElem e) : IsIdempotentElem (eᵀ.map MulOpposite.unop) := by
  rw [IsIdempotentElem, ← transpose_mul_map_unop, he.eq]

/-- Two square matrices are equivalent idempotents exactly when their transposes, with entries
in the opposite ring, are. -/
theorem idempotentEquivalent_transpose_map_op_iff {e : Matrix ι ι A} {f : Matrix κ κ A} :
    IdempotentEquivalent (eᵀ.map MulOpposite.op) (fᵀ.map MulOpposite.op) ↔
      IdempotentEquivalent e f :=
  ⟨fun h ↦ by
    simpa only [transpose_map_op_transpose_map_unop] using h.transpose_map_unop,
    IdempotentEquivalent.transpose_map_op⟩

end MulAddCommMonoid

section NonUnitalNonAssocSemiring

variable {A : Type*} [NonUnitalNonAssocSemiring A] {ι κ ι' κ' : Type*}
  [Fintype ι] [Fintype κ] [Fintype ι'] [Fintype κ']

/-- **Block sums.** Block-diagonal sums of equivalent idempotents are equivalent. -/
theorem IdempotentEquivalent.fromBlocks {e : Matrix ι ι A} {f : Matrix κ κ A}
    {e' : Matrix ι' ι' A} {f' : Matrix κ' κ' A} (h : IdempotentEquivalent e f)
    (h' : IdempotentEquivalent e' f') :
    IdempotentEquivalent (Matrix.fromBlocks e 0 0 e') (Matrix.fromBlocks f 0 0 f') := by
  obtain ⟨x, y, hxy, hyx, hex, hxf, hfy, hye⟩ := h
  obtain ⟨x', y', hxy', hyx', hex', hxf', hfy', hye'⟩ := h'
  refine ⟨Matrix.fromBlocks x 0 0 x', Matrix.fromBlocks y 0 0 y', ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [fromBlocks_multiply, *]

/-- **Ring homomorphisms.** Applying a (possibly nonunital) ring homomorphism to the entries
preserves equivalence of idempotents. -/
theorem IdempotentEquivalent.map {B : Type*} [NonUnitalNonAssocSemiring B] {F : Type*}
    [FunLike F A B] [NonUnitalRingHomClass F A B] {e : Matrix ι ι A} {f : Matrix κ κ A}
    (h : IdempotentEquivalent e f) (φ : F) : IdempotentEquivalent (e.map φ) (f.map φ) := by
  obtain ⟨x, y, hxy, hyx, hex, hxf, hfy, hye⟩ := h
  refine ⟨x.map φ, y.map φ, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [← Matrix.map_mul, *]

/-- Zero matrices of any two finite sizes are equivalent idempotents. -/
theorem idempotentEquivalent_zero_zero (m n : Type*) [Fintype m] [Fintype n] :
    IdempotentEquivalent (0 : Matrix m m A) (0 : Matrix n n A) :=
  idempotentEquivalent_iff.mpr ⟨0, 0, by simp, by simp, by simp, by simp, by simp, by simp⟩

/-- Only the zero matrix is equivalent to a zero matrix. -/
@[simp]
theorem idempotentEquivalent_zero_iff {e : Matrix ι ι A} :
    IdempotentEquivalent e (0 : Matrix κ κ A) ↔ e = 0 := by
  refine ⟨?_, fun h ↦ h ▸ idempotentEquivalent_zero_zero ι κ⟩
  rw [idempotentEquivalent_iff]; rintro ⟨x, y, rfl, -, -, hxf, -, -⟩
  rw [← hxf, Matrix.mul_zero, Matrix.zero_mul]

/-- A zero matrix is equivalent only to the zero matrix. -/
@[simp]
theorem zero_idempotentEquivalent_iff {f : Matrix κ κ A} :
    IdempotentEquivalent (0 : Matrix ι ι A) f ↔ f = 0 :=
  ⟨fun h ↦ idempotentEquivalent_zero_iff.1 h.symm, fun h ↦ h ▸ idempotentEquivalent_zero_zero ι κ⟩

/-- Padding an idempotent matrix by a lower-right zero block preserves its equivalence class. -/
theorem _root_.IsIdempotentElem.idempotentEquivalent_fromBlocks_zero_right (n : Type*)
    [Fintype n] {e : Matrix ι ι A} (he : IsIdempotentElem e) :
    IdempotentEquivalent (fromBlocks e 0 0 (0 : Matrix n n A)) e := by
  have hee (i j : ι) : ∑ k, e i k * e k j = e i j := by
    simpa [Matrix.mul_apply] using congr_fun (congr_fun he.eq i) j
  refine idempotentEquivalent_iff.mpr ⟨fromRows e 0, fromCols e 0, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · ext (i | i) (j | j) <;> simp [Matrix.mul_apply, hee]
  · ext i j; simp [Matrix.mul_apply, Fintype.sum_sum_type, hee]
  · ext (i | i) j <;> simp [Matrix.mul_apply, Fintype.sum_sum_type, hee]
  · ext (i | i) j <;> simp [Matrix.mul_apply, hee]
  · ext i (j | j) <;> simp [Matrix.mul_apply, hee]
  · ext i (j | j) <;> simp [Matrix.mul_apply, Fintype.sum_sum_type, hee]

/-- Padding an idempotent matrix by an upper-left zero block preserves its equivalence class. -/
theorem _root_.IsIdempotentElem.idempotentEquivalent_fromBlocks_zero_left (m : Type*)
    [Fintype m] {e : Matrix ι ι A} (he : IsIdempotentElem e) :
    IdempotentEquivalent (fromBlocks (0 : Matrix m m A) 0 0 e) e := by
  have hEq : fromBlocks (0 : Matrix m m A) 0 0 e =
      (fromBlocks e 0 0 (0 : Matrix m m A)).submatrix (Equiv.sumComm m ι) (Equiv.sumComm m ι) := by
    ext (_ | _) (_ | _) <;> simp
  rw [hEq]
  simpa using (he.idempotentEquivalent_fromBlocks_zero_right m).submatrix
    (Equiv.sumComm m ι) (Equiv.refl ι)

end NonUnitalNonAssocSemiring

section NonUnitalSemiring

variable {A : Type*} [NonUnitalSemiring A] {ι κ μ : Type*} [Fintype ι] [Fintype κ] [Fintype μ]

namespace IdempotentEquivalent

variable {e : Matrix ι ι A} {f : Matrix κ κ A} {g : Matrix μ μ A}

/-- The first of two equivalent idempotents is idempotent. -/
theorem isIdempotentElem_left (h : IdempotentEquivalent e f) : IsIdempotentElem e := by
  obtain ⟨x, y, hxy, -, -, -, -, hye⟩ := h
  rw [IsIdempotentElem]
  nth_rw 1 [← hxy]
  rw [Matrix.mul_assoc, hye, hxy]

/-- The second of two equivalent idempotents is idempotent. -/
theorem isIdempotentElem_right (h : IdempotentEquivalent e f) : IsIdempotentElem f := by
  obtain ⟨x, y, -, hyx, -, hxf, -, -⟩ := h
  rw [IsIdempotentElem]
  nth_rw 1 [← hyx]
  rw [Matrix.mul_assoc, hxf, hyx]

/-- Equivalence of idempotents is transitive, through the products `x * x'` and `y' * y`. -/
protected theorem trans (h : IdempotentEquivalent e f) (h' : IdempotentEquivalent f g) :
    IdempotentEquivalent e g := by
  obtain ⟨x, y, hxy, hyx, hex, hxf, -, hye⟩ := h
  obtain ⟨x', y', hxy', hyx', -, hxg', hgy', hyf'⟩ := h'
  refine ⟨x * x', y' * y, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc x', hxy', ← Matrix.mul_assoc, hxf, hxy]
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc y, hyx, ← Matrix.mul_assoc, hyf', hyx']
  · rw [← Matrix.mul_assoc, hex]
  · rw [Matrix.mul_assoc, hxg']
  · rw [← Matrix.mul_assoc, hgy']
  · rw [Matrix.mul_assoc, hye]

end IdempotentEquivalent

/-- For idempotent `e` and `f`, the side conditions in `Matrix.IdempotentEquivalent` can always be
arranged: `e` and `f` are equivalent as soon as `e = x * y` and `f = y * x` for some rectangular
`x` and `y`, by replacing `x` with `x * f` and `y` with `y * e`. -/
theorem idempotentEquivalent_iff_exists_mul_eq {e : Matrix ι ι A} {f : Matrix κ κ A}
    (he : IsIdempotentElem e) (hf : IsIdempotentElem f) :
    IdempotentEquivalent e f ↔ ∃ (x : Matrix ι κ A) (y : Matrix κ ι A), x * y = e ∧ y * x = f := by
  refine ⟨fun ⟨x, y, hxy, hyx, _⟩ ↦ ⟨x, y, hxy, hyx⟩, fun ⟨x, y, hxy, hyx⟩ ↦ ?_⟩
  -- `x * f = e * x` and `y * e = f * y`, and both products below reduce to powers of `e` or `f`.
  have hxf : x * f = e * x := by rw [← hyx, ← hxy, Matrix.mul_assoc]
  have hye : y * e = f * y := by rw [← hyx, ← hxy, Matrix.mul_assoc]
  refine ⟨x * f, y * e, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hxf, Matrix.mul_assoc, ← Matrix.mul_assoc x, hxy, he.eq, he.eq]
  · rw [hye, Matrix.mul_assoc, ← Matrix.mul_assoc y, hyx, hf.eq, hf.eq]
  · rw [hxf, ← Matrix.mul_assoc, he.eq]
  · rw [Matrix.mul_assoc, hf.eq]
  · rw [hye, ← Matrix.mul_assoc, hf.eq]
  · rw [Matrix.mul_assoc, he.eq]

/-- A square matrix is equivalent to itself if and only if it is idempotent. -/
@[simp]
theorem idempotentEquivalent_self_iff {e : Matrix ι ι A} :
    IdempotentEquivalent e e ↔ IsIdempotentElem e :=
  ⟨IdempotentEquivalent.isIdempotentElem_left, IdempotentEquivalent.refl⟩

end NonUnitalSemiring

section NonAssocSemiring

variable {A : Type*} [NonAssocSemiring A] {ι κ : Type*}

/-- Any two diagonal matrix units `Eᵢᵢ ∈ Matrix ι ι A` and `Eⱼⱼ ∈ Matrix κ κ A` are equivalent
idempotents, witnessed by `Eᵢⱼ` and `Eⱼᵢ`. -/
theorem idempotentEquivalent_single_one [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (i : ι) (j : κ) : IdempotentEquivalent (single i i (1 : A)) (single j j (1 : A)) :=
  idempotentEquivalent_iff.mpr
    ⟨single i j 1, single j i 1, by simp, by simp, by simp, by simp, by simp, by simp⟩

/-- Any diagonal matrix unit `Eᵢᵢ` is equivalent to the `1 × 1` identity matrix. -/
theorem idempotentEquivalent_single_one_one [Fintype ι] [DecidableEq ι] (i : ι) :
    IdempotentEquivalent (single i i (1 : A)) (1 : Matrix (Fin 1) (Fin 1) A) := by
  have h1 : single (0 : Fin 1) 0 (1 : A) = (1 : Matrix (Fin 1) (Fin 1) A) := by
    ext a b; simp [Subsingleton.elim a 0, Subsingleton.elim b 0, Matrix.one_apply]
  exact h1 ▸ idempotentEquivalent_single_one i (0 : Fin 1)

/-- Over a nontrivial nonassociative semiring, `Eᵢᵢ` is not equivalent to a zero matrix. -/
theorem not_idempotentEquivalent_single_one_zero [Nontrivial A] [Fintype ι] [Fintype κ]
    [DecidableEq ι] (i : ι) : ¬ IdempotentEquivalent (single i i (1 : A)) (0 : Matrix κ κ A) := by
  rw [idempotentEquivalent_zero_iff]; intro h; have hii := congrFun (congrFun h i) i; simp at hii

end NonAssocSemiring

section Semiring

variable {A : Type*} [Semiring A] {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- **Conjugation.** An idempotent matrix is equivalent to each of its conjugates. -/
theorem idempotentEquivalent_conj [DecidableEq ι] {e : Matrix ι ι A} (he : IsIdempotentElem e)
    (u : (Matrix ι ι A)ˣ) : IdempotentEquivalent e (u * e * u⁻¹ : Matrix ι ι A) := by
  have hue : IsIdempotentElem (u * e * u⁻¹ : Matrix ι ι A) := by
    simp only [IsIdempotentElem, Matrix.mul_assoc, Units.inv_mul_cancel_left]
    rw [← Matrix.mul_assoc e e, he.eq]
  refine (idempotentEquivalent_iff_exists_mul_eq he hue).2
    ⟨e * (↑u⁻¹ : Matrix ι ι A), u * e, ?_, ?_⟩
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc (↑u⁻¹ : Matrix ι ι A), Units.inv_mul, Matrix.one_mul,
      he.eq]
  · rw [← Matrix.mul_assoc, Matrix.mul_assoc (u : Matrix ι ι A), he.eq]

/-- **Complements.** For an idempotent `f`, the block sum of `f` and its complement `1 - f` is
equivalent to the identity matrix: the images of `f` and `1 - f` together make up all vectors. -/
theorem idempotentEquivalent_fromBlocks_one_sub {A : Type*} [Ring A] [DecidableEq κ]
    {f : Matrix κ κ A} (hf : IsIdempotentElem f) :
    IdempotentEquivalent (Matrix.fromBlocks f 0 0 (1 - f)) (1 : Matrix κ κ A) := by
  refine (idempotentEquivalent_iff_exists_mul_eq (hf.fromBlocks_zero₁₂_zero₂₁ hf.one_sub)
    .one).2 ⟨fromRows f (1 - f), fromCols f (1 - f), ?_, ?_⟩
  · rw [fromRows_mul_fromCols, hf.eq, hf.mul_one_sub_self, hf.one_sub_mul_self, hf.one_sub.eq]
  · rw [fromCols_mul_fromRows, hf.eq, hf.one_sub.eq, add_sub_cancel]

end Semiring

end IdempotentEquivalent

variable {A : Type*} [Semiring A] {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- The matrix whose rows are the images of the rows of an idempotent matrix `e` under an
isomorphism of ranges. -/
private def rowImage {e : Matrix ι ι A} {f : Matrix κ κ A}
    (ψ : range e.vecMulLinear ≃ₗ[A] range f.vecMulLinear) : Matrix ι κ A :=
  .of fun i ↦ ψ ⟨e i, e.row_mem_range_vecMulLinear i⟩

private theorem rowImage_mul_rowImage_symm {e : Matrix ι ι A} {f : Matrix κ κ A}
    (hf : IsIdempotentElem f) (ψ : range e.vecMulLinear ≃ₗ[A] range f.vecMulLinear) :
    rowImage ψ * rowImage ψ.symm = e := by
  ext i j
  rw [mul_apply_eq_vecMul]
  have h := hf.linearMap_apply_eq_vecMul ((range e.vecMulLinear).subtype ∘ₗ ψ.symm.toLinearMap)
    (ψ ⟨e i, e.row_mem_range_vecMulLinear i⟩).property
  simp only [LinearMap.comp_apply, Submodule.subtype_apply, LinearEquiv.coe_coe, Subtype.coe_eta,
    LinearEquiv.symm_apply_apply] at h
  exact congrFun h.symm j

/-- **Mutually inverse module maps from equivalence witnesses.** When `x * y = e` and `y * x = f`
for idempotent `e` and `f`, right multiplication by `x` and `y` induces `Aᵐ e ≃ₗ[A] Aⁿ f`. -/
def linearEquivRangeVecMulLinearOfMulEq
    {e : Matrix ι ι A} {f : Matrix κ κ A} {x : Matrix ι κ A} {y : Matrix κ ι A}
    (hxy : x * y = e) (hyx : y * x = f) (he : IsIdempotentElem e) (hf : IsIdempotentElem f) :
    range e.vecMulLinear ≃ₗ[A] range f.vecMulLinear where
  toFun v := ⟨v ᵥ* x, by
    rw [hf.mem_range_vecMulLinear_iff, vecMul_vecMul, ← hyx, ← Matrix.mul_assoc, hxy,
      ← vecMul_vecMul, he.mem_range_vecMulLinear_iff.1 v.property]⟩
  invFun w := ⟨w ᵥ* y, by
    rw [he.mem_range_vecMulLinear_iff, vecMul_vecMul, ← hxy, ← Matrix.mul_assoc, hyx,
      ← vecMul_vecMul, hf.mem_range_vecMulLinear_iff.1 w.property]⟩
  map_add' _ _ := Subtype.ext (add_vecMul _ _ _)
  map_smul' _ _ := Subtype.ext (smul_vecMul _ _ _)
  left_inv v := Subtype.ext <| by
    simp [vecMul_vecMul, hxy, he.mem_range_vecMulLinear_iff.1 v.property]
  right_inv w := Subtype.ext <| by
    simp [vecMul_vecMul, hyx, hf.mem_range_vecMulLinear_iff.1 w.property]

@[simp]
theorem coe_linearEquivRangeVecMulLinearOfMulEq_apply
    {e : Matrix ι ι A} {f : Matrix κ κ A} {x : Matrix ι κ A} {y : Matrix κ ι A}
    (hxy : x * y = e) (hyx : y * x = f) (he : IsIdempotentElem e) (hf : IsIdempotentElem f)
    (v : range e.vecMulLinear) :
    (linearEquivRangeVecMulLinearOfMulEq hxy hyx he hf v : κ → A) = v ᵥ* x := (rfl)

@[simp]
theorem coe_linearEquivRangeVecMulLinearOfMulEq_symm_apply
    {e : Matrix ι ι A} {f : Matrix κ κ A} {x : Matrix ι κ A} {y : Matrix κ ι A}
    (hxy : x * y = e) (hyx : y * x = f) (he : IsIdempotentElem e) (hf : IsIdempotentElem f)
    (w : range f.vecMulLinear) :
    ((linearEquivRangeVecMulLinearOfMulEq hxy hyx he hf).symm w : ι → A) = w ᵥ* y := (rfl)

/-- **Algebraic equivalence of idempotent matrices.** The ranges of right multiplication by two
idempotent matrices `e` and `f` are isomorphic left `A`-modules if and only if `e` and `f` are
equivalent idempotents. -/
theorem nonempty_linearEquiv_range_vecMulLinear_iff {e : Matrix ι ι A} {f : Matrix κ κ A}
    (he : IsIdempotentElem e) (hf : IsIdempotentElem f) :
    Nonempty (range e.vecMulLinear ≃ₗ[A] range f.vecMulLinear) ↔ IdempotentEquivalent e f := by
  rw [idempotentEquivalent_iff_exists_mul_eq he hf]
  constructor
  · rintro ⟨ψ⟩
    refine ⟨rowImage ψ, rowImage ψ.symm, rowImage_mul_rowImage_symm hf ψ, ?_⟩
    simpa using rowImage_mul_rowImage_symm he ψ.symm
  · rintro ⟨x, y, hxy, hyx⟩
    exact ⟨linearEquivRangeVecMulLinearOfMulEq hxy hyx he hf⟩

/-- **Equivalence of idempotents and right modules.** The images `eAⁿ` and `fAᵐ` of the actions of
two idempotent matrices on column vectors are isomorphic right `A`-modules (left `Aᵐᵒᵖ`-modules)
if and only if `e` and `f` are equivalent idempotents. -/
theorem nonempty_linearEquiv_range_mulVecBilin_iff {e : Matrix ι ι A} {f : Matrix κ κ A}
    (he : IsIdempotentElem e) (hf : IsIdempotentElem f) :
    Nonempty (range (mulVecBilin A Aᵐᵒᵖ e) ≃ₗ[Aᵐᵒᵖ] range (mulVecBilin A Aᵐᵒᵖ f)) ↔
      IdempotentEquivalent e f := by
  rw [← idempotentEquivalent_transpose_map_op_iff, ← nonempty_linearEquiv_range_vecMulLinear_iff
    he.matrix_transpose_map_op hf.matrix_transpose_map_op]
  exact ⟨fun ⟨φ⟩ ↦ ⟨((rangeVecMulLinearTransposeMapOpEquiv e).trans φ).trans
      (rangeVecMulLinearTransposeMapOpEquiv f).symm⟩,
    fun ⟨φ⟩ ↦ ⟨((rangeVecMulLinearTransposeMapOpEquiv e).symm.trans φ).trans
      (rangeVecMulLinearTransposeMapOpEquiv f)⟩⟩

end Matrix

end Idempotent

namespace Module.Finite

variable (A P : Type*) [Semiring A] [AddCommMonoid P] [Module A P] [Module.Finite A P]
  [Module.Projective A P]

/-- **Finitely generated projective modules come from idempotent matrices.** A finitely generated
projective left `A`-module is isomorphic to the range of right multiplication by an idempotent
square matrix over `A`. -/
theorem exists_linearEquiv_range_vecMulLinear :
    ∃ (n : ℕ) (e : Matrix (Fin n) (Fin n) A), IsIdempotentElem e ∧
      Nonempty (P ≃ₗ[A] LinearMap.range e.vecMulLinear) := by
  obtain ⟨n, f, g, hf, hg, hfg⟩ := exists_comp_eq_id_of_projective A P
  -- `e` is the matrix of the idempotent endomorphism `g ∘ f` of the row vectors.
  refine ⟨n, (g ∘ₗ f).toMatrixRight', isIdempotentElem_toMatrixRight'_comp hfg, ?_⟩
  have he : (g ∘ₗ f).toMatrixRight'.vecMulLinear = g ∘ₗ f :=
    LinearMap.ext (vecMul_toMatrixRight' _)
  rw [he, range_comp_of_range_eq_top g (range_eq_top.2 hf)]
  exact ⟨LinearEquiv.ofInjective g hg⟩

end Module.Finite
