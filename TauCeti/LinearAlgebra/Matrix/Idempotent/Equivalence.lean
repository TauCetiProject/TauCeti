/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.InvariantBasisNumber
public import TauCeti.Algebra.Module.StableEquivalent
public import TauCeti.Data.Matrix.Block
public import TauCeti.LinearAlgebra.Matrix.Idempotent.RightRange
public import TauCeti.RingTheory.Idempotents.Matrix

/-!
# Rectangular algebraic equivalence of idempotent matrices

Two square matrices `e : Matrix m m R` and `f : Matrix n n R`, possibly of different sizes, are
*algebraically equivalent* (`Matrix.IsAlgebraicEquivalent e f`) if there exist rectangular matrices
`x : Matrix m n R` and `y : Matrix n m R` satisfying

`x * y = e`, `y * x = f`, `e * x = x`, `x * f = x`, `f * y = y`, and `y * e = y`.

The four corner absorptions force `e` and `f` to be idempotent whenever multiplication is
associative, and ensure that left multiplication by `x` and `y` restrict directly to mutually
inverse right `R`-module maps between the column ranges `f Rⁿ` and `e Rᵐ`
(`Matrix.linearEquivRangeMulVecBilinOfMulEq`). When `e` and `f` are already idempotent, raw
witnesses with `x * y = e` and `y * x = f` can always be normalized to `(e * x * f, f * y * e)`
(`Matrix.isAlgebraicEquivalent_iff_exists_mul_eq`).

This file establishes the calculus of rectangular algebraic equivalence:

* reflexivity on idempotent matrices, symmetry, and transitivity;
* equivalence with `Rᵐᵒᵖ`-linear isomorphism of column ranges `e Rᵐ ≃ f Rⁿ` and with `R`-linear
  isomorphism of row ranges `Rᵐ e ≃ Rⁿ f`;
* invariance under unit conjugation, zero-block padding, block direct sums, ring homomorphisms, and
  index bijections;
* over any semiring with invariant basis number, characterization of equivalence between identity
  matrices (`1ₘ ~ 1ₙ ↔ |m| = |n|`) and non-equivalence of rank-one matrix units `Eᵢᵢ` with `0` and
  with `1ₘ` (`|m| > 1`);
* comparison with similarity after adding zero blocks (`e ⊕ 0` and `0 ⊕ f` are conjugate by the
  involution `!![1 - e, x; y, 1 - f]`), and comparison of stable equivalence of column ranges with
  stabilized similarity after adding both an identity block `1ₖ` and zero blocks.

## Main definitions

* `Matrix.IsAlgebraicEquivalent`: rectangular algebraic equivalence of square matrices.
* `Matrix.linearEquivRangeMulVecBilinOfMulEq`: the explicit `Rᵐᵒᵖ`-linear isomorphism between
  column ranges induced by normalized witnesses `(x, y)`.
* `Matrix.rangeMulVecBilinOneEquiv`: the column range of `1 : Matrix m m R` is `m → R`.

## Main results

* `Matrix.isAlgebraicEquivalent_self_iff`, `Matrix.IsAlgebraicEquivalent.symm`,
  `Matrix.IsAlgebraicEquivalent.trans`: equivalence-relation laws on idempotent matrices.
* `Matrix.isAlgebraicEquivalent_iff_exists_mul_eq`: corner normalization `(e * x * f, f * y * e)`.
* `Matrix.isAlgebraicEquivalent_one_iff`, `Matrix.not_isAlgebraicEquivalent_single_one_zero`, and
  `Matrix.not_isAlgebraicEquivalent_single_one_one`: size invariance of identity matrices and
  separation of rank-one matrix units `Eᵢᵢ` from `0` and `1` under invariant basis number.
* `Matrix.isAlgebraicEquivalent_iff_nonempty_linearEquiv_range_mulVecBilin` and
  `Matrix.isAlgebraicEquivalent_iff_nonempty_linearEquiv_range_vecMulLinear`: equivalence matches
  isomorphism of column right-modules and of row left-modules.
* `Matrix.isAlgebraicEquivalent_iff_exists_units_conj_fromBlocks_zero`: algebraic equivalence of an
  idempotent `e` with `f` is unit conjugacy of `e ⊕ 0` and `0 ⊕ f`.
* `Matrix.stableEquivalent_range_mulVecBilin_iff` and
  `Matrix.stableEquivalent_range_mulVecBilin_iff_exists_units_conj`: stable equivalence of column
  ranges matches algebraic equivalence after adding `1ₖ`, and unit conjugacy after also adding zero
  blocks.

## References

* J. Rosenberg, *Algebraic K-Theory and Its Applications*, §1.2.
* C. A. Weibel, *The K-book*, Chapter I, §2, and Chapter II, §§1–2.
* B. Blackadar, *K-Theory for Operator Algebras*, §§4.2–4.6.
-/

public section

open LinearMap MulOpposite

namespace Matrix

section Defs

variable {l m m' n n' R : Type*}

/-- Two square matrices `e : Matrix m m R` and `f : Matrix n n R` are *algebraically equivalent* if
there exist rectangular matrices `x : Matrix m n R` and `y : Matrix n m R` with `x * y = e`,
`y * x = f`, `e * x = x`, `x * f = x`, `f * y = y`, and `y * e = y`. -/
def IsAlgebraicEquivalent [Fintype m] [Fintype n] [Mul R] [AddCommMonoid R]
    (e : Matrix m m R) (f : Matrix n n R) : Prop :=
  ∃ (x : Matrix m n R) (y : Matrix n m R),
    x * y = e ∧ y * x = f ∧ e * x = x ∧ x * f = x ∧ f * y = y ∧ y * e = y

theorem isAlgebraicEquivalent_iff [Fintype m] [Fintype n] [Mul R] [AddCommMonoid R]
    {e : Matrix m m R} {f : Matrix n n R} :
    e.IsAlgebraicEquivalent f ↔ ∃ (x : Matrix m n R) (y : Matrix n m R),
      x * y = e ∧ y * x = f ∧ e * x = x ∧ x * f = x ∧ f * y = y ∧ y * e = y :=
  Iff.rfl

/-- Rectangular algebraic equivalence is symmetric. -/
@[symm]
theorem IsAlgebraicEquivalent.symm [Fintype m] [Fintype n] [Mul R] [AddCommMonoid R]
    {e : Matrix m m R} {f : Matrix n n R} (h : e.IsAlgebraicEquivalent f) :
    f.IsAlgebraicEquivalent e := by
  obtain ⟨x, y, hxy, hyx, hex, hxf, hfy, hye⟩ := h
  exact ⟨y, x, hyx, hxy, hfy, hye, hex, hxf⟩

theorem isAlgebraicEquivalent_comm [Fintype m] [Fintype n] [Mul R] [AddCommMonoid R]
    {e : Matrix m m R} {f : Matrix n n R} :
    e.IsAlgebraicEquivalent f ↔ f.IsAlgebraicEquivalent e :=
  ⟨IsAlgebraicEquivalent.symm, IsAlgebraicEquivalent.symm⟩

/-- Simultaneous row-and-column reindexing preserves rectangular algebraic equivalence. -/
theorem IsAlgebraicEquivalent.reindex [Fintype m] [Fintype m'] [Fintype n] [Fintype n']
    [Mul R] [AddCommMonoid R] {e : Matrix m m R} {f : Matrix n n R}
    (h : e.IsAlgebraicEquivalent f) (σ : m ≃ m') (τ : n ≃ n') :
    (e.reindex σ σ).IsAlgebraicEquivalent (f.reindex τ τ) := by
  obtain ⟨x, y, hxy, hyx, hex, hxf, hfy, hye⟩ := h
  refine ⟨x.reindex σ τ, y.reindex τ σ, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [reindex_apply, submatrix_mul_equiv, hxy, hyx, hex, hxf, hfy, hye]

/-- Over any type with multiplication and commutative addition, transpose followed by entrywise
`MulOpposite.op` reverses matrix multiplication. -/
theorem transpose_map_op_mul [Fintype n] [Mul R] [AddCommMonoid R]
    (x : Matrix m n R) (y : Matrix n l R) :
    y.transpose.map op * x.transpose.map op = (x * y).transpose.map op := by
  ext i j
  simp [Matrix.mul_apply]

private theorem transpose_map_unop_mul [Fintype n] [Mul R] [AddCommMonoid R]
    (x : Matrix m n Rᵐᵒᵖ) (y : Matrix n l Rᵐᵒᵖ) :
    y.transpose.map unop * x.transpose.map unop = (x * y).transpose.map unop := by
  ext i j
  simp [Matrix.mul_apply]

/-- Transpose followed by entrywise `MulOpposite.op` preserves and reflects rectangular algebraic
equivalence. -/
theorem isAlgebraicEquivalent_transpose_map_op_iff [Fintype m] [Fintype n] [Mul R]
    [AddCommMonoid R] {e : Matrix m m R} {f : Matrix n n R} :
    (e.transpose.map op).IsAlgebraicEquivalent (f.transpose.map op) ↔
      e.IsAlgebraicEquivalent f := by
  have he_op : (e.transpose.map op).transpose.map unop = e := by ext; simp
  have hf_op : (f.transpose.map op).transpose.map unop = f := by ext; simp
  constructor
  · rintro ⟨x, y, hxy, hyx, hex, hxf, hfy, hye⟩
    exact ⟨y.transpose.map unop, x.transpose.map unop,
      by rw [transpose_map_unop_mul, hxy, he_op],
      by rw [transpose_map_unop_mul, hyx, hf_op],
      by simpa [he_op] using (transpose_map_unop_mul y (e.transpose.map op)).trans (by rw [hye]),
      by simpa [hf_op] using (transpose_map_unop_mul (f.transpose.map op) y).trans (by rw [hfy]),
      by simpa [hf_op] using (transpose_map_unop_mul x (f.transpose.map op)).trans (by rw [hxf]),
      by simpa [he_op] using (transpose_map_unop_mul (e.transpose.map op) x).trans (by rw [hex])⟩
  · rintro ⟨x, y, hxy, hyx, hex, hxf, hfy, hye⟩
    exact ⟨y.transpose.map op, x.transpose.map op,
      by rw [transpose_map_op_mul, hxy], by rw [transpose_map_op_mul, hyx],
      by rw [transpose_map_op_mul, hye], by rw [transpose_map_op_mul, hfy],
      by rw [transpose_map_op_mul, hxf], by rw [transpose_map_op_mul, hex]⟩

/-- An idempotent matrix is algebraically equivalent to itself, witnessed by `(e, e)`. -/
theorem _root_.IsIdempotentElem.isAlgebraicEquivalent_self [Fintype m] [Mul R] [AddCommMonoid R]
    {e : Matrix m m R} (he : IsIdempotentElem e) : e.IsAlgebraicEquivalent e :=
  ⟨e, e, he.eq, he.eq, he.eq, he.eq, he.eq, he.eq⟩

/-- Reindexing an idempotent matrix along an index bijection yields an algebraically equivalent
matrix. -/
theorem _root_.IsIdempotentElem.isAlgebraicEquivalent_reindex [Fintype m] [Fintype m']
    [Mul R] [AddCommMonoid R] {e : Matrix m m R} (he : IsIdempotentElem e) (σ : m ≃ m') :
    (e.reindex σ σ).IsAlgebraicEquivalent e := by
  have he' (a b : m) : ∑ k, e a k * e k b = e a b := congrFun (congrFun he.eq a) b
  refine ⟨e.submatrix σ.symm _root_.id, e.submatrix _root_.id σ.symm, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · ext i j; simp [Matrix.mul_apply, he']
  · ext i j
    simp only [Matrix.mul_apply, submatrix_apply, id_eq]
    exact (σ.symm.sum_comp fun x ↦ e i x * e x j).trans (he' i j)
  · ext i j
    simp only [Matrix.mul_apply, reindex_apply, submatrix_apply, id_eq]
    exact (σ.symm.sum_comp fun x ↦ e (σ.symm i) x * e x j).trans (he' (σ.symm i) j)
  · ext i j; simp [Matrix.mul_apply, he']
  · ext i j; simp [Matrix.mul_apply, he']
  · ext i j
    simp only [Matrix.mul_apply, reindex_apply, submatrix_apply, id_eq]
    exact (σ.symm.sum_comp fun x ↦ e i x * e x (σ.symm j)).trans (he' i (σ.symm j))

end Defs

section NonUnitalNonAssocSemiring

variable {m m₁ m₂ n n₁ n₂ R S F : Type*} [NonUnitalNonAssocSemiring R]

/-- Zero matrices of any two finite sizes are algebraically equivalent. -/
theorem isAlgebraicEquivalent_zero_zero (m n : Type*) [Fintype m] [Fintype n] :
    (0 : Matrix m m R).IsAlgebraicEquivalent (0 : Matrix n n R) :=
  ⟨0, 0, by simp, by simp, by simp, by simp, by simp, by simp⟩

/-- Only the zero matrix is algebraically equivalent to a zero matrix. -/
@[simp]
theorem isAlgebraicEquivalent_zero_iff [Fintype m] [Fintype n] {e : Matrix m m R} :
    e.IsAlgebraicEquivalent (0 : Matrix n n R) ↔ e = 0 := by
  refine ⟨?_, fun h ↦ h ▸ isAlgebraicEquivalent_zero_zero m n⟩
  rintro ⟨x, y, rfl, -, -, hxf, -, -⟩
  rw [← hxf, Matrix.mul_zero, Matrix.zero_mul]

/-- A zero matrix is algebraically equivalent only to the zero matrix. -/
@[simp]
theorem zero_isAlgebraicEquivalent_iff [Fintype m] [Fintype n] {f : Matrix n n R} :
    (0 : Matrix m m R).IsAlgebraicEquivalent f ↔ f = 0 := by
  rw [isAlgebraicEquivalent_comm, isAlgebraicEquivalent_zero_iff]

/-- Entrywise application of a nonunital ring homomorphism preserves matrix idempotence,
generalizing `IsIdempotentElem.matrix_map` from `RingHom` to `NonUnitalRingHomClass`. -/
theorem _root_.IsIdempotentElem.map_nonUnitalRingHom [Fintype m] [NonUnitalNonAssocSemiring S]
    [FunLike F R S] [NonUnitalRingHomClass F R S] {e : Matrix m m R}
    (he : IsIdempotentElem e) (φ : F) :
    IsIdempotentElem (e.map φ) := by
  rw [IsIdempotentElem, ← Matrix.map_mul, he.eq]

/-- Entrywise application of a nonunital ring homomorphism preserves rectangular algebraic
equivalence. -/
theorem IsAlgebraicEquivalent.map [Fintype m] [Fintype n] [NonUnitalNonAssocSemiring S]
    [FunLike F R S] [NonUnitalRingHomClass F R S] {e : Matrix m m R} {f : Matrix n n R}
    (h : e.IsAlgebraicEquivalent f) (φ : F) :
    (e.map φ).IsAlgebraicEquivalent (f.map φ) := by
  obtain ⟨x, y, hxy, hyx, hex, hxf, hfy, hye⟩ := h
  exact ⟨x.map φ, y.map φ, by rw [← Matrix.map_mul, hxy], by rw [← Matrix.map_mul, hyx],
    by rw [← Matrix.map_mul, hex], by rw [← Matrix.map_mul, hxf],
    by rw [← Matrix.map_mul, hfy], by rw [← Matrix.map_mul, hye]⟩

/-- Block direct sums preserve rectangular algebraic equivalence. -/
theorem IsAlgebraicEquivalent.fromBlocks_zero₁₂_zero₂₁ [Fintype m₁] [Fintype m₂] [Fintype n₁]
    [Fintype n₂] {e₁ : Matrix m₁ m₁ R} {f₁ : Matrix n₁ n₁ R} {e₂ : Matrix m₂ m₂ R}
    {f₂ : Matrix n₂ n₂ R} (h₁ : e₁.IsAlgebraicEquivalent f₁) (h₂ : e₂.IsAlgebraicEquivalent f₂) :
    (fromBlocks e₁ 0 0 e₂).IsAlgebraicEquivalent (fromBlocks f₁ 0 0 f₂) := by
  obtain ⟨x₁, y₁, hxy₁, hyx₁, hex₁, hxf₁, hfy₁, hye₁⟩ := h₁
  obtain ⟨x₂, y₂, hxy₂, hyx₂, hex₂, hxf₂, hfy₂, hye₂⟩ := h₂
  refine ⟨fromBlocks x₁ 0 0 x₂, fromBlocks y₁ 0 0 y₂, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [fromBlocks_multiply, hxy₁, hyx₁, hex₁, hxf₁, hfy₁, hye₁,
      hxy₂, hyx₂, hex₂, hxf₂, hfy₂, hye₂]

/-- Padding an idempotent matrix by a lower-right zero block preserves its algebraic equivalence
class. -/
theorem _root_.IsIdempotentElem.isAlgebraicEquivalent_fromBlocks_zero_right (n : Type*)
    [Fintype m] [Fintype n] {e : Matrix m m R} (he : IsIdempotentElem e) :
    (fromBlocks e 0 0 (0 : Matrix n n R)).IsAlgebraicEquivalent e := by
  let x : Matrix (m ⊕ n) m R := of fun i j ↦ match i with | Sum.inl i => e i j | Sum.inr _ => 0
  let y : Matrix m (m ⊕ n) R := of fun i j ↦ match j with | Sum.inl j => e i j | Sum.inr _ => 0
  have he' (i j : m) : ∑ k, e i k * e k j = e i j := congrFun (congrFun he.eq i) j
  refine ⟨x, y, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · ext (i | i) (j | j) <;> simp [x, y, Matrix.mul_apply, he']
  · ext i j; simp [x, y, Matrix.mul_apply, Fintype.sum_sum_type, he']
  · ext (i | i) j <;> simp [x, Matrix.mul_apply, Fintype.sum_sum_type, he']
  · ext (i | i) j <;> simp [x, Matrix.mul_apply, he']
  · ext i (j | j) <;> simp [y, Matrix.mul_apply, he']
  · ext i (j | j) <;> simp [y, Matrix.mul_apply, Fintype.sum_sum_type, he']

/-- Padding an idempotent matrix by an upper-left zero block preserves its algebraic equivalence
class. -/
theorem _root_.IsIdempotentElem.isAlgebraicEquivalent_fromBlocks_zero_left (m : Type*)
    [Fintype m] [Fintype n] {e : Matrix n n R} (he : IsIdempotentElem e) :
    (fromBlocks (0 : Matrix m m R) 0 0 e).IsAlgebraicEquivalent e := by
  have hEq : fromBlocks (0 : Matrix m m R) 0 0 e =
      (fromBlocks e 0 0 (0 : Matrix m m R)).reindex (Equiv.sumComm n m) (Equiv.sumComm n m) := by
    ext (_ | _) (_ | _) <;> rfl
  rw [hEq]
  exact (he.isAlgebraicEquivalent_fromBlocks_zero_right m).reindex
    (Equiv.sumComm n m) (Equiv.refl n)

end NonUnitalNonAssocSemiring

section NonUnitalSemiring

variable {l m n R : Type*} [NonUnitalSemiring R]

/-- The left matrix in a rectangular algebraic equivalence is idempotent. -/
theorem IsAlgebraicEquivalent.isIdempotentElem_left [Fintype m] [Fintype n]
    {e : Matrix m m R} {f : Matrix n n R} (h : e.IsAlgebraicEquivalent f) :
    IsIdempotentElem e := by
  obtain ⟨x, y, rfl, rfl, -, hxf, -, -⟩ := h
  rw [IsIdempotentElem, Matrix.mul_assoc, ← Matrix.mul_assoc y, ← Matrix.mul_assoc x, hxf]

/-- The right matrix in a rectangular algebraic equivalence is idempotent. -/
theorem IsAlgebraicEquivalent.isIdempotentElem_right [Fintype m] [Fintype n]
    {e : Matrix m m R} {f : Matrix n n R} (h : e.IsAlgebraicEquivalent f) :
    IsIdempotentElem f :=
  h.symm.isIdempotentElem_left

/-- A square matrix is algebraically equivalent to itself if and only if it is idempotent. -/
@[simp]
theorem isAlgebraicEquivalent_self_iff [Fintype m] {e : Matrix m m R} :
    e.IsAlgebraicEquivalent e ↔ IsIdempotentElem e :=
  ⟨IsAlgebraicEquivalent.isIdempotentElem_left, IsIdempotentElem.isAlgebraicEquivalent_self⟩

/-- Rectangular algebraic equivalence is transitive. -/
@[trans]
theorem IsAlgebraicEquivalent.trans [Fintype l] [Fintype m] [Fintype n]
    {e : Matrix l l R} {f : Matrix m m R} {g : Matrix n n R}
    (h₁ : e.IsAlgebraicEquivalent f) (h₂ : f.IsAlgebraicEquivalent g) :
    e.IsAlgebraicEquivalent g := by
  obtain ⟨x₁, y₁, hxy₁, hyx₁, hex₁, hxf₁, -, hye₁⟩ := h₁
  obtain ⟨x₂, y₂, hxy₂, hyx₂, -, hxg₂, hgy₂, hyf₂⟩ := h₂
  refine ⟨x₁ * x₂, y₂ * y₁, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc x₂, hxy₂, ← Matrix.mul_assoc, hxf₁, hxy₁]
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc y₁, hyx₁, ← Matrix.mul_assoc, hyf₂, hyx₂]
  · rw [← Matrix.mul_assoc, hex₁]
  · rw [Matrix.mul_assoc, hxg₂]
  · rw [← Matrix.mul_assoc, hgy₂]
  · rw [Matrix.mul_assoc, hye₁]

/-- **Corner normalization of rectangular equivalence.** When `e` and `f` are idempotent, any pair
`(x, y)` with `x * y = e` and `y * x = f` can be replaced by `(e * x * f, f * y * e)` to satisfy all
four corner absorptions. -/
theorem isAlgebraicEquivalent_iff_exists_mul_eq [Fintype m] [Fintype n]
    {e : Matrix m m R} {f : Matrix n n R} (he : IsIdempotentElem e) (hf : IsIdempotentElem f) :
    e.IsAlgebraicEquivalent f ↔
      ∃ (x : Matrix m n R) (y : Matrix n m R), x * y = e ∧ y * x = f := by
  refine ⟨fun ⟨x, y, hxy, hyx, _, _, _, _⟩ ↦ ⟨x, y, hxy, hyx⟩, fun ⟨x, y, hxy, hyx⟩ ↦ ?_⟩
  refine ⟨e * x * f, f * y * e, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · calc
      e * x * f * (f * y * e) = e * (x * (f * f) * y) * e := by simp only [Matrix.mul_assoc]
      _ = e * ((x * y) * (x * y)) * e := by
        rw [hf.eq, ← hyx]
        simp only [Matrix.mul_assoc]
      _ = e := by rw [hxy, he.eq, he.eq, he.eq]
  · calc
      f * y * e * (e * x * f) = f * (y * (e * e) * x) * f := by simp only [Matrix.mul_assoc]
      _ = f * ((y * x) * (y * x)) * f := by
        rw [he.eq, ← hxy]
        simp only [Matrix.mul_assoc]
      _ = f := by rw [hyx, hf.eq, hf.eq, hf.eq]
  · simp only [← Matrix.mul_assoc, he.eq]
  · simp only [Matrix.mul_assoc, hf.eq]
  · simp only [← Matrix.mul_assoc, hf.eq]
  · simp only [Matrix.mul_assoc, he.eq]

end NonUnitalSemiring

section NonAssocSemiring

variable {m n R : Type*} [NonAssocSemiring R]

/-- Any two diagonal matrix units `Eᵢᵢ ∈ Matrix m m R` and `Eⱼⱼ ∈ Matrix n n R` are algebraically
equivalent, witnessed by `Eᵢⱼ` and `Eⱼᵢ`. -/
theorem isAlgebraicEquivalent_single_one [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (i : m) (j : n) :
    (single i i (1 : R)).IsAlgebraicEquivalent (single j j (1 : R)) :=
  ⟨single i j 1, single j i 1, by simp, by simp, by simp, by simp, by simp, by simp⟩

/-- Any diagonal matrix unit `Eᵢᵢ` is algebraically equivalent to the `1 × 1` identity matrix. -/
theorem isAlgebraicEquivalent_single_one_one [Fintype m] [DecidableEq m] (i : m) :
    (single i i (1 : R)).IsAlgebraicEquivalent (1 : Matrix (Fin 1) (Fin 1) R) := by
  have h1 : single (0 : Fin 1) 0 (1 : R) = (1 : Matrix (Fin 1) (Fin 1) R) := by
    ext a b
    fin_cases a
    fin_cases b
    rfl
  exact h1 ▸ isAlgebraicEquivalent_single_one i (0 : Fin 1)

/-- Over a nontrivial nonassociative semiring, a diagonal matrix unit `Eᵢᵢ` is not algebraically
equivalent to a zero matrix. -/
theorem not_isAlgebraicEquivalent_single_one_zero [Nontrivial R] [Fintype m] [Fintype n]
    [DecidableEq m] (i : m) :
    ¬ (single i i (1 : R)).IsAlgebraicEquivalent (0 : Matrix n n R) := by
  rw [isAlgebraicEquivalent_zero_iff]
  intro h
  have hii := congrFun (congrFun h i) i
  simp at hii

end NonAssocSemiring

section Semiring

variable {m n R : Type*} [Semiring R]

/-- Conjugating an idempotent matrix by a matrix unit yields an algebraically equivalent
idempotent matrix. -/
theorem _root_.IsIdempotentElem.isAlgebraicEquivalent_conj_units [Fintype m] [DecidableEq m]
    {e : Matrix m m R} (he : IsIdempotentElem e) (u : (Matrix m m R)ˣ) :
    (u.val * e * u⁻¹.val).IsAlgebraicEquivalent e := by
  refine ⟨u.val * e, e * u⁻¹.val, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc e, he.eq, Matrix.mul_assoc]
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc u⁻¹.val, Units.inv_mul, Matrix.one_mul, he.eq]
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc u⁻¹.val, Units.inv_mul, Matrix.one_mul,
      Matrix.mul_assoc, he.eq]
  · rw [Matrix.mul_assoc, he.eq]
  · rw [← Matrix.mul_assoc, he.eq]
  · rw [← Matrix.mul_assoc (e * u⁻¹.val), ← Matrix.mul_assoc (e * u⁻¹.val),
      Matrix.mul_assoc e u⁻¹.val u.val, Units.inv_mul, Matrix.mul_one, he.eq]

/-- Over a semiring with invariant basis number, two identity matrices are algebraically equivalent
if and only if they have the same size. -/
@[simp]
theorem isAlgebraicEquivalent_one_iff [InvariantBasisNumber R] [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] :
    (1 : Matrix m m R).IsAlgebraicEquivalent (1 : Matrix n n R) ↔
      Fintype.card m = Fintype.card n := by
  refine ⟨fun ⟨x, y, hxy, hyx, _⟩ ↦ Matrix.square_of_invertible x y hxy hyx, fun h ↦ ?_⟩
  obtain ⟨σ⟩ := Fintype.card_eq.mp h.symm
  simpa using (IsIdempotentElem.one (M := Matrix n n R)).isAlgebraicEquivalent_reindex σ

/-- Over a semiring with invariant basis number and any finite index type `m` with at least two
elements, a diagonal matrix unit `Eᵢᵢ` is not algebraically equivalent to `1 : Matrix m m R`. -/
theorem not_isAlgebraicEquivalent_single_one_one [InvariantBasisNumber R] [Fintype m]
    [DecidableEq m] [Nontrivial m] (i : m) :
    ¬ (single i i (1 : R)).IsAlgebraicEquivalent (1 : Matrix m m R) := by
  intro h
  have h1 := (isAlgebraicEquivalent_single_one_one i).symm.trans h
  exact (ne_of_lt Fintype.one_lt_card) (isAlgebraicEquivalent_one_iff.mp h1)

/-- **Mutually inverse module maps from normalized equivalence witnesses.** When `x * y = e`,
`y * x = f`, `e * x = x`, and `f * y = y`, left multiplication by `x` and `y` restrict to mutually
inverse `Rᵐᵒᵖ`-linear maps between `f Rⁿ` and `e Rᵐ`. -/
def linearEquivRangeMulVecBilinOfMulEq [Fintype m] [Fintype n]
    {e : Matrix m m R} {f : Matrix n n R} {x : Matrix m n R} {y : Matrix n m R}
    (hxy : x * y = e) (hyx : y * x = f) (hex : e * x = x) (hfy : f * y = y) :
    range (f.mulVecBilin R Rᵐᵒᵖ) ≃ₗ[Rᵐᵒᵖ] range (e.mulVecBilin R Rᵐᵒᵖ) :=
  have hee : IsIdempotentElem e := by
    rw [IsIdempotentElem]
    nth_rw 2 [← hxy]
    rw [← Matrix.mul_assoc, hex, hxy]
  have hff : IsIdempotentElem f := by
    rw [IsIdempotentElem]
    nth_rw 2 [← hyx]
    rw [← Matrix.mul_assoc, hfy, hyx]
  { toFun v := ⟨x *ᵥ v, ⟨x *ᵥ v, by rw [mulVecBilin_apply, mulVec_mulVec, hex]⟩⟩
    invFun w := ⟨y *ᵥ w, ⟨y *ᵥ w, by rw [mulVecBilin_apply, mulVec_mulVec, hfy]⟩⟩
    map_add' u v := Subtype.ext (mulVec_add x u v)
    map_smul' r v := Subtype.ext (mulVec_smul x r v)
    left_inv v := Subtype.ext <| by
      change y *ᵥ (x *ᵥ (v : n → R)) = v
      rw [mulVec_mulVec, hyx]
      exact hff.mem_range_mulVecBilin_iff.mp v.2
    right_inv w := Subtype.ext <| by
      change x *ᵥ (y *ᵥ (w : m → R)) = w
      rw [mulVec_mulVec, hxy]
      exact hee.mem_range_mulVecBilin_iff.mp w.2 }

@[simp]
theorem coe_linearEquivRangeMulVecBilinOfMulEq_apply [Fintype m] [Fintype n]
    {e : Matrix m m R} {f : Matrix n n R} {x : Matrix m n R} {y : Matrix n m R}
    (hxy : x * y = e) (hyx : y * x = f) (hex : e * x = x) (hfy : f * y = y)
    (v : range (f.mulVecBilin R Rᵐᵒᵖ)) :
    (linearEquivRangeMulVecBilinOfMulEq hxy hyx hex hfy v : m → R) = x *ᵥ v :=
  (rfl)

@[simp]
theorem coe_linearEquivRangeMulVecBilinOfMulEq_symm_apply [Fintype m] [Fintype n]
    {e : Matrix m m R} {f : Matrix n n R} {x : Matrix m n R} {y : Matrix n m R}
    (hxy : x * y = e) (hyx : y * x = f) (hex : e * x = x) (hfy : f * y = y)
    (w : range (e.mulVecBilin R Rᵐᵒᵖ)) :
    ((linearEquivRangeMulVecBilinOfMulEq hxy hyx hex hfy).symm w : n → R) = y *ᵥ w :=
  (rfl)

/-- **Rectangular equivalence matches row-range isomorphism.** Two idempotent matrices over `R` are
algebraically equivalent if and only if their row ranges are isomorphic left `R`-modules. -/
theorem isAlgebraicEquivalent_iff_nonempty_linearEquiv_range_vecMulLinear [Fintype m] [Fintype n]
    {e : Matrix m m R} {f : Matrix n n R} (he : IsIdempotentElem e) (hf : IsIdempotentElem f) :
    e.IsAlgebraicEquivalent f ↔
      Nonempty (range e.vecMulLinear ≃ₗ[R] range f.vecMulLinear) :=
  (isAlgebraicEquivalent_iff_exists_mul_eq he hf).trans
    (nonempty_linearEquiv_range_vecMulLinear_iff he hf).symm

/-- **Rectangular equivalence matches column-range isomorphism.** Two idempotent matrices over `R`
are algebraically equivalent if and only if their column ranges are isomorphic right `R`-modules. -/
theorem isAlgebraicEquivalent_iff_nonempty_linearEquiv_range_mulVecBilin [Fintype m] [Fintype n]
    {e : Matrix m m R} {f : Matrix n n R} (he : IsIdempotentElem e) (hf : IsIdempotentElem f) :
    e.IsAlgebraicEquivalent f ↔
      Nonempty (range (e.mulVecBilin R Rᵐᵒᵖ) ≃ₗ[Rᵐᵒᵖ] range (f.mulVecBilin R Rᵐᵒᵖ)) := by
  rw [← isAlgebraicEquivalent_transpose_map_op_iff,
    isAlgebraicEquivalent_iff_nonempty_linearEquiv_range_vecMulLinear
      he.transpose_map_op hf.transpose_map_op]
  exact ⟨fun ⟨ψ⟩ ↦ ⟨e.rangeMulVecBilinEquivRangeVecMulLinear.trans
      (ψ.trans f.rangeMulVecBilinEquivRangeVecMulLinear.symm)⟩,
    fun ⟨ψ⟩ ↦ ⟨e.rangeMulVecBilinEquivRangeVecMulLinear.symm.trans
      (ψ.trans f.rangeMulVecBilinEquivRangeVecMulLinear)⟩⟩

variable (m R) in
/-- The column range of the identity matrix `1 : Matrix m m R` is `Rᵐᵒᵖ`-linearly isomorphic to
the coordinate column module `m → R`. -/
def rangeMulVecBilinOneEquiv [Fintype m] [DecidableEq m] :
    range ((1 : Matrix m m R).mulVecBilin R Rᵐᵒᵖ) ≃ₗ[Rᵐᵒᵖ] (m → R) where
  toFun v := v
  invFun v := ⟨v, ⟨v, by simp⟩⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

@[simp]
theorem rangeMulVecBilinOneEquiv_apply [Fintype m] [DecidableEq m]
    (v : range ((1 : Matrix m m R).mulVecBilin R Rᵐᵒᵖ)) :
    rangeMulVecBilinOneEquiv m R v = (v : m → R) :=
  (rfl)

/-- **Stable equivalence of column ranges in matrix form.** For idempotent matrices `e` and `f`,
their column ranges are stably equivalent right `R`-modules if and only if `e ⊕ 1ₖ` and `f ⊕ 1ₖ`
are algebraically equivalent for some `k : ℕ`. -/
theorem stableEquivalent_range_mulVecBilin_iff [Fintype m] [Fintype n]
    {e : Matrix m m R} {f : Matrix n n R} (he : IsIdempotentElem e) (hf : IsIdempotentElem f) :
    TauCeti.StableEquivalent Rᵐᵒᵖ
        (range (e.mulVecBilin R Rᵐᵒᵖ)) (range (f.mulVecBilin R Rᵐᵒᵖ)) ↔
      ∃ k : ℕ, (fromBlocks e 0 0 (1 : Matrix (Fin k) (Fin k) R)).IsAlgebraicEquivalent
        (fromBlocks f 0 0 (1 : Matrix (Fin k) (Fin k) R)) := by
  rw [TauCeti.stableEquivalent_iff]
  refine exists_congr fun k ↦ ?_
  rw [isAlgebraicEquivalent_iff_nonempty_linearEquiv_range_mulVecBilin
    (he.fromBlocks_zero₁₂_zero₂₁ IsIdempotentElem.one)
    (hf.fromBlocks_zero₁₂_zero₂₁ IsIdempotentElem.one)]
  let freeEq : range ((1 : Matrix (Fin k) (Fin k) R).mulVecBilin R Rᵐᵒᵖ) ≃ₗ[Rᵐᵒᵖ]
      (Fin k → Rᵐᵒᵖ) :=
    (rangeMulVecBilinOneEquiv (Fin k) R).trans
      (LinearEquiv.piCongrRight fun _ ↦ opLinearEquiv Rᵐᵒᵖ)
  let eqLeft := (rangeMulVecBilinFromBlocksEquiv e (1 : Matrix (Fin k) (Fin k) R)).trans
    ((LinearEquiv.refl Rᵐᵒᵖ _).prodCongr freeEq)
  let eqRight := (rangeMulVecBilinFromBlocksEquiv f (1 : Matrix (Fin k) (Fin k) R)).trans
    ((LinearEquiv.refl Rᵐᵒᵖ _).prodCongr freeEq)
  exact ⟨fun ⟨ψ⟩ ↦ ⟨eqLeft.trans (ψ.trans eqRight.symm)⟩,
    fun ⟨ψ⟩ ↦ ⟨eqLeft.symm.trans (ψ.trans eqRight)⟩⟩

end Semiring

section Ring

variable {m n R : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] [Ring R]

/-- **Algebraically equivalent matrices become unit-conjugate after zero-block stabilization.** If
`e` and `f` are algebraically equivalent, the involution `!![1 - e, x; y, 1 - f]` conjugates
`e ⊕ 0` to `0 ⊕ f`. -/
theorem IsAlgebraicEquivalent.exists_units_conj_fromBlocks_zero
    {e : Matrix m m R} {f : Matrix n n R} (h : e.IsAlgebraicEquivalent f) :
    ∃ u : (Matrix (m ⊕ n) (m ⊕ n) R)ˣ,
      u.val * fromBlocks e 0 0 0 * u⁻¹.val = fromBlocks 0 0 0 f := by
  obtain ⟨x, y, hxy, hyx, hex, -, -, hye⟩ := h
  have hinv := fromBlocks_one_sub_mul_self_of_mul_eq hxy hyx hex hye
  refine ⟨⟨fromBlocks (1 - e) x y (1 - f), fromBlocks (1 - e) x y (1 - f), hinv, hinv⟩, ?_⟩
  exact fromBlocks_one_sub_mul_fromBlocks_mul_fromBlocks_one_sub_of_mul_eq hxy hyx hye

/-- **Algebraic equivalence of an idempotent with another matrix is stabilized similarity.** For an
idempotent matrix `e`, `e` is algebraically equivalent to `f` if and only if `e ⊕ 0` and `0 ⊕ f`
are conjugate by an invertible block matrix. -/
theorem isAlgebraicEquivalent_iff_exists_units_conj_fromBlocks_zero
    {e : Matrix m m R} {f : Matrix n n R} (he : IsIdempotentElem e) :
    e.IsAlgebraicEquivalent f ↔ ∃ u : (Matrix (m ⊕ n) (m ⊕ n) R)ˣ,
      u.val * fromBlocks e 0 0 0 * u⁻¹.val = fromBlocks 0 0 0 f := by
  refine ⟨IsAlgebraicEquivalent.exists_units_conj_fromBlocks_zero, fun ⟨u, hu⟩ ↦ ?_⟩
  have hconj : (fromBlocks (0 : Matrix m m R) 0 0 f).IsAlgebraicEquivalent
      (fromBlocks e 0 0 (0 : Matrix n n R)) := by
    rw [← hu]
    exact (he.fromBlocks_zero₁₂_zero₂₁ IsIdempotentElem.zero).isAlgebraicEquivalent_conj_units u
  have hf : IsIdempotentElem f := by
    have h0f := hconj.isIdempotentElem_left.eq
    rw [fromBlocks_multiply] at h0f
    rw [IsIdempotentElem]
    simpa using congrArg toBlocks₂₂ h0f
  exact (he.isAlgebraicEquivalent_fromBlocks_zero_right n).symm.trans
    (hconj.symm.trans (hf.isAlgebraicEquivalent_fromBlocks_zero_left m))

/-- **Stable equivalence of column ranges is stabilized similarity.** For idempotent matrices `e`
and `f`, their column ranges are stably equivalent right `R`-modules if and only if after adding a
common identity block `1ₖ` and complementary zero blocks, the resulting block matrices are
conjugate by an invertible matrix. -/
theorem stableEquivalent_range_mulVecBilin_iff_exists_units_conj
    {e : Matrix m m R} {f : Matrix n n R} (he : IsIdempotentElem e) (hf : IsIdempotentElem f) :
    TauCeti.StableEquivalent Rᵐᵒᵖ
        (range (e.mulVecBilin R Rᵐᵒᵖ)) (range (f.mulVecBilin R Rᵐᵒᵖ)) ↔
      ∃ (k : ℕ) (u : (Matrix ((m ⊕ Fin k) ⊕ (n ⊕ Fin k)) ((m ⊕ Fin k) ⊕ (n ⊕ Fin k)) R)ˣ),
        u.val * fromBlocks (fromBlocks e 0 0 (1 : Matrix (Fin k) (Fin k) R)) 0 0 0 * u⁻¹.val =
          fromBlocks 0 0 0 (fromBlocks f 0 0 (1 : Matrix (Fin k) (Fin k) R)) := by
  rw [stableEquivalent_range_mulVecBilin_iff he hf]
  exact exists_congr fun k ↦ isAlgebraicEquivalent_iff_exists_units_conj_fromBlocks_zero
    (he.fromBlocks_zero₁₂_zero₂₁ IsIdempotentElem.one)

end Ring

end Matrix
