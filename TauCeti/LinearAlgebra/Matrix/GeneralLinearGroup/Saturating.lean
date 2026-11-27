/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Subalgebra.Matrix
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Elementary
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Idempotent
import TauCeti.LinearAlgebra.Matrix.Range

/-!
# Saturating matrices

Let `S` be a subalgebra of a commutative ring `A`, for instance the integral finite adeles `Ô`
inside the finite adeles `𝔸_f` of a number field, and write `Sⁿ` for the vectors of `Aⁿ` with
entries in `S`. For `g ∈ GL_n(A)`, a matrix `u ∈ GL_n(A)` is **saturating** for `g`
(`Matrix.GeneralLinearGroup.IsSaturating`) if `u` and `g u` have entries in `S` and
`u⁻¹ = l + m g` for matrices `l`, `m` with entries in `S`. Equivalently, `g = (g u) u⁻¹` is a
fraction of the two matrices `g u` and `u` over `S` that is right coprime: `l u + m (g u) = 1`.

The main point is that a saturating matrix computes the lattice `Sⁿ ∩ g⁻¹Sⁿ`: its columns span
it over `S` (`Matrix.GeneralLinearGroup.IsSaturating.span_col_eq`), and two invertible matrices
whose columns span the same `S`-submodule differ by a matrix of `GL_n(S)` on the right
(`Matrix.GeneralLinearGroup.exists_eq_mul_map_of_span_col_eq`). So the class of `det u` modulo
the units of `S` depends on `g` alone. Saturating matrices are compatible with the operations on
`g` that this class sees: `g u` is saturating for `g⁻¹`, `k'⁻¹ u` for `k g k'` with `k`,
`k' ∈ GL_n(S)`, and saturating matrices of two blocks, or of two matrices cut along
complementary idempotents of `S`, assemble to one of the assembled matrix.

Over the finite adeles of a number field saturating matrices exist, and the class of `det u`
modulo the integral units is the multiplier of `g`
(`TauCeti.NumberTheory.NumberField.Global.Adeles.Multiplier`).

## Main declarations

* `Matrix.GeneralLinearGroup.IsSaturating`: saturating matrices.
* `Matrix.GeneralLinearGroup.IsSaturating.span_col_eq`: `u Sⁿ = Sⁿ ∩ g⁻¹ Sⁿ`.
* `Matrix.GeneralLinearGroup.IsSaturating.exists_eq_mul_map`: two saturating matrices of `g`
  differ by an element of `GL_n(S)`.
* `Matrix.GeneralLinearGroup.isSaturating_iff_span_col_transpose_eq`: `u` is saturating for `g`
  exactly when the columns of `(u⁻¹)ᵀ` span `Sⁿ + gᵀ Sⁿ`.
* `Matrix.GeneralLinearGroup.isSaturating_one_of_mem`: `1` is saturating for a matrix with
  entries in `S`.
* `Matrix.GeneralLinearGroup.IsSaturating.inv`, `IsSaturating.map_mul_mul_map`,
  `IsSaturating.mul_map`, `IsSaturating.fromBlocksGL`, `IsSaturating.cutGL_mul_cutGL`: the
  compatibilities with inverses, with `GL_n(S)` on both sides, with block-diagonal matrices and
  with cutting along idempotents.

## References

* G. Shimura, *Euler Products and Eisenstein Series*, CBMS Regional Conference Series in
  Mathematics 93, American Mathematical Society, 1997: coprime fractions of matrices over a
  Dedekind domain and the denominator ideal `det(c)` of `x = c⁻¹ d` (here in the transposed form
  `g = (g u) u⁻¹`).
-/

public section

open Matrix

namespace Matrix.GeneralLinearGroup

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] {S : Subalgebra R A}
variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ### Saturating matrices -/

variable {g u : GL n A}

/-- Entries of `M y` lie in `S` when those of `M` and of `y` do. -/
private theorem mulVec_apply_mem {M : Matrix n n A} (hM : M ∈ S.matrix) {y : n → A}
    (hy : ∀ j, y j ∈ S) (i : n) : (M *ᵥ y) i ∈ S :=
  Subalgebra.sum_mem _ fun j _ ↦ S.mul_mem (hM i j) (hy j)

/-- The image of an invertible matrix over `S` has entries in `S`. -/
private theorem val_map_mem (k : GL n S) : (map S.val.toRingHom k : Matrix n n A) ∈ S.matrix :=
  fun i j ↦ ((k : Matrix n n S) i j).property

variable (S) in
/-- For `g ∈ GL_n(A)`, a matrix `u ∈ GL_n(A)` is **saturating** for `g`, relative to the
subalgebra `S`, if `u` and `g u` have entries in `S` and `u⁻¹ = l + m g` for matrices `l`, `m`
with entries in `S`. Then the columns of `u` span `Sⁿ ∩ g⁻¹Sⁿ` over `S`
(`Matrix.GeneralLinearGroup.IsSaturating.span_col_eq`). -/
structure IsSaturating (g u : GL n A) : Prop where
  /-- The entries of `u` lie in `S`. -/
  val_mem : (u : Matrix n n A) ∈ S.matrix
  /-- The entries of `g u` lie in `S`. -/
  mul_val_mem : (g : Matrix n n A) * (u : Matrix n n A) ∈ S.matrix
  /-- `u⁻¹ = l + m g` for matrices `l`, `m` with entries in `S`. -/
  exists_inv_eq : ∃ l ∈ S.matrix, ∃ m ∈ S.matrix,
    ((u⁻¹ : GL n A) : Matrix n n A) = l + m * (g : Matrix n n A)

/-- **A saturating matrix computes `Sⁿ ∩ g⁻¹Sⁿ`.** If `u` is saturating for `g`, the `S`-span of
the columns of `u` is the set of `x ∈ Sⁿ` with `g x ∈ Sⁿ`. -/
theorem IsSaturating.span_col_eq (h : IsSaturating S g u) :
    Submodule.span S (Set.range (u : Matrix n n A).col) =
      Submodule.span S (Set.range (1 : Matrix n n A).col) ⊓
        Submodule.span S (Set.range ((g⁻¹ : GL n A) : Matrix n n A).col) := by
  obtain ⟨l, hl, m, hm, hlm⟩ := h.exists_inv_eq
  ext x
  rw [Submodule.mem_inf, mem_span_col_one_iff, mem_span_col_iff_mulVec_inv_mem,
    mem_span_col_iff_mulVec_inv_mem, inv_inv]
  constructor
  · intro hx
    -- `x = u (u⁻¹ x)` and `g x = (g u) (u⁻¹ x)`.
    refine ⟨fun i ↦ ?_, fun i ↦ ?_⟩
    · simpa [mulVec_mulVec] using mulVec_apply_mem h.val_mem hx i
    · simpa [mulVec_mulVec, Matrix.mul_assoc] using mulVec_apply_mem h.mul_val_mem hx i
  · rintro ⟨hx, hgx⟩ i
    -- `u⁻¹ x = l x + m (g x)`.
    rw [hlm, add_mulVec, ← mulVec_mulVec]
    exact S.add_mem (mulVec_apply_mem hl hx i) (mulVec_apply_mem hm hgx i)

/-- **Uniqueness of saturating matrices.** Two saturating matrices `u`, `u'` of `g` differ by an
element of `GL_n(S)`: `u' = u k`. -/
theorem IsSaturating.exists_eq_mul_map {u' : GL n A} (h : IsSaturating S g u)
    (h' : IsSaturating S g u') : ∃ k : GL n S, u' = u * map S.val.toRingHom k :=
  exists_eq_mul_map_of_span_col_eq (h.span_col_eq.trans h'.span_col_eq.symm)

/-- If every column of `B` lies in the `S`-span of the columns of `w ∈ GL_n(A)`, then `w⁻¹ B` has
entries in `S`. -/
private theorem inv_mul_mem_of_col_mem (w : GL n A) {B : Matrix n n A}
    (hB : ∀ j, B.col j ∈ Submodule.span S (Set.range (w : Matrix n n A).col)) :
    ((w⁻¹ : GL n A) : Matrix n n A) * B ∈ S.matrix := fun i j ↦ by
  simpa [mulVec, dotProduct, Matrix.mul_apply] using
    (mem_span_col_iff_mulVec_inv_mem w).1 (hB j) i

/-- The inverse of the transpose `(u⁻¹)ᵀ` of `u⁻¹` is `uᵀ`. -/
private theorem coe_inv_unop_transposeMulEquiv_inv (u : GL n A) :
    ((((transposeMulEquiv n u⁻¹).unop)⁻¹ : GL n A) : Matrix n n A) = (u : Matrix n n A)ᵀ := by
  rw [← MulOpposite.unop_inv, ← map_inv, inv_inv, coe_unop_transposeMulEquiv]

/-- If the columns of `(u⁻¹)ᵀ` span `Sⁿ + gᵀ Sⁿ` over `S`, then `u` is saturating for `g`. -/
private theorem isSaturating_of_span_col_transpose_eq
    (hspan : Submodule.span S (Set.range ((u⁻¹ : GL n A) : Matrix n n A)ᵀ.col) =
      Submodule.span S (Set.range (1 : Matrix n n A).col) ⊔
        Submodule.span S (Set.range (g : Matrix n n A)ᵀ.col)) :
    IsSaturating S g u := by
  -- `w = (u⁻¹)ᵀ` is invertible, with inverse `uᵀ`.
  set w : GL n A := (transposeMulEquiv n u⁻¹).unop
  have hw_inv := coe_inv_unop_transposeMulEquiv_inv u
  -- The columns of `1` and of `gᵀ` lie in the span of those of `w`, so `w⁻¹ = uᵀ` and
  -- `w⁻¹ gᵀ = (g u)ᵀ` have entries in `S`.
  have hu := inv_mul_mem_of_col_mem w (B := 1) fun j ↦
    hspan.ge (Submodule.mem_sup_left (Submodule.subset_span ⟨j, rfl⟩))
  have hgu := inv_mul_mem_of_col_mem w (B := (g : Matrix n n A)ᵀ) fun j ↦
    hspan.ge (Submodule.mem_sup_right (Submodule.subset_span ⟨j, rfl⟩))
  rw [Matrix.mul_one, hw_inv] at hu
  rw [hw_inv, ← transpose_mul] at hgu
  -- Each column of `w` is `y + gᵀ b` with `y`, `b` in `Sⁿ`.
  have hcol (j : n) : ∃ y : n → A, (∀ i, y i ∈ S) ∧ ∃ b : n → A, (∀ i, b i ∈ S) ∧
      y + (g : Matrix n n A)ᵀ *ᵥ b = (w : Matrix n n A).col j := by
    obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.1 (hspan.le (Submodule.subset_span ⟨j, rfl⟩))
    obtain ⟨b, hb, rfl⟩ := mem_span_col_iff.1 hz
    exact ⟨y, mem_span_col_one_iff.1 hy, b, hb, hyz⟩
  choose y hy b hb hyb using hcol
  -- Then `u⁻¹ = wᵀ = yᵀ + bᵀ g`.
  refine ⟨fun i j ↦ hu j i, fun i j ↦ hgu j i, Matrix.of fun i j ↦ y i j, fun i j ↦ hy i j,
    Matrix.of fun i j ↦ b i j, fun i j ↦ hb i j, ?_⟩
  ext i j
  have h := congrFun (hyb i) j
  simp only [Pi.add_apply, mulVec, dotProduct, transpose_apply, col_apply, w,
    coe_unop_transposeMulEquiv] at h
  simp [← h, Matrix.mul_apply, mul_comm]

/-- **The row lattice of a saturating matrix.** A matrix `u` is saturating for `g` exactly when
the rows of `u⁻¹` span `Sⁿ + Sⁿ g` over `S`, that is, when the columns of `(u⁻¹)ᵀ` span
`Sⁿ + gᵀ Sⁿ`. -/
theorem isSaturating_iff_span_col_transpose_eq :
    IsSaturating S g u ↔
      Submodule.span S (Set.range ((u⁻¹ : GL n A) : Matrix n n A)ᵀ.col) =
        Submodule.span S (Set.range (1 : Matrix n n A).col) ⊔
          Submodule.span S (Set.range (g : Matrix n n A)ᵀ.col) := by
  refine ⟨fun ⟨hu, hgu, l, hl, m, hm, hlm⟩ ↦ ?_, isSaturating_of_span_col_transpose_eq⟩
  -- `w = (u⁻¹)ᵀ` is invertible, with inverse `uᵀ`.
  set w : GL n A := (transposeMulEquiv n u⁻¹).unop
  have hw : (w : Matrix n n A) = ((u⁻¹ : GL n A) : Matrix n n A)ᵀ := rfl
  have hw_inv := coe_inv_unop_transposeMulEquiv_inv u
  rw [← hw]
  refine le_antisymm (Submodule.span_le.2 ?_) (sup_le (fun x hx ↦ ?_) (fun x hx ↦ ?_))
  · -- The `j`-th column of `(u⁻¹)ᵀ = lᵀ + gᵀ mᵀ` lies in `Sⁿ + gᵀ Sⁿ`.
    rintro _ ⟨j, rfl⟩
    have hcol : (w : Matrix n n A).col j = lᵀ.col j + (g : Matrix n n A)ᵀ *ᵥ mᵀ.col j := by
      ext i
      simp [hw, hlm, mulVec, dotProduct, Matrix.mul_apply, mul_comm]
    rw [SetLike.mem_coe, hcol]
    exact Submodule.add_mem_sup (mem_span_col_one_iff.2 fun i ↦ hl j i)
      (mem_span_col_iff.2 ⟨_, fun i ↦ hm j i, rfl⟩)
  · -- `w⁻¹ x = uᵀ x`.
    rw [mem_span_col_iff_mulVec_inv_mem, hw_inv]
    exact mulVec_apply_mem (fun i j ↦ hu j i) (mem_span_col_one_iff.1 hx)
  · -- `w⁻¹ gᵀ y = (g u)ᵀ y`.
    obtain ⟨y, hy, rfl⟩ := mem_span_col_iff.1 hx
    rw [mem_span_col_iff_mulVec_inv_mem, hw_inv, mulVec_mulVec, ← transpose_mul]
    exact mulVec_apply_mem (fun i j ↦ hgu j i) hy

/-- A matrix with entries in `S` has `1` as a saturating matrix. -/
theorem isSaturating_one_of_mem (hg : (g : Matrix n n A) ∈ S.matrix) : IsSaturating S g 1 where
  val_mem := one_mem _
  mul_val_mem := by rwa [Units.val_one, Matrix.mul_one]
  exists_inv_eq := ⟨1, one_mem _, 0, zero_mem _, by simp⟩

/-- Multiplying a saturating matrix on the right by an element of `GL_n(S)` gives a saturating
matrix. -/
theorem IsSaturating.mul_map (h : IsSaturating S g u) (k : GL n S) :
    IsSaturating S g (u * map S.val.toRingHom k) := by
  obtain ⟨l, hl, m, hm, hlm⟩ := h.exists_inv_eq
  have hk := val_map_mem k
  have hk' := val_map_mem k⁻¹
  rw [map_inv] at hk'
  refine ⟨?_, ?_, ((map S.val.toRingHom k)⁻¹ : GL n A) * l, mul_mem hk' hl,
    ((map S.val.toRingHom k)⁻¹ : GL n A) * m, mul_mem hk' hm, ?_⟩
  · rw [Units.val_mul]
    exact mul_mem h.val_mem hk
  · rw [Units.val_mul, ← Matrix.mul_assoc]
    exact mul_mem h.mul_val_mem hk
  · rw [_root_.mul_inv_rev, Units.val_mul, hlm, Matrix.mul_add, Matrix.mul_assoc]

/-- If `u` is saturating for `g`, then `k'⁻¹ u` is saturating for `k g k'`, for `k`,
`k' ∈ GL_n(S)`. -/
theorem IsSaturating.map_mul_mul_map (h : IsSaturating S g u) (k k' : GL n S) :
    IsSaturating S (map S.val.toRingHom k * g * map S.val.toRingHom k')
      ((map S.val.toRingHom k')⁻¹ * u) := by
  obtain ⟨l, hl, m, hm, hlm⟩ := h.exists_inv_eq
  have hk' := val_map_mem k'
  have hk_inv := val_map_mem k⁻¹
  have hk'_inv := val_map_mem k'⁻¹
  rw [map_inv] at hk_inv hk'_inv
  refine ⟨?_, ?_, l * map S.val.toRingHom k', mul_mem hl hk',
    m * ((map S.val.toRingHom k)⁻¹ : GL n A), mul_mem hm hk_inv, ?_⟩
  · rw [Units.val_mul]
    exact mul_mem hk'_inv h.val_mem
  · -- `(k g k') (k'⁻¹ u) = k (g u)`.
    have h_mul : ((map S.val.toRingHom k * g * map S.val.toRingHom k' : GL n A) :
        Matrix n n A) * ((map S.val.toRingHom k')⁻¹ * u : GL n A) =
          (map S.val.toRingHom k : Matrix n n A) * ((g : Matrix n n A) * (u : Matrix n n A)) := by
      simp only [← Units.val_mul, mul_assoc, mul_inv_cancel_left]
    rw [h_mul]
    exact mul_mem (val_map_mem k) h.mul_val_mem
  · -- `(k'⁻¹ u)⁻¹ = u⁻¹ k' = l k' + m k⁻¹ (k g k')`.
    rw [_root_.mul_inv_rev, inv_inv, Units.val_mul, hlm, Matrix.add_mul]
    simp only [Units.val_mul, Matrix.mul_assoc, Units.inv_mul_cancel_left]

/-- **Saturating matrices of the inverse.** If `u` is saturating for `g`, then `g u` is
saturating for `g⁻¹`. -/
theorem IsSaturating.inv (h : IsSaturating S g u) : IsSaturating S g⁻¹ (g * u) := by
  obtain ⟨l, hl, m, hm, hlm⟩ := h.exists_inv_eq
  refine ⟨?_, ?_, m, hm, l, hl, ?_⟩
  · rw [Units.val_mul]
    exact h.mul_val_mem
  · rw [Units.val_mul, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
    exact h.val_mem
  · -- `(g u)⁻¹ = u⁻¹ g⁻¹ = (l + m g) g⁻¹ = m + l g⁻¹`.
    rw [_root_.mul_inv_rev, Units.val_mul, hlm, Matrix.add_mul, Matrix.mul_assoc, Units.mul_inv,
      Matrix.mul_one, add_comm]

/-- Saturating matrices of two blocks assemble to a saturating matrix of the block-diagonal
matrix. -/
theorem IsSaturating.fromBlocksGL {m : Type*} [Fintype m] [DecidableEq m] {g₁ u₁ : GL n A}
    {g₂ u₂ : GL m A} (h₁ : IsSaturating S g₁ u₁) (h₂ : IsSaturating S g₂ u₂) :
    IsSaturating S (TauCeti.fromBlocksGL (g₁, g₂)) (TauCeti.fromBlocksGL (u₁, u₂)) := by
  obtain ⟨l₁, hl₁, m₁, hm₁, hlm₁⟩ := h₁.exists_inv_eq
  obtain ⟨l₂, hl₂, m₂, hm₂, hlm₂⟩ := h₂.exists_inv_eq
  have h_mem {P : Matrix n n A} {Q : Matrix m m A} (hP : P ∈ S.matrix) (hQ : Q ∈ S.matrix) :
      fromBlocks P 0 0 Q ∈ S.matrix := by
    rintro (i | i) (j | j)
    exacts [hP i j, zero_mem S, zero_mem S, hQ i j]
  refine ⟨?_, ?_, fromBlocks l₁ 0 0 l₂, h_mem hl₁ hl₂, fromBlocks m₁ 0 0 m₂, h_mem hm₁ hm₂, ?_⟩
  · rw [TauCeti.coe_fromBlocksGL]
    exact h_mem h₁.val_mem h₂.val_mem
  · simp only [TauCeti.coe_fromBlocksGL, fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul,
      add_zero, zero_add]
    exact h_mem h₁.mul_val_mem h₂.mul_val_mem
  · rw [← map_inv, TauCeti.coe_fromBlocksGL, Prod.fst_inv, Prod.snd_inv, hlm₁, hlm₂,
      TauCeti.coe_fromBlocksGL, fromBlocks_multiply, fromBlocks_add]
    simp

omit [DecidableEq n] in
/-- For an idempotent `e`, `(e • a + (1 - e) • b) (e • c + (1 - e) • d) = e • a c + (1 - e) • b d`:
matrices cut along `e` and `1 - e` multiply blockwise. -/
private theorem smul_add_smul_mul_smul_add_smul {e : A} (he : IsIdempotentElem e)
    (a b c d : Matrix n n A) :
    (e • a + (1 - e) • b) * (e • c + (1 - e) • d) = e • (a * c) + (1 - e) • (b * d) := by
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_add,
    smul_smul, he.eq, he.one_sub.eq, he.mul_one_sub_self, he.one_sub_mul_self, zero_smul,
    add_zero, zero_add]

/-- The matrix underlying `he.cutGL a * he.one_sub.cutGL b` is `e • a + (1 - e) • b`. -/
private theorem val_cutGL_mul_cutGL {e : A} (he : IsIdempotentElem e) (a b : GL n A) :
    ((he.cutGL a * he.one_sub.cutGL b : GL n A) : Matrix n n A) =
      e • (a : Matrix n n A) + (1 - e) • (b : Matrix n n A) := by
  have h := smul_add_smul_mul_smul_add_smul he (a : Matrix n n A) 1 1 b
  rw [Matrix.mul_one, Matrix.one_mul] at h
  rw [Units.val_mul, IsIdempotentElem.val_cutGL, IsIdempotentElem.val_cutGL, sub_sub_cancel,
    add_comm (_ • (b : Matrix n n A)), h]

/-- The matrix underlying the inverse of `he.cutGL a * he.one_sub.cutGL b` is
`e • a⁻¹ + (1 - e) • b⁻¹`. -/
private theorem val_inv_cutGL_mul_cutGL {e : A} (he : IsIdempotentElem e) (a b : GL n A) :
    (((he.cutGL a * he.one_sub.cutGL b)⁻¹ : GL n A) : Matrix n n A) =
      e • ((a⁻¹ : GL n A) : Matrix n n A) + (1 - e) • ((b⁻¹ : GL n A) : Matrix n n A) := by
  have h := smul_add_smul_mul_smul_add_smul he 1 ((b⁻¹ : GL n A) : Matrix n n A)
    ((a⁻¹ : GL n A) : Matrix n n A) 1
  rw [Matrix.mul_one, Matrix.one_mul] at h
  rw [_root_.mul_inv_rev, Units.val_mul, ← map_inv, ← map_inv, IsIdempotentElem.val_cutGL,
    IsIdempotentElem.val_cutGL, sub_sub_cancel, add_comm ((1 - e) • _), h]

/-- **Cutting along an idempotent.** Let `e ∈ S` be an idempotent. If `u₁` is saturating for
`g₁` and `u₂` for `g₂`, then the matrix equal to `u₁` along `e` and to `u₂` along `1 - e` is
saturating for the matrix equal to `g₁` along `e` and to `g₂` along `1 - e`. -/
theorem IsSaturating.cutGL_mul_cutGL {e : A} (he : IsIdempotentElem e) (heS : e ∈ S)
    {g₁ g₂ u₁ u₂ : GL n A} (h₁ : IsSaturating S g₁ u₁) (h₂ : IsSaturating S g₂ u₂) :
    IsSaturating S (he.cutGL g₁ * he.one_sub.cutGL g₂) (he.cutGL u₁ * he.one_sub.cutGL u₂) := by
  obtain ⟨l₁, hl₁, m₁, hm₁, hlm₁⟩ := h₁.exists_inv_eq
  obtain ⟨l₂, hl₂, m₂, hm₂, hlm₂⟩ := h₂.exists_inv_eq
  have h_mem {P Q : Matrix n n A} (hP : P ∈ S.matrix) (hQ : Q ∈ S.matrix) :
      e • P + (1 - e) • Q ∈ S.matrix := fun i j ↦
    S.add_mem (S.mul_mem heS (hP i j)) (S.mul_mem (S.sub_mem (S.one_mem) heS) (hQ i j))
  refine ⟨?_, ?_, e • l₁ + (1 - e) • l₂, h_mem hl₁ hl₂, e • m₁ + (1 - e) • m₂, h_mem hm₁ hm₂, ?_⟩
  · rw [val_cutGL_mul_cutGL]
    exact h_mem h₁.val_mem h₂.val_mem
  · rw [val_cutGL_mul_cutGL, val_cutGL_mul_cutGL, smul_add_smul_mul_smul_add_smul he]
    exact h_mem h₁.mul_val_mem h₂.mul_val_mem
  · rw [val_inv_cutGL_mul_cutGL, val_cutGL_mul_cutGL, smul_add_smul_mul_smul_add_smul he, hlm₁,
      hlm₂, smul_add, smul_add]
    abel

end Matrix.GeneralLinearGroup
