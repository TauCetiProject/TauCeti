/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Hom
public import Mathlib.Data.Matrix.PEquiv
public import TauCeti.Analysis.CStarAlgebra.CStarMatrix.Basic
import TauCeti.Data.Matrix.Block

/-!
# Rectangular norms, reindexing, and permutation matrices on `CStarMatrix`

Mathlib equips square matrices `CStarMatrix n n A` over a C⋆-algebra `A` with a C⋆-algebra
structure and rectangular matrices `CStarMatrix m n A` with their operator norm on the right
Hilbert `A`-module `n → A`. Operator-algebraic constructions across different matrix sizes—such as
Murray–von Neumann equivalence `p = vᴴ * v`, `q = v * vᴴ` via rectangular matrices, rectangular
block decompositions, and coordinate equivalences `e : m ≃ n`—also require rectangular
multiplication, conjugate transposition, and reindexing to interact cleanly with that operator norm.

This file develops the rectangular calculus for `CStarMatrix`:

* Rectangular algebraic, conjugate-transpose, entrywise map, and proper-star cancellation
  identities (`Mᴴ * M = 0 ↔ M = 0` and `(Mᴴ * M) * N = 0 ↔ M * N = 0`).
* Rectangular operator-norm submultiplicativity `‖M * N‖ ≤ ‖M‖ * ‖N‖` and the rectangular
  C⋆-identities `‖M.conjTranspose‖ = ‖M‖`, `‖M * M.conjTranspose‖ = ‖M‖ ^ 2`, and
  `‖M.conjTranspose * M‖ = ‖M‖ ^ 2`.
* Rectangular row-and-column reindexing `CStarMatrix.reindexₗᵢ` as a linear isometry equivalence,
  together with rectangular `0`-`1` permutation matrices `CStarMatrix.permMatrix` implementing
  `CStarMatrix.reindexₐ` by conjugation.

## Main declarations

* `CStarMatrix.conjTranspose_mul_self_eq_zero`, `CStarMatrix.conjTranspose_mul_self_mul_eq_zero`:
  proper-star cancellation laws for rectangular `CStarMatrix` values.
* `CStarMatrix.norm_hMul_le`, `CStarMatrix.norm_conjTranspose`,
  `CStarMatrix.norm_self_mul_conjTranspose`, `CStarMatrix.norm_conjTranspose_mul_self`:
  rectangular operator-norm submultiplicativity and C⋆-identities.
* `CStarMatrix.reindexₗᵢ`: rectangular row-and-column reindexing as a linear isometry equivalence.
* `CStarMatrix.permMatrix`: rectangular `0`-`1` matrices attached to `e : m ≃ n`, implementing
  `reindexₐ` by `(permMatrix A e).conjTranspose * M * permMatrix A e = reindexₐ R A e M`.

## References

* B. Blackadar, *K-Theory for Operator Algebras*, 2nd ed., §3.1 and §4.1.
* M. Rørdam, F. Larsen, and N. Laustsen, *An Introduction to K-Theory for C⋆-Algebras*, Chapter 2.
* E. C. Lance, *Hilbert C⋆-Modules: A Toolkit for Operator Algebraists*, Chapter 4.
-/

public section

open scoped Matrix InnerProductSpace WithCStarModule

namespace CStarMatrix

section RectangularAlgebraic

variable {k l m n o p q R A B : Type*}

/-- Reading a product of rectangular `CStarMatrix` values as an ordinary matrix respects
multiplication. -/
@[simp]
theorem ofMatrix_symm_hMul [Fintype m] [Mul A] [AddCommMonoid A]
    (M : CStarMatrix l m A) (N : CStarMatrix m n A) :
    ofMatrix.symm (M * N) = ofMatrix.symm M * ofMatrix.symm N := (rfl)

/-- `ofMatrix` transports rectangular matrix multiplication to `CStarMatrix` multiplication. -/
@[simp]
theorem of_mul_of [Fintype m] [Mul A] [AddCommMonoid A]
    (M : Matrix l m A) (N : Matrix m n A) :
    ofMatrix M * ofMatrix N = ofMatrix (M * N) := (rfl)

/-- Reading a rectangular `CStarMatrix` as an ordinary matrix sends `conjTranspose` to `ᴴ`. -/
@[simp]
theorem ofMatrix_symm_conjTranspose [Star A] (M : CStarMatrix m n A) :
    ofMatrix.symm M.conjTranspose = (ofMatrix.symm M)ᴴ := (rfl)

/-- `ofMatrix` commutes with conjugate transposition. -/
@[simp]
theorem conjTranspose_of [Star A] (M : Matrix m n A) :
    (ofMatrix M).conjTranspose = ofMatrix Mᴴ := (rfl)

/-- Rectangular matrix multiplication on `CStarMatrix` is associative. -/
protected theorem mul_assoc [Fintype l] [Fintype m] [NonUnitalSemiring A]
    (L : CStarMatrix k l A) (M : CStarMatrix l m A) (N : CStarMatrix m n A) :
    L * M * N = L * (M * N) :=
  Matrix.mul_assoc L M N

/-- Left multiplication by the identity `CStarMatrix` is the identity on rectangular matrices. -/
@[simp]
protected theorem one_mul [Fintype m] [DecidableEq m] [NonAssocSemiring A]
    (M : CStarMatrix m n A) : (1 : CStarMatrix m m A) * M = M :=
  Matrix.one_mul M

/-- Right multiplication by the identity `CStarMatrix` is the identity on rectangular matrices. -/
@[simp]
protected theorem mul_one [Fintype n] [DecidableEq n] [NonAssocSemiring A]
    (M : CStarMatrix m n A) : M * (1 : CStarMatrix n n A) = M :=
  Matrix.mul_one M

/-- Rectangular left multiplication distributes over subtraction. -/
protected theorem mul_sub [Fintype m] [NonUnitalNonAssocRing A]
    (L : CStarMatrix l m A) (M N : CStarMatrix m n A) :
    L * (M - N) = L * M - L * N :=
  Matrix.mul_sub L M N

/-- Rectangular right multiplication distributes over subtraction. -/
protected theorem sub_mul [Fintype m] [NonUnitalNonAssocRing A]
    (L M : CStarMatrix l m A) (N : CStarMatrix m n A) :
    (L - M) * N = L * N - M * N :=
  Matrix.sub_mul L M N

/-- Rectangular left multiplication commutes with negation. -/
@[simp]
protected theorem mul_neg [Fintype m] [NonUnitalNonAssocRing A]
    (M : CStarMatrix l m A) (N : CStarMatrix m n A) :
    M * (-N) = -(M * N) :=
  Matrix.mul_neg M N

/-- Rectangular right multiplication commutes with negation. -/
@[simp]
protected theorem neg_mul [Fintype m] [NonUnitalNonAssocRing A]
    (M : CStarMatrix l m A) (N : CStarMatrix m n A) :
    (-M) * N = -(M * N) :=
  Matrix.neg_mul M N

/-- Conjugate transposition on rectangular `CStarMatrix` is an involution. -/
@[simp]
theorem conjTranspose_conjTranspose [InvolutiveStar A] (M : CStarMatrix m n A) :
    M.conjTranspose.conjTranspose = M :=
  Matrix.conjTranspose_conjTranspose M

/-- The conjugate transpose of the identity `CStarMatrix` is the identity. -/
@[simp]
theorem conjTranspose_one [DecidableEq n] [Semiring A] [StarRing A] :
    (1 : CStarMatrix n n A).conjTranspose = 1 :=
  Matrix.conjTranspose_one

/-- Conjugate transposition distributes over addition. -/
@[simp]
theorem conjTranspose_add [AddMonoid A] [StarAddMonoid A] (M N : CStarMatrix m n A) :
    (M + N).conjTranspose = M.conjTranspose + N.conjTranspose :=
  Matrix.conjTranspose_add M N

/-- Conjugate transposition commutes with negation. -/
@[simp]
theorem conjTranspose_neg [AddGroup A] [StarAddMonoid A] (M : CStarMatrix m n A) :
    (-M).conjTranspose = -M.conjTranspose :=
  Matrix.conjTranspose_neg M

/-- Conjugate transposition distributes over subtraction. -/
@[simp]
theorem conjTranspose_sub [AddGroup A] [StarAddMonoid A] (M N : CStarMatrix m n A) :
    (M - N).conjTranspose = M.conjTranspose - N.conjTranspose :=
  Matrix.conjTranspose_sub M N

/-- Conjugate transposition is conjugate-linear with respect to scalar multiplication. -/
@[simp]
theorem conjTranspose_smul [Star R] [Star A] [SMul R A] [StarModule R A]
    (c : R) (M : CStarMatrix m n A) :
    (c • M).conjTranspose = star c • M.conjTranspose :=
  Matrix.conjTranspose_smul c M

/-- Conjugate transposition reverses rectangular matrix products. -/
@[simp]
theorem conjTranspose_mul [Fintype m] [NonUnitalSemiring A] [StarRing A]
    (M : CStarMatrix l m A) (N : CStarMatrix m n A) :
    (M * N).conjTranspose = N.conjTranspose * M.conjTranspose :=
  Matrix.conjTranspose_mul M N

/-- A rectangular `CStarMatrix` vanishes iff its conjugate transpose vanishes. -/
@[simp]
theorem conjTranspose_eq_zero [AddMonoid A] [StarAddMonoid A] {M : CStarMatrix m n A} :
    M.conjTranspose = 0 ↔ M = 0 :=
  Matrix.conjTranspose_eq_zero

/-- Applying a non-unital ring homomorphism entrywise commutes with rectangular multiplication. -/
theorem map_mul [Fintype m] [NonUnitalNonAssocSemiring A] [NonUnitalNonAssocSemiring B]
    {F : Type*} [FunLike F A B] [NonUnitalRingHomClass F A B]
    (f : F) (M : CStarMatrix l m A) (N : CStarMatrix m n A) :
    (M * N).map f = M.map f * N.map f := by
  ext i j
  simp [mul_apply, map_sum, _root_.map_mul]

/-- Applying a `⋆`-preserving map entrywise commutes with `conjTranspose`. -/
theorem map_conjTranspose [Star A] [Star B] {F : Type*} [FunLike F A B] [StarHomClass F A B]
    (f : F) (M : CStarMatrix m n A) :
    M.conjTranspose.map f = (M.map f).conjTranspose := by
  ext i j
  simp [map_star]

/-- `CStarMatrix.mapₙₐ f M` applies `f` entrywise via `CStarMatrix.map`. -/
theorem mapₙₐ_eq_map [Fintype n] [Semiring R] [NonUnitalNonAssocSemiring A] [Module R A]
    [Star A] [NonUnitalNonAssocSemiring B] [Module R B] [Star B]
    (f : A →⋆ₙₐ[R] B) (M : CStarMatrix n n A) :
    mapₙₐ f M = M.map f := (rfl)

/-- Evaluating `reindexₗ R A e₁ e₂ M` at `(i, j)` looks up `M (e₁.symm i) (e₂.symm j)`. -/
theorem reindexₗ_apply_eq [Semiring R] [AddCommMonoid A] [Module R A]
    (e₁ : m ≃ l) (e₂ : n ≃ o) (M : CStarMatrix m n A) (i : l) (j : o) :
    reindexₗ R A e₁ e₂ M i j = M (e₁.symm i) (e₂.symm j) := (rfl)

/-- Rectangular row-and-column reindexing respects matrix multiplication when the inner index
equivalences match. -/
theorem reindexₗ_mul [Fintype m] [Fintype o] [Semiring R] [NonUnitalNonAssocSemiring A] [Module R A]
    (e₁ : l ≃ n) (e₂ : m ≃ o) (e₃ : p ≃ q)
    (M : CStarMatrix l m A) (N : CStarMatrix m p A) :
    reindexₗ R A e₁ e₂ M * reindexₗ R A e₂ e₃ N = reindexₗ R A e₁ e₃ (M * N) := by
  ext i k
  simp only [mul_apply, reindexₗ_apply_eq]
  refine (Fintype.sum_equiv e₂ _ _ fun j ↦ ?_).symm
  simp

/-- Rectangular row-and-column reindexing swaps equivalences under `conjTranspose`. -/
theorem reindexₗ_conjTranspose [Semiring R] [AddCommMonoid A] [Module R A] [Star A]
    (e₁ : m ≃ l) (e₂ : n ≃ o) (M : CStarMatrix m n A) :
    (reindexₗ R A e₁ e₂ M).conjTranspose = reindexₗ R A e₂ e₁ M.conjTranspose := by
  ext i j
  rfl

/-- On square matrices, `reindexₗ R A e e` agrees with `reindexₐ R A e`. -/
@[simp]
theorem reindexₗ_eq_reindexₐ [Fintype m] [Fintype n] [Semiring R] [AddCommMonoid A] [Mul A]
    [Module R A] [Star A] (e : m ≃ n) (M : CStarMatrix m m A) :
    reindexₗ R A e e M = reindexₐ R A e M := (rfl)

section ProperStar

variable [NonUnitalRing A] [StarRing A] [PartialOrder A] [StarOrderedRing A] [IsProperStar A]

/-- Over a star-ordered ring with proper star, `Mᴴ * M = 0` iff `M = 0`. -/
@[simp]
theorem conjTranspose_mul_self_eq_zero [Fintype m] {M : CStarMatrix m n A} :
    M.conjTranspose * M = 0 ↔ M = 0 := by
  simpa only [← ofMatrix.symm.injective.eq_iff, ofMatrix_symm_hMul, ofMatrix_symm_conjTranspose,
    of_zero.symm, Equiv.symm_apply_apply] using
    Matrix.conjTranspose_mul_self_eq_zero (A := ofMatrix.symm M)

/-- Over a star-ordered ring with proper star, `M * Mᴴ = 0` iff `M = 0`. -/
@[simp]
theorem self_mul_conjTranspose_eq_zero [Fintype n] {M : CStarMatrix m n A} :
    M * M.conjTranspose = 0 ↔ M = 0 := by
  simpa using conjTranspose_mul_self_eq_zero (M := M.conjTranspose)

/-- Left cancellation of `M.conjTranspose` from `(M.conjTranspose * M) * N = 0`. -/
theorem conjTranspose_mul_self_mul_eq_zero [Fintype m] [Fintype n]
    (M : CStarMatrix m n A) (N : CStarMatrix n p A) :
    (M.conjTranspose * M) * N = 0 ↔ M * N = 0 := by
  simpa only [← ofMatrix.symm.injective.eq_iff, ofMatrix_symm_hMul, ofMatrix_symm_conjTranspose,
    of_zero.symm, Equiv.symm_apply_apply] using
    Matrix.conjTranspose_mul_self_mul_eq_zero (ofMatrix.symm M) (ofMatrix.symm N)

/-- Left cancellation of `M` from `(M * M.conjTranspose) * N = 0`. -/
theorem self_mul_conjTranspose_mul_eq_zero [Fintype m] [Fintype n]
    (M : CStarMatrix m n A) (N : CStarMatrix m p A) :
    (M * M.conjTranspose) * N = 0 ↔ M.conjTranspose * N = 0 := by
  simpa only [conjTranspose_conjTranspose] using
    conjTranspose_mul_self_mul_eq_zero M.conjTranspose N

/-- Right cancellation of `M.conjTranspose` from `N * (M * M.conjTranspose) = 0`. -/
theorem mul_self_mul_conjTranspose_eq_zero [Fintype m] [Fintype n]
    (M : CStarMatrix m n A) (N : CStarMatrix p m A) :
    N * (M * M.conjTranspose) = 0 ↔ N * M = 0 := by
  rw [← conjTranspose_eq_zero, conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose,
    self_mul_conjTranspose_mul_eq_zero, ← conjTranspose_mul, conjTranspose_eq_zero]

/-- Right cancellation of `M` from `N * (M.conjTranspose * M) = 0`. -/
theorem mul_conjTranspose_mul_self_eq_zero [Fintype m] [Fintype n]
    (M : CStarMatrix m n A) (N : CStarMatrix p n A) :
    N * (M.conjTranspose * M) = 0 ↔ N * M.conjTranspose = 0 := by
  simpa only [conjTranspose_conjTranspose] using
    mul_self_mul_conjTranspose_eq_zero M.conjTranspose N

end ProperStar

end RectangularAlgebraic

section RectangularNorm

variable {l m n o A : Type*} [NonUnitalCStarAlgebra A]

/-- Acting on right Hilbert modules by `M * N` composes the operators in reverse order, because
`toCLM` acts on rows from the right. -/
theorem toCLM_mul [Fintype l] [Fintype m] (M : CStarMatrix l m A) (N : CStarMatrix m n A) :
    toCLM (M * N) = (toCLM N).comp (toCLM M) := by
  ext v k
  simp only [ContinuousLinearMap.comp_apply, toCLM_apply_eq_sum,
    WithCStarModule.equiv_symm_pi_apply, mul_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [mul_assoc]

variable [PartialOrder A] [StarOrderedRing A]

/-- Adjoint relation for `toCLM` with respect to `CStarMatrix.conjTranspose` (stated directly on
`CStarMatrix.conjTranspose`, following `CStarMatrix.inner_toCLM_conjTranspose_left` in Mathlib). -/
theorem inner_toCLM_conjTranspose [Fintype m] [Fintype n]
    (M : CStarMatrix m n A) (v : C⋆ᵐᵒᵈ(A, n → A)) (w : C⋆ᵐᵒᵈ(A, m → A)) :
    ⟪toCLM M.conjTranspose v, w⟫_A = ⟪v, toCLM M w⟫_A := by
  simp only [toCLM_apply_eq_sum, WithCStarModule.pi_inner, WithCStarModule.equiv_symm_pi_apply,
    WithCStarModule.inner_def, Finset.mul_sum, conjTranspose_apply, star_sum, star_mul, star_star,
    Finset.sum_mul]
  rw [Finset.sum_comm]
  simp_rw [mul_assoc]

/-- Right-hand adjoint relation for `toCLM` with respect to `CStarMatrix.conjTranspose`. -/
theorem inner_toCLM_conjTranspose' [Fintype m] [Fintype n]
    (M : CStarMatrix m n A) (v : C⋆ᵐᵒᵈ(A, m → A)) (w : C⋆ᵐᵒᵈ(A, n → A)) :
    ⟪v, toCLM M.conjTranspose w⟫_A = ⟪toCLM M v, w⟫_A := by
  simpa using (inner_toCLM_conjTranspose M.conjTranspose v w).symm

/-- The operator norm on rectangular `CStarMatrix` values is submultiplicative. -/
theorem norm_hMul_le [Fintype l] [Fintype m] [Fintype n]
    (M : CStarMatrix l m A) (N : CStarMatrix m n A) :
    ‖M * N‖ ≤ ‖M‖ * ‖N‖ := by
  rw [norm_def, norm_def, norm_def, toCLM_mul, mul_comm]
  exact (toCLM N).opNorm_comp_le (toCLM M)

/-- Auxiliary bound `‖M.conjTranspose‖ ≤ ‖M‖`; see `norm_conjTranspose` for equality. -/
theorem norm_conjTranspose_le [Fintype m] [Fintype n] (M : CStarMatrix m n A) :
    ‖M.conjTranspose‖ ≤ ‖M‖ := by
  refine norm_le_of_forall_inner_le (C := ‖M‖₊) fun v w ↦ ?_
  rw [coe_nnNorm, inner_toCLM_conjTranspose']
  calc ‖⟪toCLM M w, v⟫_A‖
      ≤ ‖toCLM M w‖ * ‖v‖ := CStarModule.norm_inner_le _
    _ ≤ (‖toCLM M‖ * ‖w‖) * ‖v‖ :=
        mul_le_mul_of_nonneg_right ((toCLM M).le_opNorm w) (norm_nonneg v)
    _ = ‖M‖ * ‖v‖ * ‖w‖ := by
        rw [norm_def]
        ring

/-- Conjugate transposition preserves the operator norm of a rectangular `CStarMatrix`. -/
@[simp]
theorem norm_conjTranspose [Fintype m] [Fintype n] (M : CStarMatrix m n A) :
    ‖M.conjTranspose‖ = ‖M‖ :=
  le_antisymm (norm_conjTranspose_le M)
    (by simpa only [conjTranspose_conjTranspose] using norm_conjTranspose_le M.conjTranspose)

/-- The rectangular C⋆-identity `‖M * Mᴴ‖ = ‖M‖ ^ 2` for `M : CStarMatrix m n A`, extending the
square `CStarRing` norm estimate of `CStarMatrix.instCStarRing` in Mathlib. -/
@[simp]
theorem norm_self_mul_conjTranspose [Fintype m] [Fintype n] (M : CStarMatrix m n A) :
    ‖M * M.conjTranspose‖ = ‖M‖ ^ 2 := by
  refine le_antisymm ?_ ?_
  · calc ‖M * M.conjTranspose‖ ≤ ‖M‖ * ‖M.conjTranspose‖ := norm_hMul_le M M.conjTranspose
      _ = ‖M‖ ^ 2 := by rw [norm_conjTranspose, sq]
  · have hsqrt : ‖M‖ ≤ √‖M * M.conjTranspose‖ := by
      rw [norm_def, ContinuousLinearMap.opNorm_le_iff (by positivity)]
      intro v
      rw [CStarModule.norm_eq_sqrt_norm_inner_self (A := A), ← inner_toCLM_conjTranspose',
        ← ContinuousLinearMap.comp_apply, ← toCLM_mul]
      have hinner : ‖⟪v, toCLM (M * M.conjTranspose) v⟫_A‖ ≤
          ‖M * M.conjTranspose‖ * ‖v‖ ^ 2 := by
        calc ‖⟪v, toCLM (M * M.conjTranspose) v⟫_A‖
            ≤ ‖v‖ * ‖toCLM (M * M.conjTranspose) v‖ := CStarModule.norm_inner_le _
          _ ≤ ‖v‖ * (‖toCLM (M * M.conjTranspose)‖ * ‖v‖) := by
              gcongr
              exact (toCLM (M * M.conjTranspose)).le_opNorm v
          _ = ‖M * M.conjTranspose‖ * ‖v‖ ^ 2 := by
              rw [norm_def]
              ring
      have hv : ‖v‖ = √(‖v‖ ^ 2) := by simp
      rw [hv, ← Real.sqrt_mul (by positivity)]
      exact Real.sqrt_le_sqrt hinner
    simpa [Real.sq_sqrt (norm_nonneg (M * M.conjTranspose))] using
      pow_le_pow_left₀ (norm_nonneg M) hsqrt 2

/-- The rectangular C⋆-identity `‖Mᴴ * M‖ = ‖M‖ ^ 2` for `M : CStarMatrix m n A`. -/
@[simp]
theorem norm_conjTranspose_mul_self [Fintype m] [Fintype n] (M : CStarMatrix m n A) :
    ‖M.conjTranspose * M‖ = ‖M‖ ^ 2 := by
  simpa using norm_self_mul_conjTranspose M.conjTranspose

/-- Reindexing rows and columns of a rectangular `CStarMatrix` preserves the operator norm. -/
@[simp]
theorem norm_reindexₗ [Fintype l] [Fintype m] [Fintype n] [Fintype o]
    (eₘ : m ≃ l) (eₙ : n ≃ o) (M : CStarMatrix m n A) :
    ‖reindexₗ ℂ A eₘ eₙ M‖ = ‖M‖ := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), ← norm_conjTranspose_mul_self,
    ← norm_conjTranspose_mul_self M, reindexₗ_conjTranspose, reindexₗ_mul, reindexₗ_eq_reindexₐ]
  exact NonUnitalStarAlgHom.norm_map (reindexₐ ℂ A eₙ).toNonUnitalStarAlgHom
    (reindexₐ ℂ A eₙ).injective (M.conjTranspose * M)

/-- Rectangular row-and-column reindexing bundled as a linear isometry equivalence. -/
noncomputable def reindexₗᵢ [Fintype l] [Fintype m] [Fintype n] [Fintype o]
    (eₘ : m ≃ l) (eₙ : n ≃ o) :
    CStarMatrix m n A ≃ₗᵢ[ℂ] CStarMatrix l o A :=
  { reindexₗ ℂ A eₘ eₙ with
    norm_map' := norm_reindexₗ eₘ eₙ }

@[simp]
theorem coe_reindexₗᵢ [Fintype l] [Fintype m] [Fintype n] [Fintype o]
    (eₘ : m ≃ l) (eₙ : n ≃ o) :
    ⇑(reindexₗᵢ (A := A) eₘ eₙ) = reindexₗ ℂ A eₘ eₙ := (rfl)

@[simp]
theorem reindexₗᵢ_symm [Fintype l] [Fintype m] [Fintype n] [Fintype o]
    (eₘ : m ≃ l) (eₙ : n ≃ o) :
    (reindexₗᵢ (A := A) eₘ eₙ).symm = reindexₗᵢ eₘ.symm eₙ.symm := (rfl)

end RectangularNorm

section PermMatrix

variable {l m n R A : Type*}

/-- Rectangular `0`-`1` permutation matrix in `CStarMatrix m n A` attached to an equivalence
`e : m ≃ n`, with entry `1` at `(i, e i)` and `0` elsewhere (extending `Equiv.Perm.permMatrix` from
permutations to arbitrary equivalences). -/
def permMatrix (A : Type*) [Zero A] [One A] [DecidableEq n] (e : m ≃ n) : CStarMatrix m n A :=
  ofMatrix e.toPEquiv.toMatrix

@[simp]
theorem ofMatrix_symm_permMatrix [Zero A] [One A] [DecidableEq n] (e : m ≃ n) :
    ofMatrix.symm (permMatrix A e) = e.toPEquiv.toMatrix := (rfl)

theorem permMatrix_apply [Zero A] [One A] [DecidableEq n] (e : m ≃ n) (i : m) (j : n) :
    permMatrix A e i j = if e i = j then 1 else 0 := by
  simp [permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, eq_comm]

@[simp]
theorem permMatrix_refl [Zero A] [One A] [DecidableEq n] :
    permMatrix A (Equiv.refl n) = 1 :=
  PEquiv.toMatrix_refl

theorem permMatrix_trans [Fintype m] [DecidableEq m] [DecidableEq n] [NonAssocSemiring A]
    (e₁ : l ≃ m) (e₂ : m ≃ n) :
    permMatrix A (e₁.trans e₂) = permMatrix A e₁ * permMatrix A e₂ :=
  PEquiv.toMatrix_trans e₁.toPEquiv e₂.toPEquiv

@[simp]
theorem conjTranspose_permMatrix [DecidableEq m] [DecidableEq n] [NonAssocSemiring A] [StarRing A]
    (e : m ≃ n) :
    (permMatrix A e).conjTranspose = permMatrix A e.symm := by
  ext i j
  by_cases h : e j = i <;> simp [permMatrix_apply, h, Equiv.eq_symm_apply, eq_comm]

@[simp]
theorem permMatrix_symm_mul_self [Fintype m] [DecidableEq m] [DecidableEq n]
    [NonAssocSemiring A] (e : m ≃ n) :
    permMatrix A e.symm * permMatrix A e = 1 := by
  rw [← permMatrix_trans, Equiv.symm_trans_self, permMatrix_refl]

@[simp]
theorem permMatrix_mul_symm_self [Fintype n] [DecidableEq m] [DecidableEq n]
    [NonAssocSemiring A] (e : m ≃ n) :
    permMatrix A e * permMatrix A e.symm = 1 := by
  rw [← permMatrix_trans, Equiv.self_trans_symm, permMatrix_refl]

theorem permMatrix_conjTranspose_mul_self [Fintype m] [DecidableEq n]
    [NonAssocSemiring A] [StarRing A] (e : m ≃ n) :
    (permMatrix A e).conjTranspose * permMatrix A e = 1 := by
  classical
  rw [conjTranspose_permMatrix, permMatrix_symm_mul_self]

theorem permMatrix_mul_conjTranspose_self [Fintype n] [DecidableEq m] [DecidableEq n]
    [NonAssocSemiring A] [StarRing A] (e : m ≃ n) :
    permMatrix A e * (permMatrix A e).conjTranspose = 1 := by
  rw [conjTranspose_permMatrix, permMatrix_mul_symm_self]

/-- A square permutation `CStarMatrix` is unitary. -/
theorem permMatrix_mem_unitary [Fintype n] [DecidableEq n] [Semiring A] [StarRing A]
    (σ : Equiv.Perm n) :
    permMatrix A σ ∈ unitary (CStarMatrix n n A) :=
  ⟨permMatrix_conjTranspose_mul_self σ, permMatrix_mul_conjTranspose_self σ⟩

/-- Conjugating `M : CStarMatrix m m A` by `permMatrix A e` implements `reindexₐ R A e M`. -/
theorem conjTranspose_permMatrix_mul_permMatrix [Fintype m] [Fintype n] [DecidableEq n]
    [Semiring R] [Semiring A] [Module R A] [StarRing A]
    (e : m ≃ n) (M : CStarMatrix m m A) :
    (permMatrix A e).conjTranspose * M * permMatrix A e = reindexₐ R A e M := by
  classical
  rw [conjTranspose_permMatrix]
  apply ofMatrix.symm.injective
  simp only [ofMatrix_symm_hMul, ofMatrix_symm_permMatrix, PEquiv.toMatrix_toPEquiv_mul,
    PEquiv.mul_toMatrix_toPEquiv]
  ext i j
  rfl

end PermMatrix

end CStarMatrix
