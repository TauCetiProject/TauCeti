/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Matrix.PEquiv
public import TauCeti.Analysis.CStarAlgebra.CStarMatrix.Basic
import Mathlib.Analysis.CStarAlgebra.Hom
import TauCeti.Analysis.CStarAlgebra.Module.AdjointPair
import TauCeti.LinearAlgebra.Matrix.PartialIsometry

/-!
# Rectangular norms, reindexing, and permutation matrices on `CStarMatrix`

Mathlib equips square matrices `CStarMatrix n n A` over a C⋆-algebra `A` with a C⋆-algebra
structure and rectangular matrices `CStarMatrix m n A` with the operator norm of the row-action
operator `CStarMatrix.toCLM M` (`v ↦ v ᵥ* M`) from the left Hilbert `A`-module `m → A` to
`n → A` (which reverses composition order on products: `toCLM (M * N) = (toCLM N).comp (toCLM M)`).
Comparing projections across different matrix sizes via rectangular partial isometries, block
decompositions, and coordinate equivalences `e : m ≃ n` requires rectangular multiplication,
conjugate transposition, and reindexing to interact cleanly with that operator norm. This file
develops that rectangular calculus:

* Rectangular algebraic, conjugate-transpose, and entrywise map identities.
* Rectangular operator-norm submultiplicativity `‖M * N‖ ≤ ‖M‖ * ‖N‖` and the rectangular
  C⋆-identities `‖M.conjTranspose‖ = ‖M‖`, `‖M * M.conjTranspose‖ = ‖M‖ ^ 2`, and
  `‖M.conjTranspose * M‖ = ‖M‖ ^ 2`.
* Row-and-column reindexing `CStarMatrix.reindexₗᵢ` as a linear isometry equivalence, together
  with rectangular `0`-`1` permutation matrices `CStarMatrix.permMatrix` implementing `reindexₗ`.

## Main declarations

* `CStarMatrix.norm_mul_le`, `CStarMatrix.norm_conjTranspose`,
  `CStarMatrix.norm_self_mul_conjTranspose`, `CStarMatrix.norm_conjTranspose_mul_self`:
  rectangular operator-norm submultiplicativity and C⋆-identities.
* `CStarMatrix.reindexₗᵢ`: rectangular row-and-column reindexing as a linear isometry equivalence.
* `CStarMatrix.permMatrix`: rectangular `0`-`1` matrices attached to `e : m ≃ n`, implementing
  `reindexₗ` by `(permMatrix A e₁).conjTranspose * M * permMatrix A e₂ = reindexₗ R A e₁ e₂ M`.
* `CStarMatrix.mul_eq_self_of_conjTranspose_mul_eq`: over a star-ordered ring with proper star,
  a rectangular matrix is supported on its initial projection.

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

/-- `ofMatrix` transports rectangular matrix multiplication to `CStarMatrix` multiplication. -/
@[simp] theorem of_mul_of [Fintype m] [Mul A] [AddCommMonoid A] (M : Matrix l m A)
    (N : Matrix m n A) : ofMatrix M * ofMatrix N = ofMatrix (M * N) := (rfl)

/-- Transporting a `CStarMatrix` product identity to ordinary `Matrix` multiplication. -/
lemma ofMatrix_symm_mul_eq [Fintype m] [Mul A] [AddCommMonoid A]
    {M : CStarMatrix l m A} {N : CStarMatrix m n A} {P : CStarMatrix l n A} (h : M * N = P) :
    ofMatrix.symm M * ofMatrix.symm N = ofMatrix.symm P :=
  h ▸ (ofMatrix_symm_mul M N).symm

/-- `ofMatrix` commutes with conjugate transposition. -/
@[simp] theorem conjTranspose_of [Star A] (M : Matrix m n A) :
    (ofMatrix M).conjTranspose = ofMatrix Mᴴ := (rfl)

/-- Left multiplication by the identity `CStarMatrix` is the identity on rectangular matrices. -/
@[simp] protected theorem one_mul [Fintype m] [DecidableEq m] [NonAssocSemiring A]
    (M : CStarMatrix m n A) : (1 : CStarMatrix m m A) * M = M := Matrix.one_mul M

/-- Right multiplication by the identity `CStarMatrix` is the identity on rectangular matrices. -/
@[simp] protected theorem mul_one [Fintype n] [DecidableEq n] [NonAssocSemiring A]
    (M : CStarMatrix m n A) : M * (1 : CStarMatrix n n A) = M := Matrix.mul_one M

/-- Rectangular left multiplication distributes over subtraction. -/
protected theorem mul_sub [Fintype m] [NonUnitalNonAssocRing A]
    (L : CStarMatrix l m A) (M N : CStarMatrix m n A) :
    L * (M - N) = L * M - L * N := Matrix.mul_sub L M N

/-- Rectangular right multiplication distributes over subtraction. -/
protected theorem sub_mul [Fintype m] [NonUnitalNonAssocRing A]
    (L M : CStarMatrix l m A) (N : CStarMatrix m n A) :
    (L - M) * N = L * N - M * N := Matrix.sub_mul L M N

/-- Rectangular left multiplication commutes with negation. -/
@[simp] protected theorem mul_neg [Fintype m] [NonUnitalNonAssocRing A]
    (M : CStarMatrix l m A) (N : CStarMatrix m n A) : M * (-N) = -(M * N) := Matrix.mul_neg M N

/-- Rectangular right multiplication commutes with negation. -/
@[simp] protected theorem neg_mul [Fintype m] [NonUnitalNonAssocRing A]
    (M : CStarMatrix l m A) (N : CStarMatrix m n A) : (-M) * N = -(M * N) := Matrix.neg_mul M N

/-- The conjugate transpose of the identity `CStarMatrix` is the identity. -/
@[simp] theorem conjTranspose_one [DecidableEq n] [NonAssocSemiring A] [StarRing A] :
    (1 : CStarMatrix n n A).conjTranspose = 1 := Matrix.conjTranspose_one

/-- Conjugate transposition distributes over addition. -/
@[simp] theorem conjTranspose_add [AddMonoid A] [StarAddMonoid A] (M N : CStarMatrix m n A) :
    (M + N).conjTranspose = M.conjTranspose + N.conjTranspose := Matrix.conjTranspose_add M N

/-- Conjugate transposition commutes with negation. -/
@[simp] theorem conjTranspose_neg [AddGroup A] [StarAddMonoid A] (M : CStarMatrix m n A) :
    (-M).conjTranspose = -M.conjTranspose := Matrix.conjTranspose_neg M

/-- Conjugate transposition distributes over subtraction. -/
@[simp] theorem conjTranspose_sub [AddGroup A] [StarAddMonoid A] (M N : CStarMatrix m n A) :
    (M - N).conjTranspose = M.conjTranspose - N.conjTranspose := Matrix.conjTranspose_sub M N

/-- Conjugate transposition is conjugate-linear with respect to scalar multiplication. -/
@[simp] theorem conjTranspose_smul [Star R] [Star A] [SMul R A] [StarModule R A]
    (c : R) (M : CStarMatrix m n A) :
    (c • M).conjTranspose = star c • M.conjTranspose := Matrix.conjTranspose_smul c M

/-- A rectangular `CStarMatrix` vanishes iff its conjugate transpose vanishes. -/
@[simp] theorem conjTranspose_eq_zero [AddMonoid A] [StarAddMonoid A] {M : CStarMatrix m n A} :
    M.conjTranspose = 0 ↔ M = 0 := Matrix.conjTranspose_eq_zero

/-- Applying a non-unital ring homomorphism entrywise commutes with rectangular multiplication. -/
theorem map_mul [Fintype m] [NonUnitalNonAssocSemiring A] [NonUnitalNonAssocSemiring B]
    {F : Type*} [FunLike F A B] [NonUnitalRingHomClass F A B]
    (f : F) (M : CStarMatrix l m A) (N : CStarMatrix m n A) :
    (M * N).map f = M.map f * N.map f :=
  ofMatrix.symm.injective (Matrix.map_mul (L := ofMatrix.symm M) (M := ofMatrix.symm N) (f := f))

/-- Applying a `⋆`-preserving map entrywise commutes with `conjTranspose`. -/
theorem map_conjTranspose [Star A] [Star B] {F : Type*} [FunLike F A B] [StarHomClass F A B]
    (f : F) (M : CStarMatrix m n A) : M.conjTranspose.map f = (M.map f).conjTranspose :=
  ofMatrix.symm.injective (Matrix.conjTranspose_map (A := ofMatrix.symm M) f (fun a ↦ map_star f a))

/-- `CStarMatrix.mapₙₐ f M` applies `f` entrywise via `CStarMatrix.map`. -/
theorem mapₙₐ_eq_map [Fintype n] [Semiring R] [NonUnitalNonAssocSemiring A] [Module R A] [Star A]
    [NonUnitalNonAssocSemiring B] [Module R B] [Star B] (f : A →⋆ₙₐ[R] B) (M : CStarMatrix n n A) :
    mapₙₐ f M = M.map f := (rfl)

/-- Reading `reindexₗ R A e₁ e₂ M` as an ordinary matrix gives `Matrix.reindex e₁ e₂`. -/
@[simp] theorem ofMatrix_symm_reindexₗ [Semiring R] [AddCommMonoid A] [Module R A]
    (e₁ : m ≃ l) (e₂ : n ≃ o) (M : CStarMatrix m n A) :
    ofMatrix.symm (reindexₗ R A e₁ e₂ M) = Matrix.reindex e₁ e₂ (ofMatrix.symm M) := by
  ext i j
  exact reindexₗ_apply (R := R)

/-- Row-and-column reindexing `reindexₗ R A e₁ e₂ M` is independent of the scalar ring `R`. -/
theorem reindexₗ_eq_reindexₗ (S : Type*) [Semiring R] [Semiring S] [AddCommMonoid A]
    [Module R A] [Module S A] (e₁ : m ≃ l) (e₂ : n ≃ o) (M : CStarMatrix m n A) :
    reindexₗ R A e₁ e₂ M = reindexₗ S A e₁ e₂ M :=
  ofMatrix.symm.injective (by simp)

/-- Rectangular row-and-column reindexing respects matrix multiplication when inner equivalences
match. -/
theorem reindexₗ_mul [Fintype m] [Fintype o] [Semiring R] [AddCommMonoid A] [Mul A] [Module R A]
    (e₁ : l ≃ n) (e₂ : m ≃ o) (e₃ : p ≃ q) (M : CStarMatrix l m A) (N : CStarMatrix m p A) :
    reindexₗ R A e₁ e₂ M * reindexₗ R A e₂ e₃ N = reindexₗ R A e₁ e₃ (M * N) := by
  apply ofMatrix.symm.injective
  simpa only [ofMatrix_symm_mul, ofMatrix_symm_reindexₗ, Matrix.reindex_apply] using
    Matrix.submatrix_mul_equiv (ofMatrix.symm M) (ofMatrix.symm N) e₁.symm e₂.symm e₃.symm

/-- Rectangular row-and-column reindexing swaps equivalences under `conjTranspose`. -/
theorem reindexₗ_conjTranspose [Semiring R] [AddCommMonoid A] [Module R A] [Star A]
    (e₁ : m ≃ l) (e₂ : n ≃ o) (M : CStarMatrix m n A) :
    (reindexₗ R A e₁ e₂ M).conjTranspose = reindexₗ R A e₂ e₁ M.conjTranspose := by
  apply ofMatrix.symm.injective
  simp only [ofMatrix_symm_conjTranspose, ofMatrix_symm_reindexₗ, Matrix.reindex_apply,
    Matrix.conjTranspose_submatrix]

/-- On square matrices, `reindexₗ R A e e` agrees with `reindexₐ R A e`. -/
@[simp] theorem reindexₗ_eq_reindexₐ [Fintype m] [Fintype n] [Semiring R] [AddCommMonoid A] [Mul A]
    [Module R A] [Star A] (e : m ≃ n) (M : CStarMatrix m m A) :
    reindexₗ R A e e M = reindexₐ R A e M := (rfl)

/-- If `v.conjTranspose * v = p` and `v * p = v`, then `p * v.conjTranspose = v.conjTranspose`. -/
lemma mul_conjTranspose_eq_self_of_mul_eq {p : CStarMatrix m m A} {v : CStarMatrix n m A}
    [Fintype m] [Fintype n] [NonUnitalSemiring A] [StarRing A]
    (hvp : v.conjTranspose * v = p) (hv : v * p = v) :
    p * v.conjTranspose = v.conjTranspose := by
  have hp_sa : p.conjTranspose = p := by rw [← hvp, conjTranspose_mul, conjTranspose_conjTranspose]
  simpa [hp_sa] using congrArg conjTranspose hv

/-- If `v.conjTranspose * v = p`, `v * v.conjTranspose = q`, and `v * p = v`, then `q * v = v`. -/
lemma mul_self_eq_self_of_mul_eq [Fintype m] [Fintype n] [NonUnitalSemiring A]
    [StarRing A] {p : CStarMatrix m m A} {q : CStarMatrix n n A} {v : CStarMatrix n m A}
    (hvp : v.conjTranspose * v = p) (hvq : v * v.conjTranspose = q) (hv : v * p = v) :
    q * v = v := by
  rw [← hvq, mul_assoc_rectangular, hvp, hv]

/-- If `v.conjTranspose * v = p`, `v * v.conjTranspose = q`, and `v * p = v`, then
`v.conjTranspose * q = v.conjTranspose`. -/
lemma conjTranspose_mul_eq_self_of_mul_eq [Fintype m] [Fintype n]
    [NonUnitalSemiring A] [StarRing A] {p : CStarMatrix m m A} {q : CStarMatrix n n A}
    {v : CStarMatrix n m A} (hvp : v.conjTranspose * v = p) (hvq : v * v.conjTranspose = q)
    (hv : v * p = v) : v.conjTranspose * q = v.conjTranspose := by
  have hq_sa : q.conjTranspose = q := by rw [← hvq, conjTranspose_mul, conjTranspose_conjTranspose]
  simpa [hq_sa] using congrArg conjTranspose (mul_self_eq_self_of_mul_eq hvp hvq hv)

/-- If `v.conjTranspose * v = p`, `v * v.conjTranspose = q`, and `v * p = v`, then `q` is
idempotent. -/
lemma isIdempotentElem_of_mul_conjTranspose_eq [Fintype m] [Fintype n]
    [NonUnitalSemiring A] [StarRing A] {p : CStarMatrix m m A} {q : CStarMatrix n n A}
    {v : CStarMatrix n m A} (hvp : v.conjTranspose * v = p) (hvq : v * v.conjTranspose = q)
    (hv : v * p = v) : IsIdempotentElem q := by
  rw [IsIdempotentElem, ← hvq, mul_assoc_rectangular, hvq,
    conjTranspose_mul_eq_self_of_mul_eq hvp hvq hv, hvq]

/-- Over a star-ordered ring with proper star, a rectangular matrix whose initial Gram matrix is
an idempotent `p` is supported on `p`. -/
lemma mul_eq_self_of_conjTranspose_mul_eq [Fintype m] [Fintype n] [NonUnitalRing A]
    [StarRing A] [PartialOrder A] [StarOrderedRing A] [IsProperStar A] {p : CStarMatrix m m A}
    (v : CStarMatrix n m A) (hp : IsIdempotentElem p) (hv : v.conjTranspose * v = p) :
    v * p = v := by
  have hp' : IsIdempotentElem (v.conjTranspose * v) := by
    rw [hv]
    exact hp
  have hpM := congrArg ofMatrix.symm hp'.eq
  simp only [ofMatrix_symm_mul, ofMatrix_symm_conjTranspose] at hpM
  have h := Matrix.mul_conjTranspose_mul_self_of_isIdempotentElem (ofMatrix.symm v) hpM
  rw [← hv]
  apply ofMatrix.symm.injective
  simpa only [ofMatrix_symm_mul, ofMatrix_symm_conjTranspose, Matrix.mul_assoc] using h

/-- Over a star-ordered ring with proper star, if `v.conjTranspose * v = p` is idempotent, then
`p * v.conjTranspose = v.conjTranspose`. -/
lemma mul_conjTranspose_eq_self_of_conjTranspose_mul_self [Fintype m] [Fintype n]
    [NonUnitalRing A] [StarRing A] [PartialOrder A] [StarOrderedRing A] [IsProperStar A]
    {p : CStarMatrix m m A} {v : CStarMatrix n m A} (hp : IsIdempotentElem p)
    (hvp : v.conjTranspose * v = p) : p * v.conjTranspose = v.conjTranspose :=
  mul_conjTranspose_eq_self_of_mul_eq hvp (mul_eq_self_of_conjTranspose_mul_eq v hp hvp)

/-- Over a star-ordered ring with proper star, if `v.conjTranspose * v = p` is idempotent and
`v * v.conjTranspose = q`, then `q * v = v`. -/
lemma mul_self_eq_self_of_self_mul_conjTranspose [Fintype m] [Fintype n]
    [NonUnitalRing A] [StarRing A] [PartialOrder A] [StarOrderedRing A] [IsProperStar A]
    {p : CStarMatrix m m A} {q : CStarMatrix n n A} {v : CStarMatrix n m A}
    (hp : IsIdempotentElem p) (hvp : v.conjTranspose * v = p) (hvq : v * v.conjTranspose = q) :
    q * v = v :=
  mul_self_eq_self_of_mul_eq hvp hvq (mul_eq_self_of_conjTranspose_mul_eq v hp hvp)

/-- Over a star-ordered ring with proper star, if `v.conjTranspose * v = p` is idempotent and
`v * v.conjTranspose = q`, then `v.conjTranspose * q = v.conjTranspose`. -/
lemma conjTranspose_mul_eq_self_of_self_mul_conjTranspose [Fintype m] [Fintype n]
    [NonUnitalRing A] [StarRing A] [PartialOrder A] [StarOrderedRing A] [IsProperStar A]
    {p : CStarMatrix m m A} {q : CStarMatrix n n A} {v : CStarMatrix n m A}
    (hp : IsIdempotentElem p) (hvp : v.conjTranspose * v = p) (hvq : v * v.conjTranspose = q) :
    v.conjTranspose * q = v.conjTranspose :=
  conjTranspose_mul_eq_self_of_mul_eq hvp hvq (mul_eq_self_of_conjTranspose_mul_eq v hp hvp)

/-- Over a star-ordered ring with proper star, if `v.conjTranspose * v = p` is idempotent and
`v * v.conjTranspose = q`, then `q` is idempotent. -/
lemma isIdempotentElem_of_conjTranspose_mul_self [Fintype m] [Fintype n]
    [NonUnitalRing A] [StarRing A] [PartialOrder A] [StarOrderedRing A] [IsProperStar A]
    {p : CStarMatrix m m A} {q : CStarMatrix n n A} {v : CStarMatrix n m A}
    (hp : IsIdempotentElem p) (hvp : v.conjTranspose * v = p) (hvq : v * v.conjTranspose = q) :
    IsIdempotentElem q :=
  isIdempotentElem_of_mul_conjTranspose_eq hvp hvq (mul_eq_self_of_conjTranspose_mul_eq v hp hvp)

end RectangularAlgebraic

section RectangularNorm

variable {l m n o R A : Type*} [NonUnitalCStarAlgebra A]

/-- `toCLM` acts by right multiplication on rows in the left Hilbert `A`-module, so `M * N`
composes the operators in reverse order. -/
theorem toCLM_mul [Fintype l] [Fintype m] (M : CStarMatrix l m A) (N : CStarMatrix m n A) :
    toCLM (M * N) = (toCLM N).comp (toCLM M) := by
  refine ContinuousLinearMap.ext fun v ↦ ?_
  simp only [ContinuousLinearMap.comp_apply, toCLM_apply]
  exact congrArg (WithCStarModule.equiv A (n → A)).symm (Matrix.vecMul_vecMul _ M N).symm

variable [PartialOrder A] [StarOrderedRing A]

/-- The operator norm on rectangular `CStarMatrix` values is submultiplicative. -/
protected theorem norm_mul_le [Fintype l] [Fintype m] [Fintype n]
    (M : CStarMatrix l m A) (N : CStarMatrix m n A) : ‖M * N‖ ≤ ‖M‖ * ‖N‖ := by
  rw [norm_def, norm_def, norm_def, toCLM_mul, mul_comm]
  exact (toCLM N).opNorm_comp_le (toCLM M)

/-- `toCLM M` and `toCLM M.conjTranspose` form a bounded Hilbert C⋆-module adjoint pair. -/
private theorem isAdjointPair_toCLM [Fintype m] [Fintype n] (M : CStarMatrix m n A) :
    LinearMap.IsAdjointPair (CStarModule.innerₛₗ (A := A) (E := C⋆ᵐᵒᵈ(A, m → A))).flip
      (CStarModule.innerₛₗ (A := A) (E := C⋆ᵐᵒᵈ(A, n → A))).flip
      (toCLM M : C⋆ᵐᵒᵈ(A, m → A) →L[ℂ] C⋆ᵐᵒᵈ(A, n → A))
      (toCLM M.conjTranspose : C⋆ᵐᵒᵈ(A, n → A) →L[ℂ] C⋆ᵐᵒᵈ(A, m → A)) :=
  CStarModule.isAdjointPair_inner_iff.mpr fun v w ↦ by
    -- `CStarMatrix.conjTranspose` agrees definitionally with `Matrix.conjTranspose` (`Mᴴ`).
    change ⟪toCLM M v, w⟫_A = ⟪v, toCLM Mᴴ w⟫_A
    exact inner_toCLM_conjTranspose_right.symm

/-- Conjugate transposition preserves the operator norm of a rectangular `CStarMatrix`. -/
@[simp] theorem norm_conjTranspose [Fintype m] [Fintype n] (M : CStarMatrix m n A) :
    ‖M.conjTranspose‖ = ‖M‖ := by
  rw [norm_def, norm_def]
  exact (isAdjointPair_toCLM M).norm_eq_cstarModule

/-- The rectangular C⋆-identity `‖M * Mᴴ‖ = ‖M‖ ^ 2` for `M : CStarMatrix m n A`, extending the
square `CStarRing` norm estimate of `CStarMatrix.instCStarRing` in Mathlib. -/
@[simp] theorem norm_self_mul_conjTranspose [Fintype m] [Fintype n] (M : CStarMatrix m n A) :
    ‖M * M.conjTranspose‖ = ‖M‖ ^ 2 := by
  rw [norm_def, norm_def, toCLM_mul]
  exact (isAdjointPair_toCLM M).norm_adjoint_comp_self_cstarModule

/-- The rectangular C⋆-identity `‖Mᴴ * M‖ = ‖M‖ ^ 2` for `M : CStarMatrix m n A`. -/
@[simp] theorem norm_conjTranspose_mul_self [Fintype m] [Fintype n] (M : CStarMatrix m n A) :
    ‖M.conjTranspose * M‖ = ‖M‖ ^ 2 := by simpa using norm_self_mul_conjTranspose M.conjTranspose

/-- Reindexing rows and columns of a rectangular `CStarMatrix` preserves the operator norm. -/
@[simp] theorem norm_reindexₗ [Semiring R] [Module R A]
    [Fintype l] [Fintype m] [Fintype n] [Fintype o]
    (eₘ : m ≃ l) (eₙ : n ≃ o) (M : CStarMatrix m n A) : ‖reindexₗ R A eₘ eₙ M‖ = ‖M‖ := by
  rw [reindexₗ_eq_reindexₗ ℂ, ← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _),
    ← norm_conjTranspose_mul_self, ← norm_conjTranspose_mul_self M,
    reindexₗ_conjTranspose, reindexₗ_mul, reindexₗ_eq_reindexₐ]
  exact NonUnitalStarAlgHom.norm_map (reindexₐ ℂ A eₙ).toNonUnitalStarAlgHom
    (reindexₐ ℂ A eₙ).injective (M.conjTranspose * M)

variable (R) (A) in
/-- Rectangular row-and-column reindexing bundled as a linear isometry equivalence. -/
noncomputable def reindexₗᵢ [Semiring R] [Module R A]
    [Fintype l] [Fintype m] [Fintype n] [Fintype o]
    (eₘ : m ≃ l) (eₙ : n ≃ o) : CStarMatrix m n A ≃ₗᵢ[R] CStarMatrix l o A :=
  { reindexₗ R A eₘ eₙ with norm_map' := norm_reindexₗ eₘ eₙ }

@[simp] theorem coe_reindexₗᵢ [Semiring R] [Module R A]
    [Fintype l] [Fintype m] [Fintype n] [Fintype o]
    (eₘ : m ≃ l) (eₙ : n ≃ o) : ⇑(reindexₗᵢ R A eₘ eₙ) = reindexₗ R A eₘ eₙ := (rfl)

@[simp] theorem reindexₗᵢ_symm [Semiring R] [Module R A]
    [Fintype l] [Fintype m] [Fintype n] [Fintype o]
    (eₘ : m ≃ l) (eₙ : n ≃ o) :
    (reindexₗᵢ R A eₘ eₙ).symm = reindexₗᵢ R A eₘ.symm eₙ.symm := (rfl)

end RectangularNorm

section PermMatrix

variable {l m n o R A : Type*}

/-- Rectangular `0`-`1` permutation matrix in `CStarMatrix m n A` attached to `e : m ≃ n`, with
entry `1` at `(i, e i)` and `0` elsewhere (extending `Equiv.Perm.permMatrix`). -/
def permMatrix (A : Type*) [Zero A] [One A] [DecidableEq n] (e : m ≃ n) : CStarMatrix m n A :=
  ofMatrix e.toPEquiv.toMatrix

@[simp] theorem ofMatrix_symm_permMatrix [Zero A] [One A] [DecidableEq n] (e : m ≃ n) :
    ofMatrix.symm (permMatrix A e) = e.toPEquiv.toMatrix := (rfl)

theorem permMatrix_apply [Zero A] [One A] [DecidableEq n] (e : m ≃ n) (i : m) (j : n) :
    permMatrix A e i j = if e i = j then 1 else 0 := by
  simp [permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, eq_comm]

@[simp] theorem permMatrix_refl [Zero A] [One A] [DecidableEq n] :
    permMatrix A (Equiv.refl n) = 1 := PEquiv.toMatrix_refl

theorem permMatrix_trans [Fintype m] [DecidableEq m] [DecidableEq n] [NonAssocSemiring A]
    (e₁ : l ≃ m) (e₂ : m ≃ n) :
    permMatrix A (e₁.trans e₂) = permMatrix A e₁ * permMatrix A e₂ :=
  PEquiv.toMatrix_trans e₁.toPEquiv e₂.toPEquiv

@[simp] theorem conjTranspose_permMatrix [DecidableEq m] [DecidableEq n] [NonAssocSemiring A]
    [StarRing A] (e : m ≃ n) : (permMatrix A e).conjTranspose = permMatrix A e.symm := by
  ext i j; by_cases h : e j = i <;> simp [permMatrix_apply, h, Equiv.eq_symm_apply, eq_comm]

@[simp] theorem permMatrix_symm_mul_self [Fintype m] [DecidableEq m] [DecidableEq n]
    [NonAssocSemiring A] (e : m ≃ n) : permMatrix A e.symm * permMatrix A e = 1 := by
  rw [← permMatrix_trans, Equiv.symm_trans_self, permMatrix_refl]

@[simp] theorem permMatrix_mul_symm_self [Fintype n] [DecidableEq m] [DecidableEq n]
    [NonAssocSemiring A] (e : m ≃ n) : permMatrix A e * permMatrix A e.symm = 1 := by
  rw [← permMatrix_trans, Equiv.self_trans_symm, permMatrix_refl]

/-- Conjugating a rectangular matrix `M : CStarMatrix l m A` by permutation matrices implements
`reindexₗ R A e₁ e₂ M`. -/
theorem conjTranspose_permMatrix_mul_permMatrix_eq_reindexₗ [Fintype l] [Fintype m]
    [DecidableEq n] [DecidableEq o] [Semiring R] [NonAssocSemiring A] [Module R A] [StarRing A]
    (e₁ : l ≃ n) (e₂ : m ≃ o) (M : CStarMatrix l m A) :
    (permMatrix A e₁).conjTranspose * M * permMatrix A e₂ = reindexₗ R A e₁ e₂ M := by
  classical
  rw [conjTranspose_permMatrix]
  apply ofMatrix.symm.injective
  simp only [ofMatrix_symm_mul, ofMatrix_symm_permMatrix, PEquiv.toMatrix_toPEquiv_mul,
    PEquiv.mul_toMatrix_toPEquiv, ofMatrix_symm_reindexₗ, Matrix.reindex_apply,
    Matrix.submatrix_submatrix, Function.id_comp, Function.comp_id]

end PermMatrix

end CStarMatrix
