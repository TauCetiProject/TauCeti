/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Matrix.ColumnRowPartitioned
public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import Mathlib.LinearAlgebra.Matrix.Rank
public import TauCeti.Algebra.Star.PartialIsometry
public import TauCeti.Data.Matrix.Block

/-!
# Murray–von Neumann equivalence of matrix projections

Let `R` be a star ring. Square matrices `p : Matrix m m R` and `q : Matrix n n R`, possibly of
different sizes, are *Murray–von Neumann equivalent* when both are star projections and there is a
rectangular matrix `v : Matrix n m R` with `vᴴ * v = p` and `v * vᴴ = q`. This is the equivalence
relation on matrix projections from which the projection monoid `V(A)` and the group `K₀(A)` of a
C⋆-algebra `A` are built. The matrices are rectangular on purpose: over `ℂ` the row `(1 0)`
witnesses that the rank-one projection `diag(1, 0)` of size two is equivalent to the identity
of size one, which no comparison of matrices of a single size can see.

Everything here is algebraic, so it is stated for matrices over a star ring `R`. For a C⋆-algebra
`A`, the matrix algebra `CStarMatrix m m A` is a type synonym for `Matrix m m A` with the same
multiplication and star operation. Over any star ring an equivalence is implemented by a partial
isometry. Only the statement that every implementing matrix is one, so that `v * vᴴ` is a
projection as soon as `vᴴ * v` is, needs `vᴴ * v = 0` to force `v = 0` for rectangular matrices.
That holds over a star-ordered ring with `IsProperStar`, such as `ℂ` or a C⋆-algebra with its
spectral order (`Matrix.conjTranspose_mul_self_eq_zero`).

## Main definitions

* `Matrix.IsMurrayVonNeumannEquivalent p q`: the matrix projections `p` and `q` are
  Murray–von Neumann equivalent.

## Main statements

* `Matrix.IsMurrayVonNeumannEquivalent.refl`, `Matrix.IsMurrayVonNeumannEquivalent.symm` and
  `Matrix.IsMurrayVonNeumannEquivalent.trans`: the relation is an equivalence relation on
  matrix projections of all sizes.
* `IsStarProjection.isMurrayVonNeumannEquivalent_mul_mul_star`: unitary conjugacy implies
  equivalence. More generally, `IsStarProjection.isMurrayVonNeumannEquivalent_mul_mul_conjTranspose`
  compresses by a rectangular matrix that is isometric on the range of the projection.
* `Matrix.IsMurrayVonNeumannEquivalent.reindex`, `Matrix.IsMurrayVonNeumannEquivalent.fromBlocks`
  and `Matrix.IsMurrayVonNeumannEquivalent.map`: the relation is preserved by reindexing, by block
  sums and by entrywise star ring homomorphisms.
* `IsStarProjection.isMurrayVonNeumannEquivalent_fromBlocks_zero`,
  `Matrix.isMurrayVonNeumannEquivalent_fromBlocks_comm` and
  `Matrix.isMurrayVonNeumannEquivalent_fromBlocks_assoc`: padding by a zero block, and
  commutativity and associativity of block sums, up to equivalence.
* `Matrix.isMurrayVonNeumannEquivalent_of_mul_conjTranspose_mul_self_eq`: a rectangular partial
  isometry `v` gives `vᴴ * v ∼ v * vᴴ`. Conversely every equivalence is implemented by a partial
  isometry (`Matrix.IsMurrayVonNeumannEquivalent.exists_mul_conjTranspose_mul_self_eq`), so for
  square matrices the implementing elements are Tau Ceti's partial isometries
  (`Matrix.isMurrayVonNeumannEquivalent_iff_exists_isPartialIsometry`).
* `Matrix.mul_conjTranspose_mul_self_eq_of_isStarProjection`: over a star-ordered proper star
  ring, a matrix `v` with `vᴴ * v` a projection is a partial isometry.
* `Matrix.isMurrayVonNeumannEquivalent_iff_exists_mem_unitary_mul_fromBlocks_mul_star`: projections
  are equivalent exactly when `p ⊕ 0` and `0 ⊕ q` are unitarily conjugate, and
  `Matrix.IsMurrayVonNeumannEquivalent.exists_isSelfAdjoint_mem_unitary_mul_fromBlocks_mul_star`
  supplies the conjugating self-adjoint unitary `!![1 - p, vᴴ; v, 1 - q]`.
* `Matrix.isMurrayVonNeumannEquivalent_single_one` and
  `Matrix.IsMurrayVonNeumannEquivalent.rank_eq`: diagonal matrix units of any sizes are
  equivalent, and over a commutative star ring equivalent projections have equal rank.

## References

* B. Blackadar, *K-Theory for Operator Algebras*, 2nd ed., Cambridge University Press (1998),
  Definition 4.6.1 and Propositions 4.6.2–4.6.6.
* M. Rørdam, F. Larsen and N. Laustsen, *An Introduction to K-Theory for C⋆-Algebras*,
  Cambridge University Press (2000), Chapter 2.
-/

public section

open TauCeti

namespace Matrix

variable {m n o R : Type*} [Fintype m] [Fintype n] [Fintype o]

/-- The entrywise image of a matrix projection under a star ring homomorphism is a matrix
projection. -/
theorem _root_.IsStarProjection.matrix_map {S F : Type*} [NonUnitalNonAssocSemiring R] [Star R]
    [NonUnitalNonAssocSemiring S] [Star S] [FunLike F R S] [NonUnitalRingHomClass F R S]
    [StarHomClass F R S] {p : Matrix m m R} (hp : IsStarProjection p) (f : F) :
    IsStarProjection (p.map f) :=
  ⟨by rw [IsIdempotentElem, ← Matrix.map_mul, hp.isIdempotentElem.eq],
    (IsHermitian.map hp.isSelfAdjoint f fun _ ↦ map_star f _).isSelfAdjoint⟩

section NonUnitalSemiring

variable [NonUnitalSemiring R] [StarRing R]

/-- Square matrices `p` and `q`, possibly of different sizes, are **Murray–von Neumann
equivalent** when both are star projections and `vᴴ * v = p` and `v * vᴴ = q` for some rectangular
matrix `v`. -/
@[mk_iff]
structure IsMurrayVonNeumannEquivalent (p : Matrix m m R) (q : Matrix n n R) : Prop where
  protected isStarProjection_left : IsStarProjection p
  protected isStarProjection_right : IsStarProjection q
  exists_conjTranspose_mul_self_eq : ∃ v : Matrix n m R, vᴴ * v = p ∧ v * vᴴ = q

/-- A matrix projection is equivalent to itself, through itself. -/
theorem IsMurrayVonNeumannEquivalent.refl {p : Matrix m m R} (hp : IsStarProjection p) :
    IsMurrayVonNeumannEquivalent p p := by
  have hpp : pᴴ * p = p := by
    rw [← star_eq_conjTranspose, hp.isSelfAdjoint.star_eq, hp.isIdempotentElem.eq]
  refine ⟨hp, hp, p, hpp, ?_⟩
  rw [← star_eq_conjTranspose, hp.isSelfAdjoint.star_eq, hp.isIdempotentElem.eq]

/-- A matrix is equivalent to itself exactly when it is a star projection. -/
@[simp]
theorem isMurrayVonNeumannEquivalent_self_iff {p : Matrix m m R} :
    IsMurrayVonNeumannEquivalent p p ↔ IsStarProjection p :=
  ⟨IsMurrayVonNeumannEquivalent.isStarProjection_left, .refl⟩

/-- Murray–von Neumann equivalence is symmetric: if `v` implements `p ∼ q` then `vᴴ` implements
`q ∼ p`. -/
@[symm]
theorem IsMurrayVonNeumannEquivalent.symm {p : Matrix m m R} {q : Matrix n n R}
    (h : IsMurrayVonNeumannEquivalent p q) : IsMurrayVonNeumannEquivalent q p := by
  obtain ⟨hp, hq, v, hvp, hvq⟩ := h
  exact ⟨hq, hp, vᴴ, by rwa [conjTranspose_conjTranspose], by rwa [conjTranspose_conjTranspose]⟩

/-- Murray–von Neumann equivalence is symmetric. -/
theorem isMurrayVonNeumannEquivalent_comm {p : Matrix m m R} {q : Matrix n n R} :
    IsMurrayVonNeumannEquivalent p q ↔ IsMurrayVonNeumannEquivalent q p :=
  ⟨.symm, .symm⟩

/-- Murray–von Neumann equivalence is transitive: if `v` implements `p ∼ q` and `w` implements
`q ∼ r` then `w * v` implements `p ∼ r`. -/
@[trans]
theorem IsMurrayVonNeumannEquivalent.trans {p : Matrix m m R} {q : Matrix n n R}
    {r : Matrix o o R} (h₁ : IsMurrayVonNeumannEquivalent p q)
    (h₂ : IsMurrayVonNeumannEquivalent q r) : IsMurrayVonNeumannEquivalent p r := by
  obtain ⟨hp, -, v, hvp, hvq⟩ := h₁
  obtain ⟨-, hr, w, hwq, hwr⟩ := h₂
  refine ⟨hp, hr, w * v, ?_, ?_⟩
  · calc (w * v)ᴴ * (w * v) = vᴴ * (wᴴ * w) * v := by
          simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = (vᴴ * v) * (vᴴ * v) := by rw [hwq, ← hvq]; simp only [Matrix.mul_assoc]
      _ = p := by rw [hvp, hp.isIdempotentElem.eq]
  · calc w * v * (w * v)ᴴ = w * (v * vᴴ) * wᴴ := by
          simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = (w * wᴴ) * (w * wᴴ) := by rw [hvq, ← hwq]; simp only [Matrix.mul_assoc]
      _ = r := by rw [hwr, hr.isIdempotentElem.eq]

/-- A rectangular partial isometry `v`, one with `v * vᴴ * v = v`, implements the equivalence of
its initial projection `vᴴ * v` with its final projection `v * vᴴ`. -/
theorem isMurrayVonNeumannEquivalent_of_mul_conjTranspose_mul_self_eq {v : Matrix n m R}
    (hv : v * vᴴ * v = v) : IsMurrayVonNeumannEquivalent (vᴴ * v) (v * vᴴ) := by
  have hv' : vᴴ * v * vᴴ = vᴴ := by
    simpa [conjTranspose_mul, Matrix.mul_assoc] using congr_arg conjTranspose hv
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, v, rfl, rfl⟩
  · rw [IsIdempotentElem, ← Matrix.mul_assoc, hv']
  · rw [IsSelfAdjoint, star_eq_conjTranspose, conjTranspose_mul, conjTranspose_conjTranspose]
  · rw [IsIdempotentElem, ← Matrix.mul_assoc, hv]
  · rw [IsSelfAdjoint, star_eq_conjTranspose, conjTranspose_mul, conjTranspose_conjTranspose]

/-- For square matrices, a partial isometry in the sense of `TauCeti.IsPartialIsometry` implements
the equivalence of its initial and final projections. -/
theorem _root_.TauCeti.IsPartialIsometry.isMurrayVonNeumannEquivalent {v : Matrix m m R}
    (hv : IsPartialIsometry v) : IsMurrayVonNeumannEquivalent (star v * v) (v * star v) :=
  isMurrayVonNeumannEquivalent_of_mul_conjTranspose_mul_self_eq hv.mul_star_mul_self

/-- **Compression of a projection.** If `wᴴ * w` acts as the identity on the range of the
projection `p`, then `p` is equivalent to `w * p * wᴴ`, through `w * p`. -/
theorem _root_.IsStarProjection.isMurrayVonNeumannEquivalent_mul_mul_conjTranspose
    {p : Matrix m m R} (hp : IsStarProjection p) {w : Matrix n m R} (hw : wᴴ * w * p = p) :
    IsMurrayVonNeumannEquivalent p (w * p * wᴴ) := by
  have hpH : pᴴ = p := by rw [← star_eq_conjTranspose, hp.isSelfAdjoint.star_eq]
  have hvp : (w * p)ᴴ * (w * p) = p := by
    rw [conjTranspose_mul, hpH, Matrix.mul_assoc, ← Matrix.mul_assoc wᴴ, hw,
      hp.isIdempotentElem.eq]
  have hvq : w * p * (w * p)ᴴ = w * p * wᴴ := by
    rw [conjTranspose_mul, hpH, ← Matrix.mul_assoc, Matrix.mul_assoc w, hp.isIdempotentElem.eq]
  have h := isMurrayVonNeumannEquivalent_of_mul_conjTranspose_mul_self_eq (v := w * p)
    (by rw [Matrix.mul_assoc, hvp, Matrix.mul_assoc, hp.isIdempotentElem.eq])
  rwa [hvp, hvq] at h

/-- The zero matrix of any size is equivalent only to zero. -/
@[simp]
theorem isMurrayVonNeumannEquivalent_zero_right_iff {p : Matrix m m R} :
    IsMurrayVonNeumannEquivalent p (0 : Matrix n n R) ↔ p = 0 := by
  refine ⟨fun ⟨hp, _, v, hvp, hvq⟩ ↦ ?_, ?_⟩
  · rw [← hp.isIdempotentElem.eq, ← hvp, Matrix.mul_assoc, ← Matrix.mul_assoc v, hvq,
      Matrix.zero_mul, Matrix.mul_zero]
  · rintro rfl
    exact ⟨.zero _, .zero _, 0, by simp, by simp⟩

/-- The zero matrix of any size is equivalent only to zero. -/
@[simp]
theorem isMurrayVonNeumannEquivalent_zero_left_iff {q : Matrix n n R} :
    IsMurrayVonNeumannEquivalent (0 : Matrix m m R) q ↔ q = 0 := by
  rw [isMurrayVonNeumannEquivalent_comm, isMurrayVonNeumannEquivalent_zero_right_iff]

/-- Murray–von Neumann equivalence is preserved by reindexing both matrices. -/
theorem IsMurrayVonNeumannEquivalent.reindex {m' n' : Type*} [Fintype m'] [Fintype n']
    {p : Matrix m m R} {q : Matrix n n R} (h : IsMurrayVonNeumannEquivalent p q) (eₘ : m ≃ m')
    (eₙ : n ≃ n') :
    IsMurrayVonNeumannEquivalent (Matrix.reindex eₘ eₘ p) (Matrix.reindex eₙ eₙ q) := by
  obtain ⟨hp, hq, v, hvp, hvq⟩ := h
  refine ⟨?_, ?_, Matrix.reindex eₙ eₘ v, ?_, ?_⟩
  · simpa using hp.map (reindexStarAlgEquiv ℕ R eₘ)
  · simpa using hq.map (reindexStarAlgEquiv ℕ R eₙ)
  · rw [conjTranspose_reindex, reindex_apply, reindex_apply, submatrix_mul_equiv, hvp,
      reindex_apply]
  · rw [conjTranspose_reindex, reindex_apply, reindex_apply, submatrix_mul_equiv, hvq,
      reindex_apply]

/-- A matrix projection is equivalent to each of its reindexings. -/
theorem _root_.IsStarProjection.isMurrayVonNeumannEquivalent_reindex {m' : Type*} [Fintype m']
    {p : Matrix m m R} (hp : IsStarProjection p) (e : m ≃ m') :
    IsMurrayVonNeumannEquivalent p (reindex e e p) := by
  simpa using (IsMurrayVonNeumannEquivalent.refl hp).reindex (Equiv.refl m) e

/-- **Additivity.** Murray–von Neumann equivalence is compatible with block sums: if `v₁` and `v₂`
implement `p₁ ∼ q₁` and `p₂ ∼ q₂`, then `v₁ ⊕ v₂` implements `p₁ ⊕ p₂ ∼ q₁ ⊕ q₂`. -/
theorem IsMurrayVonNeumannEquivalent.fromBlocks {m' n' : Type*} [Fintype m'] [Fintype n']
    {p₁ : Matrix m m R} {q₁ : Matrix n n R} {p₂ : Matrix m' m' R} {q₂ : Matrix n' n' R}
    (h₁ : IsMurrayVonNeumannEquivalent p₁ q₁) (h₂ : IsMurrayVonNeumannEquivalent p₂ q₂) :
    IsMurrayVonNeumannEquivalent (Matrix.fromBlocks p₁ 0 0 p₂) (Matrix.fromBlocks q₁ 0 0 q₂) := by
  obtain ⟨hp₁, hq₁, v₁, hvp₁, hvq₁⟩ := h₁
  obtain ⟨hp₂, hq₂, v₂, hvp₂, hvq₂⟩ := h₂
  refine ⟨hp₁.fromBlocks_zero₁₂_zero₂₁ hp₂, hq₁.fromBlocks_zero₁₂_zero₂₁ hq₂,
    Matrix.fromBlocks v₁ 0 0 v₂, ?_, ?_⟩ <;>
  simp [fromBlocks_conjTranspose, fromBlocks_multiply, hvp₁, hvp₂, hvq₁, hvq₂]

/-- **Padding by zero.** A matrix projection `p` is equivalent to `p ⊕ 0` for a zero block of any
size. -/
theorem _root_.IsStarProjection.isMurrayVonNeumannEquivalent_fromBlocks_zero {p : Matrix m m R}
    (hp : IsStarProjection p) :
    IsMurrayVonNeumannEquivalent p (fromBlocks p 0 0 (0 : Matrix n n R)) := by
  have hpH : pᴴ = p := by rw [← star_eq_conjTranspose, hp.isSelfAdjoint.star_eq]
  refine ⟨hp, hp.fromBlocks_zero₁₂_zero₂₁ (.zero _), fromRows p 0, ?_, ?_⟩
  · have h : (fromRows p (0 : Matrix n m R))ᴴ * fromRows p 0 = pᴴ * p := by
      ext i j
      simp [Matrix.mul_apply, Fintype.sum_sum_type]
    rw [h, hpH, hp.isIdempotentElem.eq]
  · have h : fromRows p (0 : Matrix n m R) * (fromRows p (0 : Matrix n m R))ᴴ =
        fromBlocks (p * pᴴ) 0 0 0 := by
      ext (i | i) (j | j) <;> simp [Matrix.mul_apply]
    rw [h, hpH, hp.isIdempotentElem.eq]

/-- **Padding by zero.** A matrix projection `p` is equivalent to `0 ⊕ p` for a zero block of any
size. -/
theorem _root_.IsStarProjection.isMurrayVonNeumannEquivalent_zero_fromBlocks {p : Matrix m m R}
    (hp : IsStarProjection p) :
    IsMurrayVonNeumannEquivalent p (fromBlocks (0 : Matrix n n R) 0 0 p) := by
  have hpH : pᴴ = p := by rw [← star_eq_conjTranspose, hp.isSelfAdjoint.star_eq]
  refine ⟨hp, (IsStarProjection.zero _).fromBlocks_zero₁₂_zero₂₁ hp, fromRows 0 p, ?_, ?_⟩
  · have h : (fromRows (0 : Matrix n m R) p)ᴴ * fromRows 0 p = pᴴ * p := by
      ext i j
      simp [Matrix.mul_apply, Fintype.sum_sum_type]
    rw [h, hpH, hp.isIdempotentElem.eq]
  · have h : fromRows (0 : Matrix n m R) p * (fromRows (0 : Matrix n m R) p)ᴴ =
        fromBlocks 0 0 0 (p * pᴴ) := by
      ext (i | i) (j | j) <;> simp [Matrix.mul_apply]
    rw [h, hpH, hp.isIdempotentElem.eq]

/-- **Commutativity of block sums.** For matrix projections `p` and `q`, `p ⊕ q ∼ q ⊕ p`. -/
theorem isMurrayVonNeumannEquivalent_fromBlocks_comm {p : Matrix m m R} {q : Matrix n n R}
    (hp : IsStarProjection p) (hq : IsStarProjection q) :
    IsMurrayVonNeumannEquivalent (fromBlocks p 0 0 q) (fromBlocks q 0 0 p) := by
  convert (hp.fromBlocks_zero₁₂_zero₂₁ hq).isMurrayVonNeumannEquivalent_reindex
    (Equiv.sumComm m n) using 1
  ext (i | i) (j | j) <;> simp

/-- **Associativity of block sums.** For matrix projections `p`, `q` and `r`,
`(p ⊕ q) ⊕ r ∼ p ⊕ (q ⊕ r)`. -/
theorem isMurrayVonNeumannEquivalent_fromBlocks_assoc {p : Matrix m m R} {q : Matrix n n R}
    {r : Matrix o o R} (hp : IsStarProjection p) (hq : IsStarProjection q)
    (hr : IsStarProjection r) :
    IsMurrayVonNeumannEquivalent (fromBlocks (fromBlocks p 0 0 q) 0 0 r)
      (fromBlocks p 0 0 (fromBlocks q 0 0 r)) := by
  convert ((hp.fromBlocks_zero₁₂_zero₂₁ hq).fromBlocks_zero₁₂_zero₂₁
    hr).isMurrayVonNeumannEquivalent_reindex (Equiv.sumAssoc m n o) using 1
  ext (i | i | i) (j | j | j) <;> simp

/-- Murray–von Neumann equivalence is preserved by applying a star ring homomorphism to the
entries. -/
theorem IsMurrayVonNeumannEquivalent.map {S F : Type*} [NonUnitalSemiring S] [StarRing S]
    [FunLike F R S] [NonUnitalRingHomClass F R S] [StarHomClass F R S] {p : Matrix m m R}
    {q : Matrix n n R} (h : IsMurrayVonNeumannEquivalent p q) (f : F) :
    IsMurrayVonNeumannEquivalent (Matrix.map p f) (Matrix.map q f) := by
  obtain ⟨hp, hq, v, hvp, hvq⟩ := h
  refine ⟨hp.matrix_map f, hq.matrix_map f, Matrix.map v f, ?_, ?_⟩
  · rw [← conjTranspose_map f fun _ ↦ map_star f _, ← Matrix.map_mul, hvp]
  · rw [← conjTranspose_map f fun _ ↦ map_star f _, ← Matrix.map_mul, hvq]

/-- Every Murray–von Neumann equivalence is implemented by a partial isometry: if `v` implements
`p ∼ q`, then so does the partial isometry `v * p`. -/
theorem IsMurrayVonNeumannEquivalent.exists_mul_conjTranspose_mul_self_eq {p : Matrix m m R}
    {q : Matrix n n R} (h : IsMurrayVonNeumannEquivalent p q) :
    ∃ v : Matrix n m R, vᴴ * v = p ∧ v * vᴴ = q ∧ v * vᴴ * v = v := by
  obtain ⟨hp, hq, v, hvp, hvq⟩ := h
  have hpH : pᴴ = p := by rw [← star_eq_conjTranspose, hp.isSelfAdjoint.star_eq]
  have hvpp : v * p * p = v * p := by rw [Matrix.mul_assoc, hp.isIdempotentElem.eq]
  have hq' : v * p * (v * p)ᴴ = q := by
    rw [conjTranspose_mul, hpH, ← Matrix.mul_assoc, hvpp, ← hvp, ← Matrix.mul_assoc, hvq,
      Matrix.mul_assoc, hvq, hq.isIdempotentElem.eq]
  refine ⟨v * p, ?_, hq', ?_⟩
  · rw [conjTranspose_mul, hpH, Matrix.mul_assoc, ← Matrix.mul_assoc vᴴ, hvp,
      hp.isIdempotentElem.eq, hp.isIdempotentElem.eq]
  · rw [hq', ← hvq, Matrix.mul_assoc, ← Matrix.mul_assoc vᴴ, hvp, ← Matrix.mul_assoc, hvpp]

/-- Square matrix projections are equivalent exactly when they are the initial and final
projections of a partial isometry. -/
theorem isMurrayVonNeumannEquivalent_iff_exists_isPartialIsometry {p q : Matrix m m R} :
    IsMurrayVonNeumannEquivalent p q ↔
      ∃ v : Matrix m m R, IsPartialIsometry v ∧ star v * v = p ∧ v * star v = q := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · obtain ⟨v, hvp, hvq, hv⟩ := h.exists_mul_conjTranspose_mul_self_eq
    exact ⟨v, isPartialIsometry_iff.mpr hv, hvp, hvq⟩
  · rintro ⟨v, hv, rfl, rfl⟩
    exact hv.isMurrayVonNeumannEquivalent

end NonUnitalSemiring

section Semiring

variable [Semiring R] [StarRing R]

/-- **Unitary conjugacy implies equivalence.** A matrix projection `p` is equivalent to its
conjugate `u * p * star u` by a unitary `u`. -/
theorem _root_.IsStarProjection.isMurrayVonNeumannEquivalent_mul_mul_star [DecidableEq m]
    {p : Matrix m m R} (hp : IsStarProjection p) {u : Matrix m m R} (hu : u ∈ unitary _) :
    IsMurrayVonNeumannEquivalent p (u * p * star u) := by
  refine hp.isMurrayVonNeumannEquivalent_mul_mul_conjTranspose ?_
  rw [← star_eq_conjTranspose, Unitary.star_mul_self_of_mem hu, Matrix.one_mul]

/-- If a unitary conjugates `p ⊕ 0` to `0 ⊕ q` for a matrix projection `p`, then `q` is a matrix
projection equivalent to `p`. -/
theorem isMurrayVonNeumannEquivalent_of_mem_unitary_mul_fromBlocks_mul_star [DecidableEq m]
    [DecidableEq n] {p : Matrix m m R} {q : Matrix n n R} (hp : IsStarProjection p)
    {w : Matrix (m ⊕ n) (m ⊕ n) R} (hw : w ∈ unitary _)
    (hwpq : w * fromBlocks p 0 0 0 * star w = fromBlocks 0 0 0 q) :
    IsMurrayVonNeumannEquivalent p q := by
  have h := (hp.isMurrayVonNeumannEquivalent_fromBlocks_zero (n := n)).trans
    ((hp.fromBlocks_zero₁₂_zero₂₁ (.zero _)).isMurrayVonNeumannEquivalent_mul_mul_star hw)
  rw [hwpq] at h
  obtain ⟨hq₁, hq₂⟩ := h.isStarProjection_right
  have hq : IsStarProjection q := by
    refine ⟨?_, ?_⟩
    · simpa [IsIdempotentElem, fromBlocks_multiply] using hq₁.eq
    · simpa [IsSelfAdjoint, star_eq_conjTranspose, fromBlocks_conjTranspose] using hq₂.star_eq
  exact h.trans (hq.isMurrayVonNeumannEquivalent_zero_fromBlocks (n := m)).symm

/-- Diagonal matrix units of any sizes are equivalent: `single j i 1` implements
`single i i 1 ∼ single j j 1`. -/
theorem isMurrayVonNeumannEquivalent_single_one [DecidableEq m] [DecidableEq n] (i : m) (j : n) :
    IsMurrayVonNeumannEquivalent (single i i (1 : R)) (single j j 1) := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, single j i 1, by simp, by simp⟩ <;>
  simp [IsIdempotentElem, IsSelfAdjoint, star_eq_conjTranspose]

/-- A diagonal matrix unit of any size is equivalent to the identity matrix of size one. Over `ℂ`
this is the equivalence of `diag(1, 0)` with `1`, through the row `(1 0)`. -/
theorem isMurrayVonNeumannEquivalent_single_one_one [DecidableEq m] [Unique n] (i : m) :
    IsMurrayVonNeumannEquivalent (single i i (1 : R)) (1 : Matrix n n R) := by
  have h : (1 : Matrix n n R) = single default default 1 := by
    ext a b
    rw [Unique.eq_default a, Unique.eq_default b, one_apply_eq, single_apply_same]
  rw [h]
  exact isMurrayVonNeumannEquivalent_single_one i default

end Semiring

section StarOrderedRing

variable [NonUnitalRing R] [StarRing R] [PartialOrder R] [StarOrderedRing R] [IsProperStar R]

/-- Over a star-ordered proper star ring, a rectangular matrix `v` whose initial element `vᴴ * v` is
a projection is a partial isometry. -/
theorem mul_conjTranspose_mul_self_eq_of_isStarProjection {v : Matrix n m R}
    (h : IsStarProjection (vᴴ * v)) : v * vᴴ * v = v := by
  have hp : vᴴ * (v * (vᴴ * v)) = vᴴ * v := by
    rw [← Matrix.mul_assoc, h.isIdempotentElem.eq]
  have hx : (v * (vᴴ * v) - v)ᴴ * (v * (vᴴ * v) - v) = 0 := by
    simp only [conjTranspose_sub, conjTranspose_mul, conjTranspose_conjTranspose, Matrix.sub_mul,
      Matrix.mul_sub, Matrix.mul_assoc, hp, sub_self]
  rw [conjTranspose_mul_self_eq_zero, sub_eq_zero] at hx
  rwa [Matrix.mul_assoc]

/-- Over a star-ordered proper star ring, a rectangular matrix `v` whose initial element `vᴴ * v` is
a projection implements the equivalence of `vᴴ * v` with `v * vᴴ`. -/
theorem isMurrayVonNeumannEquivalent_of_isStarProjection {v : Matrix n m R}
    (h : IsStarProjection (vᴴ * v)) : IsMurrayVonNeumannEquivalent (vᴴ * v) (v * vᴴ) :=
  isMurrayVonNeumannEquivalent_of_mul_conjTranspose_mul_self_eq
    (mul_conjTranspose_mul_self_eq_of_isStarProjection h)

end StarOrderedRing

section Ring

variable [Ring R] [StarRing R] [DecidableEq m] [DecidableEq n]

/-- **Stabilized unitary conjugacy.** Equivalent matrix projections `p ∼ q` become unitarily
conjugate after stabilization: if the partial isometry `v` implements `p ∼ q`, then the
self-adjoint unitary `!![1 - p, vᴴ; v, 1 - q]` conjugates `p ⊕ 0` to `0 ⊕ q`. -/
theorem IsMurrayVonNeumannEquivalent.exists_isSelfAdjoint_mem_unitary_mul_fromBlocks_mul_star
    {p : Matrix m m R} {q : Matrix n n R} (h : IsMurrayVonNeumannEquivalent p q) :
    ∃ w : Matrix (m ⊕ n) (m ⊕ n) R, IsSelfAdjoint w ∧ w ∈ unitary _ ∧
      w * Matrix.fromBlocks p 0 0 0 * star w = Matrix.fromBlocks 0 0 0 q := by
  have hp := h.isStarProjection_left
  have hq := h.isStarProjection_right
  obtain ⟨v, hvp, hvq, hv⟩ := h.exists_mul_conjTranspose_mul_self_eq
  have hbe : v * p = v := by rw [← hvp, ← Matrix.mul_assoc, hv]
  have hea : p * vᴴ = vᴴ := by
    simpa [conjTranspose_mul, ← star_eq_conjTranspose, hp.isSelfAdjoint.star_eq] using
      congr_arg conjTranspose hbe
  have hw : IsSelfAdjoint (Matrix.fromBlocks (1 - p) vᴴ v (1 - q)) := by
    rw [IsSelfAdjoint, star_eq_conjTranspose, fromBlocks_conjTranspose, conjTranspose_sub,
      conjTranspose_sub, conjTranspose_one, conjTranspose_one, conjTranspose_conjTranspose,
      ← star_eq_conjTranspose, ← star_eq_conjTranspose, hp.isSelfAdjoint.star_eq,
      hq.isSelfAdjoint.star_eq]
  have hww := fromBlocks_one_sub_mul_self_of_mul_eq hvp hvq hea hbe
  refine ⟨_, hw, ⟨?_, ?_⟩, ?_⟩
  · rwa [hw.star_eq]
  · rwa [hw.star_eq]
  · rw [hw.star_eq,
      fromBlocks_one_sub_mul_fromBlocks_mul_fromBlocks_one_sub_of_mul_eq hvp hvq hbe]

/-- **Stabilized unitary conjugacy.** A matrix projection `p` is equivalent to `q` exactly when
`p ⊕ 0` and `0 ⊕ q` are conjugate by a unitary. -/
theorem isMurrayVonNeumannEquivalent_iff_exists_mem_unitary_mul_fromBlocks_mul_star
    {p : Matrix m m R} {q : Matrix n n R} (hp : IsStarProjection p) :
    IsMurrayVonNeumannEquivalent p q ↔ ∃ w ∈ unitary (Matrix (m ⊕ n) (m ⊕ n) R),
      w * fromBlocks p 0 0 0 * star w = fromBlocks 0 0 0 q := by
  refine ⟨fun h ↦ ?_, fun ⟨w, hw, hwpq⟩ ↦
    isMurrayVonNeumannEquivalent_of_mem_unitary_mul_fromBlocks_mul_star hp hw hwpq⟩
  obtain ⟨w, -, hw, hwpq⟩ := h.exists_isSelfAdjoint_mem_unitary_mul_fromBlocks_mul_star
  exact ⟨w, hw, hwpq⟩

end Ring

/-- Equivalent matrix projections have equal rank: if `v` implements `p ∼ q`, then
`p = vᴴ * q * v` and `q = v * p * vᴴ`. -/
theorem IsMurrayVonNeumannEquivalent.rank_eq [CommSemiring R] [StarRing R]
    [StrongRankCondition R] {p : Matrix m m R} {q : Matrix n n R}
    (h : IsMurrayVonNeumannEquivalent p q) : p.rank = q.rank := by
  obtain ⟨hp, hq, v, hvp, hvq⟩ := h
  have hp' : vᴴ * q * v = p := by
    rw [← hvq, ← hp.isIdempotentElem.eq, ← hvp]
    simp only [Matrix.mul_assoc]
  have hq' : v * p * vᴴ = q := by
    rw [← hvp, ← hq.isIdempotentElem.eq, ← hvq]
    simp only [Matrix.mul_assoc]
  refine le_antisymm ?_ ?_
  · rw [← hp']
    exact (rank_mul_le_left _ _).trans (rank_mul_le_right _ _)
  · rw [← hq']
    exact (rank_mul_le_left _ _).trans (rank_mul_le_right _ _)

end Matrix
