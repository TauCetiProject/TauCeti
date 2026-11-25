/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.CStarMatrix.Block
public import TauCeti.LinearAlgebra.Matrix.MurrayVonNeumann

/-!
# Rectangular Murray–von Neumann equivalence of `CStarMatrix` projections

Matrix projections `p : CStarMatrix m m A` and `q : CStarMatrix n n A` over a star ring `A` are
Murray–von Neumann equivalent (`CStarMatrix.MurrayVonNeumannEquiv p q`) when they are the initial
and final projections of a rectangular matrix `v : CStarMatrix n m A` (`v.conjTranspose * v = p`
and `v * v.conjTranspose = q`). Because the index types `m` and `n` may differ, this relation
identifies a projection with its zero padding and finite reindexings without casts between unequal
matrix sizes.

Reading `CStarMatrix`es as ordinary `Matrix`es identifies `CStarMatrix.MurrayVonNeumannEquiv` with
`Matrix.IsMurrayVonNeumannEquivalent`
(`CStarMatrix.murrayVonNeumannEquiv_iff_isMurrayVonNeumannEquivalent`), from which we transfer the
equivalence-relation, block-sum, zero-padding, entrywise-map, reindexing, block
commutativity/associativity, partial-isometry, and unital stabilized unitary-conjugacy laws,
together with diagonal-entry corner equivalence for `CStarMatrix.singleCorner`. Perturbation
invariance and stabilized projection homotopy over C⋆-algebras are developed in
`TauCeti.Analysis.CStarAlgebra.Projection.Perturbation`.

## References

* B. Blackadar, *K-Theory for Operator Algebras*, 2nd ed., MSRI Publications 5, Cambridge
  University Press (1998), §4.6 (Definition 4.6.1 and Propositions 4.6.2–4.6.6).
* M. Rørdam, F. Larsen, and N. Laustsen, *An Introduction to K-Theory for C⋆-Algebras*, London
  Mathematical Society Student Texts 49, Cambridge University Press (2000), Chapter 2.
-/

public section

open Matrix TauCeti

namespace CStarMatrix

variable {A B m n k l : Type*} [Fintype m] [Fintype n] [Fintype k] [Fintype l]

section Algebraic

variable [NonUnitalSemiring A] [StarRing A]
  {p : CStarMatrix m m A} {q : CStarMatrix n n A} {r : CStarMatrix k k A}

/-- Two matrix projections are Murray–von Neumann equivalent when a rectangular matrix has
them as its initial and final projections. The projection conditions are part of the relation. -/
def MurrayVonNeumannEquiv (p : CStarMatrix m m A) (q : CStarMatrix n n A) : Prop :=
  IsStarProjection p ∧ IsStarProjection q ∧
    ∃ v : CStarMatrix n m A, v.conjTranspose * v = p ∧ v * v.conjTranspose = q

/-- `MurrayVonNeumannEquiv` on `CStarMatrix` agrees with `Matrix.IsMurrayVonNeumannEquivalent` on
the underlying matrices. -/
theorem murrayVonNeumannEquiv_iff_isMurrayVonNeumannEquivalent :
    MurrayVonNeumannEquiv p q ↔
      Matrix.IsMurrayVonNeumannEquivalent (ofMatrix.symm p) (ofMatrix.symm q) := by
  rw [MurrayVonNeumannEquiv, Matrix.isMurrayVonNeumannEquivalent_iff,
    isStarProjection_ofMatrix_symm_iff, isStarProjection_ofMatrix_symm_iff]
  refine and_congr_right fun _ => and_congr_right fun _ => ofMatrix.symm.exists_congr fun v => ?_
  simp only [← ofMatrix.symm.injective.eq_iff, ofMatrix_symm_mul, ofMatrix_symm_conjTranspose]

namespace MurrayVonNeumannEquiv

/-- The initial matrix of a Murray–von Neumann equivalence is a projection. -/
theorem isStarProjection_left (h : MurrayVonNeumannEquiv p q) : IsStarProjection p :=
  h.1

/-- The final matrix of a Murray–von Neumann equivalence is a projection. -/
theorem isStarProjection_right (h : MurrayVonNeumannEquiv p q) : IsStarProjection q :=
  h.2.1

/-- Extract a rectangular implementing matrix. -/
theorem exists_matrix (h : MurrayVonNeumannEquiv p q) :
    ∃ v : CStarMatrix n m A, v.conjTranspose * v = p ∧ v * v.conjTranspose = q :=
  h.2.2

/-- Every matrix projection is Murray–von Neumann equivalent to itself. -/
protected theorem refl (hp : IsStarProjection p) : MurrayVonNeumannEquiv p p :=
  murrayVonNeumannEquiv_iff_isMurrayVonNeumannEquivalent.mpr
    (.refl (isStarProjection_ofMatrix_symm_iff.mpr hp))

/-- Rectangular Murray–von Neumann equivalence is symmetric. -/
@[symm]
protected theorem symm (h : MurrayVonNeumannEquiv p q) : MurrayVonNeumannEquiv q p :=
  murrayVonNeumannEquiv_iff_isMurrayVonNeumannEquivalent.mpr
    (murrayVonNeumannEquiv_iff_isMurrayVonNeumannEquivalent.mp h).symm

/-- Zero projections of any two finite sizes are equivalent. -/
protected theorem zero : MurrayVonNeumannEquiv (0 : CStarMatrix m m A)
    (0 : CStarMatrix n n A) :=
  ⟨.zero _, .zero _, 0, by simp, by simp⟩

/-- Block-diagonal sums of equivalent projections are equivalent. -/
theorem fromBlocks {p' : CStarMatrix k k A} {q' : CStarMatrix l l A}
    (h : MurrayVonNeumannEquiv p q) (h' : MurrayVonNeumannEquiv p' q') :
    MurrayVonNeumannEquiv (CStarMatrix.fromBlocks p 0 0 p')
      (CStarMatrix.fromBlocks q 0 0 q') := by
  rw [murrayVonNeumannEquiv_iff_isMurrayVonNeumannEquivalent, ofMatrix_symm_fromBlocks,
    ofMatrix_symm_fromBlocks, ofMatrix_symm_zero, ofMatrix_symm_zero]
  exact (murrayVonNeumannEquiv_iff_isMurrayVonNeumannEquivalent.mp h).fromBlocks
    (murrayVonNeumannEquiv_iff_isMurrayVonNeumannEquivalent.mp h')

/-- A nonunital star ring homomorphism preserves rectangular equivalence entrywise. -/
theorem map [NonUnitalSemiring B] [StarRing B] {F : Type*} [FunLike F A B]
    [NonUnitalRingHomClass F A B] [StarHomClass F A B]
    (h : MurrayVonNeumannEquiv p q) (f : F) :
    MurrayVonNeumannEquiv (p.map f) (q.map f) :=
  murrayVonNeumannEquiv_iff_isMurrayVonNeumannEquivalent.mpr
    ((murrayVonNeumannEquiv_iff_isMurrayVonNeumannEquivalent.mp h).map f)

/-- Padding a projection in the top-left corner by a zero block does not change its rectangular
equivalence class. -/
theorem pad_zero (hp : IsStarProjection p) :
    MurrayVonNeumannEquiv p (CStarMatrix.fromBlocks p (0 : CStarMatrix m k A) 0 0) := by
  rw [murrayVonNeumannEquiv_iff_isMurrayVonNeumannEquivalent, ofMatrix_symm_fromBlocks,
    ofMatrix_symm_zero, ofMatrix_symm_zero]
  exact (isStarProjection_ofMatrix_symm_iff.mpr hp).isMurrayVonNeumannEquivalent_fromBlocks_zero

/-- A Murray–von Neumann equivalence is implemented by a matrix supported on its initial
projection. -/
theorem exists_matrix_mul_eq_self (h : MurrayVonNeumannEquiv p q) :
    ∃ v : CStarMatrix n m A,
      v.conjTranspose * v = p ∧ v * v.conjTranspose = q ∧ v * p = v := by
  obtain ⟨v, hvp, hvq, hv⟩ :=
    (murrayVonNeumannEquiv_iff_isMurrayVonNeumannEquivalent.mp
      h).exists_mul_conjTranspose_mul_self_eq
  refine ⟨ofMatrix v, ofMatrix.symm.injective ?_, ofMatrix.symm.injective ?_,
    ofMatrix.symm.injective ?_⟩
  · simpa only [ofMatrix_symm_mul, ofMatrix_symm_conjTranspose, Equiv.symm_apply_apply] using hvp
  · simpa only [ofMatrix_symm_mul, ofMatrix_symm_conjTranspose, Equiv.symm_apply_apply] using hvq
  · simpa only [ofMatrix_symm_mul, Equiv.symm_apply_apply, ← hvp, ← Matrix.mul_assoc] using hv

/-- Rectangular Murray–von Neumann equivalence is transitive. -/
@[trans]
protected theorem trans (h : MurrayVonNeumannEquiv p q) (h' : MurrayVonNeumannEquiv q r) :
    MurrayVonNeumannEquiv p r :=
  murrayVonNeumannEquiv_iff_isMurrayVonNeumannEquivalent.mpr
    ((murrayVonNeumannEquiv_iff_isMurrayVonNeumannEquivalent.mp h).trans
      (murrayVonNeumannEquiv_iff_isMurrayVonNeumannEquivalent.mp h'))

end MurrayVonNeumannEquiv

/-- The witness criterion for Murray–von Neumann equivalence of given projections. -/
theorem murrayVonNeumannEquiv_iff (hp : IsStarProjection p) (hq : IsStarProjection q) :
    MurrayVonNeumannEquiv p q ↔
      ∃ v : CStarMatrix n m A, v.conjTranspose * v = p ∧ v * v.conjTranspose = q :=
  ⟨MurrayVonNeumannEquiv.exists_matrix, fun h => ⟨hp, hq, h⟩⟩

/-- Reflexivity characterizes the matrices on which the relation is defined. -/
@[simp]
theorem murrayVonNeumannEquiv_self_iff : MurrayVonNeumannEquiv p p ↔ IsStarProjection p :=
  ⟨MurrayVonNeumannEquiv.isStarProjection_left, MurrayVonNeumannEquiv.refl⟩

/-- For equal matrix sizes, two matrices are Murray–von Neumann equivalent if and only if they
are the initial and final projections of some partial isometry. -/
theorem murrayVonNeumannEquiv_iff_exists_partialIsometry {q : CStarMatrix m m A} :
    MurrayVonNeumannEquiv p q ↔
      ∃ v : CStarMatrix m m A, TauCeti.IsPartialIsometry v ∧ star v * v = p ∧
        v * star v = q := by
  constructor
  · intro h
    obtain ⟨v, hv, hv', hvp⟩ := h.exists_matrix_mul_eq_self
    simp only [← star_eq_conjTranspose] at hv hv'
    refine ⟨v, ?_, hv, hv'⟩
    rw [TauCeti.isPartialIsometry_iff, mul_assoc, hv]
    exact hvp
  · rintro ⟨v, hv, rfl, rfl⟩
    exact ⟨hv.isStarProjection_star_mul_self, hv.isStarProjection_mul_star_self, v,
      by rw [star_eq_conjTranspose], by rw [star_eq_conjTranspose]⟩

/-- Only the zero projection is equivalent to a zero projection, in any matrix size. -/
@[simp]
theorem murrayVonNeumannEquiv_zero_iff :
    MurrayVonNeumannEquiv p (0 : CStarMatrix n n A) ↔ p = 0 := by
  rw [murrayVonNeumannEquiv_iff_isMurrayVonNeumannEquivalent, ofMatrix_symm_zero,
    Matrix.isMurrayVonNeumannEquivalent_zero_right_iff, ← ofMatrix_symm_zero,
    ofMatrix.symm.injective.eq_iff]

/-- Only zero is equivalent to the zero projection on the initial side. -/
@[simp]
theorem zero_murrayVonNeumannEquiv_iff :
    MurrayVonNeumannEquiv (0 : CStarMatrix n n A) p ↔ p = 0 :=
  ⟨fun h => murrayVonNeumannEquiv_zero_iff.mp h.symm,
    fun h => h ▸ MurrayVonNeumannEquiv.zero⟩

/-- Reindexing a star projection along any bijection `e : m ≃ n` yields a Murray–von Neumann
equivalent projection. -/
theorem _root_.IsStarProjection.murrayVonNeumannEquiv_reindex
    (hp : IsStarProjection p) (e : m ≃ n) :
    MurrayVonNeumannEquiv p (reindexₐ ℕ A e p) := by
  rw [murrayVonNeumannEquiv_iff_isMurrayVonNeumannEquivalent, ofMatrix_symm_reindexₐ]
  exact (isStarProjection_ofMatrix_symm_iff.mpr hp).isMurrayVonNeumannEquivalent_reindex e

/-- `MurrayVonNeumannEquiv` is invariant under arbitrary finite reindexings on both sides. -/
@[simp]
theorem MurrayVonNeumannEquiv.reindex_iff (e₁ : m ≃ k) (e₂ : n ≃ l) :
    MurrayVonNeumannEquiv (reindexₐ ℕ A e₁ p) (reindexₐ ℕ A e₂ q) ↔
      MurrayVonNeumannEquiv p q := by
  simp only [murrayVonNeumannEquiv_iff_isMurrayVonNeumannEquivalent, ofMatrix_symm_reindexₐ]
  refine ⟨fun h => ?_, fun h => h.reindex e₁ e₂⟩
  simpa using h.reindex e₁.symm e₂.symm

/-- Placing a star projection `q` in the bottom-right corner (`CStarMatrix.fromBlocks 0 0 0 q`)
preserves its Murray–von Neumann equivalence class. -/
theorem _root_.IsStarProjection.murrayVonNeumannEquiv_inrCorner (hq : IsStarProjection q) :
    MurrayVonNeumannEquiv q (CStarMatrix.fromBlocks (0 : CStarMatrix m m A) 0 0 q) := by
  rw [murrayVonNeumannEquiv_iff_isMurrayVonNeumannEquivalent, ofMatrix_symm_fromBlocks,
    ofMatrix_symm_zero, ofMatrix_symm_zero]
  exact (isStarProjection_ofMatrix_symm_iff.mpr hq).isMurrayVonNeumannEquivalent_zero_fromBlocks

/-- Block-diagonal direct sum of star projections is commutative up to `MurrayVonNeumannEquiv`. -/
theorem _root_.IsStarProjection.murrayVonNeumannEquiv_fromBlocks_comm
    (hp : IsStarProjection p) (hq : IsStarProjection q) :
    MurrayVonNeumannEquiv (CStarMatrix.fromBlocks p 0 0 q) (CStarMatrix.fromBlocks q 0 0 p) := by
  rw [murrayVonNeumannEquiv_iff_isMurrayVonNeumannEquivalent, ofMatrix_symm_fromBlocks,
    ofMatrix_symm_fromBlocks, ofMatrix_symm_zero, ofMatrix_symm_zero]
  exact Matrix.isMurrayVonNeumannEquivalent_fromBlocks_comm
    (isStarProjection_ofMatrix_symm_iff.mpr hp) (isStarProjection_ofMatrix_symm_iff.mpr hq)

/-- Block-diagonal direct sum of star projections is associative up to `MurrayVonNeumannEquiv`. -/
theorem _root_.IsStarProjection.murrayVonNeumannEquiv_fromBlocks_assoc
    (hp : IsStarProjection p) (hq : IsStarProjection q) (hr : IsStarProjection r) :
    MurrayVonNeumannEquiv
      (CStarMatrix.fromBlocks (CStarMatrix.fromBlocks p 0 0 q) 0 0 r)
      (CStarMatrix.fromBlocks p 0 0 (CStarMatrix.fromBlocks q 0 0 r)) := by
  rw [murrayVonNeumannEquiv_iff_isMurrayVonNeumannEquivalent]
  simp only [ofMatrix_symm_fromBlocks, ofMatrix_symm_zero]
  exact Matrix.isMurrayVonNeumannEquivalent_fromBlocks_assoc
    (isStarProjection_ofMatrix_symm_iff.mpr hp) (isStarProjection_ofMatrix_symm_iff.mpr hq)
    (isStarProjection_ofMatrix_symm_iff.mpr hr)

end Algebraic

/-- A `1 × 1` star projection `toOneByOne u ℕ A a` is Murray–von Neumann equivalent to its `(i, i)`
diagonal corner `singleCorner i a` in `CStarMatrix n n A`. -/
theorem _root_.IsStarProjection.murrayVonNeumannEquiv_singleCorner {u : Type*}
    [Unique u] [DecidableEq n] [NonUnitalSemiring A] [StarRing A] {a : A}
    (ha : IsStarProjection a) (i : n) :
    MurrayVonNeumannEquiv (toOneByOne u ℕ A a) (singleCorner (R := ℕ) i a) := by
  refine ⟨ha.map (toOneByOne u ℕ A), (isStarProjection_singleCorner (R := ℕ) i).mpr ha,
    ofMatrix (Matrix.single i (default : u) a), ?_, ?_⟩
  · ext x y
    rw [Subsingleton.elim x default, Subsingleton.elim y default]
    simp only [mul_apply, conjTranspose_apply, ofMatrix_apply, toOneByOne_apply]
    rw [Finset.sum_eq_single i (fun j _ hji => by simp [hji.symm])
      (fun hi => absurd (Finset.mem_univ i) hi)]
    simp [ha.isSelfAdjoint.star_eq, ha.isIdempotentElem.eq]
  · ext j s
    simp only [mul_apply, Finset.univ_unique, Finset.sum_singleton, conjTranspose_apply,
      ofMatrix_apply, singleCorner_apply]
    rcases eq_or_ne i j with rfl | hj
    · rcases eq_or_ne i s with rfl | hs
      · simp [ha.isSelfAdjoint.star_eq, ha.isIdempotentElem.eq]
      · simp [hs]
    · simp [hj]

/-- Over a star-ordered ring with proper star, if `IsStarProjection p` and
`v.conjTranspose * v = p`, `v * v.conjTranspose = q`, then `q` is automatically a star projection
and `MurrayVonNeumannEquiv p q`. -/
theorem MurrayVonNeumannEquiv.of_conjTranspose_mul_self
    [NonUnitalRing A] [StarRing A] [PartialOrder A] [StarOrderedRing A] [IsProperStar A]
    {p : CStarMatrix m m A} {q : CStarMatrix n n A} (hp : IsStarProjection p)
    (v : CStarMatrix n m A) (hv₁ : v.conjTranspose * v = p) (hv₂ : v * v.conjTranspose = q) :
    MurrayVonNeumannEquiv p q := by
  rw [← hv₁, ← hv₂, murrayVonNeumannEquiv_iff_isMurrayVonNeumannEquivalent,
    ofMatrix_symm_mul, ofMatrix_symm_mul, ofMatrix_symm_conjTranspose]
  exact Matrix.isMurrayVonNeumannEquivalent_of_isStarProjection
    (by simpa only [← ofMatrix_symm_conjTranspose, ← ofMatrix_symm_mul, hv₁,
      isStarProjection_ofMatrix_symm_iff] using hp)

/-- Unitary conjugacy implies Murray–von Neumann equivalence. -/
theorem murrayVonNeumannEquiv_unitary_conj [Semiring B] [StarRing B] [DecidableEq m]
    {p : CStarMatrix m m B} (hp : IsStarProjection p) (u : unitary (CStarMatrix m m B)) :
    MurrayVonNeumannEquiv p ((u : CStarMatrix m m B) * p * star (u : CStarMatrix m m B)) := by
  rw [murrayVonNeumannEquiv_iff_isMurrayVonNeumannEquivalent, ofMatrix_symm_mul, ofMatrix_symm_mul,
    ofMatrix_symm_star, ← Matrix.star_eq_conjTranspose]
  exact (isStarProjection_ofMatrix_symm_iff.mpr hp).isMurrayVonNeumannEquivalent_mul_mul_star
    (ofMatrix_symm_mem_unitary_iff.mpr (SetLike.coe_mem u))

/-- Over a unital star ring, Murray–von Neumann equivalent projections become conjugate by a
self-adjoint unitary after block stabilization (`fromBlocks p 0 0 0` to `fromBlocks 0 0 0 q`). -/
theorem MurrayVonNeumannEquiv.exists_isSelfAdjoint_unitary_conj_fromBlocks
    [Ring B] [StarRing B] [DecidableEq m] [DecidableEq n]
    {p : CStarMatrix m m B} {q : CStarMatrix n n B} (h : MurrayVonNeumannEquiv p q) :
    ∃ u : unitary (CStarMatrix (m ⊕ n) (m ⊕ n) B),
      IsSelfAdjoint (u : CStarMatrix (m ⊕ n) (m ⊕ n) B) ∧
      (u : CStarMatrix (m ⊕ n) (m ⊕ n) B) * CStarMatrix.fromBlocks p 0 0 0 *
        star (u : CStarMatrix (m ⊕ n) (m ⊕ n) B) = CStarMatrix.fromBlocks 0 0 0 q := by
  obtain ⟨w, hw_sa, hw_u, hw_conj⟩ :=
    (murrayVonNeumannEquiv_iff_isMurrayVonNeumannEquivalent.mp
      h).exists_isSelfAdjoint_mem_unitary_mul_fromBlocks_mul_star
  refine ⟨⟨ofMatrix w, ofMatrix_mem_unitary_iff.mpr hw_u⟩, isSelfAdjoint_ofMatrix_iff.mpr hw_sa,
    ofMatrix.symm.injective ?_⟩
  simpa only [ofMatrix_symm_mul, ofMatrix_symm_star, ofMatrix_symm_fromBlocks,
    ofMatrix_symm_zero, Equiv.symm_apply_apply, ← Matrix.star_eq_conjTranspose] using hw_conj

/-- Over a unital star ring, a matrix projection `p` is Murray–von Neumann equivalent to `q` iff
`fromBlocks p 0 0 0` and `fromBlocks 0 0 0 q` are unitarily conjugate. -/
theorem murrayVonNeumannEquiv_iff_exists_unitary_conj_fromBlocks
    [Ring B] [StarRing B] [DecidableEq m] [DecidableEq n]
    {p : CStarMatrix m m B} {q : CStarMatrix n n B} (hp : IsStarProjection p) :
    MurrayVonNeumannEquiv p q ↔
      ∃ u : unitary (CStarMatrix (m ⊕ n) (m ⊕ n) B),
        (u : CStarMatrix (m ⊕ n) (m ⊕ n) B) * fromBlocks p 0 0 0 *
          star (u : CStarMatrix (m ⊕ n) (m ⊕ n) B) = fromBlocks 0 0 0 q := by
  rw [murrayVonNeumannEquiv_iff_isMurrayVonNeumannEquivalent,
    Matrix.isMurrayVonNeumannEquivalent_iff_exists_mem_unitary_mul_fromBlocks_mul_star
      (isStarProjection_ofMatrix_symm_iff.mpr hp)]
  constructor
  · rintro ⟨w, hw, hwpq⟩
    refine ⟨⟨ofMatrix w, ofMatrix_mem_unitary_iff.mpr hw⟩, ofMatrix.symm.injective ?_⟩
    simpa only [ofMatrix_symm_mul, ofMatrix_symm_star, ofMatrix_symm_fromBlocks,
      ofMatrix_symm_zero, Equiv.symm_apply_apply, ← Matrix.star_eq_conjTranspose] using hwpq
  · rintro ⟨u, hu⟩
    refine ⟨ofMatrix.symm (u : CStarMatrix (m ⊕ n) (m ⊕ n) B),
      ofMatrix_symm_mem_unitary_iff.mpr (SetLike.coe_mem u), ?_⟩
    simpa only [ofMatrix_symm_mul, ofMatrix_symm_star, ofMatrix_symm_fromBlocks,
      ofMatrix_symm_zero, ← Matrix.star_eq_conjTranspose] using congrArg ofMatrix.symm hu

end CStarMatrix
