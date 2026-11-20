/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.CStarMatrix
public import TauCeti.Algebra.Star.PartialIsometry
public import Mathlib.Data.Matrix.ColumnRowPartitioned

/-!
# Murray–von Neumann equivalence of matrix projections

Two projections `p` and `q` in matrix algebras over a C⋆-algebra `A`, possibly of different
sizes, are *Murray–von Neumann equivalent* when there is a rectangular matrix `v` with
`vᴴ * v = p` and `v * vᴴ = q`. This is the equivalence relation on projections from which the
projection monoid `V(A)` and the group `K₀(A)` of operator K-theory are built. Comparing
projections of different sizes through rectangular matrices, rather than identifying unequal
matrix sizes, is what makes `diag(1, 0)` in `M₂(ℂ)` equivalent to `1` in `M₁(ℂ)`.

The relation is stated for `p : CStarMatrix m m A` and `q : CStarMatrix n n A` with arbitrary
finite index types `m` and `n`, using the rectangular products and conjugate transposes of
`CStarMatrix`. The algebraic part of the theory holds over any star ring. The facts that need
positivity, such as that the implementing matrix of an equivalence of projections is a partial
isometry, are proved over star-ordered rings whose star is proper, `IsProperStar`, the setting
that contains every C⋆-algebra.

## Main definitions

* `CStarMatrix.IsMurrayVonNeumannEquiv p q`: there is a rectangular `v` with `vᴴ * v = p` and
  `v * vᴴ = q`.

## Main statements

* `CStarMatrix.IsMurrayVonNeumannEquiv.refl`, `.symm`, `.trans`: Murray–von Neumann equivalence
  is reflexive and transitive on projections, and symmetric.
* `CStarMatrix.IsMurrayVonNeumannEquiv.isStarProjection_iff`: a matrix equivalent to a
  projection is a projection.
* `CStarMatrix.mul_conjTranspose_mul_self_of_isIdempotentElem`: if `vᴴ * v` is idempotent then
  `v * vᴴ * v = v`, so the implementing matrices of equivalences of projections are partial
  isometries; for square matrices,
  `CStarMatrix.isMurrayVonNeumannEquiv_iff_exists_isPartialIsometry` states this with
  `TauCeti.IsPartialIsometry`.
* `CStarMatrix.IsMurrayVonNeumannEquiv.add`: compatibility with orthogonal sums.
* `CStarMatrix.IsMurrayVonNeumannEquiv.fromBlocks`: compatibility with block sums `p ⊕ q`;
  `CStarMatrix.isMurrayVonNeumannEquiv_fromBlocks_comm` and
  `CStarMatrix.isMurrayVonNeumannEquiv_fromBlocks_assoc`: block sums are commutative and
  associative up to equivalence.
* `CStarMatrix.isMurrayVonNeumannEquiv_zero`: zero matrices of all sizes are equivalent.
* `CStarMatrix.isMurrayVonNeumannEquiv_fromBlocks_zero`: padding a projection by a zero block,
  and `CStarMatrix.IsMurrayVonNeumannEquiv.submatrix_right`: reindexing it along a bijection,
  give equivalent projections.
* `CStarMatrix.isMurrayVonNeumannEquiv_mul_mul_conjTranspose` and
  `CStarMatrix.isMurrayVonNeumannEquiv_mul_mul_star_of_mem_unitary`: unitary conjugacy, and more
  generally conjugation by a rectangular matrix isometric on the range, implies equivalence.
* `CStarMatrix.IsMurrayVonNeumannEquiv.map`: equivalence is preserved by entrywise application
  of star ring homomorphisms, such as ⋆-homomorphisms of C⋆-algebras.

## References

* B. Blackadar, *K-Theory for Operator Algebras*, 2nd ed., Cambridge University Press (1998),
  Definition 4.6.1 and Propositions 4.6.2–4.6.6.
* M. Rørdam, F. Larsen, N. Laustsen, *An Introduction to K-Theory for C⋆-Algebras*, Cambridge
  University Press (2000), Chapter 2 and Section 3.1.
-/

public section

open Matrix

namespace CStarMatrix

variable {l m n o m' A : Type*} [Fintype l] [Fintype m] [Fintype n] [Fintype o] [Fintype m']

section Basic

variable [NonUnitalNonAssocSemiring A] [Star A]

/-- Two square C⋆-matrices `p` and `q`, possibly of different sizes, are **Murray–von Neumann
equivalent** when there is a rectangular matrix `v` with `vᴴ * v = p` and `v * vᴴ = q`. The
relation is meant for projections; over a C⋆-algebra it is an equivalence relation on them. -/
def IsMurrayVonNeumannEquiv (p : CStarMatrix m m A) (q : CStarMatrix n n A) : Prop :=
  ∃ v : CStarMatrix n m A, v.conjTranspose * v = p ∧ v * v.conjTranspose = q

/-- Unfold the definition of Murray–von Neumann equivalence. -/
theorem isMurrayVonNeumannEquiv_iff {p : CStarMatrix m m A} {q : CStarMatrix n n A} :
    IsMurrayVonNeumannEquiv p q ↔
      ∃ v : CStarMatrix n m A, v.conjTranspose * v = p ∧ v * v.conjTranspose = q :=
  Iff.rfl

/-- The initial and final matrices `vᴴ * v` and `v * vᴴ` of any rectangular matrix `v` are
Murray–von Neumann equivalent. -/
theorem isMurrayVonNeumannEquiv_conjTranspose_mul_self (v : CStarMatrix n m A) :
    IsMurrayVonNeumannEquiv (v.conjTranspose * v) (v * v.conjTranspose) :=
  ⟨v, rfl, rfl⟩

/-- Zero matrices of any two sizes are Murray–von Neumann equivalent. -/
theorem isMurrayVonNeumannEquiv_zero :
    IsMurrayVonNeumannEquiv (0 : CStarMatrix m m A) (0 : CStarMatrix n n A) :=
  ⟨0, CStarMatrix.mul_zero _, CStarMatrix.zero_mul _⟩

namespace IsMurrayVonNeumannEquiv

/-- Every star projection is Murray–von Neumann equivalent to itself. -/
protected theorem refl {p : CStarMatrix m m A} (hp : IsStarProjection p) :
    IsMurrayVonNeumannEquiv p p := by
  refine ⟨p, ?_, ?_⟩ <;>
    rw [← star_eq_conjTranspose, hp.isSelfAdjoint.star_eq, hp.isIdempotentElem.eq]

/-- Murray–von Neumann equivalence is preserved by reindexing the right side along a
bijection. -/
theorem submatrix_right {p : CStarMatrix m m A} {q : CStarMatrix n n A}
    (h : IsMurrayVonNeumannEquiv p q) (e : m' ≃ n) :
    IsMurrayVonNeumannEquiv p (ofMatrix ((ofMatrix.symm q).submatrix e e)) := by
  obtain ⟨v, rfl, rfl⟩ := h
  obtain ⟨V, rfl⟩ := ofMatrix.surjective v
  refine ⟨ofMatrix (V.submatrix e id), ?_, ?_⟩
  · simp [conjTranspose_submatrix, submatrix_mul_equiv Vᴴ V id e id]
  · simp [conjTranspose_submatrix, ← submatrix_mul V Vᴴ e id e Function.bijective_id]

/-- Murray–von Neumann equivalence is preserved by applying a star-preserving non-unital ring
homomorphism to every entry, for instance a ⋆-homomorphism of C⋆-algebras. -/
protected theorem map {B F : Type*} [NonUnitalNonAssocSemiring B] [Star B]
    [FunLike F A B] [NonUnitalRingHomClass F A B] [StarHomClass F A B] (φ : F)
    {p : CStarMatrix m m A} {q : CStarMatrix n n A} (h : IsMurrayVonNeumannEquiv p q) :
    IsMurrayVonNeumannEquiv (p.map φ) (q.map φ) := by
  obtain ⟨v, rfl, rfl⟩ := h
  exact ⟨v.map φ, by rw [map_mul, map_conjTranspose], by rw [map_mul, map_conjTranspose]⟩

end IsMurrayVonNeumannEquiv

end Basic

section BlockSums

variable [NonUnitalNonAssocSemiring A] [StarAddMonoid A]

/-- Block sums of Murray–von Neumann equivalent pairs are Murray–von Neumann equivalent. -/
protected theorem IsMurrayVonNeumannEquiv.fromBlocks {p : CStarMatrix m m A}
    {p' : CStarMatrix n n A} {q : CStarMatrix l l A} {q' : CStarMatrix o o A}
    (h₁ : IsMurrayVonNeumannEquiv p p') (h₂ : IsMurrayVonNeumannEquiv q q') :
    IsMurrayVonNeumannEquiv (ofMatrix (Matrix.fromBlocks (ofMatrix.symm p) 0 0 (ofMatrix.symm q)))
      (ofMatrix (Matrix.fromBlocks (ofMatrix.symm p') 0 0 (ofMatrix.symm q'))) := by
  obtain ⟨v, rfl, rfl⟩ := h₁
  obtain ⟨w, rfl, rfl⟩ := h₂
  obtain ⟨V, rfl⟩ := ofMatrix.surjective v
  obtain ⟨W, rfl⟩ := ofMatrix.surjective w
  refine ⟨ofMatrix (Matrix.fromBlocks V 0 0 W), ?_, ?_⟩ <;>
    simp [fromBlocks_conjTranspose, fromBlocks_multiply]

/-- Block sums of star projections are commutative up to Murray–von Neumann equivalence. -/
theorem isMurrayVonNeumannEquiv_fromBlocks_comm {p : CStarMatrix m m A} {q : CStarMatrix n n A}
    (hp : IsStarProjection p) (hq : IsStarProjection q) :
    IsMurrayVonNeumannEquiv (ofMatrix (Matrix.fromBlocks (ofMatrix.symm p) 0 0 (ofMatrix.symm q)))
      (ofMatrix (Matrix.fromBlocks (ofMatrix.symm q) 0 0 (ofMatrix.symm p))) := by
  simpa [fromBlocks_submatrix_sum_swap_sum_swap] using
    ((IsMurrayVonNeumannEquiv.refl hp).fromBlocks (IsMurrayVonNeumannEquiv.refl hq)).submatrix_right
      (Equiv.sumComm n m)

/-- Block sums of star projections are associative up to Murray–von Neumann equivalence. -/
theorem isMurrayVonNeumannEquiv_fromBlocks_assoc {p : CStarMatrix m m A} {q : CStarMatrix n n A}
    {r : CStarMatrix l l A} (hp : IsStarProjection p) (hq : IsStarProjection q)
    (hr : IsStarProjection r) :
    IsMurrayVonNeumannEquiv
      (ofMatrix (Matrix.fromBlocks (Matrix.fromBlocks (ofMatrix.symm p) 0 0 (ofMatrix.symm q)) 0 0
        (ofMatrix.symm r)))
      (ofMatrix (Matrix.fromBlocks (ofMatrix.symm p) 0 0
        (Matrix.fromBlocks (ofMatrix.symm q) 0 0 (ofMatrix.symm r)))) := by
  have key : (Matrix.fromBlocks (Matrix.fromBlocks (ofMatrix.symm p) 0 0 (ofMatrix.symm q)) 0 0
      (ofMatrix.symm r)).submatrix (Equiv.sumAssoc m n l).symm (Equiv.sumAssoc m n l).symm =
      Matrix.fromBlocks (ofMatrix.symm p) 0 0
        (Matrix.fromBlocks (ofMatrix.symm q) 0 0 (ofMatrix.symm r)) := by
    ext (i | i | i) (j | j | j) <;> rfl
  simpa [key] using (((IsMurrayVonNeumannEquiv.refl hp).fromBlocks
    (IsMurrayVonNeumannEquiv.refl hq)).fromBlocks (IsMurrayVonNeumannEquiv.refl hr)).submatrix_right
      (Equiv.sumAssoc m n l).symm

/-- Padding a star projection by a zero block gives a Murray–von Neumann equivalent
projection. -/
theorem isMurrayVonNeumannEquiv_fromBlocks_zero {p : CStarMatrix m m A}
    (hp : IsStarProjection p) :
    IsMurrayVonNeumannEquiv p
      (ofMatrix (Matrix.fromBlocks (ofMatrix.symm p) 0 0 (0 : Matrix l l A))) := by
  obtain ⟨P, rfl⟩ := ofMatrix.surjective p
  have hsa : Pᴴ = P := congrArg ofMatrix.symm hp.isSelfAdjoint.star_eq
  have hid : P * P = P := congrArg ofMatrix.symm hp.isIdempotentElem.eq
  have h₁ : Pᴴ * P = P := by rw [hsa, hid]
  have h₂ : P * Pᴴ = P := by rw [hsa, hid]
  refine ⟨ofMatrix (Matrix.fromRows P 0), ?_, ?_⟩
  · conv_rhs => rw [← h₁]
    ext i j
    simp [Matrix.mul_apply, Fintype.sum_sum_type]
  · conv_rhs => rw [← h₂]
    ext (i | i) (j | j) <;> simp [Matrix.mul_apply]

end BlockSums

section Involutive

variable [NonUnitalNonAssocSemiring A] [InvolutiveStar A]

/-- Murray–von Neumann equivalence is symmetric. -/
protected theorem IsMurrayVonNeumannEquiv.symm {p : CStarMatrix m m A} {q : CStarMatrix n n A}
    (h : IsMurrayVonNeumannEquiv p q) : IsMurrayVonNeumannEquiv q p := by
  obtain ⟨v, rfl, rfl⟩ := h
  simpa only [conjTranspose_conjTranspose] using
    isMurrayVonNeumannEquiv_conjTranspose_mul_self v.conjTranspose

/-- Murray–von Neumann equivalence is a symmetric relation. -/
theorem isMurrayVonNeumannEquiv_comm {p : CStarMatrix m m A} {q : CStarMatrix n n A} :
    IsMurrayVonNeumannEquiv p q ↔ IsMurrayVonNeumannEquiv q p :=
  ⟨.symm, .symm⟩

end Involutive

namespace IsMurrayVonNeumannEquiv

variable [NonUnitalNonAssocSemiring A] [StarRing A]

/-- The left side of a Murray–von Neumann equivalence is self-adjoint. -/
theorem isSelfAdjoint_left {p : CStarMatrix m m A} {q : CStarMatrix n n A}
    (h : IsMurrayVonNeumannEquiv p q) : IsSelfAdjoint p := by
  obtain ⟨v, rfl, -⟩ := h
  rw [IsSelfAdjoint, star_eq_conjTranspose, conjTranspose_mul, conjTranspose_conjTranspose]

/-- The right side of a Murray–von Neumann equivalence is self-adjoint. -/
theorem isSelfAdjoint_right {p : CStarMatrix m m A} {q : CStarMatrix n n A}
    (h : IsMurrayVonNeumannEquiv p q) : IsSelfAdjoint q :=
  h.symm.isSelfAdjoint_left

end IsMurrayVonNeumannEquiv

/-- Conjugating a star projection `p` by a rectangular matrix `u` that is isometric on the range
of `p`, in the sense that `uᴴ * u * p = p`, gives a Murray–von Neumann equivalent matrix. -/
theorem isMurrayVonNeumannEquiv_mul_mul_conjTranspose [NonUnitalSemiring A] [StarRing A]
    {p : CStarMatrix m m A} (hp : IsStarProjection p) {u : CStarMatrix n m A}
    (hu : u.conjTranspose * u * p = p) :
    IsMurrayVonNeumannEquiv p (u * p * u.conjTranspose) := by
  have hsa : p.conjTranspose = p := hp.isSelfAdjoint.star_eq
  refine ⟨u * p, ?_, ?_⟩
  · rw [conjTranspose_mul, hsa, CStarMatrix.mul_assoc, ← CStarMatrix.mul_assoc _ u, hu,
      hp.isIdempotentElem.eq]
  · rw [conjTranspose_mul, hsa, CStarMatrix.mul_assoc, ← CStarMatrix.mul_assoc p p,
      hp.isIdempotentElem.eq, ← CStarMatrix.mul_assoc]

/-- Unitary conjugates of a star projection are Murray–von Neumann equivalent to it. -/
theorem isMurrayVonNeumannEquiv_mul_mul_star_of_mem_unitary [Semiring A] [StarRing A]
    [DecidableEq m] {p : CStarMatrix m m A} (hp : IsStarProjection p) {u : CStarMatrix m m A}
    (hu : u ∈ unitary (CStarMatrix m m A)) :
    IsMurrayVonNeumannEquiv p (u * p * star u) :=
  isMurrayVonNeumannEquiv_mul_mul_conjTranspose hp <| by
    rw [← star_eq_conjTranspose, Unitary.star_mul_self_of_mem hu, one_mul]

section PartialIsometry

variable [NonUnitalSemiring A] [StarRing A]

/-- Partial isometries with orthogonal final projections have orthogonal ranges: if
`v * vᴴ * v = v`, `w * wᴴ * w = w` and `(v * vᴴ) * (w * wᴴ) = 0`, then `vᴴ * w = 0`. -/
private theorem conjTranspose_mul_eq_zero_of_orthogonal {v : CStarMatrix n m A}
    {w : CStarMatrix n l A} (hv : v * v.conjTranspose * v = v) (hw : w * w.conjTranspose * w = w)
    (h : v * v.conjTranspose * (w * w.conjTranspose) = 0) : v.conjTranspose * w = 0 := by
  have hv' : v.conjTranspose * v * v.conjTranspose = v.conjTranspose := by
    simpa [CStarMatrix.mul_assoc] using congrArg conjTranspose hv
  calc v.conjTranspose * w
      = v.conjTranspose * v * v.conjTranspose * (w * w.conjTranspose * w) := by rw [hv', hw]
    _ = v.conjTranspose * (v * v.conjTranspose * (w * w.conjTranspose)) * w := by
      simp only [CStarMatrix.mul_assoc]
    _ = 0 := by rw [h, CStarMatrix.mul_zero, CStarMatrix.zero_mul]

end PartialIsometry

section Proper

variable [NonUnitalRing A] [StarRing A] [PartialOrder A] [StarOrderedRing A] [IsProperStar A]

/-- If `vᴴ * v` is idempotent then `v * vᴴ * v = v`: a rectangular matrix whose initial matrix is
a projection is a partial isometry. -/
theorem mul_conjTranspose_mul_self_of_isIdempotentElem {v : CStarMatrix n m A}
    (hv : IsIdempotentElem (v.conjTranspose * v)) : v * v.conjTranspose * v = v := by
  rw [CStarMatrix.mul_assoc]
  -- With `x = v * (vᴴ * v) - v`, idempotence gives `vᴴ * x = 0`, hence `xᴴ * x = 0`.
  have h₁ : v.conjTranspose * (v * (v.conjTranspose * v) - v) = 0 := by
    rw [CStarMatrix.mul_sub, ← CStarMatrix.mul_assoc, hv.eq, sub_self]
  have h₂ : (v * (v.conjTranspose * v) - v).conjTranspose * v = 0 := by
    simpa using congrArg conjTranspose h₁
  rw [← sub_eq_zero, ← conjTranspose_mul_self_eq_zero, CStarMatrix.mul_sub,
    ← CStarMatrix.mul_assoc, h₂, CStarMatrix.zero_mul, sub_zero]

/-- If `v * vᴴ` is idempotent then `v * vᴴ * v = v`: a rectangular matrix whose final matrix is
a projection is a partial isometry. -/
theorem mul_conjTranspose_mul_self_of_isIdempotentElem_mul_conjTranspose {v : CStarMatrix n m A}
    (hv : IsIdempotentElem (v * v.conjTranspose)) : v * v.conjTranspose * v = v := by
  have := mul_conjTranspose_mul_self_of_isIdempotentElem (v := v.conjTranspose)
    (by rwa [conjTranspose_conjTranspose])
  simpa [CStarMatrix.mul_assoc] using congrArg conjTranspose this

namespace IsMurrayVonNeumannEquiv

/-- A matrix Murray–von Neumann equivalent to an idempotent matrix is a star projection. -/
theorem isStarProjection_right {p : CStarMatrix m m A} {q : CStarMatrix n n A}
    (h : IsMurrayVonNeumannEquiv p q) (hp : IsIdempotentElem p) : IsStarProjection q := by
  refine ⟨?_, h.isSelfAdjoint_right⟩
  obtain ⟨v, rfl, rfl⟩ := h
  rw [IsIdempotentElem, ← CStarMatrix.mul_assoc, mul_conjTranspose_mul_self_of_isIdempotentElem hp]

/-- Murray–von Neumann equivalent matrices are star projections together. -/
theorem isStarProjection_iff {p : CStarMatrix m m A} {q : CStarMatrix n n A}
    (h : IsMurrayVonNeumannEquiv p q) : IsStarProjection p ↔ IsStarProjection q :=
  ⟨fun hp => h.isStarProjection_right hp.isIdempotentElem,
    fun hq => h.symm.isStarProjection_right hq.isIdempotentElem⟩

/-- Murray–von Neumann equivalence is transitive through an idempotent middle term, in
particular on star projections. -/
protected theorem trans {p : CStarMatrix m m A} {q : CStarMatrix n n A} {r : CStarMatrix l l A}
    (hpq : IsMurrayVonNeumannEquiv p q) (hqr : IsMurrayVonNeumannEquiv q r)
    (hq : IsIdempotentElem q) : IsMurrayVonNeumannEquiv p r := by
  obtain ⟨v, rfl, rfl⟩ := hpq
  obtain ⟨w, hw, rfl⟩ := hqr
  have hv := mul_conjTranspose_mul_self_of_isIdempotentElem_mul_conjTranspose hq
  have hw' := mul_conjTranspose_mul_self_of_isIdempotentElem (hw ▸ hq)
  refine ⟨w * v, ?_, ?_⟩
  · rw [conjTranspose_mul, CStarMatrix.mul_assoc, ← CStarMatrix.mul_assoc w.conjTranspose, hw,
      ← CStarMatrix.mul_assoc, CStarMatrix.mul_assoc, hv]
  · rw [conjTranspose_mul, CStarMatrix.mul_assoc, ← CStarMatrix.mul_assoc v,
      ← hw, ← CStarMatrix.mul_assoc, ← CStarMatrix.mul_assoc, hw']

/-- Orthogonal sums of Murray–von Neumann equivalent pairs of projections are Murray–von Neumann
equivalent: if `p ∼ p'` and `q ∼ q'` with `p`, `q` idempotent, `p * q = 0` and `p' * q' = 0`, then
`p + q ∼ p' + q'`. -/
protected theorem add {p q : CStarMatrix m m A} {p' q' : CStarMatrix n n A}
    (h₁ : IsMurrayVonNeumannEquiv p p') (h₂ : IsMurrayVonNeumannEquiv q q')
    (hp : IsIdempotentElem p) (hq : IsIdempotentElem q) (hpq : p * q = 0) (hpq' : p' * q' = 0) :
    IsMurrayVonNeumannEquiv (p + q) (p' + q') := by
  have hqp : q * p = 0 := by
    simpa [h₁.isSelfAdjoint_left.star_eq, h₂.isSelfAdjoint_left.star_eq] using congrArg star hpq
  have hqp' : q' * p' = 0 := by
    simpa [h₁.isSelfAdjoint_right.star_eq, h₂.isSelfAdjoint_right.star_eq] using
      congrArg star hpq'
  obtain ⟨v, rfl, rfl⟩ := h₁
  obtain ⟨w, rfl, rfl⟩ := h₂
  have hv := mul_conjTranspose_mul_self_of_isIdempotentElem hp
  have hw := mul_conjTranspose_mul_self_of_isIdempotentElem hq
  have hv' :=
    mul_conjTranspose_mul_self_of_isIdempotentElem_mul_conjTranspose (v := v.conjTranspose)
      (by rwa [conjTranspose_conjTranspose])
  have hw' :=
    mul_conjTranspose_mul_self_of_isIdempotentElem_mul_conjTranspose (v := w.conjTranspose)
      (by rwa [conjTranspose_conjTranspose])
  have h₁₂ := conjTranspose_mul_eq_zero_of_orthogonal hv hw hpq'
  have h₂₁ := conjTranspose_mul_eq_zero_of_orthogonal hw hv hqp'
  have h₁₂' := conjTranspose_mul_eq_zero_of_orthogonal hv' hw'
    (by rwa [conjTranspose_conjTranspose, conjTranspose_conjTranspose])
  have h₂₁' := conjTranspose_mul_eq_zero_of_orthogonal hw' hv'
    (by rwa [conjTranspose_conjTranspose, conjTranspose_conjTranspose])
  rw [conjTranspose_conjTranspose] at h₁₂' h₂₁'
  refine ⟨v + w, ?_, ?_⟩
  · rw [conjTranspose_add, CStarMatrix.add_mul, CStarMatrix.mul_add, CStarMatrix.mul_add, h₁₂, h₂₁,
      add_zero, zero_add]
  · rw [conjTranspose_add, CStarMatrix.mul_add, CStarMatrix.add_mul, CStarMatrix.add_mul, h₁₂',
      h₂₁', add_zero, zero_add]

end IsMurrayVonNeumannEquiv

/-- For square matrices and an idempotent `p`, `p` and `q` are Murray–von Neumann equivalent
exactly when `star v * v = p` and `v * star v = q` for a partial isometry `v`. -/
theorem isMurrayVonNeumannEquiv_iff_exists_isPartialIsometry {p q : CStarMatrix n n A}
    (hp : IsIdempotentElem p) :
    IsMurrayVonNeumannEquiv p q ↔
      ∃ v : CStarMatrix n n A, TauCeti.IsPartialIsometry v ∧ star v * v = p ∧ v * star v = q := by
  refine ⟨fun ⟨v, hvp, hvq⟩ => ⟨v, ?_, hvp, hvq⟩, fun ⟨v, _, hvp, hvq⟩ => ⟨v, hvp, hvq⟩⟩
  exact TauCeti.isPartialIsometry_iff.mpr
    (mul_conjTranspose_mul_self_of_isIdempotentElem (hvp ▸ hp))

end Proper

end CStarMatrix
