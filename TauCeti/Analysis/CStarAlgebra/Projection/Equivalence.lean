/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.CStarMatrix.Block
public import TauCeti.Analysis.CStarAlgebra.Projection.Homotopy
public import TauCeti.Algebra.Star.PartialIsometry
public import TauCeti.LinearAlgebra.Matrix.MurrayVonNeumann
import Mathlib.Analysis.CStarAlgebra.Unitization
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Tactic.LinearCombination
import TauCeti.Data.Matrix.Block

/-!
# Rectangular Murray–von Neumann equivalence and stabilized projection homotopy

Matrix projections are Murray–von Neumann equivalent when they are the initial and final
projections of a rectangular matrix. The index types may differ, so this relation identifies
a projection with its zero padding, without identifying different matrix sizes by casts.

We prove reflexivity on projections, symmetry, transitivity, compatibility with block sums,
reindexing, and orthogonal addition, preservation by nonunital star homomorphisms, the bridge to
`Matrix.IsMurrayVonNeumannEquivalent`, stabilized self-adjoint unitary conjugacy, and — over
possibly non-unital C⋆-algebras — the equivalence between Murray–von Neumann equivalence and
stabilized projection homotopy (as well as stabilized unitary conjugacy in `U₀` over unital
C⋆-algebras). No unit, separability, or cancellation is assumed for the algebraic or homotopy
equivalences.

The algebraic matrix calculations use Mathlib's underlying `Matrix` operations, which are the
operations used to define `CStarMatrix` multiplication and conjugate transpose.

## References

* B. Blackadar, *K-Theory for Operator Algebras*, §4.6 (Definition 4.6.1, Propositions 4.6.2–4.6.6)
  and §5.1.
* M. Rørdam, F. Larsen, N. Laustsen, *An Introduction to K-Theory for C⋆-Algebras*, LMS Student
  Texts 49, Cambridge University Press (2000), §§2.1–2.2.
-/

public section

open scoped Matrix Real unitInterval

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
  ⟨hp, hp, p, by simpa only [← star_eq_conjTranspose, hp.isSelfAdjoint.star_eq] using
    hp.isIdempotentElem.eq, by simpa only [← star_eq_conjTranspose,
      hp.isSelfAdjoint.star_eq] using hp.isIdempotentElem.eq⟩

/-- Rectangular Murray–von Neumann equivalence is symmetric. -/
@[symm]
protected theorem symm (h : MurrayVonNeumannEquiv p q) : MurrayVonNeumannEquiv q p := by
  obtain ⟨hp, hq, v, hv, hv'⟩ := h
  exact ⟨hq, hp, v.conjTranspose, by simpa using hv', by simpa using hv⟩

/-- Zero projections of any two finite sizes are equivalent. -/
protected theorem zero : MurrayVonNeumannEquiv (0 : CStarMatrix m m A)
    (0 : CStarMatrix n n A) :=
  ⟨.zero _, .zero _, 0, by simp, by simp⟩

/-- Block-diagonal sums of equivalent projections are equivalent. -/
theorem fromBlocks {p' : CStarMatrix k k A} {q' : CStarMatrix l l A}
    (h : MurrayVonNeumannEquiv p q) (h' : MurrayVonNeumannEquiv p' q') :
    MurrayVonNeumannEquiv (ofMatrix (Matrix.fromBlocks (ofMatrix.symm p) 0 0 (ofMatrix.symm p')))
      (ofMatrix (Matrix.fromBlocks (ofMatrix.symm q) 0 0 (ofMatrix.symm q'))) := by
  obtain ⟨hp, hq, v, hv, hv'⟩ := h
  obtain ⟨hp', hq', w, hw, hw'⟩ := h'
  refine ⟨⟨hp.isIdempotentElem.fromBlocks_zero₁₂_zero₂₁ hp'.isIdempotentElem,
    hp.isSelfAdjoint.isHermitian.fromBlocks (by simp) hp'.isSelfAdjoint.isHermitian⟩,
    ⟨hq.isIdempotentElem.fromBlocks_zero₁₂_zero₂₁ hq'.isIdempotentElem,
      hq.isSelfAdjoint.isHermitian.fromBlocks (by simp) hq'.isSelfAdjoint.isHermitian⟩,
    ofMatrix (Matrix.fromBlocks (ofMatrix.symm v) 0 0 (ofMatrix.symm w)), ?_, ?_⟩
  · apply ofMatrix.symm.injective
    simpa only [ofMatrix_symm_mul, ofMatrix_symm_conjTranspose, Equiv.symm_apply_apply,
      Matrix.fromBlocks_conjTranspose, Matrix.conjTranspose_zero,
      Matrix.fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
      using congrArg₂ (fun x y => Matrix.fromBlocks x 0 0 y)
        (congrArg ofMatrix.symm hv) (congrArg ofMatrix.symm hw)
  · apply ofMatrix.symm.injective
    simpa only [ofMatrix_symm_mul, ofMatrix_symm_conjTranspose, Equiv.symm_apply_apply,
      Matrix.fromBlocks_conjTranspose, Matrix.conjTranspose_zero,
      Matrix.fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
      using congrArg₂ (fun x y => Matrix.fromBlocks x 0 0 y)
        (congrArg ofMatrix.symm hv') (congrArg ofMatrix.symm hw')

/-- A nonunital star ring homomorphism preserves rectangular equivalence entrywise. -/
theorem map [NonUnitalSemiring B] [StarRing B] {F : Type*} [FunLike F A B]
    [NonUnitalRingHomClass F A B] [StarHomClass F A B]
    (h : MurrayVonNeumannEquiv p q) (f : F) :
    MurrayVonNeumannEquiv (p.map f) (q.map f) := by
  obtain ⟨hp, hq, v, hv, hv'⟩ := h
  have hpf : ofMatrix.symm (p.map f) = (ofMatrix.symm p).map f := rfl
  have hqf : ofMatrix.symm (q.map f) = (ofMatrix.symm q).map f := rfl
  have hvf : ofMatrix.symm (v.map f) = (ofMatrix.symm v).map f := rfl
  have hf : Function.Semiconj f star star := map_star f
  refine ⟨isStarProjection_iff'.mpr ⟨?_, ?_⟩, isStarProjection_iff'.mpr ⟨?_, ?_⟩, v.map f, ?_,
    ?_⟩ <;> apply ofMatrix.symm.injective
  · simpa only [ofMatrix_symm_mul, ofMatrix_symm_star, ofMatrix_symm_conjTranspose, hpf, hqf, hvf,
      Matrix.map_mul, Matrix.conjTranspose_map f hf] using
      congrArg (Matrix.map · f) (congrArg ofMatrix.symm hp.isIdempotentElem.eq)
  · simpa only [ofMatrix_symm_mul, ofMatrix_symm_star, ofMatrix_symm_conjTranspose, hpf, hqf, hvf,
      Matrix.map_mul, Matrix.conjTranspose_map f hf] using
      congrArg (Matrix.map · f) (congrArg ofMatrix.symm hp.isSelfAdjoint.star_eq)
  · simpa only [ofMatrix_symm_mul, ofMatrix_symm_star, ofMatrix_symm_conjTranspose, hpf, hqf, hvf,
      Matrix.map_mul, Matrix.conjTranspose_map f hf] using
      congrArg (Matrix.map · f) (congrArg ofMatrix.symm hq.isIdempotentElem.eq)
  · simpa only [ofMatrix_symm_mul, ofMatrix_symm_star, ofMatrix_symm_conjTranspose, hpf, hqf, hvf,
      Matrix.map_mul, Matrix.conjTranspose_map f hf] using
      congrArg (Matrix.map · f) (congrArg ofMatrix.symm hq.isSelfAdjoint.star_eq)
  · simpa only [ofMatrix_symm_mul, ofMatrix_symm_star, ofMatrix_symm_conjTranspose, hpf, hqf, hvf,
      Matrix.map_mul, Matrix.conjTranspose_map f hf] using
      congrArg (Matrix.map · f) (congrArg ofMatrix.symm hv)
  · simpa only [ofMatrix_symm_mul, ofMatrix_symm_star, ofMatrix_symm_conjTranspose, hpf, hqf, hvf,
      Matrix.map_mul, Matrix.conjTranspose_map f hf] using
      congrArg (Matrix.map · f) (congrArg ofMatrix.symm hv')

/-- Padding a projection by a zero block does not change its rectangular equivalence class. -/
theorem pad_zero (hp : IsStarProjection p) :
    MurrayVonNeumannEquiv p
      (ofMatrix (Matrix.fromBlocks (ofMatrix.symm p) 0 0 (0 : Matrix k k A))) := by
  have hsa : (ofMatrix.symm p)ᴴ = ofMatrix.symm p := by
    simpa only [ofMatrix_symm_star] using congrArg ofMatrix.symm hp.isSelfAdjoint.star_eq
  have hid : ofMatrix.symm p * ofMatrix.symm p = ofMatrix.symm p := by
    simpa only [ofMatrix_symm_mul] using congrArg ofMatrix.symm hp.isIdempotentElem.eq
  refine ⟨hp, ⟨hp.isIdempotentElem.fromBlocks_zero₁₂_zero₂₁ .zero,
    hp.isSelfAdjoint.isHermitian.fromBlocks (by simp) Matrix.isHermitian_zero⟩,
    ofMatrix (Matrix.fromRows (ofMatrix.symm p) (0 : Matrix k m A)), ?_, ?_⟩ <;>
    apply ofMatrix.symm.injective
  · simp only [ofMatrix_symm_mul, ofMatrix_symm_conjTranspose, Equiv.symm_apply_apply,
      Matrix.conjTranspose_fromRows_eq_fromCols_conjTranspose, Matrix.conjTranspose_zero, hsa]
    ext i j
    simpa [Matrix.mul_apply] using congrFun (congrFun hid i) j
  · simp only [ofMatrix_symm_mul, ofMatrix_symm_conjTranspose, Equiv.symm_apply_apply,
      Matrix.conjTranspose_fromRows_eq_fromCols_conjTranspose, Matrix.conjTranspose_zero, hsa]
    ext (i | i) (j | j)
    · simpa [Matrix.mul_apply] using congrFun (congrFun hid i) j
    · simp [Matrix.mul_apply]
    · simp [Matrix.mul_apply]
    · simp [Matrix.mul_apply]

/-- A Murray–von Neumann equivalence is implemented by a matrix supported on its initial
projection. -/
theorem exists_matrix_mul_eq_self (h : MurrayVonNeumannEquiv p q) :
    ∃ v : CStarMatrix n m A,
      v.conjTranspose * v = p ∧ v * v.conjTranspose = q ∧ v * p = v := by
  obtain ⟨hp, hq, v, hv, hv'⟩ := h
  have hpp : p * p = p := hp.isIdempotentElem.eq
  have hpc : p.conjTranspose = p := by rw [← star_eq_conjTranspose, hp.isSelfAdjoint.star_eq]
  refine ⟨v * p, ?_, ?_, by rw [mul_assoc_rectangular, hpp]⟩
  · calc
      _ = p * (v.conjTranspose * v) * p := by
        simp only [conjTranspose_mul, hpc, mul_assoc_rectangular]
      _ = p := by rw [hv, hpp, hpp]
  · calc
      _ = v * (p * p) * v.conjTranspose := by
        simp only [conjTranspose_mul, hpc, mul_assoc_rectangular]
      _ = (v * v.conjTranspose) * (v * v.conjTranspose) := by
        rw [hpp, ← hv]
        simp only [mul_assoc_rectangular]
      _ = q := by rw [hv', hq.isIdempotentElem.eq]

/-- Rectangular Murray–von Neumann equivalence is transitive. -/
@[trans]
protected theorem trans (h : MurrayVonNeumannEquiv p q) (h' : MurrayVonNeumannEquiv q r) :
    MurrayVonNeumannEquiv p r := by
  obtain ⟨v, hv, hv', hvp⟩ := h.exists_matrix_mul_eq_self
  obtain ⟨w, hw, hw', hwq⟩ := h'.exists_matrix_mul_eq_self
  have hqv : q * v = v := by
    rw [← hv', mul_assoc_rectangular, hv, hvp]
  refine ⟨h.isStarProjection_left, h'.isStarProjection_right, w * v, ?_, ?_⟩
  · calc
      _ = v.conjTranspose * (w.conjTranspose * w) * v := by
        simp only [conjTranspose_mul, mul_assoc_rectangular]
      _ = v.conjTranspose * v := by rw [hw, mul_assoc_rectangular, hqv]
      _ = p := hv
  · calc
      _ = w * (v * v.conjTranspose) * w.conjTranspose := by
        simp only [conjTranspose_mul, mul_assoc_rectangular]
      _ = w * w.conjTranspose := by rw [hv', hwq]
      _ = r := hw'

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
  refine ⟨?_, fun h => h ▸ .zero⟩
  rintro ⟨hp, _, v, hv, hv'⟩
  calc
    p = p * p := hp.isIdempotentElem.eq.symm
    _ = v.conjTranspose * (v * v.conjTranspose) * v := by
      rw [← hv]
      simp only [mul_assoc_rectangular]
    _ = 0 := by rw [hv', CStarMatrix.mul_zero, CStarMatrix.zero_mul]

/-- Only zero is equivalent to the zero projection on the initial side. -/
@[simp]
theorem zero_murrayVonNeumannEquiv_iff :
    MurrayVonNeumannEquiv (0 : CStarMatrix n n A) p ↔ p = 0 :=
  ⟨fun h => murrayVonNeumannEquiv_zero_iff.mp h.symm,
    fun h => h ▸ MurrayVonNeumannEquiv.zero⟩

/-- `CStarMatrix.MurrayVonNeumannEquiv` agrees with `Matrix.IsMurrayVonNeumannEquivalent` on the
underlying matrices. -/
theorem murrayVonNeumannEquiv_iff_isMurrayVonNeumannEquivalent :
    MurrayVonNeumannEquiv p q ↔
      Matrix.IsMurrayVonNeumannEquivalent (ofMatrix.symm p) (ofMatrix.symm q) := by
  simp [MurrayVonNeumannEquiv, Matrix.isMurrayVonNeumannEquivalent_iff,
    ← ofMatrix.symm.injective.eq_iff, ofMatrix.symm.exists_congr_left]

/-- A rectangular partial isometry `v` (`v * vᴴ * v = v`) implements Murray–von Neumann equivalence
between its initial projection `vᴴ * v` and final projection `v * vᴴ`. -/
theorem murrayVonNeumannEquiv_of_mul_conjTranspose_mul_self_eq {v : CStarMatrix n m A}
    (hv : v * v.conjTranspose * v = v) :
    MurrayVonNeumannEquiv (v.conjTranspose * v) (v * v.conjTranspose) := by
  rw [murrayVonNeumannEquiv_iff_isMurrayVonNeumannEquivalent]
  simpa only [ofMatrix_symm_mul, ofMatrix_symm_conjTranspose] using
    Matrix.isMurrayVonNeumannEquivalent_of_mul_conjTranspose_mul_self_eq
      (by simpa only [ofMatrix_symm_mul, ofMatrix_symm_conjTranspose] using
        congrArg ofMatrix.symm hv)

/-- Padding a projection by a lower-right zero block preserves its Murray–von Neumann class. -/
theorem murrayVonNeumannEquiv_fromBlocks_zero_right (hp : IsStarProjection p) :
    MurrayVonNeumannEquiv p (fromBlocks p 0 0 (0 : CStarMatrix k k A)) := by
  rw [murrayVonNeumannEquiv_iff_isMurrayVonNeumannEquivalent]
  simpa only [ofMatrix_symm_fromBlocks, ofMatrix_symm_zero] using
    (isStarProjection_ofMatrix_symm.mpr hp).isMurrayVonNeumannEquivalent_fromBlocks_zero

/-- Padding a projection by an upper-left zero block preserves its Murray–von Neumann class. -/
theorem murrayVonNeumannEquiv_fromBlocks_zero_left (hp : IsStarProjection p) :
    MurrayVonNeumannEquiv p (fromBlocks (0 : CStarMatrix k k A) 0 0 p) := by
  rw [murrayVonNeumannEquiv_iff_isMurrayVonNeumannEquivalent]
  simpa only [ofMatrix_symm_fromBlocks, ofMatrix_symm_zero] using
    (isStarProjection_ofMatrix_symm.mpr hp).isMurrayVonNeumannEquivalent_zero_fromBlocks

/-- Reindexing rows and columns by a bijection `e : m ≃ n` preserves the Murray–von Neumann class,
even when `A` is non-unital. -/
theorem murrayVonNeumannEquiv_reindexₐ {R : Type*} [Semiring R] [Module R A]
    (hp : IsStarProjection p) (e : m ≃ n) :
    MurrayVonNeumannEquiv p (reindexₐ R A e p) := by
  rw [murrayVonNeumannEquiv_iff_isMurrayVonNeumannEquivalent, reindexₐ_eq_reindexₗ,
    ofMatrix_symm_reindexₗ]
  exact (isStarProjection_ofMatrix_symm.mpr hp).isMurrayVonNeumannEquivalent_reindex e

/-- Block-diagonal direct sum is commutative up to Murray–von Neumann equivalence. -/
theorem murrayVonNeumannEquiv_fromBlocks_zero_comm
    (hp : IsStarProjection p) (hq : IsStarProjection q) :
    MurrayVonNeumannEquiv (fromBlocks p 0 0 q) (fromBlocks q 0 0 p) := by
  rw [murrayVonNeumannEquiv_iff_isMurrayVonNeumannEquivalent]
  simpa only [ofMatrix_symm_fromBlocks, ofMatrix_symm_zero] using
    Matrix.isMurrayVonNeumannEquivalent_fromBlocks_comm
      (isStarProjection_ofMatrix_symm.mpr hp) (isStarProjection_ofMatrix_symm.mpr hq)

/-- Block-diagonal direct sum is associative up to Murray–von Neumann equivalence. -/
theorem murrayVonNeumannEquiv_fromBlocks_zero_assoc
    (hp : IsStarProjection p) (hq : IsStarProjection q) (hr : IsStarProjection r) :
    MurrayVonNeumannEquiv (fromBlocks (fromBlocks p 0 0 q) 0 0 r)
      (fromBlocks p 0 0 (fromBlocks q 0 0 r)) := by
  rw [murrayVonNeumannEquiv_iff_isMurrayVonNeumannEquivalent]
  simpa only [ofMatrix_symm_fromBlocks, ofMatrix_symm_zero] using
    Matrix.isMurrayVonNeumannEquivalent_fromBlocks_assoc
      (isStarProjection_ofMatrix_symm.mpr hp) (isStarProjection_ofMatrix_symm.mpr hq)
      (isStarProjection_ofMatrix_symm.mpr hr)

/-- If `p` and `p'` are orthogonal star projections (`p * p' = 0`) in `CStarMatrix m m A`, their
internal sum `p + p'` is Murray–von Neumann equivalent to their block-diagonal direct sum
`fromBlocks p 0 0 p'`. -/
theorem add_murrayVonNeumannEquiv_fromBlocks_zero_of_mul_eq_zero {p' : CStarMatrix m m A}
    (hp : IsStarProjection p) (hp' : IsStarProjection p') (hpp' : p * p' = 0) :
    MurrayVonNeumannEquiv (p + p') (fromBlocks p 0 0 p') := by
  have hp_ct : p.conjTranspose = p := hp.isSelfAdjoint
  have hp'_ct : p'.conjTranspose = p' := hp'.isSelfAdjoint
  have hp'p : p' * p = 0 := by
    simpa only [conjTranspose_mul, hp_ct, hp'_ct, conjTranspose_zero] using
      congrArg conjTranspose hpp'
  have hv₁ : (fromRows p p').conjTranspose * fromRows p p' = p + p' := by
    rw [conjTranspose_fromRows, fromCols_mul_fromRows, hp_ct, hp'_ct, hp.isIdempotentElem.eq,
      hp'.isIdempotentElem.eq]
  have hv₂ : fromRows p p' * (fromRows p p').conjTranspose = fromBlocks p 0 0 p' := by
    rw [conjTranspose_fromRows, fromRows_mul_fromCols, hp_ct, hp'_ct, hp.isIdempotentElem.eq,
      hp'.isIdempotentElem.eq, hpp', hp'p]
  have hv : fromRows p p' * (fromRows p p').conjTranspose * fromRows p p' = fromRows p p' := by
    rw [hv₂, fromBlocks_mul_fromRows, hp.isIdempotentElem.eq, hp'.isIdempotentElem.eq,
      CStarMatrix.zero_mul, CStarMatrix.zero_mul, add_zero, zero_add]
  simpa only [hv₁, hv₂] using murrayVonNeumannEquiv_of_mul_conjTranspose_mul_self_eq hv

end Algebraic

/-- Unitary conjugacy implies Murray–von Neumann equivalence. -/
theorem murrayVonNeumannEquiv_unitary_conj [Semiring B] [StarRing B] [DecidableEq m]
    {p : CStarMatrix m m B} (hp : IsStarProjection p) (u : unitary (CStarMatrix m m B)) :
    MurrayVonNeumannEquiv p ((u : CStarMatrix m m B) * p * star (u : CStarMatrix m m B)) := by
  have hq : IsStarProjection ((u : CStarMatrix m m B) * p * star (u : CStarMatrix m m B)) :=
    ⟨by simp only [IsIdempotentElem, mul_assoc,
        ← mul_assoc (star (u : CStarMatrix m m B)), Unitary.coe_star_mul_self,
        one_mul, ← mul_assoc p, hp.isIdempotentElem.eq], hp.isSelfAdjoint.conjugate u⟩
  refine ⟨hp, hq, (u : CStarMatrix m m B) * p, ?_, ?_⟩
  · rw [← star_eq_conjTranspose, star_mul, hp.isSelfAdjoint.star_eq]
    simp only [mul_assoc, ← mul_assoc (star (u : CStarMatrix m m B)),
      Unitary.coe_star_mul_self, one_mul, hp.isIdempotentElem.eq]
  · rw [← star_eq_conjTranspose, star_mul, hp.isSelfAdjoint.star_eq]
    simp only [mul_assoc, ← mul_assoc p, hp.isIdempotentElem.eq]

section Stabilization

variable [DecidableEq m] [DecidableEq n] [Ring A] [StarRing A]
  {p : CStarMatrix m m A} {q : CStarMatrix n n A}

/-- Over a unital `⋆`-ring, a star projection `p` is Murray–von Neumann equivalent to `q` if and
only if `fromBlocks p 0 0 0` and `fromBlocks 0 0 0 q` are conjugate by a self-adjoint unitary in
`CStarMatrix (m ⊕ n) (m ⊕ n) A`. -/
theorem murrayVonNeumannEquiv_iff_exists_isSelfAdjoint_unitary_fromBlocks_zero_right_left
    (hp : IsStarProjection p) :
    MurrayVonNeumannEquiv p q ↔
      ∃ u : unitary (CStarMatrix (m ⊕ n) (m ⊕ n) A),
        IsSelfAdjoint (u : CStarMatrix (m ⊕ n) (m ⊕ n) A) ∧
          (u : CStarMatrix (m ⊕ n) (m ⊕ n) A) * fromBlocks p 0 0 0 *
            star (u : CStarMatrix (m ⊕ n) (m ⊕ n) A) = fromBlocks 0 0 0 q := by
  rw [murrayVonNeumannEquiv_iff_isMurrayVonNeumannEquivalent]
  refine ⟨fun h ↦ ?_, fun ⟨u, _, hconj⟩ ↦ ?_⟩
  · obtain ⟨w, hw_sa, hw_u, hw_conj⟩ :=
      h.exists_isSelfAdjoint_mem_unitary_mul_fromBlocks_mul_star
    refine ⟨⟨ofMatrix w, ?_⟩, ?_, ?_⟩
    · rw [Unitary.mem_iff] at hw_u ⊢
      exact ⟨ofMatrix.symm.injective (by simpa [Matrix.star_eq_conjTranspose] using hw_u.1),
        ofMatrix.symm.injective (by simpa [Matrix.star_eq_conjTranspose] using hw_u.2)⟩
    · rw [IsSelfAdjoint]
      exact ofMatrix.symm.injective <| by simpa [Matrix.star_eq_conjTranspose] using hw_sa.star_eq
    · exact ofMatrix.symm.injective <| by simpa [Matrix.star_eq_conjTranspose] using hw_conj
  · have hu₁ := congrArg ofMatrix.symm (Unitary.coe_star_mul_self u)
    have hu₂ := congrArg ofMatrix.symm (Unitary.coe_mul_star_self u)
    simp only [ofMatrix_symm_mul, ofMatrix_symm_star, ofMatrix_symm_one] at hu₁ hu₂
    have hc := congrArg ofMatrix.symm hconj
    refine Matrix.isMurrayVonNeumannEquivalent_of_mem_unitary_mul_fromBlocks_mul_star
      (isStarProjection_ofMatrix_symm.mpr hp) (w := ofMatrix.symm (u : CStarMatrix _ _ A)) ?_ ?_
    · rw [Unitary.mem_iff]
      exact ⟨by rwa [Matrix.star_eq_conjTranspose], by rwa [Matrix.star_eq_conjTranspose]⟩
    · simpa [Matrix.star_eq_conjTranspose] using hc

end Stabilization

section StarOrderedRing

/-- Over a star-ordered ring with proper star, a rectangular matrix `v` whose initial Gram matrix
`vᴴ * v` is a star projection implements `MurrayVonNeumannEquiv (vᴴ * v) (v * vᴴ)`. -/
theorem murrayVonNeumannEquiv_of_isStarProjection [NonUnitalRing A] [StarRing A] [PartialOrder A]
    [StarOrderedRing A] [IsProperStar A] {v : CStarMatrix n m A}
    (hv : IsStarProjection (v.conjTranspose * v)) :
    MurrayVonNeumannEquiv (v.conjTranspose * v) (v * v.conjTranspose) := by
  rw [murrayVonNeumannEquiv_iff_isMurrayVonNeumannEquivalent]
  simpa only [ofMatrix_symm_mul, ofMatrix_symm_conjTranspose] using
    Matrix.isMurrayVonNeumannEquivalent_of_isStarProjection
      (by simpa only [ofMatrix_symm_mul, ofMatrix_symm_conjTranspose] using
        isStarProjection_ofMatrix_symm.mpr hv)

end StarOrderedRing

section CStarAlgebra

private theorem murrayVonNeumannEquiv_of_unitization_unitary_conj [NonUnitalCStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A] {p q : CStarMatrix n n A} (hp : IsStarProjection p)
    (u : unitary (Unitization ℂ (CStarMatrix n n A)))
    (hconj : (u : Unitization ℂ (CStarMatrix n n A)) * (p : Unitization ℂ (CStarMatrix n n A)) *
      star (u : Unitization ℂ (CStarMatrix n n A)) = (q : Unitization ℂ (CStarMatrix n n A))) :
    MurrayVonNeumannEquiv p q := by
  let B := CStarMatrix n n A
  let v : B := ((u : Unitization ℂ B) * (p : Unitization ℂ B)).snd
  have hv_inr : (v : Unitization ℂ B) = (u : Unitization ℂ B) * (p : Unitization ℂ B) :=
    Unitization.ext (by simp) rfl
  have hv₁ : v.conjTranspose * v = p := Unitization.inr_injective (R := ℂ) <| by
    rw [← star_eq_conjTranspose, Unitization.inr_mul, Unitization.inr_star, hv_inr, star_mul,
      hp.inr.isSelfAdjoint.star_eq, mul_assoc, ← mul_assoc (star (u : Unitization ℂ B)),
      Unitary.coe_star_mul_self, one_mul, hp.inr.isIdempotentElem.eq]
  have hv₂ : v * v.conjTranspose = q := Unitization.inr_injective (R := ℂ) <| by
    rw [← star_eq_conjTranspose, Unitization.inr_mul, Unitization.inr_star, hv_inr, star_mul,
      hp.inr.isSelfAdjoint.star_eq, ← mul_assoc, mul_assoc (u : Unitization ℂ B),
      hp.inr.isIdempotentElem.eq, hconj]
  have heq := murrayVonNeumannEquiv_of_isStarProjection (hv₁.symm ▸ hp)
  rwa [hv₁, hv₂] at heq

/-- Two matrix star projections over a (possibly non-unital) C⋆-algebra at operator-norm distance
`< 1` are Murray–von Neumann equivalent. -/
theorem murrayVonNeumannEquiv_of_norm_sub_lt_one [NonUnitalCStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A] {p q : CStarMatrix n n A}
    (hp : IsStarProjection p) (hq : IsStarProjection q) (h : ‖p - q‖ < 1) :
    MurrayVonNeumannEquiv p q := by
  have h' : ‖(p : Unitization ℂ (CStarMatrix n n A)) -
      (q : Unitization ℂ (CStarMatrix n n A))‖ < 1 := by
    rwa [← Unitization.inr_sub, Unitization.norm_inr]
  exact murrayVonNeumannEquiv_of_unitization_unitary_conj hp
    (hp.inr.conjUnitaryOfNormSubLtOne hq.inr h')
    (hp.inr.conjUnitaryOfNormSubLtOne_mul_mul_star hq.inr h')

/-- Any norm-continuous path of star projections in `CStarMatrix n n A` over a (possibly non-unital)
C⋆-algebra has Murray–von Neumann equivalent endpoints. -/
theorem murrayVonNeumannEquiv_of_path [NonUnitalCStarAlgebra A]
    {p q : CStarMatrix n n A} (γ : Path p q) (hγ : ∀ t, IsStarProjection (γ t)) :
    MurrayVonNeumannEquiv p q := by
  let : PartialOrder A := CStarAlgebra.spectralOrder A
  let : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
  obtain ⟨u, -, hconj⟩ := IsStarProjection.exists_joined_one_unitary_conj_of_path
    (γ.map (Unitization.continuous_inr (𝕜 := ℂ))) fun t ↦ (hγ t).inr
  exact murrayVonNeumannEquiv_of_unitization_unitary_conj (γ.source ▸ hγ 0) u hconj

/-- **Explicit `2 × 2` rotation path for Murray–von Neumann equivalent projections.** Given matrices
`p : CStarMatrix m m A`, `q : CStarMatrix n n A`, and `v : CStarMatrix n m A` over a (possibly
non-unital) C⋆-algebra `A`, this is the continuous path from `fromBlocks p 0 0 0` to
`fromBlocks 0 0 0 q` given by rotating by angle `πt/2`; every point is a star projection when `v`
is a partial isometry implementing `MurrayVonNeumannEquiv p q`. -/
noncomputable def stabilizedRotationPath [NonUnitalCStarAlgebra A]
    (p : CStarMatrix m m A) (q : CStarMatrix n n A) (v : CStarMatrix n m A) :
    Path (fromBlocks p 0 0 (0 : CStarMatrix n n A))
      (fromBlocks (0 : CStarMatrix m m A) 0 0 q) where
  toFun t :=
    fromBlocks (Real.cos (π / 2 * t) ^ 2 • p)
      ((Real.cos (π / 2 * t) * Real.sin (π / 2 * t)) • v.conjTranspose)
      ((Real.cos (π / 2 * t) * Real.sin (π / 2 * t)) • v)
      (Real.sin (π / 2 * t) ^ 2 • q)
  continuous_toFun := by
    let : PartialOrder A := CStarAlgebra.spectralOrder A
    let : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
    have hfun : (fun t : I ↦
        fromBlocks (Real.cos (π / 2 * t) ^ 2 • p)
          ((Real.cos (π / 2 * t) * Real.sin (π / 2 * t)) • v.conjTranspose)
          ((Real.cos (π / 2 * t) * Real.sin (π / 2 * t)) • v)
          (Real.sin (π / 2 * t) ^ 2 • q)) =
      fun t : I ↦
        Real.cos (π / 2 * t) ^ 2 • fromBlocks p 0 0 (0 : CStarMatrix n n A) +
          (Real.cos (π / 2 * t) * Real.sin (π / 2 * t)) •
            fromBlocks (0 : CStarMatrix m m A) v.conjTranspose v (0 : CStarMatrix n n A) +
          Real.sin (π / 2 * t) ^ 2 • fromBlocks (0 : CStarMatrix m m A) 0 0 q := by
      ext t (i | i) (j | j) <;> simp
    rw [hfun]; fun_prop
  source' := by simp
  target' := by simp

@[simp] theorem stabilizedRotationPath_apply [NonUnitalCStarAlgebra A]
    (p : CStarMatrix m m A) (q : CStarMatrix n n A) (v : CStarMatrix n m A) (t : I) :
    stabilizedRotationPath p q v t =
      fromBlocks (Real.cos (π / 2 * t) ^ 2 • p)
        ((Real.cos (π / 2 * t) * Real.sin (π / 2 * t)) • v.conjTranspose)
        ((Real.cos (π / 2 * t) * Real.sin (π / 2 * t)) • v)
        (Real.sin (π / 2 * t) ^ 2 • q) := (rfl)

/-- Every point along `stabilizedRotationPath p q v` is a star projection when `v` is a partial
isometry witnessing `MurrayVonNeumannEquiv p q`. -/
theorem isStarProjection_stabilizedRotationPath [NonUnitalCStarAlgebra A]
    {p : CStarMatrix m m A} {q : CStarMatrix n n A} {v : CStarMatrix n m A}
    (hv : v * v.conjTranspose * v = v) (hv₁ : v.conjTranspose * v = p)
    (hv₂ : v * v.conjTranspose = q) (t : I) :
    IsStarProjection (stabilizedRotationPath p q v t) := by
  open scoped ComplexStarModule in
  have heq := murrayVonNeumannEquiv_of_mul_conjTranspose_mul_self_eq hv
  rw [hv₁, hv₂] at heq
  have hp : IsStarProjection p := heq.isStarProjection_left
  have hq : IsStarProjection q := heq.isStarProjection_right
  have hvp : v * p = v := by rw [← hv₁, ← mul_assoc_rectangular, hv]
  have hpv : p * v.conjTranspose = v.conjTranspose := by
    simpa [← star_eq_conjTranspose, hp.isSelfAdjoint.star_eq] using congrArg conjTranspose hvp
  have hqv : q * v = v := by rw [← hv₂, hv]
  have hvq : v.conjTranspose * q = v.conjTranspose := by
    simpa [← star_eq_conjTranspose, hq.isSelfAdjoint.star_eq] using congrArg conjTranspose hqv
  set c : ℝ := Real.cos (π / 2 * t)
  set s : ℝ := Real.sin (π / 2 * t)
  have hcs : c ^ 2 + s ^ 2 = 1 := Real.cos_sq_add_sin_sq (π / 2 * t)
  rw [stabilizedRotationPath_apply]
  refine ⟨?_, ?_⟩
  · rw [IsIdempotentElem, fromBlocks_multiply]
    simp only [CStarMatrix.smul_mul, CStarMatrix.mul_smul, smul_smul, hp.isIdempotentElem.eq,
      hq.isIdempotentElem.eq, hv₁, hv₂, hvp, hpv, hqv, hvq, ← add_smul, fromBlocks_inj]
    refine ⟨?_, ?_, ?_, ?_⟩
    · congr 1; linear_combination c ^ 2 * hcs
    · congr 1; linear_combination c * s * hcs
    · congr 1; linear_combination c * s * hcs
    · congr 1; linear_combination s ^ 2 * hcs
  · rw [IsSelfAdjoint, fromBlocks_star]; simp [hp.isSelfAdjoint.star_eq, hq.isSelfAdjoint.star_eq]

/-- Over a (possibly non-unital) C⋆-algebra, two matrix elements `p : CStarMatrix m m A` and
`q : CStarMatrix n n A` are Murray–von Neumann equivalent if and only if `fromBlocks p 0 0 0` and
`fromBlocks 0 0 0 q` are joined by a continuous path of star projections. -/
theorem murrayVonNeumannEquiv_iff_exists_path_fromBlocks_zero_right_left [NonUnitalCStarAlgebra A]
    {p : CStarMatrix m m A} {q : CStarMatrix n n A} :
    MurrayVonNeumannEquiv p q ↔
      ∃ γ : Path (fromBlocks p 0 0 (0 : CStarMatrix n n A))
        (fromBlocks (0 : CStarMatrix m m A) 0 0 q), ∀ t, IsStarProjection (γ t) := by
  refine ⟨fun h ↦ ?_, fun ⟨γ, hγ⟩ ↦ ?_⟩
  · obtain ⟨v, hv₁, hv₂, hvp⟩ := h.exists_matrix_mul_eq_self
    have hv : v * v.conjTranspose * v = v := by rw [mul_assoc_rectangular, hv₁, hvp]
    exact ⟨stabilizedRotationPath p q v, isStarProjection_stabilizedRotationPath hv hv₁ hv₂⟩
  · have hp : IsStarProjection p := (isStarProjection_fromBlocks_zero.mp (γ.source ▸ hγ 0)).1
    have hq : IsStarProjection q := (isStarProjection_fromBlocks_zero.mp (γ.target ▸ hγ 1)).2
    exact (murrayVonNeumannEquiv_fromBlocks_zero_right hp).trans
      ((murrayVonNeumannEquiv_of_path γ hγ).trans
        (murrayVonNeumannEquiv_fromBlocks_zero_left hq).symm)

/-- Over a unital C⋆-algebra, a star projection `p : CStarMatrix m m A` is Murray–von Neumann
equivalent to `q : CStarMatrix n n A` if and only if `fromBlocks p 0 0 0` and `fromBlocks 0 0 0 q`
are conjugate by a unitary in the identity path component of
`unitary (CStarMatrix (m ⊕ n) (m ⊕ n) A)`. -/
theorem murrayVonNeumannEquiv_iff_exists_joined_one_unitary_fromBlocks_zero_right_left
    [DecidableEq m] [DecidableEq n] [CStarAlgebra A]
    {p : CStarMatrix m m A} {q : CStarMatrix n n A} (hp : IsStarProjection p) :
    MurrayVonNeumannEquiv p q ↔
      ∃ u : unitary (CStarMatrix (m ⊕ n) (m ⊕ n) A), Joined 1 u ∧
        (u : CStarMatrix (m ⊕ n) (m ⊕ n) A) * fromBlocks p 0 0 0 *
          star (u : CStarMatrix (m ⊕ n) (m ⊕ n) A) = fromBlocks 0 0 0 q := by
  let : PartialOrder A := CStarAlgebra.spectralOrder A
  let : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
  have hp0 : IsStarProjection (fromBlocks p 0 0 (0 : CStarMatrix n n A)) :=
    isStarProjection_fromBlocks_zero.mpr ⟨hp, .zero _⟩
  rw [murrayVonNeumannEquiv_iff_exists_path_fromBlocks_zero_right_left,
    hp0.exists_path_iff_exists_joined_one_unitary_conj]

/-- Over a (possibly non-unital) C⋆-algebra, two matrix elements `p, q : CStarMatrix n n A` are
Murray–von Neumann equivalent if and only if `fromBlocks p 0 0 0` and `fromBlocks q 0 0 0` are
joined by a continuous path of star projections. -/
theorem murrayVonNeumannEquiv_iff_exists_path_fromBlocks_zero_right [NonUnitalCStarAlgebra A]
    {p q : CStarMatrix n n A} :
    MurrayVonNeumannEquiv p q ↔
      ∃ γ : Path (fromBlocks p 0 0 (0 : CStarMatrix n n A))
        (fromBlocks q 0 0 (0 : CStarMatrix n n A)), ∀ t, IsStarProjection (γ t) := by
  refine ⟨fun h ↦ ?_, fun ⟨γ, hγ⟩ ↦ ?_⟩
  · obtain ⟨γ₁, hγ₁⟩ := murrayVonNeumannEquiv_iff_exists_path_fromBlocks_zero_right_left.mp h
    obtain ⟨γ₂, hγ₂⟩ := murrayVonNeumannEquiv_iff_exists_path_fromBlocks_zero_right_left.mp
      (.refl h.isStarProjection_right)
    refine ⟨γ₁.trans γ₂.symm, fun t ↦ ?_⟩
    rw [Path.trans_apply]; split_ifs <;> simp [hγ₁, hγ₂]
  · have hp : IsStarProjection p := (isStarProjection_fromBlocks_zero.mp (γ.source ▸ hγ 0)).1
    have hq : IsStarProjection q := (isStarProjection_fromBlocks_zero.mp (γ.target ▸ hγ 1)).1
    exact (murrayVonNeumannEquiv_fromBlocks_zero_right hp).trans
      ((murrayVonNeumannEquiv_of_path γ hγ).trans
        (murrayVonNeumannEquiv_fromBlocks_zero_right hq).symm)

/-- Over a unital C⋆-algebra, a star projection `p : CStarMatrix n n A` is Murray–von Neumann
equivalent to `q : CStarMatrix n n A` if and only if `fromBlocks p 0 0 0` and `fromBlocks q 0 0 0`
are conjugate by a unitary in the identity path component of
`unitary (CStarMatrix (n ⊕ n) (n ⊕ n) A)`. -/
theorem murrayVonNeumannEquiv_iff_exists_joined_one_unitary_fromBlocks_zero_right
    [DecidableEq n] [CStarAlgebra A]
    {p q : CStarMatrix n n A} (hp : IsStarProjection p) :
    MurrayVonNeumannEquiv p q ↔
      ∃ u : unitary (CStarMatrix (n ⊕ n) (n ⊕ n) A), Joined 1 u ∧
        (u : CStarMatrix (n ⊕ n) (n ⊕ n) A) * fromBlocks p 0 0 0 *
          star (u : CStarMatrix (n ⊕ n) (n ⊕ n) A) = fromBlocks q 0 0 0 := by
  let : PartialOrder A := CStarAlgebra.spectralOrder A
  let : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
  have hp0 : IsStarProjection (fromBlocks p 0 0 (0 : CStarMatrix n n A)) :=
    isStarProjection_fromBlocks_zero.mpr ⟨hp, .zero _⟩
  rw [murrayVonNeumannEquiv_iff_exists_path_fromBlocks_zero_right,
    hp0.exists_path_iff_exists_joined_one_unitary_conj]

end CStarAlgebra

end CStarMatrix
