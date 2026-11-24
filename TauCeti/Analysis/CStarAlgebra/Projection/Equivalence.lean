/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.CStarMatrix.Block
public import TauCeti.Analysis.CStarAlgebra.Projection.Perturbation
public import TauCeti.LinearAlgebra.Matrix.MurrayVonNeumann
import Mathlib.Algebra.Star.UnitaryStarAlgAut
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Tactic.LinearCombination
import TauCeti.Data.Matrix.Block

/-!
# Rectangular Murray–von Neumann equivalence and stabilized homotopy of matrix projections

Matrix projections `p : CStarMatrix m m A` and `q : CStarMatrix n n A` are Murray–von Neumann
equivalent (`CStarMatrix.MurrayVonNeumannEquiv p q`) when they are the initial and final
projections of a rectangular matrix `v : CStarMatrix n m A` (`v.conjTranspose * v = p` and
`v * v.conjTranspose = q`). The index types may differ, so this relation identifies a projection
with its zero padding and finite reindexings without casts between unequal matrix sizes.

We prove:

* **Equivalence-relation and monoid laws**: reflexivity on projections, symmetry, transitivity,
  compatibility with block sums, preservation by nonunital star homomorphisms, comparison with
  `Matrix.IsMurrayVonNeumannEquivalent`, invariance under zero-block corners, finite reindexings,
  block commutativity and associativity, diagonal-entry corners, and unital stabilized conjugacy.
* **Perturbation and homotopy → equivalence**: over any possibly non-unital C⋆-algebra `A`, nearby
  matrix projections (`‖p - q‖ < 1`) and endpoints of any norm-continuous path of star projections
  (`Path.murrayVonNeumannEquiv_of_isStarProjection`) are Murray–von Neumann equivalent.
* **Equivalence → stabilized homotopy**: for `r = stabilizedProjection p q v`, the explicit
  rotation path `stabilizedPath p q v` from `fromBlocks p 0 0 0` to `fromBlocks 0 0 0 q` equals
  unitary conjugation by `expUnitary ((t * π) • r)` in the unitization while remaining inside
  `CStarMatrix (m ⊕ n) (m ⊕ n) A` even when `A` is non-unital, yielding
  `CStarMatrix.murrayVonNeumannEquiv_iff_exists_stabilized_path`.

## References

* B. Blackadar, *K-Theory for Operator Algebras*, 2nd ed., MSRI Publications 5, Cambridge
  University Press (1998), §4.6 (Definition 4.6.1 and Propositions 4.6.2–4.6.6) and §5.1.
* M. Rørdam, F. Larsen, and N. Laustsen, *An Introduction to K-Theory for C⋆-Algebras*, London
  Mathematical Society Student Texts 49, Cambridge University Press (2000), Chapter 2.
-/

public section

noncomputable section

open Matrix TauCeti
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

/-- `ofMatrix.symm` preserves and reflects `IsStarProjection`. -/
@[simp]
theorem isStarProjection_ofMatrix_symm_iff :
    IsStarProjection (ofMatrix.symm p) ↔ IsStarProjection p := by
  simp only [isStarProjection_iff, IsIdempotentElem, isSelfAdjoint_iff,
    ← ofMatrix.symm.injective.eq_iff, ofMatrix_symm_mul, ofMatrix_symm_star,
    Matrix.star_eq_conjTranspose]

/-- `MurrayVonNeumannEquiv` on `CStarMatrix` agrees with `Matrix.IsMurrayVonNeumannEquivalent` on
the underlying matrices. -/
theorem murrayVonNeumannEquiv_iff_isMurrayVonNeumannEquivalent :
    MurrayVonNeumannEquiv p q ↔
      Matrix.IsMurrayVonNeumannEquivalent (ofMatrix.symm p) (ofMatrix.symm q) := by
  rw [MurrayVonNeumannEquiv, Matrix.isMurrayVonNeumannEquivalent_iff,
    isStarProjection_ofMatrix_symm_iff, isStarProjection_ofMatrix_symm_iff]
  refine and_congr_right fun _ => and_congr_right fun _ => ofMatrix.symm.exists_congr fun v => ?_
  simp only [← ofMatrix.symm.injective.eq_iff, ofMatrix_symm_mul, ofMatrix_symm_conjTranspose]

/-- Placing a star projection `p` in the top-left corner (`CStarMatrix.fromBlocks p 0 0 0`)
preserves its Murray–von Neumann equivalence class. -/
theorem _root_.IsStarProjection.murrayVonNeumannEquiv_inlCorner (hp : IsStarProjection p) :
    MurrayVonNeumannEquiv p (CStarMatrix.fromBlocks p (0 : CStarMatrix m n A) 0 0) := by
  have heq : CStarMatrix.fromBlocks p (0 : CStarMatrix m n A) 0 0 =
      ofMatrix (Matrix.fromBlocks (ofMatrix.symm p) 0 0 (0 : Matrix n n A)) :=
    ofMatrix.symm.injective (by simp)
  rw [heq]
  exact MurrayVonNeumannEquiv.pad_zero hp

/-- Reindexing a star projection along any bijection `e : m ≃ n` yields a Murray–von Neumann
equivalent projection. -/
theorem _root_.IsStarProjection.murrayVonNeumannEquiv_reindex
    (hp : IsStarProjection p) (e : m ≃ n) :
    MurrayVonNeumannEquiv p (reindexₐ ℕ A e p) := by
  refine ⟨hp, hp.map (reindexₐ ℕ A e).toNonUnitalStarAlgHom,
    reindexₗ ℕ A e (Equiv.refl m) p, ?_, ?_⟩
  · rw [conjTranspose_reindexₗ, reindexₗ_mul, ← star_eq_conjTranspose, hp.isSelfAdjoint.star_eq,
      hp.isIdempotentElem.eq, reindexₗ_refl_refl]
  · rw [conjTranspose_reindexₗ, reindexₗ_mul, ← star_eq_conjTranspose, hp.isSelfAdjoint.star_eq,
      hp.isIdempotentElem.eq, reindexₗ_eq_reindexₐ]

/-- `MurrayVonNeumannEquiv` is invariant under arbitrary finite reindexings on both sides. -/
@[simp]
theorem MurrayVonNeumannEquiv.reindex_iff (e₁ : m ≃ k) (e₂ : n ≃ l) :
    MurrayVonNeumannEquiv (reindexₐ ℕ A e₁ p) (reindexₐ ℕ A e₂ q) ↔
      MurrayVonNeumannEquiv p q := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · have hp : IsStarProjection p := by
      simpa using h.isStarProjection_left.map (reindexₐ ℕ A e₁.symm).toNonUnitalStarAlgHom
    have hq : IsStarProjection q := by
      simpa using h.isStarProjection_right.map (reindexₐ ℕ A e₂.symm).toNonUnitalStarAlgHom
    exact (hp.murrayVonNeumannEquiv_reindex e₁).trans
      (h.trans (hq.murrayVonNeumannEquiv_reindex e₂).symm)
  · exact (h.isStarProjection_left.murrayVonNeumannEquiv_reindex e₁).symm.trans
      (h.trans (h.isStarProjection_right.murrayVonNeumannEquiv_reindex e₂))

/-- Placing a star projection `q` in the bottom-right corner (`CStarMatrix.fromBlocks 0 0 0 q`)
preserves its Murray–von Neumann equivalence class. -/
theorem _root_.IsStarProjection.murrayVonNeumannEquiv_inrCorner (hq : IsStarProjection q) :
    MurrayVonNeumannEquiv q (CStarMatrix.fromBlocks (0 : CStarMatrix m m A) 0 0 q) := by
  have h1 := hq.murrayVonNeumannEquiv_inlCorner (n := m)
  have h2 := (isStarProjection_fromBlocks_zero₁₂_zero₂₁.mpr ⟨hq, .zero (CStarMatrix m m A)⟩)
    |>.murrayVonNeumannEquiv_reindex (Equiv.sumComm n m)
  rw [reindexₐ_sumComm_fromBlocks] at h2
  exact h1.trans h2

/-- Block-diagonal direct sum of star projections is commutative up to `MurrayVonNeumannEquiv`. -/
theorem _root_.IsStarProjection.murrayVonNeumannEquiv_fromBlocks_comm
    (hp : IsStarProjection p) (hq : IsStarProjection q) :
    MurrayVonNeumannEquiv (CStarMatrix.fromBlocks p 0 0 q) (CStarMatrix.fromBlocks q 0 0 p) := by
  have h := (isStarProjection_fromBlocks_zero₁₂_zero₂₁.mpr ⟨hp, hq⟩).murrayVonNeumannEquiv_reindex
    (Equiv.sumComm m n)
  rwa [reindexₐ_sumComm_fromBlocks] at h

/-- Block-diagonal direct sum of star projections is associative up to `MurrayVonNeumannEquiv`. -/
theorem _root_.IsStarProjection.murrayVonNeumannEquiv_fromBlocks_assoc
    (hp : IsStarProjection p) (hq : IsStarProjection q) (hr : IsStarProjection r) :
    MurrayVonNeumannEquiv
      (CStarMatrix.fromBlocks (CStarMatrix.fromBlocks p 0 0 q) 0 0 r)
      (CStarMatrix.fromBlocks p 0 0 (CStarMatrix.fromBlocks q 0 0 r)) := by
  have hpq : IsStarProjection (CStarMatrix.fromBlocks p 0 0 q) :=
    isStarProjection_fromBlocks_zero₁₂_zero₂₁.mpr ⟨hp, hq⟩
  have h := (isStarProjection_fromBlocks_zero₁₂_zero₂₁.mpr ⟨hpq, hr⟩).murrayVonNeumannEquiv_reindex
    (Equiv.sumAssoc m n k)
  rwa [reindexₐ_sumAssoc_fromBlocks] at h

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
  refine ⟨⟨ofMatrix w, ?_, ?_⟩, ?_, ?_⟩ <;> apply ofMatrix.symm.injective
  · simpa only [ofMatrix_symm_mul, ofMatrix_symm_star, ofMatrix_symm_one, Equiv.symm_apply_apply,
      ← Matrix.star_eq_conjTranspose] using hw_u.1
  · simpa only [ofMatrix_symm_mul, ofMatrix_symm_star, ofMatrix_symm_one, Equiv.symm_apply_apply,
      ← Matrix.star_eq_conjTranspose] using hw_u.2
  · simpa only [ofMatrix_symm_star, Equiv.symm_apply_apply, ← Matrix.star_eq_conjTranspose] using
      hw_sa.star_eq
  · simpa only [ofMatrix_symm_mul, ofMatrix_symm_star, ofMatrix_symm_fromBlocks,
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
  refine ⟨fun h => ?_, fun ⟨u, hu⟩ => ?_⟩
  · obtain ⟨u, -, hu⟩ := h.exists_isSelfAdjoint_unitary_conj_fromBlocks
    exact ⟨u, hu⟩
  · have h := (hp.murrayVonNeumannEquiv_inlCorner (n := n)).trans
      (murrayVonNeumannEquiv_unitary_conj
        (isStarProjection_fromBlocks_zero₁₂_zero₂₁.mpr ⟨hp, .zero _⟩) u)
    rw [hu] at h
    have hq := (isStarProjection_fromBlocks_zero₁₂_zero₂₁.mp h.isStarProjection_right).2
    exact h.trans (hq.murrayVonNeumannEquiv_inrCorner (m := m)).symm

end CStarMatrix

section PerturbationAndPath

variable {m n A : Type*} [Fintype m] [Fintype n] [NonUnitalCStarAlgebra A]

/-- Smart constructor over a C⋆-algebra: if `IsStarProjection p` and `v.conjTranspose * v = p`,
`v * v.conjTranspose = q`, then `q` is automatically a star projection and
`CStarMatrix.MurrayVonNeumannEquiv p q`. -/
theorem CStarMatrix.MurrayVonNeumannEquiv.of_conjTranspose_mul_self {p : CStarMatrix m m A}
    {q : CStarMatrix n n A} (hp : IsStarProjection p) (v : CStarMatrix n m A)
    (hv₁ : v.conjTranspose * v = p) (hv₂ : v * v.conjTranspose = q) :
    CStarMatrix.MurrayVonNeumannEquiv p q := by
  refine ⟨hp, ?_, v, hv₁, hv₂⟩
  rw [← hv₂]
  exact CStarMatrix.isStarProjection_mul_conjTranspose_self_of_isIdempotentElem
    (hv₁.symm ▸ hp.isIdempotentElem)

/-- Unitary conjugacy in `Unitization ℂ (CStarMatrix n n A)` implies Murray–von Neumann equivalence
in `CStarMatrix n n A`. -/
theorem CStarMatrix.MurrayVonNeumannEquiv.of_unitization_unitary_conj {p q : CStarMatrix n n A}
    (hp : IsStarProjection p) (u : unitary (Unitization ℂ (CStarMatrix n n A)))
    (hconj : (u : Unitization ℂ (CStarMatrix n n A)) * (p : Unitization ℂ (CStarMatrix n n A)) *
      star (u : Unitization ℂ (CStarMatrix n n A)) = (q : Unitization ℂ (CStarMatrix n n A))) :
    CStarMatrix.MurrayVonNeumannEquiv p q := by
  rw [CStarMatrix.murrayVonNeumannEquiv_iff_exists_partialIsometry]
  exact hp.exists_isPartialIsometry_of_unitization_unitary_conj u hconj

/-- Nearby matrix projections (`‖p - q‖ < 1`) in `CStarMatrix n n A` are Murray–von Neumann
equivalent, even when `A` is non-unital. -/
theorem IsStarProjection.murrayVonNeumannEquiv_of_norm_sub_lt_one
    [PartialOrder A] [StarOrderedRing A]
    {p q : CStarMatrix n n A} (hp : IsStarProjection p) (hq : IsStarProjection q)
    (h : ‖p - q‖ < 1) : CStarMatrix.MurrayVonNeumannEquiv p q := by
  rw [CStarMatrix.murrayVonNeumannEquiv_iff_exists_partialIsometry]
  exact hp.exists_isPartialIsometry_of_norm_sub_lt_one hq h

/-- Endpoints of any norm-continuous path of star projections in `CStarMatrix n n A` are
Murray–von Neumann equivalent. -/
theorem Path.murrayVonNeumannEquiv_of_isStarProjection {p q : CStarMatrix n n A} (γ : Path p q)
    (hγ : ∀ t : I, IsStarProjection (γ t)) : CStarMatrix.MurrayVonNeumannEquiv p q := by
  let _ : PartialOrder A := CStarAlgebra.spectralOrder A
  let _ : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
  rw [CStarMatrix.murrayVonNeumannEquiv_iff_exists_partialIsometry]
  exact γ.exists_isPartialIsometry_of_isStarProjection hγ

end PerturbationAndPath

namespace CStarMatrix

section StabilizedHomotopy

variable {m n A : Type*}

/-- The block matrix `r = (1 / 2 : ℝ) • fromBlocks p (-v.conjTranspose) (-v) q` in
`CStarMatrix (m ⊕ n) (m ⊕ n) A`, which is a star projection when `v` implements a Murray–von
Neumann equivalence over a C⋆-algebra, without requiring a unit in `A` or `DecidableEq` on the
index types. -/
def stabilizedProjection [Neg A] [SMul ℝ A] [Star A]
    (p : CStarMatrix m m A) (q : CStarMatrix n n A)
    (v : CStarMatrix n m A) : CStarMatrix (m ⊕ n) (m ⊕ n) A :=
  (1 / 2 : ℝ) • fromBlocks p (-v.conjTranspose) (-v) q

/-- Unfold `CStarMatrix.stabilizedProjection`. -/
theorem stabilizedProjection_def [Neg A] [SMul ℝ A] [Star A]
    (p : CStarMatrix m m A) (q : CStarMatrix n n A) (v : CStarMatrix n m A) :
    stabilizedProjection p q v = (1 / 2 : ℝ) • fromBlocks p (-v.conjTranspose) (-v) q := (rfl)

section RotationPath

variable [NonUnitalCStarAlgebra A]

/-- Explicit rotation family `stabilizedRotation p q v t` in `CStarMatrix (m ⊕ n) (m ⊕ n) A` joining
`fromBlocks p 0 0 0` (at `t = 0`) to `fromBlocks 0 0 0 q` (at `t = 1`). When `p` and `q` are star
projections with `v.conjTranspose * v = p` and `v * v.conjTranspose = q`, this equals the unitary
conjugate `expUnitary ((t * π) • r) * fromBlocks p 0 0 0 * star (expUnitary ((t * π) • r))` in the
unitization (`r = stabilizedProjection p q v`) while remaining inside
`CStarMatrix (m ⊕ n) (m ⊕ n) A` even for non-unital `A`. -/
def stabilizedRotation (p : CStarMatrix m m A) (q : CStarMatrix n n A)
    (v : CStarMatrix n m A) (t : ℝ) : CStarMatrix (m ⊕ n) (m ⊕ n) A :=
  fromBlocks ((Real.cos (π * t / 2) ^ 2 : ℝ) • p)
    (((Complex.I / 2) * Real.sin (π * t)) • v.conjTranspose)
    ((-(Complex.I / 2) * Real.sin (π * t)) • v)
    ((Real.sin (π * t / 2) ^ 2 : ℝ) • q)

/-- Unfold `CStarMatrix.stabilizedRotation`. -/
theorem stabilizedRotation_def (p : CStarMatrix m m A) (q : CStarMatrix n n A)
    (v : CStarMatrix n m A) (t : ℝ) :
    stabilizedRotation p q v t =
      fromBlocks ((Real.cos (π * t / 2) ^ 2 : ℝ) • p)
        (((Complex.I / 2) * Real.sin (π * t)) • v.conjTranspose)
        ((-(Complex.I / 2) * Real.sin (π * t)) • v)
        ((Real.sin (π * t / 2) ^ 2 : ℝ) • q) := (rfl)

/-- At `t = 0`, `stabilizedRotation p q v 0` is the top-left corner `fromBlocks p 0 0 0`. -/
@[simp]
theorem stabilizedRotation_zero (p : CStarMatrix m m A) (q : CStarMatrix n n A)
    (v : CStarMatrix n m A) :
    stabilizedRotation p q v 0 = fromBlocks p 0 0 0 := by simp [stabilizedRotation_def]

/-- At `t = 1`, `stabilizedRotation p q v 1` is the bottom-right corner `fromBlocks 0 0 0 q`. -/
@[simp]
theorem stabilizedRotation_one (p : CStarMatrix m m A) (q : CStarMatrix n n A)
    (v : CStarMatrix n m A) :
    stabilizedRotation p q v 1 = fromBlocks 0 0 0 q := by simp [stabilizedRotation_def]

/-- At the midpoint `t = 1 / 2`, `stabilizedRotation p q v (1 / 2)` equals the block matrix
`fromBlocks ((1 / 2 : ℝ) • p) ((I / 2) • v.conjTranspose) (-(I / 2) • v) ((1 / 2 : ℝ) • q)`
(which is a star projection under the hypotheses of `isStarProjection_stabilizedRotation`). -/
theorem stabilizedRotation_half (p : CStarMatrix m m A) (q : CStarMatrix n n A)
    (v : CStarMatrix n m A) :
    stabilizedRotation p q v (1 / 2) =
      fromBlocks ((1 / 2 : ℝ) • p) ((Complex.I / 2) • v.conjTranspose)
        (-(Complex.I / 2) • v) ((1 / 2 : ℝ) • q) := by
  have hangle : π * (1 / 2 : ℝ) / 2 = π / 4 := by ring
  have hangle2 : π * (1 / 2 : ℝ) = π / 2 := by ring
  have hcos : Real.cos (π / 4) ^ 2 = (1 / 2 : ℝ) := by
    rw [Real.cos_pi_div_four, div_pow, Real.sq_sqrt zero_le_two]; norm_num
  have hsin : Real.sin (π / 4) ^ 2 = (1 / 2 : ℝ) := by
    rw [Real.sin_pi_div_four, div_pow, Real.sq_sqrt zero_le_two]; norm_num
  rw [stabilizedRotation_def, hangle, hangle2, hcos, hsin, Real.sin_pi_div_two]
  simp

/-- Continuity of `t ↦ stabilizedRotation p q v t` in operator norm. -/
theorem continuous_stabilizedRotation (p : CStarMatrix m m A) (q : CStarMatrix n n A)
    (v : CStarMatrix n m A) : Continuous (stabilizedRotation p q v) := by
  have hdecomp : stabilizedRotation p q v = fun t : ℝ ↦
      (Real.cos (π * t / 2) ^ 2 : ℝ) • fromBlocks p (0 : CStarMatrix m n A) 0 0 +
      (((Complex.I / 2) * Real.sin (π * t)) •
        fromBlocks (0 : CStarMatrix m m A) v.conjTranspose 0 0 +
      (((-(Complex.I / 2) * Real.sin (π * t)) •
        fromBlocks (0 : CStarMatrix m m A) (0 : CStarMatrix m n A) v 0) +
      (Real.sin (π * t / 2) ^ 2 : ℝ) • fromBlocks (0 : CStarMatrix m m A) 0 0 q)) :=
    funext fun t ↦ by simp [stabilizedRotation_def]
  rw [hdecomp]
  fun_prop

/-- Bundled norm-continuous `Path` in `CStarMatrix (m ⊕ n) (m ⊕ n) A` from `fromBlocks p 0 0 0` to
`fromBlocks 0 0 0 q` defined by `stabilizedRotation p q v`. When `p` and `q` are star projections
satisfying `v.conjTranspose * v = p` and `v * v.conjTranspose = q`, every point on this path is a
star projection (`isStarProjection_stabilizedPath`). -/
def stabilizedPath (p : CStarMatrix m m A) (q : CStarMatrix n n A)
    (v : CStarMatrix n m A) :
    Path (fromBlocks p (0 : CStarMatrix m n A) 0 0)
      (fromBlocks (0 : CStarMatrix m m A) 0 0 q) where
  toFun t := stabilizedRotation p q v t
  continuous_toFun := (continuous_stabilizedRotation p q v).comp continuous_subtypeVal
  source' := stabilizedRotation_zero p q v
  target' := stabilizedRotation_one p q v

/-- Evaluation of `stabilizedPath` at `t : I` gives `stabilizedRotation` at `(t : ℝ)`. -/
@[simp]
theorem stabilizedPath_apply (p : CStarMatrix m m A) (q : CStarMatrix n n A)
    (v : CStarMatrix n m A) (t : I) :
    stabilizedPath p q v t = stabilizedRotation p q v t := (rfl)

private theorem exp_I_mul_pi_identities {ζ : ℂ} (t : ℝ)
    (hζ_def : ζ = Complex.exp (Complex.I * (t * π))) :
    1 + (ζ - 1) * (1 / 2 : ℂ) + (star ζ - 1) * (1 / 2 : ℂ) +
        (ζ - 1) * (star ζ - 1) * (1 / 4 : ℂ) = ((Real.cos (π * t / 2) ^ 2 : ℝ) : ℂ) ∧
      -((star ζ - 1) * (1 / 2 : ℂ)) - (ζ - 1) * (star ζ - 1) * (1 / 4 : ℂ) =
        (Complex.I / 2) * (Real.sin (π * t) : ℂ) ∧
      -((ζ - 1) * (1 / 2 : ℂ)) - (ζ - 1) * (star ζ - 1) * (1 / 4 : ℂ) =
        -(Complex.I / 2) * (Real.sin (π * t) : ℂ) ∧
      (ζ - 1) * (star ζ - 1) * (1 / 4 : ℂ) =
        ((Real.sin (π * t / 2) ^ 2 : ℝ) : ℂ) := by
  have hζ : ζ = (Real.cos (π * t) : ℂ) + (Real.sin (π * t) : ℂ) * Complex.I := by
    have harg : Complex.I * (t * π : ℂ) = ((π * t : ℝ) : ℂ) * Complex.I := by push_cast; ring
    rw [hζ_def, harg, Complex.exp_mul_I, Complex.ofReal_cos, Complex.ofReal_sin]
  have hζ_star : star ζ = (Real.cos (π * t) : ℂ) - (Real.sin (π * t) : ℂ) * Complex.I := by
    rw [hζ, star_add, star_mul, Complex.star_def, Complex.conj_ofReal, Complex.conj_ofReal,
      Complex.conj_I]; ring
  have hcos_sq : ((Real.cos (π * t / 2) ^ 2 : ℝ) : ℂ) = (1 + (Real.cos (π * t) : ℂ)) / 2 := by
    have h := Real.cos_sq (π * t / 2)
    have htwo_angle : 2 * (π * t / 2) = π * t := by ring
    rw [htwo_angle] at h
    rw [h]; push_cast; ring
  have hsin_sq : ((Real.sin (π * t / 2) ^ 2 : ℝ) : ℂ) = (1 - (Real.cos (π * t) : ℂ)) / 2 := by
    rw [Real.sin_sq, Complex.ofReal_sub, Complex.ofReal_one, hcos_sq]; ring
  have hpyth : (Real.cos (π * t) : ℂ) ^ 2 + (Real.sin (π * t) : ℂ) ^ 2 = 1 := by
    exact_mod_cast Real.cos_sq_add_sin_sq (π * t)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hcos_sq, hζ_star, hζ]
    linear_combination (1 / 4 : ℂ) * hpyth - (1 / 4 : ℂ) * (Real.sin (π * t) : ℂ) ^ 2 * Complex.I_sq
  · rw [hζ_star, hζ]
    linear_combination -(1 / 4 : ℂ) * hpyth +
      (1 / 4 : ℂ) * (Real.sin (π * t) : ℂ) ^ 2 * Complex.I_sq
  · rw [hζ_star, hζ]
    linear_combination -(1 / 4 : ℂ) * hpyth +
      (1 / 4 : ℂ) * (Real.sin (π * t) : ℂ) ^ 2 * Complex.I_sq
  · rw [hsin_sq, hζ_star, hζ]
    linear_combination (1 / 4 : ℂ) * hpyth - (1 / 4 : ℂ) * (Real.sin (π * t) : ℂ) ^ 2 * Complex.I_sq

private theorem real_smul_cstarMatrix {m' n' : Type*} (c : ℝ) (M : CStarMatrix m' n' A) :
    c • M = (c : ℂ) • M := by
  rw [← algebraMap_smul ℂ c M, Complex.coe_algebraMap]

section Fintype

variable [Fintype m] [Fintype n] {p : CStarMatrix m m A} {q : CStarMatrix n n A}
  {v : CStarMatrix n m A}

private theorem mul_eq_of_conjTranspose_mul_self
    (hp : IsStarProjection p) (hv₁ : v.conjTranspose * v = p) (hv₂ : v * v.conjTranspose = q) :
    v * p = v ∧ p * v.conjTranspose = v.conjTranspose ∧
      q * v = v ∧ v.conjTranspose * q = v.conjTranspose := by
  have hvvv : v * v.conjTranspose * v = v :=
    mul_conjTranspose_mul_self_of_isIdempotentElem (hv₁.symm ▸ hp.isIdempotentElem)
  have hvvv' : v.conjTranspose * v * v.conjTranspose = v.conjTranspose :=
    conjTranspose_mul_self_mul_conjTranspose_of_isIdempotentElem (hv₁.symm ▸ hp.isIdempotentElem)
  exact ⟨by rw [← hv₁, ← mul_assoc_rectangular, hvvv], by rw [← hv₁, hvvv'],
    by rw [← hv₂, hvvv], by rw [← hv₂, ← mul_assoc_rectangular, hvvv']⟩

/-- When `v` implements a Murray–von Neumann equivalence between `p` and `q`,
`stabilizedProjection p q v` is a star projection in `CStarMatrix (m ⊕ n) (m ⊕ n) A`. -/
theorem isStarProjection_stabilizedProjection (hp : IsStarProjection p) (hq : IsStarProjection q)
    (hv₁ : v.conjTranspose * v = p) (hv₂ : v * v.conjTranspose = q) :
    IsStarProjection (stabilizedProjection p q v) := by
  obtain ⟨hvp, hpv, hqv, hvq⟩ := mul_eq_of_conjTranspose_mul_self hp hv₁ hv₂
  refine ⟨?_, ?_⟩
  · rw [IsIdempotentElem, stabilizedProjection_def, smul_mul, mul_smul, smul_smul, fromBlocks_mul]
    simp only [CStarMatrix.neg_mul, CStarMatrix.mul_neg, neg_neg, hp.isIdempotentElem.eq,
      hq.isIdempotentElem.eq, hv₁, hv₂, hvp, hpv, hqv, hvq, ← two_smul ℝ,
      fromBlocks_smul, smul_neg, smul_smul]
    norm_num
  · rw [isSelfAdjoint_iff, stabilizedProjection_def, star_smul, star_trivial, star_fromBlocks,
      hp.isSelfAdjoint.star_eq, hq.isSelfAdjoint.star_eq, conjTranspose_neg, conjTranspose_neg,
      conjTranspose_conjTranspose]

/-- Left product of `stabilizedProjection p q v` with `fromBlocks p 0 0 0`. -/
theorem stabilizedProjection_mul_fromBlocks
    (hp : IsStarProjection p) (hv₁ : v.conjTranspose * v = p) (hv₂ : v * v.conjTranspose = q) :
    stabilizedProjection p q v * fromBlocks p 0 0 0 = (1 / 2 : ℝ) • fromBlocks p 0 (-v) 0 := by
  obtain ⟨hvp, -, -, -⟩ := mul_eq_of_conjTranspose_mul_self hp hv₁ hv₂
  rw [stabilizedProjection_def, smul_mul, fromBlocks_mul]; simp [hp.isIdempotentElem.eq, hvp]

/-- Right product of `fromBlocks p 0 0 0` with `stabilizedProjection p q v`. -/
theorem fromBlocks_mul_stabilizedProjection
    (hp : IsStarProjection p) (hv₁ : v.conjTranspose * v = p) (hv₂ : v * v.conjTranspose = q) :
    fromBlocks p 0 0 0 * stabilizedProjection p q v =
      (1 / 2 : ℝ) • fromBlocks p (-v.conjTranspose) 0 0 := by
  obtain ⟨-, hpv, -, -⟩ := mul_eq_of_conjTranspose_mul_self hp hv₁ hv₂
  rw [stabilizedProjection_def, mul_smul, fromBlocks_mul]; simp [hp.isIdempotentElem.eq, hpv]

/-- Two-sided compression of `fromBlocks p 0 0 0` by `stabilizedProjection p q v`. -/
theorem stabilizedProjection_mul_fromBlocks_mul
    (hp : IsStarProjection p) (hv₁ : v.conjTranspose * v = p) (hv₂ : v * v.conjTranspose = q) :
    stabilizedProjection p q v * fromBlocks p 0 0 0 * stabilizedProjection p q v =
      (1 / 4 : ℝ) • fromBlocks p (-v.conjTranspose) (-v) q := by
  obtain ⟨hvp, hpv, -, -⟩ := mul_eq_of_conjTranspose_mul_self hp hv₁ hv₂
  rw [stabilizedProjection_mul_fromBlocks hp hv₁ hv₂, stabilizedProjection_def, smul_mul, mul_smul,
    smul_smul, fromBlocks_mul]
  simp only [CStarMatrix.neg_mul, CStarMatrix.mul_neg, neg_neg, CStarMatrix.zero_mul, add_zero,
    hp.isIdempotentElem.eq, hpv, hvp, hv₂]
  norm_num

/-- In `Unitization ℂ (CStarMatrix (m ⊕ n) (m ⊕ n) A)`, `stabilizedRotation p q v t` is the
unitary conjugate of `fromBlocks p 0 0 0` by `expUnitary ((t * π) • r)` for
`r = stabilizedProjection p q v`. -/
theorem inr_stabilizedRotation_eq_expUnitary_conj [PartialOrder A] [StarOrderedRing A]
    (hp : IsStarProjection p) (hq : IsStarProjection q)
    (hv₁ : v.conjTranspose * v = p) (hv₂ : v * v.conjTranspose = q) (t : ℝ) :
    let u := selfAdjoint.expUnitary ((t * π) •
      ⟨((stabilizedProjection p q v : CStarMatrix (m ⊕ n) (m ⊕ n) A) :
          Unitization ℂ (CStarMatrix (m ⊕ n) (m ⊕ n) A)),
        selfAdjoint.mem_iff.mpr (((isStarProjection_stabilizedProjection hp hq hv₁ hv₂).map
          (Unitization.inrNonUnitalStarAlgHom ℂ _)).isSelfAdjoint)⟩)
    ((stabilizedRotation p q v t : CStarMatrix (m ⊕ n) (m ⊕ n) A) :
        Unitization ℂ (CStarMatrix (m ⊕ n) (m ⊕ n) A)) =
      (u : Unitization ℂ _) *
        ((fromBlocks p (0 : CStarMatrix m n A) 0 0 : CStarMatrix (m ⊕ n) (m ⊕ n) A) :
          Unitization ℂ (CStarMatrix (m ⊕ n) (m ⊕ n) A)) * star (u : Unitization ℂ _) := by
  set B := CStarMatrix (m ⊕ n) (m ⊕ n) A
  set r : B := stabilizedProjection p q v
  set x : B := fromBlocks p (0 : CStarMatrix m n A) 0 0
  have hr_inr : IsStarProjection (r : Unitization ℂ B) :=
    (isStarProjection_stabilizedProjection hp hq hv₁ hv₂).map
      (Unitization.inrNonUnitalStarAlgHom ℂ B)
  set ζ : ℂ := Complex.exp (Complex.I * (t * π))
  have h_exp : (selfAdjoint.expUnitary ((t * π) •
      ⟨(r : Unitization ℂ B), selfAdjoint.mem_iff.mpr hr_inr.isSelfAdjoint⟩) :
      Unitization ℂ B) = 1 + (ζ - 1) • (r : Unitization ℂ B) := by
    simpa [ζ] using hr_inr.coe_expUnitary_smul (t * π)
  dsimp only
  rw [h_exp, star_add, star_one, star_smul, star_sub, star_one, hr_inr.isSelfAdjoint.star_eq]
  have hexpand :
      (1 + (ζ - 1) • (r : Unitization ℂ B)) * (x : Unitization ℂ B) *
          (1 + (star ζ - 1) • (r : Unitization ℂ B)) =
        ((x + (ζ - 1) • (r * x) + (star ζ - 1) • (x * r) +
          ((ζ - 1) * (star ζ - 1)) • (r * x * r) : B) : Unitization ℂ B) := by
    push_cast
    simp only [add_mul, mul_add, one_mul, mul_one, smul_add, smul_mul_assoc, mul_smul_comm,
      smul_smul, mul_assoc, mul_comm (star ζ - 1) (ζ - 1)]; abel
  rw [hexpand]; congr 1
  obtain ⟨hc11, hc12, hc21, hc22⟩ := exp_I_mul_pi_identities (ζ := ζ) t rfl
  dsimp only [B, r, x]
  rw [stabilizedRotation_def, stabilizedProjection_mul_fromBlocks_mul hp hv₁ hv₂,
    stabilizedProjection_mul_fromBlocks hp hv₁ hv₂,
    fromBlocks_mul_stabilizedProjection hp hv₁ hv₂]
  simp only [fromBlocks_smul, fromBlocks_add, smul_zero, smul_neg, add_zero, zero_add,
    fromBlocks_inj, real_smul_cstarMatrix, Complex.ofReal_div, Complex.ofReal_one,
    Complex.ofReal_ofNat, smul_smul]
  refine ⟨?_, ?_, ?_, ?_⟩
  · nth_rw 2 [← one_smul ℂ p]; rw [← add_smul, ← add_smul, ← add_smul, hc11]
  · rw [← neg_smul, ← neg_smul, ← add_smul, ← sub_eq_add_neg, hc12]
  · rw [← neg_smul, ← neg_smul, ← add_smul, ← sub_eq_add_neg, hc21]
  · rw [hc22]

/-- For every `t : ℝ`, `stabilizedRotation p q v t` is a star projection when `p` and `q` are star
projections with `v.conjTranspose * v = p` and `v * v.conjTranspose = q`. -/
theorem isStarProjection_stabilizedRotation (hp : IsStarProjection p) (hq : IsStarProjection q)
    (hv₁ : v.conjTranspose * v = p) (hv₂ : v * v.conjTranspose = q) (t : ℝ) :
    IsStarProjection (stabilizedRotation p q v t) := by
  let _ : PartialOrder A := CStarAlgebra.spectralOrder A
  let _ : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
  set B := CStarMatrix (m ⊕ n) (m ⊕ n) A
  let u := selfAdjoint.expUnitary ((t * π) •
    ⟨((stabilizedProjection p q v : B) : Unitization ℂ B),
      selfAdjoint.mem_iff.mpr (((isStarProjection_stabilizedProjection hp hq hv₁ hv₂).map
        (Unitization.inrNonUnitalStarAlgHom ℂ B)).isSelfAdjoint)⟩)
  set x0 : Unitization ℂ B := ((fromBlocks p (0 : CStarMatrix m n A) 0 0 : B) : Unitization ℂ B)
  have hx : IsStarProjection x0 :=
    (isStarProjection_fromBlocks_zero₁₂_zero₂₁.mpr ⟨hp, .zero _⟩).map
      (Unitization.inrNonUnitalStarAlgHom ℂ B)
  have hconj_proj : IsStarProjection ((u : Unitization ℂ B) * x0 * star (u : Unitization ℂ B)) := by
    simpa using hx.map (Unitary.conjStarAlgAut ℂ (Unitization ℂ B) u)
  rw [← inr_stabilizedRotation_eq_expUnitary_conj hp hq hv₁ hv₂ t] at hconj_proj
  exact ⟨Unitization.inr_injective (R := ℂ)
      (by simpa only [Unitization.inr_mul] using hconj_proj.isIdempotentElem.eq),
    Unitization.inr_injective (R := ℂ)
      (by simpa only [Unitization.inr_star] using hconj_proj.isSelfAdjoint.star_eq)⟩

/-- Every point on `stabilizedPath p q v` is a star projection when `v` implements `p ∼ q`. -/
theorem isStarProjection_stabilizedPath (hp : IsStarProjection p) (hq : IsStarProjection q)
    (hv₁ : v.conjTranspose * v = p) (hv₂ : v * v.conjTranspose = q) (t : I) :
    IsStarProjection (stabilizedPath p q v t) :=
  isStarProjection_stabilizedRotation hp hq hv₁ hv₂ t

/-- **Stabilized homotopy of Murray–von Neumann equivalent projections**: if `p` and `q` are
Murray–von Neumann equivalent over a possibly non-unital C⋆-algebra `A`, then `fromBlocks p 0 0 0`
and `fromBlocks 0 0 0 q` are joined by a norm-continuous path of star projections. -/
theorem MurrayVonNeumannEquiv.exists_stabilized_path (h : MurrayVonNeumannEquiv p q) :
    ∃ γ : Path (CStarMatrix.fromBlocks p (0 : CStarMatrix m n A) 0 0)
        (CStarMatrix.fromBlocks (0 : CStarMatrix m m A) 0 0 q),
      ∀ t : I, IsStarProjection (γ t) := by
  obtain ⟨hp, hq, v, hv₁, hv₂⟩ := h
  exact ⟨stabilizedPath p q v, isStarProjection_stabilizedPath hp hq hv₁ hv₂⟩

/-- **Characterization of Murray–von Neumann equivalence via stabilized homotopy**: star projections
`p : CStarMatrix m m A` and `q : CStarMatrix n n A` over a C⋆-algebra `A` are Murray–von Neumann
equivalent iff `fromBlocks p 0 0 0` and `fromBlocks 0 0 0 q` are joined by a norm-continuous path of
star projections in `CStarMatrix (m ⊕ n) (m ⊕ n) A`. -/
theorem murrayVonNeumannEquiv_iff_exists_stabilized_path
    (hp : IsStarProjection p) (hq : IsStarProjection q) :
    MurrayVonNeumannEquiv p q ↔
      ∃ γ : Path (fromBlocks p (0 : CStarMatrix m n A) 0 0)
          (fromBlocks (0 : CStarMatrix m m A) 0 0 q),
        ∀ t : I, IsStarProjection (γ t) :=
  ⟨MurrayVonNeumannEquiv.exists_stabilized_path, fun ⟨γ, hγ⟩ ↦
    (hp.murrayVonNeumannEquiv_inlCorner (n := n)).trans
      ((γ.murrayVonNeumannEquiv_of_isStarProjection hγ).trans
        (hq.murrayVonNeumannEquiv_inrCorner (m := m)).symm)⟩

end Fintype

end RotationPath

end StabilizedHomotopy

end CStarMatrix
