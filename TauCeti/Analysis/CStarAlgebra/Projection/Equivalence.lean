/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.CStarMatrix.Block
public import TauCeti.Algebra.Star.PartialIsometry
public import Mathlib.Analysis.CStarAlgebra.Unitization
import TauCeti.Algebra.Star.Projection.Basic
import TauCeti.Data.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Data.Matrix.ColumnRowPartitioned

/-!
# Rectangular Murray–von Neumann equivalence

Matrix projections are Murray–von Neumann equivalent when they are the initial and final
projections of a rectangular matrix. The index types may differ, so this relation identifies
a projection with its zero padding, without identifying different matrix sizes by casts.

We prove reflexivity on projections, symmetry, transitivity, compatibility with block sums,
corner embeddings, matrix units, reindexing, orthogonal sums, and preservation by nonunital star
homomorphisms, as well as descent of unitary conjugacy in the forced unitization to Murray–von
Neumann equivalence and the resulting projection setoid. No unit, separability, or cancellation is
assumed.

## References

* B. Blackadar, *K-Theory for Operator Algebras*, §4.6 (Definition 4.6.1) and §5.1.
-/

public section

open scoped Matrix

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
    MurrayVonNeumannEquiv (CStarMatrix.fromBlocks p 0 0 p')
      (CStarMatrix.fromBlocks q 0 0 q') := by
  obtain ⟨hp, hq, v, hv, hv'⟩ := h
  obtain ⟨hp', hq', w, hw, hw'⟩ := h'
  refine ⟨⟨?_, isSelfAdjoint_fromBlocks_zero₁₂_zero₂₁.mpr ⟨hp.isSelfAdjoint, hp'.isSelfAdjoint⟩⟩,
    ⟨?_, isSelfAdjoint_fromBlocks_zero₁₂_zero₂₁.mpr ⟨hq.isSelfAdjoint, hq'.isSelfAdjoint⟩⟩,
    CStarMatrix.fromBlocks v 0 0 w, ?_, ?_⟩
  · rw [IsIdempotentElem, fromBlocks_multiply]
    simp [hp.isIdempotentElem.eq, hp'.isIdempotentElem.eq]
  · rw [IsIdempotentElem, fromBlocks_multiply]
    simp [hq.isIdempotentElem.eq, hq'.isIdempotentElem.eq]
  · simp [fromBlocks_conjTranspose, fromBlocks_multiply, hv, hw]
  · simp [fromBlocks_conjTranspose, fromBlocks_multiply, hv', hw']

/-- Upper-left corner embeddings of equivalent projections are equivalent. -/
theorem inl {R : Type*} [Semiring R] [Module R A] (h : MurrayVonNeumannEquiv p q) :
    MurrayVonNeumannEquiv (CStarMatrix.inl (n := k) (R := R) p)
      (CStarMatrix.inl (n := l) (R := R) q) := by
  simpa only [inl_apply] using h.fromBlocks .zero

/-- Lower-right corner embeddings of equivalent projections are equivalent. -/
theorem inr {R : Type*} [Semiring R] [Module R A] (h : MurrayVonNeumannEquiv p q) :
    MurrayVonNeumannEquiv (CStarMatrix.inr (m := k) (R := R) p)
      (CStarMatrix.inr (m := l) (R := R) q) := by
  simpa only [inr_apply] using MurrayVonNeumannEquiv.zero.fromBlocks h

/-- Diagonal matrix units supported by the same projection `a` at positions `i` and `j` are
Murray–von Neumann equivalent. -/
theorem single [DecidableEq m] [DecidableEq n] {a : A} (ha : IsStarProjection a) (i : m) (j : n) :
    MurrayVonNeumannEquiv (CStarMatrix.single i i a) (CStarMatrix.single j j a) := by
  refine ⟨?_, ?_, CStarMatrix.single j i a, ?_, ?_⟩
  · simpa only [singleNonUnitalStarAlgHom_apply] using ha.map (singleNonUnitalStarAlgHom (R := ℕ) i)
  · simpa only [singleNonUnitalStarAlgHom_apply] using ha.map (singleNonUnitalStarAlgHom (R := ℕ) j)
  · simp [ha.isSelfAdjoint.star_eq, ha.isIdempotentElem.eq]
  · simp [ha.isSelfAdjoint.star_eq, ha.isIdempotentElem.eq]

/-- Reindexing equivalent projections along size equivalences preserves Murray–von Neumann
equivalence. -/
theorem reindexₐ {R m' n' : Type*} [Semiring R] [Module R A] [Fintype m'] [Fintype n']
    (h : MurrayVonNeumannEquiv p q) (eₘ : m ≃ m') (eₙ : n ≃ n') :
    MurrayVonNeumannEquiv (CStarMatrix.reindexₐ R A eₘ p) (CStarMatrix.reindexₐ R A eₙ q) := by
  obtain ⟨hp, hq, v, hvp, hvq⟩ := h
  refine ⟨hp.map (CStarMatrix.reindexₐ R A eₘ), hq.map (CStarMatrix.reindexₐ R A eₙ),
    CStarMatrix.reindexₗ R A eₙ eₘ v, ?_, ?_⟩
  · rw [reindexₗ_conjTranspose, reindexₗ_mul, hvp, reindexₗ_eq_reindexₐ]
  · rw [reindexₗ_conjTranspose, reindexₗ_mul, hvq, reindexₗ_eq_reindexₐ]

/-- A nonunital star ring homomorphism preserves rectangular equivalence entrywise. -/
theorem map [NonUnitalSemiring B] [StarRing B] {F : Type*} [FunLike F A B]
    [NonUnitalRingHomClass F A B] [StarHomClass F A B]
    (h : MurrayVonNeumannEquiv p q) (f : F) :
    MurrayVonNeumannEquiv (p.map f) (q.map f) := by
  obtain ⟨hp, hq, v, hv, hv'⟩ := h
  refine ⟨isStarProjection_iff'.mpr ⟨?_, ?_⟩, isStarProjection_iff'.mpr ⟨?_, ?_⟩, v.map f, ?_, ?_⟩
  · rw [← map_mul, hp.isIdempotentElem.eq]
  · rw [star_eq_conjTranspose, ← map_conjTranspose, ← star_eq_conjTranspose,
      hp.isSelfAdjoint.star_eq]
  · rw [← map_mul, hq.isIdempotentElem.eq]
  · rw [star_eq_conjTranspose, ← map_conjTranspose, ← star_eq_conjTranspose,
      hq.isSelfAdjoint.star_eq]
  · rw [← map_conjTranspose, ← map_mul, hv]
  · rw [← map_conjTranspose, ← map_mul, hv']

/-- A nonunital `⋆`-algebra homomorphism preserves Murray–von Neumann equivalence entrywise. -/
theorem mapₙₐ {R : Type*} [Semiring R] [NonUnitalSemiring B] [StarRing B] [Module R A]
    [Module R B] (h : MurrayVonNeumannEquiv p q) (f : A →⋆ₙₐ[R] B) :
    MurrayVonNeumannEquiv (CStarMatrix.mapₙₐ f p) (CStarMatrix.mapₙₐ f q) := by
  simpa only [mapₙₐ_eq_map] using h.map f

/-- Padding a projection by a zero block does not change its rectangular equivalence class. -/
theorem pad_zero (hp : IsStarProjection p) :
    MurrayVonNeumannEquiv p (CStarMatrix.fromBlocks p 0 0 (0 : CStarMatrix k k A)) := by
  have hsa : (ofMatrix.symm p)ᴴ = ofMatrix.symm p := by
    simpa only [ofMatrix_symm_star] using congrArg ofMatrix.symm hp.isSelfAdjoint.star_eq
  have hid : ofMatrix.symm p * ofMatrix.symm p = ofMatrix.symm p :=
    ofMatrix_symm_mul_eq hp.isIdempotentElem.eq
  refine ⟨hp, ⟨?_, isSelfAdjoint_fromBlocks_zero₁₂_zero₂₁.mpr ⟨hp.isSelfAdjoint, .zero _⟩⟩,
    ofMatrix (Matrix.fromRows (ofMatrix.symm p) (0 : Matrix k m A)), ?_, ?_⟩
  · rw [IsIdempotentElem, fromBlocks_multiply]
    simp [hp.isIdempotentElem.eq]
  all_goals
    apply ofMatrix.symm.injective
    simp only [ofMatrix_symm_mul, ofMatrix_symm_conjTranspose, ofMatrix_symm_fromBlocks,
      ofMatrix_symm_zero, Equiv.symm_apply_apply,
      Matrix.conjTranspose_fromRows_eq_fromCols_conjTranspose, Matrix.conjTranspose_zero, hsa]
  · ext i j
    simpa [Matrix.mul_apply] using congrFun (congrFun hid i) j
  · ext (i | i) (j | j)
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
protected theorem trans (h : MurrayVonNeumannEquiv p q) (h' : MurrayVonNeumannEquiv q r) :
    MurrayVonNeumannEquiv p r := by
  obtain ⟨v, hv, hv', hvp⟩ := h.exists_matrix_mul_eq_self
  obtain ⟨w, hw, hw', hwq⟩ := h'.exists_matrix_mul_eq_self
  have hqv : q * v = v := mul_self_eq_self_of_mul_eq hv hv' hvp
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

/-- Orthogonal sums of Murray–von Neumann equivalent projections are equivalent. -/
theorem add_of_mul_eq_zero {p₁ p₂ : CStarMatrix m m A} {q₁ q₂ : CStarMatrix n n A}
    (h₁ : MurrayVonNeumannEquiv p₁ q₁) (h₂ : MurrayVonNeumannEquiv p₂ q₂)
    (hp : p₁ * p₂ = 0) (hq : q₁ * q₂ = 0) :
    MurrayVonNeumannEquiv (p₁ + p₂) (q₁ + q₂) := by
  obtain ⟨v₁, hv₁p, hv₁q, hv₁⟩ := h₁.exists_matrix_mul_eq_self
  obtain ⟨v₂, hv₂p, hv₂q, hv₂⟩ := h₂.exists_matrix_mul_eq_self
  have hp' : p₂ * p₁ = 0 := by
    have h := congrArg conjTranspose hp
    rwa [conjTranspose_mul, ← star_eq_conjTranspose, ← star_eq_conjTranspose,
      h₁.isStarProjection_left.isSelfAdjoint.star_eq,
      h₂.isStarProjection_left.isSelfAdjoint.star_eq, conjTranspose_zero] at h
  have hq' : q₂ * q₁ = 0 := by
    have h := congrArg conjTranspose hq
    rwa [conjTranspose_mul, ← star_eq_conjTranspose, ← star_eq_conjTranspose,
      h₁.isStarProjection_right.isSelfAdjoint.star_eq,
      h₂.isStarProjection_right.isSelfAdjoint.star_eq, conjTranspose_zero] at h
  have hv₁_conj : p₁ * v₁.conjTranspose = v₁.conjTranspose :=
    mul_conjTranspose_eq_self_of_mul_eq hv₁p hv₁
  have hv₂_conj : p₂ * v₂.conjTranspose = v₂.conjTranspose :=
    mul_conjTranspose_eq_self_of_mul_eq hv₂p hv₂
  have hq₁v₁ : q₁ * v₁ = v₁ := mul_self_eq_self_of_mul_eq hv₁p hv₁q hv₁
  have hv₁q₁ : v₁.conjTranspose * q₁ = v₁.conjTranspose :=
    conjTranspose_mul_eq_self_of_mul_eq hv₁p hv₁q hv₁
  have hq₂v₂ : q₂ * v₂ = v₂ := mul_self_eq_self_of_mul_eq hv₂p hv₂q hv₂
  have hv₂q₂ : v₂.conjTranspose * q₂ = v₂.conjTranspose :=
    conjTranspose_mul_eq_self_of_mul_eq hv₂p hv₂q hv₂
  have h12_conj : v₁.conjTranspose * v₂ = 0 := by
    calc
      v₁.conjTranspose * v₂ = (v₁.conjTranspose * q₁) * (q₂ * v₂) := by rw [hv₁q₁, hq₂v₂]
      _ = v₁.conjTranspose * (q₁ * q₂) * v₂ := by simp only [mul_assoc_rectangular]
      _ = 0 := by rw [hq, CStarMatrix.mul_zero, CStarMatrix.zero_mul]
  have h21_conj : v₂.conjTranspose * v₁ = 0 := by
    calc
      v₂.conjTranspose * v₁ = (v₂.conjTranspose * q₂) * (q₁ * v₁) := by rw [hv₂q₂, hq₁v₁]
      _ = v₂.conjTranspose * (q₂ * q₁) * v₁ := by simp only [mul_assoc_rectangular]
      _ = 0 := by rw [hq', CStarMatrix.mul_zero, CStarMatrix.zero_mul]
  have h12 : v₁ * v₂.conjTranspose = 0 := by
    calc
      v₁ * v₂.conjTranspose = (v₁ * p₁) * (p₂ * v₂.conjTranspose) := by rw [hv₁, hv₂_conj]
      _ = v₁ * (p₁ * p₂) * v₂.conjTranspose := by simp only [mul_assoc_rectangular]
      _ = 0 := by rw [hp, CStarMatrix.mul_zero, CStarMatrix.zero_mul]
  have h21 : v₂ * v₁.conjTranspose = 0 := by
    calc
      v₂ * v₁.conjTranspose = (v₂ * p₂) * (p₁ * v₁.conjTranspose) := by rw [hv₂, hv₁_conj]
      _ = v₂ * (p₂ * p₁) * v₁.conjTranspose := by simp only [mul_assoc_rectangular]
      _ = 0 := by rw [hp', CStarMatrix.mul_zero, CStarMatrix.zero_mul]
  refine ⟨h₁.isStarProjection_left.add h₂.isStarProjection_left hp,
    h₁.isStarProjection_right.add h₂.isStarProjection_right hq, v₁ + v₂, ?_, ?_⟩
  · simp [CStarMatrix.add_mul, CStarMatrix.mul_add, hv₁p, hv₂p, h12_conj, h21_conj]
  · simp [CStarMatrix.add_mul, CStarMatrix.mul_add, hv₁q, hv₂q, h12, h21]

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
  · rw [← star_eq_conjTranspose]
    exact hp.star_mul_mul_self_of_mem_unitary u.property
  · rw [← star_eq_conjTranspose]
    exact hp.mul_star_mul_eq_mul_mul_star _

/-- If two matrix projections `p, q : CStarMatrix n n A` over a possibly non-unital `⋆`-algebra `A`
become unitarily conjugate inside the unitization `Unitization R (CStarMatrix n n A)`, then `p` and
`q` are Murray–von Neumann equivalent inside `CStarMatrix n n A`. -/
theorem murrayVonNeumannEquiv_of_unitization_unitary_conj {R : Type*}
    [CommSemiring R] [StarRing R] [NonUnitalSemiring A] [StarRing A] [Module R A]
    [IsScalarTower R A A] [SMulCommClass R A A] [StarModule R A]
    {p q : CStarMatrix n n A} (hp : IsStarProjection p)
    {u : Unitization R (CStarMatrix n n A)}
    (hu : u ∈ unitary (Unitization R (CStarMatrix n n A)))
    (hconj : u * (p : Unitization R (CStarMatrix n n A)) * star u =
      (q : Unitization R (CStarMatrix n n A))) :
    MurrayVonNeumannEquiv p q := by
  let M := CStarMatrix n n A
  let v : M := (u * (p : Unitization R M)).snd
  have hv_coe : (v : Unitization R M) = u * (p : Unitization R M) :=
    Unitization.inr_snd_of_fst_eq_zero (by simp [Unitization.fst_mul, Unitization.fst_inr])
  have hp_coe : IsStarProjection (p : Unitization R M) := hp.inr
  have hq : IsStarProjection q := by
    have hq_snd := Unitization.isStarProjection_snd_conj hp hu
    rwa [hconj, Unitization.snd_inr] at hq_snd
  refine (murrayVonNeumannEquiv_iff hp hq).mpr ⟨v, Unitization.inr_injective (R := R) ?_,
    Unitization.inr_injective (R := R) ?_⟩
  · rw [Unitization.inr_mul, ← star_eq_conjTranspose, Unitization.inr_star, hv_coe]
    exact hp_coe.star_mul_mul_self_of_mem_unitary hu
  · rw [Unitization.inr_mul, ← star_eq_conjTranspose, Unitization.inr_star, hv_coe]
    exact (hp_coe.mul_star_mul_eq_mul_mul_star u).trans hconj

/-- Setoid of Murray–von Neumann equivalence on star projections of fixed size `n`. -/
def murrayVonNeumannSetoid (n A : Type*) [Fintype n]
    [NonUnitalSemiring A] [StarRing A] :
    Setoid {p : CStarMatrix n n A // IsStarProjection p} where
  r p q := MurrayVonNeumannEquiv p.val q.val
  iseqv := ⟨fun p ↦ .refl p.property, .symm, .trans⟩

/-- The relation of `murrayVonNeumannSetoid n A` is Murray–von Neumann equivalence on the underlying
projections. -/
@[simp] theorem murrayVonNeumannSetoid_r (n A : Type*) [Fintype n]
    [NonUnitalSemiring A] [StarRing A]
    (p q : {p : CStarMatrix n n A // IsStarProjection p}) :
    (murrayVonNeumannSetoid n A).r p q ↔ MurrayVonNeumannEquiv p.val q.val :=
  (Iff.rfl)

end CStarMatrix
