/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Star.PartialIsometry
public import TauCeti.Analysis.CStarAlgebra.CStarMatrix.Block
public import TauCeti.Analysis.CStarAlgebra.Projection.Homotopy
import Mathlib.Analysis.CStarAlgebra.Unitization
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.Tactic.LinearCombination
import TauCeti.Data.Matrix.Block

/-!
# Murray–von Neumann equivalence and stabilized homotopy of matrix projections

Two projections `p ∈ CStarMatrix m m A` and `q ∈ CStarMatrix n n A`, possibly of different matrix
sizes and over a possibly non-unital `⋆`-algebra `A`, are **Murray–von Neumann equivalent** when
there exists a rectangular partial isometry `v ∈ CStarMatrix n m A` (`v * vᴴ * v = v`) with initial
projection `vᴴ * v = p` and final projection `v * vᴴ = q`. Over any non-unital C⋆-algebra (or any
star-ordered ring with proper star), the partial-isometry condition `v * vᴴ * v = v` is automatic as
soon as `vᴴ * v` is idempotent (`CStarMatrix.murrayVonNeumannEquiv_iff_of_isIdempotentElem`).

This file develops the algebraic, functorial, block-sum, and analytic properties of
`CStarMatrix.MurrayVonNeumannEquiv`, culminating in the equivalence between Murray–von Neumann
equivalence and stabilized projection homotopy over non-unital C⋆-algebras (and stabilized unitary
conjugacy in `U₀` over unital C⋆-algebras):

* Equivalence relation (`murrayVonNeumannEquiv_refl`, `MurrayVonNeumannEquiv.symm`,
  `MurrayVonNeumannEquiv.trans`), non-degeneracy of zero (`murrayVonNeumannEquiv_zero_iff`,
  `zero_murrayVonNeumannEquiv_iff`), and functoriality under `MurrayVonNeumannEquiv.map`, `mapₙₐ`,
  `mapₐ`, and finite reindexing `reindexₐ` (for non-unital `A`).
* Block-diagonal monoid laws up to equivalence: corner padding
  (`murrayVonNeumannEquiv_fromBlocks_zero_right`, `murrayVonNeumannEquiv_fromBlocks_zero_left`),
  congruence (`MurrayVonNeumannEquiv.fromBlocks_zero`), commutativity
  (`murrayVonNeumannEquiv_fromBlocks_zero_comm`), associativity
  (`murrayVonNeumannEquiv_fromBlocks_zero_assoc`), and compatibility of orthogonal addition with
  block-diagonal sums (`add_murrayVonNeumannEquiv_fromBlocks_zero_of_mul_eq_zero`).
* Stabilized self-adjoint unitary conjugacy (`stabilizedSymmUnitary`,
  `stabilizedSymmUnitary_mul_fromBlocks_mul_star`,
  `murrayVonNeumannEquiv_iff_exists_isSelfAdjoint_unitary_fromBlocks_zero_right_left`) via the
  `2 × 2` block involution `fromBlocks (1 - p) vᴴ v (1 - q)`.
* Explicit `2 × 2` rotation path (`stabilizedRotationPath`) and equivalence between Murray–von
  Neumann equivalence and stabilized projection homotopy over non-unital C⋆-algebras
  (`murrayVonNeumannEquiv_iff_exists_path_fromBlocks_zero_right_left`,
  `murrayVonNeumannEquiv_iff_exists_path_fromBlocks_zero_right`), together with stabilized unitary
  conjugacy in `U₀` over unital C⋆-algebras
  (`murrayVonNeumannEquiv_iff_exists_joined_one_unitary_fromBlocks_zero_right_left`,
  `murrayVonNeumannEquiv_iff_exists_joined_one_unitary_fromBlocks_zero_right`).

## References

* B. Blackadar, *K-Theory for Operator Algebras*, 2nd ed., MSRI Publications 5, Cambridge
  University Press (1998), Chapter III, §4.6.
* M. Rørdam, F. Larsen, N. Laustsen, *An Introduction to K-Theory for C⋆-Algebras*, LMS Student
  Texts 49, Cambridge University Press (2000), §§2.1–2.2.
-/

public section

open scoped Real unitInterval

namespace CStarMatrix

section Algebraic

variable {l m m₁ m₂ n n₁ n₂ R A B : Type*}

/-- Two matrix elements `p : CStarMatrix m m A` and `q : CStarMatrix n n A` (potentially of
different finite sizes and over a non-unital `⋆`-algebra) are **Murray–von Neumann equivalent** if
there is a rectangular partial isometry `v : CStarMatrix n m A` with initial projection `vᴴ * v = p`
and final projection `v * vᴴ = q`. -/
def MurrayVonNeumannEquiv [Fintype m] [Fintype n] [Mul A] [AddCommMonoid A] [Star A]
    (p : CStarMatrix m m A) (q : CStarMatrix n n A) : Prop :=
  ∃ v : CStarMatrix n m A, v * v.conjTranspose * v = v ∧ v.conjTranspose * v = p ∧
    v * v.conjTranspose = q

theorem murrayVonNeumannEquiv_iff [Fintype m] [Fintype n] [Mul A] [AddCommMonoid A] [Star A]
    {p : CStarMatrix m m A} {q : CStarMatrix n n A} :
    p.MurrayVonNeumannEquiv q ↔
      ∃ v : CStarMatrix n m A, v * v.conjTranspose * v = v ∧ v.conjTranspose * v = p ∧
        v * v.conjTranspose = q :=
  Iff.rfl

/-- For square matrices of the same size, `MurrayVonNeumannEquiv` is witnessed by a partial isometry
in the sense of `TauCeti.IsPartialIsometry`. -/
theorem murrayVonNeumannEquiv_iff_exists_isPartialIsometry [Fintype n]
    [Mul A] [AddCommMonoid A] [Star A] {p q : CStarMatrix n n A} :
    p.MurrayVonNeumannEquiv q ↔
      ∃ v : CStarMatrix n n A, TauCeti.IsPartialIsometry v ∧ star v * v = p ∧ v * star v = q := by
  simp only [murrayVonNeumannEquiv_iff, TauCeti.isPartialIsometry_iff, star_eq_conjTranspose]

/-- The left argument of a Murray–von Neumann equivalence is a star projection. -/
theorem MurrayVonNeumannEquiv.isStarProjection_left [Fintype m] [Fintype n]
    [NonUnitalSemiring A] [StarRing A] {p : CStarMatrix m m A} {q : CStarMatrix n n A}
    (h : p.MurrayVonNeumannEquiv q) : IsStarProjection p := by
  obtain ⟨v, hv, rfl, -⟩ := h
  refine ⟨?_, ?_⟩
  · rw [IsIdempotentElem, CStarMatrix.mul_assoc v.conjTranspose,
      ← CStarMatrix.mul_assoc v, hv]
  · rw [IsSelfAdjoint, star_eq_conjTranspose, conjTranspose_mul, conjTranspose_conjTranspose]

/-- The right argument of a Murray–von Neumann equivalence is a star projection. -/
theorem MurrayVonNeumannEquiv.isStarProjection_right [Fintype m] [Fintype n]
    [NonUnitalSemiring A] [StarRing A] {p : CStarMatrix m m A} {q : CStarMatrix n n A}
    (h : p.MurrayVonNeumannEquiv q) : IsStarProjection q := by
  obtain ⟨v, hv, -, rfl⟩ := h
  refine ⟨?_, ?_⟩
  · rw [IsIdempotentElem, ← CStarMatrix.mul_assoc, hv]
  · rw [IsSelfAdjoint, star_eq_conjTranspose, conjTranspose_mul, conjTranspose_conjTranspose]

/-- Over a star-ordered ring with proper star, the partial-isometry identity `v * vᴴ * v = v` in
`MurrayVonNeumannEquiv` is automatic whenever `p` is idempotent. -/
theorem murrayVonNeumannEquiv_iff_of_isIdempotentElem [Fintype m] [Fintype n]
    [NonUnitalRing A] [PartialOrder A] [StarRing A] [StarOrderedRing A] [IsProperStar A]
    {p : CStarMatrix m m A} {q : CStarMatrix n n A} (hp : IsIdempotentElem p) :
    p.MurrayVonNeumannEquiv q ↔
      ∃ v : CStarMatrix n m A, v.conjTranspose * v = p ∧ v * v.conjTranspose = q := by
  refine ⟨fun ⟨v, _, hv₁, hv₂⟩ ↦ ⟨v, hv₁, hv₂⟩, fun ⟨v, hv₁, hv₂⟩ ↦ ?_⟩
  exact ⟨v, mul_conjTranspose_mul_self_of_isIdempotentElem (hv₁.symm ▸ hp), hv₁, hv₂⟩

/-- Every matrix star projection is Murray–von Neumann equivalent to itself. -/
theorem murrayVonNeumannEquiv_refl [Fintype m] [NonUnitalSemiring A] [StarRing A]
    {p : CStarMatrix m m A} (hp : IsStarProjection p) : p.MurrayVonNeumannEquiv p := by
  refine ⟨p, ?_, ?_, ?_⟩
  · rw [← star_eq_conjTranspose, hp.isSelfAdjoint.star_eq, hp.isIdempotentElem.eq,
      hp.isIdempotentElem.eq]
  · rw [← star_eq_conjTranspose, hp.isSelfAdjoint.star_eq, hp.isIdempotentElem.eq]
  · rw [← star_eq_conjTranspose, hp.isSelfAdjoint.star_eq, hp.isIdempotentElem.eq]

/-- Murray–von Neumann equivalence is symmetric. -/
@[symm]
theorem MurrayVonNeumannEquiv.symm [Fintype m] [Fintype n] [NonUnitalSemiring A] [StarRing A]
    {p : CStarMatrix m m A} {q : CStarMatrix n n A} (h : p.MurrayVonNeumannEquiv q) :
    q.MurrayVonNeumannEquiv p := by
  obtain ⟨v, hv, hv₁, hv₂⟩ := h
  refine ⟨v.conjTranspose, ?_, ?_, ?_⟩
  · simpa only [conjTranspose_mul, conjTranspose_conjTranspose, CStarMatrix.mul_assoc] using
      congrArg conjTranspose hv
  · rwa [conjTranspose_conjTranspose]
  · rwa [conjTranspose_conjTranspose]

theorem murrayVonNeumannEquiv_comm [Fintype m] [Fintype n] [NonUnitalSemiring A] [StarRing A]
    {p : CStarMatrix m m A} {q : CStarMatrix n n A} :
    p.MurrayVonNeumannEquiv q ↔ q.MurrayVonNeumannEquiv p :=
  ⟨MurrayVonNeumannEquiv.symm, MurrayVonNeumannEquiv.symm⟩

/-- Murray–von Neumann equivalence is transitive across arbitrary finite matrix sizes. -/
@[trans]
theorem MurrayVonNeumannEquiv.trans [Fintype l] [Fintype m] [Fintype n]
    [NonUnitalSemiring A] [StarRing A]
    {p : CStarMatrix l l A} {q : CStarMatrix m m A} {r : CStarMatrix n n A}
    (hpq : p.MurrayVonNeumannEquiv q) (hqr : q.MurrayVonNeumannEquiv r) :
    p.MurrayVonNeumannEquiv r := by
  obtain ⟨v, hv, hv₁, hv₂⟩ := hpq
  obtain ⟨w, hw, hw₁, hw₂⟩ := hqr
  have hqv : q * v = v := by rw [← hv₂, hv]
  have hwq : w * q = w := by rw [← hw₁, ← CStarMatrix.mul_assoc, hw]
  refine ⟨w * v, ?_, ?_, ?_⟩
  · calc w * v * (w * v).conjTranspose * (w * v)
        = w * (v * v.conjTranspose) * (w.conjTranspose * w) * v := by
            simp only [conjTranspose_mul, CStarMatrix.mul_assoc]
      _ = (w * q) * (q * v) := by rw [hv₂, hw₁, CStarMatrix.mul_assoc]
      _ = w * v := by rw [hwq, hqv]
  · calc (w * v).conjTranspose * (w * v)
        = v.conjTranspose * (w.conjTranspose * w * v) := by
            simp only [conjTranspose_mul, CStarMatrix.mul_assoc]
      _ = p := by rw [hw₁, hqv, hv₁]
  · calc w * v * (w * v).conjTranspose
        = w * (v * v.conjTranspose) * w.conjTranspose := by
            simp only [conjTranspose_mul, CStarMatrix.mul_assoc]
      _ = r := by rw [hv₂, hwq, hw₂]

/-- Zero matrices of any two finite sizes are Murray–von Neumann equivalent. -/
theorem murrayVonNeumannEquiv_zero [Fintype m] [Fintype n] [NonUnitalSemiring A] [StarAddMonoid A] :
    (0 : CStarMatrix m m A).MurrayVonNeumannEquiv (0 : CStarMatrix n n A) :=
  ⟨0, by simp, by simp, by simp⟩

/-- Over a star-ordered ring with proper star, only `0` is Murray–von Neumann equivalent to `0`. -/
@[simp]
theorem murrayVonNeumannEquiv_zero_iff [Fintype m] [Fintype n]
    [NonUnitalRing A] [PartialOrder A] [StarRing A] [StarOrderedRing A] [IsProperStar A]
    {p : CStarMatrix m m A} :
    p.MurrayVonNeumannEquiv (0 : CStarMatrix n n A) ↔ p = 0 := by
  refine ⟨fun ⟨v, _, hv₁, hv₂⟩ ↦ ?_, fun h ↦ h ▸ murrayVonNeumannEquiv_zero⟩
  have hv_ct : v.conjTranspose = 0 := by
    rw [← conjTranspose_mul_self_eq_zero, conjTranspose_conjTranspose]
    exact hv₂
  rw [← hv₁, hv_ct, CStarMatrix.zero_mul]

/-- Over a star-ordered ring with proper star, `0` is Murray–von Neumann equivalent only to `0`. -/
@[simp]
theorem zero_murrayVonNeumannEquiv_iff [Fintype m] [Fintype n]
    [NonUnitalRing A] [PartialOrder A] [StarRing A] [StarOrderedRing A] [IsProperStar A]
    {q : CStarMatrix n n A} :
    (0 : CStarMatrix m m A).MurrayVonNeumannEquiv q ↔ q = 0 := by
  rw [murrayVonNeumannEquiv_comm, murrayVonNeumannEquiv_zero_iff]

/-- Any star-preserving non-unital ring homomorphism preserves Murray–von Neumann equivalence
entrywise across arbitrary finite matrix sizes. -/
theorem MurrayVonNeumannEquiv.map [Fintype m] [Fintype n]
    [NonUnitalNonAssocSemiring A] [Star A] [NonUnitalNonAssocSemiring B] [Star B]
    {F : Type*} [FunLike F A B] [NonUnitalRingHomClass F A B] [StarHomClass F A B]
    {p : CStarMatrix m m A} {q : CStarMatrix n n A}
    (h : p.MurrayVonNeumannEquiv q) (f : F) :
    (p.map f).MurrayVonNeumannEquiv (q.map f) := by
  obtain ⟨v, hv, hv₁, hv₂⟩ := h
  refine ⟨v.map f, ?_, ?_, ?_⟩
  · simp [← CStarMatrix.map_mul, hv]
  · simp [← CStarMatrix.map_mul, hv₁]
  · simp [← CStarMatrix.map_mul, hv₂]

/-- Non-unital `⋆`-algebra homomorphisms preserve Murray–von Neumann equivalence across arbitrary
finite matrix sizes. -/
theorem MurrayVonNeumannEquiv.mapₙₐ [Fintype m] [Fintype n] [Semiring R]
    [NonUnitalNonAssocSemiring A] [Module R A] [Star A]
    [NonUnitalNonAssocSemiring B] [Module R B] [Star B]
    {p : CStarMatrix m m A} {q : CStarMatrix n n A}
    (h : p.MurrayVonNeumannEquiv q) (f : A →⋆ₙₐ[R] B) :
    (CStarMatrix.mapₙₐ f p).MurrayVonNeumannEquiv (CStarMatrix.mapₙₐ f q) := by
  simpa using h.map f

/-- Unital `⋆`-algebra homomorphisms preserve Murray–von Neumann equivalence. -/
theorem MurrayVonNeumannEquiv.mapₐ [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    [CommSemiring R] [Semiring A] [Algebra R A] [Star A] [Semiring B] [Algebra R B] [Star B]
    {p : CStarMatrix m m A} {q : CStarMatrix n n A}
    (h : p.MurrayVonNeumannEquiv q) (f : A →⋆ₐ[R] B) :
    (CStarMatrix.mapₐ f p).MurrayVonNeumannEquiv (CStarMatrix.mapₐ f q) := by
  simpa only [mapₐ_apply] using h.map f

/-- Reindexing rows and columns by a bijection `e : m ≃ n` yields a Murray–von Neumann equivalent
projection, even when `A` is non-unital. -/
theorem murrayVonNeumannEquiv_reindexₐ [Fintype m] [Fintype n] [Semiring R]
    [NonUnitalSemiring A] [StarRing A] [Module R A]
    {p : CStarMatrix m m A} (hp : IsStarProjection p) (e : m ≃ n) :
    p.MurrayVonNeumannEquiv (reindexₐ R A e p) := by
  have hp_ct : p.conjTranspose = p := hp.isSelfAdjoint
  refine ⟨reindexₗ R A e (.refl m) p, ?_, ?_, ?_⟩
  · rw [reindexₗ_conjTranspose, hp_ct, ← reindexₗ_mul, ← reindexₗ_mul,
      hp.isIdempotentElem.eq, hp.isIdempotentElem.eq]
  · rw [reindexₗ_conjTranspose, hp_ct, ← reindexₗ_mul, hp.isIdempotentElem.eq,
      reindexₗ_refl, LinearEquiv.refl_apply]
  · rw [reindexₗ_conjTranspose, hp_ct, ← reindexₗ_mul, hp.isIdempotentElem.eq,
      ← reindexₐ_eq_reindexₗ]

/-- Unitary conjugation `u * p * star u` in `CStarMatrix n n A` implies Murray–von Neumann
equivalence. -/
theorem murrayVonNeumannEquiv_star_right_conjugate [Fintype n] [DecidableEq n]
    [Semiring A] [StarRing A] {p : CStarMatrix n n A} (hp : IsStarProjection p)
    (u : unitary (CStarMatrix n n A)) :
    p.MurrayVonNeumannEquiv ((u : CStarMatrix n n A) * p * star (u : CStarMatrix n n A)) := by
  let U : CStarMatrix n n A := u
  have hp_ct : p.conjTranspose = p := hp.isSelfAdjoint
  refine ⟨U * p, ?_, ?_, ?_⟩
  · calc U * p * (U * p).conjTranspose * (U * p)
        = U * p * p * (star U * U) * p := by
            simp only [conjTranspose_mul, hp_ct, star_eq_conjTranspose, CStarMatrix.mul_assoc]
      _ = U * p := by
            rw [Unitary.coe_star_mul_self, mul_one, CStarMatrix.mul_assoc U p p,
              hp.isIdempotentElem.eq, CStarMatrix.mul_assoc U p p, hp.isIdempotentElem.eq]
  · calc (U * p).conjTranspose * (U * p)
        = p * (star U * U) * p := by
            simp only [conjTranspose_mul, hp_ct, star_eq_conjTranspose, CStarMatrix.mul_assoc]
      _ = p := by rw [Unitary.coe_star_mul_self, mul_one, hp.isIdempotentElem.eq]
  · simp only [conjTranspose_mul, hp_ct]
    rw [← star_eq_conjTranspose, ← CStarMatrix.mul_assoc, CStarMatrix.mul_assoc U p p,
      hp.isIdempotentElem.eq]

/-- Left unitary conjugation `star u * p * u` in `CStarMatrix n n A` implies Murray–von Neumann
equivalence. -/
theorem murrayVonNeumannEquiv_star_left_conjugate [Fintype n] [DecidableEq n]
    [Semiring A] [StarRing A] {p : CStarMatrix n n A} (hp : IsStarProjection p)
    (u : unitary (CStarMatrix n n A)) :
    p.MurrayVonNeumannEquiv (star (u : CStarMatrix n n A) * p * (u : CStarMatrix n n A)) := by
  simpa using murrayVonNeumannEquiv_star_right_conjugate hp (star u)

end Algebraic

section BlockOperations

variable {l m m₁ m₂ n n₁ n₂ A : Type*}

/-- Block-diagonal direct sum respects Murray–von Neumann equivalence in both summands. -/
theorem MurrayVonNeumannEquiv.fromBlocks_zero [Fintype m₁] [Fintype m₂] [Fintype n₁] [Fintype n₂]
    [NonUnitalSemiring A] [StarRing A]
    {p₁ : CStarMatrix m₁ m₁ A} {p₂ : CStarMatrix m₂ m₂ A}
    {q₁ : CStarMatrix n₁ n₁ A} {q₂ : CStarMatrix n₂ n₂ A}
    (h₁ : p₁.MurrayVonNeumannEquiv q₁) (h₂ : p₂.MurrayVonNeumannEquiv q₂) :
    (fromBlocks p₁ 0 0 p₂).MurrayVonNeumannEquiv (fromBlocks q₁ 0 0 q₂) := by
  obtain ⟨v₁, hv₁, hp₁, hq₁⟩ := h₁
  obtain ⟨v₂, hv₂, hp₂, hq₂⟩ := h₂
  refine ⟨fromBlocks v₁ 0 0 v₂, ?_, ?_, ?_⟩
  · simp [fromBlocks_multiply, hv₁, hv₂]
  · simp [fromBlocks_multiply, hp₁, hp₂]
  · simp [fromBlocks_multiply, hq₁, hq₂]

/-- Product identities for the row-stacked matrix
`ofMatrix (Matrix.fromRows (ofMatrix.symm a) (ofMatrix.symm b))` over a non-unital `⋆`-semiring. -/
private theorem fromRows_conjTranspose_identities [Fintype m₁] [Fintype m₂] [Fintype n]
    [NonUnitalNonAssocSemiring A] [Star A]
    (a : CStarMatrix m₁ n A) (b : CStarMatrix m₂ n A) :
    let v : CStarMatrix (m₁ ⊕ m₂) n A :=
      ofMatrix (Matrix.fromRows (ofMatrix.symm a) (ofMatrix.symm b))
    v.conjTranspose * v = a.conjTranspose * a + b.conjTranspose * b ∧
      v * v.conjTranspose =
        fromBlocks (a * a.conjTranspose) (a * b.conjTranspose)
          (b * a.conjTranspose) (b * b.conjTranspose) ∧
      ∀ (M₁₁ : CStarMatrix m₁ m₁ A) (M₁₂ : CStarMatrix m₁ m₂ A)
        (M₂₁ : CStarMatrix m₂ m₁ A) (M₂₂ : CStarMatrix m₂ m₂ A),
        fromBlocks M₁₁ M₁₂ M₂₁ M₂₂ * v =
          ofMatrix (Matrix.fromRows (ofMatrix.symm (M₁₁ * a + M₁₂ * b))
            (ofMatrix.symm (M₂₁ * a + M₂₂ * b))) := by
  intro v
  refine ⟨?_, ?_, fun M₁₁ M₁₂ M₂₁ M₂₂ ↦ ?_⟩
  · ext i j
    simp [v, mul_apply, conjTranspose_apply, Fintype.sum_sum_type]
  · ext (i | i) (j | j) <;> simp [v, mul_apply, conjTranspose_apply]
  · ext (i | i) j <;> simp [v, mul_apply, Matrix.mul_apply, Fintype.sum_sum_type]

/-- If `p` and `q` are orthogonal star projections (`p * q = 0`) in `CStarMatrix m m A`, their
internal sum `p + q` is Murray–von Neumann equivalent to their block-diagonal direct sum
`fromBlocks p 0 0 q`. -/
theorem add_murrayVonNeumannEquiv_fromBlocks_zero_of_mul_eq_zero [Fintype m]
    [NonUnitalSemiring A] [StarRing A]
    {p q : CStarMatrix m m A} (hp : IsStarProjection p) (hq : IsStarProjection q)
    (hpq : p * q = 0) :
    (p + q).MurrayVonNeumannEquiv (fromBlocks p 0 0 q) := by
  have hp_ct : p.conjTranspose = p := hp.isSelfAdjoint
  have hq_ct : q.conjTranspose = q := hq.isSelfAdjoint
  have hqp : q * p = 0 := by
    simpa only [conjTranspose_mul, hp_ct, hq_ct, conjTranspose_zero] using
      congrArg conjTranspose hpq
  obtain ⟨hvv₁, hvv₂, hv_mul⟩ := fromRows_conjTranspose_identities p q
  set v : CStarMatrix (m ⊕ m) m A :=
    ofMatrix (Matrix.fromRows (ofMatrix.symm p) (ofMatrix.symm q))
  have hvv : v * v.conjTranspose = fromBlocks p 0 0 q := by
    rw [hvv₂, hp_ct, hq_ct, hp.isIdempotentElem.eq, hq.isIdempotentElem.eq, hpq, hqp]
  refine ⟨v, ?_, ?_, hvv⟩
  · rw [hvv, hv_mul, hp.isIdempotentElem.eq, hq.isIdempotentElem.eq, CStarMatrix.zero_mul,
      CStarMatrix.zero_mul, add_zero, zero_add]
  · rw [hvv₁, hp_ct, hq_ct, hp.isIdempotentElem.eq, hq.isIdempotentElem.eq]

/-- Padding a star projection `p` with a zero lower-right block preserves its Murray–von Neumann
class (`p ∼ diag(p, 0)`). -/
theorem murrayVonNeumannEquiv_fromBlocks_zero_right (n : Type*) [Fintype m] [Fintype n]
    [NonUnitalSemiring A] [StarRing A]
    {p : CStarMatrix m m A} (hp : IsStarProjection p) :
    p.MurrayVonNeumannEquiv (fromBlocks p 0 0 (0 : CStarMatrix n n A)) := by
  simpa only [add_zero] using
    (add_murrayVonNeumannEquiv_fromBlocks_zero_of_mul_eq_zero hp (.zero _)
      (CStarMatrix.mul_zero p)).trans
      ((murrayVonNeumannEquiv_refl hp).fromBlocks_zero murrayVonNeumannEquiv_zero)

/-- Block-diagonal direct sum is commutative up to Murray–von Neumann equivalence. -/
theorem murrayVonNeumannEquiv_fromBlocks_zero_comm [Fintype m] [Fintype n]
    [NonUnitalSemiring A] [StarRing A]
    {p : CStarMatrix m m A} {q : CStarMatrix n n A}
    (hp : IsStarProjection p) (hq : IsStarProjection q) :
    (fromBlocks p 0 0 q).MurrayVonNeumannEquiv (fromBlocks q 0 0 p) := by
  have hproj : IsStarProjection (fromBlocks p 0 0 q) :=
    isStarProjection_fromBlocks_zero.mpr ⟨hp, hq⟩
  simpa only [reindexₐ_sumComm_fromBlocks] using
    murrayVonNeumannEquiv_reindexₐ (R := ℕ) hproj (Equiv.sumComm m n)

/-- Padding a star projection `q` with a zero upper-left block preserves its Murray–von Neumann
class (`q ∼ diag(0, q)`). -/
theorem murrayVonNeumannEquiv_fromBlocks_zero_left (m : Type*) [Fintype m] [Fintype n]
    [NonUnitalSemiring A] [StarRing A]
    {q : CStarMatrix n n A} (hq : IsStarProjection q) :
    q.MurrayVonNeumannEquiv (fromBlocks (0 : CStarMatrix m m A) 0 0 q) :=
  (murrayVonNeumannEquiv_fromBlocks_zero_right m hq).trans
    (murrayVonNeumannEquiv_fromBlocks_zero_comm hq (.zero _))

/-- Block-diagonal direct sum is associative up to Murray–von Neumann equivalence. -/
theorem murrayVonNeumannEquiv_fromBlocks_zero_assoc [Fintype l] [Fintype m] [Fintype n]
    [NonUnitalSemiring A] [StarRing A]
    {p : CStarMatrix l l A} {q : CStarMatrix m m A} {r : CStarMatrix n n A}
    (hp : IsStarProjection p) (hq : IsStarProjection q) (hr : IsStarProjection r) :
    (fromBlocks (fromBlocks p 0 0 q) 0 0 r).MurrayVonNeumannEquiv
      (fromBlocks p 0 0 (fromBlocks q 0 0 r)) := by
  have hproj : IsStarProjection (fromBlocks (fromBlocks p 0 0 q) 0 0 r) :=
    isStarProjection_fromBlocks_zero.mpr ⟨isStarProjection_fromBlocks_zero.mpr ⟨hp, hq⟩, hr⟩
  simpa only [reindexₐ_sumAssoc_fromBlocks_zero] using
    murrayVonNeumannEquiv_reindexₐ (R := ℕ) hproj (Equiv.sumAssoc l m n)

end BlockOperations

section Stabilization

variable {m n A : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
  [Ring A] [StarRing A]

private theorem isSelfAdjoint_fromBlocks_one_sub {p : CStarMatrix m m A} {q : CStarMatrix n n A}
    {v : CStarMatrix n m A} (hv : v * v.conjTranspose * v = v)
    (hv₁ : v.conjTranspose * v = p) (hv₂ : v * v.conjTranspose = q) :
    IsSelfAdjoint (fromBlocks (1 - p) v.conjTranspose v (1 - q)) := by
  have hp : IsStarProjection p := MurrayVonNeumannEquiv.isStarProjection_left ⟨v, hv, hv₁, hv₂⟩
  have hq : IsStarProjection q := MurrayVonNeumannEquiv.isStarProjection_right ⟨v, hv, hv₁, hv₂⟩
  rw [IsSelfAdjoint]
  simp [hp.one_sub.isSelfAdjoint.star_eq, hq.one_sub.isSelfAdjoint.star_eq]

/-- Given a rectangular partial isometry `v : CStarMatrix n m A` with `v * vᴴ * v = v`,
`vᴴ * v = p`, and `v * vᴴ = q`, the `2 × 2` block matrix
`fromBlocks (1 - p) vᴴ v (1 - q)` is a self-adjoint unitary involution in
`CStarMatrix (m ⊕ n) (m ⊕ n) A` conjugating `diag(p, 0)` to `diag(0, q)`. -/
def stabilizedSymmUnitary {p : CStarMatrix m m A} {q : CStarMatrix n n A}
    {v : CStarMatrix n m A} (hv : v * v.conjTranspose * v = v)
    (hv₁ : v.conjTranspose * v = p) (hv₂ : v * v.conjTranspose = q) :
    unitary (CStarMatrix (m ⊕ n) (m ⊕ n) A) := by
  have hp : IsStarProjection p := MurrayVonNeumannEquiv.isStarProjection_left ⟨v, hv, hv₁, hv₂⟩
  let w : CStarMatrix (m ⊕ n) (m ⊕ n) A := fromBlocks (1 - p) v.conjTranspose v (1 - q)
  have hw_sa : star w = w := (isSelfAdjoint_fromBlocks_one_sub hv hv₁ hv₂).star_eq
  have hvp : v * p = v := by rw [← hv₁, ← CStarMatrix.mul_assoc, hv]
  have hpv : p * v.conjTranspose = v.conjTranspose := by
    have := congrArg conjTranspose hvp
    rwa [conjTranspose_mul, ← star_eq_conjTranspose, hp.isSelfAdjoint.star_eq] at this
  have hww : w * w = 1 := by
    apply ofMatrix.symm.injective
    rw [ofMatrix_symm_mul, ofMatrix_symm_fromBlocks, ofMatrix_symm_sub, ofMatrix_symm_sub,
      ofMatrix_symm_one, ofMatrix_symm_one]
    exact Matrix.fromBlocks_one_sub_mul_self_of_mul_eq
      (congrArg ofMatrix.symm hv₁) (congrArg ofMatrix.symm hv₂)
      (congrArg ofMatrix.symm hpv) (congrArg ofMatrix.symm hvp)
  exact ⟨w, Unitary.mem_iff.mpr ⟨by rw [hw_sa, hww], by rw [hw_sa, hww]⟩⟩

@[simp]
theorem coe_stabilizedSymmUnitary {p : CStarMatrix m m A} {q : CStarMatrix n n A}
    {v : CStarMatrix n m A} (hv : v * v.conjTranspose * v = v)
    (hv₁ : v.conjTranspose * v = p) (hv₂ : v * v.conjTranspose = q) :
    (stabilizedSymmUnitary hv hv₁ hv₂ : CStarMatrix (m ⊕ n) (m ⊕ n) A) =
      fromBlocks (1 - p) v.conjTranspose v (1 - q) :=
  (rfl)

/-- The `2 × 2` block unitary `stabilizedSymmUnitary` is self-adjoint. -/
theorem isSelfAdjoint_stabilizedSymmUnitary {p : CStarMatrix m m A} {q : CStarMatrix n n A}
    {v : CStarMatrix n m A} (hv : v * v.conjTranspose * v = v)
    (hv₁ : v.conjTranspose * v = p) (hv₂ : v * v.conjTranspose = q) :
    IsSelfAdjoint (stabilizedSymmUnitary hv hv₁ hv₂ : CStarMatrix (m ⊕ n) (m ⊕ n) A) :=
  isSelfAdjoint_fromBlocks_one_sub hv hv₁ hv₂

@[simp]
theorem star_stabilizedSymmUnitary {p : CStarMatrix m m A} {q : CStarMatrix n n A}
    {v : CStarMatrix n m A} (hv : v * v.conjTranspose * v = v)
    (hv₁ : v.conjTranspose * v = p) (hv₂ : v * v.conjTranspose = q) :
    star (stabilizedSymmUnitary hv hv₁ hv₂) = stabilizedSymmUnitary hv hv₁ hv₂ :=
  Subtype.ext (isSelfAdjoint_stabilizedSymmUnitary hv hv₁ hv₂).star_eq

/-- The self-adjoint unitary `stabilizedSymmUnitary` conjugates `fromBlocks p 0 0 0` to
`fromBlocks 0 0 0 q`. -/
theorem stabilizedSymmUnitary_mul_fromBlocks_mul_star {p : CStarMatrix m m A}
    {q : CStarMatrix n n A} {v : CStarMatrix n m A}
    (hv : v * v.conjTranspose * v = v) (hv₁ : v.conjTranspose * v = p)
    (hv₂ : v * v.conjTranspose = q) :
    (stabilizedSymmUnitary hv hv₁ hv₂ : CStarMatrix (m ⊕ n) (m ⊕ n) A) *
        fromBlocks p 0 0 0 *
        star (stabilizedSymmUnitary hv hv₁ hv₂ : CStarMatrix (m ⊕ n) (m ⊕ n) A) =
      fromBlocks 0 0 0 q := by
  rw [(isSelfAdjoint_stabilizedSymmUnitary hv hv₁ hv₂).star_eq, coe_stabilizedSymmUnitary]
  have hvp : v * p = v := by rw [← hv₁, ← CStarMatrix.mul_assoc, hv]
  apply ofMatrix.symm.injective
  rw [ofMatrix_symm_mul, ofMatrix_symm_mul, ofMatrix_symm_fromBlocks, ofMatrix_symm_fromBlocks,
    ofMatrix_symm_fromBlocks, ofMatrix_symm_sub, ofMatrix_symm_sub, ofMatrix_symm_one,
    ofMatrix_symm_one, ofMatrix_symm_zero]
  exact Matrix.fromBlocks_one_sub_mul_fromBlocks_mul_fromBlocks_one_sub_of_mul_eq
    (congrArg ofMatrix.symm hv₁) (congrArg ofMatrix.symm hv₂) (congrArg ofMatrix.symm hvp)

/-- Over a unital `⋆`-ring, a star projection `p` is Murray–von Neumann equivalent to `q` if and
only if `fromBlocks p 0 0 0` and `fromBlocks 0 0 0 q` are conjugate by a self-adjoint unitary in
`CStarMatrix (m ⊕ n) (m ⊕ n) A`. -/
theorem murrayVonNeumannEquiv_iff_exists_isSelfAdjoint_unitary_fromBlocks_zero_right_left
    {p : CStarMatrix m m A} {q : CStarMatrix n n A}
    (hp : IsStarProjection p) :
    p.MurrayVonNeumannEquiv q ↔
      ∃ u : unitary (CStarMatrix (m ⊕ n) (m ⊕ n) A),
        IsSelfAdjoint (u : CStarMatrix (m ⊕ n) (m ⊕ n) A) ∧
          (u : CStarMatrix (m ⊕ n) (m ⊕ n) A) * fromBlocks p 0 0 0 *
            star (u : CStarMatrix (m ⊕ n) (m ⊕ n) A) = fromBlocks 0 0 0 q := by
  refine ⟨fun ⟨v, hv, hv₁, hv₂⟩ ↦ ⟨stabilizedSymmUnitary hv hv₁ hv₂,
    isSelfAdjoint_stabilizedSymmUnitary hv hv₁ hv₂,
    stabilizedSymmUnitary_mul_fromBlocks_mul_star hv hv₁ hv₂⟩, ?_⟩
  rintro ⟨u, -, hconj⟩
  have hp0 : IsStarProjection (fromBlocks p 0 0 (0 : CStarMatrix n n A)) :=
    isStarProjection_fromBlocks_zero.mpr ⟨hp, .zero _⟩
  have hq : IsStarProjection q :=
    (isStarProjection_fromBlocks_zero.mp (hconj ▸ hp0.star_right_conjugate u)).2
  have hmid : (fromBlocks p 0 0 (0 : CStarMatrix n n A)).MurrayVonNeumannEquiv
      (fromBlocks (0 : CStarMatrix m m A) 0 0 q) :=
    hconj ▸ murrayVonNeumannEquiv_star_right_conjugate hp0 u
  exact (murrayVonNeumannEquiv_fromBlocks_zero_right n hp).trans
    (hmid.trans (murrayVonNeumannEquiv_fromBlocks_zero_left m hq).symm)

end Stabilization

section CStarAlgebra

variable {m n A : Type*} [Fintype m] [Fintype n]

/-- Over a non-unital C⋆-algebra, an idempotent `p` is Murray–von Neumann equivalent to `q` if and
only if `vᴴ * v = p` and `v * vᴴ = q` for some rectangular matrix `v`. -/
theorem murrayVonNeumannEquiv_iff_exists_conjTranspose_mul [NonUnitalCStarAlgebra A]
    {p : CStarMatrix m m A} {q : CStarMatrix n n A} (hp : IsIdempotentElem p) :
    p.MurrayVonNeumannEquiv q ↔
      ∃ v : CStarMatrix n m A, v.conjTranspose * v = p ∧ v * v.conjTranspose = q := by
  let : PartialOrder A := CStarAlgebra.spectralOrder A
  let : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
  exact murrayVonNeumannEquiv_iff_of_isIdempotentElem hp

private theorem murrayVonNeumannEquiv_of_unitization_unitary_conj
    [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    {p q : CStarMatrix n n A} (hp : IsStarProjection p)
    (u : unitary (Unitization ℂ (CStarMatrix n n A)))
    (hconj : (u : Unitization ℂ (CStarMatrix n n A)) * (p : Unitization ℂ (CStarMatrix n n A)) *
      star (u : Unitization ℂ (CStarMatrix n n A)) = (q : Unitization ℂ (CStarMatrix n n A))) :
    p.MurrayVonNeumannEquiv q := by
  let B := CStarMatrix n n A
  let v : B := ((u : Unitization ℂ B) * (p : Unitization ℂ B)).snd
  have hv_inr : (v : Unitization ℂ B) = (u : Unitization ℂ B) * (p : Unitization ℂ B) :=
    Unitization.ext (by simp) rfl
  refine (murrayVonNeumannEquiv_iff_exists_conjTranspose_mul hp.isIdempotentElem).mpr ⟨v, ?_, ?_⟩
  · apply Unitization.inr_injective (R := ℂ)
    rw [← star_eq_conjTranspose, Unitization.inr_mul, Unitization.inr_star, hv_inr, star_mul,
      hp.inr.isSelfAdjoint.star_eq, mul_assoc, ← mul_assoc (star (u : Unitization ℂ B)),
      Unitary.coe_star_mul_self, one_mul, hp.inr.isIdempotentElem.eq]
  · apply Unitization.inr_injective (R := ℂ)
    rw [← star_eq_conjTranspose, Unitization.inr_mul, Unitization.inr_star, hv_inr, star_mul,
      hp.inr.isSelfAdjoint.star_eq, ← mul_assoc, mul_assoc (u : Unitization ℂ B),
      hp.inr.isIdempotentElem.eq, hconj]

/-- Two matrix star projections over a (possibly non-unital) C⋆-algebra at operator-norm distance
`< 1` are Murray–von Neumann equivalent. -/
theorem murrayVonNeumannEquiv_of_norm_sub_lt_one [NonUnitalCStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A]
    {p q : CStarMatrix n n A} (hp : IsStarProjection p) (hq : IsStarProjection q)
    (h : ‖p - q‖ < 1) :
    p.MurrayVonNeumannEquiv q := by
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
    p.MurrayVonNeumannEquiv q := by
  let : PartialOrder A := CStarAlgebra.spectralOrder A
  let : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
  have hp : IsStarProjection p := γ.source ▸ hγ 0
  obtain ⟨u, -, hconj⟩ :=
    IsStarProjection.exists_joined_one_unitary_conj_of_path
      (γ.map (Unitization.continuous_inr (𝕜 := ℂ))) fun t ↦ (hγ t).inr
  exact murrayVonNeumannEquiv_of_unitization_unitary_conj hp u hconj

/-- **Explicit `2 × 2` rotation path for Murray–von Neumann equivalent projections.** Given matrices
`p : CStarMatrix m m A`, `q : CStarMatrix n n A`, and `v : CStarMatrix n m A` over a (possibly
non-unital) C⋆-algebra `A`, this is the continuous path
`t ↦ fromBlocks (cos²(πt/2) • p) (cos(πt/2) sin(πt/2) • vᴴ)`
`      (cos(πt/2) sin(πt/2) • v) (sin²(πt/2) • q)`
from `fromBlocks p 0 0 0` to `fromBlocks 0 0 0 q`. When `v * vᴴ * v = v`, `vᴴ * v = p`, and
`v * vᴴ = q`, every point along this path is a star projection
(see `isStarProjection_stabilizedRotationPath`). -/
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
    rw [hfun]
    fun_prop
  source' := by simp
  target' := by simp

@[simp]
theorem stabilizedRotationPath_apply [NonUnitalCStarAlgebra A]
    (p : CStarMatrix m m A) (q : CStarMatrix n n A) (v : CStarMatrix n m A) (t : I) :
    stabilizedRotationPath p q v t =
      fromBlocks (Real.cos (π / 2 * t) ^ 2 • p)
        ((Real.cos (π / 2 * t) * Real.sin (π / 2 * t)) • v.conjTranspose)
        ((Real.cos (π / 2 * t) * Real.sin (π / 2 * t)) • v)
        (Real.sin (π / 2 * t) ^ 2 • q) :=
  (rfl)

/-- Every point along `stabilizedRotationPath p q v` is a star projection when `v` is a partial
isometry witnessing `p.MurrayVonNeumannEquiv q`. -/
theorem isStarProjection_stabilizedRotationPath [NonUnitalCStarAlgebra A]
    {p : CStarMatrix m m A} {q : CStarMatrix n n A} {v : CStarMatrix n m A}
    (hv : v * v.conjTranspose * v = v) (hv₁ : v.conjTranspose * v = p)
    (hv₂ : v * v.conjTranspose = q) (t : I) :
    IsStarProjection (stabilizedRotationPath p q v t) := by
  open scoped ComplexStarModule in
  have hp : IsStarProjection p := MurrayVonNeumannEquiv.isStarProjection_left ⟨v, hv, hv₁, hv₂⟩
  have hq : IsStarProjection q := MurrayVonNeumannEquiv.isStarProjection_right ⟨v, hv, hv₁, hv₂⟩
  have hvp : v * p = v := by rw [← hv₁, ← CStarMatrix.mul_assoc, hv]
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
  · rw [IsSelfAdjoint, fromBlocks_star]
    simp [hp.isSelfAdjoint.star_eq, hq.isSelfAdjoint.star_eq]

/-- Over a (possibly non-unital) C⋆-algebra, two matrix elements `p : CStarMatrix m m A` and
`q : CStarMatrix n n A` are Murray–von Neumann equivalent if and only if `fromBlocks p 0 0 0` and
`fromBlocks 0 0 0 q` are joined by a continuous path of star projections in
`CStarMatrix (m ⊕ n) (m ⊕ n) A`. -/
theorem murrayVonNeumannEquiv_iff_exists_path_fromBlocks_zero_right_left [NonUnitalCStarAlgebra A]
    {p : CStarMatrix m m A} {q : CStarMatrix n n A} :
    p.MurrayVonNeumannEquiv q ↔
      ∃ γ : Path (fromBlocks p 0 0 (0 : CStarMatrix n n A))
        (fromBlocks (0 : CStarMatrix m m A) 0 0 q), ∀ t, IsStarProjection (γ t) := by
  refine ⟨fun ⟨v, hv, hv₁, hv₂⟩ ↦ ⟨stabilizedRotationPath p q v,
    isStarProjection_stabilizedRotationPath hv hv₁ hv₂⟩, fun ⟨γ, hγ⟩ ↦ ?_⟩
  have hp : IsStarProjection p := (isStarProjection_fromBlocks_zero.mp (γ.source ▸ hγ 0)).1
  have hq : IsStarProjection q := (isStarProjection_fromBlocks_zero.mp (γ.target ▸ hγ 1)).2
  exact (murrayVonNeumannEquiv_fromBlocks_zero_right n hp).trans
    ((murrayVonNeumannEquiv_of_path γ hγ).trans
      (murrayVonNeumannEquiv_fromBlocks_zero_left m hq).symm)

/-- Over a unital C⋆-algebra, a star projection `p : CStarMatrix m m A` is Murray–von Neumann
equivalent to `q : CStarMatrix n n A` if and only if `fromBlocks p 0 0 0` and `fromBlocks 0 0 0 q`
are conjugate by a unitary in the identity path component of
`unitary (CStarMatrix (m ⊕ n) (m ⊕ n) A)`. -/
theorem murrayVonNeumannEquiv_iff_exists_joined_one_unitary_fromBlocks_zero_right_left
    [DecidableEq m] [DecidableEq n] [CStarAlgebra A]
    {p : CStarMatrix m m A} {q : CStarMatrix n n A}
    (hp : IsStarProjection p) :
    p.MurrayVonNeumannEquiv q ↔
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
joined by a continuous path of star projections in `CStarMatrix (n ⊕ n) (n ⊕ n) A`. -/
theorem murrayVonNeumannEquiv_iff_exists_path_fromBlocks_zero_right [NonUnitalCStarAlgebra A]
    {p q : CStarMatrix n n A} :
    p.MurrayVonNeumannEquiv q ↔
      ∃ γ : Path (fromBlocks p 0 0 (0 : CStarMatrix n n A))
        (fromBlocks q 0 0 (0 : CStarMatrix n n A)), ∀ t, IsStarProjection (γ t) := by
  refine ⟨fun h ↦ ?_, fun ⟨γ, hγ⟩ ↦ ?_⟩
  · have hqq : q.MurrayVonNeumannEquiv q := murrayVonNeumannEquiv_refl h.isStarProjection_right
    obtain ⟨γ₁, hγ₁⟩ := murrayVonNeumannEquiv_iff_exists_path_fromBlocks_zero_right_left.mp h
    obtain ⟨γ₂, hγ₂⟩ := murrayVonNeumannEquiv_iff_exists_path_fromBlocks_zero_right_left.mp hqq
    refine ⟨γ₁.trans γ₂.symm, fun t ↦ ?_⟩
    rw [Path.trans_apply]
    split_ifs <;> simp [hγ₁, hγ₂]
  · have hp : IsStarProjection p := (isStarProjection_fromBlocks_zero.mp (γ.source ▸ hγ 0)).1
    have hq : IsStarProjection q := (isStarProjection_fromBlocks_zero.mp (γ.target ▸ hγ 1)).1
    exact (murrayVonNeumannEquiv_fromBlocks_zero_right n hp).trans
      ((murrayVonNeumannEquiv_of_path γ hγ).trans
        (murrayVonNeumannEquiv_fromBlocks_zero_right n hq).symm)

/-- Over a unital C⋆-algebra, a star projection `p : CStarMatrix n n A` is Murray–von Neumann
equivalent to `q : CStarMatrix n n A` if and only if `fromBlocks p 0 0 0` and `fromBlocks q 0 0 0`
are conjugate by a unitary in the identity path component of
`unitary (CStarMatrix (n ⊕ n) (n ⊕ n) A)`. -/
theorem murrayVonNeumannEquiv_iff_exists_joined_one_unitary_fromBlocks_zero_right
    [DecidableEq n] [CStarAlgebra A]
    {p q : CStarMatrix n n A} (hp : IsStarProjection p) :
    p.MurrayVonNeumannEquiv q ↔
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
