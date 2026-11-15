/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Star.PartialIsometry
public import TauCeti.Analysis.CStarAlgebra.CStarMatrix.Block
public import TauCeti.Analysis.CStarAlgebra.Projection.Homotopy
import TauCeti.Data.Matrix.Block

/-!
# Murray–von Neumann equivalence and stabilized homotopy of matrix projections

Two projections `p ∈ CStarMatrix m m A` and `q ∈ CStarMatrix n n A`, possibly of different matrix
sizes and over a possibly non-unital `⋆`-algebra `A`, are **Murray–von Neumann equivalent** when
there exists a rectangular partial isometry `v ∈ CStarMatrix n m A` (`v * vᴴ * v = v`) with initial
projection `vᴴ * v = p` and final projection `v * vᴴ = q`. Over any C⋆-algebra (or any star-ordered
ring with proper star), the partial-isometry condition `v * vᴴ * v = v` is automatic as soon as
`vᴴ * v` is idempotent (`CStarMatrix.murrayVonNeumannEquiv_iff_of_isIdempotentElem`).

This file develops the algebraic, functorial, block-sum, and analytic properties of
`CStarMatrix.MurrayVonNeumannEquiv`, culminating in the equivalence between Murray–von Neumann
equivalence, stabilized unitary conjugacy in `U₀`, and stabilized projection homotopy over unital
C⋆-algebras:

* Equivalence relation (`murrayVonNeumannEquiv_refl`, `MurrayVonNeumannEquiv.symm`,
  `MurrayVonNeumannEquiv.trans`), non-degeneracy of zero (`murrayVonNeumannEquiv_zero_iff`), and
  functoriality under `MurrayVonNeumannEquiv.map`, `mapₙₐ`, `mapₐ`, and finite reindexing
  `reindexₐ` (for non-unital `A`).
* Block-diagonal monoid laws up to equivalence: corner padding
  (`murrayVonNeumannEquiv_fromBlocks_zero_right`, `murrayVonNeumannEquiv_fromBlocks_zero_left`),
  congruence (`MurrayVonNeumannEquiv.fromBlocks_zero`), commutativity
  (`murrayVonNeumannEquiv_fromBlocks_zero_comm`), associativity
  (`murrayVonNeumannEquiv_fromBlocks_zero_assoc`), and compatibility of orthogonal addition with
  block-diagonal sums (`murrayVonNeumannEquiv_fromBlocks_of_mul_eq_zero`).
* Stabilized self-adjoint unitary conjugacy (`stabilizedSymmUnitary`,
  `stabilizedSymmUnitary_mul_fromBlocks_mul_star`) via the `2 × 2` block involution
  `fromBlocks (1 - p) vᴴ v (1 - q)`.
* Equivalence with stabilized unitary conjugacy in `U₀` and stabilized projection homotopy over a
  unital C⋆-algebra (`murrayVonNeumannEquiv_iff_exists_joined_one_unitary`,
  `murrayVonNeumannEquiv_iff_exists_path_fromBlocks_zero_lr`,
  `murrayVonNeumannEquiv_iff_exists_path_fromBlocks_zero`, and
  `murrayVonNeumannEquiv_iff_exists_joined_one_unitary_fromBlocks_zero`).

## References

* B. Blackadar, *K-Theory for Operator Algebras*, 2nd ed., MSRI Publications 5, Cambridge
  University Press (1998), Chapter II, §4.6.
* M. Rørdam, F. Larsen, N. Laustsen, *An Introduction to K-Theory for C⋆-Algebras*, LMS Student
  Texts 49, Cambridge University Press (2000), §§2.1–2.2.
-/

public section

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

/-- Murray–von Neumann equivalence is symmetric, via the conjugate transpose of the witnessing
rectangular partial isometry. -/
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

/-- Murray–von Neumann equivalence is transitive: if `v` witnesses `p ∼ q` and `w` witnesses
`q ∼ r`, then `w * v` is a rectangular partial isometry witnessing `p ∼ r`. -/
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
  · rw [map_conjTranspose v f (map_star f), ← map_mul_of_nonUnitalRingHom f,
      ← map_mul_of_nonUnitalRingHom f, hv]
  · rw [map_conjTranspose v f (map_star f), ← map_mul_of_nonUnitalRingHom f, hv₁]
  · rw [map_conjTranspose v f (map_star f), ← map_mul_of_nonUnitalRingHom f, hv₂]

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
  · rw [reindexₗ_conjTranspose, hp_ct, ← reindexₗ_mul, hp.isIdempotentElem.eq]
    ext
    rfl
  · rw [reindexₗ_conjTranspose, hp_ct, ← reindexₗ_mul, hp.isIdempotentElem.eq]
    ext
    rfl

/-- Unitary conjugation in `CStarMatrix n n A` implies Murray–von Neumann equivalence. -/
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

end Algebraic

section BlockOperations

variable {l m m₁ m₂ n n₁ n₂ A : Type*}

/-- Padding a star projection `p` with a zero lower-right block preserves its Murray–von Neumann
class (`p ∼ diag(p, 0)`). -/
theorem murrayVonNeumannEquiv_fromBlocks_zero_right [Fintype m] [Fintype n]
    [NonUnitalSemiring A] [StarRing A]
    {p : CStarMatrix m m A} (hp : IsStarProjection p) :
    p.MurrayVonNeumannEquiv (fromBlocks p 0 0 (0 : CStarMatrix n n A)) := by
  let v : CStarMatrix (m ⊕ n) m A := ofMatrix (Sum.elim p 0)
  have hv_inl (i : m) (j : m) : v (.inl i) j = p i j := rfl
  have hv_inr (i : n) (j : m) : v (.inr i) j = 0 := rfl
  have hp_ct : p.conjTranspose = p := hp.isSelfAdjoint
  have hvv : v * v.conjTranspose = fromBlocks p 0 0 0 := by
    ext (i | i) (j | j)
    · rw [fromBlocks_apply₁₁, mul_apply]
      -- Identify `∑ k, v (.inl i) k * (vᴴ) k (.inl j)` with `(p * pᴴ) i j`.
      change (p * p.conjTranspose) i j = p i j
      rw [hp_ct, hp.isIdempotentElem.eq]
    · simp [mul_apply, hv_inl, hv_inr]
    · simp [mul_apply, hv_inl, hv_inr]
    · simp [mul_apply, hv_inr]
  refine ⟨v, ?_, ?_, hvv⟩
  · rw [hvv]
    ext (i | i) j
    · simp only [mul_apply, Fintype.sum_sum_type, fromBlocks_apply₁₁, fromBlocks_apply₁₂,
        hv_inl, hv_inr, zero_apply, zero_mul, Finset.sum_const_zero, add_zero]
      exact congrFun (congrFun hp.isIdempotentElem.eq i) j
    · simp [mul_apply, Fintype.sum_sum_type, hv_inr]
  · ext i j
    simp only [mul_apply, conjTranspose_apply, Fintype.sum_sum_type, hv_inl, hv_inr,
      star_zero, zero_mul, Finset.sum_const_zero, add_zero]
    -- Identify `∑ x, star (p x i) * p x j` with `(pᴴ * p) i j`.
    change (p.conjTranspose * p) i j = p i j
    rw [hp_ct, hp.isIdempotentElem.eq]

/-- Block-diagonal direct sum is commutative up to Murray–von Neumann equivalence. -/
theorem murrayVonNeumannEquiv_fromBlocks_zero_comm [Fintype m] [Fintype n]
    [NonUnitalSemiring A] [StarRing A]
    {p : CStarMatrix m m A} {q : CStarMatrix n n A}
    (hp : IsStarProjection p) (hq : IsStarProjection q) :
    (fromBlocks p 0 0 q).MurrayVonNeumannEquiv (fromBlocks q 0 0 p) := by
  have hproj : IsStarProjection (fromBlocks p 0 0 q) :=
    isStarProjection_fromBlocks_zero.mpr ⟨hp, hq⟩
  have heq : reindexₐ ℕ A (Equiv.sumComm m n) (fromBlocks p 0 0 q) = fromBlocks q 0 0 p := by
    rw [← reindexₗ_sumComm_fromBlocks (R := ℕ) p 0 0 q]
    ext i j
    rw [reindexₐ_apply, reindexₗ_apply]
  exact heq ▸ murrayVonNeumannEquiv_reindexₐ (R := ℕ) hproj (Equiv.sumComm m n)

/-- Padding a star projection `q` with a zero upper-left block preserves its Murray–von Neumann
class (`q ∼ diag(0, q)`). -/
theorem murrayVonNeumannEquiv_fromBlocks_zero_left (m : Type*) [Fintype m] [Fintype n]
    [NonUnitalSemiring A] [StarRing A]
    {q : CStarMatrix n n A} (hq : IsStarProjection q) :
    q.MurrayVonNeumannEquiv (fromBlocks (0 : CStarMatrix m m A) 0 0 q) :=
  (murrayVonNeumannEquiv_fromBlocks_zero_right (n := m) hq).trans
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
  have heq : reindexₐ ℕ A (Equiv.sumAssoc l m n) (fromBlocks (fromBlocks p 0 0 q) 0 0 r) =
      fromBlocks p 0 0 (fromBlocks q 0 0 r) := by
    rw [← reindexₗ_sumAssoc_fromBlocks_zero (R := ℕ)]
    ext i j
    rw [reindexₐ_apply, reindexₗ_apply]
  exact heq ▸ murrayVonNeumannEquiv_reindexₐ (R := ℕ) hproj (Equiv.sumAssoc l m n)

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

/-- If `p` and `q` are orthogonal star projections (`p * q = 0`) in `CStarMatrix m m A`, their
internal sum `p + q` is Murray–von Neumann equivalent to their block-diagonal direct sum
`fromBlocks p 0 0 q`. -/
theorem murrayVonNeumannEquiv_fromBlocks_of_mul_eq_zero [Fintype m]
    [NonUnitalSemiring A] [StarRing A]
    {p q : CStarMatrix m m A} (hp : IsStarProjection p) (hq : IsStarProjection q)
    (hpq : p * q = 0) :
    (p + q).MurrayVonNeumannEquiv (fromBlocks p 0 0 q) := by
  have hp_ct : p.conjTranspose = p := hp.isSelfAdjoint
  have hq_ct : q.conjTranspose = q := hq.isSelfAdjoint
  have hqp : q * p = 0 := by
    simpa only [conjTranspose_mul, hp_ct, hq_ct, conjTranspose_zero] using
      congrArg conjTranspose hpq
  let v : CStarMatrix (m ⊕ m) m A := ofMatrix (Sum.elim p q)
  have hv_inl (i j : m) : v (.inl i) j = p i j := rfl
  have hv_inr (i j : m) : v (.inr i) j = q i j := rfl
  have hvv : v * v.conjTranspose = fromBlocks p 0 0 q := by
    ext (i | i) (j | j)
    · rw [fromBlocks_apply₁₁, mul_apply]
      -- Evaluate the `(inl i, inl j)` entry as `(p * pᴴ) i j = p i j`.
      change (p * p.conjTranspose) i j = p i j
      rw [hp_ct, hp.isIdempotentElem.eq]
    · rw [fromBlocks_apply₁₂, mul_apply]
      -- Evaluate the `(inl i, inr j)` entry as `(p * qᴴ) i j = 0`.
      change (p * q.conjTranspose) i j = 0
      rw [hq_ct, hpq, zero_apply]
    · rw [fromBlocks_apply₂₁, mul_apply]
      -- Evaluate the `(inr i, inl j)` entry as `(q * pᴴ) i j = 0`.
      change (q * p.conjTranspose) i j = 0
      rw [hp_ct, hqp, zero_apply]
    · rw [fromBlocks_apply₂₂, mul_apply]
      -- Evaluate the `(inr i, inr j)` entry as `(q * qᴴ) i j = q i j`.
      change (q * q.conjTranspose) i j = q i j
      rw [hq_ct, hq.isIdempotentElem.eq]
  refine ⟨v, ?_, ?_, hvv⟩
  · rw [hvv]
    ext (i | i) j
    · simp only [mul_apply, Fintype.sum_sum_type, fromBlocks_apply₁₁, fromBlocks_apply₁₂,
        hv_inl, hv_inr, zero_apply, zero_mul, Finset.sum_const_zero, add_zero]
      exact congrFun (congrFun hp.isIdempotentElem.eq i) j
    · simp only [mul_apply, Fintype.sum_sum_type, fromBlocks_apply₂₁, fromBlocks_apply₂₂,
        hv_inl, hv_inr, zero_apply, zero_mul, Finset.sum_const_zero, zero_add]
      exact congrFun (congrFun hq.isIdempotentElem.eq i) j
  · ext i j
    simp only [mul_apply, conjTranspose_apply, Fintype.sum_sum_type, hv_inl, hv_inr, add_apply]
    -- Identify the two summands with `(pᴴ * p) i j` and `(qᴴ * q) i j`.
    change (p.conjTranspose * p) i j + (q.conjTranspose * q) i j = p i j + q i j
    rw [hp_ct, hq_ct, hp.isIdempotentElem.eq, hq.isIdempotentElem.eq]

end BlockOperations

section Stabilization

variable {m n A : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
  [Ring A] [StarRing A]

/-- Given a rectangular partial isometry `v : CStarMatrix n m A` with `v * vᴴ * v = v`,
`vᴴ * v = p`, and `v * vᴴ = q`, the `2 × 2` block matrix
`fromBlocks (1 - p) vᴴ v (1 - q)` is a self-adjoint unitary involution in
`CStarMatrix (m ⊕ n) (m ⊕ n) A` conjugating `diag(p, 0)` to `diag(0, q)`. -/
def stabilizedSymmUnitary {p : CStarMatrix m m A} {q : CStarMatrix n n A}
    {v : CStarMatrix n m A} (hv : v * v.conjTranspose * v = v)
    (hv₁ : v.conjTranspose * v = p) (hv₂ : v * v.conjTranspose = q) :
    unitary (CStarMatrix (m ⊕ n) (m ⊕ n) A) := by
  have hp : IsStarProjection p := MurrayVonNeumannEquiv.isStarProjection_left ⟨v, hv, hv₁, hv₂⟩
  have hq : IsStarProjection q := MurrayVonNeumannEquiv.isStarProjection_right ⟨v, hv, hv₁, hv₂⟩
  let w : CStarMatrix (m ⊕ n) (m ⊕ n) A := fromBlocks (1 - p) v.conjTranspose v (1 - q)
  have hw_sa : star w = w := by
    simp [w, hp.one_sub.isSelfAdjoint.star_eq, hq.one_sub.isSelfAdjoint.star_eq]
  have hvp : v * p = v := by rw [← hv₁, ← CStarMatrix.mul_assoc, hv]
  have hpv : p * v.conjTranspose = v.conjTranspose := by
    have := congrArg conjTranspose hvp
    rwa [conjTranspose_mul, ← star_eq_conjTranspose, hp.isSelfAdjoint.star_eq] at this
  have h1p : ofMatrix.symm (1 - p) = 1 - ofMatrix.symm p := rfl
  have h1q : ofMatrix.symm (1 - q) = 1 - ofMatrix.symm q := rfl
  have hww : w * w = 1 := by
    apply ofMatrix.symm.injective
    rw [ofMatrix_symm_mul, ofMatrix_symm_fromBlocks, h1p, h1q]
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
    IsSelfAdjoint (stabilizedSymmUnitary hv hv₁ hv₂ : CStarMatrix (m ⊕ n) (m ⊕ n) A) := by
  have hp : IsStarProjection p := MurrayVonNeumannEquiv.isStarProjection_left ⟨v, hv, hv₁, hv₂⟩
  have hq : IsStarProjection q := MurrayVonNeumannEquiv.isStarProjection_right ⟨v, hv, hv₁, hv₂⟩
  rw [IsSelfAdjoint, coe_stabilizedSymmUnitary]
  simp [hp.one_sub.isSelfAdjoint.star_eq, hq.one_sub.isSelfAdjoint.star_eq]

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
  have h1p : ofMatrix.symm (1 - p) = 1 - ofMatrix.symm p := rfl
  have h1q : ofMatrix.symm (1 - q) = 1 - ofMatrix.symm q := rfl
  apply ofMatrix.symm.injective
  rw [ofMatrix_symm_mul, ofMatrix_symm_mul, ofMatrix_symm_fromBlocks, ofMatrix_symm_fromBlocks,
    ofMatrix_symm_fromBlocks, h1p, h1q]
  exact Matrix.fromBlocks_one_sub_mul_fromBlocks_mul_fromBlocks_one_sub_of_mul_eq
    (congrArg ofMatrix.symm hv₁) (congrArg ofMatrix.symm hv₂) (congrArg ofMatrix.symm hvp)

/-- Two projections are Murray–von Neumann equivalent if and only if `diag(p, 0)` and `diag(0, q)`
are conjugate by a self-adjoint unitary in `CStarMatrix (m ⊕ n) (m ⊕ n) A`. -/
theorem murrayVonNeumannEquiv_iff_exists_isSelfAdjoint_unitary
    {p : CStarMatrix m m A} {q : CStarMatrix n n A}
    (hp : IsStarProjection p) (hq : IsStarProjection q) :
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
  have hmid : (fromBlocks p 0 0 (0 : CStarMatrix n n A)).MurrayVonNeumannEquiv
      (fromBlocks (0 : CStarMatrix m m A) 0 0 q) :=
    hconj ▸ murrayVonNeumannEquiv_star_right_conjugate hp0 u
  exact (murrayVonNeumannEquiv_fromBlocks_zero_right hp).trans
    (hmid.trans (murrayVonNeumannEquiv_fromBlocks_zero_left m hq).symm)

end Stabilization

section CStarAlgebra

variable {m n A : Type*} [Fintype m] [Fintype n]

/-- Over a non-unital C⋆-algebra, a rectangular matrix `v` witnesses `p.MurrayVonNeumannEquiv q`
for an idempotent `p` if and only if `vᴴ * v = p` and `v * vᴴ = q`. -/
theorem murrayVonNeumannEquiv_iff_exists_conjTranspose_mul [NonUnitalCStarAlgebra A]
    {p : CStarMatrix m m A} {q : CStarMatrix n n A} (hp : IsIdempotentElem p) :
    p.MurrayVonNeumannEquiv q ↔
      ∃ v : CStarMatrix n m A, v.conjTranspose * v = p ∧ v * v.conjTranspose = q := by
  let : PartialOrder A := CStarAlgebra.spectralOrder A
  let : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
  exact murrayVonNeumannEquiv_iff_of_isIdempotentElem hp

/-- Two matrix star projections over a unital C⋆-algebra at operator-norm distance `< 1` are
Murray–von Neumann equivalent. -/
theorem murrayVonNeumannEquiv_of_norm_sub_lt_one [CStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A]
    {p q : CStarMatrix n n A} (hp : IsStarProjection p) (hq : IsStarProjection q)
    (h : ‖p - q‖ < 1) :
    p.MurrayVonNeumannEquiv q := by
  classical
  obtain ⟨u, hconj, -⟩ := hp.exists_unitary_conj_of_norm_sub_lt_one hq h
  exact hconj ▸ murrayVonNeumannEquiv_star_right_conjugate hp u

/-- Any norm-continuous path of star projections in `CStarMatrix n n A` over a unital C⋆-algebra
has Murray–von Neumann equivalent endpoints. -/
theorem murrayVonNeumannEquiv_of_path [CStarAlgebra A]
    {p q : CStarMatrix n n A} (γ : Path p q) (hγ : ∀ t, IsStarProjection (γ t)) :
    p.MurrayVonNeumannEquiv q := by
  classical
  let : PartialOrder A := CStarAlgebra.spectralOrder A
  let : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
  have hp : IsStarProjection p := γ.source ▸ hγ 0
  obtain ⟨u, -, hconj⟩ := IsStarProjection.exists_joined_one_unitary_conj_of_path γ hγ
  exact hconj ▸ murrayVonNeumannEquiv_star_right_conjugate hp u

/-- **Three equivalences of matrix projections (rectangular sizes).** Over a unital C⋆-algebra, two
star projections `p : CStarMatrix m m A` and `q : CStarMatrix n n A` are Murray–von Neumann
equivalent if and only if `fromBlocks p 0 0 0` and `fromBlocks 0 0 0 q` are joined by a continuous
path of star projections in `CStarMatrix (m ⊕ n) (m ⊕ n) A`. -/
theorem murrayVonNeumannEquiv_iff_exists_path_fromBlocks_zero_lr [CStarAlgebra A]
    {p : CStarMatrix m m A} {q : CStarMatrix n n A}
    (hp : IsStarProjection p) (hq : IsStarProjection q) :
    p.MurrayVonNeumannEquiv q ↔
      ∃ γ : Path (fromBlocks p 0 0 (0 : CStarMatrix n n A))
        (fromBlocks (0 : CStarMatrix m m A) 0 0 q), ∀ t, IsStarProjection (γ t) := by
  classical
  let : PartialOrder A := CStarAlgebra.spectralOrder A
  let : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
  have hp0 : IsStarProjection (fromBlocks p 0 0 (0 : CStarMatrix n n A)) :=
    isStarProjection_fromBlocks_zero.mpr ⟨hp, .zero _⟩
  refine ⟨fun h ↦ ?_, fun ⟨γ, hγ⟩ ↦ ?_⟩
  · obtain ⟨u, hu_sa, hconj⟩ :=
      (murrayVonNeumannEquiv_iff_exists_isSelfAdjoint_unitary hp hq).mp h
    obtain ⟨γ, hγ⟩ := hp0.exists_path_of_isSelfAdjoint_unitary u hu_sa
    exact ⟨γ.cast rfl hconj.symm, fun t ↦ by simpa using hγ t⟩
  · have hmid := murrayVonNeumannEquiv_of_path γ hγ
    exact (murrayVonNeumannEquiv_fromBlocks_zero_right hp).trans
      (hmid.trans (murrayVonNeumannEquiv_fromBlocks_zero_left m hq).symm)

/-- Over a unital C⋆-algebra, two star projections `p : CStarMatrix m m A` and
`q : CStarMatrix n n A` are Murray–von Neumann equivalent if and only if `fromBlocks p 0 0 0` and
`fromBlocks 0 0 0 q` are conjugate by a unitary in the identity path component of
`unitary (CStarMatrix (m ⊕ n) (m ⊕ n) A)`. -/
theorem murrayVonNeumannEquiv_iff_exists_joined_one_unitary
    [DecidableEq m] [DecidableEq n] [CStarAlgebra A]
    {p : CStarMatrix m m A} {q : CStarMatrix n n A}
    (hp : IsStarProjection p) (hq : IsStarProjection q) :
    p.MurrayVonNeumannEquiv q ↔
      ∃ u : unitary (CStarMatrix (m ⊕ n) (m ⊕ n) A), Joined 1 u ∧
        (u : CStarMatrix (m ⊕ n) (m ⊕ n) A) * fromBlocks p 0 0 0 *
          star (u : CStarMatrix (m ⊕ n) (m ⊕ n) A) = fromBlocks 0 0 0 q := by
  let : PartialOrder A := CStarAlgebra.spectralOrder A
  let : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
  have hp0 : IsStarProjection (fromBlocks p 0 0 (0 : CStarMatrix n n A)) :=
    isStarProjection_fromBlocks_zero.mpr ⟨hp, .zero _⟩
  rw [murrayVonNeumannEquiv_iff_exists_path_fromBlocks_zero_lr hp hq,
    hp0.exists_path_iff_exists_joined_one_unitary_conj]

/-- **Three equivalences of matrix projections (doubled matrix size).** Over a unital C⋆-algebra,
two star projections `p, q : CStarMatrix n n A` are Murray–von Neumann equivalent if and only if
`fromBlocks p 0 0 0` and `fromBlocks q 0 0 0` are joined by a continuous path of star projections
in `CStarMatrix (n ⊕ n) (n ⊕ n) A`. -/
theorem murrayVonNeumannEquiv_iff_exists_path_fromBlocks_zero [CStarAlgebra A]
    {p q : CStarMatrix n n A} (hp : IsStarProjection p) (hq : IsStarProjection q) :
    p.MurrayVonNeumannEquiv q ↔
      ∃ γ : Path (fromBlocks p 0 0 (0 : CStarMatrix n n A))
        (fromBlocks q 0 0 (0 : CStarMatrix n n A)), ∀ t, IsStarProjection (γ t) := by
  classical
  let : PartialOrder A := CStarAlgebra.spectralOrder A
  let : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
  refine ⟨fun h ↦ ?_, fun ⟨γ, hγ⟩ ↦ ?_⟩
  · obtain ⟨γ₁, hγ₁⟩ := (murrayVonNeumannEquiv_iff_exists_path_fromBlocks_zero_lr hp hq).mp h
    let σ : Equiv.Perm (n ⊕ n) := Equiv.sumComm n n
    have hσ_sa : IsSelfAdjoint (permUnitary A σ : CStarMatrix (n ⊕ n) (n ⊕ n) A) := by
      rw [IsSelfAdjoint, coe_permUnitary, star_eq_conjTranspose, conjTranspose_permMatrix]
      rfl
    have h0q : IsStarProjection (fromBlocks (0 : CStarMatrix n n A) 0 0 q) :=
      isStarProjection_fromBlocks_zero.mpr ⟨.zero _, hq⟩
    have hconj : (permUnitary A σ : CStarMatrix (n ⊕ n) (n ⊕ n) A) *
        fromBlocks (0 : CStarMatrix n n A) 0 0 q *
        star (permUnitary A σ : CStarMatrix (n ⊕ n) (n ⊕ n) A) =
        fromBlocks q 0 0 (0 : CStarMatrix n n A) := by
      rw [permUnitary_mul_mul_star (R := ℕ)]
      dsimp only [σ]
      rw [← reindexₗ_sumComm_fromBlocks (R := ℕ) 0 0 0 q]
      ext i j
      rw [reindexₐ_apply, reindexₗ_apply]
    obtain ⟨γ₂, hγ₂⟩ := h0q.exists_path_of_isSelfAdjoint_unitary (permUnitary A σ) hσ_sa
    refine ⟨γ₁.trans (γ₂.cast rfl hconj.symm), fun t ↦ ?_⟩
    rw [Path.trans_apply]
    split_ifs <;> simp [hγ₁, hγ₂]
  · have hmid := murrayVonNeumannEquiv_of_path γ hγ
    exact (murrayVonNeumannEquiv_fromBlocks_zero_right hp).trans
      (hmid.trans (murrayVonNeumannEquiv_fromBlocks_zero_right hq).symm)

/-- Over a unital C⋆-algebra, two star projections `p, q : CStarMatrix n n A` are Murray–von
Neumann equivalent if and only if `fromBlocks p 0 0 0` and `fromBlocks q 0 0 0` are conjugate by a
unitary in the identity path component of `unitary (CStarMatrix (n ⊕ n) (n ⊕ n) A)`. -/
theorem murrayVonNeumannEquiv_iff_exists_joined_one_unitary_fromBlocks_zero
    [DecidableEq n] [CStarAlgebra A]
    {p q : CStarMatrix n n A} (hp : IsStarProjection p) (hq : IsStarProjection q) :
    p.MurrayVonNeumannEquiv q ↔
      ∃ u : unitary (CStarMatrix (n ⊕ n) (n ⊕ n) A), Joined 1 u ∧
        (u : CStarMatrix (n ⊕ n) (n ⊕ n) A) * fromBlocks p 0 0 0 *
          star (u : CStarMatrix (n ⊕ n) (n ⊕ n) A) = fromBlocks q 0 0 0 := by
  let : PartialOrder A := CStarAlgebra.spectralOrder A
  let : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
  have hp0 : IsStarProjection (fromBlocks p 0 0 (0 : CStarMatrix n n A)) :=
    isStarProjection_fromBlocks_zero.mpr ⟨hp, .zero _⟩
  rw [murrayVonNeumannEquiv_iff_exists_path_fromBlocks_zero hp hq,
    hp0.exists_path_iff_exists_joined_one_unitary_conj]

end CStarAlgebra

end CStarMatrix
