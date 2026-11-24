/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Star.PartialIsometry
public import TauCeti.Analysis.CStarAlgebra.CStarMatrix.Block
import TauCeti.Analysis.CStarAlgebra.Basic

/-!
# Rectangular partial isometries on `CStarMatrix`

Rectangular partial isometries (`v * v.conjTranspose * v = v`) on `CStarMatrix m n A`,
characterized via initial and final star projections, proper-star idempotency criteria,
compatibility with `blockSum`, `fromRows`, `reindexₗ`, `reindexₐ`, `map`, and `amplify`, and
C⋆-algebra operator-norm bounds (`‖v‖ ≤ 1`, and `‖v‖ = 1` when `v ≠ 0`).

## Main definitions and statements

* `CStarMatrix.IsPartialIsometry`: predicate `v * v.conjTranspose * v = v`.
* `CStarMatrix.isPartialIsometry_iff_starMul`: coincidence with `TauCeti.IsPartialIsometry` on
  square matrices.
* `CStarMatrix.IsPartialIsometry.isStarProjection_conjTranspose_mul_self`,
  `CStarMatrix.IsPartialIsometry.isStarProjection_mul_conjTranspose_self`: initial and final
  projections of a rectangular partial isometry.
* `CStarMatrix.IsPartialIsometry.of_conjTranspose_mul_self_eq_one`,
  `CStarMatrix.IsPartialIsometry.of_mul_conjTranspose_self_eq_one`,
  `CStarMatrix.IsPartialIsometry.of_mem_unitary`: isometries, coisometries, and unitaries are
  partial isometries.
* `CStarMatrix.isPartialIsometry_iff_isStarProjection_conjTranspose_mul_self`,
  `CStarMatrix.isPartialIsometry_iff_isStarProjection_mul_conjTranspose_self`: proper-star
  characterizations.
* `CStarMatrix.IsPartialIsometry.norm_le_one`, `CStarMatrix.IsPartialIsometry.norm_eq_one`:
  operator-norm bounds over a C⋆-algebra.

## References

* B. Blackadar, *K-Theory for Operator Algebras*, 2nd ed., §4.6 and §5.1.
-/

public section

namespace CStarMatrix
variable {k l m n o R A B F : Type*}

section
variable [Fintype l] [Fintype m] [Fintype n] [Fintype o]
section
variable [Mul A] [AddCommMonoid A] [Star A]
/-- `v : CStarMatrix m n A` is a **partial isometry** when `v * v.conjTranspose * v = v`. -/
def IsPartialIsometry (v : CStarMatrix m n A) : Prop := v * v.conjTranspose * v = v
theorem isPartialIsometry_iff {v : CStarMatrix m n A} :
    v.IsPartialIsometry ↔ v * v.conjTranspose * v = v := Iff.rfl
theorem IsPartialIsometry.mul_conjTranspose_mul_self {v : CStarMatrix m n A}
    (hv : v.IsPartialIsometry) : v * v.conjTranspose * v = v := hv
/-- Square `CStarMatrix.IsPartialIsometry` coincides with `TauCeti.IsPartialIsometry`. -/
theorem isPartialIsometry_iff_starMul {v : CStarMatrix n n A} :
    v.IsPartialIsometry ↔ TauCeti.IsPartialIsometry v := by
  rw [isPartialIsometry_iff, TauCeti.isPartialIsometry_iff, ← star_eq_conjTranspose]
end
namespace IsPartialIsometry
/-- Right-associated partial-isometry identity `v * (v.conjTranspose * v) = v`. -/
theorem mul_conjTranspose_mul_self' [NonUnitalSemiring A] [Star A] {v : CStarMatrix m n A}
    (hv : v.IsPartialIsometry) : v * (v.conjTranspose * v) = v := by
  rw [← mul_assoc_rectangular, hv.mul_conjTranspose_mul_self]
/-- Right-multiplying a rectangular partial isometry by its initial projection fixes `v`. -/
theorem mul_eq_self_of_conjTranspose_mul_self_eq [NonUnitalSemiring A] [Star A]
    {v : CStarMatrix n m A} {p : CStarMatrix m m A} (hv : v.IsPartialIsometry)
    (hp : v.conjTranspose * v = p) : v * p = v := by rw [← hp, hv.mul_conjTranspose_mul_self']
/-- Left-multiplying a rectangular partial isometry by its final projection fixes `v`. -/
theorem mul_eq_self_of_mul_conjTranspose_self_eq [Mul A] [AddCommMonoid A] [Star A]
    {v : CStarMatrix n m A} {q : CStarMatrix n n A} (hv : v.IsPartialIsometry)
    (hq : v * v.conjTranspose = q) : q * v = v := by rw [← hq, hv.mul_conjTranspose_mul_self]
@[simp] protected theorem zero [NonUnitalNonAssocSemiring A] [Star A] :
    (0 : CStarMatrix m n A).IsPartialIsometry := by simp [isPartialIsometry_iff]
section StarRing
variable [NonUnitalSemiring A] [StarRing A] {v : CStarMatrix m n A} (hv : v.IsPartialIsometry)
include hv
/-- The conjugate transpose of a rectangular partial isometry is a partial isometry. -/
protected theorem conjTranspose : v.conjTranspose.IsPartialIsometry := by
  rw [isPartialIsometry_iff, conjTranspose_conjTranspose, mul_assoc_rectangular]
  simpa only [conjTranspose_mul, conjTranspose_conjTranspose] using
    congrArg CStarMatrix.conjTranspose hv.mul_conjTranspose_mul_self
/-- Adjoint partial-isometry identity `v.conjTranspose * v * v.conjTranspose = v.conjTranspose`. -/
theorem conjTranspose_mul_self_mul_conjTranspose :
    v.conjTranspose * v * v.conjTranspose = v.conjTranspose := by
  simpa using hv.conjTranspose.mul_conjTranspose_mul_self
/-- Adjoint identity `v.conjTranspose * (v * v.conjTranspose) = v.conjTranspose`. -/
theorem conjTranspose_mul_self_mul_conjTranspose' :
    v.conjTranspose * (v * v.conjTranspose) = v.conjTranspose := by
  rw [← mul_assoc_rectangular, hv.conjTranspose_mul_self_mul_conjTranspose]
/-- The initial projection `v.conjTranspose * v` of a partial isometry is a star projection. -/
theorem isStarProjection_conjTranspose_mul_self : IsStarProjection (v.conjTranspose * v) :=
  ⟨by rw [IsIdempotentElem, mul_assoc_rectangular, ← mul_assoc_rectangular v, hv],
   by rw [isSelfAdjoint_iff, star_eq_conjTranspose, conjTranspose_mul, conjTranspose_conjTranspose]⟩
/-- The final projection `v * v.conjTranspose` of a partial isometry is a star projection. -/
theorem isStarProjection_mul_conjTranspose_self : IsStarProjection (v * v.conjTranspose) := by
  simpa using hv.conjTranspose.isStarProjection_conjTranspose_mul_self
/-- Left-multiplying `v.conjTranspose` by the initial projection of `v` fixes `v.conjTranspose`. -/
theorem mul_conjTranspose_eq_of_conjTranspose_mul_self_eq {p : CStarMatrix n n A}
    (hp : v.conjTranspose * v = p) : p * v.conjTranspose = v.conjTranspose := by
  rw [← hp, hv.conjTranspose_mul_self_mul_conjTranspose]
/-- Right-multiplying `v.conjTranspose` by the final projection of `v` fixes `v.conjTranspose`. -/
theorem conjTranspose_mul_eq_of_mul_conjTranspose_self_eq {q : CStarMatrix m m A}
    (hq : v * v.conjTranspose = q) : v.conjTranspose * q = v.conjTranspose := by
  rw [← hq, hv.conjTranspose_mul_self_mul_conjTranspose']
end StarRing
@[simp] protected theorem one [DecidableEq n] [NonAssocSemiring A] [StarRing A] :
    (1 : CStarMatrix n n A).IsPartialIsometry := by
  rw [isPartialIsometry_iff, conjTranspose_one, CStarMatrix.mul_one, CStarMatrix.mul_one]
theorem _root_.IsStarProjection.cstarMatrix_isPartialIsometry [Mul A] [AddCommMonoid A] [Star A]
    {p : CStarMatrix n n A} (hp : IsStarProjection p) : p.IsPartialIsometry :=
  isPartialIsometry_iff_starMul.mpr hp.isPartialIsometry
/-- Any rectangular isometry (`uᴴ * u = 1`) is a partial isometry. -/
theorem of_conjTranspose_mul_self_eq_one [DecidableEq n] [Semiring A] [Star A]
    {u : CStarMatrix m n A} (hu : u.conjTranspose * u = 1) : u.IsPartialIsometry := by
  rw [isPartialIsometry_iff, mul_assoc_rectangular, hu, CStarMatrix.mul_one]
/-- Any rectangular coisometry (`u * uᴴ = 1`) is a partial isometry. -/
theorem of_mul_conjTranspose_self_eq_one [DecidableEq m] [NonAssocSemiring A] [Star A]
    {u : CStarMatrix m n A} (hu : u * u.conjTranspose = 1) : u.IsPartialIsometry := by
  rw [isPartialIsometry_iff, hu, CStarMatrix.one_mul]
theorem of_mem_unitary [DecidableEq n] [Semiring A] [StarRing A] {u : CStarMatrix n n A}
    (hu : u ∈ unitary (CStarMatrix n n A)) : u.IsPartialIsometry :=
  of_conjTranspose_mul_self_eq_one
    (by simpa [star_eq_conjTranspose] using (Unitary.mem_iff.mp hu).1)
section ProperStar
variable [NonUnitalRing A] [StarRing A] [PartialOrder A] [StarOrderedRing A] [IsProperStar A]
  {v : CStarMatrix m n A}
/-- Over a proper-star ordered ring, `v` is a partial isometry if `vᴴ * v` is idempotent. -/
theorem of_isIdempotentElem_conjTranspose_mul_self (h : IsIdempotentElem (v.conjTranspose * v)) :
    v.IsPartialIsometry := by rw [isPartialIsometry_iff, mul_assoc_rectangular,
  CStarMatrix.mul_eq_self_of_conjTranspose_mul_eq v h rfl]
/-- Over a proper-star ordered ring, `v` is a partial isometry if `v * vᴴ` is idempotent. -/
theorem of_isIdempotentElem_mul_conjTranspose_self (h : IsIdempotentElem (v * v.conjTranspose)) :
    v.IsPartialIsometry := by
  simpa only [conjTranspose_conjTranspose] using (of_isIdempotentElem_conjTranspose_mul_self
    (v := v.conjTranspose) (by rwa [conjTranspose_conjTranspose])).conjTranspose
end ProperStar
protected theorem reindexₗ [Semiring R] [AddCommMonoid A] [Mul A] [Module R A] [Star A]
    (eₘ : m ≃ l) (eₙ : n ≃ o) {v : CStarMatrix m n A} (hv : v.IsPartialIsometry) :
    (CStarMatrix.reindexₗ R A eₘ eₙ v).IsPartialIsometry := by
  simp [isPartialIsometry_iff, hv.mul_conjTranspose_mul_self]
protected theorem reindexₐ [Semiring R] [AddCommMonoid A] [Mul A] [Module R A] [Star A]
    (e : m ≃ n) {v : CStarMatrix m m A} (hv : v.IsPartialIsometry) :
    (CStarMatrix.reindexₐ R A e v).IsPartialIsometry :=
  reindexₗ_self_eq_reindexₐ (R := R) e v ▸ hv.reindexₗ (R := R) e e
protected theorem map [NonUnitalNonAssocSemiring A] [Star A] [NonUnitalNonAssocSemiring B] [Star B]
    [FunLike F A B] [NonUnitalRingHomClass F A B] [StarHomClass F A B] (φ : F)
    {v : CStarMatrix m n A} (hv : v.IsPartialIsometry) : (v.map φ).IsPartialIsometry := by
  rw [isPartialIsometry_iff, ← map_conjTranspose, ← map_mul, ← map_mul, hv]
protected theorem amplify (k : Type*) [Fintype k] [DecidableEq k] [NonUnitalNonAssocSemiring A]
    [StarAddMonoid A] {v : CStarMatrix m n A} (hv : v.IsPartialIsometry) :
    (CStarMatrix.amplify k v).IsPartialIsometry := by
  simp [isPartialIsometry_iff, hv.mul_conjTranspose_mul_self]
end IsPartialIsometry
end

/-- Vertical row stack `fromRows p₁ p₂` of two orthogonal star projections is a partial isometry. -/
theorem _root_.IsStarProjection.isPartialIsometry_fromRows_of_mul_eq_zero [Fintype n]
    [NonUnitalNonAssocSemiring A] [StarRing A] {p₁ p₂ : CStarMatrix n n A}
    (hp₁ : IsStarProjection p₁) (hp₂ : IsStarProjection p₂) (h₁₂ : p₁ * p₂ = 0) :
    (fromRows p₁ p₂).IsPartialIsometry := by
  rw [isPartialIsometry_iff, hp₁.fromRows_mul_conjTranspose_fromRows_eq_blockSum hp₂ h₁₂,
    blockSum_mul_fromRows, hp₁.isIdempotentElem.eq, hp₂.isIdempotentElem.eq]
/-- If `uᴴ * u` acts as the identity on the range of a star projection `p`, then `u * p` is a
partial isometry. -/
theorem IsPartialIsometry.mul_of_conjTranspose_mul_self_mul_eq_of_isStarProjection
    [Fintype m] [Fintype n] [NonUnitalSemiring A] [StarRing A] {p : CStarMatrix n n A}
    {u : CStarMatrix m n A} (hu : u.conjTranspose * u * p = p) (hp : IsStarProjection p) :
    (u * p).IsPartialIsometry := by
  rw [isPartialIsometry_iff, mul_assoc_rectangular,
    hp.conjTranspose_mul_self_mul_of_conjTranspose_mul_self_mul_eq hu, mul_assoc_rectangular,
    hp.isIdempotentElem.eq]
/-- Left-multiplying a star projection `p` by an isometry `u` yields a partial isometry. -/
theorem IsPartialIsometry.mul_of_conjTranspose_mul_self_eq_one_of_isStarProjection
    [Fintype m] [Fintype n] [DecidableEq n] [Semiring A] [StarRing A] {p : CStarMatrix n n A}
    {u : CStarMatrix m n A} (hu : u.conjTranspose * u = 1) (hp : IsStarProjection p) :
    (u * p).IsPartialIsometry :=
  mul_of_conjTranspose_mul_self_mul_eq_of_isStarProjection (by rw [hu, CStarMatrix.one_mul]) hp

section
variable [Fintype k] [Fintype l] [Fintype m] [Fintype n] [Fintype o]
@[simp] theorem isPartialIsometry_conjTranspose_iff [NonUnitalSemiring A] [StarRing A]
    {v : CStarMatrix m n A} : v.conjTranspose.IsPartialIsometry ↔ v.IsPartialIsometry :=
  ⟨fun h => by simpa using h.conjTranspose, IsPartialIsometry.conjTranspose⟩
@[simp] theorem isPartialIsometry_blockSum_iff [NonUnitalNonAssocSemiring A] [StarAddMonoid A]
    {v : CStarMatrix m l A} {w : CStarMatrix o n A} :
    (blockSum v w).IsPartialIsometry ↔ v.IsPartialIsometry ∧ w.IsPartialIsometry := by
  simp only [isPartialIsometry_iff, blockSum_conjTranspose, blockSum_mul, blockSum_inj]
protected theorem IsPartialIsometry.blockSum [NonUnitalNonAssocSemiring A] [StarAddMonoid A]
    {v : CStarMatrix m l A} {w : CStarMatrix o n A} (hv : v.IsPartialIsometry)
    (hw : w.IsPartialIsometry) : (CStarMatrix.blockSum v w).IsPartialIsometry :=
  isPartialIsometry_blockSum_iff.mpr ⟨hv, hw⟩
@[simp] theorem isPartialIsometry_reindexₗ_iff [Semiring R] [AddCommMonoid A] [Mul A] [Module R A]
    [Star A] (eₘ : m ≃ l) (eₙ : n ≃ o) {v : CStarMatrix m n A} :
    (reindexₗ R A eₘ eₙ v).IsPartialIsometry ↔ v.IsPartialIsometry :=
  ⟨fun h => by simpa [reindexₗ_symm] using h.reindexₗ (R := R) eₘ.symm eₙ.symm, .reindexₗ eₘ eₙ⟩
@[simp] theorem isPartialIsometry_reindexₐ_iff [Semiring R] [AddCommMonoid A] [Mul A] [Module R A]
    [Star A] (e : m ≃ n) {v : CStarMatrix m m A} :
    (reindexₐ R A e v).IsPartialIsometry ↔ v.IsPartialIsometry :=
  ⟨fun h => by simpa [reindexₐ_symm] using h.reindexₐ (R := R) e.symm, .reindexₐ e⟩
@[simp] theorem isPartialIsometry_amplify_iff [DecidableEq k] [Nonempty k]
    [NonUnitalNonAssocSemiring A] [StarAddMonoid A] {v : CStarMatrix m n A} :
    (amplify k v).IsPartialIsometry ↔ v.IsPartialIsometry := by
  simp only [isPartialIsometry_iff, amplify_conjTranspose, amplify_mul, amplify_inj]
section
variable [NonUnitalRing A] [StarRing A] [PartialOrder A] [StarOrderedRing A] [IsProperStar A]
  {v : CStarMatrix m n A}
/-- Over a proper-star ordered ring, `v` is a partial isometry iff its initial product `vᴴ * v`
is idempotent. -/
theorem isPartialIsometry_iff_isIdempotentElem_conjTranspose_mul_self :
    v.IsPartialIsometry ↔ IsIdempotentElem (v.conjTranspose * v) :=
  ⟨fun hv => hv.isStarProjection_conjTranspose_mul_self.isIdempotentElem,
    .of_isIdempotentElem_conjTranspose_mul_self⟩
/-- Over a proper-star ordered ring, `v` is a partial isometry iff its final product `v * vᴴ`
is idempotent. -/
theorem isPartialIsometry_iff_isIdempotentElem_mul_conjTranspose_self :
    v.IsPartialIsometry ↔ IsIdempotentElem (v * v.conjTranspose) :=
  ⟨fun hv => hv.isStarProjection_mul_conjTranspose_self.isIdempotentElem,
    .of_isIdempotentElem_mul_conjTranspose_self⟩
/-- Over a proper-star ordered ring, `v` is a partial isometry iff its initial product `vᴴ * v`
is a star projection. -/
theorem isPartialIsometry_iff_isStarProjection_conjTranspose_mul_self :
    v.IsPartialIsometry ↔ IsStarProjection (v.conjTranspose * v) :=
  ⟨IsPartialIsometry.isStarProjection_conjTranspose_mul_self,
    fun h => .of_isIdempotentElem_conjTranspose_mul_self h.isIdempotentElem⟩
/-- Over a proper-star ordered ring, `v` is a partial isometry iff its final product `v * vᴴ`
is a star projection. -/
theorem isPartialIsometry_iff_isStarProjection_mul_conjTranspose_self :
    v.IsPartialIsometry ↔ IsStarProjection (v * v.conjTranspose) := by
  rw [← isPartialIsometry_conjTranspose_iff,
    isPartialIsometry_iff_isStarProjection_conjTranspose_mul_self, conjTranspose_conjTranspose]
end
section
variable [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A] {v : CStarMatrix m n A}
/-- Every rectangular partial isometry over a C⋆-algebra is a contraction (`‖v‖ ≤ 1`). -/
theorem IsPartialIsometry.norm_le_one (hv : v.IsPartialIsometry) : ‖v‖ ≤ 1 :=
  (sq_le_sq₀ (norm_nonneg v) zero_le_one).mp <| by
    simpa [norm_conjTranspose_mul_self] using
      IsStarProjection.norm_le _ hv.isStarProjection_conjTranspose_mul_self
/-- Every nonzero rectangular partial isometry over a C⋆-algebra has norm `1`. -/
theorem IsPartialIsometry.norm_eq_one (hv : v.IsPartialIsometry) (hv0 : v ≠ 0) : ‖v‖ = 1 :=
  (sq_eq_sq₀ (norm_nonneg v) zero_le_one).mp <| by
    rw [one_pow, ← norm_conjTranspose_mul_self]
    exact hv.isStarProjection_conjTranspose_mul_self.norm_eq_one
      (mt conjTranspose_mul_self_eq_zero.mp hv0)
end
end

end CStarMatrix
