/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Unitization
public import Mathlib.Analysis.CStarAlgebra.Unitary.Connected
public import TauCeti.Algebra.Star.PartialIsometry
public import TauCeti.Analysis.CStarAlgebra.CStarMatrix.Block
public import TauCeti.Analysis.CStarAlgebra.Exponential
public import TauCeti.Analysis.CStarAlgebra.Projection.Equivalence
public import TauCeti.LinearAlgebra.Matrix.MurrayVonNeumann
import TauCeti.Analysis.CStarAlgebra.Basic
import TauCeti.Analysis.CStarAlgebra.Unitary.Connected
import TauCeti.Data.Matrix.Block
import TauCeti.LinearAlgebra.Matrix.PartialIsometry

/-!
# Rectangular partial isometries and stabilized Murray–von Neumann paths on `CStarMatrix`

Rectangular partial isometries (`v * vᴴ * v = v`) and extensions of Murray–von Neumann
equivalence (`TauCeti.Analysis.CStarAlgebra.Projection.Equivalence`) over a (possibly non-unital)
C⋆-algebra `A`: proper-star characterizations, compatibility with `blockSum`, `add_of_mul_eq_zero`,
`amplify`, `IsStarProjection.murrayVonNeumannEquiv_reindexₐ`, rectangular unitization descent,
the self-adjoint unitary `stabilizedConjUnitary` sending `blockSum p 0` to `blockSum 0 q`, the
exponential unitary conjugation formula `expUnitary_conj_blockSum_eq_stabilizedProjRot` over
unital `A`, and the unit-free projection path `stabilizedProjPath`.

## Main definitions and statements

* `CStarMatrix.IsPartialIsometry`, `IsPartialIsometry.murrayVonNeumannEquiv`,
  `MurrayVonNeumannEquiv.exists_isPartialIsometry`,
  `murrayVonNeumannEquiv_iff_exists_isPartialIsometry`,
  `isPartialIsometry_iff_isStarProjection_conjTranspose_mul_self`,
  `murrayVonNeumannEquiv_iff_exists_mul_eq_of_isIdempotentElem_left`/`_right`.
* `MurrayVonNeumannEquiv.blockSum`, `add_of_mul_eq_zero`,
  `IsStarProjection.murrayVonNeumannEquiv_of_conj_unitization`, `of_unitary_conj_unitization`,
  `amplify`, `IsStarProjection.murrayVonNeumannEquiv_reindexₐ`,
  `exists_isSelfAdjoint_unitary_conj_blockSum_eq`, `exists_joined_one_unitary_conj_blockSum_eq`,
  `joined_blockSum`.
* `IsPartialIsometry.stabilizedConjUnitary`, `stabilizedNegProj`, `stabilizedProjRot`,
  `IsPartialIsometry.expUnitary_conj_blockSum_eq_stabilizedProjRot`,
  `IsPartialIsometry.stabilizedProjPath`.

## References

* B. Blackadar, *K-Theory for Operator Algebras*, 2nd ed., §4.6 and §5.1.
-/

public section

noncomputable section

open scoped Matrix ComplexOrder

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
theorem of_mem_unitary [DecidableEq n] [Semiring A] [StarRing A] {u : CStarMatrix n n A}
    (hu : u ∈ unitary (CStarMatrix n n A)) : u.IsPartialIsometry :=
  isPartialIsometry_iff_starMul.mpr (TauCeti.IsPartialIsometry.of_mem_unitary hu)
section ProperStar
variable [NonUnitalRing A] [StarRing A] [PartialOrder A] [StarOrderedRing A] [IsProperStar A]
  {v : CStarMatrix m n A}
/-- Over a proper-star ordered ring, `v` is a partial isometry if `vᴴ * v` is idempotent. -/
theorem of_isIdempotentElem_conjTranspose_mul_self (h : IsIdempotentElem (v.conjTranspose * v)) :
    v.IsPartialIsometry :=
  isPartialIsometry_iff.mpr <| ofMatrix.symm.injective <|
    Matrix.mul_conjTranspose_mul_self_of_isIdempotentElem (ofMatrix.symm v) <| by
      simpa only [IsIdempotentElem, ofMatrix_symm_mul, ofMatrix_symm_conjTranspose] using
        congrArg ofMatrix.symm h.eq
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

/-- For a star projection `p`, `fromRows p 0 * (fromRows p 0)ᴴ = blockSum p 0`. -/
theorem _root_.IsStarProjection.fromRows_zero_mul_conjTranspose_fromRows_zero [Fintype m]
    [NonUnitalNonAssocSemiring A] [StarAddMonoid A] {p : CStarMatrix m m A}
    (hp : IsStarProjection p) :
    fromRows p (0 : CStarMatrix n m A) * (fromRows p (0 : CStarMatrix n m A)).conjTranspose =
      blockSum p (0 : CStarMatrix n n A) := by
  rw [fromRows_mul_conjTranspose_fromRows]
  simp [hp.isSelfAdjoint.conjTranspose_eq, hp.isIdempotentElem.eq, blockSum_def]
section
variable [Fintype n] [NonUnitalNonAssocSemiring A] [StarRing A]
  {p₁ p₂ : CStarMatrix n n A} (hp₁ : IsStarProjection p₁) (hp₂ : IsStarProjection p₂)
  (h₁₂ : p₁ * p₂ = 0)
include hp₁ hp₂ h₁₂
/-- For orthogonal projections `p₁, p₂`, `fromRows p₁ p₂ * (fromRows p₁ p₂)ᴴ = blockSum p₁ p₂`. -/
theorem _root_.IsStarProjection.fromRows_mul_conjTranspose_fromRows_eq_blockSum :
    fromRows p₁ p₂ * (fromRows p₁ p₂).conjTranspose = blockSum p₁ p₂ := by
  have h₂₁ : p₂ * p₁ = 0 := by
    have h := congrArg CStarMatrix.conjTranspose h₁₂
    rw [conjTranspose_mul, hp₁.isSelfAdjoint.conjTranspose_eq,
      hp₂.isSelfAdjoint.conjTranspose_eq, conjTranspose_zero] at h
    exact h
  rw [fromRows_mul_conjTranspose_fromRows, hp₁.isSelfAdjoint.conjTranspose_eq,
    hp₂.isSelfAdjoint.conjTranspose_eq, hp₁.isIdempotentElem.eq,
    hp₂.isIdempotentElem.eq, h₁₂, h₂₁, ← blockSum_def]
/-- Vertical row stack `fromRows p₁ p₂` of two orthogonal star projections is a partial isometry. -/
theorem _root_.IsStarProjection.isPartialIsometry_fromRows_of_mul_eq_zero :
    (fromRows p₁ p₂).IsPartialIsometry := by
  rw [isPartialIsometry_iff, hp₁.fromRows_mul_conjTranspose_fromRows_eq_blockSum hp₂ h₁₂,
    blockSum_mul_fromRows, hp₁.isIdempotentElem.eq, hp₂.isIdempotentElem.eq]
end
section
variable [Fintype n] [NonUnitalSemiring A] [StarRing A]
/-- Right-multiplying `M` by a star projection `p` gives `(M * p) * (M * p)ᴴ = M * p * Mᴴ`. -/
theorem self_mul_conjTranspose_mul_of_isStarProjection (M : CStarMatrix m n A)
    {p : CStarMatrix n n A} (hp : IsStarProjection p) :
    (M * p) * (M * p).conjTranspose = M * p * M.conjTranspose := by
  rw [conjTranspose_mul, hp.isSelfAdjoint.conjTranspose_eq,
    mul_assoc_rectangular, ← mul_assoc_rectangular p, hp.isIdempotentElem.eq,
    mul_assoc_rectangular]
end
section
variable [Fintype m] [Fintype n] [NonUnitalSemiring A] [StarRing A] {p : CStarMatrix n n A}
/-- If `uᴴ * u` acts as the identity on the range of a star projection `p`, then
`(u * p)ᴴ * (u * p) = p`. -/
theorem _root_.IsStarProjection.conjTranspose_mul_self_mul_of_conjTranspose_mul_self_mul_eq
    (hp : IsStarProjection p) {u : CStarMatrix m n A} (hu : u.conjTranspose * u * p = p) :
    (u * p).conjTranspose * (u * p) = p := by
  rw [conjTranspose_mul, hp.isSelfAdjoint.conjTranspose_eq, mul_assoc_rectangular,
    ← mul_assoc_rectangular u.conjTranspose, hu, hp.isIdempotentElem.eq]
/-- If `uᴴ * u` acts as the identity on the range of a star projection `p`, then `u * p` is a
partial isometry. -/
theorem IsPartialIsometry.mul_of_conjTranspose_mul_self_mul_eq_of_isStarProjection
    {u : CStarMatrix m n A} (hu : u.conjTranspose * u * p = p) (hp : IsStarProjection p) :
    (u * p).IsPartialIsometry := by
  rw [isPartialIsometry_iff, mul_assoc_rectangular,
    hp.conjTranspose_mul_self_mul_of_conjTranspose_mul_self_mul_eq hu, mul_assoc_rectangular,
    hp.isIdempotentElem.eq]
end
section
variable [Fintype m] [Fintype n] [DecidableEq n] [Semiring A] [StarRing A] {p : CStarMatrix n n A}
/-- Initial projection of `u * p` for an isometry `u` (`uᴴ * u = 1`) and star projection `p`. -/
theorem _root_.IsStarProjection.conjTranspose_mul_self_mul_of_conjTranspose_mul_self_eq_one
    (hp : IsStarProjection p) {u : CStarMatrix m n A} (hu : u.conjTranspose * u = 1) :
    (u * p).conjTranspose * (u * p) = p :=
  hp.conjTranspose_mul_self_mul_of_conjTranspose_mul_self_mul_eq (by rw [hu, CStarMatrix.one_mul])
/-- Left-multiplying a star projection `p` by an isometry `u` yields a partial isometry. -/
theorem IsPartialIsometry.mul_of_conjTranspose_mul_self_eq_one_of_isStarProjection
    {u : CStarMatrix m n A} (hu : u.conjTranspose * u = 1) (hp : IsStarProjection p) :
    (u * p).IsPartialIsometry :=
  mul_of_conjTranspose_mul_self_mul_eq_of_isStarProjection (by rw [hu, CStarMatrix.one_mul]) hp
end

section
variable [Fintype k] [Fintype l] [Fintype m] [Fintype n] [Fintype o]
@[simp] theorem isPartialIsometry_conjTranspose_iff [NonUnitalSemiring A] [StarRing A]
    {v : CStarMatrix m n A} : v.conjTranspose.IsPartialIsometry ↔ v.IsPartialIsometry :=
  ⟨fun h => by simpa using h.conjTranspose, IsPartialIsometry.conjTranspose⟩
@[simp] theorem isPartialIsometry_blockSum_iff [NonUnitalNonAssocSemiring A] [StarAddMonoid A]
    {v : CStarMatrix m l A} {w : CStarMatrix o n A} :
    (blockSum v w).IsPartialIsometry ↔ v.IsPartialIsometry ∧ w.IsPartialIsometry := by
  rw [isPartialIsometry_iff, blockSum_conjTranspose, blockSum_mul, blockSum_mul, blockSum_inj]; rfl
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
  rw [isPartialIsometry_iff, amplify_conjTranspose, amplify_mul, amplify_mul, amplify_inj]; rfl
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
/-- `ofMatrix.symm p` is a star projection iff `p` is a star projection. -/
@[simp] theorem isStarProjection_ofMatrix_symm_iff [NonUnitalNonAssocSemiring A] [Star A]
    {p : CStarMatrix m m A} : IsStarProjection (ofMatrix.symm p) ↔ IsStarProjection p := by
  rw [isStarProjection_iff, isStarProjection_iff, IsIdempotentElem, IsIdempotentElem,
    IsSelfAdjoint, IsSelfAdjoint, ← ofMatrix_symm_mul, Matrix.star_eq_conjTranspose,
    ← ofMatrix_symm_star, ofMatrix.symm.injective.eq_iff, ofMatrix.symm.injective.eq_iff]
/-- `CStarMatrix.MurrayVonNeumannEquiv` coincides with `Matrix.IsMurrayVonNeumannEquivalent` on
underlying matrices via `ofMatrix.symm`. -/
theorem murrayVonNeumannEquiv_iff_matrix [NonUnitalSemiring A] [StarRing A]
    {p : CStarMatrix m m A} {q : CStarMatrix n n A} :
    p.MurrayVonNeumannEquiv q ↔
      Matrix.IsMurrayVonNeumannEquivalent (ofMatrix.symm p) (ofMatrix.symm q) := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · obtain ⟨v, hvp, hvq⟩ := h.exists_matrix
    rw [Matrix.isMurrayVonNeumannEquivalent_iff]
    exact ⟨isStarProjection_ofMatrix_symm_iff.mpr h.isStarProjection_left,
      isStarProjection_ofMatrix_symm_iff.mpr h.isStarProjection_right,
      ofMatrix.symm v, by rw [← ofMatrix_symm_conjTranspose, ← ofMatrix_symm_mul, hvp],
      by rw [← ofMatrix_symm_conjTranspose, ← ofMatrix_symm_mul, hvq]⟩
  · rw [Matrix.isMurrayVonNeumannEquivalent_iff] at h
    rcases h with ⟨hp, hq, v, hvp, hvq⟩
    exact (murrayVonNeumannEquiv_iff (isStarProjection_ofMatrix_symm_iff.mp hp)
      (isStarProjection_ofMatrix_symm_iff.mp hq)).mpr
      ⟨ofMatrix v, ofMatrix.symm.injective <| by
        rw [ofMatrix_symm_mul, ofMatrix_symm_conjTranspose, Equiv.symm_apply_apply, hvp],
        ofMatrix.symm.injective <| by
          rw [ofMatrix_symm_mul, ofMatrix_symm_conjTranspose, Equiv.symm_apply_apply, hvq]⟩
section
variable [NonUnitalSemiring A] [StarRing A] {p : CStarMatrix m m A} {q : CStarMatrix n n A}
/-- A rectangular partial isometry implements Murray–von Neumann equivalence between its initial
and final projections. -/
theorem IsPartialIsometry.murrayVonNeumannEquiv {v : CStarMatrix n m A} (hv : v.IsPartialIsometry) :
    (v.conjTranspose * v).MurrayVonNeumannEquiv (v * v.conjTranspose) :=
  (murrayVonNeumannEquiv_iff hv.isStarProjection_conjTranspose_mul_self
    hv.isStarProjection_mul_conjTranspose_self).mpr ⟨v, rfl, rfl⟩
/-- Extract a rectangular partial-isometry witness from a Murray–von Neumann equivalence. -/
theorem MurrayVonNeumannEquiv.exists_isPartialIsometry (h : p.MurrayVonNeumannEquiv q) :
    ∃ v : CStarMatrix n m A, v.IsPartialIsometry ∧ v.conjTranspose * v = p ∧
      v * v.conjTranspose = q := by
  obtain ⟨v, hvp, hvq, hvp_eq⟩ := h.exists_matrix_mul_eq_self
  exact ⟨v, isPartialIsometry_iff.mpr <| by rw [mul_assoc_rectangular, hvp, hvp_eq], hvp, hvq⟩
/-- Rectangular `MurrayVonNeumannEquiv` holds iff witnessed by a rectangular partial isometry. -/
theorem murrayVonNeumannEquiv_iff_exists_isPartialIsometry :
    p.MurrayVonNeumannEquiv q ↔
      ∃ v : CStarMatrix n m A, v.IsPartialIsometry ∧ v.conjTranspose * v = p ∧
        v * v.conjTranspose = q :=
  ⟨MurrayVonNeumannEquiv.exists_isPartialIsometry,
    fun ⟨_, hv, hvp, hvq⟩ => hvp ▸ hvq ▸ hv.murrayVonNeumannEquiv⟩
end
section
variable [NonUnitalRing A] [StarRing A] [PartialOrder A] [StarOrderedRing A] [IsProperStar A]
  {p : CStarMatrix m m A} {q : CStarMatrix n n A}
/-- Over a proper-star ordered ring, idempotent `p ∼ q` iff `∃ v, vᴴ * v = p ∧ v * vᴴ = q`. -/
theorem murrayVonNeumannEquiv_iff_exists_mul_eq_of_isIdempotentElem_left (hp : IsIdempotentElem p) :
    p.MurrayVonNeumannEquiv q ↔ ∃ v : CStarMatrix n m A, v.conjTranspose * v = p ∧
      v * v.conjTranspose = q :=
  ⟨MurrayVonNeumannEquiv.exists_matrix, fun ⟨v, hvp, hvq⟩ => by
    have hv : v.IsPartialIsometry :=
      .of_isIdempotentElem_conjTranspose_mul_self (hvp.symm ▸ hp)
    rw [← hvp, ← hvq]
    exact hv.murrayVonNeumannEquiv⟩
/-- Over a proper-star ordered ring, `p ∼ q` (idempotent `q`) iff `∃ v, vᴴ * v = p ∧ v * vᴴ = q`. -/
theorem murrayVonNeumannEquiv_iff_exists_mul_eq_of_isIdempotentElem_right
    (hq : IsIdempotentElem q) : p.MurrayVonNeumannEquiv q ↔
      ∃ v : CStarMatrix n m A, v.conjTranspose * v = p ∧ v * v.conjTranspose = q :=
  ⟨MurrayVonNeumannEquiv.exists_matrix, fun ⟨v, hvp, hvq⟩ => by
    have hv : v.IsPartialIsometry :=
      .of_isIdempotentElem_mul_conjTranspose_self (hvq.symm ▸ hq)
    rw [← hvp, ← hvq]
    exact hv.murrayVonNeumannEquiv⟩
end
namespace MurrayVonNeumannEquiv
/-- `MurrayVonNeumannEquiv` is compatible with `blockSum`. -/
protected theorem blockSum [NonUnitalSemiring A] [StarRing A] {p₁ : CStarMatrix l l A}
    {q₁ : CStarMatrix m m A} {p₂ : CStarMatrix n n A} {q₂ : CStarMatrix o o A}
    (h₁ : p₁.MurrayVonNeumannEquiv q₁) (h₂ : p₂.MurrayVonNeumannEquiv q₂) :
    (CStarMatrix.blockSum p₁ p₂).MurrayVonNeumannEquiv (CStarMatrix.blockSum q₁ q₂) :=
  murrayVonNeumannEquiv_iff_matrix.mpr <| by
    simpa only [ofMatrix_symm_blockSum, ofMatrix_symm_zero] using
      (murrayVonNeumannEquiv_iff_matrix.mp h₁).fromBlocks
        (murrayVonNeumannEquiv_iff_matrix.mp h₂)
section
variable {p : CStarMatrix m m A} {q : CStarMatrix n n A}
/-- Finite block-diagonal amplification preserves rectangular `MurrayVonNeumannEquiv`. -/
protected theorem amplify (k : Type*) [Fintype k] [DecidableEq k] [NonUnitalSemiring A]
    [StarRing A] (h : p.MurrayVonNeumannEquiv q) :
    (CStarMatrix.amplify k p).MurrayVonNeumannEquiv (CStarMatrix.amplify k q) := by
  rcases h.exists_isPartialIsometry with ⟨v, hv, rfl, rfl⟩
  simpa [amplify_conjTranspose, amplify_mul] using (hv.amplify k).murrayVonNeumannEquiv
end
end MurrayVonNeumannEquiv
theorem murrayVonNeumannEquiv_comm [NonUnitalSemiring A] [StarRing A] {p : CStarMatrix m m A}
    {q : CStarMatrix n n A} : p.MurrayVonNeumannEquiv q ↔ q.MurrayVonNeumannEquiv p := by
  rw [murrayVonNeumannEquiv_iff_matrix, murrayVonNeumannEquiv_iff_matrix,
    Matrix.isMurrayVonNeumannEquivalent_comm]
section
variable [NonUnitalSemiring A] [StarRing A]
private theorem mvn_reindexₐ_congr (R) [Semiring R] [Module R A] (e₁ : k ≃ l) (e₂ : m ≃ n)
    {p : CStarMatrix k k A} {q : CStarMatrix m m A} (h : p.MurrayVonNeumannEquiv q) :
    (reindexₐ R A e₁ p).MurrayVonNeumannEquiv (reindexₐ R A e₂ q) :=
  murrayVonNeumannEquiv_iff_matrix.mpr <| by
    simpa only [ofMatrix_symm_reindexₐ] using
      (murrayVonNeumannEquiv_iff_matrix.mp h).reindex e₁ e₂
/-- Reindexing a star projection along a bijection `e : m ≃ n` yields an equivalent projection. -/
theorem _root_.IsStarProjection.murrayVonNeumannEquiv_reindexₐ {p : CStarMatrix m m A}
    (hp : IsStarProjection p) (R : Type*) [Semiring R] [Module R A] (e : m ≃ n) :
    p.MurrayVonNeumannEquiv (reindexₐ R A e p) :=
  murrayVonNeumannEquiv_iff_matrix.mpr <| by
    simpa only [ofMatrix_symm_reindexₐ] using
      (isStarProjection_ofMatrix_symm_iff.mpr hp).isMurrayVonNeumannEquivalent_reindex e
section
variable [Semiring R] [Module R A]
@[simp] theorem murrayVonNeumannEquiv_reindexₐ_right_iff (e : m ≃ n) {p : CStarMatrix l l A}
    {q : CStarMatrix m m A} :
    p.MurrayVonNeumannEquiv (reindexₐ R A e q) ↔ p.MurrayVonNeumannEquiv q :=
  ⟨fun h => by simpa [reindexₐ_symm] using mvn_reindexₐ_congr R (.refl l) e.symm h,
   fun h => by simpa using mvn_reindexₐ_congr R (.refl l) e h⟩
@[simp] theorem murrayVonNeumannEquiv_reindexₐ_left_iff (e : l ≃ m) {p : CStarMatrix l l A}
    {q : CStarMatrix n n A} :
    (reindexₐ R A e p).MurrayVonNeumannEquiv q ↔ p.MurrayVonNeumannEquiv q :=
  ⟨fun h => by simpa [reindexₐ_symm] using mvn_reindexₐ_congr R e.symm (.refl n) h,
   fun h => by simpa using mvn_reindexₐ_congr R e (.refl n) h⟩
end
end
section
variable [NonUnitalSemiring A] [StarRing A]
/-- Padding a star projection by a lower-right zero block yields an equivalent projection. -/
theorem _root_.IsStarProjection.murrayVonNeumannEquiv_blockSum_zero {p : CStarMatrix m m A}
    (hp : IsStarProjection p) (n : Type*) [Fintype n] :
    p.MurrayVonNeumannEquiv (blockSum p (0 : CStarMatrix n n A)) :=
  murrayVonNeumannEquiv_iff_matrix.mpr <| by
    simpa only [ofMatrix_symm_blockSum, ofMatrix_symm_zero] using
      (isStarProjection_ofMatrix_symm_iff.mpr hp).isMurrayVonNeumannEquivalent_fromBlocks_zero
/-- Swapping the two diagonal blocks of `blockSum p q` preserves Murray–von Neumann equivalence. -/
theorem _root_.IsStarProjection.murrayVonNeumannEquiv_blockSum_comm {p : CStarMatrix m m A}
    {q : CStarMatrix n n A} (hp : IsStarProjection p) (hq : IsStarProjection q) :
    (blockSum p q).MurrayVonNeumannEquiv (blockSum q p) :=
  murrayVonNeumannEquiv_iff_matrix.mpr <| by
    simpa only [ofMatrix_symm_blockSum, ofMatrix_symm_zero] using
      Matrix.isMurrayVonNeumannEquivalent_fromBlocks_comm
        (isStarProjection_ofMatrix_symm_iff.mpr hp) (isStarProjection_ofMatrix_symm_iff.mpr hq)
/-- `blockSum` of star projections is associative up to Murray–von Neumann equivalence. -/
theorem _root_.IsStarProjection.murrayVonNeumannEquiv_blockSum_assoc {p : CStarMatrix l l A}
    {q : CStarMatrix m m A} {r : CStarMatrix n n A} (hp : IsStarProjection p)
    (hq : IsStarProjection q) (hr : IsStarProjection r) :
    (blockSum (blockSum p q) r).MurrayVonNeumannEquiv (blockSum p (blockSum q r)) :=
  murrayVonNeumannEquiv_iff_matrix.mpr <| by
    simpa only [ofMatrix_symm_blockSum, ofMatrix_symm_zero] using
      Matrix.isMurrayVonNeumannEquivalent_fromBlocks_assoc
        (isStarProjection_ofMatrix_symm_iff.mpr hp)
        (isStarProjection_ofMatrix_symm_iff.mpr hq)
        (isStarProjection_ofMatrix_symm_iff.mpr hr)
/-- Padding a star projection by an upper-left zero block yields an equivalent projection. -/
theorem _root_.IsStarProjection.murrayVonNeumannEquiv_zero_blockSum {q : CStarMatrix n n A}
    (hq : IsStarProjection q) (m : Type*) [Fintype m] :
    q.MurrayVonNeumannEquiv (blockSum (0 : CStarMatrix m m A) q) :=
  murrayVonNeumannEquiv_iff_matrix.mpr <| by
    simpa only [ofMatrix_symm_blockSum, ofMatrix_symm_zero] using
      (isStarProjection_ofMatrix_symm_iff.mpr hq).isMurrayVonNeumannEquivalent_zero_fromBlocks
@[simp] theorem murrayVonNeumannEquiv_blockSum_zero_right_iff {p : CStarMatrix l l A}
    {q : CStarMatrix m m A} : p.MurrayVonNeumannEquiv (blockSum q (0 : CStarMatrix n n A)) ↔
      p.MurrayVonNeumannEquiv q := ⟨fun h => h.trans
        ((isStarProjection_blockSum_iff.mp
          h.isStarProjection_right).1.murrayVonNeumannEquiv_blockSum_zero n).symm,
  fun h => h.trans (h.isStarProjection_right.murrayVonNeumannEquiv_blockSum_zero n)⟩
@[simp] theorem murrayVonNeumannEquiv_blockSum_zero_left_iff {p : CStarMatrix l l A}
    {q : CStarMatrix n n A} : (blockSum p (0 : CStarMatrix m m A)).MurrayVonNeumannEquiv q ↔
      p.MurrayVonNeumannEquiv q := by
  rw [murrayVonNeumannEquiv_comm, murrayVonNeumannEquiv_blockSum_zero_right_iff,
    murrayVonNeumannEquiv_comm]
@[simp] theorem murrayVonNeumannEquiv_zero_blockSum_right_iff {p : CStarMatrix l l A}
    {q : CStarMatrix m m A} : p.MurrayVonNeumannEquiv (blockSum (0 : CStarMatrix n n A) q) ↔
      p.MurrayVonNeumannEquiv q := ⟨fun h => h.trans
        ((isStarProjection_blockSum_iff.mp
          h.isStarProjection_right).2.murrayVonNeumannEquiv_zero_blockSum n).symm,
  fun h => h.trans (h.isStarProjection_right.murrayVonNeumannEquiv_zero_blockSum n)⟩
@[simp] theorem murrayVonNeumannEquiv_zero_blockSum_left_iff {p : CStarMatrix m m A}
    {q : CStarMatrix n n A} : (blockSum (0 : CStarMatrix l l A) p).MurrayVonNeumannEquiv q ↔
      p.MurrayVonNeumannEquiv q := by
  rw [murrayVonNeumannEquiv_comm, murrayVonNeumannEquiv_zero_blockSum_right_iff,
    murrayVonNeumannEquiv_comm]
/-- For orthogonal star projections `p₁, p₂`, `p₁ + p₂` is equivalent to `blockSum p₁ p₂`. -/
theorem _root_.IsStarProjection.murrayVonNeumannEquiv_add_blockSum_of_mul_eq_zero
    {p₁ p₂ : CStarMatrix n n A} (hp₁ : IsStarProjection p₁) (hp₂ : IsStarProjection p₂)
    (h₁₂ : p₁ * p₂ = 0) : (p₁ + p₂).MurrayVonNeumannEquiv (blockSum p₁ p₂) := by
  have h1 : (fromRows p₁ p₂).conjTranspose * fromRows p₁ p₂ = p₁ + p₂ := by
    rw [conjTranspose_fromRows_mul_fromRows, hp₁.isSelfAdjoint.conjTranspose_eq,
      hp₂.isSelfAdjoint.conjTranspose_eq, hp₁.isIdempotentElem.eq,
      hp₂.isIdempotentElem.eq]
  have h2 := hp₁.fromRows_mul_conjTranspose_fromRows_eq_blockSum hp₂ h₁₂
  rw [← h1, ← h2]
  exact (hp₁.isPartialIsometry_fromRows_of_mul_eq_zero hp₂ h₁₂).murrayVonNeumannEquiv
/-- Orthogonal sums of pairwise Murray–von Neumann equivalent projections are equivalent. -/
theorem MurrayVonNeumannEquiv.add_of_mul_eq_zero {p₁ p₂ : CStarMatrix m m A}
    {q₁ q₂ : CStarMatrix n n A} (h₁ : p₁.MurrayVonNeumannEquiv q₁)
    (h₂ : p₂.MurrayVonNeumannEquiv q₂) (hp : p₁ * p₂ = 0) (hq : q₁ * q₂ = 0) :
    (p₁ + p₂).MurrayVonNeumannEquiv (q₁ + q₂) :=
  (h₁.isStarProjection_left.murrayVonNeumannEquiv_add_blockSum_of_mul_eq_zero
    h₂.isStarProjection_left hp).trans <| (h₁.blockSum h₂).trans
      (h₁.isStarProjection_right.murrayVonNeumannEquiv_add_blockSum_of_mul_eq_zero
        h₂.isStarProjection_right hq).symm
end
/-- If `uᴴ * u` acts as the identity on the range of a star projection `p`, then
`p ∼ u * p * uᴴ`. -/
theorem _root_.IsStarProjection.murrayVonNeumannEquiv_conj_of_conjTranspose_mul_self_mul_eq
    [NonUnitalSemiring A] [StarRing A] {p : CStarMatrix n n A} (hp : IsStarProjection p)
    {u : CStarMatrix m n A} (hu : u.conjTranspose * u * p = p) :
    p.MurrayVonNeumannEquiv (u * p * u.conjTranspose) :=
  murrayVonNeumannEquiv_iff_matrix.mpr <| by
    simpa only [ofMatrix_symm_mul, ofMatrix_symm_conjTranspose] using
      (isStarProjection_ofMatrix_symm_iff.mpr hp).isMurrayVonNeumannEquivalent_mul_mul_conjTranspose
        (w := ofMatrix.symm u) (by
          simpa only [← ofMatrix_symm_mul, ← ofMatrix_symm_conjTranspose] using
            congrArg ofMatrix.symm hu)
/-- Conjugating a star projection `p` by an isometry `u` (`uᴴ * u = 1`) gives `p ∼ u * p * uᴴ`. -/
theorem _root_.IsStarProjection.murrayVonNeumannEquiv_conj_of_conjTranspose_mul_self_eq_one
    [DecidableEq n] [Semiring A] [StarRing A] {p : CStarMatrix n n A} (hp : IsStarProjection p)
    {u : CStarMatrix m n A} (hu : u.conjTranspose * u = 1) :
    p.MurrayVonNeumannEquiv (u * p * u.conjTranspose) :=
  hp.murrayVonNeumannEquiv_conj_of_conjTranspose_mul_self_mul_eq (by rw [hu, CStarMatrix.one_mul])
/-- Rectangular unitization descent: if `u : CStarMatrix n m (Unitization R A)` satisfies
`uᴴ * u * p.map ι = p.map ι` and `u * p.map ι * uᴴ = q.map ι` for projections `p, q` over `A`,
then `p ∼ q`. -/
theorem _root_.IsStarProjection.murrayVonNeumannEquiv_of_conj_unitization (R : Type*)
    [CommSemiring R] [StarRing R] [NonUnitalSemiring A] [StarRing A] [Module R A]
    [IsScalarTower R A A] [SMulCommClass R A A] [StarModule R A] {p : CStarMatrix m m A}
    (hp : IsStarProjection p) {q : CStarMatrix n n A}
    (u : CStarMatrix n m (Unitization R A))
    (hu_init : u.conjTranspose * u * p.map (Unitization.inrNonUnitalStarAlgHom R A) =
      p.map (Unitization.inrNonUnitalStarAlgHom R A))
    (hu_conj : u * p.map (Unitization.inrNonUnitalStarAlgHom R A) * u.conjTranspose =
      q.map (Unitization.inrNonUnitalStarAlgHom R A)) : p.MurrayVonNeumannEquiv q := by
  let ι := Unitization.inrNonUnitalStarAlgHom R A
  have hι : Function.Injective fun M : CStarMatrix n m A => M.map ι :=
    CStarMatrix.map_injective Unitization.inr_injective
  have hι_m : Function.Injective fun M : CStarMatrix m m A => M.map ι :=
    CStarMatrix.map_injective Unitization.inr_injective
  have hι_n : Function.Injective fun M : CStarMatrix n n A => M.map ι :=
    CStarMatrix.map_injective Unitization.inr_injective
  let w : CStarMatrix n m (Unitization R A) := u * p.map ι
  let v : CStarMatrix n m A := ofMatrix fun i j => (w i j).snd
  have hv_map : v.map ι = w := CStarMatrix.ext fun i j => Unitization.ext (by
    simp only [map_apply, ι, Unitization.inrNonUnitalStarAlgHom_apply, Unitization.fst_inr]
    dsimp only [w]; rw [mul_apply, ← Unitization.fstHom_apply, map_sum]
    exact (Finset.sum_eq_zero fun k _ => by simp [ι, Unitization.fst_mul]).symm) rfl
  have hpι : IsStarProjection (p.map ι) := by rw [← mapₙₐ_eq_map]; exact hp.map (mapₙₐ ι)
  have hv : v.IsPartialIsometry := isPartialIsometry_iff.mpr <| hι <| by
    simpa only [map_mul, map_conjTranspose, hv_map] using
      (IsPartialIsometry.mul_of_conjTranspose_mul_self_mul_eq_of_isStarProjection
        hu_init hpι).mul_conjTranspose_mul_self
  have hvp : v.conjTranspose * v = p := hι_m <| by
    simpa only [map_mul, map_conjTranspose, hv_map] using
      hpι.conjTranspose_mul_self_mul_of_conjTranspose_mul_self_mul_eq hu_init
  have hvq : v * v.conjTranspose = q := hι_n <| by
    simpa only [map_mul, map_conjTranspose, hv_map, w] using
      (self_mul_conjTranspose_mul_of_isStarProjection u hpι).trans hu_conj
  exact hvp ▸ hvq ▸ hv.murrayVonNeumannEquiv
/-- Unitary conjugacy over `Unitization R A` between projections from `A` gives `p ∼ q`. -/
theorem MurrayVonNeumannEquiv.of_unitary_conj_unitization (R : Type*) [DecidableEq n]
    [CommSemiring R] [StarRing R] [NonUnitalSemiring A] [StarRing A] [Module R A]
    [IsScalarTower R A A] [SMulCommClass R A A] [StarModule R A] {p q : CStarMatrix n n A}
    (hp : IsStarProjection p) (u : unitary (CStarMatrix n n (Unitization R A)))
    (hu : (u : CStarMatrix n n (Unitization R A)) * p.map (Unitization.inrNonUnitalStarAlgHom R A) *
        star (u : CStarMatrix n n (Unitization R A)) =
      q.map (Unitization.inrNonUnitalStarAlgHom R A)) : p.MurrayVonNeumannEquiv q :=
  hp.murrayVonNeumannEquiv_of_conj_unitization R (u : CStarMatrix n n (Unitization R A))
    (by rw [← star_eq_conjTranspose, Unitary.coe_star_mul_self, CStarMatrix.one_mul])
    (by rwa [← star_eq_conjTranspose])
end

namespace IsPartialIsometry
variable [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] [Ring A] [StarRing A]
  {v : CStarMatrix n m A} {p : CStarMatrix m m A} {q : CStarMatrix n n A}
  (hv : v.IsPartialIsometry) (hp : v.conjTranspose * v = p) (hq : v * v.conjTranspose = q)
include hv hp hq
private theorem isSelfAdjoint_fromBlocks_one_sub :
    IsSelfAdjoint (fromBlocks (1 - p) v.conjTranspose v (1 - q)) := by
  simp [isSelfAdjoint_iff, (hp ▸ hv.isStarProjection_conjTranspose_mul_self).isSelfAdjoint.star_eq,
    (hq ▸ hv.isStarProjection_mul_conjTranspose_self).isSelfAdjoint.star_eq]
/-- Self-adjoint unitary `fromBlocks (1 - p) vᴴ v (1 - q)` sending `p ⊕ 0` to `0 ⊕ q`. -/
def stabilizedConjUnitary : unitary (CStarMatrix (m ⊕ n) (m ⊕ n) A) :=
  ⟨fromBlocks (1 - p) v.conjTranspose v (1 - q), by
    rw [Unitary.mem_iff, (hv.isSelfAdjoint_fromBlocks_one_sub hp hq).star_eq, and_self]
    have hp' : (ofMatrix.symm v)ᴴ * ofMatrix.symm v = ofMatrix.symm p := by
      simpa only [ofMatrix_symm_mul, ofMatrix_symm_conjTranspose] using congrArg ofMatrix.symm hp
    have hq' : ofMatrix.symm v * (ofMatrix.symm v)ᴴ = ofMatrix.symm q := by
      simpa only [ofMatrix_symm_mul, ofMatrix_symm_conjTranspose] using congrArg ofMatrix.symm hq
    have h1' : ofMatrix.symm p * (ofMatrix.symm v)ᴴ = (ofMatrix.symm v)ᴴ := by
      simpa only [ofMatrix_symm_mul, ofMatrix_symm_conjTranspose] using
        congrArg ofMatrix.symm (hv.mul_conjTranspose_eq_of_conjTranspose_mul_self_eq hp)
    have h2' : ofMatrix.symm v * ofMatrix.symm p = ofMatrix.symm v := by
      simpa only [ofMatrix_symm_mul] using
        congrArg ofMatrix.symm (hv.mul_eq_self_of_conjTranspose_mul_self_eq hp)
    exact ofMatrix.symm.injective <| by
      simpa only [ofMatrix_symm_mul, ofMatrix_symm_fromBlocks, ofMatrix_symm_sub, ofMatrix_symm_one,
        ofMatrix_symm_conjTranspose] using
        Matrix.fromBlocks_one_sub_mul_self_of_mul_eq hp' hq' h1' h2'⟩
@[simp] theorem coe_stabilizedConjUnitary : ((hv.stabilizedConjUnitary hp hq : unitary _) :
    CStarMatrix (m ⊕ n) (m ⊕ n) A) = fromBlocks (1 - p) v.conjTranspose v (1 - q) := (rfl)
/-- The stabilized conjugating unitary `stabilizedConjUnitary` is self-adjoint. -/
theorem isSelfAdjoint_stabilizedConjUnitary :
    IsSelfAdjoint ((hv.stabilizedConjUnitary hp hq : unitary _) : CStarMatrix (m ⊕ n) (m ⊕ n) A) :=
  hv.isSelfAdjoint_fromBlocks_one_sub hp hq
/-- `stabilizedConjUnitary` conjugates `blockSum p 0` to `blockSum 0 q`. -/
theorem stabilizedConjUnitary_conj :
    (hv.stabilizedConjUnitary hp hq : CStarMatrix (m ⊕ n) (m ⊕ n) A) * blockSum p 0 *
      star (hv.stabilizedConjUnitary hp hq : CStarMatrix (m ⊕ n) (m ⊕ n) A) = blockSum 0 q := by
  rw [(hv.isSelfAdjoint_stabilizedConjUnitary hp hq).star_eq, coe_stabilizedConjUnitary]
  have hp' : (ofMatrix.symm v)ᴴ * ofMatrix.symm v = ofMatrix.symm p := by
    simpa only [ofMatrix_symm_mul, ofMatrix_symm_conjTranspose] using congrArg ofMatrix.symm hp
  have hq' : ofMatrix.symm v * (ofMatrix.symm v)ᴴ = ofMatrix.symm q := by
    simpa only [ofMatrix_symm_mul, ofMatrix_symm_conjTranspose] using congrArg ofMatrix.symm hq
  have hvp' : ofMatrix.symm v * ofMatrix.symm p = ofMatrix.symm v := by
    simpa only [ofMatrix_symm_mul] using
      congrArg ofMatrix.symm (hv.mul_eq_self_of_conjTranspose_mul_self_eq hp)
  exact ofMatrix.symm.injective <| by
    simpa only [ofMatrix_symm_mul, ofMatrix_symm_fromBlocks, ofMatrix_symm_blockSum,
      ofMatrix_symm_sub, ofMatrix_symm_one, ofMatrix_symm_zero, ofMatrix_symm_conjTranspose] using
      Matrix.fromBlocks_one_sub_mul_fromBlocks_mul_fromBlocks_one_sub_of_mul_eq hp' hq' hvp'
end IsPartialIsometry

section
variable (v : CStarMatrix n m A) (p : CStarMatrix m m A) (q : CStarMatrix n n A)
/-- Unit-free `(2⁻¹ : ℝ) • fromBlocks p (-v.conjTranspose) (-v) q`. When `v` witnesses
Murray–von Neumann equivalence between `p` and `q` over a unital ring with real scalar action,
this equals `(2⁻¹ : ℝ) • (1 - w)` for the associated `stabilizedConjUnitary` `w`. -/
def stabilizedNegProj [Neg A] [Star A] [SMul ℝ A] : CStarMatrix (m ⊕ n) (m ⊕ n) A :=
  (2⁻¹ : ℝ) • fromBlocks p (-v.conjTranspose) (-v) q
theorem stabilizedNegProj_def [Neg A] [Star A] [SMul ℝ A] :
    stabilizedNegProj v p q = (2⁻¹ : ℝ) • fromBlocks p (-v.conjTranspose) (-v) q := (rfl)
/-- Unit-free rotation curve from `blockSum p 0` (at `t = 0`) to `blockSum 0 q` (at `t = 1`). -/
def stabilizedProjRot [Star A] [SMul ℂ A] (t : ℝ) : CStarMatrix (m ⊕ n) (m ⊕ n) A :=
  let c : ℂ := ↑(Real.cos (Real.pi * t / 2)); let s : ℂ := ↑(Real.sin (Real.pi * t / 2))
  fromBlocks ((c ^ 2) • p) ((Complex.I * s * c) • v.conjTranspose)
    ((-Complex.I * s * c) • v) ((s ^ 2) • q)
theorem stabilizedProjRot_def [Star A] [SMul ℂ A] (t : ℝ) : stabilizedProjRot v p q t =
    fromBlocks (((Real.cos (Real.pi * t / 2) : ℂ) ^ 2) • p)
      ((Complex.I * ↑(Real.sin (Real.pi * t / 2)) * ↑(Real.cos (Real.pi * t / 2))) •
        v.conjTranspose)
      ((-Complex.I * ↑(Real.sin (Real.pi * t / 2)) * ↑(Real.cos (Real.pi * t / 2))) • v)
      (((Real.sin (Real.pi * t / 2) : ℂ) ^ 2) • q) := (rfl)
private def stabilizedProjRotRows [SMul ℂ A] (t : ℝ) : CStarMatrix (m ⊕ n) m A :=
  fromRows ((Real.cos (Real.pi * t / 2) : ℂ) • p) ((-Complex.I * ↑(Real.sin (Real.pi * t / 2))) • v)
section
variable [AddCommMonoid A] [Star A] [Module ℂ A]
@[simp] theorem stabilizedProjRot_zero : stabilizedProjRot v p q 0 = blockSum p 0 := by
  simp [stabilizedProjRot, blockSum_def]
@[simp] theorem stabilizedProjRot_one : stabilizedProjRot v p q 1 = blockSum 0 q := by
  simp [stabilizedProjRot, blockSum_def]
/-- Midpoint value of `stabilizedProjRot v p q` at `t = 1 / 2`. -/
theorem stabilizedProjRot_half : stabilizedProjRot v p q (1 / 2) =
    fromBlocks ((2⁻¹ : ℂ) • p) ((Complex.I / 2) • v.conjTranspose)
      ((-Complex.I / 2) • v) ((2⁻¹ : ℂ) • q) := by
  have hθ : Real.pi * (1 / 2) / 2 = Real.pi / 4 := by ring
  have hc2 : (Real.cos (Real.pi / 4) : ℂ) ^ 2 = 2⁻¹ := by
    rw [Real.cos_pi_div_four, ← Complex.ofReal_pow, div_pow, Real.sq_sqrt (by norm_num)]; norm_num
  simp only [stabilizedProjRot, hθ, Real.sin_pi_div_four, ← Real.cos_pi_div_four, mul_assoc, ← sq,
    hc2, fromBlocks_inj, true_and, and_true]; exact ⟨by congr 1, by congr 1⟩
end
/-- `stabilizedProjRot v p q` is continuous on `ℝ` for any (possibly non-unital) C⋆-algebra `A`. -/
@[fun_prop] theorem continuous_stabilizedProjRot [NonUnitalCStarAlgebra A] :
    Continuous (stabilizedProjRot v p q) := by unfold stabilizedProjRot; fun_prop
end

namespace IsPartialIsometry
variable [Fintype m] [Fintype n] {v : CStarMatrix n m A} {p : CStarMatrix m m A}
  {q : CStarMatrix n n A}
/-- Over a unital real star-algebra, `stabilizedNegProj` is `2⁻¹ • (1 - stabilizedConjUnitary)`. -/
theorem stabilizedNegProj_eq_half_one_sub [DecidableEq m] [DecidableEq n] [Ring A] [StarRing A]
    [Module ℝ A] (hv : v.IsPartialIsometry) (hp : v.conjTranspose * v = p)
    (hq : v * v.conjTranspose = q) : stabilizedNegProj v p q =
      (2⁻¹ : ℝ) • (1 - (hv.stabilizedConjUnitary hp hq : CStarMatrix (m ⊕ n) (m ⊕ n) A)) := by
  rw [stabilizedNegProj_def, coe_stabilizedConjUnitary, ← fromBlocks_one, fromBlocks_sub]; simp
/-- `stabilizedNegProj v p q` is a star projection when `v` witnesses `p ∼ q`. -/
theorem isStarProjection_stabilizedNegProj [NonUnitalRing A] [StarRing A] [Module ℝ A]
    [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] [StarModule ℝ A] (hv : v.IsPartialIsometry)
    (hp : v.conjTranspose * v = p) (hq : v * v.conjTranspose = q) :
    IsStarProjection (stabilizedNegProj v p q) := by
  have hp_proj : IsStarProjection p := hp ▸ hv.isStarProjection_conjTranspose_mul_self
  have hq_proj : IsStarProjection q := hq ▸ hv.isStarProjection_mul_conjTranspose_self
  refine ⟨?_, by simp [isSelfAdjoint_iff, stabilizedNegProj_def,
    hp_proj.isSelfAdjoint.star_eq, hq_proj.isSelfAdjoint.star_eq]⟩
  rw [IsIdempotentElem, stabilizedNegProj_def, CStarMatrix.smul_mul_smul, fromBlocks_mul]
  simp only [CStarMatrix.neg_mul, CStarMatrix.mul_neg, neg_neg, hp_proj.isIdempotentElem.eq,
    hq_proj.isIdempotentElem.eq, hp, hq, hv.mul_eq_self_of_conjTranspose_mul_self_eq hp,
    hv.mul_conjTranspose_eq_of_conjTranspose_mul_self_eq hp,
    hv.mul_eq_self_of_mul_conjTranspose_self_eq hq,
    hv.conjTranspose_mul_eq_of_mul_conjTranspose_self_eq hq,
    ← two_smul ℝ, fromBlocks_smul, smul_neg, smul_smul]; norm_num
section
variable [NonUnitalSemiring A] [StarRing A] [Module ℂ A] [IsScalarTower ℂ A A]
  [SMulCommClass ℂ A A] [StarModule ℂ A] (hv : v.IsPartialIsometry) (hp : v.conjTranspose * v = p)
include hv hp
private theorem stabilizedProjRotRows_mul_conjTranspose (hq : v * v.conjTranspose = q) (t : ℝ) :
    stabilizedProjRotRows v p t * (stabilizedProjRotRows v p t).conjTranspose =
      stabilizedProjRot v p q t := by
  have hp_proj : IsStarProjection p := hp ▸ hv.isStarProjection_conjTranspose_mul_self
  rw [stabilizedProjRotRows, fromRows_mul_conjTranspose_fromRows, stabilizedProjRot_def]
  simp only [conjTranspose_smul, hp_proj.isSelfAdjoint.conjTranspose_eq,
    star_mul, star_neg, Complex.star_def, Complex.conj_ofReal, Complex.conj_I, neg_neg,
    CStarMatrix.smul_mul_smul, hp_proj.isIdempotentElem.eq, hq, fromBlocks_inj,
    hv.mul_conjTranspose_eq_of_conjTranspose_mul_self_eq hp,
    hv.mul_eq_self_of_conjTranspose_mul_self_eq hp]
  exact ⟨by congr 1; ring, by congr 1; ring, trivial,
    by congr 1; linear_combination -(Real.sin (Real.pi * t / 2) : ℂ) ^ 2 * Complex.I_sq⟩
private theorem isPartialIsometry_stabilizedProjRotRows (t : ℝ) :
    (stabilizedProjRotRows v p t).IsPartialIsometry := by
  have hp_proj : IsStarProjection p := hp ▸ hv.isStarProjection_conjTranspose_mul_self
  have htrig : (Real.cos (Real.pi * t / 2) : ℂ) * (Real.cos (Real.pi * t / 2) : ℂ) +
      (Real.sin (Real.pi * t / 2) : ℂ) * Complex.I *
        (-Complex.I * (Real.sin (Real.pi * t / 2) : ℂ)) = 1 := by
    linear_combination (by simp : (Real.cos (Real.pi * t / 2) : ℂ) ^ 2 +
      (Real.sin (Real.pi * t / 2) : ℂ) ^ 2 = 1) -
      (Real.sin (Real.pi * t / 2) : ℂ) ^ 2 * Complex.I_sq
  have hinit : (stabilizedProjRotRows v p t).conjTranspose * stabilizedProjRotRows v p t = p := by
    rw [stabilizedProjRotRows, conjTranspose_fromRows_mul_fromRows]
    simp only [conjTranspose_smul, hp_proj.isSelfAdjoint.conjTranspose_eq,
      star_mul, star_neg, Complex.star_def, Complex.conj_ofReal, Complex.conj_I, neg_neg,
      CStarMatrix.smul_mul_smul, hp_proj.isIdempotentElem.eq, hp, ← add_smul, htrig, one_smul]
  rw [isPartialIsometry_iff, mul_assoc_rectangular, hinit, stabilizedProjRotRows, fromRows_mul,
    CStarMatrix.smul_mul, CStarMatrix.smul_mul, hp_proj.isIdempotentElem.eq,
    hv.mul_eq_self_of_conjTranspose_mul_self_eq hp]
/-- Every point on `stabilizedProjRot v p q` is a star projection when `p = vᴴ * v` and
`q = v * vᴴ` are the initial and final projections of a partial isometry `v`. -/
theorem isStarProjection_stabilizedProjRot (hq : v * v.conjTranspose = q) (t : ℝ) :
    IsStarProjection (stabilizedProjRot v p q t) :=
  hv.stabilizedProjRotRows_mul_conjTranspose hp hq t ▸
    (hv.isPartialIsometry_stabilizedProjRotRows hp t).isStarProjection_mul_conjTranspose_self
end
section
variable [DecidableEq m] [DecidableEq n] [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  (hv : v.IsPartialIsometry) (hp : v.conjTranspose * v = p) (hq : v * v.conjTranspose = q)
/-- Underlying matrix of `expUnitary (θ • stabilizedNegProj v p q)` for `θ : ℝ`. -/
theorem coe_expUnitary_smul_stabilizedNegProj (θ : ℝ) :
    ((selfAdjoint.expUnitary (θ • ⟨stabilizedNegProj v p q,
      (hv.isStarProjection_stabilizedNegProj hp hq).isSelfAdjoint⟩) : unitary _) :
      CStarMatrix (m ⊕ n) (m ⊕ n) A) =
      1 + ((Complex.exp (θ * Complex.I) - 1) * 2⁻¹) • fromBlocks p (-v.conjTranspose) (-v) q := by
  have hcast : (2⁻¹ : ℝ) • fromBlocks p (-v.conjTranspose) (-v) q =
      ((2⁻¹ : ℝ) : ℂ) • fromBlocks p (-v.conjTranspose) (-v) q :=
    ext fun _ _ => (Complex.coe_smul _ _).symm
  refine ((hv.isStarProjection_stabilizedNegProj hp hq).coe_expUnitary_smul θ).trans ?_
  rw [stabilizedNegProj_def, hcast, smul_smul]
  congr 2; push_cast; rfl
private theorem expUnitary_smul_stabilizedNegProj_mul_fromRows (t : ℝ) :
    ((selfAdjoint.expUnitary ((t * Real.pi) • ⟨stabilizedNegProj v p q,
      (hv.isStarProjection_stabilizedNegProj hp hq).isSelfAdjoint⟩) : unitary _) :
      CStarMatrix (m ⊕ n) (m ⊕ n) A) * fromRows p (0 : CStarMatrix n m A) =
      (↑(Real.cos (Real.pi * t / 2)) + ↑(Real.sin (Real.pi * t / 2)) * Complex.I) •
        stabilizedProjRotRows v p t := by
  set c : ℂ := ↑(Real.cos (Real.pi * t / 2)) with hc
  set s : ℂ := ↑(Real.sin (Real.pi * t / 2)) with hs
  set z : ℂ := c + s * Complex.I with hz; have hcs : c ^ 2 + s ^ 2 = 1 := by simp [hc, hs]
  set α : ℂ := (Complex.exp (t * Real.pi * Complex.I) - 1) * 2⁻¹ with hα_def
  -- Write `exp (i π t) = z ^ 2` with `z = exp (i π t / 2) = c + i s`, so `1 + α = z c` and
  -- `-α = z (-i s)`.
  have harg : (t : ℂ) * Real.pi * Complex.I = ((Real.pi * t / 2 : ℝ) : ℂ) * Complex.I +
      ((Real.pi * t / 2 : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  have hα : α = (z ^ 2 - 1) * 2⁻¹ := by
    rw [hα_def, harg, Complex.exp_add, Complex.exp_ofReal_mul_I, ← hc, ← hs, ← hz, sq]
  have h1α : 1 + α = z * c := by
    rw [hα, hz]; linear_combination -((1 : ℂ) / 2) * hcs + (s ^ 2 / 2) * Complex.I_sq
  have hnα : -α = z * (-Complex.I * s) := by
    rw [hα, hz]; linear_combination -((1 : ℂ) / 2) * hcs + (s ^ 2 / 2) * Complex.I_sq
  have hp_act : p + α • p = (z * c) • p := by rw [← h1α, add_smul, one_smul]
  have hv_act : -(α • v) = (z * (-Complex.I * s)) • v := by rw [← neg_smul, hnα]
  rw [hv.coe_expUnitary_smul_stabilizedNegProj hp hq (t * Real.pi), Complex.ofReal_mul, ← hα_def,
    CStarMatrix.add_mul, CStarMatrix.one_mul, CStarMatrix.smul_mul, fromBlocks_mul_fromRows]
  simp [stabilizedProjRotRows, ← hc, ← hs,
    (hp ▸ hv.isStarProjection_conjTranspose_mul_self).isIdempotentElem.eq,
    hv.mul_eq_self_of_conjTranspose_mul_self_eq hp, hp_act, hv_act, smul_smul]
/-- Over a unital C⋆-algebra, `expUnitary` conjugates `blockSum p 0` to `stabilizedProjRot`. -/
theorem expUnitary_conj_blockSum_eq_stabilizedProjRot (t : ℝ) :
    ((selfAdjoint.expUnitary ((t * Real.pi) • ⟨stabilizedNegProj v p q,
      (hv.isStarProjection_stabilizedNegProj hp hq).isSelfAdjoint⟩) : unitary _) :
      CStarMatrix (m ⊕ n) (m ⊕ n) A) * blockSum p 0 *
      star ((selfAdjoint.expUnitary ((t * Real.pi) • ⟨stabilizedNegProj v p q,
        (hv.isStarProjection_stabilizedNegProj hp hq).isSelfAdjoint⟩) : unitary _) :
        CStarMatrix (m ⊕ n) (m ⊕ n) A) = stabilizedProjRot v p q t := by
  set z : ℂ := ↑(Real.cos (Real.pi * t / 2)) + ↑(Real.sin (Real.pi * t / 2)) * Complex.I with hz
  have hzz : z * star z = 1 := by
    rw [Complex.star_def, Complex.mul_conj, hz, Complex.normSq_add_mul_I]; simp
  have hp_proj : IsStarProjection p := hp ▸ hv.isStarProjection_conjTranspose_mul_self
  -- Factor `blockSum p 0 = F * Fᴴ` so `U * blockSum p 0 * Uᴴ = (U * F) * (U * F)ᴴ`.
  rw [star_eq_conjTranspose, ← hp_proj.fromRows_zero_mul_conjTranspose_fromRows_zero,
    ← mul_assoc_rectangular, mul_assoc_rectangular (_ * fromRows p 0), ← conjTranspose_mul,
    hv.expUnitary_smul_stabilizedNegProj_mul_fromRows hp hq t, conjTranspose_smul,
    CStarMatrix.smul_mul_smul, hzz, one_smul, hv.stabilizedProjRotRows_mul_conjTranspose hp hq t]
end
section
variable [NonUnitalCStarAlgebra A] (hv : v.IsPartialIsometry) (hp : v.conjTranspose * v = p)
  (hq : v * v.conjTranspose = q)
/-- Continuous path of star projections from `blockSum p 0` to `blockSum 0 q`. -/
def stabilizedProjPath : Path (⟨blockSum p 0, isStarProjection_blockSum_iff.mpr
        ⟨hp ▸ hv.isStarProjection_conjTranspose_mul_self, .zero _⟩⟩ :
        {P : CStarMatrix (m ⊕ n) (m ⊕ n) A // IsStarProjection P})
      ⟨blockSum 0 q, isStarProjection_blockSum_iff.mpr
        ⟨.zero _, hq ▸ hv.isStarProjection_mul_conjTranspose_self⟩⟩ :=
  ⟨⟨fun t => ⟨stabilizedProjRot v p q t, hv.isStarProjection_stabilizedProjRot hp hq t⟩,
    ((continuous_stabilizedProjRot v p q).comp continuous_subtypeVal).subtype_mk _⟩,
    Subtype.ext (stabilizedProjRot_zero v p q), Subtype.ext (stabilizedProjRot_one v p q)⟩
@[simp] theorem coe_stabilizedProjPath_apply (t : unitInterval) :
    ((hv.stabilizedProjPath hp hq t : {P : CStarMatrix (m ⊕ n) (m ⊕ n) A // IsStarProjection P}) :
      CStarMatrix (m ⊕ n) (m ⊕ n) A) = stabilizedProjRot v p q t := (rfl)
end
end IsPartialIsometry

section
variable [Fintype m] [Fintype n] {p : CStarMatrix m m A} {q : CStarMatrix n n A}
/-- Equivalent projections are conjugate by a self-adjoint unitary after stabilization. -/
theorem MurrayVonNeumannEquiv.exists_isSelfAdjoint_unitary_conj_blockSum_eq
    [DecidableEq m] [DecidableEq n] [Ring A] [StarRing A] (h : p.MurrayVonNeumannEquiv q) :
    ∃ w : unitary (CStarMatrix (m ⊕ n) (m ⊕ n) A),
      IsSelfAdjoint (w : CStarMatrix (m ⊕ n) (m ⊕ n) A) ∧
      (w : CStarMatrix (m ⊕ n) (m ⊕ n) A) * blockSum p 0 *
        star (w : CStarMatrix (m ⊕ n) (m ⊕ n) A) = blockSum 0 q :=
  let ⟨_, hv, hp, hq⟩ := h.exists_isPartialIsometry
  ⟨hv.stabilizedConjUnitary hp hq, hv.isSelfAdjoint_stabilizedConjUnitary hp hq,
    hv.stabilizedConjUnitary_conj hp hq⟩
/-- Over a unital C⋆-algebra, if `p` and `q` are Murray–von Neumann equivalent, a unitary joined
to `1` conjugates `blockSum p 0` to `blockSum 0 q`. -/
theorem MurrayVonNeumannEquiv.exists_joined_one_unitary_conj_blockSum_eq
    [DecidableEq m] [DecidableEq n] [CStarAlgebra A] (h : p.MurrayVonNeumannEquiv q) :
    ∃ w : unitary (CStarMatrix (m ⊕ n) (m ⊕ n) A), Joined 1 w ∧
      (w : CStarMatrix (m ⊕ n) (m ⊕ n) A) * blockSum p 0 *
        star (w : CStarMatrix (m ⊕ n) (m ⊕ n) A) = blockSum 0 q := by
  let _ : PartialOrder A := CStarAlgebra.spectralOrder A
  have _ : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
  obtain ⟨v, hv, hp, hq⟩ := h.exists_isPartialIsometry
  exact ⟨hv.stabilizedConjUnitary hp hq,
    Unitary.joined_one_of_isSelfAdjoint _ (hv.isSelfAdjoint_stabilizedConjUnitary hp hq),
    hv.stabilizedConjUnitary_conj hp hq⟩
/-- Equivalent projections over any C⋆-algebra are joined by a path of projections stably. -/
theorem MurrayVonNeumannEquiv.joined_blockSum [NonUnitalCStarAlgebra A]
    (h : p.MurrayVonNeumannEquiv q) :
    Joined (⟨blockSum p 0, isStarProjection_blockSum_iff.mpr ⟨h.isStarProjection_left, .zero _⟩⟩ :
        {P : CStarMatrix (m ⊕ n) (m ⊕ n) A // IsStarProjection P})
      ⟨blockSum 0 q, isStarProjection_blockSum_iff.mpr ⟨.zero _, h.isStarProjection_right⟩⟩ :=
  let ⟨_, hv, hp, hq⟩ := h.exists_isPartialIsometry
  ⟨hv.stabilizedProjPath hp hq⟩
end

end CStarMatrix
