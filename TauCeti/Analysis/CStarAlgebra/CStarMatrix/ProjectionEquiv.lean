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
import TauCeti.Analysis.CStarAlgebra.Basic
import TauCeti.Data.Matrix.Block

/-!
# Rectangular partial isometries and stabilized Murray–von Neumann paths on `CStarMatrix`

Rectangular partial isometries (`v * vᴴ * v = v`) and extensions of Murray–von Neumann
equivalence (`TauCeti.Analysis.CStarAlgebra.Projection.Equivalence`) over a (possibly non-unital)
C⋆-algebra `A`: proper-star characterizations, compatibility with `blockSum`, `add_of_mul_eq_zero`,
`mapₙₐ`/`mapₐ`, `amplify`, `reindexₐ`, unitization descent, the self-adjoint unitary
`stabilizedConjUnitary` sending `blockSum p 0` to `blockSum 0 q`, its path
`stabilizedConjUnitaryPath` to `1` over unital `A`, and the unit-free projection path
`stabilizedProjPath`.

## Main definitions and statements

* `CStarMatrix.IsPartialIsometry`, `IsPartialIsometry.murrayVonNeumannEquiv`,
  `MurrayVonNeumannEquiv.exists_isPartialIsometry`,
  `murrayVonNeumannEquiv_iff_exists_isPartialIsometry`,
  `isPartialIsometry_iff_isStarProjection_conjTranspose_mul_self`,
  `murrayVonNeumannEquiv_iff_exists_mul_eq_of_isIdempotentElem_left`/`_right`.
* `MurrayVonNeumannEquiv.blockSum`, `add_of_mul_eq_zero`, `of_unitary_conj_unitization`,
  `mapₙₐ`, `mapₐ`, `amplify`, `exists_isSelfAdjoint_unitary_conj_blockSum_eq`,
  `exists_joined_one_unitary_conj_blockSum_eq`, `joined_blockSum`.
* `IsPartialIsometry.stabilizedConjUnitary`, `stabilizedNegProj`, `stabilizedProjRot`,
  `IsPartialIsometry.stabilizedConjUnitaryPath`, `IsPartialIsometry.stabilizedProjPath`.

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
  rw [← CStarMatrix.mul_assoc, hv.mul_conjTranspose_mul_self]
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
  rw [isPartialIsometry_iff, conjTranspose_conjTranspose, CStarMatrix.mul_assoc]
  simpa only [conjTranspose_mul, conjTranspose_conjTranspose] using
    congrArg CStarMatrix.conjTranspose hv.mul_conjTranspose_mul_self
/-- Adjoint partial-isometry identity `v.conjTranspose * v * v.conjTranspose = v.conjTranspose`. -/
theorem conjTranspose_mul_self_mul_conjTranspose :
    v.conjTranspose * v * v.conjTranspose = v.conjTranspose := by
  simpa using hv.conjTranspose.mul_conjTranspose_mul_self
/-- Adjoint identity `v.conjTranspose * (v * v.conjTranspose) = v.conjTranspose`. -/
theorem conjTranspose_mul_self_mul_conjTranspose' :
    v.conjTranspose * (v * v.conjTranspose) = v.conjTranspose := by
  rw [← CStarMatrix.mul_assoc, hv.conjTranspose_mul_self_mul_conjTranspose]
/-- The initial projection `v.conjTranspose * v` of a partial isometry is a star projection. -/
theorem isStarProjection_conjTranspose_mul_self : IsStarProjection (v.conjTranspose * v) :=
  ⟨by rw [IsIdempotentElem, CStarMatrix.mul_assoc, ← CStarMatrix.mul_assoc v, hv],
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
@[simp] protected theorem one [DecidableEq n] [Semiring A] [StarRing A] :
    (1 : CStarMatrix n n A).IsPartialIsometry :=
  isPartialIsometry_iff_starMul.mpr TauCeti.IsPartialIsometry.one
theorem of_isStarProjection [Mul A] [AddCommMonoid A] [Star A] {p : CStarMatrix n n A}
    (hp : IsStarProjection p) : p.IsPartialIsometry :=
  isPartialIsometry_iff_starMul.mpr hp.isPartialIsometry
theorem of_mem_unitary [DecidableEq n] [Semiring A] [StarRing A] {u : CStarMatrix n n A}
    (hu : u ∈ unitary (CStarMatrix n n A)) : u.IsPartialIsometry :=
  isPartialIsometry_iff_starMul.mpr (TauCeti.IsPartialIsometry.of_mem_unitary hu)
section ProperStar
variable [NonUnitalRing A] [StarRing A] [PartialOrder A] [StarOrderedRing A] [IsProperStar A]
  {v : CStarMatrix m n A}
/-- Over a proper-star ordered ring, `v` is a partial isometry if `vᴴ * v` is idempotent. -/
theorem of_isIdempotentElem_conjTranspose_mul_self (h : IsIdempotentElem (v.conjTranspose * v)) :
    v.IsPartialIsometry := by
  let B : CStarMatrix (m ⊕ n) (m ⊕ n) A := fromBlocks 0 v 0 0
  have hB : TauCeti.IsPartialIsometry B := .of_isIdempotentElem_star_mul_self <| by
    simpa [B, fromBlocks_mul, blockSum_def] using isIdempotentElem_blockSum_iff.mpr ⟨.zero, h⟩
  simpa [isPartialIsometry_iff, B, fromBlocks_mul] using congrArg toBlocks₁₂ hB.mul_star_mul_self
/-- Over a proper-star ordered ring, `v` is a partial isometry if `v * vᴴ` is idempotent. -/
theorem of_isIdempotentElem_mul_conjTranspose_self (h : IsIdempotentElem (v * v.conjTranspose)) :
    v.IsPartialIsometry := by
  simpa only [conjTranspose_conjTranspose] using (of_isIdempotentElem_conjTranspose_mul_self
    (v := v.conjTranspose) (by rwa [conjTranspose_conjTranspose])).conjTranspose
end ProperStar
protected theorem blockSum [NonUnitalNonAssocSemiring A] [StarAddMonoid A] {v : CStarMatrix m l A}
    {w : CStarMatrix o n A} (hv : v.IsPartialIsometry) (hw : w.IsPartialIsometry) :
    (CStarMatrix.blockSum v w).IsPartialIsometry := by
  simp [isPartialIsometry_iff, hv.mul_conjTranspose_mul_self, hw.mul_conjTranspose_mul_self]
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
theorem fromRows_zero_mul_conjTranspose_fromRows_zero [Fintype m] [NonUnitalNonAssocSemiring A]
    [StarAddMonoid A] {p : CStarMatrix m m A} (hp : IsStarProjection p) :
    fromRows p (0 : CStarMatrix n m A) * (fromRows p (0 : CStarMatrix n m A)).conjTranspose =
      blockSum p (0 : CStarMatrix n n A) := by
  rw [fromRows_mul_conjTranspose_fromRows]
  simp [conjTranspose_eq_of_isSelfAdjoint hp.isSelfAdjoint, hp.isIdempotentElem.eq, blockSum_def]
section
variable [Fintype n] [NonUnitalSemiring A] [StarRing A]
section
variable {p₁ p₂ : CStarMatrix n n A} (hp₁ : IsStarProjection p₁) (hp₂ : IsStarProjection p₂)
  (h₁₂ : p₁ * p₂ = 0)
include hp₁ hp₂ h₁₂
/-- For orthogonal projections `p₁, p₂`, `fromRows p₁ p₂ * (fromRows p₁ p₂)ᴴ = blockSum p₁ p₂`. -/
theorem fromRows_mul_conjTranspose_fromRows_eq_blockSum :
    fromRows p₁ p₂ * (fromRows p₁ p₂).conjTranspose = blockSum p₁ p₂ := by
  have h₂₁ : p₂ * p₁ = 0 := by
    rw [← hp₂.isSelfAdjoint.star_eq, ← hp₁.isSelfAdjoint.star_eq, ← star_mul, h₁₂, star_zero]
  rw [fromRows_mul_conjTranspose_fromRows, conjTranspose_eq_of_isSelfAdjoint hp₁.isSelfAdjoint,
    conjTranspose_eq_of_isSelfAdjoint hp₂.isSelfAdjoint, hp₁.isIdempotentElem.eq,
    hp₂.isIdempotentElem.eq, h₁₂, h₂₁, ← blockSum_def]
/-- Vertical row stack `fromRows p₁ p₂` of two orthogonal star projections is a partial isometry. -/
theorem IsPartialIsometry.fromRows_of_mul_eq_zero : (fromRows p₁ p₂).IsPartialIsometry := by
  rw [isPartialIsometry_iff, fromRows_mul_conjTranspose_fromRows_eq_blockSum hp₁ hp₂ h₁₂,
    blockSum_mul_fromRows, hp₁.isIdempotentElem.eq, hp₂.isIdempotentElem.eq]
end
/-- Right-multiplying `M` by a star projection `p` gives `(M * p) * (M * p)ᴴ = M * p * Mᴴ`. -/
theorem self_mul_conjTranspose_mul_of_isStarProjection (M : CStarMatrix m n A)
    {p : CStarMatrix n n A} (hp : IsStarProjection p) :
    (M * p) * (M * p).conjTranspose = M * p * M.conjTranspose := by
  rw [conjTranspose_mul, conjTranspose_eq_of_isSelfAdjoint hp.isSelfAdjoint,
    CStarMatrix.mul_assoc, ← CStarMatrix.mul_assoc p, hp.isIdempotentElem.eq, CStarMatrix.mul_assoc]
end
section
variable [Fintype n] [DecidableEq n] [Semiring A] [StarRing A] {p : CStarMatrix n n A}
/-- Initial projection of `u * p` for an isometry `u` (`uᴴ * u = 1`) and star projection `p`. -/
theorem conjTranspose_mul_self_mul_of_conjTranspose_mul_self_eq_one_of_isStarProjection [Fintype m]
    {u : CStarMatrix m n A} (hu : u.conjTranspose * u = 1) (hp : IsStarProjection p) :
    (u * p).conjTranspose * (u * p) = p := by
  rw [conjTranspose_mul, conjTranspose_eq_of_isSelfAdjoint hp.isSelfAdjoint,
    CStarMatrix.mul_assoc, ← CStarMatrix.mul_assoc u.conjTranspose, hu, CStarMatrix.one_mul,
    hp.isIdempotentElem.eq]
/-- Left-multiplying a star projection `p` by an isometry `u` yields a partial isometry. -/
theorem IsPartialIsometry.mul_of_conjTranspose_mul_self_eq_one_of_isStarProjection [Fintype m]
    {u : CStarMatrix m n A} (hu : u.conjTranspose * u = 1) (hp : IsStarProjection p) :
    (u * p).IsPartialIsometry := by
  rw [isPartialIsometry_iff, CStarMatrix.mul_assoc,
    conjTranspose_mul_self_mul_of_conjTranspose_mul_self_eq_one_of_isStarProjection hu hp,
    CStarMatrix.mul_assoc, hp.isIdempotentElem.eq]
/-- Initial projection of `(u : CStarMatrix n n A) * p` for unitary `u` and star projection `p`. -/
theorem conjTranspose_mul_self_unitary_mul_of_isStarProjection (u : unitary (CStarMatrix n n A))
    (hp : IsStarProjection p) :
    ((u : CStarMatrix n n A) * p).conjTranspose * ((u : CStarMatrix n n A) * p) = p :=
  conjTranspose_mul_self_mul_of_conjTranspose_mul_self_eq_one_of_isStarProjection
    (by rw [← star_eq_conjTranspose]; exact Unitary.coe_star_mul_self u) hp
/-- Left-multiplying a star projection `p` by a unitary `u` yields a partial isometry. -/
theorem IsPartialIsometry.unitary_mul_of_isStarProjection (u : unitary (CStarMatrix n n A))
    (hp : IsStarProjection p) : ((u : CStarMatrix n n A) * p).IsPartialIsometry :=
  .mul_of_conjTranspose_mul_self_eq_one_of_isStarProjection
    (by rw [← star_eq_conjTranspose]; exact Unitary.coe_star_mul_self u) hp
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
theorem isPartialIsometry_iff_isIdempotentElem_conjTranspose_mul_self :
    v.IsPartialIsometry ↔ IsIdempotentElem (v.conjTranspose * v) :=
  ⟨fun hv => hv.isStarProjection_conjTranspose_mul_self.isIdempotentElem,
    .of_isIdempotentElem_conjTranspose_mul_self⟩
theorem isPartialIsometry_iff_isIdempotentElem_mul_conjTranspose_self :
    v.IsPartialIsometry ↔ IsIdempotentElem (v * v.conjTranspose) :=
  ⟨fun hv => hv.isStarProjection_mul_conjTranspose_self.isIdempotentElem,
    .of_isIdempotentElem_mul_conjTranspose_self⟩
/-- Over a proper-star ordered ring, `v.IsPartialIsometry ↔ IsStarProjection (vᴴ * v)`. -/
theorem isPartialIsometry_iff_isStarProjection_conjTranspose_mul_self :
    v.IsPartialIsometry ↔ IsStarProjection (v.conjTranspose * v) :=
  ⟨IsPartialIsometry.isStarProjection_conjTranspose_mul_self,
    fun h => .of_isIdempotentElem_conjTranspose_mul_self h.isIdempotentElem⟩
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
  obtain ⟨v, hv, hv', hvp⟩ := h.exists_matrix_mul_eq_self
  exact ⟨v, by rw [isPartialIsometry_iff, CStarMatrix.mul_assoc, hv, hvp], hv, hv'⟩
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
    (CStarMatrix.blockSum p₁ p₂).MurrayVonNeumannEquiv (CStarMatrix.blockSum q₁ q₂) := by
  rcases h₁.exists_isPartialIsometry with ⟨v₁, hv₁, rfl, rfl⟩
  rcases h₂.exists_isPartialIsometry with ⟨v₂, hv₂, rfl, rfl⟩
  simpa only [blockSum_conjTranspose, blockSum_mul] using (hv₁.blockSum hv₂).murrayVonNeumannEquiv
section
variable {p : CStarMatrix m m A} {q : CStarMatrix n n A}
/-- Non-unital `⋆`-algebra homomorphisms via `mapₙₐ` preserve `MurrayVonNeumannEquiv`. -/
protected theorem mapₙₐ [Semiring R] [NonUnitalSemiring A] [Module R A] [StarRing A]
    [NonUnitalSemiring B] [Module R B] [StarRing B] (φ : A →⋆ₙₐ[R] B)
    (h : p.MurrayVonNeumannEquiv q) : (CStarMatrix.mapₙₐ φ p).MurrayVonNeumannEquiv
      (CStarMatrix.mapₙₐ φ q) := by rw [mapₙₐ_eq_map, mapₙₐ_eq_map]; exact h.map φ
/-- Unital `⋆`-algebra homomorphisms via `mapₐ` preserve `MurrayVonNeumannEquiv`. -/
protected theorem mapₐ [DecidableEq m] [DecidableEq n] [CommSemiring R] [Semiring A] [Algebra R A]
    [StarRing A] [Semiring B] [Algebra R B] [StarRing B] (φ : A →⋆ₐ[R] B)
    (h : p.MurrayVonNeumannEquiv q) : (CStarMatrix.mapₐ φ p).MurrayVonNeumannEquiv
      (CStarMatrix.mapₐ φ q) := by rw [mapₐ_apply, mapₐ_apply]; exact h.map φ
/-- Finite block-diagonal amplification preserves rectangular `MurrayVonNeumannEquiv`. -/
protected theorem amplify (k : Type*) [Fintype k] [DecidableEq k] [NonUnitalSemiring A]
    [StarRing A] (h : p.MurrayVonNeumannEquiv q) :
    (CStarMatrix.amplify k p).MurrayVonNeumannEquiv (CStarMatrix.amplify k q) := by
  rcases h.exists_isPartialIsometry with ⟨v, hv, rfl, rfl⟩
  simpa [amplify_conjTranspose, amplify_mul] using (hv.amplify k).murrayVonNeumannEquiv
end
end MurrayVonNeumannEquiv
theorem murrayVonNeumannEquiv_comm [NonUnitalSemiring A] [StarRing A] {p : CStarMatrix m m A}
    {q : CStarMatrix n n A} : p.MurrayVonNeumannEquiv q ↔ q.MurrayVonNeumannEquiv p :=
  ⟨MurrayVonNeumannEquiv.symm, MurrayVonNeumannEquiv.symm⟩
section
variable [Semiring R] [NonUnitalSemiring A] [Module R A] [StarRing A]
private theorem mvn_reindexₐ_congr (R) [Semiring R] [Module R A] (e₁ : k ≃ l) (e₂ : m ≃ n)
    {p : CStarMatrix k k A} {q : CStarMatrix m m A} (h : p.MurrayVonNeumannEquiv q) :
    (reindexₐ R A e₁ p).MurrayVonNeumannEquiv (reindexₐ R A e₂ q) := by
  rcases h.exists_isPartialIsometry with ⟨v, hv, rfl, rfl⟩
  simpa [conjTranspose_reindexₗ, reindexₗ_mul, reindexₗ_self_eq_reindexₐ] using
    (hv.reindexₗ (R := R) e₂ e₁).murrayVonNeumannEquiv
/-- Reindexing a star projection along a bijection `e : m ≃ n` yields an equivalent projection. -/
theorem murrayVonNeumannEquiv_reindexₐ (e : m ≃ n) {p : CStarMatrix m m A}
    (hp : IsStarProjection p) : p.MurrayVonNeumannEquiv (reindexₐ R A e p) := by
  simpa using mvn_reindexₐ_congr R (.refl m) e (.refl hp)
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
section
variable [NonUnitalSemiring A] [StarRing A]
/-- Padding a star projection by a lower-right zero block yields an equivalent projection. -/
theorem murrayVonNeumannEquiv_blockSum_zero (n : Type*) [Fintype n] {p : CStarMatrix m m A}
    (hp : IsStarProjection p) : p.MurrayVonNeumannEquiv (blockSum p (0 : CStarMatrix n n A)) := by
  have hfr := fromRows_zero_mul_conjTranspose_fromRows_zero (n := n) hp
  have hv : (fromRows p (0 : CStarMatrix n m A)).IsPartialIsometry := by
    rw [isPartialIsometry_iff, hfr, blockSum_mul_fromRows, hp.isIdempotentElem.eq,
      CStarMatrix.zero_mul]
  have h1 : (fromRows p (0 : CStarMatrix n m A)).conjTranspose * fromRows p 0 = p := by
    simp [conjTranspose_eq_of_isSelfAdjoint hp.isSelfAdjoint, hp.isIdempotentElem.eq]
  simpa only [h1, hfr] using hv.murrayVonNeumannEquiv
/-- Swapping the two diagonal blocks of `blockSum p q` preserves Murray–von Neumann equivalence. -/
theorem murrayVonNeumannEquiv_blockSum_comm {p : CStarMatrix m m A} {q : CStarMatrix n n A}
    (hp : IsStarProjection p) (hq : IsStarProjection q) :
    (blockSum p q).MurrayVonNeumannEquiv (blockSum q p) :=
  reindexₐ_sumComm_blockSum (R := ℕ) p q ▸
    murrayVonNeumannEquiv_reindexₐ (R := ℕ) (.sumComm m n)
      (isStarProjection_blockSum_iff.mpr ⟨hp, hq⟩)
/-- `blockSum` of star projections is associative up to Murray–von Neumann equivalence. -/
theorem murrayVonNeumannEquiv_blockSum_assoc {p : CStarMatrix l l A} {q : CStarMatrix m m A}
    {r : CStarMatrix n n A} (hp : IsStarProjection p) (hq : IsStarProjection q)
    (hr : IsStarProjection r) : (blockSum (blockSum p q) r).MurrayVonNeumannEquiv
      (blockSum p (blockSum q r)) := reindexₐ_sumAssoc_blockSum (R := ℕ) p q r ▸
  murrayVonNeumannEquiv_reindexₐ (R := ℕ) (.sumAssoc l m n)
    (isStarProjection_blockSum_iff.mpr ⟨isStarProjection_blockSum_iff.mpr ⟨hp, hq⟩, hr⟩)
/-- Padding a star projection by an upper-left zero block yields an equivalent projection. -/
theorem murrayVonNeumannEquiv_zero_blockSum (m : Type*) [Fintype m] {q : CStarMatrix n n A}
    (hq : IsStarProjection q) : q.MurrayVonNeumannEquiv (blockSum (0 : CStarMatrix m m A) q) :=
  (murrayVonNeumannEquiv_blockSum_zero m hq).trans <|
    murrayVonNeumannEquiv_blockSum_comm hq (.zero _)
@[simp] theorem murrayVonNeumannEquiv_blockSum_zero_right_iff {p : CStarMatrix l l A}
    {q : CStarMatrix m m A} : p.MurrayVonNeumannEquiv (blockSum q (0 : CStarMatrix n n A)) ↔
      p.MurrayVonNeumannEquiv q := ⟨fun h => h.trans (murrayVonNeumannEquiv_blockSum_zero n
        (isStarProjection_blockSum_iff.mp h.isStarProjection_right).1).symm,
  fun h => h.trans (murrayVonNeumannEquiv_blockSum_zero n h.isStarProjection_right)⟩
@[simp] theorem murrayVonNeumannEquiv_blockSum_zero_left_iff {p : CStarMatrix l l A}
    {q : CStarMatrix n n A} : (blockSum p (0 : CStarMatrix m m A)).MurrayVonNeumannEquiv q ↔
      p.MurrayVonNeumannEquiv q := by
  rw [murrayVonNeumannEquiv_comm, murrayVonNeumannEquiv_blockSum_zero_right_iff,
    murrayVonNeumannEquiv_comm]
@[simp] theorem murrayVonNeumannEquiv_zero_blockSum_right_iff {p : CStarMatrix l l A}
    {q : CStarMatrix m m A} : p.MurrayVonNeumannEquiv (blockSum (0 : CStarMatrix n n A) q) ↔
      p.MurrayVonNeumannEquiv q := ⟨fun h => h.trans (murrayVonNeumannEquiv_zero_blockSum n
        (isStarProjection_blockSum_iff.mp h.isStarProjection_right).2).symm,
  fun h => h.trans (murrayVonNeumannEquiv_zero_blockSum n h.isStarProjection_right)⟩
@[simp] theorem murrayVonNeumannEquiv_zero_blockSum_left_iff {p : CStarMatrix m m A}
    {q : CStarMatrix n n A} : (blockSum (0 : CStarMatrix l l A) p).MurrayVonNeumannEquiv q ↔
      p.MurrayVonNeumannEquiv q := by
  rw [murrayVonNeumannEquiv_comm, murrayVonNeumannEquiv_zero_blockSum_right_iff,
    murrayVonNeumannEquiv_comm]
/-- For orthogonal star projections `p₁, p₂`, `p₁ + p₂` is equivalent to `blockSum p₁ p₂`. -/
theorem murrayVonNeumannEquiv_add_blockSum_of_mul_eq_zero {p₁ p₂ : CStarMatrix n n A}
    (hp₁ : IsStarProjection p₁) (hp₂ : IsStarProjection p₂) (h₁₂ : p₁ * p₂ = 0) :
    (p₁ + p₂).MurrayVonNeumannEquiv (blockSum p₁ p₂) := by
  have h1 : (fromRows p₁ p₂).conjTranspose * fromRows p₁ p₂ = p₁ + p₂ := by
    rw [conjTranspose_fromRows_mul_fromRows, conjTranspose_eq_of_isSelfAdjoint hp₁.isSelfAdjoint,
      conjTranspose_eq_of_isSelfAdjoint hp₂.isSelfAdjoint, hp₁.isIdempotentElem.eq,
      hp₂.isIdempotentElem.eq]
  have h2 := fromRows_mul_conjTranspose_fromRows_eq_blockSum hp₁ hp₂ h₁₂
  rw [← h1, ← h2]
  exact (IsPartialIsometry.fromRows_of_mul_eq_zero hp₁ hp₂ h₁₂).murrayVonNeumannEquiv
/-- Orthogonal sums of pairwise Murray–von Neumann equivalent projections are equivalent. -/
theorem MurrayVonNeumannEquiv.add_of_mul_eq_zero {p₁ p₂ : CStarMatrix m m A}
    {q₁ q₂ : CStarMatrix n n A} (h₁ : p₁.MurrayVonNeumannEquiv q₁)
    (h₂ : p₂.MurrayVonNeumannEquiv q₂) (hp : p₁ * p₂ = 0) (hq : q₁ * q₂ = 0) :
    (p₁ + p₂).MurrayVonNeumannEquiv (q₁ + q₂) :=
  (murrayVonNeumannEquiv_add_blockSum_of_mul_eq_zero h₁.isStarProjection_left
    h₂.isStarProjection_left hp).trans <| (h₁.blockSum h₂).trans
      (murrayVonNeumannEquiv_add_blockSum_of_mul_eq_zero h₁.isStarProjection_right
        h₂.isStarProjection_right hq).symm
end
/-- Conjugating a star projection `p` by an isometry `u` (`uᴴ * u = 1`) gives `p ∼ u * p * uᴴ`. -/
theorem murrayVonNeumannEquiv_conj_of_conjTranspose_mul_self_eq_one [DecidableEq n] [Semiring A]
    [StarRing A] {u : CStarMatrix m n A} (hu : u.conjTranspose * u = 1) {p : CStarMatrix n n A}
    (hp : IsStarProjection p) : p.MurrayVonNeumannEquiv (u * p * u.conjTranspose) := by
  have h1 := conjTranspose_mul_self_mul_of_conjTranspose_mul_self_eq_one_of_isStarProjection hu hp
  have h2 := self_mul_conjTranspose_mul_of_isStarProjection u hp
  simpa only [h1, h2] using
    (IsPartialIsometry.mul_of_conjTranspose_mul_self_eq_one_of_isStarProjection hu
      hp).murrayVonNeumannEquiv
/-- Unitary conjugacy over `Unitization R A` between projections from `A` gives `p ∼ q`. -/
theorem MurrayVonNeumannEquiv.of_unitary_conj_unitization (R : Type*) [DecidableEq n]
    [CommSemiring R] [StarRing R] [NonUnitalSemiring A] [StarRing A] [Module R A]
    [IsScalarTower R A A] [SMulCommClass R A A] [StarModule R A] {p q : CStarMatrix n n A}
    (hp : IsStarProjection p) (u : unitary (CStarMatrix n n (Unitization R A)))
    (hu : (u : CStarMatrix n n (Unitization R A)) * p.map (Unitization.inrNonUnitalStarAlgHom R A) *
        star (u : CStarMatrix n n (Unitization R A)) =
      q.map (Unitization.inrNonUnitalStarAlgHom R A)) : p.MurrayVonNeumannEquiv q := by
  let ι := Unitization.inrNonUnitalStarAlgHom R A
  have hι : Function.Injective fun M : CStarMatrix n n A => M.map ι :=
    CStarMatrix.map_injective Unitization.inr_injective
  let w : CStarMatrix n n (Unitization R A) := (u : CStarMatrix n n (Unitization R A)) * p.map ι
  let v : CStarMatrix n n A := ofMatrix fun i j => (w i j).snd
  have hv_map : v.map ι = w := CStarMatrix.ext fun i j => Unitization.ext (by
    simp only [map_apply, ι, Unitization.inrNonUnitalStarAlgHom_apply, Unitization.fst_inr]
    dsimp only [w]; rw [mul_apply, ← Unitization.fstHom_apply, map_sum]
    exact (Finset.sum_eq_zero fun k _ => by simp [ι, Unitization.fst_mul]).symm) rfl
  have hpι : IsStarProjection (p.map ι) := by rw [← mapₙₐ_eq_map]; exact hp.map (mapₙₐ ι)
  have hv : v.IsPartialIsometry := hι <| by
    simpa only [map_mul, map_conjTranspose, hv_map] using
      (IsPartialIsometry.unitary_mul_of_isStarProjection u hpι).mul_conjTranspose_mul_self
  have hvp : v.conjTranspose * v = p := hι <| by
    simpa only [map_mul, map_conjTranspose, hv_map] using
      conjTranspose_mul_self_unitary_mul_of_isStarProjection u hpι
  have hvq : v * v.conjTranspose = q := hι <| by
    simpa only [map_mul, map_conjTranspose, hv_map, w, ← hu, star_eq_conjTranspose, ι] using
      self_mul_conjTranspose_mul_of_isStarProjection u.val hpι
  exact hvp ▸ hvq ▸ hv.murrayVonNeumannEquiv
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
    exact ofMatrix.symm.injective <| by
      simpa using Matrix.fromBlocks_one_sub_mul_self_of_mul_eq (congrArg ofMatrix.symm hp)
        (congrArg ofMatrix.symm hq)
        (congrArg ofMatrix.symm (hv.mul_conjTranspose_eq_of_conjTranspose_mul_self_eq hp))
        (congrArg ofMatrix.symm (hv.mul_eq_self_of_conjTranspose_mul_self_eq hp))⟩
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
  exact ofMatrix.symm.injective <| by
    simpa [blockSum_def] using
      Matrix.fromBlocks_one_sub_mul_fromBlocks_mul_fromBlocks_one_sub_of_mul_eq
        (congrArg ofMatrix.symm hp) (congrArg ofMatrix.symm hq)
        (congrArg ofMatrix.symm (hv.mul_eq_self_of_conjTranspose_mul_self_eq hp))
end IsPartialIsometry

section
variable (v : CStarMatrix n m A) (p : CStarMatrix m m A) (q : CStarMatrix n n A)
/-- Unit-free `(2⁻¹ : ℝ) • fromBlocks p (-v.conjTranspose) (-v) q`, matching `2⁻¹ • (1 - w)`. -/
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
  simp only [conjTranspose_smul, conjTranspose_eq_of_isSelfAdjoint hp_proj.isSelfAdjoint,
    star_mul, star_neg, Complex.star_def, Complex.conj_ofReal, Complex.conj_I, neg_neg,
    CStarMatrix.smul_mul_smul, hp_proj.isIdempotentElem.eq, hq, fromBlocks_inj,
    hv.mul_conjTranspose_eq_of_conjTranspose_mul_self_eq hp,
    hv.mul_eq_self_of_conjTranspose_mul_self_eq hp]
  exact ⟨by congr 1; ring, by congr 1; ring, trivial,
    by congr 1; linear_combination -(Real.sin (Real.pi * t / 2) : ℂ) ^ 2 * Complex.I_sq⟩
private theorem isPartialIsometry_stabilizedProjRotRows (t : ℝ) :
    (stabilizedProjRotRows v p t).IsPartialIsometry := by
  set θ := Real.pi * t / 2
  have hp_proj : IsStarProjection p := hp ▸ hv.isStarProjection_conjTranspose_mul_self
  have hinit : (stabilizedProjRotRows v p t).conjTranspose * stabilizedProjRotRows v p t = p := by
    rw [stabilizedProjRotRows, conjTranspose_fromRows_mul_fromRows]
    simp only [conjTranspose_smul, conjTranspose_eq_of_isSelfAdjoint hp_proj.isSelfAdjoint,
      star_mul, star_neg, Complex.star_def, Complex.conj_ofReal, Complex.conj_I, neg_neg,
      CStarMatrix.smul_mul_smul, hp_proj.isIdempotentElem.eq, hp, ← add_smul]
    rw [show (Real.cos θ : ℂ) * ↑(Real.cos θ) +
        ↑(Real.sin θ) * Complex.I * (-Complex.I * ↑(Real.sin θ)) = 1 by
      linear_combination (by simp : (Real.cos θ : ℂ) ^ 2 + (Real.sin θ : ℂ) ^ 2 = 1) -
        (Real.sin θ : ℂ) ^ 2 * Complex.I_sq, one_smul]
  rw [isPartialIsometry_iff, CStarMatrix.mul_assoc, hinit, stabilizedProjRotRows, fromRows_mul,
    CStarMatrix.smul_mul, CStarMatrix.smul_mul, hp_proj.isIdempotentElem.eq,
    hv.mul_eq_self_of_conjTranspose_mul_self_eq hp]
/-- Every point on `stabilizedProjRot v p q` for a partial isometry `v` is a star projection. -/
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
  refine ((hv.isStarProjection_stabilizedNegProj hp hq).coe_expUnitary_smul θ).trans ?_
  rw [stabilizedNegProj_def, show (2⁻¹ : ℝ) • fromBlocks p (-v.conjTranspose) (-v) q =
    ((2⁻¹ : ℝ) : ℂ) • _ from ext fun _ _ => (Complex.coe_smul _ _).symm, smul_smul]
  congr 2; push_cast; rfl
/-- At `π`, the exponential unitary of `stabilizedNegProj v p q` is `stabilizedConjUnitary`. -/
theorem expUnitary_pi_smul_stabilizedNegProj :
    selfAdjoint.expUnitary (Real.pi • ⟨stabilizedNegProj v p q,
      (hv.isStarProjection_stabilizedNegProj hp hq).isSelfAdjoint⟩) =
      hv.stabilizedConjUnitary hp hq :=
  (congrArg (fun x => selfAdjoint.expUnitary (Real.pi • x))
    (Subtype.ext (hv.stabilizedNegProj_eq_half_one_sub hp hq))).trans
      (Unitary.expUnitary_pi_smul_half_one_sub _ (hv.isSelfAdjoint_stabilizedConjUnitary hp hq))
/-- Path `t ↦ expUnitary ((t * π) • stabilizedNegProj)` from `1` to `stabilizedConjUnitary`. -/
def stabilizedConjUnitaryPath :
    Path (1 : unitary (CStarMatrix (m ⊕ n) (m ⊕ n) A)) (hv.stabilizedConjUnitary hp hq) :=
  (selfAdjoint.expUnitaryPathToOne (Real.pi • ⟨stabilizedNegProj v p q,
    (hv.isStarProjection_stabilizedNegProj hp hq).isSelfAdjoint⟩)).cast
    rfl (hv.expUnitary_pi_smul_stabilizedNegProj hp hq).symm
@[simp low] theorem stabilizedConjUnitaryPath_apply (t : unitInterval) :
    (hv.stabilizedConjUnitaryPath hp hq) t = selfAdjoint.expUnitary (((t : ℝ) * Real.pi) •
      ⟨stabilizedNegProj v p q, (hv.isStarProjection_stabilizedNegProj hp hq).isSelfAdjoint⟩) := by
  rw [stabilizedConjUnitaryPath, Path.cast_coe, selfAdjoint.expUnitaryPathToOne_apply]
  congr 1; exact Subtype.ext (ext fun _ _ => smul_smul (t : ℝ) Real.pi _)
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
  have hα : α = (z ^ 2 - 1) * 2⁻¹ := by
    rw [hα_def, show (t : ℂ) * Real.pi * Complex.I = ((Real.pi * t / 2 : ℝ) : ℂ) * Complex.I +
        ((Real.pi * t / 2 : ℝ) : ℂ) * Complex.I by push_cast; ring, Complex.exp_add,
      Complex.exp_ofReal_mul_I, ← hc, ← hs, ← hz, sq]
  have h1α : 1 + α = z * c := by
    rw [hα, hz]; linear_combination -((1 : ℂ) / 2) * hcs + (s ^ 2 / 2) * Complex.I_sq
  have hnα : -α = z * (-Complex.I * s) := by
    rw [hα, hz]; linear_combination -((1 : ℂ) / 2) * hcs + (s ^ 2 / 2) * Complex.I_sq
  rw [hv.coe_expUnitary_smul_stabilizedNegProj hp hq (t * Real.pi), Complex.ofReal_mul, ← hα_def,
    CStarMatrix.add_mul, CStarMatrix.one_mul, CStarMatrix.smul_mul, fromBlocks_mul_fromRows]
  simp [stabilizedProjRotRows, ← hc, ← hs,
    (hp ▸ hv.isStarProjection_conjTranspose_mul_self).isIdempotentElem.eq,
    hv.mul_eq_self_of_conjTranspose_mul_self_eq hp, show p + α • p = (z * c) • p by
      rw [← h1α, add_smul, one_smul], show -(α • v) = (z * (-Complex.I * s)) • v by
      rw [← neg_smul, hnα], smul_smul]
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
  -- Factor `blockSum p 0 = F * Fᴴ` so `U * blockSum p 0 * Uᴴ = (U * F) * (U * F)ᴴ`.
  rw [star_eq_conjTranspose, ← fromRows_zero_mul_conjTranspose_fromRows_zero
      (hp ▸ hv.isStarProjection_conjTranspose_mul_self), ← CStarMatrix.mul_assoc,
    CStarMatrix.mul_assoc (_ * fromRows p 0), ← conjTranspose_mul,
    hv.expUnitary_smul_stabilizedNegProj_mul_fromRows hp hq t, conjTranspose_smul,
    CStarMatrix.smul_mul_smul, hzz, one_smul, hv.stabilizedProjRotRows_mul_conjTranspose hp hq t]
end
/-- Over a unital C⋆-algebra, `stabilizedConjUnitary` is joined to `1` in `unitary`. -/
theorem joined_one_stabilizedConjUnitary [DecidableEq m] [DecidableEq n] [CStarAlgebra A]
    (hv : v.IsPartialIsometry) (hp : v.conjTranspose * v = p) (hq : v * v.conjTranspose = q) :
    Joined (1 : unitary (CStarMatrix (m ⊕ n) (m ⊕ n) A)) (hv.stabilizedConjUnitary hp hq) := by
  let _ : PartialOrder A := CStarAlgebra.spectralOrder A
  have _ : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
  exact ⟨hv.stabilizedConjUnitaryPath hp hq⟩
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
  ⟨hv.stabilizedConjUnitary hp hq,
    hv.isSelfAdjoint_stabilizedConjUnitary hp hq, hv.stabilizedConjUnitary_conj hp hq⟩
/-- Over a unital C⋆-algebra, equivalent projections are conjugate by a unitary joined to `1`. -/
theorem MurrayVonNeumannEquiv.exists_joined_one_unitary_conj_blockSum_eq
    [DecidableEq m] [DecidableEq n] [CStarAlgebra A] (h : p.MurrayVonNeumannEquiv q) :
    ∃ w : unitary (CStarMatrix (m ⊕ n) (m ⊕ n) A), Joined 1 w ∧
      (w : CStarMatrix (m ⊕ n) (m ⊕ n) A) * blockSum p 0 *
        star (w : CStarMatrix (m ⊕ n) (m ⊕ n) A) = blockSum 0 q :=
  let ⟨_, hv, hp, hq⟩ := h.exists_isPartialIsometry
  ⟨hv.stabilizedConjUnitary hp hq,
    hv.joined_one_stabilizedConjUnitary hp hq, hv.stabilizedConjUnitary_conj hp hq⟩
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
