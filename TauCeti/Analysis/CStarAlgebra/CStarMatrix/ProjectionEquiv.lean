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
import TauCeti.Data.Matrix.Block

/-!
# Rectangular partial isometries and Murray–von Neumann equivalence on `CStarMatrix`

Comparing matrix projections across different sizes (for `V(A)` and `K₀(A)` of a possibly
non-unital C⋆-algebra `A`) requires rectangular partial isometries and block-sum stabilization. Two
elements `p : CStarMatrix m m A` and `q : CStarMatrix n n A` are Murray–von Neumann equivalent when
there is a partial isometry `v : CStarMatrix n m A` with `v.conjTranspose * v = p` and
`v * v.conjTranspose = q`:

* Over star semirings (`[NonUnitalSemiring A] [StarRing A]`): `MurrayVonNeumannEquiv` is symmetric,
  transitive, reflexive on star projections, and compatible with `blockSum`, orthogonal sums
  (`add_of_mul_eq_zero`), entrywise homomorphisms (`map`, `mapₙₐ`, `mapₐ`), `amplify`, `reindexₐ`,
  zero-padding, and unitization descent (`of_unitary_conj_unitization`). Over a star-ordered ring
  with proper star, `v.IsPartialIsometry` holds whenever `v.conjTranspose * v` or
  `v * v.conjTranspose` is idempotent.
* Over unital star rings (`[Ring A] [StarRing A]`): `stabilizedConjUnitary` is the self-adjoint
  unitary `fromBlocks (1 - p) v.conjTranspose v (1 - q)` conjugating `blockSum p 0` to
  `blockSum 0 q`.
* Over C⋆-algebras: for `[CStarAlgebra A]`, `stabilizedConjUnitaryPath` joins `1` to
  `stabilizedConjUnitary` via `t ↦ expUnitary ((t * π) • stabilizedNegProj v p q)`; for general
  `[NonUnitalCStarAlgebra A]`, `stabilizedProjPath` gives the unit-free continuous projection path
  from `blockSum p 0` to `blockSum 0 q`.

## Main definitions and statements

* `CStarMatrix.IsPartialIsometry`, `CStarMatrix.MurrayVonNeumannEquiv`,
  `CStarMatrix.isPartialIsometry_iff_isStarProjection_conjTranspose_mul_self`,
  `CStarMatrix.murrayVonNeumannEquiv_iff_exists_mul_eq`,
  `CStarMatrix.murrayVonNeumannEquiv_iff_exists_mul_eq_of_isIdempotentElem_right`.
* `CStarMatrix.MurrayVonNeumannEquiv.refl`, `symm`, `trans`, `blockSum`, `add_of_mul_eq_zero`,
  `of_unitary_conj_unitization`, `map`.
* `CStarMatrix.IsPartialIsometry.stabilizedConjUnitary`, `CStarMatrix.stabilizedNegProj`,
  `CStarMatrix.stabilizedProjRot`, `CStarMatrix.IsPartialIsometry.stabilizedConjUnitaryPath`,
  `CStarMatrix.IsPartialIsometry.stabilizedProjPath`,
  `CStarMatrix.MurrayVonNeumannEquiv.exists_isSelfAdjoint_unitary_conj_blockSum_eq`,
  `exists_joined_one_unitary_conj_blockSum_eq`, `joined_blockSum`.

## References

* B. Blackadar, *K-Theory for Operator Algebras*, 2nd ed., §4.6 and §5.1.
-/

public section

noncomputable section

open scoped Matrix ComplexOrder

namespace CStarMatrix
variable {k l m n o R A B F : Type*}

section
variable [Fintype m] [Fintype n] [Mul A] [AddCommMonoid A] [Star A]
/-- `v : CStarMatrix m n A` is a **partial isometry** when `v * v.conjTranspose * v = v`. -/
def IsPartialIsometry (v : CStarMatrix m n A) : Prop := v * v.conjTranspose * v = v
theorem isPartialIsometry_iff {v : CStarMatrix m n A} :
    v.IsPartialIsometry ↔ v * v.conjTranspose * v = v := Iff.rfl
theorem IsPartialIsometry.mul_conjTranspose_mul_self {v : CStarMatrix m n A}
    (hv : v.IsPartialIsometry) : v * v.conjTranspose * v = v := hv
end
/-- Square `CStarMatrix.IsPartialIsometry` coincides with `TauCeti.IsPartialIsometry`. -/
theorem isPartialIsometry_iff_starMul [Fintype n] [Mul A] [AddCommMonoid A] [Star A]
    {v : CStarMatrix n n A} : v.IsPartialIsometry ↔ TauCeti.IsPartialIsometry v := by
  rw [isPartialIsometry_iff, TauCeti.isPartialIsometry_iff, ← star_eq_conjTranspose]
namespace IsPartialIsometry
section
variable [Fintype m] [Fintype n]
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
@[simp] protected theorem zero [NonUnitalNonAssocSemiring A] [StarAddMonoid A] :
    (0 : CStarMatrix m n A).IsPartialIsometry := by simp [IsPartialIsometry]
section StarRing
variable [NonUnitalSemiring A] [StarRing A]
section
variable {v : CStarMatrix m n A}
/-- The conjugate transpose of a rectangular partial isometry is a partial isometry. -/
protected theorem conjTranspose (hv : v.IsPartialIsometry) : v.conjTranspose.IsPartialIsometry := by
  rw [isPartialIsometry_iff, conjTranspose_conjTranspose, CStarMatrix.mul_assoc]
  simpa only [conjTranspose_mul, conjTranspose_conjTranspose] using
    congrArg CStarMatrix.conjTranspose hv.mul_conjTranspose_mul_self
/-- Adjoint partial-isometry identity `v.conjTranspose * v * v.conjTranspose = v.conjTranspose`. -/
theorem conjTranspose_mul_self_mul_conjTranspose (hv : v.IsPartialIsometry) :
    v.conjTranspose * v * v.conjTranspose = v.conjTranspose := by
  simpa using hv.conjTranspose.mul_conjTranspose_mul_self
/-- Adjoint identity `v.conjTranspose * (v * v.conjTranspose) = v.conjTranspose`. -/
theorem conjTranspose_mul_self_mul_conjTranspose' (hv : v.IsPartialIsometry) :
    v.conjTranspose * (v * v.conjTranspose) = v.conjTranspose := by
  rw [← CStarMatrix.mul_assoc, hv.conjTranspose_mul_self_mul_conjTranspose]
/-- The initial projection `v.conjTranspose * v` of a partial isometry is a star projection. -/
theorem isStarProjection_conjTranspose_mul_self (hv : v.IsPartialIsometry) :
    IsStarProjection (v.conjTranspose * v) where
  isIdempotentElem := by
    rw [IsIdempotentElem, CStarMatrix.mul_assoc, ← CStarMatrix.mul_assoc v,
      hv.mul_conjTranspose_mul_self]
  isSelfAdjoint := by
    rw [isSelfAdjoint_iff, star_eq_conjTranspose, conjTranspose_mul, conjTranspose_conjTranspose]
/-- The final projection `v * v.conjTranspose` of a partial isometry is a star projection. -/
theorem isStarProjection_mul_conjTranspose_self (hv : v.IsPartialIsometry) :
    IsStarProjection (v * v.conjTranspose) := by
  simpa using hv.conjTranspose.isStarProjection_conjTranspose_mul_self
end
/-- Left-multiplying `v.conjTranspose` by the initial projection of `v` fixes `v.conjTranspose`. -/
theorem mul_conjTranspose_eq_of_conjTranspose_mul_self_eq {v : CStarMatrix n m A}
    {p : CStarMatrix m m A} (hv : v.IsPartialIsometry) (hp : v.conjTranspose * v = p) :
    p * v.conjTranspose = v.conjTranspose := by
  rw [← hp, hv.conjTranspose_mul_self_mul_conjTranspose]
/-- Right-multiplying `v.conjTranspose` by the final projection of `v` fixes `v.conjTranspose`. -/
theorem conjTranspose_mul_eq_of_mul_conjTranspose_self_eq {v : CStarMatrix n m A}
    {q : CStarMatrix n n A} (hv : v.IsPartialIsometry) (hq : v * v.conjTranspose = q) :
    v.conjTranspose * q = v.conjTranspose := by
  rw [← hq, hv.conjTranspose_mul_self_mul_conjTranspose']
end StarRing
end
@[simp] protected theorem one [Fintype n] [DecidableEq n] [Semiring A] [StarRing A] :
    (1 : CStarMatrix n n A).IsPartialIsometry :=
  isPartialIsometry_iff_starMul.mpr TauCeti.IsPartialIsometry.one
theorem of_isStarProjection [Fintype n] [Mul A] [AddCommMonoid A] [Star A]
    {p : CStarMatrix n n A} (hp : IsStarProjection p) : p.IsPartialIsometry :=
  isPartialIsometry_iff_starMul.mpr hp.isPartialIsometry
theorem of_mem_unitary [Fintype n] [DecidableEq n] [Semiring A] [StarRing A]
    {u : CStarMatrix n n A} (hu : u ∈ unitary (CStarMatrix n n A)) : u.IsPartialIsometry :=
  isPartialIsometry_iff_starMul.mpr (TauCeti.IsPartialIsometry.of_mem_unitary hu)
section ProperStar
variable [Fintype m] [Fintype n] [NonUnitalRing A] [StarRing A] [PartialOrder A]
  [StarOrderedRing A] [IsProperStar A] {v : CStarMatrix m n A}
/-- Over a proper-star ordered ring, `v` is a partial isometry if `v.conjTranspose * v` is
idempotent. -/
theorem of_isIdempotentElem_conjTranspose_mul_self
    (h : IsIdempotentElem (v.conjTranspose * v)) : v.IsPartialIsometry := by
  rw [isPartialIsometry_iff, ← sub_eq_zero, ← conjTranspose_mul_self_eq_zero]
  have h1 : (v * v.conjTranspose * v).conjTranspose = v.conjTranspose * v * v.conjTranspose := by
    rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, CStarMatrix.mul_assoc]
  have h4 : v.conjTranspose * (v * v.conjTranspose * v) = v.conjTranspose * v := by
    simpa only [CStarMatrix.mul_assoc] using h.eq
  have h2 : (v.conjTranspose * v * v.conjTranspose) * (v * v.conjTranspose * v) =
      v.conjTranspose * v := by rw [CStarMatrix.mul_assoc, h4, h.eq]
  have h3 : (v.conjTranspose * v * v.conjTranspose) * v = v.conjTranspose * v := by
    rw [CStarMatrix.mul_assoc, h.eq]
  rw [conjTranspose_sub, h1, CStarMatrix.sub_mul, CStarMatrix.mul_sub, CStarMatrix.mul_sub,
    h2, h3, h4, sub_self]
/-- Over a proper-star ordered ring, `v` is a partial isometry if `v * v.conjTranspose` is
idempotent. -/
theorem of_isIdempotentElem_mul_conjTranspose_self
    (h : IsIdempotentElem (v * v.conjTranspose)) : v.IsPartialIsometry := by
  have h' : IsIdempotentElem (v.conjTranspose.conjTranspose * v.conjTranspose) := by
    rwa [conjTranspose_conjTranspose]
  simpa only [conjTranspose_conjTranspose] using
    (of_isIdempotentElem_conjTranspose_mul_self h').conjTranspose
end ProperStar
section
variable [Fintype m] [Fintype n]
protected theorem blockSum [Fintype l] [Fintype o] [NonUnitalNonAssocSemiring A] [StarAddMonoid A]
    {v : CStarMatrix m l A} {w : CStarMatrix o n A}
    (hv : v.IsPartialIsometry) (hw : w.IsPartialIsometry) :
    (CStarMatrix.blockSum v w).IsPartialIsometry := by
  rw [isPartialIsometry_iff, blockSum_conjTranspose, blockSum_mul, blockSum_mul,
    hv.mul_conjTranspose_mul_self, hw.mul_conjTranspose_mul_self]
protected theorem reindexₗ [Fintype l] [Fintype o] [Semiring R] [NonUnitalNonAssocSemiring A]
    [Module R A] [Star A] (eₘ : m ≃ l) (eₙ : n ≃ o) {v : CStarMatrix m n A}
    (hv : v.IsPartialIsometry) : (CStarMatrix.reindexₗ R A eₘ eₙ v).IsPartialIsometry := by
  rw [isPartialIsometry_iff, reindexₗ_conjTranspose, reindexₗ_mul, reindexₗ_mul,
    hv.mul_conjTranspose_mul_self]
protected theorem reindexₐ [Semiring R] [AddCommMonoid A] [Mul A] [Module R A] [Star A]
    (e : m ≃ n) {v : CStarMatrix m m A} (hv : v.IsPartialIsometry) :
    (CStarMatrix.reindexₐ R A e v).IsPartialIsometry := by
  rw [isPartialIsometry_iff_starMul, TauCeti.isPartialIsometry_iff, ← map_star, ← _root_.map_mul,
    ← _root_.map_mul, (isPartialIsometry_iff_starMul.mp hv).mul_star_mul_self]
protected theorem map [NonUnitalNonAssocSemiring A] [Star A] [NonUnitalNonAssocSemiring B] [Star B]
    [FunLike F A B] [NonUnitalRingHomClass F A B] [StarHomClass F A B] (φ : F)
    {v : CStarMatrix m n A} (hv : v.IsPartialIsometry) : (v.map φ).IsPartialIsometry := by
  rw [isPartialIsometry_iff, ← map_conjTranspose, ← map_mul, ← map_mul,
    hv.mul_conjTranspose_mul_self]
protected theorem amplify (k : Type*) [Fintype k] [DecidableEq k] [NonUnitalNonAssocSemiring A]
    [StarAddMonoid A] {v : CStarMatrix m n A} (hv : v.IsPartialIsometry) :
    (CStarMatrix.amplify k v).IsPartialIsometry := by
  rw [isPartialIsometry_iff, amplify_conjTranspose, amplify_mul, amplify_mul,
    hv.mul_conjTranspose_mul_self]
end
end IsPartialIsometry

section
variable [Fintype n] [NonUnitalSemiring A] [StarRing A]
/-- For orthogonal star projections `p₁, p₂`, `fromRows p₁ p₂ * (fromRows p₁ p₂)ᴴ = blockSum p₁ p₂`.
-/
theorem fromRows_mul_conjTranspose_fromRows_eq_blockSum {p₁ p₂ : CStarMatrix n n A}
    (hp₁ : IsStarProjection p₁) (hp₂ : IsStarProjection p₂) (h₁₂ : p₁ * p₂ = 0) :
    fromRows p₁ p₂ * (fromRows p₁ p₂).conjTranspose = blockSum p₁ p₂ := by
  have h₂₁ : p₂ * p₁ = 0 := by
    rw [← hp₂.isSelfAdjoint.star_eq, ← hp₁.isSelfAdjoint.star_eq, ← star_mul, h₁₂, star_zero]
  rw [fromRows_mul_conjTranspose_fromRows, conjTranspose_eq_of_isSelfAdjoint hp₁.isSelfAdjoint,
    conjTranspose_eq_of_isSelfAdjoint hp₂.isSelfAdjoint, hp₁.isIdempotentElem.eq,
    hp₂.isIdempotentElem.eq, h₁₂, h₂₁, ← blockSum_def]
/-- Vertical row stack `fromRows p₁ p₂` of two orthogonal star projections is a partial isometry. -/
theorem IsPartialIsometry.fromRows_of_mul_eq_zero {p₁ p₂ : CStarMatrix n n A}
    (hp₁ : IsStarProjection p₁) (hp₂ : IsStarProjection p₂) (h₁₂ : p₁ * p₂ = 0) :
    (fromRows p₁ p₂).IsPartialIsometry := by
  rw [isPartialIsometry_iff, fromRows_mul_conjTranspose_fromRows_eq_blockSum hp₁ hp₂ h₁₂,
    blockSum_mul_fromRows, hp₁.isIdempotentElem.eq, hp₂.isIdempotentElem.eq]
/-- Right-multiplying `M` by a star projection `p` gives `(M * p) * (M * p)ᴴ = M * p * Mᴴ`. -/
theorem self_mul_conjTranspose_mul_of_isStarProjection (M : CStarMatrix m n A)
    {p : CStarMatrix n n A} (hp : IsStarProjection p) :
    (M * p) * (M * p).conjTranspose = M * p * M.conjTranspose := by
  rw [conjTranspose_mul, conjTranspose_eq_of_isSelfAdjoint hp.isSelfAdjoint,
    CStarMatrix.mul_assoc, ← CStarMatrix.mul_assoc p, hp.isIdempotentElem.eq, CStarMatrix.mul_assoc]
end
section
variable [Fintype n] [DecidableEq n] [Semiring A] [StarRing A]
/-- Initial projection of `(u : CStarMatrix n n A) * p` for unitary `u` and star projection `p`. -/
theorem conjTranspose_mul_self_unitary_mul_of_isStarProjection (u : unitary (CStarMatrix n n A))
    {p : CStarMatrix n n A} (hp : IsStarProjection p) :
    ((u : CStarMatrix n n A) * p).conjTranspose * ((u : CStarMatrix n n A) * p) = p := by
  rw [← star_eq_conjTranspose]; exact hp.star_mul_self_unitary_mul u
/-- Left-multiplying a star projection `p` by a unitary `u` yields a partial isometry. -/
theorem IsPartialIsometry.unitary_mul_of_isStarProjection (u : unitary (CStarMatrix n n A))
    {p : CStarMatrix n n A} (hp : IsStarProjection p) :
    ((u : CStarMatrix n n A) * p).IsPartialIsometry :=
  isPartialIsometry_iff_starMul.mpr
    (TauCeti.IsPartialIsometry.unitary_mul_of_isStarProjection u hp)
end
section
variable [Fintype m] [Fintype n]
@[simp] theorem isPartialIsometry_conjTranspose_iff [NonUnitalSemiring A] [StarRing A]
    {v : CStarMatrix m n A} : v.conjTranspose.IsPartialIsometry ↔ v.IsPartialIsometry :=
  ⟨fun h => by simpa using h.conjTranspose, IsPartialIsometry.conjTranspose⟩
@[simp] theorem isPartialIsometry_blockSum_iff [Fintype l] [Fintype o]
    [NonUnitalNonAssocSemiring A] [StarAddMonoid A] {v : CStarMatrix m l A}
    {w : CStarMatrix o n A} :
    (blockSum v w).IsPartialIsometry ↔ v.IsPartialIsometry ∧ w.IsPartialIsometry := by
  rw [isPartialIsometry_iff, blockSum_conjTranspose, blockSum_mul, blockSum_mul, blockSum_inj]; rfl
@[simp] theorem isPartialIsometry_reindexₗ_iff [Fintype l] [Fintype o] [Semiring R]
    [NonUnitalNonAssocSemiring A] [Module R A] [Star A] (eₘ : m ≃ l) (eₙ : n ≃ o)
    {v : CStarMatrix m n A} : (reindexₗ R A eₘ eₙ v).IsPartialIsometry ↔ v.IsPartialIsometry :=
  ⟨fun h => by
    rw [← reindexₗ_refl (R := R) v, ← Equiv.self_trans_symm eₘ, ← Equiv.self_trans_symm eₙ,
      reindexₗ_trans]; exact h.reindexₗ eₘ.symm eₙ.symm, IsPartialIsometry.reindexₗ eₘ eₙ⟩
@[simp] theorem isPartialIsometry_reindexₐ_iff [Semiring R] [AddCommMonoid A] [Mul A] [Module R A]
    [Star A] (e : m ≃ n) {v : CStarMatrix m m A} :
    (reindexₐ R A e v).IsPartialIsometry ↔ v.IsPartialIsometry :=
  ⟨fun h => by
    have h' := h.reindexₐ (R := R) e.symm
    rwa [reindexₐ_symm, StarAlgEquiv.symm_apply_apply] at h', IsPartialIsometry.reindexₐ e⟩
@[simp] theorem isPartialIsometry_amplify_iff [Fintype k] [DecidableEq k] [Nonempty k]
    [NonUnitalNonAssocSemiring A] [StarAddMonoid A] {v : CStarMatrix m n A} :
    (amplify k v).IsPartialIsometry ↔ v.IsPartialIsometry := by
  rw [isPartialIsometry_iff, amplify_conjTranspose, amplify_mul, amplify_mul, amplify_inj]; rfl
end
section
variable [Fintype m] [Fintype n] [NonUnitalRing A] [StarRing A] [PartialOrder A]
  [StarOrderedRing A] [IsProperStar A] {v : CStarMatrix m n A}
theorem isPartialIsometry_iff_isIdempotentElem_conjTranspose_mul_self :
    v.IsPartialIsometry ↔ IsIdempotentElem (v.conjTranspose * v) :=
  ⟨fun hv => hv.isStarProjection_conjTranspose_mul_self.isIdempotentElem,
    IsPartialIsometry.of_isIdempotentElem_conjTranspose_mul_self⟩
theorem isPartialIsometry_iff_isIdempotentElem_mul_conjTranspose_self :
    v.IsPartialIsometry ↔ IsIdempotentElem (v * v.conjTranspose) :=
  ⟨fun hv => hv.isStarProjection_mul_conjTranspose_self.isIdempotentElem,
    IsPartialIsometry.of_isIdempotentElem_mul_conjTranspose_self⟩
/-- Over a proper-star ordered ring, `v.IsPartialIsometry ↔ IsStarProjection (v.conjTranspose * v)`.
-/
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
variable [Fintype m] [Fintype n] [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  {v : CStarMatrix m n A}
/-- Every rectangular partial isometry over a C⋆-algebra is a contraction (`‖v‖ ≤ 1`). -/
theorem IsPartialIsometry.norm_le_one (hv : v.IsPartialIsometry) : ‖v‖ ≤ 1 :=
  (sq_le_sq₀ (norm_nonneg v) zero_le_one).mp <| by
    simpa [norm_conjTranspose_mul_self] using
      IsStarProjection.norm_le _ hv.isStarProjection_conjTranspose_mul_self
/-- Every nonzero rectangular partial isometry over a C⋆-algebra has norm `1`. -/
theorem IsPartialIsometry.norm_eq_one (hv : v.IsPartialIsometry) (hv0 : v ≠ 0) : ‖v‖ = 1 := by
  have hp := hv.isStarProjection_conjTranspose_mul_self
  have h4 : (‖v‖ ^ 2) * (‖v‖ ^ 2) = (‖v‖ ^ 2) * 1 := by
    rw [mul_one, ← norm_conjTranspose_mul_self v, ← CStarRing.norm_star_mul_self,
      hp.isSelfAdjoint.star_eq, hp.isIdempotentElem.eq]
  exact (sq_eq_sq₀ (norm_nonneg v) zero_le_one).mp <| by
    simpa using mul_left_cancel₀ (sq_pos_of_pos (norm_pos_iff.mpr hv0)).ne' h4
end
section
variable [Fintype m] [Fintype n] [Mul A] [AddCommMonoid A] [Star A]
/-- Rectangular **Murray–von Neumann equivalence** between `p : CStarMatrix m m A` and
`q : CStarMatrix n n A`: there exists a rectangular partial isometry `v : CStarMatrix n m A` with
`v.conjTranspose * v = p` and `v * v.conjTranspose = q`. -/
def MurrayVonNeumannEquiv (p : CStarMatrix m m A) (q : CStarMatrix n n A) : Prop :=
  ∃ v : CStarMatrix n m A, v.IsPartialIsometry ∧ v.conjTranspose * v = p ∧ v * v.conjTranspose = q
theorem murrayVonNeumannEquiv_iff {p : CStarMatrix m m A} {q : CStarMatrix n n A} :
    p.MurrayVonNeumannEquiv q ↔
      ∃ v : CStarMatrix n m A, v.IsPartialIsometry ∧ v.conjTranspose * v = p ∧
        v * v.conjTranspose = q := Iff.rfl
end
/-- On square matrices of the same size, `MurrayVonNeumannEquiv` is witnessed by a
`TauCeti.IsPartialIsometry` `v` satisfying `star v * v = p` and `v * star v = q`. -/
theorem murrayVonNeumannEquiv_iff_exists_star_mul [Fintype n] [Mul A] [AddCommMonoid A] [Star A]
    {p q : CStarMatrix n n A} : p.MurrayVonNeumannEquiv q ↔
      ∃ v : CStarMatrix n n A, TauCeti.IsPartialIsometry v ∧ star v * v = p ∧ v * star v = q := by
  simp_rw [murrayVonNeumannEquiv_iff, isPartialIsometry_iff_starMul, ← star_eq_conjTranspose]
section
variable [Fintype m] [Fintype n] [NonUnitalRing A] [StarRing A] [PartialOrder A]
  [StarOrderedRing A] [IsProperStar A] {p : CStarMatrix m m A} {q : CStarMatrix n n A}
/-- Over a star-ordered ring with proper star, an idempotent `p` is Murray–von Neumann equivalent
to `q` iff there exists `v` with `v.conjTranspose * v = p` and `v * v.conjTranspose = q`. -/
theorem murrayVonNeumannEquiv_iff_exists_mul_eq (hp : IsIdempotentElem p) :
    p.MurrayVonNeumannEquiv q ↔
      ∃ v : CStarMatrix n m A, v.conjTranspose * v = p ∧ v * v.conjTranspose = q :=
  ⟨fun ⟨v, _, hvp, hvq⟩ => ⟨v, hvp, hvq⟩,
    fun ⟨v, hvp, hvq⟩ => ⟨v, .of_isIdempotentElem_conjTranspose_mul_self (hvp.symm ▸ hp), hvp, hvq⟩⟩
/-- Over a star-ordered ring with proper star, `p` is Murray–von Neumann equivalent to an
idempotent `q` iff there exists `v` with `v.conjTranspose * v = p` and `v * v.conjTranspose = q`. -/
theorem murrayVonNeumannEquiv_iff_exists_mul_eq_of_isIdempotentElem_right
    (hq : IsIdempotentElem q) : p.MurrayVonNeumannEquiv q ↔
      ∃ v : CStarMatrix n m A, v.conjTranspose * v = p ∧ v * v.conjTranspose = q :=
  ⟨fun ⟨v, _, hvp, hvq⟩ => ⟨v, hvp, hvq⟩,
    fun ⟨v, hvp, hvq⟩ => ⟨v, .of_isIdempotentElem_mul_conjTranspose_self (hvq.symm ▸ hq), hvp, hvq⟩⟩
end
namespace MurrayVonNeumannEquiv
section
variable [Fintype m] [Fintype n] [NonUnitalSemiring A] [StarRing A]
  {p : CStarMatrix m m A} {q : CStarMatrix n n A}
theorem isStarProjection_left (h : p.MurrayVonNeumannEquiv q) : IsStarProjection p := by
  rcases h with ⟨v, hv, rfl, -⟩; exact hv.isStarProjection_conjTranspose_mul_self
theorem isStarProjection_right (h : p.MurrayVonNeumannEquiv q) : IsStarProjection q := by
  rcases h with ⟨v, hv, -, rfl⟩; exact hv.isStarProjection_mul_conjTranspose_self
/-- Rectangular Murray–von Neumann equivalence is symmetric. -/
@[symm] protected theorem symm (h : p.MurrayVonNeumannEquiv q) : q.MurrayVonNeumannEquiv p := by
  rcases h with ⟨v, hv, rfl, rfl⟩; exact ⟨v.conjTranspose, hv.conjTranspose, by simp, by simp⟩
end
/-- Rectangular Murray–von Neumann equivalence is transitive across arbitrary finite sizes. -/
@[trans] protected theorem trans [Fintype l] [Fintype m] [Fintype n] [NonUnitalSemiring A]
    [StarRing A] {p : CStarMatrix l l A} {q : CStarMatrix m m A} {r : CStarMatrix n n A}
    (hpq : p.MurrayVonNeumannEquiv q) (hqr : q.MurrayVonNeumannEquiv r) :
    p.MurrayVonNeumannEquiv r := by
  rcases hpq with ⟨v, hv, rfl, hvq⟩; rcases hqr with ⟨w, hw, hwq, rfl⟩
  have hinit : (w * v).conjTranspose * (w * v) = v.conjTranspose * v := by
    rw [conjTranspose_mul, CStarMatrix.mul_assoc, ← CStarMatrix.mul_assoc w.conjTranspose, hwq,
      ← hvq, hv.mul_conjTranspose_mul_self]
  have hfinal : (w * v) * (w * v).conjTranspose = w * w.conjTranspose := by
    rw [conjTranspose_mul, CStarMatrix.mul_assoc, ← CStarMatrix.mul_assoc v, hvq, ← hwq,
      hw.conjTranspose_mul_self_mul_conjTranspose]
  exact ⟨w * v, by rw [isPartialIsometry_iff, hfinal, ← CStarMatrix.mul_assoc,
    hw.mul_conjTranspose_mul_self], hinit, hfinal⟩
/-- A star projection is Murray–von Neumann equivalent to itself. -/
protected theorem refl [Fintype m] [Mul A] [AddCommMonoid A] [Star A]
    {p : CStarMatrix m m A} (hp : IsStarProjection p) : p.MurrayVonNeumannEquiv p :=
  have hp' : p.conjTranspose = p := conjTranspose_eq_of_isSelfAdjoint hp.isSelfAdjoint
  ⟨p, .of_isStarProjection hp, by rw [hp', hp.isIdempotentElem.eq],
    by rw [hp', hp.isIdempotentElem.eq]⟩
/-- `MurrayVonNeumannEquiv` is compatible with `blockSum`. -/
protected theorem blockSum [Fintype l] [Fintype m] [Fintype n] [Fintype o]
    [NonUnitalNonAssocSemiring A] [StarAddMonoid A] {p₁ : CStarMatrix l l A}
    {q₁ : CStarMatrix m m A} {p₂ : CStarMatrix n n A} {q₂ : CStarMatrix o o A}
    (h₁ : p₁.MurrayVonNeumannEquiv q₁) (h₂ : p₂.MurrayVonNeumannEquiv q₂) :
    (CStarMatrix.blockSum p₁ p₂).MurrayVonNeumannEquiv (CStarMatrix.blockSum q₁ q₂) := by
  rcases h₁ with ⟨v₁, hv₁, rfl, rfl⟩; rcases h₂ with ⟨v₂, hv₂, rfl, rfl⟩
  exact ⟨CStarMatrix.blockSum v₁ v₂, hv₁.blockSum hv₂, by simp, by simp⟩
section
variable [Fintype m] [Fintype n] {p : CStarMatrix m m A} {q : CStarMatrix n n A}
/-- Entrywise `⋆`-ring homomorphisms preserve rectangular `MurrayVonNeumannEquiv`. -/
protected theorem map [NonUnitalNonAssocSemiring A] [Star A] [NonUnitalNonAssocSemiring B] [Star B]
    [FunLike F A B] [NonUnitalRingHomClass F A B] [StarHomClass F A B] (φ : F)
    (h : p.MurrayVonNeumannEquiv q) : (p.map φ).MurrayVonNeumannEquiv (q.map φ) := by
  rcases h with ⟨v, hv, rfl, rfl⟩
  exact ⟨v.map φ, hv.map φ, by rw [← map_conjTranspose, ← map_mul],
    by rw [← map_conjTranspose, ← map_mul]⟩
/-- Non-unital `⋆`-algebra homomorphisms via `mapₙₐ` preserve `MurrayVonNeumannEquiv`. -/
protected theorem mapₙₐ [Semiring R] [NonUnitalNonAssocSemiring A] [Module R A] [Star A]
    [NonUnitalNonAssocSemiring B] [Module R B] [Star B] (φ : A →⋆ₙₐ[R] B)
    (h : p.MurrayVonNeumannEquiv q) :
    (CStarMatrix.mapₙₐ φ p).MurrayVonNeumannEquiv (CStarMatrix.mapₙₐ φ q) := h.map φ
/-- Unital `⋆`-algebra homomorphisms via `mapₐ` preserve `MurrayVonNeumannEquiv`. -/
protected theorem mapₐ [DecidableEq m] [DecidableEq n] [CommSemiring R] [Semiring A] [Algebra R A]
    [Star A] [Semiring B] [Algebra R B] [Star B] (φ : A →⋆ₐ[R] B)
    (h : p.MurrayVonNeumannEquiv q) :
    (CStarMatrix.mapₐ φ p).MurrayVonNeumannEquiv (CStarMatrix.mapₐ φ q) := by
  rw [mapₐ_apply, mapₐ_apply]; exact h.map φ
/-- Finite block-diagonal amplification preserves rectangular `MurrayVonNeumannEquiv`. -/
protected theorem amplify (k : Type*) [Fintype k] [DecidableEq k] [NonUnitalNonAssocSemiring A]
    [StarAddMonoid A] (h : p.MurrayVonNeumannEquiv q) :
    (CStarMatrix.amplify k p).MurrayVonNeumannEquiv (CStarMatrix.amplify k q) := by
  rcases h with ⟨v, hv, rfl, rfl⟩
  exact ⟨CStarMatrix.amplify k v, hv.amplify k, by rw [amplify_conjTranspose, amplify_mul],
    by rw [amplify_conjTranspose, amplify_mul]⟩
end
end MurrayVonNeumannEquiv

theorem murrayVonNeumannEquiv_comm [Fintype m] [Fintype n] [NonUnitalSemiring A] [StarRing A]
    {p : CStarMatrix m m A} {q : CStarMatrix n n A} :
    p.MurrayVonNeumannEquiv q ↔ q.MurrayVonNeumannEquiv p := ⟨.symm, .symm⟩
@[simp] theorem murrayVonNeumannEquiv_self_iff [Fintype m] [NonUnitalSemiring A] [StarRing A]
    {p : CStarMatrix m m A} : p.MurrayVonNeumannEquiv p ↔ IsStarProjection p :=
  ⟨MurrayVonNeumannEquiv.isStarProjection_left, MurrayVonNeumannEquiv.refl⟩
@[simp] theorem murrayVonNeumannEquiv_zero_right_iff [Fintype m] [Fintype n]
    [NonUnitalNonAssocSemiring A] [StarAddMonoid A] {p : CStarMatrix m m A} :
    p.MurrayVonNeumannEquiv (0 : CStarMatrix n n A) ↔ p = 0 :=
  ⟨fun ⟨v, hv, hvp, hv0⟩ => by
    rw [← hvp, ← hv.mul_conjTranspose_mul_self, hv0, CStarMatrix.zero_mul, conjTranspose_zero,
      CStarMatrix.zero_mul], fun h => h ▸ ⟨0, .zero, by simp, by simp⟩⟩
@[simp] theorem murrayVonNeumannEquiv_zero_left_iff [Fintype m] [Fintype n]
    [NonUnitalSemiring A] [StarAddMonoid A] {q : CStarMatrix n n A} :
    (0 : CStarMatrix m m A).MurrayVonNeumannEquiv q ↔ q = 0 :=
  ⟨fun ⟨v, hv, hv0, hvq⟩ => by
    rw [← hvq, ← hv.mul_conjTranspose_mul_self', hv0, CStarMatrix.mul_zero, CStarMatrix.zero_mul],
   fun h => h ▸ ⟨0, .zero, by simp, by simp⟩⟩
section
variable [NonUnitalSemiring A] [StarRing A]
/-- Padding a star projection by a lower-right zero block yields an equivalent projection. -/
theorem murrayVonNeumannEquiv_blockSum_zero (n : Type*) [Fintype m] [Fintype n]
    {p : CStarMatrix m m A} (hp : IsStarProjection p) :
    p.MurrayVonNeumannEquiv (blockSum p (0 : CStarMatrix n n A)) := by
  have hpt : p.conjTranspose = p := conjTranspose_eq_of_isSelfAdjoint hp.isSelfAdjoint
  have hfr : fromRows p (0 : CStarMatrix n m A) *
      (fromRows p (0 : CStarMatrix n m A)).conjTranspose = blockSum p 0 := by
    rw [fromRows_mul_conjTranspose_fromRows]; simp [hpt, hp.isIdempotentElem.eq, blockSum_def]
  exact ⟨fromRows p 0, by rw [isPartialIsometry_iff, hfr, blockSum_mul_fromRows,
    hp.isIdempotentElem.eq, CStarMatrix.zero_mul], by simp [hpt, hp.isIdempotentElem.eq], hfr⟩
/-- Reindexing a star projection along a bijection `e : m ≃ n` yields an equivalent projection. -/
theorem murrayVonNeumannEquiv_reindexₐ [Fintype m] [Fintype n] [Semiring R] [Module R A]
    (e : m ≃ n) {p : CStarMatrix m m A} (hp : IsStarProjection p) :
    p.MurrayVonNeumannEquiv (reindexₐ R A e p) := by
  have hpt : p.conjTranspose = p := conjTranspose_eq_of_isSelfAdjoint hp.isSelfAdjoint
  refine ⟨reindexₗ R A e (Equiv.refl m) p,
    (IsPartialIsometry.of_isStarProjection hp).reindexₗ e (Equiv.refl m), ?_, ?_⟩
  · rw [reindexₗ_conjTranspose, reindexₗ_mul, hpt, hp.isIdempotentElem.eq, reindexₗ_refl]
  · rw [reindexₗ_conjTranspose, reindexₗ_mul, hpt, hp.isIdempotentElem.eq,
      reindexₗ_self_eq_reindexₐ]
/-- Swapping the two diagonal blocks of `blockSum p q` preserves Murray–von Neumann equivalence. -/
theorem murrayVonNeumannEquiv_blockSum_comm [Fintype m] [Fintype n]
    {p : CStarMatrix m m A} {q : CStarMatrix n n A}
    (hp : IsStarProjection p) (hq : IsStarProjection q) :
    (blockSum p q).MurrayVonNeumannEquiv (blockSum q p) := by
  rw [← reindexₐ_sumComm_blockSum (R := ℕ) p q]
  exact murrayVonNeumannEquiv_reindexₐ (R := ℕ) (Equiv.sumComm m n)
    (isStarProjection_blockSum_iff.mpr ⟨hp, hq⟩)
/-- Padding a star projection by an upper-left zero block yields an equivalent projection. -/
theorem murrayVonNeumannEquiv_zero_blockSum (m : Type*) [Fintype m] [Fintype n]
    {q : CStarMatrix n n A} (hq : IsStarProjection q) :
    q.MurrayVonNeumannEquiv (blockSum (0 : CStarMatrix m m A) q) :=
  (murrayVonNeumannEquiv_blockSum_zero m hq).trans
    (murrayVonNeumannEquiv_blockSum_comm hq (.zero _))
section
variable [Fintype l] [Fintype m] [Fintype n]
@[simp] theorem murrayVonNeumannEquiv_blockSum_zero_right_iff
    {p : CStarMatrix l l A} {q : CStarMatrix m m A} :
    p.MurrayVonNeumannEquiv (blockSum q (0 : CStarMatrix n n A)) ↔ p.MurrayVonNeumannEquiv q :=
  ⟨fun h => h.trans (murrayVonNeumannEquiv_blockSum_zero n
      (isStarProjection_blockSum_iff.mp h.isStarProjection_right).1).symm,
   fun h => h.trans (murrayVonNeumannEquiv_blockSum_zero n h.isStarProjection_right)⟩
@[simp] theorem murrayVonNeumannEquiv_blockSum_zero_left_iff
    {p : CStarMatrix l l A} {q : CStarMatrix n n A} :
    (blockSum p (0 : CStarMatrix m m A)).MurrayVonNeumannEquiv q ↔ p.MurrayVonNeumannEquiv q := by
  rw [murrayVonNeumannEquiv_comm, murrayVonNeumannEquiv_blockSum_zero_right_iff,
    murrayVonNeumannEquiv_comm]
@[simp] theorem murrayVonNeumannEquiv_reindexₐ_right_iff [Semiring R] [Module R A] (e : m ≃ n)
    {p : CStarMatrix l l A} {q : CStarMatrix m m A} :
    p.MurrayVonNeumannEquiv (reindexₐ R A e q) ↔ p.MurrayVonNeumannEquiv q :=
  ⟨fun h => by
    have h' := h.trans (murrayVonNeumannEquiv_reindexₐ (R := R) e.symm h.isStarProjection_right)
    rwa [← StarAlgEquiv.trans_apply, ← reindexₐ_trans, Equiv.self_trans_symm, reindexₐ_refl] at h',
   fun h => h.trans (murrayVonNeumannEquiv_reindexₐ (R := R) e h.isStarProjection_right)⟩
@[simp] theorem murrayVonNeumannEquiv_reindexₐ_left_iff [Semiring R] [Module R A] (e : l ≃ m)
    {p : CStarMatrix l l A} {q : CStarMatrix n n A} :
    (reindexₐ R A e p).MurrayVonNeumannEquiv q ↔ p.MurrayVonNeumannEquiv q := by
  rw [murrayVonNeumannEquiv_comm, murrayVonNeumannEquiv_reindexₐ_right_iff,
    murrayVonNeumannEquiv_comm]
/-- `blockSum` of star projections is associative up to Murray–von Neumann equivalence. -/
theorem murrayVonNeumannEquiv_blockSum_assoc {p : CStarMatrix l l A} {q : CStarMatrix m m A}
    {r : CStarMatrix n n A} (hp : IsStarProjection p) (hq : IsStarProjection q)
    (hr : IsStarProjection r) :
    (blockSum (blockSum p q) r).MurrayVonNeumannEquiv (blockSum p (blockSum q r)) := by
  rw [← reindexₐ_sumAssoc_blockSum (R := ℕ) p q r]
  exact murrayVonNeumannEquiv_reindexₐ (R := ℕ) (Equiv.sumAssoc l m n)
    (isStarProjection_blockSum_iff.mpr ⟨isStarProjection_blockSum_iff.mpr ⟨hp, hq⟩, hr⟩)
@[simp] theorem murrayVonNeumannEquiv_zero_blockSum_right_iff
    {p : CStarMatrix l l A} {q : CStarMatrix n n A} :
    p.MurrayVonNeumannEquiv (blockSum (0 : CStarMatrix m m A) q) ↔ p.MurrayVonNeumannEquiv q :=
  ⟨fun h => h.trans (murrayVonNeumannEquiv_zero_blockSum m
      (isStarProjection_blockSum_iff.mp h.isStarProjection_right).2).symm,
   fun h => h.trans (murrayVonNeumannEquiv_zero_blockSum m h.isStarProjection_right)⟩
@[simp] theorem murrayVonNeumannEquiv_zero_blockSum_left_iff
    {p : CStarMatrix m m A} {q : CStarMatrix n n A} :
    (blockSum (0 : CStarMatrix l l A) p).MurrayVonNeumannEquiv q ↔ p.MurrayVonNeumannEquiv q := by
  rw [murrayVonNeumannEquiv_comm, murrayVonNeumannEquiv_zero_blockSum_right_iff,
    murrayVonNeumannEquiv_comm]
end
/-- For orthogonal star projections `p₁, p₂`, `p₁ + p₂` is equivalent to `blockSum p₁ p₂`. -/
theorem murrayVonNeumannEquiv_add_blockSum_of_mul_eq_zero [Fintype n] {p₁ p₂ : CStarMatrix n n A}
    (hp₁ : IsStarProjection p₁) (hp₂ : IsStarProjection p₂) (h₁₂ : p₁ * p₂ = 0) :
    (p₁ + p₂).MurrayVonNeumannEquiv (blockSum p₁ p₂) :=
  ⟨fromRows p₁ p₂, .fromRows_of_mul_eq_zero hp₁ hp₂ h₁₂, by
    rw [conjTranspose_fromRows_mul_fromRows, conjTranspose_eq_of_isSelfAdjoint hp₁.isSelfAdjoint,
      conjTranspose_eq_of_isSelfAdjoint hp₂.isSelfAdjoint, hp₁.isIdempotentElem.eq,
      hp₂.isIdempotentElem.eq], fromRows_mul_conjTranspose_fromRows_eq_blockSum hp₁ hp₂ h₁₂⟩
/-- Orthogonal sums of pairwise Murray–von Neumann equivalent projections are equivalent. -/
theorem MurrayVonNeumannEquiv.add_of_mul_eq_zero [Fintype m] [Fintype n]
    {p₁ p₂ : CStarMatrix m m A} {q₁ q₂ : CStarMatrix n n A}
    (h₁ : p₁.MurrayVonNeumannEquiv q₁) (h₂ : p₂.MurrayVonNeumannEquiv q₂)
    (hp : p₁ * p₂ = 0) (hq : q₁ * q₂ = 0) : (p₁ + p₂).MurrayVonNeumannEquiv (q₁ + q₂) :=
  (murrayVonNeumannEquiv_add_blockSum_of_mul_eq_zero h₁.isStarProjection_left
    h₂.isStarProjection_left hp).trans <| (h₁.blockSum h₂).trans
      (murrayVonNeumannEquiv_add_blockSum_of_mul_eq_zero h₁.isStarProjection_right
        h₂.isStarProjection_right hq).symm
end
/-- Unitary conjugation in `CStarMatrix n n A` yields a Murray–von Neumann equivalent projection. -/
theorem murrayVonNeumannEquiv_unitary_conj [Fintype n] [DecidableEq n] [Semiring A] [StarRing A]
    (u : unitary (CStarMatrix n n A)) {p : CStarMatrix n n A} (hp : IsStarProjection p) :
    p.MurrayVonNeumannEquiv ((u : CStarMatrix n n A) * p * star (u : CStarMatrix n n A)) :=
  ⟨(u : CStarMatrix n n A) * p, .unitary_mul_of_isStarProjection u hp,
    conjTranspose_mul_self_unitary_mul_of_isStarProjection u hp, by
      rw [star_eq_conjTranspose]; exact self_mul_conjTranspose_mul_of_isStarProjection _ hp⟩
/-- Unitary conjugacy in `CStarMatrix n n (Unitization R A)` between projections from `A` implies
Murray–von Neumann equivalence in `CStarMatrix n n A`. -/
theorem MurrayVonNeumannEquiv.of_unitary_conj_unitization (R : Type*) [Fintype n] [DecidableEq n]
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
    have hw_fst : (w i j).fst = 0 := by
      dsimp only [w]; rw [mul_apply, ← Unitization.fstHom_apply, map_sum]
      exact Finset.sum_eq_zero fun k _ => by simp [ι, Unitization.fst_mul]
    simp [ι, hw_fst]) rfl
  have hpι : IsStarProjection (p.map ι) := hp.map (mapₙₐ ι)
  refine ⟨v, ?_, ?_, ?_⟩
  · rw [isPartialIsometry_iff]; apply hι; dsimp only
    rw [map_mul, map_mul, map_conjTranspose, hv_map]
    exact (IsPartialIsometry.unitary_mul_of_isStarProjection u hpι).mul_conjTranspose_mul_self
  · apply hι; dsimp only; rw [map_mul, map_conjTranspose, hv_map]
    exact conjTranspose_mul_self_unitary_mul_of_isStarProjection u hpι
  · apply hι; dsimp only; rw [map_mul, map_conjTranspose, hv_map, ← hu, star_eq_conjTranspose]
    exact self_mul_conjTranspose_mul_of_isStarProjection _ hpι
namespace IsPartialIsometry
variable [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] [Ring A] [StarRing A]
  {v : CStarMatrix n m A} {p : CStarMatrix m m A} {q : CStarMatrix n n A}
private theorem isSelfAdjoint_fromBlocks_one_sub (hv : v.IsPartialIsometry)
    (hp : v.conjTranspose * v = p) (hq : v * v.conjTranspose = q) :
    IsSelfAdjoint (fromBlocks (1 - p) v.conjTranspose v (1 - q)) := by
  have hp_proj : IsStarProjection p := hp ▸ hv.isStarProjection_conjTranspose_mul_self
  have hq_proj : IsStarProjection q := hq ▸ hv.isStarProjection_mul_conjTranspose_self
  simp [isSelfAdjoint_iff, hp_proj.isSelfAdjoint.star_eq, hq_proj.isSelfAdjoint.star_eq]
/-- Self-adjoint unitary `fromBlocks (1 - p) v.conjTranspose v (1 - q)` conjugating `blockSum p 0`
to `blockSum 0 q` when `v.conjTranspose * v = p` and `v * v.conjTranspose = q`. -/
def stabilizedConjUnitary (hv : v.IsPartialIsometry) (hp : v.conjTranspose * v = p)
    (hq : v * v.conjTranspose = q) : unitary (CStarMatrix (m ⊕ n) (m ⊕ n) A) :=
  ⟨fromBlocks (1 - p) v.conjTranspose v (1 - q), by
    have hw_sa := (hv.isSelfAdjoint_fromBlocks_one_sub hp hq).star_eq
    have hw_sq : fromBlocks (1 - p) v.conjTranspose v (1 - q) *
        fromBlocks (1 - p) v.conjTranspose v (1 - q) = 1 := ofMatrix.symm.injective <| by
      simpa using Matrix.fromBlocks_one_sub_mul_self_of_mul_eq (congrArg ofMatrix.symm hp)
        (congrArg ofMatrix.symm hq)
        (congrArg ofMatrix.symm (hv.mul_conjTranspose_eq_of_conjTranspose_mul_self_eq hp))
        (congrArg ofMatrix.symm (hv.mul_eq_self_of_conjTranspose_mul_self_eq hp))
    exact Unitary.mem_iff.mpr ⟨by rw [hw_sa, hw_sq], by rw [hw_sa, hw_sq]⟩⟩
@[simp] theorem coe_stabilizedConjUnitary (hv : v.IsPartialIsometry) (hp : v.conjTranspose * v = p)
    (hq : v * v.conjTranspose = q) :
    ((hv.stabilizedConjUnitary hp hq : unitary (CStarMatrix (m ⊕ n) (m ⊕ n) A)) :
      CStarMatrix (m ⊕ n) (m ⊕ n) A) = fromBlocks (1 - p) v.conjTranspose v (1 - q) := (rfl)
/-- The stabilized conjugating unitary `stabilizedConjUnitary` is self-adjoint. -/
theorem isSelfAdjoint_stabilizedConjUnitary (hv : v.IsPartialIsometry)
    (hp : v.conjTranspose * v = p) (hq : v * v.conjTranspose = q) :
    IsSelfAdjoint ((hv.stabilizedConjUnitary hp hq : unitary _) : CStarMatrix (m ⊕ n) (m ⊕ n) A) :=
  hv.isSelfAdjoint_fromBlocks_one_sub hp hq
/-- `stabilizedConjUnitary` conjugates `blockSum p 0` to `blockSum 0 q`. -/
theorem stabilizedConjUnitary_conj (hv : v.IsPartialIsometry) (hp : v.conjTranspose * v = p)
    (hq : v * v.conjTranspose = q) :
    (hv.stabilizedConjUnitary hp hq : CStarMatrix (m ⊕ n) (m ⊕ n) A) * blockSum p 0 *
      star (hv.stabilizedConjUnitary hp hq : CStarMatrix (m ⊕ n) (m ⊕ n) A) = blockSum 0 q := by
  rw [(hv.isSelfAdjoint_stabilizedConjUnitary hp hq).star_eq, coe_stabilizedConjUnitary]
  exact ofMatrix.symm.injective <| by
    simpa [blockSum_def] using
      Matrix.fromBlocks_one_sub_mul_fromBlocks_mul_fromBlocks_one_sub_of_mul_eq
        (congrArg ofMatrix.symm hp) (congrArg ofMatrix.symm hq)
        (congrArg ofMatrix.symm (hv.mul_eq_self_of_conjTranspose_mul_self_eq hp))
end IsPartialIsometry

/-- Unit-free block matrix `(2⁻¹ : ℝ) • fromBlocks p (-v.conjTranspose) (-v) q`, matching
`2⁻¹ • (1 - stabilizedConjUnitary)` over unital rings. -/
def stabilizedNegProj [Neg A] [Star A] [SMul ℝ A]
    (v : CStarMatrix n m A) (p : CStarMatrix m m A) (q : CStarMatrix n n A) :
    CStarMatrix (m ⊕ n) (m ⊕ n) A := (2⁻¹ : ℝ) • fromBlocks p (-v.conjTranspose) (-v) q
theorem stabilizedNegProj_def [Neg A] [Star A] [SMul ℝ A]
    (v : CStarMatrix n m A) (p : CStarMatrix m m A) (q : CStarMatrix n n A) :
    stabilizedNegProj v p q = (2⁻¹ : ℝ) • fromBlocks p (-v.conjTranspose) (-v) q := (rfl)
/-- Unit-free rotation curve of `(m ⊕ n) × (m ⊕ n)` matrices from `blockSum p 0` (at `t = 0`) to
`blockSum 0 q` (at `t = 1`). -/
def stabilizedProjRot [Star A] [SMul ℂ A]
    (v : CStarMatrix n m A) (p : CStarMatrix m m A) (q : CStarMatrix n n A) (t : ℝ) :
    CStarMatrix (m ⊕ n) (m ⊕ n) A :=
  let c : ℂ := ↑(Real.cos (Real.pi * t / 2)); let s : ℂ := ↑(Real.sin (Real.pi * t / 2))
  fromBlocks ((c ^ 2) • p) ((Complex.I * s * c) • v.conjTranspose)
    ((-Complex.I * s * c) • v) ((s ^ 2) • q)
theorem stabilizedProjRot_def [Star A] [SMul ℂ A]
    (v : CStarMatrix n m A) (p : CStarMatrix m m A) (q : CStarMatrix n n A) (t : ℝ) :
    stabilizedProjRot v p q t = fromBlocks (((Real.cos (Real.pi * t / 2) : ℂ) ^ 2) • p)
      ((Complex.I * ↑(Real.sin (Real.pi * t / 2)) * ↑(Real.cos (Real.pi * t / 2))) •
        v.conjTranspose)
      ((-Complex.I * ↑(Real.sin (Real.pi * t / 2)) * ↑(Real.cos (Real.pi * t / 2))) • v)
      (((Real.sin (Real.pi * t / 2) : ℂ) ^ 2) • q) := (rfl)
section
variable [AddCommMonoid A] [Star A] [Module ℂ A]
  (v : CStarMatrix n m A) (p : CStarMatrix m m A) (q : CStarMatrix n n A)
@[simp] theorem stabilizedProjRot_zero : stabilizedProjRot v p q 0 = blockSum p 0 := by
  simp [stabilizedProjRot, blockSum_def]
@[simp] theorem stabilizedProjRot_one : stabilizedProjRot v p q 1 = blockSum 0 q := by
  simp [stabilizedProjRot, blockSum_def]
/-- Midpoint value of `stabilizedProjRot v p q` at `t = 1 / 2`. -/
theorem stabilizedProjRot_half : stabilizedProjRot v p q (1 / 2) =
    fromBlocks ((2⁻¹ : ℂ) • p) ((Complex.I / 2) • v.conjTranspose)
      ((-Complex.I / 2) • v) ((2⁻¹ : ℂ) • q) := by
  have hangle : Real.pi * (1 / 2) / 2 = Real.pi / 4 := by ring
  have hc2 : ((Real.cos (Real.pi / 4) : ℂ) ^ 2) = 2⁻¹ := by
    rw [Real.cos_pi_div_four, ← Complex.ofReal_pow, div_pow, Real.sq_sqrt (by norm_num)]; norm_num
  have hs2 : ((Real.sin (Real.pi / 4) : ℂ) ^ 2) = 2⁻¹ := by
    rwa [Real.sin_pi_div_four, ← Real.cos_pi_div_four]
  have hsc : (Real.sin (Real.pi / 4) : ℂ) * (Real.cos (Real.pi / 4) : ℂ) = 2⁻¹ := by
    rwa [Real.sin_pi_div_four, ← Real.cos_pi_div_four, ← sq]
  unfold stabilizedProjRot; dsimp only
  simp only [hangle, hc2, hs2, mul_assoc, hsc, fromBlocks_inj, true_and, and_true]
  exact ⟨by congr 1, by congr 1⟩
end
/-- `stabilizedProjRot v p q` is continuous on `ℝ` for any (possibly non-unital) C⋆-algebra `A`. -/
@[fun_prop] theorem continuous_stabilizedProjRot [NonUnitalCStarAlgebra A]
    (v : CStarMatrix n m A) (p : CStarMatrix m m A) (q : CStarMatrix n n A) :
    Continuous (stabilizedProjRot v p q) := by
  have hθ : Continuous fun t : ℝ => Real.pi * t / 2 := by fun_prop
  have hc := Complex.continuous_ofReal.comp (Real.continuous_cos.comp hθ)
  have hs := Complex.continuous_ofReal.comp (Real.continuous_sin.comp hθ)
  exact continuous_fromBlocks ((hc.pow 2).smul continuous_const)
    (((continuous_const.mul hs).mul hc).smul continuous_const)
    (((continuous_const.mul hs).mul hc).smul continuous_const) ((hs.pow 2).smul continuous_const)
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
variable [DecidableEq m] [DecidableEq n] [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
/-- Underlying matrix of `expUnitary (θ • stabilizedNegProj v p q)` for `θ : ℝ`. -/
theorem coe_expUnitary_smul_stabilizedNegProj (hv : v.IsPartialIsometry)
    (hp : v.conjTranspose * v = p) (hq : v * v.conjTranspose = q) (θ : ℝ) :
    ((selfAdjoint.expUnitary (θ • ⟨stabilizedNegProj v p q,
      (hv.isStarProjection_stabilizedNegProj hp hq).isSelfAdjoint⟩) : unitary _) :
      CStarMatrix (m ⊕ n) (m ⊕ n) A) =
      1 + ((Complex.exp (θ * Complex.I) - 1) * 2⁻¹) • fromBlocks p (-v.conjTranspose) (-v) q := by
  refine ((hv.isStarProjection_stabilizedNegProj hp hq).coe_expUnitary_smul θ).trans ?_
  have hsmul : (2⁻¹ : ℝ) • fromBlocks p (-v.conjTranspose) (-v) q =
      ((2⁻¹ : ℝ) : ℂ) • fromBlocks p (-v.conjTranspose) (-v) q :=
    ext fun _ _ => (Complex.coe_smul (2⁻¹ : ℝ) _).symm
  rw [stabilizedNegProj_def, hsmul, smul_smul]; congr 2; push_cast; rfl
/-- At `π`, the exponential unitary of `stabilizedNegProj v p q` is `stabilizedConjUnitary`. -/
@[simp] theorem expUnitary_pi_stabilizedNegProj (hv : v.IsPartialIsometry)
    (hp : v.conjTranspose * v = p) (hq : v * v.conjTranspose = q) :
    selfAdjoint.expUnitary (Real.pi • ⟨stabilizedNegProj v p q,
      (hv.isStarProjection_stabilizedNegProj hp hq).isSelfAdjoint⟩) =
      hv.stabilizedConjUnitary hp hq :=
  (congrArg (fun x => selfAdjoint.expUnitary (Real.pi • x))
    (Subtype.ext (hv.stabilizedNegProj_eq_half_one_sub hp hq))).trans
      (Unitary.expUnitary_pi_smul_half_one_sub (hv.stabilizedConjUnitary hp hq)
        (hv.isSelfAdjoint_stabilizedConjUnitary hp hq))
/-- Path `t ↦ expUnitary ((t * π) • stabilizedNegProj v p q)` from `1` to `stabilizedConjUnitary`.
-/
def stabilizedConjUnitaryPath (hv : v.IsPartialIsometry) (hp : v.conjTranspose * v = p)
    (hq : v * v.conjTranspose = q) :
    Path (1 : unitary (CStarMatrix (m ⊕ n) (m ⊕ n) A)) (hv.stabilizedConjUnitary hp hq) :=
  (selfAdjoint.expUnitaryPathToOne (Real.pi • ⟨stabilizedNegProj v p q,
    (hv.isStarProjection_stabilizedNegProj hp hq).isSelfAdjoint⟩)).cast
    rfl (hv.expUnitary_pi_stabilizedNegProj hp hq).symm
@[simp] theorem stabilizedConjUnitaryPath_apply (hv : v.IsPartialIsometry)
    (hp : v.conjTranspose * v = p) (hq : v * v.conjTranspose = q) (t : unitInterval) :
    (hv.stabilizedConjUnitaryPath hp hq) t = selfAdjoint.expUnitary (((t : ℝ) * Real.pi) •
      ⟨stabilizedNegProj v p q, (hv.isStarProjection_stabilizedNegProj hp hq).isSelfAdjoint⟩) := by
  rw [stabilizedConjUnitaryPath, Path.cast_coe, selfAdjoint.expUnitaryPathToOne_apply]
  congr 1; exact Subtype.ext (ext fun _ _ => smul_smul (t : ℝ) Real.pi _)
end
/-- Over a unital C⋆-algebra, `stabilizedConjUnitary` is joined to `1` in `unitary`. -/
theorem joined_one_stabilizedConjUnitary [DecidableEq m] [DecidableEq n] [CStarAlgebra A]
    (hv : v.IsPartialIsometry) (hp : v.conjTranspose * v = p) (hq : v * v.conjTranspose = q) :
    Joined (1 : unitary (CStarMatrix (m ⊕ n) (m ⊕ n) A)) (hv.stabilizedConjUnitary hp hq) := by
  let _ : PartialOrder A := CStarAlgebra.spectralOrder A
  have _ : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
  exact ⟨hv.stabilizedConjUnitaryPath hp hq⟩
end IsPartialIsometry

private theorem cos_sq_add_sin_sq_complex (θ : ℝ) :
    (Real.cos θ : ℂ) ^ 2 + (Real.sin θ : ℂ) ^ 2 = 1 := by exact_mod_cast Real.cos_sq_add_sin_sq θ
private def stabilizedProjRotRows [SMul ℂ A] (v : CStarMatrix n m A) (p : CStarMatrix m m A)
    (t : ℝ) : CStarMatrix (m ⊕ n) m A :=
  fromRows ((Real.cos (Real.pi * t / 2) : ℂ) • p)
    ((-Complex.I * ↑(Real.sin (Real.pi * t / 2))) • v)
namespace IsPartialIsometry
variable [Fintype m] [Fintype n] {v : CStarMatrix n m A} {p : CStarMatrix m m A}
  {q : CStarMatrix n n A}
section
variable [NonUnitalSemiring A] [StarRing A] [Module ℂ A] [IsScalarTower ℂ A A]
  [SMulCommClass ℂ A A] [StarModule ℂ A]
private theorem stabilizedProjRotRows_mul_conjTranspose (hv : v.IsPartialIsometry)
    (hp : v.conjTranspose * v = p) (hq : v * v.conjTranspose = q) (t : ℝ) :
    stabilizedProjRotRows v p t * (stabilizedProjRotRows v p t).conjTranspose =
      stabilizedProjRot v p q t := by
  have hp_proj : IsStarProjection p := hp ▸ hv.isStarProjection_conjTranspose_mul_self
  rw [stabilizedProjRotRows, fromRows_mul_conjTranspose_fromRows, stabilizedProjRot_def]
  simp only [conjTranspose_smul, conjTranspose_eq_of_isSelfAdjoint hp_proj.isSelfAdjoint,
    star_mul, star_neg, Complex.star_def, Complex.conj_ofReal, Complex.conj_I, neg_neg,
    CStarMatrix.smul_mul_smul, hp_proj.isIdempotentElem.eq,
    hv.mul_conjTranspose_eq_of_conjTranspose_mul_self_eq hp,
    hv.mul_eq_self_of_conjTranspose_mul_self_eq hp, hq, fromBlocks_inj]
  exact ⟨by congr 1; ring, by congr 1; ring, trivial,
    by congr 1; linear_combination -(Real.sin (Real.pi * t / 2) : ℂ) ^ 2 * Complex.I_sq⟩
private theorem isPartialIsometry_stabilizedProjRotRows (hv : v.IsPartialIsometry)
    (hp : v.conjTranspose * v = p) (t : ℝ) :
    (stabilizedProjRotRows v p t).IsPartialIsometry := by
  have hp_proj : IsStarProjection p := hp ▸ hv.isStarProjection_conjTranspose_mul_self
  have hinit : (stabilizedProjRotRows v p t).conjTranspose * stabilizedProjRotRows v p t = p := by
    rw [stabilizedProjRotRows, conjTranspose_fromRows_mul_fromRows]
    simp only [conjTranspose_smul, conjTranspose_eq_of_isSelfAdjoint hp_proj.isSelfAdjoint,
      star_mul, star_neg, Complex.star_def, Complex.conj_ofReal, Complex.conj_I, neg_neg,
      CStarMatrix.smul_mul_smul, hp_proj.isIdempotentElem.eq, hp, ← add_smul]
    have hcoeff : (Real.cos (Real.pi * t / 2) : ℂ) * ↑(Real.cos (Real.pi * t / 2)) +
        ↑(Real.sin (Real.pi * t / 2)) * Complex.I *
          (-Complex.I * ↑(Real.sin (Real.pi * t / 2))) = 1 := by
      linear_combination cos_sq_add_sin_sq_complex (Real.pi * t / 2) -
        (Real.sin (Real.pi * t / 2) : ℂ) ^ 2 * Complex.I_sq
    rw [hcoeff, one_smul]
  rw [isPartialIsometry_iff, CStarMatrix.mul_assoc, hinit, stabilizedProjRotRows, fromRows_mul,
    CStarMatrix.smul_mul, CStarMatrix.smul_mul, hp_proj.isIdempotentElem.eq,
    hv.mul_eq_self_of_conjTranspose_mul_self_eq hp]
/-- Every point on `stabilizedProjRot v p q` for a partial isometry `v` is a star projection. -/
theorem isStarProjection_stabilizedProjRot (hv : v.IsPartialIsometry)
    (hp : v.conjTranspose * v = p) (hq : v * v.conjTranspose = q) (t : ℝ) :
    IsStarProjection (stabilizedProjRot v p q t) := by
  rw [← hv.stabilizedProjRotRows_mul_conjTranspose hp hq t]
  exact (hv.isPartialIsometry_stabilizedProjRotRows hp t).isStarProjection_mul_conjTranspose_self
end
/-- Over a unital C⋆-algebra, conjugating `blockSum p 0` by
`expUnitary ((t * π) • stabilizedNegProj v p q)` equals `stabilizedProjRot v p q t`. -/
theorem expUnitary_conj_blockSum_eq_stabilizedProjRot [DecidableEq m] [DecidableEq n]
    [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] (hv : v.IsPartialIsometry)
    (hp : v.conjTranspose * v = p) (hq : v * v.conjTranspose = q) (t : ℝ) :
    ((selfAdjoint.expUnitary ((t * Real.pi) • ⟨stabilizedNegProj v p q,
      (hv.isStarProjection_stabilizedNegProj hp hq).isSelfAdjoint⟩) : unitary _) :
      CStarMatrix (m ⊕ n) (m ⊕ n) A) * blockSum p 0 *
      star ((selfAdjoint.expUnitary ((t * Real.pi) • ⟨stabilizedNegProj v p q,
        (hv.isStarProjection_stabilizedNegProj hp hq).isSelfAdjoint⟩) : unitary _) :
        CStarMatrix (m ⊕ n) (m ⊕ n) A) = stabilizedProjRot v p q t := by
  set U : CStarMatrix (m ⊕ n) (m ⊕ n) A := ((selfAdjoint.expUnitary ((t * Real.pi) •
    ⟨stabilizedNegProj v p q, (hv.isStarProjection_stabilizedNegProj hp hq).isSelfAdjoint⟩) :
    unitary _) : CStarMatrix (m ⊕ n) (m ⊕ n) A) with hU
  set c : ℂ := ↑(Real.cos (Real.pi * t / 2)) with hc
  set s : ℂ := ↑(Real.sin (Real.pi * t / 2)) with hs
  set z : ℂ := c + s * Complex.I with hz
  set α : ℂ := (Complex.exp (t * Real.pi * Complex.I) - 1) * 2⁻¹ with hα_def
  have hp_proj : IsStarProjection p := hp ▸ hv.isStarProjection_conjTranspose_mul_self
  have hcs : c ^ 2 + s ^ 2 = 1 := cos_sq_add_sin_sq_complex (Real.pi * t / 2)
  have hzz : z * star z = 1 := by
    have hsz : star z = c - s * Complex.I := by
      simp only [hz, hc, hs, star_add, star_mul, Complex.star_def, Complex.conj_ofReal,
        Complex.conj_I]; ring
    rw [hsz, hz]; linear_combination hcs - s ^ 2 * Complex.I_sq
  have hα : α = (z ^ 2 - 1) * 2⁻¹ := by
    have hsplit : (t : ℂ) * Real.pi * Complex.I =
        ((Real.pi * t / 2 : ℝ) : ℂ) * Complex.I + ((Real.pi * t / 2 : ℝ) : ℂ) * Complex.I := by
      push_cast; ring
    rw [hα_def, hsplit, Complex.exp_add, Complex.exp_ofReal_mul_I, ← hc, ← hs, ← hz, sq]
  have h1α : 1 + α = z * c := by
    rw [hα, hz]; linear_combination -((1 : ℂ) / 2) * hcs + (s ^ 2 / 2) * Complex.I_sq
  have hnα : -α = z * (-Complex.I * s) := by
    rw [hα, hz]; linear_combination -((1 : ℂ) / 2) * hcs + (s ^ 2 / 2) * Complex.I_sq
  have hUF : U * fromRows p (0 : CStarMatrix n m A) = z • stabilizedProjRotRows v p t := by
    have hp1 : p + α • p = (z * c) • p := by rw [← h1α, add_smul, one_smul]
    have hv1 : -(α • v) = (z * (-Complex.I * s)) • v := by rw [← neg_smul, hnα]
    rw [hU, hv.coe_expUnitary_smul_stabilizedNegProj hp hq (t * Real.pi), Complex.ofReal_mul,
      ← hα_def, CStarMatrix.add_mul, CStarMatrix.one_mul, CStarMatrix.smul_mul,
      fromBlocks_mul_fromRows]
    simp [stabilizedProjRotRows, ← hc, ← hs, hp_proj.isIdempotentElem.eq,
      hv.mul_eq_self_of_conjTranspose_mul_self_eq hp, hp1, hv1, smul_smul]
  have hbp : fromRows p (0 : CStarMatrix n m A) *
      (fromRows p (0 : CStarMatrix n m A)).conjTranspose = blockSum p 0 := by
    rw [fromRows_mul_conjTranspose_fromRows]
    simp [conjTranspose_eq_of_isSelfAdjoint hp_proj.isSelfAdjoint, hp_proj.isIdempotentElem.eq,
      blockSum_def]
  have hfp : (fromRows p (0 : CStarMatrix n m A)).conjTranspose *
      fromRows p (0 : CStarMatrix n m A) = p := by
    simp [conjTranspose_eq_of_isSelfAdjoint hp_proj.isSelfAdjoint, hp_proj.isIdempotentElem.eq]
  have hrp : stabilizedProjRotRows v p t * p = stabilizedProjRotRows v p t := by
    simp [stabilizedProjRotRows, CStarMatrix.smul_mul, hp_proj.isIdempotentElem.eq,
      hv.mul_eq_self_of_conjTranspose_mul_self_eq hp]
  have humul : U * blockSum p 0 =
      z • (stabilizedProjRotRows v p t * (fromRows p (0 : CStarMatrix n m A)).conjTranspose) := by
    rw [← hbp, ← CStarMatrix.mul_assoc, hUF, CStarMatrix.smul_mul]
  rw [star_eq_conjTranspose, ← self_mul_conjTranspose_mul_of_isStarProjection U
      (isStarProjection_blockSum_iff.mpr ⟨hp_proj, .zero _⟩),
    humul, conjTranspose_smul, CStarMatrix.smul_mul_smul, hzz, one_smul, conjTranspose_mul,
    conjTranspose_conjTranspose, CStarMatrix.mul_assoc,
    ← CStarMatrix.mul_assoc (fromRows p (0 : CStarMatrix n m A)).conjTranspose, hfp,
    ← CStarMatrix.mul_assoc, hrp, hv.stabilizedProjRotRows_mul_conjTranspose hp hq t]
/-- Continuous path of star projections from `blockSum p 0` to `blockSum 0 q`. -/
def stabilizedProjPath [NonUnitalCStarAlgebra A] (hv : v.IsPartialIsometry)
    (hp : v.conjTranspose * v = p) (hq : v * v.conjTranspose = q) :
    Path (⟨blockSum p 0, isStarProjection_blockSum_iff.mpr
        ⟨hp ▸ hv.isStarProjection_conjTranspose_mul_self, .zero _⟩⟩ :
        {P : CStarMatrix (m ⊕ n) (m ⊕ n) A // IsStarProjection P})
      ⟨blockSum 0 q, isStarProjection_blockSum_iff.mpr
        ⟨.zero _, hq ▸ hv.isStarProjection_mul_conjTranspose_self⟩⟩ where
  toFun t := ⟨stabilizedProjRot v p q t, hv.isStarProjection_stabilizedProjRot hp hq t⟩
  continuous_toFun :=
    ((continuous_stabilizedProjRot v p q).comp continuous_subtype_val).subtype_mk _
  source' := Subtype.ext (stabilizedProjRot_zero v p q)
  target' := Subtype.ext (stabilizedProjRot_one v p q)
@[simp] theorem coe_stabilizedProjPath_apply [NonUnitalCStarAlgebra A] (hv : v.IsPartialIsometry)
    (hp : v.conjTranspose * v = p) (hq : v * v.conjTranspose = q) (t : unitInterval) :
    ((hv.stabilizedProjPath hp hq t : {P : CStarMatrix (m ⊕ n) (m ⊕ n) A // IsStarProjection P}) :
      CStarMatrix (m ⊕ n) (m ⊕ n) A) = stabilizedProjRot v p q t := (rfl)
end IsPartialIsometry

section
variable [Fintype m] [Fintype n] {p : CStarMatrix m m A} {q : CStarMatrix n n A}
/-- Murray–von Neumann equivalent projections are conjugate by a self-adjoint unitary after
stabilization. -/
theorem MurrayVonNeumannEquiv.exists_isSelfAdjoint_unitary_conj_blockSum_eq
    [DecidableEq m] [DecidableEq n] [Ring A] [StarRing A] (h : p.MurrayVonNeumannEquiv q) :
    ∃ w : unitary (CStarMatrix (m ⊕ n) (m ⊕ n) A),
      IsSelfAdjoint (w : CStarMatrix (m ⊕ n) (m ⊕ n) A) ∧
      (w : CStarMatrix (m ⊕ n) (m ⊕ n) A) * blockSum p 0 *
        star (w : CStarMatrix (m ⊕ n) (m ⊕ n) A) = blockSum 0 q :=
  let ⟨_, hv, hp, hq⟩ := h
  ⟨hv.stabilizedConjUnitary hp hq, hv.isSelfAdjoint_stabilizedConjUnitary hp hq,
    hv.stabilizedConjUnitary_conj hp hq⟩
/-- Over a unital C⋆-algebra, equivalent projections are conjugate by a unitary joined to `1`. -/
theorem MurrayVonNeumannEquiv.exists_joined_one_unitary_conj_blockSum_eq
    [DecidableEq m] [DecidableEq n] [CStarAlgebra A] (h : p.MurrayVonNeumannEquiv q) :
    ∃ w : unitary (CStarMatrix (m ⊕ n) (m ⊕ n) A), Joined 1 w ∧
      (w : CStarMatrix (m ⊕ n) (m ⊕ n) A) * blockSum p 0 *
        star (w : CStarMatrix (m ⊕ n) (m ⊕ n) A) = blockSum 0 q :=
  let ⟨_, hv, hp, hq⟩ := h
  ⟨hv.stabilizedConjUnitary hp hq, hv.joined_one_stabilizedConjUnitary hp hq,
    hv.stabilizedConjUnitary_conj hp hq⟩
/-- Over any C⋆-algebra, equivalent projections are joined by a path of projections after
stabilization. -/
theorem MurrayVonNeumannEquiv.joined_blockSum [NonUnitalCStarAlgebra A]
    (h : p.MurrayVonNeumannEquiv q) :
    Joined (⟨blockSum p 0, isStarProjection_blockSum_iff.mpr ⟨h.isStarProjection_left, .zero _⟩⟩ :
        {P : CStarMatrix (m ⊕ n) (m ⊕ n) A // IsStarProjection P})
      ⟨blockSum 0 q, isStarProjection_blockSum_iff.mpr ⟨.zero _, h.isStarProjection_right⟩⟩ :=
  let ⟨_, hv, hp, hq⟩ := h; ⟨hv.stabilizedProjPath hp hq⟩
end

end CStarMatrix
