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

/-!
# Rectangular partial isometries and Murray–von Neumann equivalence on `CStarMatrix`

Two matrix projections `p : CStarMatrix m m A` and `q : CStarMatrix n n A` over a C⋆-algebra `A`,
possibly indexed by different finite types `m` and `n`, are Murray–von Neumann equivalent when
there exists a rectangular partial isometry `v : CStarMatrix n m A` with `v.conjTranspose * v = p`
and `v * v.conjTranspose = q`. Over a star-ordered ring with proper star, `v.IsPartialIsometry` is
automatic once `v.conjTranspose * v` is idempotent; including it in the definition gives algebraic
equivalence-relation, functoriality, and block-stabilization laws over general star semirings.

## Main definitions

* `CStarMatrix.IsPartialIsometry`, `CStarMatrix.MurrayVonNeumannEquiv`: rectangular partial
  isometries and Murray–von Neumann equivalence across arbitrary finite matrix sizes.
* `CStarMatrix.IsPartialIsometry.stabilizedConjUnitary`: the self-adjoint unitary
  `fromBlocks (1 - p) v.conjTranspose v (1 - q)` conjugating `blockDiag p 0` to `blockDiag 0 q`.
* `CStarMatrix.stabilizedNegProj`, `CStarMatrix.stabilizedProjRot`,
  `CStarMatrix.IsPartialIsometry.stabilizedProjPath`: the `-1`-eigenspace projection and explicit
  projection rotation path from `blockDiag p 0` to `blockDiag 0 q` (valid for non-unital `A` and
  matching conjugation by `t ↦ expUnitary ((t * π) • r)` in the unital case).

## Main statements

* `CStarMatrix.isPartialIsometry_iff_isStarProjection_conjTranspose_mul_self` and
  `CStarMatrix.murrayVonNeumannEquiv_iff_exists_mul_eq`: proper-star characterizations.
* `CStarMatrix.MurrayVonNeumannEquiv.refl`, `symm`, `trans`, `blockDiag`, `add_of_mul_eq_zero`,
  `of_unitary_conj_unitization`, `map`: equivalence and compatibility laws.
* `CStarMatrix.MurrayVonNeumannEquiv.exists_unitary_blockDiag_eq`,
  `exists_joined_one_unitary_blockDiag_eq`, `joined_blockDiag`: stabilized unitary and homotopy
  equivalence of Murray–von Neumann equivalent projections.

## References

* B. Blackadar, *K-Theory for Operator Algebras*, 2nd ed., §4.6 and §5.1.
-/

public section

noncomputable section

open scoped Matrix ComplexOrder

namespace CStarMatrix

section PartialIsometry

variable {k l m n o R A B F : Type*}

/-- A rectangular matrix `v : CStarMatrix m n A` is a **partial isometry** when
`v * v.conjTranspose * v = v`. -/
def IsPartialIsometry [Fintype m] [Fintype n] [Mul A] [AddCommMonoid A] [Star A]
    (v : CStarMatrix m n A) : Prop :=
  v * v.conjTranspose * v = v

theorem isPartialIsometry_iff [Fintype m] [Fintype n] [Mul A] [AddCommMonoid A] [Star A]
    {v : CStarMatrix m n A} : v.IsPartialIsometry ↔ v * v.conjTranspose * v = v := Iff.rfl

theorem IsPartialIsometry.mul_conjTranspose_mul_self [Fintype m] [Fintype n] [Mul A]
    [AddCommMonoid A] [Star A] {v : CStarMatrix m n A} (hv : v.IsPartialIsometry) :
    v * v.conjTranspose * v = v := hv

/-- On square matrices, `CStarMatrix.IsPartialIsometry` coincides with `TauCeti.IsPartialIsometry`.
-/
theorem isPartialIsometry_iff_starMul [Fintype n] [Mul A] [AddCommMonoid A] [Star A]
    {v : CStarMatrix n n A} : v.IsPartialIsometry ↔ TauCeti.IsPartialIsometry v := by
  rw [isPartialIsometry_iff, TauCeti.isPartialIsometry_iff]; rfl

namespace IsPartialIsometry

/-- The conjugate transpose of a rectangular partial isometry is a partial isometry. -/
protected theorem conjTranspose [Fintype m] [Fintype n] [NonUnitalSemiring A] [StarRing A]
    {v : CStarMatrix m n A} (hv : v.IsPartialIsometry) : v.conjTranspose.IsPartialIsometry := by
  rw [isPartialIsometry_iff, conjTranspose_conjTranspose, CStarMatrix.mul_assoc]
  simpa only [conjTranspose_mul, conjTranspose_conjTranspose] using
    congrArg CStarMatrix.conjTranspose hv.mul_conjTranspose_mul_self

theorem conjTranspose_mul_conjTranspose [Fintype m] [Fintype n] [NonUnitalSemiring A] [StarRing A]
    {v : CStarMatrix m n A} (hv : v.IsPartialIsometry) :
    v.conjTranspose * v * v.conjTranspose = v.conjTranspose := by
  simpa using hv.conjTranspose.mul_conjTranspose_mul_self

/-- The initial projection `v.conjTranspose * v` of a rectangular partial isometry is a star
projection. -/
theorem isStarProjection_conjTranspose_mul_self [Fintype m] [Fintype n] [NonUnitalSemiring A]
    [StarRing A] {v : CStarMatrix m n A} (hv : v.IsPartialIsometry) :
    IsStarProjection (v.conjTranspose * v) where
  isIdempotentElem := by
    rw [IsIdempotentElem, CStarMatrix.mul_assoc, ← CStarMatrix.mul_assoc v,
      hv.mul_conjTranspose_mul_self]
  isSelfAdjoint := by
    change (v.conjTranspose * v).conjTranspose = v.conjTranspose * v
    rw [conjTranspose_mul, conjTranspose_conjTranspose]

/-- The final projection `v * v.conjTranspose` of a rectangular partial isometry is a star
projection. -/
theorem isStarProjection_mul_conjTranspose_self [Fintype m] [Fintype n] [NonUnitalSemiring A]
    [StarRing A] {v : CStarMatrix m n A} (hv : v.IsPartialIsometry) :
    IsStarProjection (v * v.conjTranspose) := by
  simpa using hv.conjTranspose.isStarProjection_conjTranspose_mul_self

protected theorem zero [Fintype m] [Fintype n] [NonUnitalNonAssocSemiring A] [StarAddMonoid A] :
    (0 : CStarMatrix m n A).IsPartialIsometry := by simp [IsPartialIsometry]

protected theorem one [Fintype n] [DecidableEq n] [Semiring A] [StarRing A] :
    (1 : CStarMatrix n n A).IsPartialIsometry :=
  isPartialIsometry_iff_starMul.mpr TauCeti.IsPartialIsometry.one

theorem of_isStarProjection [Fintype n] [Mul A] [AddCommMonoid A] [Star A]
    {p : CStarMatrix n n A} (hp : IsStarProjection p) : p.IsPartialIsometry :=
  isPartialIsometry_iff_starMul.mpr hp.isPartialIsometry

theorem of_mem_unitary [Fintype n] [DecidableEq n] [Semiring A] [StarRing A]
    {u : CStarMatrix n n A} (hu : u ∈ unitary (CStarMatrix n n A)) : u.IsPartialIsometry :=
  isPartialIsometry_iff_starMul.mpr (TauCeti.IsPartialIsometry.of_mem_unitary hu)

/-- Over a star-ordered ring with proper star, if `v.conjTranspose * v` is idempotent then `v` is a
rectangular partial isometry. -/
theorem of_isIdempotentElem_conjTranspose_mul_self [Fintype m] [Fintype n] [NonUnitalRing A]
    [StarRing A] [PartialOrder A] [StarOrderedRing A] [IsProperStar A]
    {v : CStarMatrix m n A} (h : IsIdempotentElem (v.conjTranspose * v)) :
    v.IsPartialIsometry := by
  rw [isPartialIsometry_iff, ← sub_eq_zero, ← conjTranspose_mul_self_eq_zero]
  have hq : v.conjTranspose * v * (v.conjTranspose * v) = v.conjTranspose * v := h.eq
  have h1 : (v * v.conjTranspose * v).conjTranspose = v.conjTranspose * v * v.conjTranspose := by
    rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, CStarMatrix.mul_assoc]
  have h2 : (v.conjTranspose * v * v.conjTranspose) * (v * v.conjTranspose * v) =
      v.conjTranspose * v := by
    calc (v.conjTranspose * v * v.conjTranspose) * (v * v.conjTranspose * v)
        = (v.conjTranspose * v) * ((v.conjTranspose * v) * (v.conjTranspose * v)) := by
            simp only [CStarMatrix.mul_assoc]
      _ = v.conjTranspose * v := by rw [hq, hq]
  have h3 : (v.conjTranspose * v * v.conjTranspose) * v = v.conjTranspose * v := by
    rw [CStarMatrix.mul_assoc, hq]
  have h4 : v.conjTranspose * (v * v.conjTranspose * v) = v.conjTranspose * v := by
    simpa only [CStarMatrix.mul_assoc] using hq
  rw [conjTranspose_sub, h1, CStarMatrix.sub_mul, CStarMatrix.mul_sub, CStarMatrix.mul_sub,
    h2, h3, h4, sub_self]

protected theorem blockDiag [Fintype l] [Fintype m] [Fintype n] [Fintype o]
    [NonUnitalNonAssocSemiring A] [StarAddMonoid A]
    {v : CStarMatrix m l A} {w : CStarMatrix o n A}
    (hv : v.IsPartialIsometry) (hw : w.IsPartialIsometry) :
    (CStarMatrix.blockDiag v w).IsPartialIsometry := by
  rw [isPartialIsometry_iff, blockDiag_conjTranspose, blockDiag_mul, blockDiag_mul,
    hv.mul_conjTranspose_mul_self, hw.mul_conjTranspose_mul_self]

protected theorem reindexₗ [Fintype l] [Fintype m] [Fintype n] [Fintype o] [Semiring R]
    [NonUnitalNonAssocSemiring A] [Module R A] [Star A]
    (eₘ : m ≃ l) (eₙ : n ≃ o) {v : CStarMatrix m n A} (hv : v.IsPartialIsometry) :
    (CStarMatrix.reindexₗ R A eₘ eₙ v).IsPartialIsometry := by
  rw [isPartialIsometry_iff, reindexₗ_conjTranspose, reindexₗ_mul, reindexₗ_mul,
    hv.mul_conjTranspose_mul_self]

protected theorem map [Fintype m] [Fintype n] [NonUnitalNonAssocSemiring A] [Star A]
    [NonUnitalNonAssocSemiring B] [Star B] [FunLike F A B] [NonUnitalRingHomClass F A B]
    [StarHomClass F A B] (φ : F) {v : CStarMatrix m n A} (hv : v.IsPartialIsometry) :
    (v.map φ).IsPartialIsometry := by
  rw [isPartialIsometry_iff, ← map_conjTranspose, ← map_mul, ← map_mul,
    hv.mul_conjTranspose_mul_self]

protected theorem amplify (k : Type*) [Fintype k] [DecidableEq k] [Fintype m] [Fintype n]
    [NonUnitalNonAssocSemiring A] [StarAddMonoid A]
    {v : CStarMatrix m n A} (hv : v.IsPartialIsometry) :
    (CStarMatrix.amplify k v).IsPartialIsometry := by
  rw [isPartialIsometry_iff, amplify_conjTranspose, ← amplify_mul, ← amplify_mul,
    hv.mul_conjTranspose_mul_self]

/-- Vertical stack `colBlocks p₁ p₂` of two orthogonal star projections is a partial isometry. -/
theorem colBlocks_of_mul_eq_zero [Fintype n] [NonUnitalSemiring A] [StarRing A]
    {p₁ p₂ : CStarMatrix n n A} (hp₁ : IsStarProjection p₁) (hp₂ : IsStarProjection p₂)
    (h₁₂ : p₁ * p₂ = 0) : (colBlocks p₁ p₂).IsPartialIsometry := by
  have h₂₁ : p₂ * p₁ = 0 := by
    rw [← hp₂.isSelfAdjoint.star_eq, ← hp₁.isSelfAdjoint.star_eq, ← star_mul, h₁₂, star_zero]
  have hp₁t : p₁.conjTranspose = p₁ := hp₁.isSelfAdjoint.star_eq
  have hp₂t : p₂.conjTranspose = p₂ := hp₂.isSelfAdjoint.star_eq
  simp [isPartialIsometry_iff, hp₁t, hp₂t, hp₁.isIdempotentElem.eq, hp₂.isIdempotentElem.eq,
    h₁₂, h₂₁]

end IsPartialIsometry

@[simp] theorem isPartialIsometry_conjTranspose_iff [Fintype m] [Fintype n] [NonUnitalSemiring A]
    [StarRing A] {v : CStarMatrix m n A} :
    v.conjTranspose.IsPartialIsometry ↔ v.IsPartialIsometry :=
  ⟨fun h => by simpa using h.conjTranspose, IsPartialIsometry.conjTranspose⟩

@[simp] theorem isPartialIsometry_blockDiag_iff [Fintype l] [Fintype m] [Fintype n] [Fintype o]
    [NonUnitalNonAssocSemiring A] [StarAddMonoid A]
    {v : CStarMatrix m l A} {w : CStarMatrix o n A} :
    (blockDiag v w).IsPartialIsometry ↔ v.IsPartialIsometry ∧ w.IsPartialIsometry := by
  rw [isPartialIsometry_iff, blockDiag_conjTranspose, blockDiag_mul, blockDiag_mul, blockDiag_inj]
  rfl

@[simp] theorem isPartialIsometry_reindexₗ_iff [Fintype l] [Fintype m] [Fintype n] [Fintype o]
    [Semiring R] [NonUnitalNonAssocSemiring A] [Module R A] [Star A]
    (eₘ : m ≃ l) (eₙ : n ≃ o) {v : CStarMatrix m n A} :
    (reindexₗ R A eₘ eₙ v).IsPartialIsometry ↔ v.IsPartialIsometry :=
  ⟨fun h => by
    rw [← reindexₗ_refl (R := R) v, ← Equiv.self_trans_symm eₘ, ← Equiv.self_trans_symm eₙ,
      reindexₗ_trans]
    exact h.reindexₗ eₘ.symm eₙ.symm, IsPartialIsometry.reindexₗ eₘ eₙ⟩

theorem isPartialIsometry_iff_isIdempotentElem_conjTranspose_mul_self [Fintype m] [Fintype n]
    [NonUnitalRing A] [StarRing A] [PartialOrder A] [StarOrderedRing A] [IsProperStar A]
    {v : CStarMatrix m n A} :
    v.IsPartialIsometry ↔ IsIdempotentElem (v.conjTranspose * v) :=
  ⟨fun hv => hv.isStarProjection_conjTranspose_mul_self.isIdempotentElem,
    IsPartialIsometry.of_isIdempotentElem_conjTranspose_mul_self⟩

/-- Over a star-ordered ring with proper star, `v` is a partial isometry iff
`v.conjTranspose * v` is a star projection. -/
theorem isPartialIsometry_iff_isStarProjection_conjTranspose_mul_self [Fintype m] [Fintype n]
    [NonUnitalRing A] [StarRing A] [PartialOrder A] [StarOrderedRing A] [IsProperStar A]
    {v : CStarMatrix m n A} :
    v.IsPartialIsometry ↔ IsStarProjection (v.conjTranspose * v) :=
  ⟨IsPartialIsometry.isStarProjection_conjTranspose_mul_self,
    fun h => .of_isIdempotentElem_conjTranspose_mul_self h.isIdempotentElem⟩

theorem isPartialIsometry_iff_isStarProjection_mul_conjTranspose_self [Fintype m] [Fintype n]
    [NonUnitalRing A] [StarRing A] [PartialOrder A] [StarOrderedRing A] [IsProperStar A]
    {v : CStarMatrix m n A} :
    v.IsPartialIsometry ↔ IsStarProjection (v * v.conjTranspose) := by
  rw [← isPartialIsometry_conjTranspose_iff,
    isPartialIsometry_iff_isStarProjection_conjTranspose_mul_self, conjTranspose_conjTranspose]

/-- Every rectangular partial isometry over a C⋆-algebra is a contraction (`‖v‖ ≤ 1`). -/
theorem IsPartialIsometry.norm_le_one [Fintype m] [Fintype n] [NonUnitalCStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A] {v : CStarMatrix m n A} (hv : v.IsPartialIsometry) :
    ‖v‖ ≤ 1 :=
  (sq_le_sq₀ (norm_nonneg v) zero_le_one).mp <| by
    simpa [norm_conjTranspose_mul_self] using
      IsStarProjection.norm_le _ hv.isStarProjection_conjTranspose_mul_self

/-- Every nonzero rectangular partial isometry over a C⋆-algebra has norm `1`. -/
theorem IsPartialIsometry.norm_eq_one [Fintype m] [Fintype n] [NonUnitalCStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A] {v : CStarMatrix m n A}
    (hv : v.IsPartialIsometry) (hv0 : v ≠ 0) : ‖v‖ = 1 := by
  have hp := hv.isStarProjection_conjTranspose_mul_self
  have h4 : (‖v‖ ^ 2) * (‖v‖ ^ 2) = (‖v‖ ^ 2) * 1 := by
    rw [mul_one, ← norm_conjTranspose_mul_self v, ← CStarRing.norm_star_mul_self,
      hp.isSelfAdjoint.star_eq, hp.isIdempotentElem.eq]
  exact (sq_eq_sq₀ (norm_nonneg v) zero_le_one).mp <| by
    simpa using mul_left_cancel₀ (sq_pos_of_pos (norm_pos_iff.mpr hv0)).ne' h4

end PartialIsometry

section MurrayVonNeumannEquiv

variable {k l m n o R A B F : Type*}

/-- Rectangular **Murray–von Neumann equivalence** between `p : CStarMatrix m m A` and
`q : CStarMatrix n n A`: there exists a rectangular partial isometry `v : CStarMatrix n m A` with
`v.conjTranspose * v = p` and `v * v.conjTranspose = q`. -/
def MurrayVonNeumannEquiv [Fintype m] [Fintype n] [Mul A] [AddCommMonoid A] [Star A]
    (p : CStarMatrix m m A) (q : CStarMatrix n n A) : Prop :=
  ∃ v : CStarMatrix n m A, v.IsPartialIsometry ∧ v.conjTranspose * v = p ∧ v * v.conjTranspose = q

theorem murrayVonNeumannEquiv_iff [Fintype m] [Fintype n] [Mul A] [AddCommMonoid A] [Star A]
    {p : CStarMatrix m m A} {q : CStarMatrix n n A} :
    p.MurrayVonNeumannEquiv q ↔
      ∃ v : CStarMatrix n m A,
        v.IsPartialIsometry ∧ v.conjTranspose * v = p ∧ v * v.conjTranspose = q := Iff.rfl

theorem murrayVonNeumannEquiv_iff_exists_starMul [Fintype n] [Mul A] [AddCommMonoid A] [Star A]
    {p q : CStarMatrix n n A} :
    p.MurrayVonNeumannEquiv q ↔
      ∃ v : CStarMatrix n n A, TauCeti.IsPartialIsometry v ∧ star v * v = p ∧ v * star v = q := by
  simp_rw [murrayVonNeumannEquiv_iff, isPartialIsometry_iff_starMul]; rfl

/-- Over a star-ordered ring with proper star, an idempotent `p` is Murray–von Neumann equivalent
to `q` iff there exists `v` with `v.conjTranspose * v = p` and `v * v.conjTranspose = q`. -/
theorem murrayVonNeumannEquiv_iff_exists_mul_eq [Fintype m] [Fintype n] [NonUnitalRing A]
    [StarRing A] [PartialOrder A] [StarOrderedRing A] [IsProperStar A]
    {p : CStarMatrix m m A} {q : CStarMatrix n n A} (hp : IsIdempotentElem p) :
    p.MurrayVonNeumannEquiv q ↔
      ∃ v : CStarMatrix n m A, v.conjTranspose * v = p ∧ v * v.conjTranspose = q :=
  ⟨fun ⟨v, _, hvp, hvq⟩ => ⟨v, hvp, hvq⟩,
    fun ⟨v, hvp, hvq⟩ => ⟨v, .of_isIdempotentElem_conjTranspose_mul_self (hvp.symm ▸ hp), hvp, hvq⟩⟩

namespace MurrayVonNeumannEquiv

theorem isStarProjection_left [Fintype m] [Fintype n] [NonUnitalSemiring A] [StarRing A]
    {p : CStarMatrix m m A} {q : CStarMatrix n n A} (h : p.MurrayVonNeumannEquiv q) :
    IsStarProjection p := by
  rcases h with ⟨v, hv, rfl, -⟩; exact hv.isStarProjection_conjTranspose_mul_self

theorem isStarProjection_right [Fintype m] [Fintype n] [NonUnitalSemiring A] [StarRing A]
    {p : CStarMatrix m m A} {q : CStarMatrix n n A} (h : p.MurrayVonNeumannEquiv q) :
    IsStarProjection q := by
  rcases h with ⟨v, hv, -, rfl⟩; exact hv.isStarProjection_mul_conjTranspose_self

/-- A star projection is Murray–von Neumann equivalent to itself. -/
protected theorem refl [Fintype m] [Mul A] [AddCommMonoid A] [Star A]
    {p : CStarMatrix m m A} (hp : IsStarProjection p) : p.MurrayVonNeumannEquiv p :=
  ⟨p, .of_isStarProjection hp,
    by rw [show p.conjTranspose = star p from rfl, hp.isSelfAdjoint.star_eq,
      hp.isIdempotentElem.eq],
    by rw [show p.conjTranspose = star p from rfl, hp.isSelfAdjoint.star_eq,
      hp.isIdempotentElem.eq]⟩

/-- Rectangular Murray–von Neumann equivalence is symmetric. -/
@[symm] protected theorem symm [Fintype m] [Fintype n] [NonUnitalSemiring A] [StarRing A]
    {p : CStarMatrix m m A} {q : CStarMatrix n n A} (h : p.MurrayVonNeumannEquiv q) :
    q.MurrayVonNeumannEquiv p := by
  rcases h with ⟨v, hv, rfl, rfl⟩
  exact ⟨v.conjTranspose, hv.conjTranspose, by simp, by simp⟩

/-- Rectangular Murray–von Neumann equivalence is transitive across arbitrary finite sizes. -/
@[trans] protected theorem trans [Fintype l] [Fintype m] [Fintype n] [NonUnitalSemiring A]
    [StarRing A] {p : CStarMatrix l l A} {q : CStarMatrix m m A} {r : CStarMatrix n n A}
    (hpq : p.MurrayVonNeumannEquiv q) (hqr : q.MurrayVonNeumannEquiv r) :
    p.MurrayVonNeumannEquiv r := by
  rcases hpq with ⟨v, hv, rfl, hvq⟩
  rcases hqr with ⟨w, hw, hwq, rfl⟩
  have hinit : (w * v).conjTranspose * (w * v) = v.conjTranspose * v := by
    rw [conjTranspose_mul, CStarMatrix.mul_assoc, ← CStarMatrix.mul_assoc w.conjTranspose, hwq,
      ← hvq, hv.mul_conjTranspose_mul_self]
  have hfinal : (w * v) * (w * v).conjTranspose = w * w.conjTranspose := by
    rw [conjTranspose_mul, CStarMatrix.mul_assoc, ← CStarMatrix.mul_assoc v, hvq, ← hwq,
      hw.conjTranspose_mul_conjTranspose]
  refine ⟨w * v, ?_, hinit, hfinal⟩
  rw [isPartialIsometry_iff, hfinal, ← CStarMatrix.mul_assoc, hw.mul_conjTranspose_mul_self]

/-- `MurrayVonNeumannEquiv` is compatible with `blockDiag`. -/
protected theorem blockDiag [Fintype l] [Fintype m] [Fintype n] [Fintype o]
    [NonUnitalNonAssocSemiring A] [StarAddMonoid A]
    {p₁ : CStarMatrix l l A} {q₁ : CStarMatrix m m A}
    {p₂ : CStarMatrix n n A} {q₂ : CStarMatrix o o A}
    (h₁ : p₁.MurrayVonNeumannEquiv q₁) (h₂ : p₂.MurrayVonNeumannEquiv q₂) :
    (CStarMatrix.blockDiag p₁ p₂).MurrayVonNeumannEquiv (CStarMatrix.blockDiag q₁ q₂) := by
  rcases h₁ with ⟨v₁, hv₁, rfl, rfl⟩; rcases h₂ with ⟨v₂, hv₂, rfl, rfl⟩
  exact ⟨CStarMatrix.blockDiag v₁ v₂, hv₁.blockDiag hv₂, by simp, by simp⟩

protected theorem map [Fintype m] [Fintype n] [NonUnitalNonAssocSemiring A] [Star A]
    [NonUnitalNonAssocSemiring B] [Star B] [FunLike F A B] [NonUnitalRingHomClass F A B]
    [StarHomClass F A B] (φ : F)
    {p : CStarMatrix m m A} {q : CStarMatrix n n A} (h : p.MurrayVonNeumannEquiv q) :
    (p.map φ).MurrayVonNeumannEquiv (q.map φ) := by
  rcases h with ⟨v, hv, rfl, rfl⟩
  exact ⟨v.map φ, hv.map φ, by rw [← map_conjTranspose, ← map_mul],
    by rw [← map_conjTranspose, ← map_mul]⟩

protected theorem mapₙₐ [Fintype n] [Semiring R] [NonUnitalNonAssocSemiring A] [Module R A]
    [Star A] [NonUnitalNonAssocSemiring B] [Module R B] [Star B]
    (φ : A →⋆ₙₐ[R] B) {p q : CStarMatrix n n A} (h : p.MurrayVonNeumannEquiv q) :
    (CStarMatrix.mapₙₐ φ p).MurrayVonNeumannEquiv (CStarMatrix.mapₙₐ φ q) :=
  h.map φ

protected theorem mapₐ [Fintype n] [DecidableEq n] [CommSemiring R] [Semiring A] [Algebra R A]
    [Star A] [Semiring B] [Algebra R B] [Star B]
    (φ : A →⋆ₐ[R] B) {p q : CStarMatrix n n A} (h : p.MurrayVonNeumannEquiv q) :
    (CStarMatrix.mapₐ φ p).MurrayVonNeumannEquiv (CStarMatrix.mapₐ φ q) := by
  rw [mapₐ_apply, mapₐ_apply]; exact h.map φ

protected theorem amplify (k : Type*) [Fintype k] [DecidableEq k] [Fintype m] [Fintype n]
    [NonUnitalNonAssocSemiring A] [StarAddMonoid A]
    {p : CStarMatrix m m A} {q : CStarMatrix n n A} (h : p.MurrayVonNeumannEquiv q) :
    (CStarMatrix.amplify k p).MurrayVonNeumannEquiv (CStarMatrix.amplify k q) := by
  rcases h with ⟨v, hv, rfl, rfl⟩
  exact ⟨CStarMatrix.amplify k v, hv.amplify k, by rw [amplify_conjTranspose, ← amplify_mul],
    by rw [amplify_conjTranspose, ← amplify_mul]⟩

end MurrayVonNeumannEquiv

theorem murrayVonNeumannEquiv_comm [Fintype m] [Fintype n] [NonUnitalSemiring A] [StarRing A]
    {p : CStarMatrix m m A} {q : CStarMatrix n n A} :
    p.MurrayVonNeumannEquiv q ↔ q.MurrayVonNeumannEquiv p :=
  ⟨MurrayVonNeumannEquiv.symm, MurrayVonNeumannEquiv.symm⟩

@[simp] theorem murrayVonNeumannEquiv_self_iff [Fintype m] [NonUnitalSemiring A] [StarRing A]
    {p : CStarMatrix m m A} : p.MurrayVonNeumannEquiv p ↔ IsStarProjection p :=
  ⟨MurrayVonNeumannEquiv.isStarProjection_left, MurrayVonNeumannEquiv.refl⟩

@[simp] theorem murrayVonNeumannEquiv_zero_iff_left [Fintype m] [Fintype n] [NonUnitalSemiring A]
    [StarRing A] [PartialOrder A] [StarOrderedRing A] [IsProperStar A] {p : CStarMatrix m m A} :
    p.MurrayVonNeumannEquiv (0 : CStarMatrix n n A) ↔ p = 0 :=
  ⟨fun ⟨_, _, hvp, hv0⟩ => by
    rw [← hvp, self_mul_conjTranspose_eq_zero.mp hv0, conjTranspose_zero, CStarMatrix.zero_mul],
   fun h => h ▸ ⟨0, .zero, by simp, by simp⟩⟩

@[simp] theorem murrayVonNeumannEquiv_zero_iff_right [Fintype m] [Fintype n] [NonUnitalSemiring A]
    [StarRing A] [PartialOrder A] [StarOrderedRing A] [IsProperStar A] {q : CStarMatrix n n A} :
    (0 : CStarMatrix m m A).MurrayVonNeumannEquiv q ↔ q = 0 := by
  rw [murrayVonNeumannEquiv_comm, murrayVonNeumannEquiv_zero_iff_left]

/-- Padding a star projection by a zero block in the lower-right corner yields an equivalent
projection. -/
theorem murrayVonNeumannEquiv_blockDiag_zero (n : Type*) [Fintype m] [Fintype n]
    [NonUnitalSemiring A] [StarRing A] {p : CStarMatrix m m A} (hp : IsStarProjection p) :
    p.MurrayVonNeumannEquiv (blockDiag p (0 : CStarMatrix n n A)) := by
  have hpt : p.conjTranspose = p := hp.isSelfAdjoint.star_eq
  refine ⟨colBlocks p 0, ?_, by simp [hpt, hp.isIdempotentElem.eq],
    by simp [hpt, hp.isIdempotentElem.eq, blockDiag_def]⟩
  simp [isPartialIsometry_iff, hpt, hp.isIdempotentElem.eq]

/-- Reindexing a star projection along a bijection `e : m ≃ n` yields a Murray–von Neumann
equivalent projection. -/
theorem murrayVonNeumannEquiv_reindexₐ [Fintype m] [Fintype n] [Semiring R]
    [NonUnitalSemiring A] [Module R A] [StarRing A]
    (e : m ≃ n) {p : CStarMatrix m m A} (hp : IsStarProjection p) :
    p.MurrayVonNeumannEquiv (reindexₐ R A e p) := by
  have hpt : p.conjTranspose = p := hp.isSelfAdjoint.star_eq
  refine ⟨reindexₗ R A e (Equiv.refl m) p,
    (IsPartialIsometry.of_isStarProjection hp).reindexₗ e (Equiv.refl m), ?_, ?_⟩
  · rw [reindexₗ_conjTranspose, reindexₗ_mul, hpt, hp.isIdempotentElem.eq, reindexₗ_refl]
  · rw [reindexₗ_conjTranspose, reindexₗ_mul, hpt, hp.isIdempotentElem.eq]; rfl

/-- Swapping the two diagonal blocks of `blockDiag p q` preserves Murray–von Neumann equivalence. -/
theorem murrayVonNeumannEquiv_blockDiag_comm [Fintype m] [Fintype n] [NonUnitalSemiring A]
    [StarRing A] {p : CStarMatrix m m A} {q : CStarMatrix n n A}
    (hp : IsStarProjection p) (hq : IsStarProjection q) :
    (blockDiag p q).MurrayVonNeumannEquiv (blockDiag q p) := by
  simpa using murrayVonNeumannEquiv_reindexₐ (R := ℕ) (Equiv.sumComm m n)
    (isStarProjection_blockDiag_iff.mpr ⟨hp, hq⟩)

/-- Padding a star projection by a zero block in the upper-left corner yields an equivalent
projection. -/
theorem murrayVonNeumannEquiv_zero_blockDiag (m : Type*) [Fintype m] [Fintype n]
    [NonUnitalSemiring A] [StarRing A] {q : CStarMatrix n n A} (hq : IsStarProjection q) :
    q.MurrayVonNeumannEquiv (blockDiag (0 : CStarMatrix m m A) q) :=
  (murrayVonNeumannEquiv_blockDiag_zero m hq).trans
    (murrayVonNeumannEquiv_blockDiag_comm hq (.zero _))

/-- The sum `p₁ + p₂` of two orthogonal star projections is Murray–von Neumann equivalent to their
block-diagonal direct sum `blockDiag p₁ p₂`. -/
theorem murrayVonNeumannEquiv_blockDiag_of_mul_eq_zero [Fintype n] [NonUnitalSemiring A]
    [StarRing A] {p₁ p₂ : CStarMatrix n n A}
    (hp₁ : IsStarProjection p₁) (hp₂ : IsStarProjection p₂) (h₁₂ : p₁ * p₂ = 0) :
    (p₁ + p₂).MurrayVonNeumannEquiv (blockDiag p₁ p₂) := by
  have h₂₁ : p₂ * p₁ = 0 := by
    rw [← hp₂.isSelfAdjoint.star_eq, ← hp₁.isSelfAdjoint.star_eq, ← star_mul, h₁₂, star_zero]
  have hp₁t : p₁.conjTranspose = p₁ := hp₁.isSelfAdjoint.star_eq
  have hp₂t : p₂.conjTranspose = p₂ := hp₂.isSelfAdjoint.star_eq
  exact ⟨colBlocks p₁ p₂, .colBlocks_of_mul_eq_zero hp₁ hp₂ h₁₂,
    by simp [hp₁t, hp₂t, hp₁.isIdempotentElem.eq, hp₂.isIdempotentElem.eq],
    by simp [hp₁t, hp₂t, hp₁.isIdempotentElem.eq, hp₂.isIdempotentElem.eq, h₁₂, h₂₁, blockDiag_def]⟩

/-- Orthogonal sums of pairwise Murray–von Neumann equivalent projections are Murray–von Neumann
equivalent. -/
theorem MurrayVonNeumannEquiv.add_of_mul_eq_zero [Fintype m] [Fintype n] [NonUnitalSemiring A]
    [StarRing A] {p₁ p₂ : CStarMatrix m m A} {q₁ q₂ : CStarMatrix n n A}
    (h₁ : p₁.MurrayVonNeumannEquiv q₁) (h₂ : p₂.MurrayVonNeumannEquiv q₂)
    (hp : p₁ * p₂ = 0) (hq : q₁ * q₂ = 0) :
    (p₁ + p₂).MurrayVonNeumannEquiv (q₁ + q₂) :=
  (murrayVonNeumannEquiv_blockDiag_of_mul_eq_zero h₁.isStarProjection_left
    h₂.isStarProjection_left hp).trans <|
    (h₁.blockDiag h₂).trans
      (murrayVonNeumannEquiv_blockDiag_of_mul_eq_zero h₁.isStarProjection_right
        h₂.isStarProjection_right hq).symm

/-- Unitary conjugation in `CStarMatrix n n A` yields a Murray–von Neumann equivalent projection. -/
theorem murrayVonNeumannEquiv_unitary_conj [Fintype n] [DecidableEq n] [Semiring A] [StarRing A]
    (u : unitary (CStarMatrix n n A)) {p : CStarMatrix n n A} (hp : IsStarProjection p) :
    p.MurrayVonNeumannEquiv
      ((u : CStarMatrix n n A) * p * star (u : CStarMatrix n n A)) := by
  let U : CStarMatrix n n A := u
  have hstar_mul : star (U * p) * (U * p) = p := by
    rw [star_mul, hp.isSelfAdjoint.star_eq, mul_assoc, ← mul_assoc (star U),
      Unitary.coe_star_mul_self u, one_mul, hp.isIdempotentElem.eq]
  have hmul_star : (U * p) * star (U * p) = U * p * star U := by
    rw [star_mul, hp.isSelfAdjoint.star_eq, mul_assoc, ← mul_assoc p, hp.isIdempotentElem.eq,
      mul_assoc]
  refine murrayVonNeumannEquiv_iff_exists_starMul.mpr ⟨U * p, ?_, hstar_mul, hmul_star⟩
  rw [TauCeti.isPartialIsometry_iff, mul_assoc, hstar_mul, mul_assoc, hp.isIdempotentElem.eq]

/-- Unitary conjugacy in `CStarMatrix n n (Unitization R A)` between two projections coming from a
possibly non-unital `A` implies Murray–von Neumann equivalence in `CStarMatrix n n A` itself, since
`CStarMatrix n n A` is a two-sided ideal in `CStarMatrix n n (Unitization R A)`. -/
theorem MurrayVonNeumannEquiv.of_unitary_conj_unitization (R : Type*) [Fintype n] [DecidableEq n]
    [CommSemiring R] [StarRing R] [NonUnitalSemiring A] [StarRing A] [Module R A]
    [IsScalarTower R A A] [SMulCommClass R A A] [StarModule R A]
    {p q : CStarMatrix n n A} (hp : IsStarProjection p)
    (u : unitary (CStarMatrix n n (Unitization R A)))
    (hu : (u : CStarMatrix n n (Unitization R A)) *
        p.map (Unitization.inrNonUnitalStarAlgHom R A) *
        star (u : CStarMatrix n n (Unitization R A)) =
      q.map (Unitization.inrNonUnitalStarAlgHom R A)) :
    p.MurrayVonNeumannEquiv q := by
  let ι := Unitization.inrNonUnitalStarAlgHom R A
  have hι : Function.Injective fun M : CStarMatrix n n A => M.map ι :=
    CStarMatrix.map_injective Unitization.inr_injective
  let U : CStarMatrix n n (Unitization R A) := u
  let w : CStarMatrix n n (Unitization R A) := U * p.map ι
  let v : CStarMatrix n n A := ofMatrix fun i j => (w i j).snd
  have hv_map : v.map ι = w := CStarMatrix.ext fun i j => Unitization.ext
    (by
      have hw_fst : (w i j).fst = 0 := by
        dsimp only [w]
        rw [mul_apply, show (∑ k, U i k * (p.map ι) k j).fst = ∑ k, (U i k * (p.map ι) k j).fst
          from map_sum (Unitization.fstHom R A) _ _]
        exact Finset.sum_eq_zero fun k _ => by simp [ι, Unitization.fst_mul]
      simp [ι, hw_fst])
    rfl
  have hstar_v : (star v).map ι = star w := (map_conjTranspose ι v).trans (congrArg star hv_map)
  have hpι : IsStarProjection (p.map ι) := hp.map (mapₙₐ ι)
  have hstar_w : star w * w = p.map ι := by
    rw [star_mul, hpι.isSelfAdjoint.star_eq, mul_assoc, ← mul_assoc (star U),
      Unitary.coe_star_mul_self u, one_mul, hpι.isIdempotentElem.eq]
  have hw_star : w * star w = q.map ι := by
    rw [star_mul, hpι.isSelfAdjoint.star_eq, mul_assoc, ← mul_assoc (p.map ι),
      hpι.isIdempotentElem.eq, ← mul_assoc]; exact hu
  refine murrayVonNeumannEquiv_iff_exists_starMul.mpr ⟨v, ?_, ?_, ?_⟩
  · rw [TauCeti.isPartialIsometry_iff]; apply hι; dsimp only
    rw [map_mul, map_mul, hstar_v, hv_map, mul_assoc, hstar_w]
    simp only [w, mul_assoc, hpι.isIdempotentElem.eq]
  · apply hι; dsimp only; rw [map_mul, hstar_v, hv_map, hstar_w]
  · apply hι; dsimp only; rw [map_mul, hstar_v, hv_map, hw_star]

end MurrayVonNeumannEquiv

section StabilizedConjugacy

variable {m n A : Type*}

namespace IsPartialIsometry

private theorem mul_proj_right [Fintype m] [Fintype n] [NonUnitalSemiring A] [StarRing A]
    {v : CStarMatrix n m A} {p : CStarMatrix m m A}
    (hv : v.IsPartialIsometry) (hp : v.conjTranspose * v = p) : v * p = v := by
  rw [← hp, ← CStarMatrix.mul_assoc, hv.mul_conjTranspose_mul_self]

private theorem proj_mul_conjTranspose [Fintype m] [Fintype n] [NonUnitalSemiring A] [StarRing A]
    {v : CStarMatrix n m A} {p : CStarMatrix m m A}
    (hv : v.IsPartialIsometry) (hp : v.conjTranspose * v = p) :
    p * v.conjTranspose = v.conjTranspose := by
  rw [← hp, hv.conjTranspose_mul_conjTranspose]

private theorem proj_mul_left [Fintype m] [Fintype n] [NonUnitalSemiring A] [StarRing A]
    {v : CStarMatrix n m A} {q : CStarMatrix n n A}
    (hv : v.IsPartialIsometry) (hq : v * v.conjTranspose = q) : q * v = v := by
  rw [← hq, hv.mul_conjTranspose_mul_self]

private theorem conjTranspose_mul_proj [Fintype m] [Fintype n] [NonUnitalSemiring A] [StarRing A]
    {v : CStarMatrix n m A} {q : CStarMatrix n n A}
    (hv : v.IsPartialIsometry) (hq : v * v.conjTranspose = q) :
    v.conjTranspose * q = v.conjTranspose := by
  rw [← hq, ← CStarMatrix.mul_assoc, hv.conjTranspose_mul_conjTranspose]

/-- For a rectangular partial isometry `v : CStarMatrix n m A` with `v.conjTranspose * v = p` and
`v * v.conjTranspose = q`, the four-block matrix `fromBlocks (1 - p) v.conjTranspose v (1 - q)` is a
self-adjoint unitary in `CStarMatrix (m ⊕ n) (m ⊕ n) A` conjugating `blockDiag p 0` to
`blockDiag 0 q`. -/
def stabilizedConjUnitary [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    [Ring A] [StarRing A] {v : CStarMatrix n m A} {p : CStarMatrix m m A} {q : CStarMatrix n n A}
    (hv : v.IsPartialIsometry) (hp : v.conjTranspose * v = p) (hq : v * v.conjTranspose = q) :
    unitary (CStarMatrix (m ⊕ n) (m ⊕ n) A) :=
  ⟨fromBlocks (1 - p) v.conjTranspose v (1 - q), by
    let w : CStarMatrix (m ⊕ n) (m ⊕ n) A := fromBlocks (1 - p) v.conjTranspose v (1 - q)
    have hp_proj : IsStarProjection p := hp ▸ hv.isStarProjection_conjTranspose_mul_self
    have hq_proj : IsStarProjection q := hq ▸ hv.isStarProjection_mul_conjTranspose_self
    have hw_sa : star w = w := by
      simp [w, star_fromBlocks, hp_proj.isSelfAdjoint.star_eq, hq_proj.isSelfAdjoint.star_eq]
    have hw_sq : w * w = 1 := by
      rw [show w = fromBlocks (1 - p) v.conjTranspose v (1 - q) from rfl,
        fromBlocks_mul, ← fromBlocks_one]
      simp [CStarMatrix.mul_sub, CStarMatrix.sub_mul, hp, hq, hv.mul_proj_right hp,
        hv.proj_mul_conjTranspose hp, hv.proj_mul_left hq, hv.conjTranspose_mul_proj hq,
        hp_proj.isIdempotentElem.eq, hq_proj.isIdempotentElem.eq, sub_add_cancel, add_sub_cancel]
    exact Unitary.mem_iff.mpr ⟨by change star w * w = 1; rw [hw_sa, hw_sq],
      by change w * star w = 1; rw [hw_sa, hw_sq]⟩⟩

@[simp] theorem coe_stabilizedConjUnitary [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    [Ring A] [StarRing A] {v : CStarMatrix n m A} {p : CStarMatrix m m A} {q : CStarMatrix n n A}
    (hv : v.IsPartialIsometry) (hp : v.conjTranspose * v = p) (hq : v * v.conjTranspose = q) :
    ((hv.stabilizedConjUnitary hp hq : unitary (CStarMatrix (m ⊕ n) (m ⊕ n) A)) :
      CStarMatrix (m ⊕ n) (m ⊕ n) A) = fromBlocks (1 - p) v.conjTranspose v (1 - q) := (rfl)

theorem isSelfAdjoint_stabilizedConjUnitary [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    [Ring A] [StarRing A] {v : CStarMatrix n m A} {p : CStarMatrix m m A} {q : CStarMatrix n n A}
    (hv : v.IsPartialIsometry) (hp : v.conjTranspose * v = p) (hq : v * v.conjTranspose = q) :
    IsSelfAdjoint
      ((hv.stabilizedConjUnitary hp hq : unitary _) : CStarMatrix (m ⊕ n) (m ⊕ n) A) := by
  have hp_proj : IsStarProjection p := hp ▸ hv.isStarProjection_conjTranspose_mul_self
  have hq_proj : IsStarProjection q := hq ▸ hv.isStarProjection_mul_conjTranspose_self
  simp [isSelfAdjoint_iff, star_fromBlocks, hp_proj.isSelfAdjoint.star_eq,
    hq_proj.isSelfAdjoint.star_eq]

/-- `stabilizedConjUnitary` conjugates `blockDiag p 0` to `blockDiag 0 q`. -/
theorem stabilizedConjUnitary_conj [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    [Ring A] [StarRing A] {v : CStarMatrix n m A} {p : CStarMatrix m m A} {q : CStarMatrix n n A}
    (hv : v.IsPartialIsometry) (hp : v.conjTranspose * v = p) (hq : v * v.conjTranspose = q) :
    (hv.stabilizedConjUnitary hp hq : CStarMatrix (m ⊕ n) (m ⊕ n) A) * blockDiag p 0 *
        star (hv.stabilizedConjUnitary hp hq : CStarMatrix (m ⊕ n) (m ⊕ n) A) =
      blockDiag 0 q := by
  have hp_proj : IsStarProjection p := hp ▸ hv.isStarProjection_conjTranspose_mul_self
  rw [(hv.isSelfAdjoint_stabilizedConjUnitary hp hq).star_eq, coe_stabilizedConjUnitary,
    blockDiag_def, blockDiag_def, fromBlocks_mul, fromBlocks_mul]
  simp [CStarMatrix.mul_sub, CStarMatrix.sub_mul, hq, hv.mul_proj_right hp,
    hp_proj.isIdempotentElem.eq]

end IsPartialIsometry

/-- The `-1`-eigenspace block matrix `(2⁻¹ : ℝ) • fromBlocks p (-v.conjTranspose) (-v) q`
associated with `v : CStarMatrix n m A`, `p : CStarMatrix m m A`, and `q : CStarMatrix n n A`. -/
def stabilizedNegProj [Neg A] [Star A] [SMul ℝ A]
    (v : CStarMatrix n m A) (p : CStarMatrix m m A) (q : CStarMatrix n n A) :
    CStarMatrix (m ⊕ n) (m ⊕ n) A :=
  (2⁻¹ : ℝ) • fromBlocks p (-v.conjTranspose) (-v) q

theorem stabilizedNegProj_def [Neg A] [Star A] [SMul ℝ A]
    (v : CStarMatrix n m A) (p : CStarMatrix m m A) (q : CStarMatrix n n A) :
    stabilizedNegProj v p q = (2⁻¹ : ℝ) • fromBlocks p (-v.conjTranspose) (-v) q := (rfl)

/-- Explicit rotation curve of `(m ⊕ n) × (m ⊕ n)` matrices interpolating between `blockDiag p 0`
(at `t = 0`) and `blockDiag 0 q` (at `t = 1`), defined without using `1` so that it applies equally
to non-unital C⋆-algebras. -/
def stabilizedProjRot [Star A] [SMul ℂ A]
    (v : CStarMatrix n m A) (p : CStarMatrix m m A) (q : CStarMatrix n n A) (t : ℝ) :
    CStarMatrix (m ⊕ n) (m ⊕ n) A :=
  let c : ℂ := ↑(Real.cos (Real.pi * t / 2))
  let s : ℂ := ↑(Real.sin (Real.pi * t / 2))
  fromBlocks ((c ^ 2) • p) ((Complex.I * s * c) • v.conjTranspose)
    ((-Complex.I * s * c) • v) ((s ^ 2) • q)

theorem stabilizedProjRot_def [Star A] [SMul ℂ A]
    (v : CStarMatrix n m A) (p : CStarMatrix m m A) (q : CStarMatrix n n A) (t : ℝ) :
    stabilizedProjRot v p q t =
      fromBlocks (((Real.cos (Real.pi * t / 2) : ℂ) ^ 2) • p)
        ((Complex.I * ↑(Real.sin (Real.pi * t / 2)) * ↑(Real.cos (Real.pi * t / 2))) •
          v.conjTranspose)
        ((-Complex.I * ↑(Real.sin (Real.pi * t / 2)) * ↑(Real.cos (Real.pi * t / 2))) • v)
        (((Real.sin (Real.pi * t / 2) : ℂ) ^ 2) • q) := (rfl)

@[simp] theorem stabilizedProjRot_zero [AddCommMonoid A] [Star A] [Module ℂ A]
    (v : CStarMatrix n m A) (p : CStarMatrix m m A) (q : CStarMatrix n n A) :
    stabilizedProjRot v p q 0 = blockDiag p 0 := by simp [stabilizedProjRot, blockDiag_def]

@[simp] theorem stabilizedProjRot_one [AddCommMonoid A] [Star A] [Module ℂ A]
    (v : CStarMatrix n m A) (p : CStarMatrix m m A) (q : CStarMatrix n n A) :
    stabilizedProjRot v p q 1 = blockDiag 0 q := by simp [stabilizedProjRot, blockDiag_def]

/-- At the midpoint `t = 1 / 2`, `stabilizedProjRot` passes through
`fromBlocks ((2⁻¹ : ℂ) • p) ((I / 2) • v.conjTranspose) ((-I / 2) • v) ((2⁻¹ : ℂ) • q)`. -/
theorem stabilizedProjRot_half [AddCommMonoid A] [Star A] [Module ℂ A]
    (v : CStarMatrix n m A) (p : CStarMatrix m m A) (q : CStarMatrix n n A) :
    stabilizedProjRot v p q (1 / 2) =
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

/-- `stabilizedProjRot v p q` is continuous on `ℝ` for any (possibly non-unital) C⋆-algebra `A`. -/
theorem continuous_stabilizedProjRot [NonUnitalCStarAlgebra A]
    (v : CStarMatrix n m A) (p : CStarMatrix m m A) (q : CStarMatrix n n A) :
    Continuous (stabilizedProjRot v p q) := by
  have hθ : Continuous fun t : ℝ => Real.pi * t / 2 := by fun_prop
  have hc : Continuous fun t : ℝ => (Real.cos (Real.pi * t / 2) : ℂ) :=
    Complex.continuous_ofReal.comp (Real.continuous_cos.comp hθ)
  have hs : Continuous fun t : ℝ => (Real.sin (Real.pi * t / 2) : ℂ) :=
    Complex.continuous_ofReal.comp (Real.continuous_sin.comp hθ)
  exact continuous_fromBlocks ((hc.pow 2).smul continuous_const)
    (((continuous_const.mul hs).mul hc).smul continuous_const)
    (((continuous_const.mul hs).mul hc).smul continuous_const)
    ((hs.pow 2).smul continuous_const)

namespace IsPartialIsometry

theorem stabilizedNegProj_eq_half_one_sub [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    [Ring A] [StarRing A] [Module ℝ A]
    {v : CStarMatrix n m A} {p : CStarMatrix m m A} {q : CStarMatrix n n A}
    (hv : v.IsPartialIsometry) (hp : v.conjTranspose * v = p) (hq : v * v.conjTranspose = q) :
    stabilizedNegProj v p q =
      (2⁻¹ : ℝ) • (1 - (hv.stabilizedConjUnitary hp hq : CStarMatrix (m ⊕ n) (m ⊕ n) A)) := by
  rw [stabilizedNegProj_def, coe_stabilizedConjUnitary, ← fromBlocks_one, fromBlocks_sub]; simp

theorem isStarProjection_stabilizedNegProj [Fintype m] [Fintype n]
    [NonUnitalRing A] [StarRing A] [Module ℝ A] [IsScalarTower ℝ A A] [SMulCommClass ℝ A A]
    [StarModule ℝ A] {v : CStarMatrix n m A} {p : CStarMatrix m m A} {q : CStarMatrix n n A}
    (hv : v.IsPartialIsometry) (hp : v.conjTranspose * v = p) (hq : v * v.conjTranspose = q) :
    IsStarProjection (stabilizedNegProj v p q) := by
  have hp_proj : IsStarProjection p := hp ▸ hv.isStarProjection_conjTranspose_mul_self
  have hq_proj : IsStarProjection q := hq ▸ hv.isStarProjection_mul_conjTranspose_self
  refine ⟨?_, ?_⟩
  · rw [IsIdempotentElem, stabilizedNegProj_def, CStarMatrix.smul_mul_smul, fromBlocks_mul]
    simp only [CStarMatrix.neg_mul, CStarMatrix.mul_neg, neg_neg, hp_proj.isIdempotentElem.eq,
      hq_proj.isIdempotentElem.eq, hp, hq, hv.mul_proj_right hp, hv.proj_mul_conjTranspose hp,
      hv.proj_mul_left hq, hv.conjTranspose_mul_proj hq,
      ← two_smul ℝ, fromBlocks_smul, smul_neg, smul_smul]
    norm_num
  · simp [isSelfAdjoint_iff, stabilizedNegProj_def, star_fromBlocks,
      hp_proj.isSelfAdjoint.star_eq, hq_proj.isSelfAdjoint.star_eq]

/-- At `π`, the exponential unitary of `stabilizedNegProj v p q` is `stabilizedConjUnitary`. -/
theorem expUnitary_pi_stabilizedNegProj [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    {v : CStarMatrix n m A} {p : CStarMatrix m m A} {q : CStarMatrix n n A}
    (hv : v.IsPartialIsometry) (hp : v.conjTranspose * v = p) (hq : v * v.conjTranspose = q) :
    selfAdjoint.expUnitary
      (Real.pi • ⟨stabilizedNegProj v p q,
        (hv.isStarProjection_stabilizedNegProj hp hq).isSelfAdjoint⟩) =
      hv.stabilizedConjUnitary hp hq := by
  rw [show (⟨stabilizedNegProj v p q,
      (hv.isStarProjection_stabilizedNegProj hp hq).isSelfAdjoint⟩ :
      selfAdjoint (CStarMatrix (m ⊕ n) (m ⊕ n) A)) =
      ⟨(2⁻¹ : ℝ) • (1 - (hv.stabilizedConjUnitary hp hq : CStarMatrix (m ⊕ n) (m ⊕ n) A)),
        (Unitary.isStarProjection_half_one_sub _
          (hv.isSelfAdjoint_stabilizedConjUnitary hp hq)).isSelfAdjoint⟩ from
    Subtype.ext (hv.stabilizedNegProj_eq_half_one_sub hp hq)]
  exact Unitary.expUnitary_pi_smul_half_one_sub _ (hv.isSelfAdjoint_stabilizedConjUnitary hp hq)

/-- Continuous path `t ↦ expUnitary ((t * π) • r)` from `1` to `stabilizedConjUnitary`. -/
def stabilizedConjUnitaryPath [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    {v : CStarMatrix n m A} {p : CStarMatrix m m A} {q : CStarMatrix n n A}
    (hv : v.IsPartialIsometry) (hp : v.conjTranspose * v = p) (hq : v * v.conjTranspose = q) :
    Path (1 : unitary (CStarMatrix (m ⊕ n) (m ⊕ n) A)) (hv.stabilizedConjUnitary hp hq) :=
  (selfAdjoint.expUnitaryPathToOne
    (Real.pi • ⟨stabilizedNegProj v p q,
      (hv.isStarProjection_stabilizedNegProj hp hq).isSelfAdjoint⟩)).cast
    rfl (hv.expUnitary_pi_stabilizedNegProj hp hq).symm

theorem joined_one_stabilizedConjUnitary [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    {v : CStarMatrix n m A} {p : CStarMatrix m m A} {q : CStarMatrix n n A}
    (hv : v.IsPartialIsometry) (hp : v.conjTranspose * v = p) (hq : v * v.conjTranspose = q) :
    Joined (1 : unitary (CStarMatrix (m ⊕ n) (m ⊕ n) A)) (hv.stabilizedConjUnitary hp hq) :=
  ⟨hv.stabilizedConjUnitaryPath hp hq⟩

/-- Every point on `stabilizedProjRot v p q` associated with a partial isometry `v` is a star
projection. -/
theorem isStarProjection_stabilizedProjRot [Fintype m] [Fintype n]
    [NonUnitalSemiring A] [StarRing A] [Module ℂ A] [IsScalarTower ℂ A A] [SMulCommClass ℂ A A]
    [StarModule ℂ A] {v : CStarMatrix n m A} {p : CStarMatrix m m A} {q : CStarMatrix n n A}
    (hv : v.IsPartialIsometry) (hp : v.conjTranspose * v = p) (hq : v * v.conjTranspose = q)
    (t : ℝ) : IsStarProjection (stabilizedProjRot v p q t) := by
  set c : ℂ := ↑(Real.cos (Real.pi * t / 2))
  set s : ℂ := ↑(Real.sin (Real.pi * t / 2))
  have hcs : c ^ 2 + s ^ 2 = 1 := by
    simp only [c, s, ← Complex.ofReal_pow, ← Complex.ofReal_add, Real.cos_sq_add_sin_sq,
      Complex.ofReal_one]
  have hI : Complex.I ^ 2 = -1 := Complex.I_sq
  have hp_proj : IsStarProjection p := hp ▸ hv.isStarProjection_conjTranspose_mul_self
  have hq_proj : IsStarProjection q := hq ▸ hv.isStarProjection_mul_conjTranspose_self
  refine ⟨?_, ?_⟩
  · rw [IsIdempotentElem, stabilizedProjRot_def]
    change fromBlocks (c ^ 2 • p) ((Complex.I * s * c) • v.conjTranspose)
        ((-Complex.I * s * c) • v) (s ^ 2 • q) *
      fromBlocks (c ^ 2 • p) ((Complex.I * s * c) • v.conjTranspose)
        ((-Complex.I * s * c) • v) (s ^ 2 • q) =
      fromBlocks (c ^ 2 • p) ((Complex.I * s * c) • v.conjTranspose)
        ((-Complex.I * s * c) • v) (s ^ 2 • q)
    rw [fromBlocks_mul]
    simp only [CStarMatrix.smul_mul_smul, hp_proj.isIdempotentElem.eq, hq_proj.isIdempotentElem.eq,
      hp, hq, hv.mul_proj_right hp, hv.proj_mul_left hq, hv.proj_mul_conjTranspose hp,
      hv.conjTranspose_mul_proj hq, ← add_smul, fromBlocks_inj]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> congr 1
    · linear_combination c ^ 2 * hcs - s ^ 2 * c ^ 2 * hI
    · linear_combination (Complex.I * s * c) * hcs
    · linear_combination (-Complex.I * s * c) * hcs
    · linear_combination s ^ 2 * hcs - s ^ 2 * c ^ 2 * hI
  · rw [isSelfAdjoint_iff, stabilizedProjRot_def]
    change star (fromBlocks (c ^ 2 • p) ((Complex.I * s * c) • v.conjTranspose)
        ((-Complex.I * s * c) • v) (s ^ 2 • q)) =
      fromBlocks (c ^ 2 • p) ((Complex.I * s * c) • v.conjTranspose)
        ((-Complex.I * s * c) • v) (s ^ 2 • q)
    rw [star_fromBlocks, star_smul, star_smul, conjTranspose_smul, conjTranspose_smul,
      conjTranspose_conjTranspose, hp_proj.isSelfAdjoint.star_eq, hq_proj.isSelfAdjoint.star_eq]
    simp [show star c = c from Complex.conj_ofReal _, show star s = s from Complex.conj_ofReal _]

/-- In a unital C⋆-algebra, conjugating `blockDiag p 0` by `expUnitary ((t * π) • r)` reproduces
`stabilizedProjRot v p q t` at every `t : ℝ`. -/
theorem expUnitary_conj_blockDiag_eq_stabilizedProjRot [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    {v : CStarMatrix n m A} {p : CStarMatrix m m A} {q : CStarMatrix n n A}
    (hv : v.IsPartialIsometry) (hp : v.conjTranspose * v = p) (hq : v * v.conjTranspose = q)
    (t : ℝ) :
    ((selfAdjoint.expUnitary ((t * Real.pi) •
        ⟨stabilizedNegProj v p q,
          (hv.isStarProjection_stabilizedNegProj hp hq).isSelfAdjoint⟩) : unitary _) :
      CStarMatrix (m ⊕ n) (m ⊕ n) A) * blockDiag p 0 *
      star ((selfAdjoint.expUnitary ((t * Real.pi) •
        ⟨stabilizedNegProj v p q,
          (hv.isStarProjection_stabilizedNegProj hp hq).isSelfAdjoint⟩) : unitary _) :
        CStarMatrix (m ⊕ n) (m ⊕ n) A) =
      stabilizedProjRot v p q t := by
  have hr := hv.isStarProjection_stabilizedNegProj hp hq
  let U : CStarMatrix (m ⊕ n) (m ⊕ n) A :=
    ((selfAdjoint.expUnitary ((t * Real.pi) • ⟨stabilizedNegProj v p q, hr.isSelfAdjoint⟩) :
      unitary _) : CStarMatrix (m ⊕ n) (m ⊕ n) A)
  set c : ℂ := ↑(Real.cos (Real.pi * t / 2))
  set s : ℂ := ↑(Real.sin (Real.pi * t / 2))
  set z : ℂ := c + s * Complex.I
  set α : ℂ := (Complex.exp (t * Real.pi * Complex.I) - 1) * 2⁻¹
  have hcs : c ^ 2 + s ^ 2 = 1 := by
    simp only [c, s, ← Complex.ofReal_pow, ← Complex.ofReal_add, Real.cos_sq_add_sin_sq,
      Complex.ofReal_one]
  have hI : Complex.I ^ 2 = -1 := Complex.I_sq
  have hc_conj : star c = c := Complex.conj_ofReal _
  have hs_conj : star s = s := Complex.conj_ofReal _
  have hzz : z * star z = 1 := by
    have hsz : star z = c - s * Complex.I := by
      simp only [z, star_add, star_mul, hc_conj, hs_conj, Complex.star_def, Complex.conj_I]; ring
    rw [hsz]; linear_combination hcs - s ^ 2 * hI
  have hp_proj : IsStarProjection p := hp ▸ hv.isStarProjection_conjTranspose_mul_self
  have hexp_u : U = 1 + α • fromBlocks p (-v.conjTranspose) (-v) q := by
    have hu := hr.coe_expUnitary_smul (t * Real.pi)
    change U = _ at hu
    rw [hu, stabilizedNegProj_def, show (2⁻¹ : ℝ) • fromBlocks p (-v.conjTranspose) (-v) q =
        ((2⁻¹ : ℝ) : ℂ) • fromBlocks p (-v.conjTranspose) (-v) q from
      ext fun _ _ => (Complex.coe_smul (2⁻¹ : ℝ) _).symm, smul_smul]
    congr 2; push_cast; rfl
  have hα : α = (z ^ 2 - 1) * 2⁻¹ := by
    have hexp : Complex.exp (t * Real.pi * Complex.I) = z ^ 2 := by
      have hsplit : (t : ℂ) * Real.pi * Complex.I =
          ((Real.pi * t / 2 : ℝ) : ℂ) * Complex.I + ((Real.pi * t / 2 : ℝ) : ℂ) * Complex.I := by
        push_cast; ring
      rw [hsplit, Complex.exp_add, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
        sq]
    rw [← hexp]
  have h1α : 1 + α = z * c := by
    rw [hα]; simp only [z]; linear_combination -((1 : ℂ) / 2) * hcs + (s ^ 2 / 2) * hI
  have hnα : -α = z * (-Complex.I * s) := by
    rw [hα]; simp only [z]; linear_combination -((1 : ℂ) / 2) * hcs + (s ^ 2 / 2) * hI
  let M : CStarMatrix (m ⊕ n) (m ⊕ n) A := fromBlocks (c • p) 0 ((-Complex.I * s) • v) 0
  have humul : U * blockDiag p 0 = z • M := by
    have hp1 : p + α • p = (z * c) • p := by rw [← h1α, add_smul, one_smul]
    have hv1 : -(α • v) = (z * (-Complex.I * s)) • v := by rw [← neg_smul, hnα]
    rw [hexp_u, ← fromBlocks_one, fromBlocks_smul, fromBlocks_add, blockDiag_def, fromBlocks_mul]
    simp [M, fromBlocks_smul, CStarMatrix.add_mul, CStarMatrix.smul_mul,
      hp_proj.isIdempotentElem.eq, hv.mul_proj_right hp, hp1, hv1, smul_smul]
  change U * blockDiag p 0 * star U = stabilizedProjRot v p q t
  calc U * blockDiag p 0 * star U
      = (U * blockDiag p 0) * star (U * blockDiag p 0) := by
          symm
          rw [star_mul, star_blockDiag, hp_proj.isSelfAdjoint.star_eq, star_zero, ← mul_assoc,
            mul_assoc U, blockDiag_mul, hp_proj.isIdempotentElem.eq, mul_zero]
    _ = M * star M := by rw [humul, star_smul, CStarMatrix.smul_mul_smul, hzz, one_smul]
    _ = stabilizedProjRot v p q t := by
          rw [stabilizedProjRot_def]
          simp only [M, star_fromBlocks, star_smul, star_zero, conjTranspose_smul,
            conjTranspose_zero, hp_proj.isSelfAdjoint.star_eq, hc_conj, hs_conj, star_mul,
            star_neg, Complex.star_def, Complex.conj_I, neg_neg, fromBlocks_mul,
            CStarMatrix.smul_mul_smul, CStarMatrix.mul_zero, add_zero, hp_proj.isIdempotentElem.eq,
            hv.proj_mul_conjTranspose hp, hv.mul_proj_right hp, hq]
          change fromBlocks ((c * c) • p) ((c * (s * Complex.I)) • v.conjTranspose)
              (((-Complex.I * s) * c) • v) (((-Complex.I * s) * (s * Complex.I)) • q) =
            fromBlocks (c ^ 2 • p) ((Complex.I * s * c) • v.conjTranspose)
              ((-Complex.I * s * c) • v) (s ^ 2 • q)
          rw [fromBlocks_inj]
          exact ⟨by congr 1; ring, by congr 1; ring, rfl,
            by congr 1; linear_combination -s ^ 2 * hI⟩

/-- Continuous path in the space of matrix star projections from `blockDiag p 0` to `blockDiag 0 q`
associated with a rectangular partial isometry `v`. -/
def stabilizedProjPath [Fintype m] [Fintype n] [NonUnitalCStarAlgebra A]
    {v : CStarMatrix n m A} {p : CStarMatrix m m A} {q : CStarMatrix n n A}
    (hv : v.IsPartialIsometry) (hp : v.conjTranspose * v = p) (hq : v * v.conjTranspose = q) :
    Path (⟨blockDiag p 0,
        isStarProjection_blockDiag_iff.mpr
          ⟨hp ▸ hv.isStarProjection_conjTranspose_mul_self, IsStarProjection.zero _⟩⟩ :
        {P : CStarMatrix (m ⊕ n) (m ⊕ n) A // IsStarProjection P})
      ⟨blockDiag 0 q,
        isStarProjection_blockDiag_iff.mpr
          ⟨IsStarProjection.zero _, hq ▸ hv.isStarProjection_mul_conjTranspose_self⟩⟩ where
  toFun t := ⟨stabilizedProjRot v p q t, hv.isStarProjection_stabilizedProjRot hp hq t⟩
  continuous_toFun :=
    ((continuous_stabilizedProjRot v p q).comp continuous_subtype_val).subtype_mk _
  source' := Subtype.ext (stabilizedProjRot_zero v p q)
  target' := Subtype.ext (stabilizedProjRot_one v p q)

end IsPartialIsometry

/-- Over any star ring, Murray–von Neumann equivalent projections become conjugate by a
self-adjoint unitary in `CStarMatrix (m ⊕ n) (m ⊕ n) A`. -/
theorem MurrayVonNeumannEquiv.exists_unitary_blockDiag_eq [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] [Ring A] [StarRing A]
    {p : CStarMatrix m m A} {q : CStarMatrix n n A} (h : p.MurrayVonNeumannEquiv q) :
    ∃ w : unitary (CStarMatrix (m ⊕ n) (m ⊕ n) A),
      IsSelfAdjoint (w : CStarMatrix (m ⊕ n) (m ⊕ n) A) ∧
      (w : CStarMatrix (m ⊕ n) (m ⊕ n) A) * blockDiag p 0 *
        star (w : CStarMatrix (m ⊕ n) (m ⊕ n) A) = blockDiag 0 q := by
  rcases h with ⟨v, hv, hp, hq⟩
  exact ⟨hv.stabilizedConjUnitary hp hq, hv.isSelfAdjoint_stabilizedConjUnitary hp hq,
    hv.stabilizedConjUnitary_conj hp hq⟩

/-- Over a unital C⋆-algebra, Murray–von Neumann equivalent projections become conjugate by a
unitary in the identity path component of `unitary (CStarMatrix (m ⊕ n) (m ⊕ n) A)`. -/
theorem MurrayVonNeumannEquiv.exists_joined_one_unitary_blockDiag_eq [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    {p : CStarMatrix m m A} {q : CStarMatrix n n A} (h : p.MurrayVonNeumannEquiv q) :
    ∃ w : unitary (CStarMatrix (m ⊕ n) (m ⊕ n) A),
      Joined 1 w ∧
      (w : CStarMatrix (m ⊕ n) (m ⊕ n) A) * blockDiag p 0 *
        star (w : CStarMatrix (m ⊕ n) (m ⊕ n) A) = blockDiag 0 q := by
  rcases h with ⟨v, hv, hp, hq⟩
  exact ⟨hv.stabilizedConjUnitary hp hq, hv.joined_one_stabilizedConjUnitary hp hq,
    hv.stabilizedConjUnitary_conj hp hq⟩

/-- Over any (possibly non-unital) C⋆-algebra, Murray–von Neumann equivalent projections are joined
by a continuous path of projections after stabilization to `CStarMatrix (m ⊕ n) (m ⊕ n) A`. -/
theorem MurrayVonNeumannEquiv.joined_blockDiag [Fintype m] [Fintype n] [NonUnitalCStarAlgebra A]
    {p : CStarMatrix m m A} {q : CStarMatrix n n A} (h : p.MurrayVonNeumannEquiv q) :
    Joined
      (⟨blockDiag p 0,
        isStarProjection_blockDiag_iff.mpr
          ⟨h.isStarProjection_left, IsStarProjection.zero _⟩⟩ :
        {P : CStarMatrix (m ⊕ n) (m ⊕ n) A // IsStarProjection P})
      ⟨blockDiag 0 q,
        isStarProjection_blockDiag_iff.mpr
          ⟨IsStarProjection.zero _, h.isStarProjection_right⟩⟩ := by
  rcases h with ⟨v, hv, hp, hq⟩
  exact ⟨hv.stabilizedProjPath hp hq⟩

end StabilizedConjugacy

end CStarMatrix
