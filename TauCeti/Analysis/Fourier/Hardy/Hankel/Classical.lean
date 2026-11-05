/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fourier.Hardy.Hankel.Basic

/-!
# The classical Hankel matrix and the negative-mode flip

The negative Fourier modes, ordered as `e₋₁, e₋₂, …`, form a Hilbert basis of the
orthogonal complement of boundary Hardy space. The unitary `hardyFlip` sends `e₋ₙ₋₁`
to `eₙ`. Composing it with the existing, orthogonal-complement-valued Hankel operator
of the reflected symbol gives `classicalHankel a`, whose matrix is `â(i + j + 1)`.

This comparison fixes the reflection convention in products of classical Hankel
matrices. In particular, the Toeplitz product defect is the negative of
`classicalHankel a ∘ classicalHankel (b ∘ Neg.neg)`. These are the Hankel operators
used in finite Toeplitz product identities.

## References

* A. Böttcher and B. Silbermann, *Introduction to Large Truncated Toeplitz Matrices*,
  for the classical Hankel convention and its role in finite-section products.
-/

public section

noncomputable section

open MeasureTheory Submodule
open scoped ENNReal InnerProductSpace

namespace TauCeti

/-- Every strictly negative Fourier mode belongs to the orthogonal complement of Hardy space. -/
theorem fourierBasis_mem_hardySubmodule_orthogonal (n : ℕ) :
    fourierBasis (T := 1) (-(n : ℤ) - 1) ∈ hardySubmoduleᗮ := by
  rw [hardySubmodule_orthogonal_eq]
  exact Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨n, rfl⟩)

private def negativeMode (n : ℕ) : ↥hardySubmoduleᗮ :=
  ⟨fourierBasis (T := 1) (-(n : ℤ) - 1), fourierBasis_mem_hardySubmodule_orthogonal n⟩

private theorem coe_negativeMode (n : ℕ) :
    (negativeMode n : Lp ℂ 2 (AddCircle.haarAddCircle (T := 1))) =
      fourierBasis (T := 1) (-(n : ℤ) - 1) :=
  (rfl)

private theorem orthonormal_negativeMode : Orthonormal ℂ negativeMode := by
  apply (hardySubmoduleᗮ.subtypeₗᵢ.orthonormal_comp_iff).mp
  exact (fourierBasis (T := 1)).orthonormal.comp (fun n : ℕ ↦ -(n : ℤ) - 1)
    (by intro i j h; simpa using h)

/-- The negative Fourier basis of the orthogonal complement of Hardy space, ordered
`e₋₁, e₋₂, …`. -/
def negativeHardyBasis : HilbertBasis ℕ ℂ ↥hardySubmoduleᗮ :=
  HilbertBasis.mkOfOrthogonalEqBot orthonormal_negativeMode (by
    apply le_antisymm _ bot_le
    intro x hx
    apply Subtype.ext
    simp only [Submodule.coe_zero]
    apply (fourierBasis (T := 1)).repr.injective
    rw [map_zero]
    apply lp.ext
    funext n
    simp only [lp.coeFn_zero, Pi.zero_apply, fourierBasis_repr]
    by_cases hn : n < 0
    · obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le (by omega : 0 ≤ -n - 1)
      have heq : n = -(k : ℤ) - 1 := by omega
      rw [heq, ← fourierBasis_repr, HilbertBasis.repr_apply_apply]
      exact (Submodule.mem_orthogonal _ _).mp hx (negativeMode k)
        (Submodule.subset_span ⟨k, rfl⟩)
    · obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le (by omega : 0 ≤ n)
      exact (mem_hardySubmodule_orthogonal_iff _).mp x.property k)

/-- Negative Hardy basis vectors are the corresponding ambient Fourier modes. -/
@[simp]
theorem coe_negativeHardyBasis (n : ℕ) :
    (negativeHardyBasis n : Lp ℂ 2 (AddCircle.haarAddCircle (T := 1))) =
      fourierBasis (T := 1) (-(n : ℤ) - 1) := by
  simp only [negativeHardyBasis, HilbertBasis.coe_mkOfOrthogonalEqBot, coe_negativeMode]

/-- Coordinates in the negative Hardy basis are the strictly negative Fourier coefficients. -/
theorem negativeHardyBasis_repr (f : ↥hardySubmoduleᗮ) (n : ℕ) :
    negativeHardyBasis.repr f n =
      fourierCoeff (f : Lp ℂ 2 (AddCircle.haarAddCircle (T := 1))) (-(n : ℤ) - 1) := by
  rw [HilbertBasis.repr_apply_apply, ← hardySubmoduleᗮ.subtypeₗᵢ.inner_map_map]
  simp only [Submodule.coe_subtypeₗᵢ, Submodule.subtype_apply, coe_negativeHardyBasis,
    ← HilbertBasis.repr_apply_apply, fourierBasis_repr]

/-- The unitary flip from negative modes to Hardy space, sending `e₋ₙ₋₁` to `eₙ`. -/
def hardyFlip : ↥hardySubmoduleᗮ ≃ₗᵢ[ℂ] HardySpace :=
  negativeHardyBasis.repr.trans hardyBasis.repr.symm

/-- The flip preserves coordinates in the negative and nonnegative Hardy bases. -/
@[simp]
theorem hardyBasis_repr_hardyFlip (f : ↥hardySubmoduleᗮ) :
    hardyBasis.repr (hardyFlip f) = negativeHardyBasis.repr f := by
  simp [hardyFlip]

/-- The inverse flip preserves the same coordinates. -/
@[simp]
theorem negativeHardyBasis_repr_hardyFlip_symm (f : HardySpace) :
    negativeHardyBasis.repr (hardyFlip.symm f) = hardyBasis.repr f := by
  simp [hardyFlip]

/-- The flip sends the `n`th negative mode to the `n`th nonnegative mode. -/
@[simp]
theorem hardyFlip_negativeHardyBasis (n : ℕ) :
    hardyFlip (negativeHardyBasis n) = hardyBasis n := by
  apply hardyBasis.repr.injective
  simp [HilbertBasis.repr_self]

/-- The inverse flip sends the `n`th nonnegative mode to the `n`th negative mode. -/
@[simp]
theorem hardyFlip_symm_hardyBasis (n : ℕ) :
    hardyFlip.symm (hardyBasis n) = negativeHardyBasis n := by
  exact (hardyFlip.symm_apply_eq).mpr (hardyFlip_negativeHardyBasis n).symm

/-- The negative-mode matrix of the orthogonal-complement-valued Hankel operator. -/
theorem inner_negativeHardyBasis_hankel_hardyBasis
    (a : Lp ℂ ∞ (AddCircle.haarAddCircle (T := 1))) (i j : ℕ) :
    ⟪negativeHardyBasis i, hankel a (hardyBasis j)⟫_ℂ =
      fourierCoeff a (-(i : ℤ) - 1 - j) := by
  rw [hankel_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left, coe_negativeHardyBasis,
    Submodule.subtypeL_apply, coe_hardyBasis, Lp.multiplicationOperator_apply,
    ← HilbertBasis.repr_apply_apply, fourierBasis_repr, fourierCoeff_smul_fourierBasis]

/-- The classical Hankel symbol map. Its matrix in the Hardy basis is `â(i + j + 1)`;
the reflection distinguishes it from the negative-mode Hankel compression. -/
def classicalHankel : Lp ℂ ∞ (AddCircle.haarAddCircle (T := 1)) →L[ℂ]
    HardySpace →L[ℂ] HardySpace :=
  (ContinuousLinearMap.compL ℂ HardySpace ↥hardySubmoduleᗮ HardySpace
    hardyFlip.toLinearIsometry.toContinuousLinearMap) ∘L hankel ∘L
      (Lp.compMeasurePreservingₗᵢ ℂ (fun t ↦ -t)
        (Measure.measurePreserving_neg AddCircle.haarAddCircle)).toContinuousLinearMap

/-- Classical Hankel operators are flipped Hankel compressions of the reflected symbol. -/
theorem classicalHankel_apply (a : Lp ℂ ∞ (AddCircle.haarAddCircle (T := 1))) :
    classicalHankel a = hardyFlip.toLinearIsometry.toContinuousLinearMap ∘L
      hankel (Lp.compMeasurePreserving (fun t ↦ -t)
        (Measure.measurePreserving_neg AddCircle.haarAddCircle) a) :=
  (rfl)

/-- The classical Hankel operator is bounded by the essential supremum of its symbol. -/
theorem norm_classicalHankel_le (a : Lp ℂ ∞ (AddCircle.haarAddCircle (T := 1))) :
    ‖classicalHankel a‖ ≤ ‖a‖ := by
  have h := norm_hankel_le (Lp.compMeasurePreserving (fun t ↦ -t)
    (Measure.measurePreserving_neg AddCircle.haarAddCircle) a)
  rw [Lp.norm_compMeasurePreserving] at h
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro f
  rw [classicalHankel_apply, ContinuousLinearMap.comp_apply,
    LinearIsometry.coe_toContinuousLinearMap, LinearIsometryEquiv.coe_toLinearIsometry,
    hardyFlip.norm_map]
  exact ContinuousLinearMap.le_of_opNorm_le _ h f

/-- The classical Hankel matrix has constant anti-diagonals `â(i + j + 1)`. -/
theorem inner_hardyBasis_classicalHankel_hardyBasis
    (a : Lp ℂ ∞ (AddCircle.haarAddCircle (T := 1))) (i j : ℕ) :
    ⟪hardyBasis i, classicalHankel a (hardyBasis j)⟫_ℂ =
      fourierCoeff a ((i : ℤ) + j + 1) := by
  rw [classicalHankel_apply, ContinuousLinearMap.comp_apply,
    ← HilbertBasis.repr_apply_apply, LinearIsometry.coe_toContinuousLinearMap,
    LinearIsometryEquiv.coe_toLinearIsometry,
    hardyBasis_repr_hardyFlip, HilbertBasis.repr_apply_apply,
    inner_negativeHardyBasis_hankel_hardyBasis, Lp.fourierCoeff_compMeasurePreserving_neg]
  congr 1
  ring

/-- Taking the adjoint conjugates and reflects the classical Hankel symbol. -/
@[simp]
theorem adjoint_classicalHankel (a : Lp ℂ ∞ (AddCircle.haarAddCircle (T := 1))) :
    ContinuousLinearMap.adjoint (classicalHankel a) =
      classicalHankel (Lp.compMeasurePreserving (fun t ↦ -t)
        (Measure.measurePreserving_neg AddCircle.haarAddCircle) (star a)) := by
  apply hardyBasis.ext_inner_apply hardyBasis
  intro i j
  rw [ContinuousLinearMap.adjoint_inner_right, ← inner_conj_symm,
    inner_hardyBasis_classicalHankel_hardyBasis, inner_hardyBasis_classicalHankel_hardyBasis,
    Lp.fourierCoeff_compMeasurePreserving_neg, fourierCoeff_star, neg_neg]
  congr 2
  ring

/-- Flipping the negative-mode Hankel compression reflects the classical symbol. -/
theorem hardyFlip_comp_hankel (a : Lp ℂ ∞ (AddCircle.haarAddCircle (T := 1))) :
    hardyFlip.toLinearIsometry.toContinuousLinearMap ∘L hankel a =
      classicalHankel (Lp.compMeasurePreserving (fun t ↦ -t)
        (Measure.measurePreserving_neg AddCircle.haarAddCircle) a) := by
  have hneg : (fun t : UnitAddCircle ↦ -t) ∘ (fun t ↦ -t) = id := funext neg_neg
  rw [classicalHankel_apply, ← Lp.compMeasurePreserving_comp_apply]
  simp only [hneg, Lp.compMeasurePreserving_id_apply]

/-- The adjoint Hankel factor in a Toeplitz product becomes the classical Hankel matrix. -/
theorem adjoint_hankel_comp_hardyFlip_symm
    (a : Lp ℂ ∞ (AddCircle.haarAddCircle (T := 1))) :
    ContinuousLinearMap.adjoint (hankel (star a)) ∘L
      hardyFlip.symm.toLinearIsometry.toContinuousLinearMap =
      classicalHankel a := by
  apply hardyBasis.ext_inner_apply hardyBasis
  intro i j
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right,
    LinearIsometry.coe_toContinuousLinearMap, LinearIsometryEquiv.coe_toLinearIsometry,
    hardyFlip_symm_hardyBasis,
    ← inner_conj_symm, inner_negativeHardyBasis_hankel_hardyBasis, fourierCoeff_star,
    inner_hardyBasis_classicalHankel_hardyBasis]
  simp only [starRingEnd_apply, star_star]
  congr 1
  ring

/-- **Classical Toeplitz product identity.** The product defect is minus the product of
the classical Hankel operator of the left symbol and that of the reflected right symbol. -/
theorem toeplitz_comp_sub_toeplitz_eq_classicalHankel
    (a b : Lp ℂ ∞ (AddCircle.haarAddCircle (T := 1))) :
    toeplitz a ∘L toeplitz b - toeplitz (a * b) =
      -(classicalHankel a ∘L classicalHankel (Lp.compMeasurePreserving (fun t ↦ -t)
        (Measure.measurePreserving_neg AddCircle.haarAddCircle) b)) := by
  have h : ContinuousLinearMap.adjoint (hankel (star a)) ∘L hankel b =
      (ContinuousLinearMap.adjoint (hankel (star a)) ∘L
        hardyFlip.symm.toLinearIsometry.toContinuousLinearMap) ∘L
          (hardyFlip.toLinearIsometry.toContinuousLinearMap ∘L hankel b) := by
    ext f : 1
    simp
  rw [adjoint_hankel_comp_hardyFlip_symm a, hardyFlip_comp_hankel b] at h
  exact (toeplitz_comp_sub_toeplitz a b).trans (congrArg Neg.neg h)

end TauCeti
