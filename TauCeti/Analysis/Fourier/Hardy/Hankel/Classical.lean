/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fourier.Hardy.Hankel.Basic

/-!
# The classical Hankel matrix and the negative-mode flip

The unitary `hardyFlip` from `Hardy.Basic` sends the negative Fourier mode `e₋ₙ₋₁`
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
  simpa [classicalHankel_apply] using ContinuousLinearMap.le_of_opNorm_le _ h f

/-- The classical Hankel matrix has constant anti-diagonals `â(i + j + 1)`. -/
theorem inner_hardyBasis_classicalHankel_hardyBasis
    (a : Lp ℂ ∞ (AddCircle.haarAddCircle (T := 1))) (i j : ℕ) :
    ⟪hardyBasis i, classicalHankel a (hardyBasis j)⟫_ℂ =
      fourierCoeff a ((i : ℤ) + j + 1) := by
  calc
    _ = ⟪negativeHardyBasis i, hankel (Lp.compMeasurePreserving (fun t ↦ -t)
        (Measure.measurePreserving_neg AddCircle.haarAddCircle) a) (hardyBasis j)⟫_ℂ := by
      simp [classicalHankel_apply, ← HilbertBasis.repr_apply_apply]
    _ = _ := by
      rw [inner_negativeHardyBasis_hankel_hardyBasis, Lp.fourierCoeff_compMeasurePreserving_neg]
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
  rw [inner_hardyBasis_classicalHankel_hardyBasis]
  calc
    _ = ⟪hankel (star a) (hardyBasis i), negativeHardyBasis j⟫_ℂ := by
      simp [ContinuousLinearMap.adjoint_inner_right]
    _ = starRingEnd ℂ (fourierCoeff
        (star a : Lp ℂ ∞ (AddCircle.haarAddCircle (T := 1))) (-(j : ℤ) - 1 - i)) := by
      rw [← inner_conj_symm, inner_negativeHardyBasis_hankel_hardyBasis]
    _ = _ := by
      rw [fourierCoeff_star]
      simp only [starRingEnd_apply, star_star]
      congr 1
      ring

/-- **Classical Toeplitz product identity.** The product defect is minus the product of
the classical Hankel operator of the left symbol and that of the reflected right symbol. -/
theorem toeplitz_comp_sub_toeplitz_eq_neg_classicalHankel_comp_classicalHankel
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
