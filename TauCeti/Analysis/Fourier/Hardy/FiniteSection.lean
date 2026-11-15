/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fourier.Hardy.Toeplitz
public import TauCeti.Analysis.InnerProductSpace.HilbertBasis.FiniteSection.Reflection

/-!
# Reflection of finite Toeplitz sections

Reversing both row and column order in a finite Toeplitz matrix replaces its symbol
`a(t)` by `a(-t)`. Here the finite matrices are zero-extended to boundary Hardy space,
and reversal is the finite reflection in the Hardy basis. Consequently, the reflected
finite sections converge strongly to the Toeplitz operator with reflected symbol.
This identifies the second boundary operator in the finite-section method.

Reflection of symbols uses the native `Lp.compMeasurePreserving` pullback, rather than
choosing pointwise representatives of essentially bounded functions.

## References

* A. Böttcher and B. Silbermann, *Introduction to Large Truncated Toeplitz Matrices*,
  for reflection and the two boundary operators of finite Toeplitz sections.
-/

public section

open MeasureTheory
open scoped ENNReal InnerProductSpace Topology

namespace TauCeti

/-- Reversing a finite Toeplitz section on both sides reflects its symbol. The equality
is between operators on the full Hardy space, with finite sections extended by zero. -/
theorem finiteReflection_comp_toeplitz_comp_finiteReflection
    (a : Lp ℂ ∞ (AddCircle.haarAddCircle (T := 1))) (n : ℕ) :
    hardyBasis.finiteReflection n ∘L toeplitz a ∘L hardyBasis.finiteReflection n =
      (toeplitz (Lp.compMeasurePreserving (fun t ↦ -t)
        (Measure.measurePreserving_neg AddCircle.haarAddCircle) a)).zeroExtendedFiniteSection
          hardyBasis n := by
  rw [ContinuousLinearMap.zeroExtendedFiniteSection_eq]
  apply hardyBasis.ext_inner_apply hardyBasis
  intro i j
  simp only [ContinuousLinearMap.comp_apply]
  rw [← ContinuousLinearMap.adjoint_inner_left (hardyBasis.finiteReflection n),
    HilbertBasis.adjoint_finiteReflection,
    ← ContinuousLinearMap.adjoint_inner_left (hardyBasis.finiteProjection n),
    HilbertBasis.adjoint_finiteProjection]
  by_cases hi : i < n + 1
  · by_cases hj : j < n + 1
    · have hWi := hardyBasis.finiteReflection_basis n (⟨i, hi⟩ : Fin (n + 1))
      have hWj := hardyBasis.finiteReflection_basis n (⟨j, hj⟩ : Fin (n + 1))
      rw [hWi, hWj]
      simp only [HilbertBasis.finiteProjection_basis, hi, hj, ite_true]
      rw [inner_hardyBasis_toeplitz_hardyBasis, inner_hardyBasis_toeplitz_hardyBasis,
        Lp.fourierCoeff_compMeasurePreserving_neg]
      congr 1
      simp only [Fin.val_rev]
      omega
    · simp [HilbertBasis.finiteReflection_basis_eq_zero _ n (by omega : n < j), hj]
  · simp [HilbertBasis.finiteReflection_basis_eq_zero _ n (by omega : n < i), hi]

/-- The reflected zero-extended finite Toeplitz sections converge strongly to the
Toeplitz operator of the reflected symbol. -/
theorem tendsto_finiteReflection_zeroExtendedFiniteSection_toeplitz
    (a : Lp ℂ ∞ (AddCircle.haarAddCircle (T := 1))) (x : HardySpace) :
    Filter.Tendsto (fun n ↦ hardyBasis.finiteReflection n
      ((toeplitz a).zeroExtendedFiniteSection hardyBasis n
        (hardyBasis.finiteReflection n x))) Filter.atTop
      (𝓝 (toeplitz (Lp.compMeasurePreserving (fun t ↦ -t)
        (Measure.measurePreserving_neg AddCircle.haarAddCircle) a) x)) := by
  have h (n : ℕ) :
      hardyBasis.finiteReflection n ∘L
        (toeplitz a).zeroExtendedFiniteSection hardyBasis n ∘L hardyBasis.finiteReflection n =
      hardyBasis.finiteReflection n ∘L toeplitz a ∘L hardyBasis.finiteReflection n := by
    rw [ContinuousLinearMap.zeroExtendedFiniteSection_eq]
    simp [ContinuousLinearMap.comp_assoc, ← ContinuousLinearMap.comp_assoc
      (hardyBasis.finiteReflection n) (hardyBasis.finiteProjection n)]
  simpa only [← ContinuousLinearMap.comp_apply, h,
    finiteReflection_comp_toeplitz_comp_finiteReflection] using
    (toeplitz (Lp.compMeasurePreserving (fun t ↦ -t)
      (Measure.measurePreserving_neg AddCircle.haarAddCircle) a)).tendsto_zeroExtendedFiniteSection
        hardyBasis x

end TauCeti
