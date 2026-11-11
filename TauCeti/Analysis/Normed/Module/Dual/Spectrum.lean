/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Module.Dual.Adjoint

/-!
# Spectrum of the Banach transpose

The Banach transpose of a bounded operator is precomposition on the continuous dual.
On a Banach space over `ℝ` or `ℂ`, an operator and its transpose are invertible
simultaneously and have the same spectrum. In particular, there is no complex
conjugation in this comparison: the Banach transpose is not the Hilbert adjoint.

The invertibility comparison uses `ContinuousLinearMap.bijective_precomp_iff`,
which combines the open mapping theorem with Hahn–Banach.

## References

* W. Rudin, *Functional Analysis*, 2nd ed., Chapter 4.
-/

public section

namespace ContinuousLinearMap

variable {𝕜 E : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]

/-- A bounded endomorphism of a Banach space is invertible exactly when its Banach
transpose is invertible. -/
@[simp]
theorem isUnit_precomp_iff (T : E →L[𝕜] E) :
    IsUnit (precomp 𝕜 T : StrongDual 𝕜 E →L[𝕜] StrongDual 𝕜 E) ↔ IsUnit T := by
  simp only [isUnit_iff_bijective, bijective_precomp_iff]

/-- The spectrum of the Banach transpose equals that of the original operator.
This is valid over both real and complex scalars, without conjugating the spectrum. -/
@[simp]
theorem spectrum_precomp (T : E →L[𝕜] E) :
    spectrum 𝕜 (precomp 𝕜 T : StrongDual 𝕜 E →L[𝕜] StrongDual 𝕜 E) =
      spectrum 𝕜 T := by
  ext z
  rw [spectrum.mem_iff, spectrum.mem_iff]
  have hshift :
      (precomp 𝕜 (z • (1 : E →L[𝕜] E) - T) :
        StrongDual 𝕜 E →L[𝕜] StrongDual 𝕜 E) =
        z • 1 - (precomp 𝕜 T : StrongDual 𝕜 E →L[𝕜] StrongDual 𝕜 E) := by
    ext f x
    simp
  rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, ← hshift]
  exact not_congr (isUnit_precomp_iff (z • 1 - T))

end ContinuousLinearMap
