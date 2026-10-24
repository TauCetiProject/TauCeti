/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Algebra.Spectrum

/-!
# Elements of spectral radius zero

The spectral radius of an element vanishes exactly when its quasispectrum, or in a unital
algebra its spectrum, is contained in `{0}`. In a complex Banach algebra these are the
quasinilpotent elements, by Gelfand's formula. Both statements are algebraic: they need a
norm only on the scalars, and no completeness.
-/

public section

namespace TauCeti

variable {𝕜 A : Type*} [NormedField 𝕜]

/-- The spectral radius of an element vanishes exactly when its quasispectrum is contained
in `{0}`. -/
theorem spectralRadius_eq_zero_iff [NonUnitalRing A] [Module 𝕜 A] {a : A} :
    spectralRadius 𝕜 a = 0 ↔ quasispectrum 𝕜 a ⊆ {0} := by
  simp [spectralRadius, Set.subset_def]

/-- In a unital algebra, the spectral radius of an element vanishes exactly when its spectrum
is contained in `{0}`. -/
theorem spectralRadius_eq_zero_iff_spectrum_subset_singleton_zero [Ring A] [Algebra 𝕜 A]
    {a : A} :
    spectralRadius 𝕜 a = 0 ↔ spectrum 𝕜 a ⊆ {0} := by
  rw [spectralRadius_eq_zero_iff, quasispectrum_eq_spectrum_union_zero, Set.union_subset_iff,
    and_iff_left subset_rfl]

end TauCeti
