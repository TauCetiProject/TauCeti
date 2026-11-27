/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Spectrum.Quasispectrum

/-!
# Invertibility of positive shifts in the unitization

If the quasispectrum of `a` in a nonunital algebra `A` is nonnegative, as for a positive element
of a C⋆-algebra (`NonnegSpectrumClass`), then `-r` lies outside the spectrum of `a` in the
unitization for every `r > 0`. Hence `r + a` is invertible in `Unitization S A`,
`Unitization.isUnit_algebraMap_add_of_nonneg`, which is what lets expressions such as
`a (r + a)⁻¹` be formed there.
-/

public section

namespace Unitization

/-- If `a ≥ 0` in an algebra with nonnegative quasispectra, then `r + a` is invertible in the
unitization `Unitization S A` for every `r > 0`. -/
theorem isUnit_algebraMap_add_of_nonneg {R S A : Type*} [Field R] [PartialOrder R]
    [IsOrderedRing R] [Field S] [NonUnitalRing A] [PartialOrder A] [Algebra R S] [Module S A]
    [IsScalarTower S A A] [SMulCommClass S A A] [Module R A] [IsScalarTower R S A]
    [NonnegSpectrumClass R A] {r : R} (hr : 0 < r) {a : A} (ha : 0 ≤ a) :
    IsUnit (algebraMap R (Unitization S A) r + a) := by
  have hσ : -r ∉ spectrum R (a : Unitization S A) := by
    rw [← quasispectrum_eq_spectrum_inr' R S]
    exact fun h ↦ (neg_neg_of_pos hr).not_ge (quasispectrum_nonneg_of_nonneg a ha _ h)
  simpa [sub_eq_add_neg, add_comm] using (spectrum.notMem_iff.mp hσ).neg

end Unitization
