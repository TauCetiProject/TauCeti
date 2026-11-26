/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LFunctions.DedekindZeta.Completed
public import TauCeti.NumberTheory.LFunctions.Theta.Inversion

/-!
# The normalization of Hecke's functional equation for the Dedekind zeta function

The functional equation `Λ_K(1 - s) = Λ_K(s)` depends on several conventions at once: the additive
character `𝐞 x = exp (2πi x)` and the Fourier sign inside `mixedFourier`, the self-dual measure
`volume` for the Euclidean pairing `mixedInner` (a complex coordinate counted once), the covolume
of an ideal lattice, the discriminant power `|d_K| ^ (s / 2)`, and the archimedean factors
`Γ_ℝ(s) ^ r₁ Γ_ℂ(s) ^ r₂`, including the factor `2` inside Mathlib's
`Gammaℂ s = 2 (2π) ^ (-s) Γ(s)`. A factor-of-two or an inverse-discriminant error in any one of
them is invisible over `ℚ`.

`TauCeti.LFunctions.gaussianTheta_mellin_normalization` audits all of these in one statement:

* the one-parameter Gaussian is self-dual up to `t ^ (-[K : ℚ] / 2)`;
* the theta series of an ideal lattice transforms with that factor and the inverse covolume,
  against the Euclidean dual lattice (Neukirch VII (3.6) on the imaginary axis);
* for every unit fundamental domain `D`, each completed partial zeta function is the Mellin
  transform at `s / 2` of the named kernel `mellinKernel D σ(I)` minus its constant term
  `mellinConstant K` (Neukirch VII (5.5)), the kernel averaging the theta series over `D`, which
  is what cuts the sum over lattice points down to a sum over ideals in positive unit rank;
* the completed Dedekind zeta function carries exactly `|d_K| ^ (s / 2)`, `Γ_ℝ(s) ^ r₁` and
  `Γ_ℂ(s) ^ r₂` on `Re s > 1`.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII, §§3 and 5.
-/

public section

open Complex NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
  TauCeti.NumberField.mixedEmbedding
open scoped nonZeroDivisors

namespace TauCeti.LFunctions

variable (K : Type*) [Field K] [NumberField K]

open scoped Classical in
/-- **The normalization theorem for Hecke's method.** The self-duality of the one-parameter
Gaussian, the theta transformation of an ideal lattice, the Mellin representation of every
completed partial zeta function through the kernel `mellinKernel` and its constant term
`mellinConstant` for every unit fundamental domain, and the discriminant power and archimedean
factors of the completed Dedekind zeta function, stated together so that the four number-field
constants are visibly compatible with the Fourier conventions. -/
theorem gaussianTheta_mellin_normalization :
    (∀ t : ℝ, 0 < t → ∀ ξ : mixedSpace K,
        mixedFourier K (mixedGaussian K t) ξ =
          (t : ℂ) ^ (-(Module.finrank ℚ K : ℂ) / 2) * mixedGaussian K t⁻¹ ξ) ∧
      (∀ (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (t : ℝ), 0 < t →
        ∑' x : idealLattice K I, mixedGaussian K t x =
          (ZLattice.covolume (idealLattice K I) : ℂ)⁻¹ *
            (t : ℂ) ^ (-(Module.finrank ℚ K : ℂ) / 2) *
            ∑' y : mixedDual K (idealLattice K I), mixedGaussian K t⁻¹ y) ∧
      (∀ D : Set (realSpace K), IsUnitFundamentalDomain K D →
        ∀ (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (s : ℂ), 1 < s.re →
          completedPartialZeta I s =
            mellin (fun u ↦ mellinKernel D (idealLattice K I) u - mellinConstant K) (s / 2)) ∧
      (∀ s : ℂ, 1 < s.re →
        completedDedekindZeta K s =
          ((|discr K| : ℤ) : ℂ) ^ (s / 2) * Gammaℝ s ^ nrRealPlaces K *
            Gammaℂ s ^ nrComplexPlaces K * dedekindZeta K s) :=
  ⟨fun _ ht ↦ mixedFourier_mixedGaussian ht,
    fun I _ ht ↦ tsum_mixedGaussian_eq_tsum_mixedDual (idealLattice K I) ht,
    fun _ hD I _ hs ↦ completedPartialZeta_eq_mellin hD I hs,
    fun _ hs ↦ completedDedekindZeta_eq_mul_dedekindZeta K hs⟩

end TauCeti.LFunctions
