/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.Sobolev
import TauCeti.Analysis.PDE.Schrodinger.Stationary
import TauCeti.Analysis.PDE.Vortex.ExteriorEstimate

/-!
# The Schrödinger equation with the potential of a plane vortex field

Let `x` be a field on the plane whose section `α` has unit modulus at infinity,
`4 (x₂² + x₃²) → 1`, and write `P = |α|² / 4 = x₂² + x₃²`. Then `P` is bounded, nonnegative and at
least `1 / 8` outside some ball (`TauCeti.Vortex.exists_memLp_top_sq_add_sq_and_le`), which are the
hypotheses of the stationary Schrödinger solve
(`TauCeti.exists_contDiff_re_im_mem_realSobolevFunctions_two_neg_laplacian_add_mul_eq`). This file
records the resulting solution of `Δh = P h - g` in `H²(ℂ; ℂ)`, which is the correction step shared
by the kernel constructions in `TauCeti.Analysis.PDE.Vortex.ZeroMode` and
`TauCeti.Analysis.PDE.Vortex.Kernel.Existence`.

## Main results

* `TauCeti.Vortex.exists_contDiff_laplacian_eq_mul_sub`: for a smooth field and a smooth
  `g ∈ L²(ℂ; ℂ)`, the smooth `H²(ℂ; ℂ)` solution of `Δh = P h - g`.

## References

* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III.
-/

public section

namespace TauCeti.Vortex

open MeasureTheory Filter Complex TemperedDistribution
open scoped Laplacian ContDiff Topology

variable {x : ℂ → EuclideanSpace ℝ (Fin 4)}

/-- For a smooth field whose section has unit modulus at infinity and a smooth `g ∈ L²(ℂ; ℂ)`,
the equation `Δh = P h - g`, `P = |α|² / 4`, has a smooth solution `h ∈ H²(ℂ; ℂ)`. -/
theorem exists_contDiff_laplacian_eq_mul_sub (hx : ContDiff ℝ ∞ x)
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1)) {g : ℂ → ℂ}
    (hgs : ContDiff ℝ ∞ g) (hg2 : MemLp g 2 volume) :
    ∃ h : ℂ → ℂ, ContDiff ℝ ∞ h ∧ (fun z ↦ (h z).re) ∈ realSobolevFunctions ℂ 2 2 ∧
      (fun z ↦ (h z).im) ∈ realSobolevFunctions ℂ 2 2 ∧
      ∀ z, Δ h z = ((x z 2 ^ 2 + x z 3 ^ 2 : ℝ) : ℂ) * h z - g z := by
  have hxi (i : Fin 4) : ContDiff ℝ ∞ (fun z ↦ x z i) := contDiff_euclidean.mp hx i
  obtain ⟨R, hP, hP₀, hPa⟩ := exists_memLp_top_sq_add_sq_and_le hx.continuous hlim
  obtain ⟨h, hhs, hh₁, hh₂, he⟩ :=
    exists_contDiff_re_im_mem_realSobolevFunctions_two_neg_laplacian_add_mul_eq
      (((hxi 2).pow 2).add ((hxi 3).pow 2)) hP hP₀ (by norm_num : (0 : ℝ) < 1 / 8) hPa hgs hg2
  exact ⟨h, hhs, hh₁, hh₂, fun z ↦ by linear_combination -he z⟩

end TauCeti.Vortex
