/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Schrodinger.Stationary
import TauCeti.Analysis.PDE.Vortex.ExteriorEstimate

/-!
# The Schrödinger equation with the potential of a plane vortex field

Let `x` be a field on the plane whose section `α` has unit modulus at infinity,
`4 (x₂² + x₃²) → 1`, and write `P = |α|² / 4 = x₂² + x₃²`. Then `P` is bounded, nonnegative and at
least `1 / 8` outside some ball, which are the hypotheses of the stationary Schrödinger solve
(`TauCeti.exists_contDiff_re_im_mem_realSobolevFunctions_two_neg_laplacian_add_mul_eq`). This file
records these bounds and the resulting solution of `Δh = P h - g` in `H²(ℂ; ℂ)`, which is the
correction step shared by the kernel constructions in `TauCeti.Analysis.PDE.Vortex.ZeroMode`,
`TauCeti.Analysis.PDE.Vortex.KernelExistence` and `TauCeti.Analysis.PDE.Vortex.TangentKernel`.

## Main results

* `TauCeti.Vortex.exists_memLp_top_potential_and_le`: `P` is bounded, nonnegative, and at least
  `1 / 8` outside some ball.
* `TauCeti.Vortex.memLp_top_apply`: the section coordinates `x₂` and `x₃` are bounded.
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

/-- The potential `P = |α|² / 4` of a continuous field whose section has unit modulus at infinity
is bounded above. -/
private theorem exists_forall_potential_le (hx : Continuous x)
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1)) :
    ∃ M, ∀ z, x z 2 ^ 2 + x z 3 ^ 2 ≤ M := by
  have hxi (i : Fin 4) : Continuous fun z ↦ x z i := by fun_prop
  have hPc : Continuous fun z ↦ x z 2 ^ 2 + x z 3 ^ 2 := by
    have := hxi 2; have := hxi 3; fun_prop
  obtain ⟨K, hK, hKc⟩ := mem_cocompact.1 (hlim.eventually (ge_mem_nhds (by norm_num : (1 : ℝ) < 2)))
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hPc.continuousOn
  refine ⟨max M 1, fun z ↦ ?_⟩
  by_cases hz : z ∈ K
  · exact (le_abs_self _).trans ((Real.norm_eq_abs _ ▸ hM z hz).trans (le_max_left _ _))
  · have h2 : 4 * (x z 2 ^ 2 + x z 3 ^ 2) ≤ 2 := hKc hz
    linarith [le_max_right M 1]

/-- The potential `P = |α|² / 4` of a field whose section has unit modulus at infinity is
bounded, nonnegative, and at least `1 / 8` outside some ball: the hypotheses of the Schrödinger
solve. -/
theorem exists_memLp_top_potential_and_le (hx : Continuous x)
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1)) :
    ∃ R : ℝ, MemLp (fun z ↦ x z 2 ^ 2 + x z 3 ^ 2) ⊤ volume ∧
      (∀ᵐ z ∂volume, 0 ≤ x z 2 ^ 2 + x z 3 ^ 2) ∧
      ∀ᵐ z ∂(volume : Measure ℂ), R < ‖z‖ → 1 / 8 ≤ x z 2 ^ 2 + x z 3 ^ 2 := by
  have hxi (i : Fin 4) : Continuous fun z ↦ x z i := by fun_prop
  have hPc : Continuous fun z ↦ x z 2 ^ 2 + x z 3 ^ 2 := by
    have := hxi 2; have := hxi 3; fun_prop
  obtain ⟨M, hM⟩ := exists_forall_potential_le hx hlim
  obtain ⟨R, -, hR⟩ := exists_exterior_lt_mass hlim (by norm_num : (1 : ℝ) / 8 < 1 / 4)
  refine ⟨R, memLp_top_of_bound hPc.aestronglyMeasurable M (ae_of_all _ fun z ↦ ?_),
    ae_of_all _ fun z ↦ by positivity, ae_of_all _ fun z hz ↦ (hR z hz).le⟩
  rw [Real.norm_of_nonneg (by positivity)]
  exact hM z

/-- The section coordinates of a continuous field whose section has unit modulus at infinity are
bounded. -/
theorem memLp_top_apply (hx : Continuous x)
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1)) {i : Fin 4}
    (hi : i = 2 ∨ i = 3) : MemLp (fun z ↦ x z i) ⊤ volume := by
  obtain ⟨M, hM⟩ := exists_forall_potential_le hx hlim
  have hxi : Continuous fun z ↦ x z i := by fun_prop
  refine memLp_top_of_bound hxi.aestronglyMeasurable (M + 1) (ae_of_all _ fun z ↦ ?_)
  rw [Real.norm_eq_abs]
  have hz := hM z
  rcases hi with rfl | rfl
  · nlinarith [sq_nonneg (|x z 2| - 1), sq_abs (x z 2), sq_nonneg (x z 3), abs_nonneg (x z 2)]
  · nlinarith [sq_nonneg (|x z 3| - 1), sq_abs (x z 3), sq_nonneg (x z 2), abs_nonneg (x z 3)]

/-- For a smooth field whose section has unit modulus at infinity and a smooth `g ∈ L²(ℂ; ℂ)`,
the equation `Δh = P h - g`, `P = |α|² / 4`, has a smooth solution `h ∈ H²(ℂ; ℂ)`. -/
theorem exists_contDiff_laplacian_eq_mul_sub (hx : ContDiff ℝ ∞ x)
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1)) {g : ℂ → ℂ}
    (hgs : ContDiff ℝ ∞ g) (hg2 : MemLp g 2 volume) :
    ∃ h : ℂ → ℂ, ContDiff ℝ ∞ h ∧ (fun z ↦ (h z).re) ∈ realSobolevFunctions ℂ 2 2 ∧
      (fun z ↦ (h z).im) ∈ realSobolevFunctions ℂ 2 2 ∧
      ∀ z, Δ h z = ((x z 2 ^ 2 + x z 3 ^ 2 : ℝ) : ℂ) * h z - g z := by
  have hxi (i : Fin 4) : ContDiff ℝ ∞ (fun z ↦ x z i) := contDiff_euclidean.mp hx i
  obtain ⟨R, hP, hP₀, hPa⟩ := exists_memLp_top_potential_and_le hx.continuous hlim
  obtain ⟨h, hhs, hh₁, hh₂, he⟩ :=
    exists_contDiff_re_im_mem_realSobolevFunctions_two_neg_laplacian_add_mul_eq
      (((hxi 2).pow 2).add ((hxi 3).pow 2)) hP hP₀ (by norm_num : (0 : ℝ) < 1 / 8) hPa hgs hg2
  exact ⟨h, hhs, hh₁, hh₂, fun z ↦ by linear_combination -he z⟩

end TauCeti.Vortex
