/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.ContDiff.KernelIntegral
public import TauCeti.Analysis.Quaternion.Kernel

/-!
# Separated Cauchy–Fueter kernel potentials

This file specializes the separated translation-kernel differentiation results of
`TauCeti.Analysis.Calculus.ContDiff.KernelIntegral` to `TauCeti.cauchyFueterKernel` on an
arbitrary measure space `(α, μ)` and into any real normed space `E`, without any regularity or
representation hypothesis on the density.

## Main declarations

* `ContinuousLinearMap.iteratedFDeriv_smul_sum_sub_integral_bilin_cauchyFueterKernel`:
  differentiation under a scalar-rescaled finite sum of upper-minus-lower separated bilinear
  Cauchy–Fueter integrals.

## References

* I. Frenkel and M. Libine, *Quaternionic analysis, representation theory and physics*,
  Adv. Math. 218 (2008), arXiv:0711.2699v5, §2.2, Proposition 2 and Theorem 9.
* A. Sudbery, *Quaternionic analysis*, Math. Proc. Cambridge Philos. Soc. 85 (1979), 199–225.
-/

public section

open Filter MeasureTheory Metric Quaternion Set Topology
open scoped ContDiff

namespace TauCeti

private theorem cauchyFueterKernel_sub_zero (w y : ℍ) :
    cauchyFueterKernel (w - y) 0 = cauchyFueterKernel w y := by
  simp [cauchyFueterKernel_eq]

/-- Differentiating a scalar-rescaled finite sum of upper-minus-lower separated bilinear
Cauchy–Fueter integrals commutes with the sum and with every face integral, allowing
face-specific separation radii `δ₁ i` and `δ₀ i`. -/
theorem _root_.ContinuousLinearMap.iteratedFDeriv_smul_sum_sub_integral_bilin_cauchyFueterKernel
    {ι : Type*} [Fintype ι] {α : ι → Type*} [∀ i, MeasurableSpace (α i)]
    {μ : ∀ i, Measure (α i)} {G E : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedAddCommGroup E] [NormedSpace ℝ E]
    (B : ℍ →L[ℝ] G →L[ℝ] E) (c : ℝ)
    {φ₁ φ₀ : ∀ i, α i → ℍ}
    (hφ₁ : ∀ i, AEStronglyMeasurable (φ₁ i) (μ i))
    (hφ₀ : ∀ i, AEStronglyMeasurable (φ₀ i) (μ i))
    {w₁ w₀ : ∀ i, α i → G}
    (hw₁ : ∀ i, Integrable (w₁ i) (μ i))
    (hw₀ : ∀ i, Integrable (w₀ i) (μ i))
    {q₀ : ℍ} {δ₁ δ₀ : ι → ℝ}
    (hδ₁ : ∀ i, ∀ᵐ z ∂μ i, δ₁ i ≤ ‖φ₁ i z - q₀‖)
    (hδ₀ : ∀ i, ∀ᵐ z ∂μ i, δ₀ i ≤ ‖φ₀ i z - q₀‖)
    (m : ℕ) {q : ℍ} (hq₁ : ∀ i, q ∈ ball q₀ (δ₁ i)) (hq₀ : ∀ i, q ∈ ball q₀ (δ₀ i)) :
    iteratedFDeriv ℝ m
      (fun y ↦ c • ∑ i : ι,
        ((∫ z, B (cauchyFueterKernel (φ₁ i z) y) (w₁ i z) ∂μ i) -
          ∫ z, B (cauchyFueterKernel (φ₀ i z) y) (w₀ i z) ∂μ i)) q =
    c • ∑ i : ι,
      ((∫ z, iteratedFDeriv ℝ m (fun y ↦ B (cauchyFueterKernel (φ₁ i z) y) (w₁ i z)) q ∂μ i) -
        ∫ z, iteratedFDeriv ℝ m (fun y ↦ B (cauchyFueterKernel (φ₀ i z) y) (w₀ i z)) q ∂μ i) := by
  have hK : ∀ x ≠ (0 : ℍ), ContDiffAt ℝ ∞ (fun w ↦ cauchyFueterKernel w 0) x :=
    fun _ hx ↦ contDiffAt_cauchyFueterKernel hx
  have hK_bd (k : ℕ) {ρ : ℝ} (hρ : 0 < ρ) :
      ∃ C : ℝ, ∀ x : ℍ, ρ ≤ ‖x‖ →
        ‖iteratedFDeriv ℝ k (fun w ↦ cauchyFueterKernel w 0) x‖ ≤ C := by
    obtain ⟨C, _, h⟩ := exists_norm_iteratedFDeriv_cauchyFueterKernel_right_le_of_le_norm_sub k
    exact ⟨C / ρ ^ (3 + k), fun x hx ↦ by
      simpa [iteratedFDeriv_cauchyFueterKernel_right, norm_smul] using
        h k le_rfl (q := x) (q₀ := 0) hρ (by simpa using hx)⟩
  have hcd₁ (i : ι) : ContDiffAt ℝ (m : ℕ∞)
      (fun y ↦ ∫ z, B (cauchyFueterKernel (φ₁ i z) y) (w₁ i z) ∂μ i) q := by
    simpa only [cauchyFueterKernel_sub_zero] using
      contDiffAt_integral_bilin_kernel_sub B hK hK_bd (hφ₁ i) (hw₁ i) (hδ₁ i) (hq₁ i) (n := m)
  have hcd₀ (i : ι) : ContDiffAt ℝ (m : ℕ∞)
      (fun y ↦ ∫ z, B (cauchyFueterKernel (φ₀ i z) y) (w₀ i z) ∂μ i) q := by
    simpa only [cauchyFueterKernel_sub_zero] using
      contDiffAt_integral_bilin_kernel_sub B hK hK_bd (hφ₀ i) (hw₀ i) (hδ₀ i) (hq₀ i) (n := m)
  have hint₁ (i : ι) :
      iteratedFDeriv ℝ m (fun y ↦ ∫ z, B (cauchyFueterKernel (φ₁ i z) y) (w₁ i z) ∂μ i) q =
        ∫ z, iteratedFDeriv ℝ m (fun y ↦ B (cauchyFueterKernel (φ₁ i z) y) (w₁ i z)) q ∂μ i := by
    simpa only [cauchyFueterKernel_sub_zero] using
      iteratedFDeriv_integral_bilin_kernel_sub B hK hK_bd (hφ₁ i) (hw₁ i) (hδ₁ i) m (hq₁ i)
  have hint₀ (i : ι) :
      iteratedFDeriv ℝ m (fun y ↦ ∫ z, B (cauchyFueterKernel (φ₀ i z) y) (w₀ i z) ∂μ i) q =
        ∫ z, iteratedFDeriv ℝ m (fun y ↦ B (cauchyFueterKernel (φ₀ i z) y) (w₀ i z)) q ∂μ i := by
    simpa only [cauchyFueterKernel_sub_zero] using
      iteratedFDeriv_integral_bilin_kernel_sub B hK hK_bd (hφ₀ i) (hw₀ i) (hδ₀ i) m (hq₀ i)
  rw [iteratedFDeriv_const_smul_apply' (ContDiffAt.sum fun i _ ↦ (hcd₁ i).sub (hcd₀ i)),
    iteratedFDeriv_fun_sum_apply fun i _ ↦ (hcd₁ i).sub (hcd₀ i)]
  congr 1
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [fun_iteratedFDeriv_sub_apply (hcd₁ i) (hcd₀ i), hint₁ i, hint₀ i]

end TauCeti
