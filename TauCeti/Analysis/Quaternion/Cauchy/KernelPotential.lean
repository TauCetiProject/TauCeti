/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.ContDiff.KernelIntegral
public import TauCeti.Analysis.Quaternion.Kernel

/-!
# Separated Cauchy–Fueter kernel potentials and decay bounds

This file specializes the separated translation-kernel differentiation results of
`TauCeti.Analysis.Calculus.ContDiff.KernelIntegral` to `TauCeti.cauchyFueterKernel` on an
arbitrary measure space `(α, μ)` and into any real normed space `E`, without any regularity or
representation hypothesis on the density.

## Main declarations

* `ContinuousLinearMap.iteratedFDeriv_bilin_cauchyFueterKernel`: away from the pole `w`, the
  `m`-th derivative of `p ↦ B (cauchyFueterKernel w p) c` is the `m`-th pole derivative of
  `cauchyFueterKernel w` postcomposed with `B.flip c`.
* `ContinuousLinearMap.hasFTaylorSeriesUpToOn_integral_bilin_cauchyFueterKernel`,
  `ContinuousLinearMap.contDiffOn_integral_bilin_cauchyFueterKernel`,
  `ContinuousLinearMap.contDiffAt_integral_bilin_cauchyFueterKernel`,
  `ContinuousLinearMap.iteratedFDeriv_integral_bilin_cauchyFueterKernel`: `C^∞` Taylor series,
  smoothness, and differentiation under separated bilinear Cauchy–Fueter integrals on arbitrary
  measure spaces.
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

section BilinearKernelPotentials

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}
  {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem cauchyFueterKernel_sub_zero (w y : ℍ) :
    cauchyFueterKernel (w - y) 0 = cauchyFueterKernel w y := by
  simp [cauchyFueterKernel_eq]

private theorem contDiffAt_cauchyFueterKernel_zero :
    ∀ x ≠ (0 : ℍ), ContDiffAt ℝ ∞ (fun w ↦ cauchyFueterKernel w 0) x :=
  fun _ hx ↦ contDiffAt_cauchyFueterKernel hx

private theorem exists_norm_iteratedFDeriv_cauchyFueterKernel_zero_le (k : ℕ) {ρ : ℝ}
    (hρ : 0 < ρ) :
    ∃ C : ℝ, ∀ x : ℍ, ρ ≤ ‖x‖ →
      ‖iteratedFDeriv ℝ k (fun w ↦ cauchyFueterKernel w 0) x‖ ≤ C := by
  obtain ⟨C, hC, h⟩ := exists_norm_iteratedFDeriv_cauchyFueterKernel_le k
  refine ⟨C / ρ ^ (3 + k), fun x hx ↦ ?_⟩
  have hne : x ≠ 0 := norm_pos_iff.1 (hρ.trans_le hx)
  refine (h k le_rfl x 0 hne).trans ?_
  rw [sub_zero]
  exact div_le_div_of_nonneg_left hC.le (by positivity) (pow_le_pow_left₀ hρ.le hx _)

/-- Away from the pole `w`, the `m`-th iterated Fréchet derivative of
`p ↦ B (cauchyFueterKernel w p) c` is the `m`-th pole derivative of `cauchyFueterKernel w`
postcomposed with `B.flip c`. -/
theorem _root_.ContinuousLinearMap.iteratedFDeriv_bilin_cauchyFueterKernel
    (B : ℍ →L[ℝ] G →L[ℝ] E) {w q : ℍ} (hne : w ≠ q) (c : G) (m : ℕ) :
    iteratedFDeriv ℝ m (fun p ↦ B (cauchyFueterKernel w p) c) q =
      (B.flip c).compContinuousMultilinearMap (iteratedFDeriv ℝ m (cauchyFueterKernel w) q) := by
  simpa only [cauchyFueterKernel_sub_zero, ← iteratedFDeriv_cauchyFueterKernel_right] using
    iteratedFDeriv_bilin_kernel_sub B contDiffAt_cauchyFueterKernel_zero hne c m

/-- On `Metric.ball q₀ δ`, the integrated spatial jets form a `C^∞` Taylor series for a separated
bilinear Cauchy–Fueter integral `y ↦ ∫ z, B (cauchyFueterKernel (φ z) y) (w z) ∂μ`. -/
theorem _root_.ContinuousLinearMap.hasFTaylorSeriesUpToOn_integral_bilin_cauchyFueterKernel
    (B : ℍ →L[ℝ] G →L[ℝ] E) {φ : α → ℍ} (hφ : AEStronglyMeasurable φ μ)
    {w : α → G} (hw : Integrable w μ)
    {q₀ : ℍ} {δ : ℝ} (hδ : ∀ᵐ z ∂μ, δ ≤ ‖φ z - q₀‖) :
    HasFTaylorSeriesUpToOn ∞
      (fun y ↦ ∫ z, B (cauchyFueterKernel (φ z) y) (w z) ∂μ)
      (fun y m ↦ ∫ z, iteratedFDeriv ℝ m (fun p ↦ B (cauchyFueterKernel (φ z) p) (w z)) y ∂μ)
      (ball q₀ δ) := by
  simpa only [cauchyFueterKernel_sub_zero] using
    hasFTaylorSeriesUpToOn_integral_bilin_kernel_sub B contDiffAt_cauchyFueterKernel_zero
      (fun k {_} hρ ↦ exists_norm_iteratedFDeriv_cauchyFueterKernel_zero_le k hρ) hφ hw hδ

/-- Smoothness on `Metric.ball q₀ δ` of `y ↦ ∫ z, B (cauchyFueterKernel (φ z) y) (w z) ∂μ`. -/
theorem _root_.ContinuousLinearMap.contDiffOn_integral_bilin_cauchyFueterKernel
    (B : ℍ →L[ℝ] G →L[ℝ] E) {φ : α → ℍ} (hφ : AEStronglyMeasurable φ μ)
    {w : α → G} (hw : Integrable w μ)
    {q₀ : ℍ} {δ : ℝ} (hδ : ∀ᵐ z ∂μ, δ ≤ ‖φ z - q₀‖) {n : ℕ∞} :
    ContDiffOn ℝ n (fun y ↦ ∫ z, B (cauchyFueterKernel (φ z) y) (w z) ∂μ) (ball q₀ δ) :=
  (B.hasFTaylorSeriesUpToOn_integral_bilin_cauchyFueterKernel hφ hw hδ).contDiffOn.of_le
    (WithTop.coe_le_coe.2 le_top)

/-- Pointwise smoothness at `q ∈ Metric.ball q₀ δ` of
`y ↦ ∫ z, B (cauchyFueterKernel (φ z) y) (w z) ∂μ`. -/
theorem _root_.ContinuousLinearMap.contDiffAt_integral_bilin_cauchyFueterKernel
    (B : ℍ →L[ℝ] G →L[ℝ] E) {φ : α → ℍ} (hφ : AEStronglyMeasurable φ μ)
    {w : α → G} (hw : Integrable w μ)
    {q₀ : ℍ} {δ : ℝ} (hδ : ∀ᵐ z ∂μ, δ ≤ ‖φ z - q₀‖)
    {q : ℍ} (hq : q ∈ ball q₀ δ) {n : ℕ∞} :
    ContDiffAt ℝ n (fun y ↦ ∫ z, B (cauchyFueterKernel (φ z) y) (w z) ∂μ) q :=
  (B.contDiffOn_integral_bilin_cauchyFueterKernel hφ hw hδ q hq).contDiffAt
    (isOpen_ball.mem_nhds hq)

/-- Every iterated real derivative on `Metric.ball q₀ δ` of
`y ↦ ∫ z, B (cauchyFueterKernel (φ z) y) (w z) ∂μ` commutes with the Bochner integral. -/
theorem _root_.ContinuousLinearMap.iteratedFDeriv_integral_bilin_cauchyFueterKernel
    (B : ℍ →L[ℝ] G →L[ℝ] E) {φ : α → ℍ} (hφ : AEStronglyMeasurable φ μ)
    {w : α → G} (hw : Integrable w μ)
    {q₀ : ℍ} {δ : ℝ} (hδ : ∀ᵐ z ∂μ, δ ≤ ‖φ z - q₀‖)
    (m : ℕ) {q : ℍ} (hq : q ∈ ball q₀ δ) :
    iteratedFDeriv ℝ m (fun y ↦ ∫ z, B (cauchyFueterKernel (φ z) y) (w z) ∂μ) q =
      ∫ z, iteratedFDeriv ℝ m (fun y ↦ B (cauchyFueterKernel (φ z) y) (w z)) q ∂μ := by
  simpa only [cauchyFueterKernel_sub_zero] using
    iteratedFDeriv_integral_bilin_kernel_sub B contDiffAt_cauchyFueterKernel_zero
      (fun k {_} hρ ↦ exists_norm_iteratedFDeriv_cauchyFueterKernel_zero_le k hρ) hφ hw hδ m hq

end BilinearKernelPotentials

section FiniteSum

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
  have hcd₁ (i : ι) :=
    B.contDiffAt_integral_bilin_cauchyFueterKernel (hφ₁ i) (hw₁ i) (hδ₁ i) (hq₁ i) (n := m)
  have hcd₀ (i : ι) :=
    B.contDiffAt_integral_bilin_cauchyFueterKernel (hφ₀ i) (hw₀ i) (hδ₀ i) (hq₀ i) (n := m)
  rw [iteratedFDeriv_const_smul_apply' (ContDiffAt.sum fun i _ ↦ (hcd₁ i).sub (hcd₀ i)),
    iteratedFDeriv_fun_sum_apply fun i _ ↦ (hcd₁ i).sub (hcd₀ i)]
  congr 1
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [fun_iteratedFDeriv_sub_apply (hcd₁ i) (hcd₀ i),
    B.iteratedFDeriv_integral_bilin_cauchyFueterKernel (hφ₁ i) (hw₁ i) (hδ₁ i) m (hq₁ i),
    B.iteratedFDeriv_integral_bilin_cauchyFueterKernel (hφ₀ i) (hw₀ i) (hδ₀ i) m (hq₀ i)]

end FiniteSum

end TauCeti
