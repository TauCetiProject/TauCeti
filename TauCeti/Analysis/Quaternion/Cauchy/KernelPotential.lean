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
* `ContinuousLinearMap.exists_norm_iteratedFDeriv_integral_bilinear_cauchyFueterKernel_le`: uniform
  `C / δ ^ (3 + m) * ∫ z, ‖g z‖ ∂μ` decay bound on the `m`-th derivative of a bilinearly weighted
  Cauchy–Fueter kernel potential.
* `TauCeti.iteratedFDeriv_integral_cauchyFueterKernel_mul_of_mem_ball`,
  `TauCeti.iteratedFDeriv_integral_mul_cauchyFueterKernel_of_mem_ball`: iterated derivative
  formulas for left and right Cauchy–Fueter potentials expressed via quaternion-module actions.
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

universe u

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

/-- Uniform decay bound on the `m`-th derivative of a bilinearly weighted Cauchy–Fueter kernel
potential in terms of the separation scale `δ` and the `L¹` norm of `g`. The constant depends only
on the bilinear pairing `B` and the maximum order `N`, uniformly across all measurable spaces
`X : Type u` and measures `μ` on `X`. -/
theorem
    _root_.ContinuousLinearMap.exists_norm_iteratedFDeriv_integral_bilinear_cauchyFueterKernel_le
    (B : G →L[ℝ] ℍ →L[ℝ] E) (N : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ m ≤ N, ∀ {X : Type u} [MeasurableSpace X] {μ : Measure X}
      {φ : X → ℍ} {g : X → G} {q₀ : ℍ} {δ : ℝ},
        AEStronglyMeasurable φ μ → Integrable g μ → 0 < δ → (∀ᵐ z ∂μ, δ ≤ ‖φ z - q₀‖) →
        ‖iteratedFDeriv ℝ m (fun q ↦ ∫ z, B (g z) (cauchyFueterKernel (φ z) q) ∂μ) q₀‖ ≤
          C / δ ^ (3 + m) * ∫ z, ‖g z‖ ∂μ := by
  let : NormedSpace ℝ ℍ := inferInstance
  obtain ⟨C, hC, hbound⟩ :=
    exists_norm_iteratedFDeriv_cauchyFueterKernel_right_le_of_le_norm_sub N
  refine ⟨(‖B‖ + 1) * C, mul_pos (by positivity) hC, fun m hm {X _ μ φ g q₀ δ} hφ hg hδ₀ hδ ↦ ?_⟩
  have hcomm := B.flip.iteratedFDeriv_integral_bilin_cauchyFueterKernel hφ hg hδ m
    (mem_ball_self hδ₀)
  simp only [ContinuousLinearMap.flip_apply] at hcomm
  rw [hcomm]
  refine (norm_integral_le_of_norm_le
    (hg.norm.const_mul ((‖B‖ + 1) * C / δ ^ (3 + m))) ?_).trans_eq (integral_const_mul _ _)
  filter_upwards [hδ] with z hz
  have hne : φ z ≠ q₀ := sub_ne_zero.mp (norm_pos_iff.mp (hδ₀.trans_le hz))
  have hk : ‖iteratedFDeriv ℝ m (fun p ↦ B (g z) (cauchyFueterKernel (φ z) p)) q₀‖ ≤
      ‖B‖ * ‖iteratedFDeriv ℝ m (fun w ↦ cauchyFueterKernel w 0) (φ z - q₀)‖ * ‖g z‖ := by
    simpa only [ContinuousLinearMap.flip_apply, ContinuousLinearMap.opNorm_flip,
      cauchyFueterKernel_sub_zero] using
      norm_iteratedFDeriv_bilin_kernel_sub_le B.flip contDiffAt_cauchyFueterKernel_zero hne
        (g z) m
  have hnorm : ‖iteratedFDeriv ℝ m (fun w ↦ cauchyFueterKernel w 0) (φ z - q₀)‖ =
      ‖iteratedFDeriv ℝ m (cauchyFueterKernel (φ z)) q₀‖ := by
    rw [iteratedFDeriv_cauchyFueterKernel_right, norm_smul, Real.norm_eq_abs, abs_pow, abs_neg,
      abs_one, one_pow, one_mul]
  calc ‖iteratedFDeriv ℝ m (fun p ↦ B (g z) (cauchyFueterKernel (φ z) p)) q₀‖
      ≤ ‖B‖ * ‖iteratedFDeriv ℝ m (cauchyFueterKernel (φ z)) q₀‖ * ‖g z‖ := hnorm ▸ hk
    _ ≤ (‖B‖ + 1) * (C / δ ^ (3 + m)) * ‖g z‖ := by
        gcongr
        · exact le_add_of_nonneg_right zero_le_one
        · exact hbound m hm hδ₀ hz
    _ = (‖B‖ + 1) * C / δ ^ (3 + m) * ‖g z‖ := by ring

end BilinearKernelPotentials

section QuaternionKernelPotentials

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

/-- **Iterated derivatives of a left Cauchy–Fueter kernel potential on a ball.** Right
multiplication by `g z` acts on each kernel jet through `MulOpposite.op (g z)`. -/
theorem iteratedFDeriv_integral_cauchyFueterKernel_mul_of_mem_ball {φ g : X → ℍ}
    {q₀ q : ℍ} {δ : ℝ} (m : ℕ) (hφ : AEStronglyMeasurable φ μ) (hg : Integrable g μ)
    (hδ : ∀ᵐ z ∂μ, δ ≤ ‖φ z - q₀‖) (hq : q ∈ ball q₀ δ) :
    iteratedFDeriv ℝ m (fun p ↦ ∫ z, cauchyFueterKernel (φ z) p * g z ∂μ) q =
      ∫ z, MulOpposite.op (g z) • iteratedFDeriv ℝ m (cauchyFueterKernel (φ z)) q ∂μ := by
  have h := (ContinuousLinearMap.mul ℝ ℍ).iteratedFDeriv_integral_bilin_cauchyFueterKernel
    hφ hg hδ m hq
  simp only [ContinuousLinearMap.mul_apply'] at h
  rw [h]
  refine integral_congr_ae ?_
  filter_upwards [hδ] with z hz
  have hne : φ z ≠ q := by
    intro heq
    have hq' : ‖q - q₀‖ < δ := by simpa [mem_ball, dist_eq_norm] using hq
    linarith [heq ▸ hz]
  have hpt := (ContinuousLinearMap.mul ℝ ℍ).iteratedFDeriv_bilin_cauchyFueterKernel hne (g z) m
  simp only [ContinuousLinearMap.mul_apply'] at hpt
  rw [hpt]
  refine ContinuousMultilinearMap.ext fun v ↦ ?_
  simp [ContinuousLinearMap.compContinuousMultilinearMap_coe, MulOpposite.smul_eq_mul_unop]

/-- **Iterated derivatives of a right Cauchy–Fueter kernel potential on a ball.** Left
multiplication by `g z` acts on each kernel jet through the left `ℍ`-action `•`. -/
theorem iteratedFDeriv_integral_mul_cauchyFueterKernel_of_mem_ball {φ g : X → ℍ}
    {q₀ q : ℍ} {δ : ℝ} (m : ℕ) (hφ : AEStronglyMeasurable φ μ) (hg : Integrable g μ)
    (hδ : ∀ᵐ z ∂μ, δ ≤ ‖φ z - q₀‖) (hq : q ∈ ball q₀ δ) :
    iteratedFDeriv ℝ m (fun p ↦ ∫ z, g z * cauchyFueterKernel (φ z) p ∂μ) q =
      ∫ z, g z • iteratedFDeriv ℝ m (cauchyFueterKernel (φ z)) q ∂μ := by
  have h := (ContinuousLinearMap.mul ℝ ℍ).flip.iteratedFDeriv_integral_bilin_cauchyFueterKernel
    hφ hg hδ m hq
  simp only [ContinuousLinearMap.flip_apply, ContinuousLinearMap.mul_apply'] at h
  rw [h]
  refine integral_congr_ae ?_
  filter_upwards [hδ] with z hz
  have hne : φ z ≠ q := by
    intro heq
    have hq' : ‖q - q₀‖ < δ := by simpa [mem_ball, dist_eq_norm] using hq
    linarith [heq ▸ hz]
  have hpt :=
    (ContinuousLinearMap.mul ℝ ℍ).flip.iteratedFDeriv_bilin_cauchyFueterKernel hne (g z) m
  simp only [ContinuousLinearMap.flip_apply, ContinuousLinearMap.mul_apply'] at hpt
  rw [hpt]
  refine ContinuousMultilinearMap.ext fun v ↦ ?_
  simp [ContinuousLinearMap.compContinuousMultilinearMap_coe, smul_eq_mul]

end QuaternionKernelPotentials

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
