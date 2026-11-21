/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Quaternion.Estimates
import TauCeti.Analysis.Quaternion.Forms

/-!
# Measurability, decay bounds, and box boundary sums of Cauchy–Fueter kernel potentials

This file complements `TauCeti.Analysis.Quaternion.Estimates` with additional properties of
iterated derivatives of Cauchy–Fueter kernel potentials:

* `TauCeti.aestronglyMeasurable_iteratedFDeriv_cauchyFueterKernel_right`: `AEStronglyMeasurable`
  of the `m`-th pole derivative `z ↦ iteratedFDeriv ℝ m (cauchyFueterKernel (φ z)) p` for any
  `AEStronglyMeasurable` pole map `φ`, without any pole-avoidance hypothesis.
* `TauCeti.exists_norm_iteratedFDeriv_integral_bilinear_cauchyFueterKernel_le`,
  `TauCeti.exists_norm_iteratedFDeriv_integral_cauchyFueterKernel_mul_le`,
  `TauCeti.exists_norm_iteratedFDeriv_integral_mul_cauchyFueterKernel_le`: uniform
  `C / δ ^ (3 + m) * ∫ z, ‖g z‖ ∂μ` decay bounds on the `m`-th derivative of general bilinear,
  left, and right Cauchy–Fueter kernel potentials in terms of the separation scale `δ` and the `L¹`
  norm of the density `g`.
* `TauCeti.contDiffOn_integral_cauchyFueterKernel_mul_ball`,
  `TauCeti.contDiffAt_integral_cauchyFueterKernel_mul`,
  `TauCeti.contDiffOn_integral_mul_cauchyFueterKernel_ball`,
  `TauCeti.contDiffAt_integral_mul_cauchyFueterKernel`,
  `TauCeti.iteratedFDeriv_integral_cauchyFueterKernel_mul_of_mem_ball`,
  `TauCeti.iteratedFDeriv_integral_cauchyFueterKernel_mul`,
  `TauCeti.iteratedFDeriv_integral_mul_cauchyFueterKernel_of_mem_ball`,
  `TauCeti.iteratedFDeriv_integral_mul_cauchyFueterKernel`: specialized smoothness and iterated
  derivative formulas for left and right Cauchy–Fueter potentials with quaternion-module actions.
* `TauCeti.contDiffAt_boxBoundarySum_bilinear_cauchyFueterKernel`,
  `TauCeti.iteratedFDeriv_boxBoundarySum_bilinear_cauchyFueterKernel`,
  `TauCeti.contDiffAt_boxBoundarySum_cauchyFueterKernel_left`,
  `TauCeti.contDiffAt_boxBoundarySum_cauchyFueterKernel_right`,
  `TauCeti.iteratedFDeriv_boxBoundarySum_cauchyFueterKernel_left`,
  `TauCeti.iteratedFDeriv_boxBoundarySum_cauchyFueterKernel_right`: smoothness and iterated
  derivatives of Cauchy–Fueter box boundary potentials for general facewise integrable densities.

## References

* I. Frenkel and M. Libine, *Quaternionic analysis, representation theory and physics*,
  Adv. Math. 218 (2008), arXiv:0711.2699v5, §2.2, Proposition 2 and Theorem 9.
* A. Sudbery, *Quaternionic analysis*, Math. Proc. Cambridge Philos. Soc. 85 (1979), 199–225.
-/

public section

open Filter MeasureTheory Metric Quaternion Set TauCeti.Quaternion
open scoped ContDiff Quaternion Topology

namespace TauCeti

/-! ### Measurability, decay bounds, and specialized left/right kernel potentials -/

section KernelPotentials

universe u

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}
  {G E : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- For an a.e. strongly measurable pole map `φ : X → ℍ`, the `m`-th derivative of
`cauchyFueterKernel (φ z)` at any point `p : ℍ` is a.e. strongly measurable. No pole-avoidance
hypothesis is needed. -/
theorem aestronglyMeasurable_iteratedFDeriv_cauchyFueterKernel_right
    {φ : X → ℍ} (hφ : AEStronglyMeasurable φ μ) (m : ℕ) (p : ℍ) :
    AEStronglyMeasurable (fun z ↦ iteratedFDeriv ℝ m (cauchyFueterKernel (φ z)) p) μ := by
  have : TopologicalSpace.PseudoMetrizableSpace (ℍ [×m]→L[ℝ] ℍ) :=
    @PseudoEMetricSpace.pseudoMetrizableSpace (ℍ [×m]→L[ℝ] ℍ) _
  let K₀ : (Fin 4 → ℝ) → (ℍ [×m]→L[ℝ] ℍ) :=
    fun u ↦ iteratedFDeriv ℝ m (fun y ↦ cauchyFueterKernel y 0) (dq u)
  have hK₀_cont : ContinuousOn K₀ {0}ᶜ := by
    intro u hu
    have hdu : dq u ≠ 0 := by
      intro h0
      exact hu (by simpa [h0] using (dqEquiv_symm_dq u).symm)
    exact (((contDiffAt_cauchyFueterKernel (q₀ := 0) (by simpa using hdu)
      (n := m)).continuousAt_iteratedFDeriv le_rfl).comp dq.continuous.continuousAt
      |>.continuousWithinAt)
  have hK₀_meas : StronglyMeasurable K₀ :=
    hK₀_cont.stronglyMeasurable_of_countable_compl (by simp)
  have hcoord : AEMeasurable (fun z ↦ dqEquiv.symm (φ z - p)) μ :=
    (dqEquiv.symm.continuous.comp_aestronglyMeasurable
      ((continuous_sub_right p).comp_aestronglyMeasurable hφ)).aemeasurable
  have hcomp : AEStronglyMeasurable (fun z ↦ (-1 : ℝ) ^ m • K₀ (dqEquiv.symm (φ z - p))) μ :=
    ContinuousConstSMul.continuous_const_smul ((-1 : ℝ) ^ m) |>.comp_aestronglyMeasurable
      (hK₀_meas.aestronglyMeasurable.comp_aemeasurable hcoord)
  refine hcomp.congr (ae_of_all _ fun z ↦ ?_)
  simp only [K₀, dq_dqEquiv_symm, iteratedFDeriv_cauchyFueterKernel_right]

/-- Uniform decay bound on the `m`-th derivative of a bilinearly weighted Cauchy–Fueter kernel
potential in terms of the separation scale `δ` and the `L¹` norm of `g`. The constant depends only
on the bilinear pairing `B` and the maximum order `N`, uniformly across all measurable spaces
`X : Type u` and measures `μ` on `X`. -/
theorem exists_norm_iteratedFDeriv_integral_bilinear_cauchyFueterKernel_le
    (B : G →L[ℝ] ℍ →L[ℝ] E) (N : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ m ≤ N, ∀ {X : Type u} [MeasurableSpace X] {μ : Measure X}
      {φ : X → ℍ} {g : X → G} {q₀ : ℍ} {δ : ℝ},
        AEStronglyMeasurable φ μ → Integrable g μ → 0 < δ → (∀ᵐ z ∂μ, δ ≤ ‖φ z - q₀‖) →
        ‖iteratedFDeriv ℝ m (fun q ↦ ∫ z, B (g z) (cauchyFueterKernel (φ z) q) ∂μ) q₀‖ ≤
          C / δ ^ (3 + m) * ∫ z, ‖g z‖ ∂μ := by
  obtain ⟨K, hK_pos, hK⟩ := B.isBoundedBilinearMap.bound
  obtain ⟨C, hC, hbound⟩ :=
    exists_norm_iteratedFDeriv_cauchyFueterKernel_right_le_of_le_norm_sub N
  refine ⟨K * C, mul_pos hK_pos hC, fun m hm {X _ μ φ g q₀ δ} hφ hg hδ₀ hδ ↦ ?_⟩
  have hcomm := iteratedFDeriv_integral_bilin_cauchyFueterKernel B.flip hφ hg hδ m
    (mem_ball_self hδ₀)
  simp only [ContinuousLinearMap.flip_apply] at hcomm
  rw [hcomm]
  refine (norm_integral_le_of_norm_le
    (hg.norm.const_mul (K * C / δ ^ (3 + m))) ?_).trans_eq (integral_const_mul _ _)
  filter_upwards [hδ] with z hz
  have hne : φ z ≠ q₀ := sub_ne_zero.mp (norm_pos_iff.mp (hδ₀.trans_le hz))
  have hfn : (fun p ↦ B (g z) (cauchyFueterKernel (φ z) p)) =
      B (g z) ∘ cauchyFueterKernel (φ z) := by
    funext p
    simp [Function.comp_apply]
  rw [hfn, (B (g z)).iteratedFDeriv_comp_left
    (contDiffAt_cauchyFueterKernel_right hne (n := m)) le_rfl]
  calc ‖(B (g z)).compContinuousMultilinearMap
          (iteratedFDeriv ℝ m (cauchyFueterKernel (φ z)) q₀)‖
      ≤ ‖B (g z)‖ * ‖iteratedFDeriv ℝ m (cauchyFueterKernel (φ z)) q₀‖ :=
        (B (g z)).norm_compContinuousMultilinearMap_le _
    _ ≤ (K * ‖g z‖) * (C / δ ^ (3 + m)) :=
        mul_le_mul ((B (g z)).opNorm_le_bound (by positivity) (hK (g z)))
          (hbound m hm hδ₀ hz) (norm_nonneg _) (by positivity)
    _ = K * C / δ ^ (3 + m) * ‖g z‖ := by ring

/-- Smoothness on `ball q₀ δ` of a left Cauchy–Fueter kernel potential
`q ↦ ∫ z, cauchyFueterKernel (φ z) q * g z ∂μ`. -/
theorem contDiffOn_integral_cauchyFueterKernel_mul_ball {φ g : X → ℍ}
    {q₀ : ℍ} {δ : ℝ} {n : ℕ∞} (hφ : AEStronglyMeasurable φ μ) (hg : Integrable g μ)
    (hδ : ∀ᵐ z ∂μ, δ ≤ ‖φ z - q₀‖) :
    ContDiffOn ℝ n (fun q ↦ ∫ z, cauchyFueterKernel (φ z) q * g z ∂μ) (ball q₀ δ) := by
  simpa only [ContinuousLinearMap.mul_apply'] using
    contDiffOn_integral_bilin_cauchyFueterKernel (n := n)
      (ContinuousLinearMap.mul ℝ ℍ) hφ hg hδ

/-- Smoothness at `q₀` of a left Cauchy–Fueter kernel potential
`q ↦ ∫ z, cauchyFueterKernel (φ z) q * g z ∂μ`. -/
theorem contDiffAt_integral_cauchyFueterKernel_mul {φ g : X → ℍ}
    {q₀ : ℍ} {δ : ℝ} {n : ℕ∞} (hφ : AEStronglyMeasurable φ μ) (hg : Integrable g μ)
    (hδ₀ : 0 < δ) (hδ : ∀ᵐ z ∂μ, δ ≤ ‖φ z - q₀‖) :
    ContDiffAt ℝ n (fun q ↦ ∫ z, cauchyFueterKernel (φ z) q * g z ∂μ) q₀ :=
  (contDiffOn_integral_cauchyFueterKernel_mul_ball hφ hg hδ).contDiffAt
    (isOpen_ball.mem_nhds (mem_ball_self hδ₀))

/-- Smoothness on `ball q₀ δ` of a right Cauchy–Fueter kernel potential
`q ↦ ∫ z, g z * cauchyFueterKernel (φ z) q ∂μ`. -/
theorem contDiffOn_integral_mul_cauchyFueterKernel_ball {φ g : X → ℍ}
    {q₀ : ℍ} {δ : ℝ} {n : ℕ∞} (hφ : AEStronglyMeasurable φ μ) (hg : Integrable g μ)
    (hδ : ∀ᵐ z ∂μ, δ ≤ ‖φ z - q₀‖) :
    ContDiffOn ℝ n (fun q ↦ ∫ z, g z * cauchyFueterKernel (φ z) q ∂μ) (ball q₀ δ) := by
  simpa only [ContinuousLinearMap.flip_apply, ContinuousLinearMap.mul_apply'] using
    contDiffOn_integral_bilin_cauchyFueterKernel (n := n)
      (ContinuousLinearMap.mul ℝ ℍ).flip hφ hg hδ

/-- Smoothness at `q₀` of a right Cauchy–Fueter kernel potential
`q ↦ ∫ z, g z * cauchyFueterKernel (φ z) q ∂μ`. -/
theorem contDiffAt_integral_mul_cauchyFueterKernel {φ g : X → ℍ}
    {q₀ : ℍ} {δ : ℝ} {n : ℕ∞} (hφ : AEStronglyMeasurable φ μ) (hg : Integrable g μ)
    (hδ₀ : 0 < δ) (hδ : ∀ᵐ z ∂μ, δ ≤ ‖φ z - q₀‖) :
    ContDiffAt ℝ n (fun q ↦ ∫ z, g z * cauchyFueterKernel (φ z) q ∂μ) q₀ :=
  (contDiffOn_integral_mul_cauchyFueterKernel_ball hφ hg hδ).contDiffAt
    (isOpen_ball.mem_nhds (mem_ball_self hδ₀))

/-- **Iterated derivatives of a left Cauchy–Fueter kernel potential on a ball.** Right
multiplication by `g z` acts on each kernel jet through `MulOpposite.op (g z)`. -/
theorem iteratedFDeriv_integral_cauchyFueterKernel_mul_of_mem_ball {φ g : X → ℍ}
    {q₀ q : ℍ} {δ : ℝ} (m : ℕ) (hφ : AEStronglyMeasurable φ μ) (hg : Integrable g μ)
    (hδ : ∀ᵐ z ∂μ, δ ≤ ‖φ z - q₀‖) (hq : q ∈ ball q₀ δ) :
    iteratedFDeriv ℝ m (fun p ↦ ∫ z, cauchyFueterKernel (φ z) p * g z ∂μ) q =
      ∫ z, MulOpposite.op (g z) • iteratedFDeriv ℝ m (cauchyFueterKernel (φ z)) q ∂μ := by
  have h := iteratedFDeriv_integral_bilin_cauchyFueterKernel
    (ContinuousLinearMap.mul ℝ ℍ) hφ hg hδ m hq
  simp only [ContinuousLinearMap.mul_apply'] at h
  rw [h]
  refine integral_congr_ae ?_
  filter_upwards [hδ] with z hz
  have hne : φ z ≠ q := by
    intro heq
    have hq' : ‖q - q₀‖ < δ := by simpa [mem_ball, dist_eq_norm] using hq
    linarith [heq ▸ hz]
  have hfn : (fun y ↦ cauchyFueterKernel (φ z) y * g z) =
      ((ContinuousLinearMap.mul ℝ ℍ).flip (g z)) ∘ cauchyFueterKernel (φ z) := by
    funext y
    simp
  rw [hfn, ((ContinuousLinearMap.mul ℝ ℍ).flip (g z)).iteratedFDeriv_comp_left
    (contDiffAt_cauchyFueterKernel_right hne (n := m)) le_rfl]
  refine ContinuousMultilinearMap.ext fun v ↦ ?_
  simp [ContinuousLinearMap.compContinuousMultilinearMap_coe, MulOpposite.smul_eq_mul_unop]

/-- **Iterated derivatives of a left Cauchy–Fueter kernel potential.** Right multiplication by
`g z` acts on each kernel jet through `MulOpposite.op (g z)`. -/
theorem iteratedFDeriv_integral_cauchyFueterKernel_mul {φ g : X → ℍ}
    {q₀ : ℍ} {δ : ℝ} (m : ℕ) (hφ : AEStronglyMeasurable φ μ) (hg : Integrable g μ)
    (hδ₀ : 0 < δ) (hδ : ∀ᵐ z ∂μ, δ ≤ ‖φ z - q₀‖) :
    iteratedFDeriv ℝ m (fun q ↦ ∫ z, cauchyFueterKernel (φ z) q * g z ∂μ) q₀ =
      ∫ z, MulOpposite.op (g z) • iteratedFDeriv ℝ m (cauchyFueterKernel (φ z)) q₀ ∂μ :=
  iteratedFDeriv_integral_cauchyFueterKernel_mul_of_mem_ball m hφ hg hδ (mem_ball_self hδ₀)

/-- **Iterated derivatives of a right Cauchy–Fueter kernel potential on a ball.** Left
multiplication by `g z` acts on each kernel jet through the left `ℍ`-action `•`. -/
theorem iteratedFDeriv_integral_mul_cauchyFueterKernel_of_mem_ball {φ g : X → ℍ}
    {q₀ q : ℍ} {δ : ℝ} (m : ℕ) (hφ : AEStronglyMeasurable φ μ) (hg : Integrable g μ)
    (hδ : ∀ᵐ z ∂μ, δ ≤ ‖φ z - q₀‖) (hq : q ∈ ball q₀ δ) :
    iteratedFDeriv ℝ m (fun p ↦ ∫ z, g z * cauchyFueterKernel (φ z) p ∂μ) q =
      ∫ z, g z • iteratedFDeriv ℝ m (cauchyFueterKernel (φ z)) q ∂μ := by
  have h := iteratedFDeriv_integral_bilin_cauchyFueterKernel
    (ContinuousLinearMap.mul ℝ ℍ).flip hφ hg hδ m hq
  simp only [ContinuousLinearMap.flip_apply, ContinuousLinearMap.mul_apply'] at h
  rw [h]
  refine integral_congr_ae ?_
  filter_upwards [hδ] with z hz
  have hne : φ z ≠ q := by
    intro heq
    have hq' : ‖q - q₀‖ < δ := by simpa [mem_ball, dist_eq_norm] using hq
    linarith [heq ▸ hz]
  have hfn : (fun y ↦ g z * cauchyFueterKernel (φ z) y) =
      (ContinuousLinearMap.mul ℝ ℍ (g z)) ∘ cauchyFueterKernel (φ z) := by
    funext y
    simp
  rw [hfn, (ContinuousLinearMap.mul ℝ ℍ (g z)).iteratedFDeriv_comp_left
    (contDiffAt_cauchyFueterKernel_right hne (n := m)) le_rfl]
  refine ContinuousMultilinearMap.ext fun v ↦ ?_
  simp [ContinuousLinearMap.compContinuousMultilinearMap_coe, smul_eq_mul]

/-- **Iterated derivatives of a right Cauchy–Fueter kernel potential.** Left multiplication by
`g z` acts on each kernel jet through the left `ℍ`-action `•`. -/
theorem iteratedFDeriv_integral_mul_cauchyFueterKernel {φ g : X → ℍ}
    {q₀ : ℍ} {δ : ℝ} (m : ℕ) (hφ : AEStronglyMeasurable φ μ) (hg : Integrable g μ)
    (hδ₀ : 0 < δ) (hδ : ∀ᵐ z ∂μ, δ ≤ ‖φ z - q₀‖) :
    iteratedFDeriv ℝ m (fun q ↦ ∫ z, g z * cauchyFueterKernel (φ z) q ∂μ) q₀ =
      ∫ z, g z • iteratedFDeriv ℝ m (cauchyFueterKernel (φ z)) q₀ ∂μ :=
  iteratedFDeriv_integral_mul_cauchyFueterKernel_of_mem_ball m hφ hg hδ (mem_ball_self hδ₀)

/-- Uniform decay bound on the `m`-th derivative of a left Cauchy–Fueter kernel potential
`q ↦ ∫ z, cauchyFueterKernel (φ z) q * g z ∂μ`. The constant depends only on the maximum order `N`,
uniformly across all measurable spaces `X : Type u` and measures `μ` on `X`. -/
theorem exists_norm_iteratedFDeriv_integral_cauchyFueterKernel_mul_le (N : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ m ≤ N, ∀ {X : Type u} [MeasurableSpace X] {μ : Measure X}
      {φ g : X → ℍ} {q₀ : ℍ} {δ : ℝ},
        AEStronglyMeasurable φ μ → Integrable g μ → 0 < δ → (∀ᵐ z ∂μ, δ ≤ ‖φ z - q₀‖) →
        ‖iteratedFDeriv ℝ m (fun q ↦ ∫ z, cauchyFueterKernel (φ z) q * g z ∂μ) q₀‖ ≤
          C / δ ^ (3 + m) * ∫ z, ‖g z‖ ∂μ := by
  simpa only [ContinuousLinearMap.flip_apply, ContinuousLinearMap.mul_apply'] using
    exists_norm_iteratedFDeriv_integral_bilinear_cauchyFueterKernel_le.{u}
      (ContinuousLinearMap.mul ℝ ℍ).flip N

/-- Uniform decay bound on the `m`-th derivative of a right Cauchy–Fueter kernel potential
`q ↦ ∫ z, g z * cauchyFueterKernel (φ z) q ∂μ`. The constant depends only on the maximum order `N`,
uniformly across all measurable spaces `X : Type u` and measures `μ` on `X`. -/
theorem exists_norm_iteratedFDeriv_integral_mul_cauchyFueterKernel_le (N : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ m ≤ N, ∀ {X : Type u} [MeasurableSpace X] {μ : Measure X}
      {φ g : X → ℍ} {q₀ : ℍ} {δ : ℝ},
        AEStronglyMeasurable φ μ → Integrable g μ → 0 < δ → (∀ᵐ z ∂μ, δ ≤ ‖φ z - q₀‖) →
        ‖iteratedFDeriv ℝ m (fun q ↦ ∫ z, g z * cauchyFueterKernel (φ z) q ∂μ) q₀‖ ≤
          C / δ ^ (3 + m) * ∫ z, ‖g z‖ ∂μ := by
  simpa only [ContinuousLinearMap.mul_apply'] using
    exists_norm_iteratedFDeriv_integral_bilinear_cauchyFueterKernel_le.{u}
      (ContinuousLinearMap.mul ℝ ℍ) N

end KernelPotentials

/-! ### Differentiated Cauchy–Fueter box boundary potentials -/

section BoundaryRepresentations

/-- Smoothness at `q₀` of a bilinearly weighted Cauchy–Fueter kernel boundary sum over the faces
of a coordinate box, whenever the pole map is a.e. strongly measurable on each face, each face
weight is integrable on its face, and each face is positively separated from `q₀` almost
everywhere. -/
theorem contDiffAt_boxBoundarySum_bilinear_cauchyFueterKernel
    {d : ℕ} {a b : Fin (d + 1) → ℝ}
    {G E : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (B : G →L[ℝ] ℍ →L[ℝ] E)
    {φ : (Fin (d + 1) → ℝ) → ℍ} {w : Fin (d + 1) → (Fin (d + 1) → ℝ) → G}
    {q₀ : ℍ} {n : ℕ∞}
    (hφ : ∀ (i : Fin (d + 1)) {c : ℝ}, c = a i ∨ c = b i →
      AEStronglyMeasurable (fun u ↦ φ (i.insertNth c u))
        (volume.restrict (Icc (a ∘ i.succAbove) (b ∘ i.succAbove))))
    (hw : ∀ (i : Fin (d + 1)) {c : ℝ}, c = a i ∨ c = b i →
      IntegrableOn (fun u ↦ w i (i.insertNth c u))
        (Icc (a ∘ i.succAbove) (b ∘ i.succAbove)))
    (hsep : ∀ (i : Fin (d + 1)) {c : ℝ}, c = a i ∨ c = b i →
      ∃ δ > 0, ∀ᵐ u ∂volume.restrict (Icc (a ∘ i.succAbove) (b ∘ i.succAbove)),
        δ ≤ ‖φ (i.insertNth c u) - q₀‖) :
    ContDiffAt ℝ n
      (fun q ↦ boxBoundarySum a b (fun i x ↦ B (w i x) (cauchyFueterKernel (φ x) q))) q₀ := by
  simp only [boxBoundarySum_def]
  refine ContDiffAt.sum fun i _ ↦ ?_
  have hface {c : ℝ} (hc : c = a i ∨ c = b i) :
      ContDiffAt ℝ n
        (fun q ↦ ∫ u in Icc (a ∘ i.succAbove) (b ∘ i.succAbove),
          B (w i (i.insertNth c u)) (cauchyFueterKernel (φ (i.insertNth c u)) q)) q₀ := by
    obtain ⟨δ, hδ₀, hδ⟩ := hsep i hc
    simpa only [ContinuousLinearMap.flip_apply] using
      contDiffAt_integral_bilin_cauchyFueterKernel (n := n) B.flip
        (hφ i hc) (hw i hc) hδ (mem_ball_self hδ₀)
  exact (hface (Or.inr rfl)).sub (hface (Or.inl rfl))

/-- Differentiating a bilinearly weighted Cauchy–Fueter kernel boundary sum over the faces of a
coordinate box at any point `q₀` positively separated almost everywhere from each face. -/
theorem iteratedFDeriv_boxBoundarySum_bilinear_cauchyFueterKernel
    {d : ℕ} {a b : Fin (d + 1) → ℝ}
    {G E : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (B : G →L[ℝ] ℍ →L[ℝ] E)
    {φ : (Fin (d + 1) → ℝ) → ℍ} {w : Fin (d + 1) → (Fin (d + 1) → ℝ) → G}
    {q₀ : ℍ} (m : ℕ)
    (hφ : ∀ (i : Fin (d + 1)) {c : ℝ}, c = a i ∨ c = b i →
      AEStronglyMeasurable (fun u ↦ φ (i.insertNth c u))
        (volume.restrict (Icc (a ∘ i.succAbove) (b ∘ i.succAbove))))
    (hw : ∀ (i : Fin (d + 1)) {c : ℝ}, c = a i ∨ c = b i →
      IntegrableOn (fun u ↦ w i (i.insertNth c u))
        (Icc (a ∘ i.succAbove) (b ∘ i.succAbove)))
    (hsep : ∀ (i : Fin (d + 1)) {c : ℝ}, c = a i ∨ c = b i →
      ∃ δ > 0, ∀ᵐ u ∂volume.restrict (Icc (a ∘ i.succAbove) (b ∘ i.succAbove)),
        δ ≤ ‖φ (i.insertNth c u) - q₀‖) :
    iteratedFDeriv ℝ m
        (fun q ↦ boxBoundarySum a b (fun i x ↦ B (w i x) (cauchyFueterKernel (φ x) q))) q₀ =
      boxBoundarySum a b
        (fun i x ↦ (B (w i x)).compContinuousMultilinearMap
          (iteratedFDeriv ℝ m (cauchyFueterKernel (φ x)) q₀)) := by
  have hface_cd (i : Fin (d + 1)) {c : ℝ} (hc : c = a i ∨ c = b i) :
      ContDiffAt ℝ m
        (fun q ↦ ∫ u in Icc (a ∘ i.succAbove) (b ∘ i.succAbove),
          B (w i (i.insertNth c u)) (cauchyFueterKernel (φ (i.insertNth c u)) q)) q₀ := by
    obtain ⟨δ, hδ₀, hδ⟩ := hsep i hc
    simpa only [ContinuousLinearMap.flip_apply] using
      (contDiffAt_integral_bilin_cauchyFueterKernel (n := ⊤) B.flip
        (hφ i hc) (hw i hc) hδ (mem_ball_self hδ₀)).of_le (by simp)
  have hface_deriv (i : Fin (d + 1)) {c : ℝ} (hc : c = a i ∨ c = b i) :
      iteratedFDeriv ℝ m
          (fun q ↦ ∫ u in Icc (a ∘ i.succAbove) (b ∘ i.succAbove),
            B (w i (i.insertNth c u)) (cauchyFueterKernel (φ (i.insertNth c u)) q)) q₀ =
        ∫ u in Icc (a ∘ i.succAbove) (b ∘ i.succAbove),
          (B (w i (i.insertNth c u))).compContinuousMultilinearMap
            (iteratedFDeriv ℝ m (cauchyFueterKernel (φ (i.insertNth c u))) q₀) := by
    obtain ⟨δ, hδ₀, hδ⟩ := hsep i hc
    have hcomm := iteratedFDeriv_integral_bilin_cauchyFueterKernel B.flip
      (hφ i hc) (hw i hc) hδ m (mem_ball_self hδ₀)
    simp only [ContinuousLinearMap.flip_apply] at hcomm
    rw [hcomm]
    refine integral_congr_ae ?_
    filter_upwards [hδ] with u hu
    have hne : φ (i.insertNth c u) ≠ q₀ := sub_ne_zero.mp (norm_pos_iff.mp (hδ₀.trans_le hu))
    have hfn : (fun p ↦ B (w i (i.insertNth c u)) (cauchyFueterKernel (φ (i.insertNth c u)) p)) =
        B (w i (i.insertNth c u)) ∘ cauchyFueterKernel (φ (i.insertNth c u)) := by
      funext p
      simp [Function.comp_apply]
    rw [hfn]
    exact (B (w i (i.insertNth c u))).iteratedFDeriv_comp_left
      (contDiffAt_cauchyFueterKernel_right hne (n := m)) le_rfl
  simp only [boxBoundarySum_def]
  rw [iteratedFDeriv_fun_sum_apply fun i _ ↦
    (hface_cd i (Or.inr rfl)).sub (hface_cd i (Or.inl rfl))]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [fun_iteratedFDeriv_sub_apply (hface_cd i (Or.inr rfl)) (hface_cd i (Or.inl rfl)),
    hface_deriv i (Or.inr rfl), hface_deriv i (Or.inl rfl)]

/-- Compactness supplies a positive separation distance from `q₀` to any closed `dq`-box face that
does not contain `q₀`. -/
private theorem exists_pos_le_norm_dq_insertNth_sub {a b : Fin 4 → ℝ} {q₀ : ℍ}
    (hq₀ : ∀ (i : Fin 4) {c : ℝ}, c = a i ∨ c = b i →
      ∀ u ∈ Icc (a ∘ i.succAbove) (b ∘ i.succAbove), dq (i.insertNth c u) ≠ q₀)
    (i : Fin 4) {c : ℝ} (hc : c = a i ∨ c = b i) :
    ∃ δ > 0, ∀ᵐ u ∂volume.restrict (Icc (a ∘ i.succAbove) (b ∘ i.succAbove)),
      δ ≤ ‖dq (i.insertNth c u) - q₀‖ := by
  set F := Icc (a ∘ i.succAbove) (b ∘ i.succAbove)
  rcases F.eq_empty_or_nonempty with hemp | hneF
  · exact ⟨1, zero_lt_one, by simp [hemp]⟩
  · obtain ⟨u₀, hu₀, hmin⟩ := isCompact_Icc.exists_isMinOn hneF
      (by fun_prop : Continuous fun u ↦ ‖dq (i.insertNth c u) - q₀‖).continuousOn
    exact ⟨‖dq (i.insertNth c u₀) - q₀‖, norm_pos_iff.mpr (sub_ne_zero.mpr (hq₀ i hc u₀ hu₀)),
      (ae_restrict_mem measurableSet_Icc).mono fun u hu ↦ hmin hu⟩

/-- Smoothness at any point `q₀` off the eight closed faces of a coordinate box of the left
Cauchy–Fueter box boundary potential of a facewise integrable density `g`. -/
theorem contDiffAt_boxBoundarySum_cauchyFueterKernel_left
    {a b : Fin 4 → ℝ} {g : ℍ → ℍ} {q₀ : ℍ} {n : ℕ∞}
    (hg : ∀ (i : Fin 4) {c : ℝ}, c = a i ∨ c = b i →
      IntegrableOn (fun u ↦ g (dq (i.insertNth c u)))
        (Icc (a ∘ i.succAbove) (b ∘ i.succAbove)))
    (hq₀ : ∀ (i : Fin 4) {c : ℝ}, c = a i ∨ c = b i →
      ∀ u ∈ Icc (a ∘ i.succAbove) (b ∘ i.succAbove), dq (i.insertNth c u) ≠ q₀) :
    ContDiffAt ℝ n
      (fun q ↦ boxBoundarySum a b
        (fun i x ↦ cauchyFueterKernel (dq x) q * dq (Pi.single i 1) * g (dq x))) q₀ := by
  have h := contDiffAt_boxBoundarySum_bilinear_cauchyFueterKernel (n := n)
    (a := a) (b := b) (ContinuousLinearMap.mul ℝ ℍ).flip
    (φ := dq) (w := fun i x ↦ dq (Pi.single i 1) * g (dq x)) (q₀ := q₀)
    (fun _ _ _ ↦ (by fun_prop : Continuous fun u ↦ dq _).aestronglyMeasurable)
    (fun i _ hc ↦ (hg i hc).const_mul _)
    (fun i _ hc ↦ exists_pos_le_norm_dq_insertNth_sub hq₀ i hc)
  simpa only [ContinuousLinearMap.flip_apply, ContinuousLinearMap.mul_apply', mul_assoc] using h

/-- Smoothness at any point `q₀` off the eight closed faces of a coordinate box of the right
Cauchy–Fueter box boundary potential of a facewise integrable density `g`. -/
theorem contDiffAt_boxBoundarySum_cauchyFueterKernel_right
    {a b : Fin 4 → ℝ} {g : ℍ → ℍ} {q₀ : ℍ} {n : ℕ∞}
    (hg : ∀ (i : Fin 4) {c : ℝ}, c = a i ∨ c = b i →
      IntegrableOn (fun u ↦ g (dq (i.insertNth c u)))
        (Icc (a ∘ i.succAbove) (b ∘ i.succAbove)))
    (hq₀ : ∀ (i : Fin 4) {c : ℝ}, c = a i ∨ c = b i →
      ∀ u ∈ Icc (a ∘ i.succAbove) (b ∘ i.succAbove), dq (i.insertNth c u) ≠ q₀) :
    ContDiffAt ℝ n
      (fun q ↦ boxBoundarySum a b
        (fun i x ↦ g (dq x) * dq (Pi.single i 1) * cauchyFueterKernel (dq x) q)) q₀ := by
  have h := contDiffAt_boxBoundarySum_bilinear_cauchyFueterKernel (n := n)
    (a := a) (b := b) (ContinuousLinearMap.mul ℝ ℍ)
    (φ := dq) (w := fun i x ↦ g (dq x) * dq (Pi.single i 1)) (q₀ := q₀)
    (fun _ _ _ ↦ (by fun_prop : Continuous fun u ↦ dq _).aestronglyMeasurable)
    (fun i _ hc ↦ (hg i hc).mul_const _)
    (fun i _ hc ↦ exists_pos_le_norm_dq_insertNth_sub hq₀ i hc)
  simpa only [ContinuousLinearMap.mul_apply'] using h

/-- Differentiating the left Cauchy–Fueter box boundary potential at any point `q₀` off the eight
closed faces of a coordinate box, for any facewise integrable boundary density `g`. -/
theorem iteratedFDeriv_boxBoundarySum_cauchyFueterKernel_left
    {a b : Fin 4 → ℝ} {g : ℍ → ℍ} {q₀ : ℍ} (m : ℕ)
    (hg : ∀ (i : Fin 4) {c : ℝ}, c = a i ∨ c = b i →
      IntegrableOn (fun u ↦ g (dq (i.insertNth c u)))
        (Icc (a ∘ i.succAbove) (b ∘ i.succAbove)))
    (hq₀ : ∀ (i : Fin 4) {c : ℝ}, c = a i ∨ c = b i →
      ∀ u ∈ Icc (a ∘ i.succAbove) (b ∘ i.succAbove), dq (i.insertNth c u) ≠ q₀) :
    iteratedFDeriv ℝ m
        (fun q ↦ boxBoundarySum a b
          (fun i x ↦ cauchyFueterKernel (dq x) q * dq (Pi.single i 1) * g (dq x))) q₀ =
      boxBoundarySum a b
        (fun i x ↦ MulOpposite.op (dq (Pi.single i 1) * g (dq x)) •
          iteratedFDeriv ℝ m (cauchyFueterKernel (dq x)) q₀) := by
  have h := iteratedFDeriv_boxBoundarySum_bilinear_cauchyFueterKernel
    (a := a) (b := b) (ContinuousLinearMap.mul ℝ ℍ).flip
    (φ := dq) (w := fun i x ↦ dq (Pi.single i 1) * g (dq x)) (q₀ := q₀) m
    (fun _ _ _ ↦ (by fun_prop : Continuous fun u ↦ dq _).aestronglyMeasurable)
    (fun i _ hc ↦ (hg i hc).const_mul _)
    (fun i _ hc ↦ exists_pos_le_norm_dq_insertNth_sub hq₀ i hc)
  simp only [ContinuousLinearMap.flip_apply, ContinuousLinearMap.mul_apply'] at h
  have hfn :
      (fun i x ↦ ((ContinuousLinearMap.mul ℝ ℍ).flip (dq (Pi.single i 1) * g (dq x)))
        |>.compContinuousMultilinearMap (iteratedFDeriv ℝ m (cauchyFueterKernel (dq x)) q₀)) =
      fun i x ↦ MulOpposite.op (dq (Pi.single i 1) * g (dq x)) •
        iteratedFDeriv ℝ m (cauchyFueterKernel (dq x)) q₀ := by
    funext i x
    refine ContinuousMultilinearMap.ext fun v ↦ ?_
    simp [ContinuousLinearMap.compContinuousMultilinearMap_coe, MulOpposite.smul_eq_mul_unop]
  simp only [mul_assoc]
  rw [h, hfn]

/-- Differentiating the right Cauchy–Fueter box boundary potential at any point `q₀` off the eight
closed faces of a coordinate box, for any facewise integrable boundary density `g`. -/
theorem iteratedFDeriv_boxBoundarySum_cauchyFueterKernel_right
    {a b : Fin 4 → ℝ} {g : ℍ → ℍ} {q₀ : ℍ} (m : ℕ)
    (hg : ∀ (i : Fin 4) {c : ℝ}, c = a i ∨ c = b i →
      IntegrableOn (fun u ↦ g (dq (i.insertNth c u)))
        (Icc (a ∘ i.succAbove) (b ∘ i.succAbove)))
    (hq₀ : ∀ (i : Fin 4) {c : ℝ}, c = a i ∨ c = b i →
      ∀ u ∈ Icc (a ∘ i.succAbove) (b ∘ i.succAbove), dq (i.insertNth c u) ≠ q₀) :
    iteratedFDeriv ℝ m
        (fun q ↦ boxBoundarySum a b
          (fun i x ↦ g (dq x) * dq (Pi.single i 1) * cauchyFueterKernel (dq x) q)) q₀ =
      boxBoundarySum a b
        (fun i x ↦ (g (dq x) * dq (Pi.single i 1)) •
          iteratedFDeriv ℝ m (cauchyFueterKernel (dq x)) q₀) := by
  have h := iteratedFDeriv_boxBoundarySum_bilinear_cauchyFueterKernel
    (a := a) (b := b) (ContinuousLinearMap.mul ℝ ℍ)
    (φ := dq) (w := fun i x ↦ g (dq x) * dq (Pi.single i 1)) (q₀ := q₀) m
    (fun _ _ _ ↦ (by fun_prop : Continuous fun u ↦ dq _).aestronglyMeasurable)
    (fun i _ hc ↦ (hg i hc).mul_const _)
    (fun i _ hc ↦ exists_pos_le_norm_dq_insertNth_sub hq₀ i hc)
  simp only [ContinuousLinearMap.mul_apply'] at h
  have hfn :
      (fun i x ↦ (ContinuousLinearMap.mul ℝ ℍ (g (dq x) * dq (Pi.single i 1)))
        |>.compContinuousMultilinearMap (iteratedFDeriv ℝ m (cauchyFueterKernel (dq x)) q₀)) =
      fun i x ↦ (g (dq x) * dq (Pi.single i 1)) •
        iteratedFDeriv ℝ m (cauchyFueterKernel (dq x)) q₀ := by
    funext i x
    refine ContinuousMultilinearMap.ext fun v ↦ ?_
    simp [ContinuousLinearMap.compContinuousMultilinearMap_coe, smul_eq_mul]
  rw [h, hfn]

end BoundaryRepresentations

end TauCeti
