/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Quaternion.Cauchy.Representation
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import TauCeti.Algebra.Quaternion.Basic
import TauCeti.Analysis.Calculus.IteratedFDeriv.ParametricIntegral
import TauCeti.Analysis.Calculus.IteratedFDeriv.Star
import TauCeti.Analysis.Quaternion.Cauchy.CutoffField
import TauCeti.Analysis.Quaternion.Reflection

/-!
# Differentiated Cauchy–Fueter representations and universal derivative estimates

Differentiating the Cauchy–Fueter kernel `G(q - q₀) = (q - q₀)⁻¹ / ‖q - q₀‖²` in its second
argument `q₀` produces a continuous multilinear jet of homogeneous degree `-3 - m`. Away from the
support of a boundary measure, the pole separation `δ ≤ ‖φ z - q₀‖` gives a common closed-ball
bound on `‖D^m_q G(φ z - q)‖`, so dominated differentiation under the Bochner integral commutes
`iteratedFDeriv ℝ m` with potential integration at every order `m`.

Combining this kernel-potential differentiation with the box and affine Cauchy–Fueter integral
formulas expresses every iterated real Fréchet derivative `iteratedFDeriv ℝ m f (dq x₀)` of a left
or right Fueter regular function as an explicit boundary integral over the eight three-dimensional
faces of the box or positively oriented affine parallelepiped. Quaternion coefficients act on the
continuous multilinear kernel jet `D^m[q ↦ G(z - q)](q₀) : ℍ [×m]→L[ℝ] ℍ` on the left via `•` and
on the right via `MulOpposite.op _ • _`, preserving the noncommutative factor orders
`D^m G * Dq * f` (left regular) and `f * Dq * D^m G` (right regular).

Specializing the differentiated box representation to the axis-aligned cube of side `R` centred at
`q₀` — whose closed body lies inside `closedBall q₀ R` because `√(4 (R / 2)²) = R`, whose eight
faces lie at distance at least `R / 2` from `q₀`, and whose three-dimensional faces each have
volume `R³` — yields the universal Cauchy-type derivative estimates
`TauCeti.leftFueter_iteratedFDeriv_bound` and `TauCeti.rightFueter_iteratedFDeriv_bound`: for each
`m : ℕ` there is a constant `C > 0`, depending on `m` alone, such that whenever `f` is left (or
right) Fueter regular on a set `Ω` containing `closedBall q₀ R` (`R > 0`) and bounded in norm by
`M` on `closedBall q₀ R`,

`‖iteratedFDeriv ℝ m f q₀‖ ≤ C * R⁻¹ ^ m * M`.

## Main results

* `TauCeti.hasFTaylorSeriesUpToOn_integral_bilinear_cauchyFueterKernel`,
  `TauCeti.contDiffOn_integral_bilinear_cauchyFueterKernel_ball`,
  `TauCeti.iteratedFDeriv_integral_bilinear_cauchyFueterKernel`,
  `TauCeti.iteratedFDeriv_integral_cauchyFueterKernel_mul`,
  `TauCeti.iteratedFDeriv_integral_mul_cauchyFueterKernel`: formal Taylor series, smoothness on
  open balls, and iterated derivatives of general bilinearly paired, left, and right Cauchy–Fueter
  kernel potentials at positively separated points.
* `TauCeti.contDiffAt_boxBoundarySum_bilinear_cauchyFueterKernel`,
  `TauCeti.iteratedFDeriv_boxBoundarySum_bilinear_cauchyFueterKernel`: smoothness and iterated
  derivatives of bilinearly weighted Cauchy–Fueter boundary sums off the faces of a box.
* `TauCeti.left_cauchyFueter_iteratedFDeriv_box`,
  `TauCeti.right_cauchyFueter_iteratedFDeriv_box`: differentiated Cauchy–Fueter formulas on an
  axis-aligned box.
* `TauCeti.left_cauchyFueter_iteratedFDeriv_affine`,
  `TauCeti.right_cauchyFueter_iteratedFDeriv_affine`: differentiated Cauchy–Fueter formulas over
  the unit-cube face charts of a positively oriented affine parallelepiped.
* `TauCeti.leftFueter_iteratedFDeriv_bound`, `TauCeti.rightFueter_iteratedFDeriv_bound`: universal
  `C_m R⁻ᵐ M` Cauchy estimates on closed balls for left and right Fueter regular functions.

## References

* I. Frenkel and M. Libine, *Quaternionic analysis, representation theory and physics*,
  Adv. Math. 218 (2008), arXiv:0711.2699v5, §2.2, Proposition 2 and Theorem 9.
* A. Sudbery, *Quaternionic analysis*, Math. Proc. Cambridge Philos. Soc. 85 (1979), 199–225.
-/

public section

open Filter MeasureTheory Metric Quaternion Set TauCeti.Quaternion
open scoped ContDiff Quaternion Topology

namespace TauCeti

/-! ### Differentiating Cauchy–Fueter kernel potentials -/

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

private theorem aestronglyMeasurable_bilinear_comp_iteratedFDeriv_cauchyFueterKernel
    (B : G →L[ℝ] ℍ →L[ℝ] E) {φ : X → ℍ} {g : X → G}
    (hφ : AEStronglyMeasurable φ μ) (hg : Integrable g μ) (k : ℕ) (q : ℍ) :
    AEStronglyMeasurable
      (fun z ↦ (B (g z)).compContinuousMultilinearMap
        (iteratedFDeriv ℝ k (cauchyFueterKernel (φ z)) q)) μ := by
  have hc : Continuous (fun p : G × (ℍ [×k]→L[ℝ] ℍ) ↦
      (B p.1).compContinuousMultilinearMap p.2) :=
    isBoundedBilinearMap_compMultilinear.continuous.comp (B.continuous.prodMap continuous_id)
  exact hc.comp_aestronglyMeasurable
    (hg.aestronglyMeasurable.prodMk
      (aestronglyMeasurable_iteratedFDeriv_cauchyFueterKernel_right hφ k q))

/-- **Formal Taylor series of a bilinearly weighted Cauchy–Fueter kernel potential on an open
ball.** If `φ` stays at distance at least `δ` from `q₀` almost everywhere and `g : X → G` is
Bochner integrable, then for every radius `r < δ` and finite order `N : ℕ`, the potential
`q ↦ ∫ z, B (g z) (cauchyFueterKernel (φ z) q) ∂μ` has the integrated bilinearly composed kernel
jets as its formal Taylor series up to order `N` on `ball q₀ r`. -/
theorem hasFTaylorSeriesUpToOn_integral_bilinear_cauchyFueterKernel
    (B : G →L[ℝ] ℍ →L[ℝ] E) {φ : X → ℍ} {g : X → G} {q₀ : ℍ} {δ r : ℝ} (N : ℕ)
    (hφ : AEStronglyMeasurable φ μ) (hg : Integrable g μ)
    (hrδ : r < δ) (hδ : ∀ᵐ z ∂μ, δ ≤ ‖φ z - q₀‖) :
    HasFTaylorSeriesUpToOn N
      (fun q ↦ ∫ z, B (g z) (cauchyFueterKernel (φ z) q) ∂μ)
      (fun q k ↦ ∫ z, (B (g z)).compContinuousMultilinearMap
        (iteratedFDeriv ℝ k (cauchyFueterKernel (φ z)) q) ∂μ)
      (ball q₀ r) := by
  obtain ⟨K, hK_pos, hK⟩ := B.isBoundedBilinearMap.bound
  have hB_le (x : G) : ‖B x‖ ≤ K * ‖x‖ := (B x).opNorm_le_bound (by positivity) (hK x)
  obtain ⟨C, _, hC⟩ := exists_norm_iteratedFDeriv_cauchyFueterKernel_right_le_of_mem_closedBall N
  have hsep : ∀ᵐ z ∂μ, ∀ q ∈ ball q₀ r, φ z ≠ q := by
    filter_upwards [hδ] with z hz q hq heq
    have hq' : ‖q - q₀‖ < r := by simpa [mem_ball, dist_eq_norm] using hq
    linarith [heq ▸ hz]
  have hfn (z : X) : (fun p ↦ B (g z) (cauchyFueterKernel (φ z) p)) =
      B (g z) ∘ cauchyFueterKernel (φ z) := by
    funext p
    simp [Function.comp_apply]
  have hcomp_deriv {z : X} {q : ℍ} {k : ℕ} (hne : φ z ≠ q) (hk : k ≤ N) :
      iteratedFDeriv ℝ k (fun p ↦ B (g z) (cauchyFueterKernel (φ z) p)) q =
        (B (g z)).compContinuousMultilinearMap
          (iteratedFDeriv ℝ k (cauchyFueterKernel (φ z)) q) := by
    rw [hfn z]
    exact (B (g z)).iteratedFDeriv_comp_left
      (contDiffAt_cauchyFueterKernel_right hne (n := N)) (mod_cast hk)
  have hT := hasFTaylorSeriesUpToOn_integral_of_dominated (n := (N : ℕ∞ω))
    (f := fun z q ↦ B (g z) (cauchyFueterKernel (φ z) q))
    (bound := fun k z ↦ K * ‖g z‖ * (C / (δ - r) ^ (3 + k))) isOpen_ball
    (hsep.mono fun z hz q hq ↦ by
      rw [hfn z]
      exact (B (g z)).contDiff.contDiffOn.comp
        (fun p hp ↦ (contDiffAt_cauchyFueterKernel_right (hz p hp)).contDiffWithinAt)
        (mapsTo_univ _ _) q hq)
    (fun q hq k hk ↦ by
      have hk' : k ≤ N := by exact_mod_cast hk
      refine (aestronglyMeasurable_bilinear_comp_iteratedFDeriv_cauchyFueterKernel
        B hφ hg k q).congr ?_
      filter_upwards [hsep] with z hz
      exact (hcomp_deriv (hz q hq) hk').symm)
    (by
      filter_upwards [hδ, hsep] with z hz hzne q hq k hk
      have hk' : k ≤ N := by exact_mod_cast hk
      rw [hcomp_deriv (hzne q hq) hk']
      exact ((B (g z)).norm_compContinuousMultilinearMap_le _).trans
        ((mul_le_mul_of_nonneg_right (hB_le (g z)) (norm_nonneg _)).trans
          (mul_le_mul_of_nonneg_left
            (hC k hk' hrδ hz (ball_subset_closedBall hq)) (by positivity))))
    (fun k _ ↦ (hg.norm.const_mul K).mul_const _)
  refine hT.congr_series fun k hk q hq ↦ ?_
  have hk' : k ≤ N := by exact_mod_cast hk
  refine integral_congr_ae ?_
  filter_upwards [hsep] with z hz
  exact hcomp_deriv (hz q hq) hk'

/-- Smoothness (`C^n` for any `n : ℕ∞`) on `ball q₀ δ` of a bilinearly weighted Cauchy–Fueter
kernel potential `q ↦ ∫ z, B (g z) (cauchyFueterKernel (φ z) q) ∂μ` when `φ` stays at distance at
least `δ` from `q₀` almost everywhere. -/
theorem contDiffOn_integral_bilinear_cauchyFueterKernel_ball
    (B : G →L[ℝ] ℍ →L[ℝ] E) {φ : X → ℍ} {g : X → G} {q₀ : ℍ} {δ : ℝ} {n : ℕ∞}
    (hφ : AEStronglyMeasurable φ μ) (hg : Integrable g μ)
    (hδ : ∀ᵐ z ∂μ, δ ≤ ‖φ z - q₀‖) :
    ContDiffOn ℝ n (fun q ↦ ∫ z, B (g z) (cauchyFueterKernel (φ z) q) ∂μ) (ball q₀ δ) := by
  intro q hq
  have hlt : dist q q₀ < δ := mem_ball.mp hq
  let r : ℝ := (dist q q₀ + δ) / 2
  have hqr : q ∈ ball q₀ r := by rw [mem_ball]; dsimp [r]; linarith
  have hrδ : r < δ := by dsimp [r]; linarith
  have hcd : ContDiffOn ℝ n
      (fun p ↦ ∫ z, B (g z) (cauchyFueterKernel (φ z) p) ∂μ) (ball q₀ r) := by
    rw [contDiffOn_iff_forall_nat_le]
    intro N _
    exact (hasFTaylorSeriesUpToOn_integral_bilinear_cauchyFueterKernel
      B N hφ hg hrδ hδ).contDiffOn
  exact (hcd.contDiffAt (isOpen_ball.mem_nhds hqr)).contDiffWithinAt

/-- A bilinearly weighted Cauchy–Fueter kernel potential
`q ↦ ∫ z, B (g z) (cauchyFueterKernel (φ z) q) ∂μ` is smooth (`C^n` for any `n : ℕ∞`) at every
point `q₀` positively separated almost everywhere from `φ`. -/
theorem contDiffAt_integral_bilinear_cauchyFueterKernel
    (B : G →L[ℝ] ℍ →L[ℝ] E) {φ : X → ℍ} {g : X → G} {q₀ : ℍ} {δ : ℝ} {n : ℕ∞}
    (hφ : AEStronglyMeasurable φ μ) (hg : Integrable g μ)
    (hδ₀ : 0 < δ) (hδ : ∀ᵐ z ∂μ, δ ≤ ‖φ z - q₀‖) :
    ContDiffAt ℝ n (fun q ↦ ∫ z, B (g z) (cauchyFueterKernel (φ z) q) ∂μ) q₀ :=
  (contDiffOn_integral_bilinear_cauchyFueterKernel_ball B hφ hg hδ).contDiffAt
    (isOpen_ball.mem_nhds (mem_ball_self hδ₀))

/-- **Iterated derivatives of a bilinearly weighted Cauchy–Fueter kernel potential on a ball.**
If `φ` stays at distance at least `δ` from `q₀` almost everywhere and `g : X → G` is Bochner
integrable, then at every `q ∈ ball q₀ δ`, `iteratedFDeriv ℝ m` commutes with integration of
`B (g z) (cauchyFueterKernel (φ z) p)`. -/
theorem iteratedFDeriv_integral_bilinear_cauchyFueterKernel_of_mem_ball
    (B : G →L[ℝ] ℍ →L[ℝ] E) {φ : X → ℍ} {g : X → G} {q₀ q : ℍ} {δ : ℝ} (m : ℕ)
    (hφ : AEStronglyMeasurable φ μ) (hg : Integrable g μ)
    (hδ : ∀ᵐ z ∂μ, δ ≤ ‖φ z - q₀‖) (hq : q ∈ ball q₀ δ) :
    iteratedFDeriv ℝ m (fun p ↦ ∫ z, B (g z) (cauchyFueterKernel (φ z) p) ∂μ) q =
      ∫ z, (B (g z)).compContinuousMultilinearMap
        (iteratedFDeriv ℝ m (cauchyFueterKernel (φ z)) q) ∂μ := by
  have hlt : dist q q₀ < δ := mem_ball.mp hq
  let r : ℝ := (dist q q₀ + δ) / 2
  have hqr : q ∈ ball q₀ r := by rw [mem_ball]; dsimp [r]; linarith
  have hrδ : r < δ := by dsimp [r]; linarith
  have hT := hasFTaylorSeriesUpToOn_integral_bilinear_cauchyFueterKernel B m hφ hg hrδ hδ
  rw [← iteratedFDerivWithin_of_isOpen m isOpen_ball hqr]
  exact (hT.eq_iteratedFDerivWithin_of_uniqueDiffOn le_rfl isOpen_ball.uniqueDiffOn hqr).symm

/-- **Iterated derivatives of a bilinearly weighted Cauchy–Fueter kernel potential.** If `φ` is
positively separated from `q₀` almost everywhere and `g : X → G` is Bochner integrable,
`iteratedFDeriv ℝ m` commutes with integration of `B (g z) (cauchyFueterKernel (φ z) q)`. -/
theorem iteratedFDeriv_integral_bilinear_cauchyFueterKernel
    (B : G →L[ℝ] ℍ →L[ℝ] E) {φ : X → ℍ} {g : X → G} {q₀ : ℍ} {δ : ℝ} (m : ℕ)
    (hφ : AEStronglyMeasurable φ μ) (hg : Integrable g μ)
    (hδ₀ : 0 < δ) (hδ : ∀ᵐ z ∂μ, δ ≤ ‖φ z - q₀‖) :
    iteratedFDeriv ℝ m (fun q ↦ ∫ z, B (g z) (cauchyFueterKernel (φ z) q) ∂μ) q₀ =
      ∫ z, (B (g z)).compContinuousMultilinearMap
        (iteratedFDeriv ℝ m (cauchyFueterKernel (φ z)) q₀) ∂μ :=
  iteratedFDeriv_integral_bilinear_cauchyFueterKernel_of_mem_ball
    B m hφ hg hδ (mem_ball_self hδ₀)

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
  rw [iteratedFDeriv_integral_bilinear_cauchyFueterKernel B m hφ hg hδ₀ hδ]
  refine (norm_integral_le_of_norm_le
    (hg.norm.const_mul (K * C / δ ^ (3 + m))) ?_).trans_eq (integral_const_mul _ _)
  filter_upwards [hδ] with z hz
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
  simpa only [ContinuousLinearMap.flip_apply, ContinuousLinearMap.mul_apply'] using
    contDiffOn_integral_bilinear_cauchyFueterKernel_ball (n := n)
      (ContinuousLinearMap.mul ℝ ℍ).flip hφ hg hδ

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
  simpa only [ContinuousLinearMap.mul_apply'] using
    contDiffOn_integral_bilinear_cauchyFueterKernel_ball (n := n)
      (ContinuousLinearMap.mul ℝ ℍ) hφ hg hδ

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
  have h := iteratedFDeriv_integral_bilinear_cauchyFueterKernel_of_mem_ball
    (ContinuousLinearMap.mul ℝ ℍ).flip m hφ hg hδ hq
  simp only [ContinuousLinearMap.flip_apply, ContinuousLinearMap.mul_apply'] at h
  rw [h]
  refine integral_congr_ae (ae_of_all _ fun z ↦ ContinuousMultilinearMap.ext fun v ↦ ?_)
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
  have h := iteratedFDeriv_integral_bilinear_cauchyFueterKernel_of_mem_ball
    (ContinuousLinearMap.mul ℝ ℍ) m hφ hg hδ hq
  simp only [ContinuousLinearMap.mul_apply'] at h
  rw [h]
  refine integral_congr_ae (ae_of_all _ fun z ↦ ContinuousMultilinearMap.ext fun v ↦ ?_)
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

/-! ### Differentiated Cauchy–Fueter representations on boxes and affine parallelepipeds -/

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
    exact contDiffAt_integral_bilinear_cauchyFueterKernel B (hφ i hc) (hw i hc) hδ₀ hδ
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
    exact (contDiffAt_integral_bilinear_cauchyFueterKernel (n := m) B
      (hφ i hc) (hw i hc) hδ₀ hδ).of_le le_rfl
  simp only [boxBoundarySum_def]
  rw [iteratedFDeriv_fun_sum_apply fun i _ ↦
    (hface_cd i (Or.inr rfl)).sub (hface_cd i (Or.inl rfl))]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  obtain ⟨δb, hδb₀, hδb⟩ := hsep i (Or.inr rfl)
  obtain ⟨δa, hδa₀, hδa⟩ := hsep i (Or.inl rfl)
  rw [← Pi.sub_def,
    iteratedFDeriv_sub_apply (hface_cd i (Or.inr rfl)) (hface_cd i (Or.inl rfl)),
    iteratedFDeriv_integral_bilinear_cauchyFueterKernel B m
      (hφ i (Or.inr rfl)) (hw i (Or.inr rfl)) hδb₀ hδb,
    iteratedFDeriv_integral_bilinear_cauchyFueterKernel B m
      (hφ i (Or.inl rfl)) (hw i (Or.inl rfl)) hδa₀ hδa]

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

/-- **Differentiated left Cauchy–Fueter formula on a box.** For `f` continuous on the closed box
and left Fueter regular in its open interior, the `m`-th iterated Fréchet derivative at every
interior point `dq x₀` is `1 / (2π²)` times the boundary flux of the kernel `m`-jets multiplied on
the right by `eᵢ * f (dq x)`. -/
theorem left_cauchyFueter_iteratedFDeriv_box {a b x₀ : Fin 4 → ℝ} {f : ℍ → ℍ} (m : ℕ)
    (hc : ContinuousOn f (dq '' Icc a b))
    (hf : LeftFueterOn f (dq '' pi univ (fun i ↦ Ioo (a i) (b i))))
    (ha : ∀ i, a i < x₀ i) (hb : ∀ i, x₀ i < b i) :
    iteratedFDeriv ℝ m f (dq x₀) = (1 / (2 * Real.pi ^ 2)) • boxBoundarySum a b
      (fun i x ↦ MulOpposite.op (dq (Pi.single i 1) * f (dq x)) •
        iteratedFDeriv ℝ m (cauchyFueterKernel (dq x)) (dq x₀)) := by
  obtain ⟨δ, hδ₀, hball, hdist⟩ := exists_ball_subset_and_le_norm_box_face ha hb
  have hab : a ≤ b := fun i ↦ (ha i).le.trans (hb i).le
  have hface_int (i : Fin 4) {c : ℝ} (hc' : c = a i ∨ c = b i) :
      IntegrableOn (fun u ↦ f (dq (i.insertNth c u)))
        (Icc (a ∘ i.succAbove) (b ∘ i.succAbove)) := by
    have hcIcc : c ∈ Icc (a i) (b i) := by
      rcases hc' with rfl | rfl
      · exact ⟨le_rfl, hab i⟩
      · exact ⟨hab i, le_rfl⟩
    exact ContinuousOn.integrableOn_compact isCompact_Icc <|
      hc.comp (by fun_prop) fun u hu ↦ mem_image_of_mem _ (Fin.insertNth_mem_Icc.mpr ⟨hcIcc, hu⟩)
  have hq₀ (i : Fin 4) {c : ℝ} (hc' : c = a i ∨ c = b i)
      (u : Fin 3 → ℝ) (_ : u ∈ Icc (a ∘ i.succAbove) (b ∘ i.succAbove)) :
      dq (i.insertNth c u) ≠ dq x₀ :=
    sub_ne_zero.mp (norm_pos_iff.mp (hδ₀.trans_le (hdist i c hc' u)))
  have heq : f =ᶠ[𝓝 (dq x₀)] fun q ↦ (1 / (2 * Real.pi ^ 2)) • boxBoundarySum a b
      (fun i x ↦ cauchyFueterKernel (dq x) q * dq (Pi.single i 1) * f (dq x)) := by
    filter_upwards [ball_mem_nhds (dq x₀) hδ₀] with q hq
    obtain ⟨y, hy, rfl⟩ := hball hq
    exact left_cauchyFueter_box hc (hf.mono sdiff_subset)
      (fun i ↦ (mem_pi.mp hy i (mem_univ i)).1) (fun i ↦ (mem_pi.mp hy i (mem_univ i)).2)
  have hsum_cd :=
    (contDiffAt_boxBoundarySum_cauchyFueterKernel_left (n := m) hface_int hq₀).of_le le_rfl
  rw [(heq.iteratedFDeriv ℝ m).eq_of_nhds, iteratedFDeriv_const_smul_apply' hsum_cd,
    iteratedFDeriv_boxBoundarySum_cauchyFueterKernel_left m hface_int hq₀]

/-- **Differentiated right Cauchy–Fueter formula on a box.** For `f` continuous on the closed box
and right Fueter regular in its open interior, the `m`-th iterated Fréchet derivative at every
interior point `dq x₀` is `1 / (2π²)` times the boundary flux of `f (dq x) * eᵢ` acting on the left
of the kernel `m`-jets. -/
theorem right_cauchyFueter_iteratedFDeriv_box {a b x₀ : Fin 4 → ℝ} {f : ℍ → ℍ} (m : ℕ)
    (hc : ContinuousOn f (dq '' Icc a b))
    (hf : RightFueterOn f (dq '' pi univ (fun i ↦ Ioo (a i) (b i))))
    (ha : ∀ i, a i < x₀ i) (hb : ∀ i, x₀ i < b i) :
    iteratedFDeriv ℝ m f (dq x₀) = (1 / (2 * Real.pi ^ 2)) • boxBoundarySum a b
      (fun i x ↦ (f (dq x) * dq (Pi.single i 1)) •
        iteratedFDeriv ℝ m (cauchyFueterKernel (dq x)) (dq x₀)) := by
  obtain ⟨δ, hδ₀, hball, hdist⟩ := exists_ball_subset_and_le_norm_box_face ha hb
  have hab : a ≤ b := fun i ↦ (ha i).le.trans (hb i).le
  have hface_int (i : Fin 4) {c : ℝ} (hc' : c = a i ∨ c = b i) :
      IntegrableOn (fun u ↦ f (dq (i.insertNth c u)))
        (Icc (a ∘ i.succAbove) (b ∘ i.succAbove)) := by
    have hcIcc : c ∈ Icc (a i) (b i) := by
      rcases hc' with rfl | rfl
      · exact ⟨le_rfl, hab i⟩
      · exact ⟨hab i, le_rfl⟩
    exact ContinuousOn.integrableOn_compact isCompact_Icc <|
      hc.comp (by fun_prop) fun u hu ↦ mem_image_of_mem _ (Fin.insertNth_mem_Icc.mpr ⟨hcIcc, hu⟩)
  have hq₀ (i : Fin 4) {c : ℝ} (hc' : c = a i ∨ c = b i)
      (u : Fin 3 → ℝ) (_ : u ∈ Icc (a ∘ i.succAbove) (b ∘ i.succAbove)) :
      dq (i.insertNth c u) ≠ dq x₀ :=
    sub_ne_zero.mp (norm_pos_iff.mp (hδ₀.trans_le (hdist i c hc' u)))
  have heq : f =ᶠ[𝓝 (dq x₀)] fun q ↦ (1 / (2 * Real.pi ^ 2)) • boxBoundarySum a b
      (fun i x ↦ f (dq x) * dq (Pi.single i 1) * cauchyFueterKernel (dq x) q) := by
    filter_upwards [ball_mem_nhds (dq x₀) hδ₀] with q hq
    obtain ⟨y, hy, rfl⟩ := hball hq
    exact right_cauchyFueter_box hc (hf.mono sdiff_subset)
      (fun i ↦ (mem_pi.mp hy i (mem_univ i)).1) (fun i ↦ (mem_pi.mp hy i (mem_univ i)).2)
  have hsum_cd :=
    (contDiffAt_boxBoundarySum_cauchyFueterKernel_right (n := m) hface_int hq₀).of_le le_rfl
  rw [(heq.iteratedFDeriv ℝ m).eq_of_nhds, iteratedFDeriv_const_smul_apply' hsum_cd,
    iteratedFDeriv_boxBoundarySum_cauchyFueterKernel_right m hface_int hq₀]

/-- **Differentiated left Cauchy–Fueter formula over unit-cube affine face charts.** For `f`
continuous on the closed positively oriented affine parallelepiped
`dq '' ((fun u ↦ p + L u) '' Icc 0 1)` and left Fueter regular at every point of its open interior,
`iteratedFDeriv ℝ m f (dq x₀)` at an interior point `dq x₀` equals `1 / (2π²)` times the
front-minus-back sum of `Icc 0 1` face integrals of the kernel `m`-jets at
`dq (p + L (j.insertNth c u))` (`c = 1, 0`) multiplied on the right by
`affineFaceNormal L.toContinuousLinearMap j * f (dq (p + L (j.insertNth c u)))`. -/
theorem left_cauchyFueter_iteratedFDeriv_affine
    {L : (Fin 4 → ℝ) ≃L[ℝ] (Fin 4 → ℝ)} {p x₀ : Fin 4 → ℝ} {f : ℍ → ℍ} (m : ℕ)
    (hL : 0 < LinearMap.det (L : (Fin 4 → ℝ) →ₗ[ℝ] Fin 4 → ℝ))
    (hc : ContinuousOn f (dq '' ((fun u ↦ p + L u) '' Icc 0 1)))
    (hf : ∀ u ∈ pi univ (fun _ : Fin 4 ↦ Ioo (0 : ℝ) 1), LeftFueterAt f (dq (p + L u)))
    (hx₀ : L.symm (x₀ - p) ∈ pi univ (fun _ : Fin 4 ↦ Ioo (0 : ℝ) 1)) :
    iteratedFDeriv ℝ m f (dq x₀) = (1 / (2 * Real.pi ^ 2)) •
      ∑ j : Fin 4,
        ((∫ u in Icc (0 : Fin 3 → ℝ) 1,
            MulOpposite.op (ContinuousLinearMap.affineFaceNormal L.toContinuousLinearMap j *
                f (dq (p + L (j.insertNth 1 u)))) •
              iteratedFDeriv ℝ m (cauchyFueterKernel (dq (p + L (j.insertNth 1 u)))) (dq x₀)) -
          ∫ u in Icc (0 : Fin 3 → ℝ) 1,
            MulOpposite.op (ContinuousLinearMap.affineFaceNormal L.toContinuousLinearMap j *
                f (dq (p + L (j.insertNth 0 u)))) •
              iteratedFDeriv ℝ m (cauchyFueterKernel (dq (p + L (j.insertNth 0 u)))) (dq x₀)) := by
  obtain ⟨δ, hδ₀, hball, hdist⟩ :=
    exists_ball_subset_and_le_norm_affine_face (a := (0 : Fin 4 → ℝ)) (b := (1 : Fin 4 → ℝ)) hx₀
  let φ : (Fin 4 → ℝ) → ℍ := fun x ↦ dq (p + L x)
  let w : Fin 4 → (Fin 4 → ℝ) → ℍ := fun j x ↦
    ContinuousLinearMap.affineFaceNormal L.toContinuousLinearMap j * f (φ x)
  have hφ : ∀ (j : Fin 4) {c : ℝ}, c = (0 : Fin 4 → ℝ) j ∨ c = (1 : Fin 4 → ℝ) j →
      AEStronglyMeasurable (fun u ↦ φ (j.insertNth c u))
        (volume.restrict (Icc ((0 : Fin 4 → ℝ) ∘ j.succAbove) ((1 : Fin 4 → ℝ) ∘ j.succAbove))) :=
    fun _ _ _ ↦ (by fun_prop : Continuous fun u ↦ φ _).aestronglyMeasurable
  have hw (j : Fin 4) {c : ℝ} (hc' : c = (0 : Fin 4 → ℝ) j ∨ c = (1 : Fin 4 → ℝ) j) :
      IntegrableOn (fun u ↦ w j (j.insertNth c u))
        (Icc ((0 : Fin 4 → ℝ) ∘ j.succAbove) ((1 : Fin 4 → ℝ) ∘ j.succAbove)) := by
    have hcIcc : c ∈ Icc (0 : ℝ) 1 := by rcases hc' with rfl | rfl <;> simp
    refine ContinuousOn.integrableOn_compact isCompact_Icc (continuousOn_const.mul ?_)
    exact hc.comp (by fun_prop) fun u hu ↦
      mem_image_of_mem _ (mem_image_of_mem _ (Fin.insertNth_mem_Icc.mpr ⟨hcIcc, hu⟩))
  have hsep (j : Fin 4) {c : ℝ} (hc' : c = (0 : Fin 4 → ℝ) j ∨ c = (1 : Fin 4 → ℝ) j) :
      ∃ δ' > 0, ∀ᵐ u ∂volume.restrict
        (Icc ((0 : Fin 4 → ℝ) ∘ j.succAbove) ((1 : Fin 4 → ℝ) ∘ j.succAbove)),
        δ' ≤ ‖φ (j.insertNth c u) - dq x₀‖ :=
    ⟨δ, hδ₀, ae_of_all _ (hdist j c hc')⟩
  have heq : f =ᶠ[𝓝 (dq x₀)] fun q ↦ (1 / (2 * Real.pi ^ 2)) •
      boxBoundarySum (0 : Fin 4 → ℝ) 1
        (fun j x ↦ (ContinuousLinearMap.mul ℝ ℍ).flip (w j x)
          (cauchyFueterKernel (φ x) q)) := by
    filter_upwards [ball_mem_nhds (dq x₀) hδ₀] with q hq
    obtain ⟨y, ⟨u, hu, rfl⟩, rfl⟩ := hball hq
    have hrep := left_cauchyFueter_affine (x₀ := p + L u) hL hc (fun v hv _ ↦ hf v hv)
      (by simpa [add_sub_cancel_left] using hu)
    simpa only [ContinuousLinearMap.rawAffineBoundary_eq,
      ContinuousLinearMap.mulLeftRight_apply, ContinuousLinearEquiv.coe_coe,
      ContinuousLinearMap.flip_apply, ContinuousLinearMap.mul_apply', mul_assoc,
      boxBoundarySum_zero_one, φ, w] using hrep
  have hsum_cd := (contDiffAt_boxBoundarySum_bilinear_cauchyFueterKernel (n := m)
    (ContinuousLinearMap.mul ℝ ℍ).flip hφ hw hsep).of_le le_rfl
  rw [(heq.iteratedFDeriv ℝ m).eq_of_nhds, iteratedFDeriv_const_smul_apply' hsum_cd,
    iteratedFDeriv_boxBoundarySum_bilinear_cauchyFueterKernel
      (ContinuousLinearMap.mul ℝ ℍ).flip m hφ hw hsep,
    boxBoundarySum_zero_one]
  refine congrArg _ (Finset.sum_congr rfl fun j _ ↦ congrArg₂ (· - ·) ?_ ?_)
  all_goals
    refine integral_congr_ae (ae_of_all _ fun u ↦ ContinuousMultilinearMap.ext fun v ↦ ?_)
    simp [ContinuousLinearMap.compContinuousMultilinearMap_coe, MulOpposite.smul_eq_mul_unop,
      φ, w]

/-- **Differentiated right Cauchy–Fueter formula over unit-cube affine face charts.** For `f`
continuous on the closed positively oriented affine parallelepiped
`dq '' ((fun u ↦ p + L u) '' Icc 0 1)` and right Fueter regular at every point of its open interior,
`iteratedFDeriv ℝ m f (dq x₀)` at an interior point `dq x₀` equals `1 / (2π²)` times the
front-minus-back sum of `Icc 0 1` face integrals with
`f (dq (p + L (j.insertNth c u))) * affineFaceNormal L.toContinuousLinearMap j` (`c = 1, 0`)
acting on the left of the kernel `m`-jet. -/
theorem right_cauchyFueter_iteratedFDeriv_affine
    {L : (Fin 4 → ℝ) ≃L[ℝ] (Fin 4 → ℝ)} {p x₀ : Fin 4 → ℝ} {f : ℍ → ℍ} (m : ℕ)
    (hL : 0 < LinearMap.det (L : (Fin 4 → ℝ) →ₗ[ℝ] Fin 4 → ℝ))
    (hc : ContinuousOn f (dq '' ((fun u ↦ p + L u) '' Icc 0 1)))
    (hf : ∀ u ∈ pi univ (fun _ : Fin 4 ↦ Ioo (0 : ℝ) 1), RightFueterAt f (dq (p + L u)))
    (hx₀ : L.symm (x₀ - p) ∈ pi univ (fun _ : Fin 4 ↦ Ioo (0 : ℝ) 1)) :
    iteratedFDeriv ℝ m f (dq x₀) = (1 / (2 * Real.pi ^ 2)) •
      ∑ j : Fin 4,
        ((∫ u in Icc (0 : Fin 3 → ℝ) 1,
            (f (dq (p + L (j.insertNth 1 u))) *
                ContinuousLinearMap.affineFaceNormal L.toContinuousLinearMap j) •
              iteratedFDeriv ℝ m (cauchyFueterKernel (dq (p + L (j.insertNth 1 u)))) (dq x₀)) -
          ∫ u in Icc (0 : Fin 3 → ℝ) 1,
            (f (dq (p + L (j.insertNth 0 u))) *
                ContinuousLinearMap.affineFaceNormal L.toContinuousLinearMap j) •
              iteratedFDeriv ℝ m (cauchyFueterKernel (dq (p + L (j.insertNth 0 u)))) (dq x₀)) := by
  obtain ⟨δ, hδ₀, hball, hdist⟩ :=
    exists_ball_subset_and_le_norm_affine_face (a := (0 : Fin 4 → ℝ)) (b := (1 : Fin 4 → ℝ)) hx₀
  let φ : (Fin 4 → ℝ) → ℍ := fun x ↦ dq (p + L x)
  let w : Fin 4 → (Fin 4 → ℝ) → ℍ := fun j x ↦
    f (φ x) * ContinuousLinearMap.affineFaceNormal L.toContinuousLinearMap j
  have hφ : ∀ (j : Fin 4) {c : ℝ}, c = (0 : Fin 4 → ℝ) j ∨ c = (1 : Fin 4 → ℝ) j →
      AEStronglyMeasurable (fun u ↦ φ (j.insertNth c u))
        (volume.restrict (Icc ((0 : Fin 4 → ℝ) ∘ j.succAbove) ((1 : Fin 4 → ℝ) ∘ j.succAbove))) :=
    fun _ _ _ ↦ (by fun_prop : Continuous fun u ↦ φ _).aestronglyMeasurable
  have hw (j : Fin 4) {c : ℝ} (hc' : c = (0 : Fin 4 → ℝ) j ∨ c = (1 : Fin 4 → ℝ) j) :
      IntegrableOn (fun u ↦ w j (j.insertNth c u))
        (Icc ((0 : Fin 4 → ℝ) ∘ j.succAbove) ((1 : Fin 4 → ℝ) ∘ j.succAbove)) := by
    have hcIcc : c ∈ Icc (0 : ℝ) 1 := by rcases hc' with rfl | rfl <;> simp
    refine ContinuousOn.integrableOn_compact isCompact_Icc (ContinuousOn.mul ?_ continuousOn_const)
    exact hc.comp (by fun_prop) fun u hu ↦
      mem_image_of_mem _ (mem_image_of_mem _ (Fin.insertNth_mem_Icc.mpr ⟨hcIcc, hu⟩))
  have hsep (j : Fin 4) {c : ℝ} (hc' : c = (0 : Fin 4 → ℝ) j ∨ c = (1 : Fin 4 → ℝ) j) :
      ∃ δ' > 0, ∀ᵐ u ∂volume.restrict
        (Icc ((0 : Fin 4 → ℝ) ∘ j.succAbove) ((1 : Fin 4 → ℝ) ∘ j.succAbove)),
        δ' ≤ ‖φ (j.insertNth c u) - dq x₀‖ :=
    ⟨δ, hδ₀, ae_of_all _ (hdist j c hc')⟩
  have heq : f =ᶠ[𝓝 (dq x₀)] fun q ↦ (1 / (2 * Real.pi ^ 2)) •
      boxBoundarySum (0 : Fin 4 → ℝ) 1
        (fun j x ↦ ContinuousLinearMap.mul ℝ ℍ (w j x)
          (cauchyFueterKernel (φ x) q)) := by
    filter_upwards [ball_mem_nhds (dq x₀) hδ₀] with q hq
    obtain ⟨y, ⟨u, hu, rfl⟩, rfl⟩ := hball hq
    have hrep := right_cauchyFueter_affine (x₀ := p + L u) hL hc (fun v hv _ ↦ hf v hv)
      (by simpa [add_sub_cancel_left] using hu)
    simpa only [ContinuousLinearMap.rawAffineBoundary_eq,
      ContinuousLinearMap.mulLeftRight_apply, ContinuousLinearEquiv.coe_coe,
      ContinuousLinearMap.mul_apply', boxBoundarySum_zero_one, φ, w] using hrep
  have hsum_cd := (contDiffAt_boxBoundarySum_bilinear_cauchyFueterKernel (n := m)
    (ContinuousLinearMap.mul ℝ ℍ) hφ hw hsep).of_le le_rfl
  rw [(heq.iteratedFDeriv ℝ m).eq_of_nhds, iteratedFDeriv_const_smul_apply' hsum_cd,
    iteratedFDeriv_boxBoundarySum_bilinear_cauchyFueterKernel
      (ContinuousLinearMap.mul ℝ ℍ) m hφ hw hsep,
    boxBoundarySum_zero_one]
  refine congrArg _ (Finset.sum_congr rfl fun j _ ↦ congrArg₂ (· - ·) ?_ ?_)
  all_goals
    refine integral_congr_ae (ae_of_all _ fun u ↦ ContinuousMultilinearMap.ext fun v ↦ ?_)
    simp [ContinuousLinearMap.compContinuousMultilinearMap_coe, smul_eq_mul, φ, w]

end BoundaryRepresentations

/-! ### Universal Cauchy-type derivative estimates -/

section UniversalEstimates

/-- Norm estimate on a single three-dimensional face of the cube of side `R` centred at `x₀`, given
a potential-decay constant `K` from `exists_norm_iteratedFDeriv_integral_cauchyFueterKernel_mul_le`.
Each face lies at distance at least `R / 2` from `dq x₀` and has volume `R³`. -/
private theorem norm_cube_face_iteratedFDeriv_cauchyFueterKernel_left_le
    {x₀ : Fin 4 → ℝ} {R M K : ℝ} {f : ℍ → ℍ} (m : ℕ) (hR : 0 < R) (hK : 0 ≤ K)
    (hKbound : ∀ {μ : Measure (Fin 3 → ℝ)} {φ g : (Fin 3 → ℝ) → ℍ} {q₀ : ℍ} {δ : ℝ},
      AEStronglyMeasurable φ μ → Integrable g μ → 0 < δ → (∀ᵐ z ∂μ, δ ≤ ‖φ z - q₀‖) →
      ‖iteratedFDeriv ℝ m (fun q ↦ ∫ z, cauchyFueterKernel (φ z) q * g z ∂μ) q₀‖ ≤
        K / δ ^ (3 + m) * ∫ z, ‖g z‖ ∂μ)
    (hc : ContinuousOn f (dq '' Icc (fun j ↦ x₀ j - R / 2) (fun j ↦ x₀ j + R / 2)))
    (hM : ∀ q ∈ dq '' Icc (fun j ↦ x₀ j - R / 2) (fun j ↦ x₀ j + R / 2), ‖f q‖ ≤ M)
    (i : Fin 4) {c : ℝ} (hc' : c = x₀ i - R / 2 ∨ c = x₀ i + R / 2) :
    ‖∫ u in Icc ((fun j ↦ x₀ j - R / 2) ∘ i.succAbove) ((fun j ↦ x₀ j + R / 2) ∘ i.succAbove),
        MulOpposite.op (dq (Pi.single i 1) * f (dq (i.insertNth c u))) •
          iteratedFDeriv ℝ m (cauchyFueterKernel (dq (i.insertNth c u))) (dq x₀)‖ ≤
      K / (R / 2) ^ (3 + m) * (R ^ 3 * M) := by
  let a : Fin 4 → ℝ := fun j ↦ x₀ j - R / 2
  let b : Fin 4 → ℝ := fun j ↦ x₀ j + R / 2
  have hab : a ≤ b := fun j ↦ by dsimp [a, b]; linarith [half_pos hR]
  have hcIcc : c ∈ Icc (a i) (b i) := by
    rcases hc' with rfl | rfl
    · exact ⟨le_rfl, hab i⟩
    · exact ⟨hab i, le_rfl⟩
  set F := Icc (a ∘ i.succAbove) (b ∘ i.succAbove)
  have hg_int : IntegrableOn (fun u ↦ dq (Pi.single i 1) * f (dq (i.insertNth c u))) F :=
    ContinuousOn.integrableOn_compact isCompact_Icc <| continuousOn_const.mul
      (hc.comp (by fun_prop) fun u hu ↦
        mem_image_of_mem _ (Fin.insertNth_mem_Icc.mpr ⟨hcIcc, hu⟩))
  have hsep (u : Fin 3 → ℝ) : R / 2 ≤ ‖dq (i.insertNth c u) - dq x₀‖ := by
    rw [← map_sub, norm_dq]
    have hle := PiLp.norm_apply_le (WithLp.toLp 2 (i.insertNth c u - x₀)) i
    have hval : |c - x₀ i| = R / 2 := by
      rcases hc' with rfl | rfl
      · simp [abs_of_neg (neg_lt_zero.mpr (half_pos hR))]
      · simp [abs_of_pos (half_pos hR)]
    simpa [Pi.sub_apply, Fin.insertNth_apply_same, hval] using hle
  have hpot := hKbound (μ := volume.restrict F)
    (by fun_prop : Continuous fun u ↦ dq (i.insertNth c u)).aestronglyMeasurable
    hg_int (half_pos hR) (ae_of_all _ hsep)
  rw [iteratedFDeriv_integral_cauchyFueterKernel_mul m
    (by fun_prop : Continuous fun u ↦ dq (i.insertNth c u)).aestronglyMeasurable
    hg_int (half_pos hR) (ae_of_all _ hsep)] at hpot
  refine hpot.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
  have hunit : ‖dq (Pi.single i 1)‖ = 1 := by
    rw [← mul_self_inj (norm_nonneg _) zero_le_one, mul_one, ← normSq_eq_norm_mul_self]
    fin_cases i <;> simp [normSq_def', dq_apply]
  have hlen (r : Fin 3) : b (i.succAbove r) - a (i.succAbove r) = R := by
    dsimp [a, b]; ring
  calc ∫ u in F, ‖dq (Pi.single i 1) * f (dq (i.insertNth c u))‖
      ≤ ∫ _ in F, M := setIntegral_mono_on hg_int.norm
        (integrableOn_const isCompact_Icc.measure_ne_top) measurableSet_Icc fun u hu ↦ by
          rw [norm_mul, hunit, one_mul]
          exact hM _ (mem_image_of_mem _ (Fin.insertNth_mem_Icc.mpr ⟨hcIcc, hu⟩))
    _ = R ^ 3 * M := by
        rw [setIntegral_const, smul_eq_mul, Measure.real]
        dsimp only [F]
        rw [Real.volume_Icc_pi_toReal (a := a ∘ i.succAbove) (b := b ∘ i.succAbove)
          fun r ↦ hab (i.succAbove r)]
        simp [Function.comp_apply, hlen, pow_three]

/-- **Universal Cauchy-type derivative estimate for left Fueter regular functions.** For every
order `m` there is a constant `C > 0`, depending on `m` alone, such that whenever `f` is left
Fueter regular on a set `Ω` containing `closedBall q₀ R` (`R > 0`) and `‖f q‖ ≤ M` on that closed
ball, `‖iteratedFDeriv ℝ m f q₀‖ ≤ C * R⁻¹ ^ m * M`. -/
theorem leftFueter_iteratedFDeriv_bound (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (f : ℍ → ℍ) (Ω : Set ℍ), LeftFueterOn f Ω →
      ∀ (q₀ : ℍ) (R : ℝ), 0 < R → closedBall q₀ R ⊆ Ω →
      ∀ M : ℝ, (∀ q ∈ closedBall q₀ R, ‖f q‖ ≤ M) →
      ‖iteratedFDeriv ℝ m f q₀‖ ≤ C * R⁻¹ ^ m * M := by
  obtain ⟨K, hK, hKbound⟩ :=
    exists_norm_iteratedFDeriv_integral_cauchyFueterKernel_mul_le.{0} m
  -- Eight faces, each of separation `R / 2` and volume `R³`, normalized by `1 / (2π²)`.
  refine ⟨8 * 2 ^ (3 + m) * K / (2 * Real.pi ^ 2), by positivity,
    fun f Ω hf q₀ R hR hΩ M hM ↦ ?_⟩
  let x₀ : Fin 4 → ℝ := dqEquiv.symm q₀
  have hx₀ : dq x₀ = q₀ := dq_dqEquiv_symm q₀
  let a : Fin 4 → ℝ := fun i ↦ x₀ i - R / 2
  let b : Fin 4 → ℝ := fun i ↦ x₀ i + R / 2
  have ha (i : Fin 4) : a i < x₀ i := by dsimp [a]; linarith [half_pos hR]
  have hb (i : Fin 4) : x₀ i < b i := by dsimp [b]; linarith [half_pos hR]
  have hcube : dq '' Icc a b ⊆ closedBall q₀ R := hx₀ ▸ closedCube_subset_closedBall x₀ hR.le
  have hc : ContinuousOn f (dq '' Icc a b) :=
    hf.differentiableOn.continuousOn.mono (hcube.trans hΩ)
  have hIoo : pi univ (fun i ↦ Ioo (a i) (b i)) ⊆ Icc a b := fun _ hx ↦
    ⟨fun i ↦ (hx i (mem_univ i)).1.le, fun i ↦ (hx i (mem_univ i)).2.le⟩
  have hf_open : LeftFueterOn f (dq '' pi univ (fun i ↦ Ioo (a i) (b i))) :=
    hf.mono ((image_mono hIoo).trans (hcube.trans hΩ))
  rw [← hx₀, left_cauchyFueter_iteratedFDeriv_box m hc hf_open ha hb,
    norm_smul, Real.norm_of_nonneg (by positivity), boxBoundarySum_def]
  have hface (i : Fin 4) {c : ℝ} (hc' : c = a i ∨ c = b i) :=
    norm_cube_face_iteratedFDeriv_cauchyFueterKernel_left_le m hR hK.le
      (hKbound m le_rfl (X := Fin 3 → ℝ)) hc (fun q hq ↦ hM q (hcube hq)) i hc'
  have hsum : ‖∑ i : Fin 4,
      ((∫ u in Icc (a ∘ i.succAbove) (b ∘ i.succAbove),
          MulOpposite.op (dq (Pi.single i 1) * f (dq (i.insertNth (b i) u))) •
            iteratedFDeriv ℝ m (cauchyFueterKernel (dq (i.insertNth (b i) u))) (dq x₀)) -
        ∫ u in Icc (a ∘ i.succAbove) (b ∘ i.succAbove),
          MulOpposite.op (dq (Pi.single i 1) * f (dq (i.insertNth (a i) u))) •
            iteratedFDeriv ℝ m (cauchyFueterKernel (dq (i.insertNth (a i) u))) (dq x₀))‖ ≤
      8 * (K / (R / 2) ^ (3 + m) * (R ^ 3 * M)) := by
    refine (norm_sum_le _ _).trans
      ((Finset.sum_le_sum (g := fun _ ↦ 2 * (K / (R / 2) ^ (3 + m) * (R ^ 3 * M)))
        fun i _ ↦ (norm_sub_le _ _).trans ?_).trans_eq ?_)
    · linarith [hface i (Or.inr rfl), hface i (Or.inl rfl)]
    · simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring
  refine (mul_le_mul_of_nonneg_left hsum (by positivity)).trans_eq ?_
  have hpi : (2 * Real.pi ^ 2 : ℝ) ≠ 0 := by positivity
  have hR₀ : R ≠ 0 := hR.ne'
  rw [div_pow, pow_add R 3 m, inv_pow]
  field_simp [hpi, hR₀]

/-- **Universal Cauchy-type derivative estimate for right Fueter regular functions.** For every
order `m` there is a constant `C > 0`, depending on `m` alone, such that whenever `f` is right
Fueter regular on a set `Ω` containing `closedBall q₀ R` (`R > 0`) and `‖f q‖ ≤ M` on that closed
ball, `‖iteratedFDeriv ℝ m f q₀‖ ≤ C * R⁻¹ ^ m * M`. -/
theorem rightFueter_iteratedFDeriv_bound (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (f : ℍ → ℍ) (Ω : Set ℍ), RightFueterOn f Ω →
      ∀ (q₀ : ℍ) (R : ℝ), 0 < R → closedBall q₀ R ⊆ Ω →
      ∀ M : ℝ, (∀ q ∈ closedBall q₀ R, ‖f q‖ ≤ M) →
      ‖iteratedFDeriv ℝ m f q₀‖ ≤ C * R⁻¹ ^ m * M := by
  obtain ⟨C, hC, hleft⟩ := leftFueter_iteratedFDeriv_bound m
  refine ⟨C, hC, fun f Ω hf q₀ R hR hΩ M hM ↦ ?_⟩
  have hmem {p : ℍ} (hp : p ∈ closedBall (star q₀) R) : star p ∈ closedBall q₀ R := by
    rw [mem_closedBall, dist_eq_norm, ← Quaternion.norm_star, star_sub, star_star]
    simpa [mem_closedBall, dist_eq_norm] using hp
  have hball : closedBall (star q₀) R ⊆ star '' Ω :=
    fun p hp ↦ ⟨star p, hΩ (hmem hp), star_star p⟩
  have hbound := hleft (fun q ↦ star (f (star q))) (star '' Ω)
    hf.star_star (star q₀) R hR hball M
    (fun p hp ↦ by simpa [Quaternion.norm_star] using hM (star p) (hmem hp))
  simpa only [norm_iteratedFDeriv_star_star, star_star] using hbound

end UniversalEstimates

end TauCeti
