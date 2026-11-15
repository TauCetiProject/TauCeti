/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Normed.Module.Multilinear.Basic
public import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import TauCeti.Analysis.Calculus.IteratedFDeriv.CompContinuousLinearEquiv

/-!
# Smoothness and Taylor series of separated translation-kernel integrals

Let `(α, μ)` be an arbitrary measure space, `W` a real normed space, and `K : W → F` a kernel that
is `C^∞` away from `0` and has every iterated derivative bounded outside each ball around `0`. Given
an `AEStronglyMeasurable` map `φ : α → W` separated almost everywhere from `q₀` by `δ > 0`, an
integrable weight `w : α → G`, and a continuous bilinear pairing `B : F →L[ℝ] G →L[ℝ] E` into a
real normed space `E` (with no completeness assumption on `E` and no topological or compactness
assumption on `α`), the separated integral

`y ↦ ∫ z, B (K (φ z - y)) (w z) ∂μ`

admits the integrated spatial jets as an infinite Taylor series on `Metric.ball q₀ δ`
(`TauCeti.hasFTaylorSeriesUpToOn_integral_bilin_kernel_sub`). In particular it is `C^∞` on
`Metric.ball q₀ δ` (`TauCeti.contDiffOn_integral_bilin_kernel_sub`), and every iterated Fréchet
derivative commutes with the Bochner integral (`TauCeti.iteratedFDeriv_integral_bilin_kernel_sub`),
with integrand given and bounded pointwise by `TauCeti.iteratedFDeriv_bilin_kernel_sub` and
`TauCeti.norm_iteratedFDeriv_bilin_kernel_sub_le`.

To verify strong measurability of the spatial jets without assuming finite dimensionality or
second countability of `W` or `F`, we multiply `D^k K` by a continuous radial ramp vanishing inside
`Metric.ball 0 (ρ / 2)` and equal to `1` outside `Metric.ball 0 ρ`, making the cut-off jet globally
continuous on `W` while leaving it unchanged almost everywhere on the separated integration domain.
-/

public section

open Filter MeasureTheory Metric Set Topology
open scoped ContDiff

namespace TauCeti

section SeparatedKernelIntegral

variable {α W F G E : Type*} [MeasurableSpace α] {μ : Measure α}
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Away from the pole `z`, the `k`-th iterated Fréchet derivative of `p ↦ B (K (z - p)) c` is
`(-1) ^ k • iteratedFDeriv ℝ k K (z - y)` postcomposed with `B.flip c`. -/
theorem iteratedFDeriv_bilin_kernel_sub
    (B : F →L[ℝ] G →L[ℝ] E) {K : W → F} (hK : ∀ x ≠ (0 : W), ContDiffAt ℝ ∞ K x)
    {z y : W} (hne : z ≠ y) (c : G) (k : ℕ) :
    iteratedFDeriv ℝ k (fun p ↦ B (K (z - p)) c) y =
      (B.flip c).compContinuousMultilinearMap
        ((-1 : ℝ) ^ k • iteratedFDeriv ℝ k K (z - y)) := by
  have hsub_ne : z - y ≠ 0 := sub_ne_zero.2 hne
  have hcd : ContDiffAt ℝ ∞ (fun p ↦ K (z - p)) y :=
    (hK (z - y) hsub_ne).comp y (contDiffAt_const.sub contDiffAt_id)
  have hcomp : (fun p ↦ B (K (z - p)) c) = B.flip c ∘ fun p ↦ K (z - p) := rfl
  have htrans : (fun p ↦ K (z - p)) = fun p ↦ K (z + (-1 : ℝ) • p) := by
    funext p
    simp [sub_eq_add_neg]
  rw [hcomp, (B.flip c).iteratedFDeriv_comp_left hcd (WithTop.coe_le_coe.2 le_top), htrans,
    iteratedFDeriv_comp_const_smul_apply (fun p ↦ K (z + p)),
    iteratedFDeriv_comp_add_left]
  simp [sub_eq_add_neg]

/-- Operator-norm bound for the `k`-th iterated Fréchet derivative of `p ↦ B (K (z - p)) c` away
from the pole `z`. -/
theorem norm_iteratedFDeriv_bilin_kernel_sub_le
    (B : F →L[ℝ] G →L[ℝ] E) {K : W → F} (hK : ∀ x ≠ (0 : W), ContDiffAt ℝ ∞ K x)
    {z y : W} (hne : z ≠ y) (c : G) (k : ℕ) :
    ‖iteratedFDeriv ℝ k (fun p ↦ B (K (z - p)) c) y‖ ≤
      ‖B‖ * ‖iteratedFDeriv ℝ k K (z - y)‖ * ‖c‖ := by
  rw [iteratedFDeriv_bilin_kernel_sub B hK hne c k]
  have hflip : ‖B.flip c‖ ≤ ‖B‖ * ‖c‖ :=
    ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (norm_nonneg B) (norm_nonneg c)) fun u ↦ by
      rw [ContinuousLinearMap.flip_apply]
      exact (B.le_opNorm₂ u c).trans_eq (by ring)
  calc ‖(B.flip c).compContinuousMultilinearMap ((-1 : ℝ) ^ k • iteratedFDeriv ℝ k K (z - y))‖
      ≤ ‖B.flip c‖ * ‖(-1 : ℝ) ^ k • iteratedFDeriv ℝ k K (z - y)‖ :=
        (B.flip c).norm_compContinuousMultilinearMap_le _
    _ ≤ (‖B‖ * ‖c‖) * ‖(-1 : ℝ) ^ k • iteratedFDeriv ℝ k K (z - y)‖ :=
        mul_le_mul_of_nonneg_right hflip (norm_nonneg _)
    _ = ‖B‖ * ‖iteratedFDeriv ℝ k K (z - y)‖ * ‖c‖ := by
        rw [norm_smul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
        ring

/-- Strong measurability of the `k`-th spatial jet of `p ↦ B (K (φ z - p)) (w z)` at `y ∈ ball q₀ δ`
using a continuous radial ramp to excise the pole `0`. -/
private theorem aestronglyMeasurable_iteratedFDeriv_bilin_kernel_sub
    (B : F →L[ℝ] G →L[ℝ] E) {K : W → F} (hK : ∀ x ≠ (0 : W), ContDiffAt ℝ ∞ K x)
    {φ : α → W} (hφ : AEStronglyMeasurable φ μ)
    {w : α → G} (hw : AEStronglyMeasurable w μ)
    {q₀ : W} {δ : ℝ} (hδ : ∀ᵐ z ∂μ, δ ≤ ‖φ z - q₀‖)
    (k : ℕ) {y : W} (hy : y ∈ ball q₀ δ) :
    AEStronglyMeasurable
      (fun z ↦ iteratedFDeriv ℝ k (fun p ↦ B (K (φ z - p)) (w z)) y) μ := by
  have hy_lt : ‖y - q₀‖ < δ := by simpa [mem_ball, dist_eq_norm] using hy
  set ρ := δ - ‖y - q₀‖
  have hρ : 0 < ρ := sub_pos.2 hy_lt
  let χ : W → ℝ := fun x ↦ max 0 (min 1 (2 * (‖x‖ / ρ) - 1))
  have hχ_cont : Continuous χ :=
    continuous_const.max (continuous_const.min
      ((continuous_const.mul (continuous_norm.div_const ρ)).sub continuous_const))
  let g : W → W [×k]→L[ℝ] F := fun x ↦ χ x • iteratedFDeriv ℝ k K x
  have hg : Continuous g := by
    rw [continuous_iff_continuousAt]
    intro x
    by_cases hx : x = 0
    · subst hx
      refine (continuousAt_const (y := (0 : W [×k]→L[ℝ] F))).congr ?_
      filter_upwards [ball_mem_nhds (0 : W) (half_pos hρ)] with u hu
      have hu' : ‖u‖ < ρ / 2 := by simpa [mem_ball, dist_eq_norm] using hu
      have hle : 2 * (‖u‖ / ρ) - 1 ≤ 0 := by
        have hdiv : ‖u‖ / ρ < 1 / 2 := by
          rw [div_lt_iff₀ hρ]
          linarith
        linarith
      have hχ0 : χ u = 0 := max_eq_left (min_le_of_right_le hle)
      simp [g, hχ0]
    · exact hχ_cont.continuousAt.smul
        ((hK x hx).continuousAt_iteratedFDeriv (WithTop.coe_le_coe.2 le_top))
  have hjet_meas : AEStronglyMeasurable (fun z ↦ (-1 : ℝ) ^ k • g (φ z - y)) μ :=
    (hg.comp_aestronglyMeasurable ((continuous_sub_right y).comp_aestronglyMeasurable
      hφ)).const_smul ((-1 : ℝ) ^ k)
  let L := (ContinuousLinearMap.compContinuousMultilinearMapL ℝ
    (fun _ : Fin k ↦ W) F E).comp B.flip
  refine (L.aestronglyMeasurable_comp₂ hw hjet_meas).congr ?_
  filter_upwards [hδ] with z hz
  have hsep : ρ ≤ ‖φ z - y‖ := by
    have htri := norm_sub_le (φ z - y) (q₀ - y)
    rw [sub_sub_sub_cancel_right, norm_sub_rev q₀ y] at htri
    linarith
  have hne : φ z ≠ y := by
    intro heq
    rw [heq, sub_self, norm_zero] at hsep
    linarith
  have hχ1 : χ (φ z - y) = 1 := by
    have h1 : 1 ≤ 2 * (‖φ z - y‖ / ρ) - 1 := by
      have hdiv : 1 ≤ ‖φ z - y‖ / ρ := (one_le_div hρ).2 hsep
      linarith
    simp only [χ, min_eq_left h1, max_eq_right zero_le_one]
  rw [iteratedFDeriv_bilin_kernel_sub B hK hne (w z) k]
  ext v
  simp [L, g, hχ1]

/-- Integrability of the `k`-th spatial jet at any point `y ∈ ball q₀ δ`. -/
private theorem integrable_iteratedFDeriv_bilin_kernel_sub
    (B : F →L[ℝ] G →L[ℝ] E) {K : W → F} (hK : ∀ x ≠ (0 : W), ContDiffAt ℝ ∞ K x)
    (hK_bd : ∀ (k : ℕ) {ρ : ℝ}, 0 < ρ → ∃ C : ℝ, ∀ x : W, ρ ≤ ‖x‖ → ‖iteratedFDeriv ℝ k K x‖ ≤ C)
    {φ : α → W} (hφ : AEStronglyMeasurable φ μ)
    {w : α → G} (hw : Integrable w μ)
    {q₀ : W} {δ : ℝ} (hδ : ∀ᵐ z ∂μ, δ ≤ ‖φ z - q₀‖)
    (k : ℕ) {y : W} (hy : y ∈ ball q₀ δ) :
    Integrable (fun z ↦ iteratedFDeriv ℝ k (fun p ↦ B (K (φ z - p)) (w z)) y) μ := by
  have hy_lt : ‖y - q₀‖ < δ := by simpa [mem_ball, dist_eq_norm] using hy
  obtain ⟨C, hC⟩ := hK_bd k (sub_pos.2 hy_lt)
  refine (hw.norm.const_mul (‖B‖ * C)).mono'
    (aestronglyMeasurable_iteratedFDeriv_bilin_kernel_sub B hK hφ hw.aestronglyMeasurable hδ k hy)
    ?_
  filter_upwards [hδ] with z hz
  have hsep : δ - ‖y - q₀‖ ≤ ‖φ z - y‖ := by
    have htri := norm_sub_le (φ z - y) (q₀ - y)
    rw [sub_sub_sub_cancel_right, norm_sub_rev q₀ y] at htri
    linarith
  have hne : φ z ≠ y := by
    intro heq
    rw [heq, sub_self, norm_zero] at hsep
    linarith
  exact (norm_iteratedFDeriv_bilin_kernel_sub_le B hK hne (w z) k).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hC _ hsep) (norm_nonneg B))
      (norm_nonneg (w z)))

/-- Pointwise Fréchet derivative of the `m`-th spatial jet away from the pole `z`. -/
private theorem hasFDerivAt_iteratedFDeriv_bilin_kernel_sub
    (B : F →L[ℝ] G →L[ℝ] E) {K : W → F} (hK : ∀ x ≠ (0 : W), ContDiffAt ℝ ∞ K x)
    {z y : W} (hne : z ≠ y) (c : G) (m : ℕ) :
    HasFDerivAt
      (fun x ↦ iteratedFDeriv ℝ m (fun p ↦ B (K (z - p)) c) x)
      ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (m + 1) ↦ W) E).toContinuousLinearEquiv
        (iteratedFDeriv ℝ (m + 1) (fun p ↦ B (K (z - p)) c) y)) y := by
  have hcont : ContDiffAt ℝ ∞ (fun p ↦ B (K (z - p)) c) y :=
    (B.flip c).contDiff.contDiffAt.comp y
      ((hK (z - y) (sub_ne_zero.2 hne)).comp y (contDiffAt_const.sub contDiffAt_id))
  have hd := (hcont.differentiableAt_iteratedFDeriv
    (ENat.natCast_lt_of_coe_top_le_withTop le_rfl m)).hasFDerivAt
  rwa [fderiv_iteratedFDeriv, Function.comp_apply] at hd

/-- Differentiating the `m`-th integrated spatial jet on `ball q₀ δ` produces the left-curried
`(m + 1)`-st integrated spatial jet. -/
private theorem hasFDerivAt_integral_iteratedFDeriv_bilin_kernel_sub
    (B : F →L[ℝ] G →L[ℝ] E) {K : W → F} (hK : ∀ x ≠ (0 : W), ContDiffAt ℝ ∞ K x)
    (hK_bd : ∀ (k : ℕ) {ρ : ℝ}, 0 < ρ → ∃ C : ℝ, ∀ x : W, ρ ≤ ‖x‖ → ‖iteratedFDeriv ℝ k K x‖ ≤ C)
    {φ : α → W} (hφ : AEStronglyMeasurable φ μ)
    {w : α → G} (hw : Integrable w μ)
    {q₀ : W} {δ : ℝ} (hδ : ∀ᵐ z ∂μ, δ ≤ ‖φ z - q₀‖)
    (m : ℕ) {q : W} (hq : q ∈ ball q₀ δ) :
    HasFDerivAt
      (fun y ↦ ∫ z, iteratedFDeriv ℝ m (fun p ↦ B (K (φ z - p)) (w z)) y ∂μ)
      (∫ z, iteratedFDeriv ℝ (m + 1)
        (fun p ↦ B (K (φ z - p)) (w z)) q ∂μ).curryLeft q := by
  have hq_lt : ‖q - q₀‖ < δ := by simpa [mem_ball, dist_eq_norm] using hq
  set r := (‖q - q₀‖ + δ) / 2
  have hqr : ‖q - q₀‖ < r := by dsimp [r]; linarith
  have hrδ : r < δ := by dsimp [r]; linarith
  let C_equiv := (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (m + 1) ↦ W)
    E).toContinuousLinearEquiv
  obtain ⟨C, hC⟩ := hK_bd (m + 1) (sub_pos.2 hrδ)
  have hF_meas : ∀ᶠ y in 𝓝 q, AEStronglyMeasurable
      (fun z ↦ iteratedFDeriv ℝ m (fun p ↦ B (K (φ z - p)) (w z)) y) μ := by
    filter_upwards [isOpen_ball.mem_nhds hq] with y hy
    exact aestronglyMeasurable_iteratedFDeriv_bilin_kernel_sub
      B hK hφ hw.aestronglyMeasurable hδ m hy
  have hF_int : Integrable
      (fun z ↦ iteratedFDeriv ℝ m (fun p ↦ B (K (φ z - p)) (w z)) q) μ :=
    integrable_iteratedFDeriv_bilin_kernel_sub B hK hK_bd hφ hw hδ m hq
  have hF'_meas : AEStronglyMeasurable (fun z ↦ C_equiv (iteratedFDeriv ℝ (m + 1)
      (fun p ↦ B (K (φ z - p)) (w z)) q)) μ :=
    C_equiv.continuous.comp_aestronglyMeasurable
      (aestronglyMeasurable_iteratedFDeriv_bilin_kernel_sub
        B hK hφ hw.aestronglyMeasurable hδ (m + 1) hq)
  have h_bound : ∀ᵐ z ∂μ, ∀ y ∈ ball q₀ r,
      ‖C_equiv (iteratedFDeriv ℝ (m + 1) (fun p ↦ B (K (φ z - p)) (w z)) y)‖ ≤
        (‖B‖ * C) * ‖w z‖ := by
    filter_upwards [hδ] with z hz y hy
    have hy_lt : ‖y - q₀‖ < r := by simpa [mem_ball, dist_eq_norm] using hy
    have hsep : δ - r ≤ ‖φ z - y‖ := by
      have htri := norm_sub_le (φ z - y) (q₀ - y)
      rw [sub_sub_sub_cancel_right, norm_sub_rev q₀ y] at htri
      linarith
    have hne : φ z ≠ y := fun heq ↦ by rw [heq, sub_self, norm_zero] at hsep; linarith
    have hnorm_C (g : W [×m + 1]→L[ℝ] E) : ‖C_equiv g‖ = ‖g‖ :=
      (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (m + 1) ↦ W) E).norm_map g
    rw [hnorm_C]
    exact (norm_iteratedFDeriv_bilin_kernel_sub_le B hK hne (w z) (m + 1)).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hC _ hsep) (norm_nonneg B))
        (norm_nonneg (w z)))
  have h_diff : ∀ᵐ z ∂μ, ∀ y ∈ ball q₀ r, HasFDerivAt
      (fun x ↦ iteratedFDeriv ℝ m (fun p ↦ B (K (φ z - p)) (w z)) x)
      (C_equiv (iteratedFDeriv ℝ (m + 1) (fun p ↦ B (K (φ z - p)) (w z)) y)) y := by
    filter_upwards [hδ] with z hz y hy
    have hy_lt : ‖y - q₀‖ < r := by simpa [mem_ball, dist_eq_norm] using hy
    exact hasFDerivAt_iteratedFDeriv_bilin_kernel_sub B hK
      (fun heq ↦ by rw [heq] at hz; linarith) (w z) m
  have hmain := hasFDerivAt_integral_of_dominated_of_fderiv_le
    (isOpen_ball.mem_nhds (by simpa [mem_ball, dist_eq_norm] using hqr))
    hF_meas hF_int hF'_meas h_bound (hw.norm.const_mul _) h_diff
  have hcomm := ContinuousLinearEquiv.integral_comp_comm (𝕜 := ℝ) (μ := μ)
    (E := W [×m + 1]→L[ℝ] E) (F := W →L[ℝ] W [×m]→L[ℝ] E) C_equiv
    (fun z ↦ iteratedFDeriv ℝ (m + 1) (fun p ↦ B (K (φ z - p)) (w z)) q)
  have hcurry (g : W [×m + 1]→L[ℝ] E) : C_equiv g = g.curryLeft := by
    ext v u
    simp [C_equiv]
  rwa [hcomm, hcurry] at hmain

/-- On `Metric.ball q₀ δ`, the integrated spatial jets form an infinite Taylor series for the
separated translation-kernel integral `y ↦ ∫ z, B (K (φ z - y)) (w z) ∂μ`. -/
theorem hasFTaylorSeriesUpToOn_integral_bilin_kernel_sub
    (B : F →L[ℝ] G →L[ℝ] E) {K : W → F} (hK : ∀ x ≠ (0 : W), ContDiffAt ℝ ∞ K x)
    (hK_bd : ∀ (k : ℕ) {ρ : ℝ}, 0 < ρ → ∃ C : ℝ, ∀ x : W, ρ ≤ ‖x‖ → ‖iteratedFDeriv ℝ k K x‖ ≤ C)
    {φ : α → W} (hφ : AEStronglyMeasurable φ μ)
    {w : α → G} (hw : Integrable w μ)
    {q₀ : W} {δ : ℝ} (hδ : ∀ᵐ z ∂μ, δ ≤ ‖φ z - q₀‖) :
    HasFTaylorSeriesUpToOn ∞
      (fun y ↦ ∫ z, B (K (φ z - y)) (w z) ∂μ)
      (fun y m ↦ ∫ z, iteratedFDeriv ℝ m (fun p ↦ B (K (φ z - p)) (w z)) y ∂μ)
      (ball q₀ δ) where
  zero_eq y _ := by
    let e₀ := (continuousMultilinearCurryFin0 ℝ W E).toContinuousLinearEquiv
    have hcomm := ContinuousLinearEquiv.integral_comp_comm (𝕜 := ℝ) (μ := μ)
      (E := W [×0]→L[ℝ] E) (F := E) e₀
      (fun z ↦ iteratedFDeriv ℝ 0 (fun p ↦ B (K (φ z - p)) (w z)) y)
    simpa only [e₀, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
      continuousMultilinearCurryFin0_apply, iteratedFDeriv_zero_apply,
      ContinuousMultilinearMap.curry0_apply] using hcomm.symm
  fderivWithin m _ y hy :=
    (hasFDerivAt_integral_iteratedFDeriv_bilin_kernel_sub
      B hK hK_bd hφ hw hδ m hy).hasFDerivWithinAt
  cont m _ y hy :=
    (hasFDerivAt_integral_iteratedFDeriv_bilin_kernel_sub
      B hK hK_bd hφ hw hδ m hy).continuousAt.continuousWithinAt

/-- Smoothness on `Metric.ball q₀ δ` of `y ↦ ∫ z, B (K (φ z - y)) (w z) ∂μ`. -/
theorem contDiffOn_integral_bilin_kernel_sub
    (B : F →L[ℝ] G →L[ℝ] E) {K : W → F} (hK : ∀ x ≠ (0 : W), ContDiffAt ℝ ∞ K x)
    (hK_bd : ∀ (k : ℕ) {ρ : ℝ}, 0 < ρ → ∃ C : ℝ, ∀ x : W, ρ ≤ ‖x‖ → ‖iteratedFDeriv ℝ k K x‖ ≤ C)
    {φ : α → W} (hφ : AEStronglyMeasurable φ μ)
    {w : α → G} (hw : Integrable w μ)
    {q₀ : W} {δ : ℝ} (hδ : ∀ᵐ z ∂μ, δ ≤ ‖φ z - q₀‖) {n : ℕ∞} :
    ContDiffOn ℝ n (fun y ↦ ∫ z, B (K (φ z - y)) (w z) ∂μ) (ball q₀ δ) :=
  (hasFTaylorSeriesUpToOn_integral_bilin_kernel_sub B hK hK_bd hφ hw hδ).contDiffOn.of_le
    (WithTop.coe_le_coe.2 le_top)

/-- Pointwise smoothness at `q ∈ Metric.ball q₀ δ` of `y ↦ ∫ z, B (K (φ z - y)) (w z) ∂μ`. -/
theorem contDiffAt_integral_bilin_kernel_sub
    (B : F →L[ℝ] G →L[ℝ] E) {K : W → F} (hK : ∀ x ≠ (0 : W), ContDiffAt ℝ ∞ K x)
    (hK_bd : ∀ (k : ℕ) {ρ : ℝ}, 0 < ρ → ∃ C : ℝ, ∀ x : W, ρ ≤ ‖x‖ → ‖iteratedFDeriv ℝ k K x‖ ≤ C)
    {φ : α → W} (hφ : AEStronglyMeasurable φ μ)
    {w : α → G} (hw : Integrable w μ)
    {q₀ : W} {δ : ℝ} (hδ : ∀ᵐ z ∂μ, δ ≤ ‖φ z - q₀‖)
    {q : W} (hq : q ∈ ball q₀ δ) {n : ℕ∞} :
    ContDiffAt ℝ n (fun y ↦ ∫ z, B (K (φ z - y)) (w z) ∂μ) q :=
  (contDiffOn_integral_bilin_kernel_sub B hK hK_bd hφ hw hδ q hq).contDiffAt
    (isOpen_ball.mem_nhds hq)

/-- Every iterated Fréchet derivative on `Metric.ball q₀ δ` of `y ↦ ∫ z, B (K (φ z - y)) (w z) ∂μ`
commutes with the Bochner integral. -/
theorem iteratedFDeriv_integral_bilin_kernel_sub
    (B : F →L[ℝ] G →L[ℝ] E) {K : W → F} (hK : ∀ x ≠ (0 : W), ContDiffAt ℝ ∞ K x)
    (hK_bd : ∀ (k : ℕ) {ρ : ℝ}, 0 < ρ → ∃ C : ℝ, ∀ x : W, ρ ≤ ‖x‖ → ‖iteratedFDeriv ℝ k K x‖ ≤ C)
    {φ : α → W} (hφ : AEStronglyMeasurable φ μ)
    {w : α → G} (hw : Integrable w μ)
    {q₀ : W} {δ : ℝ} (hδ : ∀ᵐ z ∂μ, δ ≤ ‖φ z - q₀‖)
    (m : ℕ) {q : W} (hq : q ∈ ball q₀ δ) :
    iteratedFDeriv ℝ m (fun y ↦ ∫ z, B (K (φ z - y)) (w z) ∂μ) q =
      ∫ z, iteratedFDeriv ℝ m (fun y ↦ B (K (φ z - y)) (w z)) q ∂μ := by
  have hseries := hasFTaylorSeriesUpToOn_integral_bilin_kernel_sub B hK hK_bd hφ hw hδ
  have heq := hseries.eq_iteratedFDerivWithin_of_uniqueDiffOn (m := m)
    (by simp) isOpen_ball.uniqueDiffOn hq
  rw [iteratedFDerivWithin_eq_iteratedFDeriv isOpen_ball.uniqueDiffOn
    (contDiffAt_integral_bilin_kernel_sub B hK hK_bd hφ hw hδ hq (n := m)) hq] at heq
  exact heq.symm

end SeparatedKernelIntegral

end TauCeti
