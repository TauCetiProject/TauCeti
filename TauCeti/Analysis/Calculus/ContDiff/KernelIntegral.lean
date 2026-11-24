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
import Mathlib.Analysis.Calculus.ContDiff.Bounds
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
  have hcomp : (fun p ↦ B (K (z - p)) c) = B.flip c ∘ fun p ↦ K (z - p) := by
    funext p
    simp
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
  have hcd : ContDiffAt ℝ ∞ (fun p ↦ K (z - p)) y :=
    (hK (z - y) (sub_ne_zero.2 hne)).comp y (contDiffAt_const.sub contDiffAt_id)
  have hcomp : (fun p ↦ B (K (z - p)) c) = B.flip c ∘ fun p ↦ K (z - p) := by
    funext p
    simp
  have hflip : ‖B.flip c‖ ≤ ‖B‖ * ‖c‖ :=
    (B.flip.le_opNorm c).trans_eq (by rw [ContinuousLinearMap.opNorm_flip])
  have hnorm_sub : ‖iteratedFDeriv ℝ k (fun p ↦ K (z - p)) y‖ =
      ‖iteratedFDeriv ℝ k K (z - y)‖ := by
    have htrans : (fun p ↦ K (z - p)) = fun p ↦ K (z + (-1 : ℝ) • p) := by
      funext p
      simp [sub_eq_add_neg]
    rw [htrans, norm_iteratedFDeriv_comp_const_smul (fun p ↦ K (z + p)),
      iteratedFDeriv_comp_add_left]
    simp [sub_eq_add_neg]
  rw [hcomp]
  calc ‖iteratedFDeriv ℝ k (B.flip c ∘ fun p ↦ K (z - p)) y‖
      ≤ ‖B.flip c‖ * ‖iteratedFDeriv ℝ k (fun p ↦ K (z - p)) y‖ :=
        (B.flip c).norm_iteratedFDeriv_comp_left hcd (WithTop.coe_le_coe.2 le_top)
    _ ≤ (‖B‖ * ‖c‖) * ‖iteratedFDeriv ℝ k K (z - y)‖ := by
        rw [hnorm_sub]
        exact mul_le_mul_of_nonneg_right hflip (norm_nonneg _)
    _ = ‖B‖ * ‖iteratedFDeriv ℝ k K (z - y)‖ * ‖c‖ := by ring

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
  have hne : φ z ≠ y := sub_ne_zero.1 (norm_pos_iff.1 (hρ.trans_le hsep))
  have hχ1 : χ (φ z - y) = 1 := by
    have h1 : 1 ≤ 2 * (‖φ z - y‖ / ρ) - 1 := by
      have hdiv : 1 ≤ ‖φ z - y‖ / ρ := (one_le_div hρ).2 hsep
      linarith
    simp only [χ, min_eq_left h1, max_eq_right zero_le_one]
  rw [iteratedFDeriv_bilin_kernel_sub B hK hne (w z) k]
  ext v
  simp [L, g, hχ1]

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
      (ball q₀ δ) := by
  have hloc (r : ℝ) (hr : r < δ) :
      HasFTaylorSeriesUpToOn ∞
        (fun y ↦ ∫ z, B (K (φ z - y)) (w z) ∂μ)
        (fun y m ↦ ∫ z, iteratedFDeriv ℝ m (fun p ↦ B (K (φ z - p)) (w z)) y ∂μ)
        (ball q₀ r) := by
    choose C hC using fun i : ℕ ↦ hK_bd i (sub_pos.2 hr)
    refine hasFTaylorSeriesUpToOn_integral_of_le_bound (bound := fun i z ↦ (‖B‖ * C i) * ‖w z‖)
      isOpen_ball ?_ ?_ (fun i _ ↦ hw.norm.const_mul _) ?_
    · intro y hy i _
      exact aestronglyMeasurable_iteratedFDeriv_bilin_kernel_sub
        B hK hφ hw.aestronglyMeasurable hδ i (ball_subset_ball hr.le hy)
    · filter_upwards [hδ] with z hz y hy i _
      have hy_lt : ‖y - q₀‖ < r := by simpa [mem_ball, dist_eq_norm] using hy
      have hsep : δ - r ≤ ‖φ z - y‖ := by
        have htri := norm_sub_norm_le (φ z - q₀) (y - q₀)
        rw [sub_sub_sub_cancel_right] at htri
        linarith
      have hne : φ z ≠ y := sub_ne_zero.1 (norm_pos_iff.1 ((sub_pos.2 hr).trans_le hsep))
      exact (norm_iteratedFDeriv_bilin_kernel_sub_le B hK hne (w z) i).trans
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hC i _ hsep) (norm_nonneg B))
          (norm_nonneg (w z)))
    · filter_upwards [hδ] with z hz
      have hcd : ContDiffOn ℝ ∞ (fun p ↦ B (K (φ z - p)) (w z)) (ball q₀ r) := fun y hy ↦ by
        have hy_lt : ‖y - q₀‖ < r := by simpa [mem_ball, dist_eq_norm] using hy
        have hne : φ z ≠ y := fun heq ↦ by linarith [heq ▸ hz]
        exact ((B.flip (w z)).contDiff.contDiffAt.comp y
          ((hK (φ z - y) (sub_ne_zero.2 hne)).comp y
            (contDiffAt_const.sub contDiffAt_id))).contDiffWithinAt
      exact (hcd.ftaylorSeriesWithin isOpen_ball.uniqueDiffOn).congr_series fun m _ y hy ↦
        iteratedFDerivWithin_of_isOpen m isOpen_ball hy
  refine (hasFTaylorSeriesUpToOn_top_iff' le_rfl).2 ⟨fun y hy ↦ ?_, fun m y hy ↦ ?_⟩
  · have hy_lt : ‖y - q₀‖ < δ := by simpa [mem_ball, dist_eq_norm] using hy
    exact (hloc ((‖y - q₀‖ + δ) / 2) (by linarith)).zero_eq y
      (by simpa [mem_ball, dist_eq_norm] using by linarith)
  · have hy_lt : ‖y - q₀‖ < δ := by simpa [mem_ball, dist_eq_norm] using hy
    have hyr : y ∈ ball q₀ ((‖y - q₀‖ + δ) / 2) := by
      simpa [mem_ball, dist_eq_norm] using by linarith
    exact (((hloc ((‖y - q₀‖ + δ) / 2) (by linarith)).fderivWithin m
      (WithTop.coe_lt_coe.2 (ENat.natCast_lt_top m)) y hyr).hasFDerivAt
      (isOpen_ball.mem_nhds hyr)).hasFDerivWithinAt

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
