/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Convolution.Holder
public import TauCeti.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# Smooth approximation with uniform Hölder bounds and controlled support

Normalized bump convolutions approximate a bounded Hölder source uniformly, preserve its
supremum and Hölder constant, and enlarge a fixed support disc by at most one unit. These
approximations let uniform smooth-data potential estimates pass to Hölder data.
-/

public noncomputable section

open MeasureTheory Metric Set ContinuousLinearMap Filter
open scoped Convolution NNReal ContDiff Pointwise Topology

namespace TauCeti

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- Smooth approximation of a bounded Hölder source, with its Hölder constant and supremum
unchanged and its support contained in one fixed larger disc. -/
theorem exists_contDiff_support_subset_holderWith_tendstoUniformly
    {f : ℂ → F} {H α M : ℝ≥0} (hα : 0 < α) (hf : HolderWith H α f)
    (hM : ∀ x, ‖f x‖ ≤ M) {c : ℂ} {r : ℝ}
    (hs : Function.support f ⊆ closedBall c r) :
    ∃ g : ℕ → ℂ → F,
      (∀ n, ContDiff ℝ ∞ (g n)) ∧
      (∀ n, Function.support (g n) ⊆ closedBall c (r + 1)) ∧
      (∀ n, HolderWith H α (g n)) ∧ (∀ n x, ‖g n x‖ ≤ M) ∧
      TendstoUniformly g f atTop := by
  let ρ (n : ℕ) : ContDiffBump (0 : ℂ) := ContDiffBump.shrinking zero_lt_one n
  let g (n : ℕ) := (ρ n).normed volume ⋆ f
  have hfc := hf.continuous hα
  have hgc (n : ℕ) : ContDiff ℝ ∞ (g n) :=
    (ρ n).hasCompactSupport_normed.contDiff_convolution_left (lsmul ℝ ℝ)
      (ρ n).contDiff_normed hfc.locallyIntegrable
  have hInt (n : ℕ) : ∫ z, ‖(ρ n).normed volume z‖ = 1 := by
    have heq : (fun z ↦ ‖(ρ n).normed volume z‖) = (ρ n).normed volume := by
      funext z
      exact Real.norm_of_nonneg ((ρ n).nonneg_normed z)
    rw [heq]
    exact (ρ n).integral_normed
  refine ⟨g, hgc, fun n ↦ ?_, fun n ↦ ?_, fun n x ↦ ?_, ?_⟩
  · have hfs : tsupport f ⊆ closedBall c r :=
      closure_minimal hs isClosed_closedBall
    have hρ : (ρ n).rOut ≤ 1 := by
      rw [ContDiffBump.rOut_shrinking]
      exact div_le_self zero_le_one (le_add_of_nonneg_left (Nat.cast_nonneg n))
    intro x hx
    have hx' := (ρ n).tsupport_normed_convolution_subset (μ := volume)
      (subset_tsupport _ hx)
    rcases hx' with ⟨a, ha, b, hb, rfl⟩
    rw [mem_closedBall] at ha ⊢
    calc
      dist (a + b) c = dist (a + b) (0 + c) := by rw [zero_add]
      _ ≤ dist a 0 + dist b c := dist_add_add_le _ _ _ _
      _ ≤ 1 + r := add_le_add (ha.trans hρ) (mem_closedBall.mp (hfs hb))
      _ = r + 1 := add_comm _ _
  · have h := holderWith_integral_kernel_smul_sub (μ := volume) (ρ n).integrable_normed hα hf hM
    have heq : g n = fun w ↦ ∫ z, (ρ n).normed volume z • f (w - z) := by
      funext w
      dsimp only [g]
      rw [convolution_def]
      rfl
    rw [heq]
    simpa only [hInt, Real.toNNReal_one, one_mul] using h
  · have h := norm_integral_kernel_smul_sub_le (μ := volume) (ρ n).integrable_normed hM x
    simpa only [hInt, one_mul, g, convolution_def, lsmul_apply] using h
  · exact ContDiffBump.tendstoUniformly_normed_convolution
      (ContDiffBump.tendsto_rOut_shrinking zero_lt_one) (hf.uniformContinuous hα)

end TauCeti
