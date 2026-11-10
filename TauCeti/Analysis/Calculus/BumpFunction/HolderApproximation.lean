/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Convolution.Holder
public import TauCeti.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.MeasureTheory.Measure.Haar.Unique
import TauCeti.Topology.MetricSpace.Holder

/-!
# Smooth approximation with uniform Hölder bounds and controlled support

Normalized bump convolutions approximate a bounded Hölder source uniformly, preserve its
supremum and Hölder constant, and enlarge a fixed support disc by at most one unit. These
approximations let uniform smooth-data potential estimates pass to Hölder data.

The approximation also holds in the Hölder seminorm when the Hölder bound is only used below the
scale of the bump: if `f` satisfies `dist (f x) (f y) ≤ η * dist x y ^ α` whenever
`dist x y < ρ.rOut`, then `ρ ⋆ f` is within `η * ρ.rOut ^ α` of `f`
(`ContDiffBump.dist_normed_convolution_le_mul_rpow`) and `f - ρ ⋆ f` is `α`-Hölder with
constant `2 η` (`ContDiffBump.holderWith_sub_normed_convolution`). Applied with `η → 0`, this is
the approximation of little Hölder functions by smooth ones.
-/

public noncomputable section

open MeasureTheory Metric Set ContinuousLinearMap Filter
open scoped Convolution NNReal ContDiff Pointwise Topology

namespace TauCeti

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

section LocalHolder

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  [MeasurableSpace G] [BorelSpace G] {μ : Measure G} [μ.IsAddHaarMeasure]
  {f : G → F} {η : ℝ} {α : ℝ≥0} (ρ : ContDiffBump (0 : G))

/-- If `f` satisfies the `α`-Hölder bound with constant `η` between points at distance less than
`ρ.rOut`, then its normalized-bump convolution is within `η * ρ.rOut ^ α` of `f`. -/
theorem _root_.ContDiffBump.dist_normed_convolution_le_mul_rpow (hf : Continuous f)
    (hloc : ∀ x y, dist x y < ρ.rOut → dist (f x) (f y) ≤ η * dist x y ^ (α : ℝ))
    (hη : 0 ≤ η) (w : G) :
    dist ((ρ.normed μ ⋆[lsmul ℝ ℝ, μ] f) w) (f w) ≤ η * ρ.rOut ^ (α : ℝ) :=
  ρ.dist_normed_convolution_le hf.aestronglyMeasurable fun x hx ↦
    (hloc x w (mem_ball.1 hx)).trans (by gcongr; exact (mem_ball.1 hx).le)

/-- If `f` satisfies the `α`-Hölder bound with constant `η` between points at distance less than
`ρ.rOut`, then `f - ρ ⋆ f` is `α`-Hölder with constant `2 η` on the whole space. -/
theorem _root_.ContDiffBump.holderWith_sub_normed_convolution (hf : Continuous f)
    (hloc : ∀ x y, dist x y < ρ.rOut → dist (f x) (f y) ≤ η * dist x y ^ (α : ℝ))
    (hη : 0 ≤ η) :
    HolderWith (2 * η).toNNReal α (f - ρ.normed μ ⋆[lsmul ℝ ℝ, μ] f) := by
  set g := ρ.normed μ ⋆[lsmul ℝ ℝ, μ] f
  -- Below the scale `ρ.rOut`, the convolution satisfies the same bound as `f`.
  have hg : ∀ x y, dist x y < ρ.rOut → dist (g x) (g y) ≤ η * dist x y ^ (α : ℝ) :=
    fun x y hxy ↦ ρ.dist_normed_convolution_le_of_dist_sub_le hf fun t ↦ by
      simpa only [dist_sub_right] using hloc (x - t) (y - t) (by rwa [dist_sub_right])
  -- Above it, the uniform bound on `f - g` is at most `η * dist x y ^ α`.
  have hsup (w : G) : ‖f w - g w‖ ≤ η * ρ.rOut ^ (α : ℝ) := by
    rw [← dist_eq_norm, dist_comm]
    exact ρ.dist_normed_convolution_le_mul_rpow hf hloc hη w
  rw [← holderOnWith_univ]
  refine HolderOnWith.of_dist_le fun x _ y _ ↦ ?_
  rw [Real.coe_toNNReal _ (by positivity), Pi.sub_apply, Pi.sub_apply]
  rcases lt_or_ge (dist x y) ρ.rOut with hxy | hxy
  · calc dist (f x - g x) (f y - g y) ≤ dist (f x) (f y) + dist (g x) (g y) :=
          dist_sub_sub_le _ _ _ _
      _ ≤ η * dist x y ^ (α : ℝ) + η * dist x y ^ (α : ℝ) :=
        add_le_add (hloc x y hxy) (hg x y hxy)
      _ = 2 * η * dist x y ^ (α : ℝ) := by ring
  · calc dist (f x - g x) (f y - g y) ≤ ‖f x - g x‖ + ‖f y - g y‖ :=
          dist_le_norm_add_norm _ _
      _ ≤ η * ρ.rOut ^ (α : ℝ) + η * ρ.rOut ^ (α : ℝ) := add_le_add (hsup x) (hsup y)
      _ = 2 * η * ρ.rOut ^ (α : ℝ) := by ring
      _ ≤ 2 * η * dist x y ^ (α : ℝ) := by gcongr; exact ρ.rOut_pos.le

end LocalHolder

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
  · exact (ρ n).norm_normed_convolution_le hM x
  · exact ContDiffBump.tendstoUniformly_normed_convolution
      (ContDiffBump.tendsto_rOut_shrinking zero_lt_one) (hf.uniformContinuous hα)

end TauCeti
