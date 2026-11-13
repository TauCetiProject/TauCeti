/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.Complex.TaylorSeries
public import TauCeti.Analysis.Calculus.FormalMultilinearSeries

/-!
# Formal power series on open extended discs for holomorphic functions

Mathlib's `Complex.hasSum_taylorSeries_on_eball` shows that the Taylor series around `z₀` of a
Banach-space-valued holomorphic function on `Metric.eball z₀ r` (`r ≤ ∞`) sums pointwise to `f`
throughout that open extended disc. Packaging this with term decay on every smaller radius yields
`HasFPowerSeriesOnBall` on the entire open extended disc `Metric.eball z₀ r` for `0 < r`
(`DifferentiableOn.hasFPowerSeriesOnBall_eball`), without requiring continuity on the boundary or a
finite radius.
-/

public section

open Filter Metric Topology
open scoped ENNReal NNReal Nat

/-- A Banach-space-valued function that is complex differentiable on an open extended disc
`Metric.eball z₀ r` (`0 < r ≤ ∞`) admits its iterated-derivative Taylor series as a
`HasFPowerSeriesOnBall` on the full disc `Metric.eball z₀ r`. -/
theorem DifferentiableOn.hasFPowerSeriesOnBall_eball
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    {f : ℂ → E} {z₀ : ℂ} {r : ℝ≥0∞}
    (hf : DifferentiableOn ℂ f (Metric.eball z₀ r)) (hr : 0 < r) :
    HasFPowerSeriesOnBall f
      (TauCeti.mkPiRingSeries ℂ fun n ↦ (n ! : ℂ)⁻¹ • iteratedDeriv n f z₀) z₀ r := by
  let c : ℕ → E := fun n ↦ (n ! : ℂ)⁻¹ • iteratedDeriv n f z₀
  have hsum : ∀ {y : ℂ}, y ∈ Metric.eball (0 : ℂ) r →
      HasSum (fun n ↦ TauCeti.mkPiRingSeries ℂ c n fun _ ↦ y) (f (z₀ + y)) := by
    intro y hy
    have hzy : z₀ + y ∈ Metric.eball z₀ r := by
      rw [Metric.mem_eball, eDist_eq_eNorm_sub, add_sub_cancel_left]
      exact mem_eball_zero_iff.mp hy
    convert Complex.hasSum_taylorSeries_on_eball hf hzy using 1
    ext n
    simp [c, smul_comm ((n ! : ℂ)⁻¹) (y ^ n)]
  refine ⟨ENNReal.le_of_forall_nnreal_lt fun R hRr ↦ ?_, hr, fun {y} hy ↦ hsum hy⟩
  have hR_mem : ((R : ℝ) : ℂ) ∈ Metric.eball (0 : ℂ) r := by
    rw [mem_eball_zero_iff]
    simpa [eNorm_eq_nnNorm] using hRr
  have htend :
      Tendsto (fun n ↦ ‖TauCeti.mkPiRingSeries ℂ c n fun _ ↦ ((R : ℝ) : ℂ)‖) atTop (𝓝 0) := by
    simpa using (hsum hR_mem).summable.tendsto_atTop_zero.norm
  refine (TauCeti.mkPiRingSeries ℂ c).le_radius_of_tendsto (htend.congr fun n ↦ ?_)
  simp [norm_smul, mul_comm]

end
