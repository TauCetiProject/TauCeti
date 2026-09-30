/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Poisson.Basic
public import Mathlib.Analysis.Complex.Harmonic.Poisson
public import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions

/-!
# Harmonicity of the planar Poisson integral

The Poisson average of integrable real boundary data is harmonic in the disk. This supplies the
interior harmonicity needed for the planar Dirichlet construction. The Poisson formula for an
already harmonic function gives the reverse identity; boundary convergence requires a separate
estimate.

The proof uses the analytic Herglotz–Riesz integral from Mathlib's
`Analysis/Complex/Poisson.lean` and takes its real part. See L. C. Evans,
*Partial Differential Equations*, Section 2.2.4.
-/

public section

noncomputable section

namespace TauCeti

open Complex InnerProductSpace Metric MeasureTheory Real

/-- The Poisson average of real boundary data on the circle of radius `R` centered at zero.
For integrable data it is harmonic at points off the circle. -/
def planarPoissonIntegral (g : ℂ → ℝ) (R : ℝ) (w : ℂ) : ℝ :=
  circleAverage (poissonKernel 0 w • g) 0 R

/-- The Poisson integral agrees with the usual circle average of the Poisson kernel times the
boundary data. -/
theorem planarPoissonIntegral_def (g : ℂ → ℝ) (R : ℝ) (w : ℂ) :
    planarPoissonIntegral g R w = circleAverage (poissonKernel 0 w • g) 0 R := by
  rw [planarPoissonIntegral]

/-- The planar Poisson integral of circle-integrable data is harmonic away from the circle,
in particular throughout the open disk. -/
theorem harmonicOnNhd_planarPoissonIntegral {g : ℂ → ℝ} {R : ℝ}
    (hg : CircleIntegrable g 0 R) :
    HarmonicOnNhd (planarPoissonIntegral g R) (sphere (0 : ℂ) |R|)ᶜ := by
  have hgc : CircleIntegrable (fun ζ ↦ (g ζ : ℂ)) 0 R := by
    simp only [CircleIntegrable, intervalIntegrable_iff] at hg ⊢
    exact Complex.ofRealCLM.integrable_comp hg
  let F : ℂ → ℂ := fun w ↦ circleAverage
    (fun ζ ↦ herglotzRieszKernel 0 w ζ • (g ζ : ℂ)) 0 R
  have hF : AnalyticOnNhd ℂ F (sphere (0 : ℂ) |R|)ᶜ :=
    analyticOnNhd_circleAverage_herglotzRieszKernel_smul hgc
  intro w hw
  have heq : (planarPoissonIntegral g R) =ᶠ[nhds w] fun z ↦ (F z).re := by
    filter_upwards [IsOpen.mem_nhds isClosed_sphere.isOpen_compl hw] with z hz
    rw [planarPoissonIntegral_def, poissonKernel_eq_re_herglotzRieszKernel]
    exact (re_circleAverage_herglotzRieszKernel_smul hg hz).symm
  exact (harmonicAt_congr_nhds heq).2 ((hF w hw : AnalyticAt ℂ F w).harmonicAt_re)

/-- The Poisson integral preserves constant boundary data at every point inside the disk. In
particular, the Poisson kernel has circle average one there. -/
@[simp] theorem planarPoissonIntegral_const {R : ℝ} {w : ℂ} (hw : w ∈ ball 0 R)
    (c : ℝ) : planarPoissonIntegral (fun _ : ℂ ↦ c) R w = c := by
  have hc : HarmonicOnNhd (fun _ : ℂ ↦ c) (closedBall 0 R) :=
    fun _ _ ↦ harmonicAt_const c
  exact hc.circleAverage_poissonKernel_smul hw

/-- A nonnegative integrable boundary function has a nonnegative Poisson integral in the disk. -/
theorem planarPoissonIntegral_nonneg {g : ℂ → ℝ} {R : ℝ} {w : ℂ}
    (hg : CircleIntegrable g 0 R) (hw : w ∈ ball 0 R)
    (hnonneg : ∀ z ∈ sphere (0 : ℂ) |R|, 0 ≤ g z) :
    0 ≤ planarPoissonIntegral g R w := by
  have hws : w ∉ sphere (0 : ℂ) |R| := by
    rw [mem_ball_zero_iff] at hw
    simp only [mem_sphere, dist_zero_right]
    intro h
    rw [abs_of_pos (lt_of_le_of_lt (norm_nonneg w) hw)] at h
    exact (ne_of_lt hw) h
  have hK : ContinuousOn (poissonKernel 0 w) (sphere (0 : ℂ) |R|) := by
    rw [poissonKernel_eq_re_herglotzRieszKernel]
    exact Complex.continuous_re.comp_continuousOn
      (continuousOn_herglotzRieszKernel_sphere hws)
  have hint : CircleIntegrable (poissonKernel 0 w • g) 0 R :=
    hg.continuousOn_smul hK
  have hzero : CircleIntegrable (fun _ : ℂ ↦ (0 : ℝ)) 0 R := by
    simp [CircleIntegrable]
  have hpoint : ∀ z ∈ sphere (0 : ℂ) |R|, (0 : ℝ) ≤ (poissonKernel 0 w • g) z := by
    intro z hz
    have hzR : ‖z‖ = R := by
      simpa [abs_of_pos (pos_of_mem_ball hw), dist_zero_right] using hz
    have hKpos : 0 ≤ poissonKernel 0 w z := by
      rw [poissonKernel_def]
      have : 0 < R ^ 2 - ‖w‖ ^ 2 := by
        have := mem_ball_zero_iff.mp hw
        nlinarith [norm_nonneg w]
      simp only [sub_zero, hzR]
      positivity
    exact mul_nonneg hKpos (hnonneg z hz)
  simpa [planarPoissonIntegral_def, circleAverage_const] using
    circleAverage_mono hzero hint hpoint

end TauCeti

end
