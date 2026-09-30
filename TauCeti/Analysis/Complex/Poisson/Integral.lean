/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Poisson
public import Mathlib.Analysis.Complex.Harmonic.Poisson
public import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions

/-!
# Harmonicity of the planar Poisson integral

The Poisson average of integrable real boundary data is harmonic in the disk. This supplies the
interior harmonicity needed for the planar Dirichlet construction. The Poisson formula for an
already harmonic function gives the reverse identity; boundary convergence requires a separate
estimate.

The Poisson integral is the real part of Mathlib's analytic Herglotz–Riesz integral.
See L. C. Evans, *Partial Differential Equations*, Section 2.2.4.
-/

public section

noncomputable section

namespace TauCeti

open Complex InnerProductSpace Metric MeasureTheory Real

/-- The Poisson average of real boundary data on the circle of radius `R` centered at `c`.
For integrable data it is harmonic at points off the circle. -/
def planarPoissonIntegral (g : ℂ → ℝ) (c : ℂ) (R : ℝ) (w : ℂ) : ℝ :=
  circleAverage (poissonKernel c w • g) c R

/-- The Poisson integral agrees with the usual circle average of the Poisson kernel times the
boundary data. -/
theorem planarPoissonIntegral_def (g : ℂ → ℝ) (c : ℂ) (R : ℝ) (w : ℂ) :
    planarPoissonIntegral g c R w = circleAverage (poissonKernel c w • g) c R := by
  rw [planarPoissonIntegral]

/-- The Poisson integral of zero boundary data is zero. -/
@[simp] theorem planarPoissonIntegral_zero (c : ℂ) (R : ℝ) (w : ℂ) :
    planarPoissonIntegral (fun _ ↦ 0) c R w = 0 := by
  change circleAverage (fun z ↦ poissonKernel c w z * (0 : ℝ)) c R = 0
  simpa using circleAverage_const (0 : ℝ) c R

/-- The Poisson integral is additive in circle-integrable boundary data away from the circle. -/
theorem planarPoissonIntegral_add {g₁ g₂ : ℂ → ℝ} {c : ℂ} {R : ℝ} {w : ℂ}
    (hg₁ : CircleIntegrable g₁ c R) (hg₂ : CircleIntegrable g₂ c R)
    (hw : w ∉ sphere c |R|) :
    planarPoissonIntegral (g₁ + g₂) c R w =
      planarPoissonIntegral g₁ c R w + planarPoissonIntegral g₂ c R w := by
  have hK : ContinuousOn (poissonKernel c w) (sphere c |R|) := by
    rw [poissonKernel_eq_re_herglotzRieszKernel]
    exact Complex.continuous_re.comp_continuousOn
      (continuousOn_herglotzRieszKernel_sphere hw)
  rw [planarPoissonIntegral_def, planarPoissonIntegral_def, planarPoissonIntegral_def]
  convert circleAverage_add (hg₁.continuousOn_smul hK) (hg₂.continuousOn_smul hK) using 1
  congr 1
  ext z
  simp [Pi.mul_apply, mul_add]

/-- The Poisson integral commutes with real scalar multiplication. -/
@[simp] theorem planarPoissonIntegral_smul (a : ℝ) (g : ℂ → ℝ) (c : ℂ) (R : ℝ)
    (w : ℂ) : planarPoissonIntegral (a • g) c R w =
      a • planarPoissonIntegral g c R w := by
  simpa [planarPoissonIntegral_def, smul_comm] using
    (circleAverage_smul (a := a) (f := poissonKernel c w • g) (c := c) (R := R))

/-- Boundary data agreeing on the circle have the same Poisson integral. -/
theorem planarPoissonIntegral_congr_sphere {g₁ g₂ : ℂ → ℝ} {c : ℂ} {R : ℝ} {w : ℂ}
    (h : Set.EqOn g₁ g₂ (sphere c |R|)) :
    planarPoissonIntegral g₁ c R w = planarPoissonIntegral g₂ c R w := by
  rw [planarPoissonIntegral_def, planarPoissonIntegral_def]
  exact circleAverage_congr_sphere (fun z hz ↦ by simp [h hz])

/-- The planar Poisson integral of circle-integrable data is harmonic away from the circle,
in particular throughout the open disk. -/
theorem harmonicOnNhd_planarPoissonIntegral {g : ℂ → ℝ} {c : ℂ} {R : ℝ}
    (hg : CircleIntegrable g c R) :
    HarmonicOnNhd (planarPoissonIntegral g c R) (sphere c |R|)ᶜ := by
  let g₀ : ℂ → ℝ := fun z ↦ g (z + c)
  have hg₀ : CircleIntegrable g₀ 0 R := by
    simpa [CircleIntegrable, g₀, circleMap, add_assoc, add_comm, add_left_comm] using hg
  have hgc : CircleIntegrable (fun ζ ↦ (g₀ ζ : ℂ)) 0 R := by
    simp only [CircleIntegrable, intervalIntegrable_iff] at hg₀ ⊢
    exact Complex.ofRealCLM.integrable_comp hg₀
  let F : ℂ → ℂ := fun w ↦ circleAverage
    (fun ζ ↦ herglotzRieszKernel 0 w ζ • (g₀ ζ : ℂ)) 0 R
  have hF : AnalyticOnNhd ℂ F (sphere (0 : ℂ) |R|)ᶜ :=
    analyticOnNhd_circleAverage_herglotzRieszKernel_smul hgc
  have htrans (z : ℂ) :
      planarPoissonIntegral g c R z = planarPoissonIntegral g₀ 0 R (z - c) := by
    rw [planarPoissonIntegral_def, ← circleAverage_map_add_const]
    simp only [planarPoissonIntegral_def, g₀]
    congr 1
    funext ζ
    simp [poissonKernel_def]
  intro w hw
  have hw₀ : w - c ∉ sphere (0 : ℂ) |R| := by
    simpa [Metric.mem_sphere, dist_eq_norm] using hw
  have heq : (planarPoissonIntegral g c R) =ᶠ[nhds w]
      fun z ↦ (F (z - c)).re := by
    filter_upwards [IsOpen.mem_nhds isClosed_sphere.isOpen_compl hw] with z hz
    have hz₀ : z - c ∉ sphere (0 : ℂ) |R| := by
      simpa [Metric.mem_sphere, dist_eq_norm] using hz
    rw [htrans, planarPoissonIntegral_def, poissonKernel_eq_re_herglotzRieszKernel]
    exact (re_circleAverage_herglotzRieszKernel_smul hg₀ hz₀).symm
  have hFa : AnalyticAt ℂ (fun z ↦ F (z - c)) w := by
    convert (hF (w - c) hw₀).comp_sub c using 1; simp
  exact (harmonicAt_congr_nhds heq).2 hFa.harmonicAt_re

/-- The Poisson integral preserves constant boundary data at every point inside the disk. In
particular, the Poisson kernel has circle average one there. -/
@[simp] theorem planarPoissonIntegral_const {c : ℂ} {R : ℝ} {w : ℂ}
    (hw : w ∈ ball c R) (a : ℝ) :
    planarPoissonIntegral (fun _ : ℂ ↦ a) c R w = a := by
  have hc : HarmonicOnNhd (fun _ : ℂ ↦ a) (closedBall c R) :=
    fun _ _ ↦ harmonicAt_const a
  rw [planarPoissonIntegral_def]
  exact hc.circleAverage_poissonKernel_smul hw

/-- The Poisson kernel is nonnegative on a circle when its evaluation point lies inside. -/
private theorem poissonKernel_nonneg_on_sphere {c w z : ℂ} {R : ℝ}
    (hw : w ∈ ball c R) (hz : z ∈ sphere c R) : 0 ≤ poissonKernel c w z := by
  rw [poissonKernel_eq_re_herglotzRieszKernel]
  have hR : ‖w - c‖ < R := mem_ball_iff_norm.mp hw
  have hRp : 0 < R := pos_of_mem_ball hw
  exact le_trans (by positivity : 0 ≤ (R - ‖w - c‖) / (R + ‖w - c‖))
    (by simpa [herglotzRieszKernel_def] using le_re_herglotzRieszKernel hz hw)

/-- The Poisson integral preserves order between circle-integrable boundary data in the disk. -/
theorem planarPoissonIntegral_mono {g₁ g₂ : ℂ → ℝ} {c : ℂ} {R : ℝ} {w : ℂ}
    (hg₁ : CircleIntegrable g₁ c R) (hg₂ : CircleIntegrable g₂ c R)
    (hw : w ∈ ball c R)
    (hle : ∀ z ∈ sphere c |R|, g₁ z ≤ g₂ z) :
    planarPoissonIntegral g₁ c R w ≤ planarPoissonIntegral g₂ c R w := by
  have hws : w ∉ sphere c |R| := by
    have hR : 0 < R := pos_of_mem_ball hw
    simp only [mem_sphere, abs_of_pos hR]
    intro h
    exact (ne_of_lt hw) h
  have hK : ContinuousOn (poissonKernel c w) (sphere c |R|) := by
    rw [poissonKernel_eq_re_herglotzRieszKernel]
    exact Complex.continuous_re.comp_continuousOn
      (continuousOn_herglotzRieszKernel_sphere hws)
  have hpoint : ∀ z ∈ sphere c |R|,
      (poissonKernel c w • g₁) z ≤ (poissonKernel c w • g₂) z := by
    intro z hz
    exact mul_le_mul_of_nonneg_left (hle z hz)
      (poissonKernel_nonneg_on_sphere hw (by simpa [abs_of_pos (pos_of_mem_ball hw)] using hz))
  rw [planarPoissonIntegral_def, planarPoissonIntegral_def]
  exact circleAverage_mono (hg₁.continuousOn_smul hK) (hg₂.continuousOn_smul hK) hpoint

/-- Nonnegative boundary data have a nonnegative Poisson integral in the disk. -/
theorem planarPoissonIntegral_nonneg {g : ℂ → ℝ} {c : ℂ} {R : ℝ} {w : ℂ}
    (hw : w ∈ ball c R) (hnonneg : ∀ z ∈ sphere c |R|, 0 ≤ g z) :
    0 ≤ planarPoissonIntegral g c R w := by
  have hpoint : ∀ z ∈ sphere c |R|, (0 : ℝ) ≤ (poissonKernel c w • g) z := by
    intro z hz
    exact mul_nonneg
      (poissonKernel_nonneg_on_sphere hw (by simpa [abs_of_pos (pos_of_mem_ball hw)] using hz))
      (hnonneg z hz)
  simpa [planarPoissonIntegral_def] using circleAverage_nonneg_of_nonneg hpoint

end TauCeti

end
