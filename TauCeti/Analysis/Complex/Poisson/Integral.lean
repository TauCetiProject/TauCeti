/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Poisson.Basic
public import Mathlib.Analysis.Complex.Harmonic.Poisson
public import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions
import Mathlib.Analysis.Normed.Group.Bounded

/-!
# Harmonicity of the planar Poisson integral

The Poisson average of integrable real boundary data is harmonic in the disk. For continuous
boundary data, it converges to the prescribed value as the interior point approaches the boundary.
Together these facts solve the planar Dirichlet problem on a disk.

The Poisson integral is the real part of Mathlib's analytic Herglotz–Riesz integral.
See L. C. Evans, *Partial Differential Equations*, Section 2.2.4.
-/

public section

noncomputable section

namespace TauCeti

open Complex Filter InnerProductSpace Metric MeasureTheory Real

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
  have h : poissonKernel c w • (fun _ : ℂ ↦ (0 : ℝ)) = fun _ ↦ 0 := by
    ext z
    simp
  rw [planarPoissonIntegral_def, h]
  exact circleAverage_const (0 : ℝ) c R

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
    have hmap : (fun θ : ℝ ↦ g₀ (circleMap 0 R θ)) =
        (fun θ : ℝ ↦ g (circleMap c R θ)) := by
      funext θ
      simp only [g₀, circleMap, zero_add]
      congr 1
      ring
    simpa only [CircleIntegrable, hmap] using hg
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
    (hw : w ∈ ball c |R|) (a : ℝ) :
    planarPoissonIntegral (fun _ : ℂ ↦ a) c R w = a := by
  have hc : HarmonicOnNhd (fun _ : ℂ ↦ a) (closedBall c |R|) :=
    fun _ _ ↦ harmonicAt_const a
  rw [planarPoissonIntegral_def]
  simpa only [circleAverage_abs_radius] using hc.circleAverage_poissonKernel_smul hw

/-- The Poisson integral preserves order between circle-integrable boundary data in the disk. -/
theorem planarPoissonIntegral_mono {g₁ g₂ : ℂ → ℝ} {c : ℂ} {R : ℝ} {w : ℂ}
    (hg₁ : CircleIntegrable g₁ c R) (hg₂ : CircleIntegrable g₂ c R)
    (hw : w ∈ ball c |R|)
    (hle : ∀ z ∈ sphere c |R|, g₁ z ≤ g₂ z) :
    planarPoissonIntegral g₁ c R w ≤ planarPoissonIntegral g₂ c R w := by
  have hws : w ∉ sphere c |R| := by
    simp only [mem_sphere]
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
      (poissonKernel_nonneg_on_sphere hw hz)
  rw [planarPoissonIntegral_def, planarPoissonIntegral_def]
  exact circleAverage_mono (hg₁.continuousOn_smul hK) (hg₂.continuousOn_smul hK) hpoint

/-- Nonnegative boundary data have a nonnegative Poisson integral in the disk. -/
theorem planarPoissonIntegral_nonneg {g : ℂ → ℝ} {c : ℂ} {R : ℝ} {w : ℂ}
    (hw : w ∈ ball c |R|) (hnonneg : ∀ z ∈ sphere c |R|, 0 ≤ g z) :
    0 ≤ planarPoissonIntegral g c R w := by
  have hpoint : ∀ z ∈ sphere c |R|, (0 : ℝ) ≤ (poissonKernel c w • g) z := by
    intro z hz
    exact mul_nonneg
      (poissonKernel_nonneg_on_sphere hw hz)
      (hnonneg z hz)
  simpa [planarPoissonIntegral_def] using circleAverage_nonneg_of_nonneg hpoint

/-- The Poisson integral of continuous boundary data converges to the prescribed value when its
argument approaches a boundary point through the open disk. -/
theorem tendsto_planarPoissonIntegral {g : ℂ → ℝ} {c z : ℂ} {R : ℝ}
    (hR : 0 < R) (hg : ContinuousOn g (sphere c R)) (hz : z ∈ sphere c R) :
    Tendsto (planarPoissonIntegral g c R) (nhdsWithin z (ball c R)) (nhds (g z)) := by
  -- Compactness of the boundary gives both a global bound and a uniform local estimate for `g`.
  have hgi : CircleIntegrable g c R := hg.circleIntegrable hR.le
  have hbound_cont : ContinuousOn (fun y ↦ g y - g z) (sphere c R) :=
    hg.sub continuousOn_const
  obtain ⟨C, hC⟩ := (isCompact_sphere c R).exists_bound_of_continuousOn hbound_cont
  have hCnonneg : 0 ≤ C := by
    have := hC z hz
    simpa using this
  have hgunif : UniformContinuousOn g (sphere c R) :=
    (isCompact_sphere c R).uniformContinuousOn_of_continuous hg
  rw [Metric.uniformContinuousOn_iff] at hgunif
  rw [Metric.tendsto_nhds]
  intro eps heps
  obtain ⟨delta, hdelta, hdelta_g⟩ := hgunif (eps / 2) (half_pos heps)
  -- This far-field bound tends to zero as the pole approaches the boundary point.
  let B : ℂ → ℝ := fun w ↦ (R ^ 2 - ‖w - c‖ ^ 2) / (delta / 2) ^ 2
  have hBcont : Continuous B := by
    dsimp [B]
    fun_prop
  have hBz : B z = 0 := by
    have hznorm : ‖z - c‖ = R := by
      simpa [mem_sphere, dist_eq_norm, abs_of_pos hR] using hz
    simp [B, hznorm]
  have hBlim : Tendsto (fun w ↦ B w * C) (nhdsWithin z (ball c R)) (nhds 0) := by
    have hmulcont : Continuous (fun w ↦ B w * C) := hBcont.mul continuous_const
    have h := hmulcont.continuousAt.tendsto.mono_left
      (nhdsWithin_le_nhds : nhdsWithin z (ball c R) ≤ nhds z)
    simpa [hBz] using h
  have hsmall : ∀ᶠ w in nhdsWithin z (ball c R), B w * C < eps / 2 :=
    (Metric.tendsto_nhds.1 hBlim (eps / 2) (half_pos heps)).mono fun w hw ↦ by
      simpa [Real.dist_eq] using (abs_lt.mp hw).2
  have hnear : ∀ᶠ w in nhdsWithin z (ball c R), dist w z ≤ delta / 2 := by
    have hmem : ball z (delta / 2) ∈ nhds z := ball_mem_nhds z (half_pos hdelta)
    have hevent : ∀ᶠ w in nhds z, w ∈ ball z (delta / 2) := hmem
    filter_upwards [hevent.filter_mono nhdsWithin_le_nhds] with w hw
    exact (mem_ball.mp hw).le
  filter_upwards [self_mem_nhdsWithin, hsmall, hnear] with w hw hwsmall hwnear
  have hwR : w ∈ ball c |R| := by simpa [abs_of_pos hR] using hw
  have hws : w ∉ sphere c |R| := by
    rw [mem_sphere]
    exact ne_of_lt hwR
  have hKcont : ContinuousOn (poissonKernel c w) (sphere c |R|) := by
    rw [poissonKernel_eq_re_herglotzRieszKernel]
    exact Complex.continuous_re.comp_continuousOn
      (continuousOn_herglotzRieszKernel_sphere hws)
  have hprod_i : CircleIntegrable (poissonKernel c w • g) c R :=
    hgi.continuousOn_smul hKcont
  have hconst_i : CircleIntegrable (poissonKernel c w • fun _ : ℂ ↦ g z) c R :=
    (continuousOn_const.circleIntegrable hR.le).continuousOn_smul hKcont
  have hdiff_i : CircleIntegrable (fun y ↦ poissonKernel c w y * (g y - g z)) c R := by
    convert hprod_i.sub hconst_i using 1
    ext y
    simp [Pi.sub_apply, mul_sub]
  have habs_i : CircleIntegrable
      (fun y ↦ |poissonKernel c w y * (g y - g z)|) c R := hdiff_i.abs
  have hmajor_i : CircleIntegrable
      (fun y ↦ poissonKernel c w y * (eps / 2) + B w * C) c R := by
    fun_prop
  have hBnonneg : 0 ≤ B w := by
    dsimp [B]
    exact div_nonneg (by
      have hwnorm : ‖w - c‖ < R := by
        simpa [mem_ball, dist_eq_norm] using hw
      nlinarith [norm_nonneg (w - c)]) (sq_nonneg _)
  -- On the near arc uniform continuity controls the data; on the far arc `B` controls the kernel.
  have hpoint (y : ℂ) (hy : y ∈ sphere c R) :
      |poissonKernel c w y * (g y - g z)| ≤
        poissonKernel c w y * (eps / 2) + B w * C := by
    have hKnonneg : 0 ≤ poissonKernel c w y :=
      poissonKernel_nonneg_on_sphere hwR (by simpa [abs_of_pos hR] using hy)
    rw [abs_mul, abs_of_nonneg hKnonneg]
    by_cases hynear : dist y z < delta
    · have hgnear : |g y - g z| < eps / 2 := by
        simpa [Real.dist_eq] using hdelta_g y hy z hz hynear
      have hBCnonneg : 0 ≤ B w * C := by
        exact mul_nonneg hBnonneg hCnonneg
      exact (mul_le_mul_of_nonneg_left hgnear.le hKnonneg).trans
        (le_add_of_nonneg_right hBCnonneg)
    · have hKle : poissonKernel c w y ≤ B w :=
        poissonKernel_le_of_dist_le_half_of_le_dist hdelta
          (mem_closedBall.mpr (mem_ball.mp hw).le) hwnear hy (le_of_not_gt hynear)
      have hgnorm : |g y - g z| ≤ C := by simpa using hC y hy
      calc
        poissonKernel c w y * |g y - g z| ≤ B w * C :=
          mul_le_mul hKle hgnorm (abs_nonneg _) hBnonneg
        _ ≤ poissonKernel c w y * (eps / 2) + B w * C :=
          le_add_of_nonneg_left (mul_nonneg hKnonneg (half_pos heps).le)
  have hdiff : planarPoissonIntegral g c R w - g z =
      circleAverage (fun y ↦ poissonKernel c w y * (g y - g z)) c R := by
    calc
      planarPoissonIntegral g c R w - g z =
          circleAverage (poissonKernel c w • g) c R -
            circleAverage (poissonKernel c w • fun _ : ℂ ↦ g z) c R := by
        rw [planarPoissonIntegral_def]
        congr 1
        exact (planarPoissonIntegral_const hwR (g z)).symm.trans
          (planarPoissonIntegral_def (fun _ : ℂ ↦ g z) c R w)
      _ = circleAverage ((poissonKernel c w • g) -
            (poissonKernel c w • fun _ : ℂ ↦ g z)) c R :=
        (circleAverage_sub hprod_i hconst_i).symm
      _ = circleAverage (fun y ↦ poissonKernel c w y * (g y - g z)) c R := by
        congr 1
        ext y
        simp [Pi.sub_apply, mul_sub]
  -- Positivity and mass one turn the pointwise majorant into the required integral estimate.
  rw [Real.dist_eq, hdiff]
  calc
    ‖circleAverage (fun y ↦ poissonKernel c w y * (g y - g z)) c R‖ ≤
        circleAverage (fun y ↦ |poissonKernel c w y * (g y - g z)|) c R :=
      norm_circleAverage_le_circleAverage_norm
    _ ≤ circleAverage (fun y ↦ poissonKernel c w y * (eps / 2) + B w * C) c R :=
      circleAverage_mono habs_i hmajor_i (by simpa [abs_of_pos hR] using hpoint)
    _ = eps / 2 + B w * C := by
      rw [circleAverage_fun_add (by fun_prop) (by fun_prop), circleAverage_const]
      have hfirst : circleAverage (fun y ↦ poissonKernel c w y * (eps / 2)) c R = eps / 2 := by
        have hmass : circleAverage (poissonKernel c w) c R = 1 := by
          calc
            circleAverage (poissonKernel c w) c R =
                planarPoissonIntegral (fun _ : ℂ ↦ (1 : ℝ)) c R w := by
              rw [planarPoissonIntegral_def]
              congr 1
              ext y
              simp
            _ = 1 := planarPoissonIntegral_const hwR 1
        calc
          circleAverage (fun y ↦ poissonKernel c w y * (eps / 2)) c R =
              circleAverage ((eps / 2) • poissonKernel c w) c R := by
            congr 1
            ext y
            simp [mul_comm]
          _ = (eps / 2) • circleAverage (poissonKernel c w) c R := circleAverage_smul
          _ = eps / 2 := by rw [hmass]; simp
      rw [hfirst]
    _ < eps := by linarith

end TauCeti

end
