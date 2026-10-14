/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.JHolomorphic.Energy.PuncturedDisc
public import TauCeti.Geometry.Symplectic.JHolomorphic.Energy.Radial
import TauCeti.Analysis.Calculus.PowerGrowth
import TauCeti.Analysis.Complex.OperatorNorm
import TauCeti.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Power decay of energy at a puncture

For a finite-energy solution of `∂ₜu = J(u) ∂ₛu`, a uniform taming constant `c > 0`
and bound `‖J‖ ≤ M` give the radial inequality
`2c E(r) ≤ (1 + M)² r E'(r)` for the real-direction energy.
Consequently `E(r) / r^(2c / (1 + M)²)` is nondecreasing, giving a quantitative
power bound at the puncture. No extension at the puncture or compactness of the
image is assumed. This is the energy-decay step in removal of singularities;
continuous extension and elliptic regularity require further arguments.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed.,
  Section 4.5.
-/

public section

open Complex MeasureTheory Metric Set
open scoped Real RealInnerProductSpace

namespace TauCeti.SymplecticForm

section Angular

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {u : ℂ → V} {J : V → V →L[ℝ] V} {z₀ : ℂ} {M : ℝ}

/-- The angular square energy is bounded by the radial boundary density, using the
Cauchy--Riemann equation and an operator-norm bound on the target structure. -/
private theorem angular_energy_le {r : ℝ} (hr : 0 < r)
    (hu : ∀ θ, ContDiffAt ℝ 1 u (circleMap z₀ r θ))
    (hCR : ∀ θ, fderiv ℝ u (circleMap z₀ r θ) I =
      J (u (circleMap z₀ r θ)) (fderiv ℝ u (circleMap z₀ r θ) 1))
    (hJ : ∀ θ, ‖J (u (circleMap z₀ r θ))‖ ≤ M) :
    (∫ θ in -π..π, ‖deriv (fun θ ↦ u (circleMap z₀ r θ)) θ‖ ^ 2) ≤
      (1 + M) ^ 2 * r ^ 2 *
        ∫ θ in -π..π, ‖fderiv ℝ u (circleMap z₀ r θ) 1‖ ^ 2 := by
  have hdu : Continuous (fun θ ↦ fderiv ℝ u (circleMap z₀ r θ)) :=
    continuous_iff_continuousAt.mpr fun θ ↦
      (hu θ).continuousAt_fderiv (by norm_num) |>.comp
        (continuous_circleMap z₀ r).continuousAt
  have hd (θ : ℝ) := ((hu θ).differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt θ
    (hasDerivAt_circleMap z₀ r θ)
  have heq (θ : ℝ) : deriv (fun θ ↦ u (circleMap z₀ r θ)) θ =
      fderiv ℝ u (circleMap z₀ r θ) (circleMap 0 r θ * I) := hd θ |>.deriv
  have hcont : Continuous (fun θ ↦ ‖deriv (fun θ ↦ u (circleMap z₀ r θ)) θ‖ ^ 2) := by
    simp_rw [heq]
    exact (hdu.clm_apply ((continuous_circleMap 0 r).mul continuous_const)).norm.pow 2
  have hbcont : Continuous (fun θ ↦ ‖fderiv ℝ u (circleMap z₀ r θ) 1‖ ^ 2) :=
    (hdu.clm_apply continuous_const).norm.pow 2
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_mono_on (by linarith [Real.pi_pos])
    (hcont.intervalIntegrable _ _) ((hbcont.const_mul _).intervalIntegrable _ _)
  intro θ _
  have hI : ‖fderiv ℝ u (circleMap z₀ r θ) I‖ ≤
      M * ‖fderiv ℝ u (circleMap z₀ r θ) 1‖ := by
    rw [hCR θ]
    exact ((J _).le_opNorm _).trans (mul_le_mul_of_nonneg_right (hJ θ) (norm_nonneg _))
  have hbound := (fderiv ℝ u (circleMap z₀ r θ)).norm_apply_le_norm_one_add_norm_I
    (circleMap 0 r θ * I)
  rw [norm_mul, norm_I, mul_one, norm_circleMap_zero, abs_of_pos hr] at hbound
  have hs : ‖deriv (fun θ ↦ u (circleMap z₀ r θ)) θ‖ ≤
      (1 + M) * r * ‖fderiv ℝ u (circleMap z₀ r θ) 1‖ := by
    rw [heq]
    nlinarith
  calc
    _ ≤ ((1 + M) * r * ‖fderiv ℝ u (circleMap z₀ r θ) 1‖) ^ 2 := by
      gcongr
    _ = _ := by ring

end Angular

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] {ω : SymplecticForm V} {J₀ : AlmostComplexStructure V}
  {u : ℂ → V} {J : V → V →L[ℝ] V} {z₀ : ℂ} {R c M : ℝ}

/-- The finite real-direction energy on a punctured disc satisfies an Euler differential
inequality. Smoothness is required only away from the puncture. -/
theorem mul_integral_norm_fderiv_one_sq_ball_le_mul_deriv
    (hg : ∀ v w, ω v (J₀ w) = ⟪v, w⟫) (hc : 0 < c)
    (hu : ContDiffOn ℝ 2 u (ball z₀ R \ {z₀}))
    (hCR : ∀ z ∈ ball z₀ R \ {z₀}, fderiv ℝ u z I = J (u z) (fderiv ℝ u z 1))
    (htame : ∀ z ∈ ball z₀ R \ {z₀}, ∀ v, c * ‖v‖ ^ 2 ≤ ω v (J (u z) v))
    (hJ : ∀ z ∈ ball z₀ R \ {z₀}, ‖J (u z)‖ ≤ M)
    (henergy : IntegrableOn (fun z ↦ ‖fderiv ℝ u z‖ ^ 2) (ball z₀ R))
    {r : ℝ} (hr : r ∈ Ioo 0 R) :
    2 * c * (∫ z in ball z₀ r, ‖fderiv ℝ u z 1‖ ^ 2) ≤
      (1 + M) ^ 2 * r * deriv (fun t ↦ ∫ z in ball z₀ t, ‖fderiv ℝ u z 1‖ ^ 2) r := by
  let D := {z : ℂ | 0 < ‖z - z₀‖ ∧ ‖z - z₀‖ ≤ r}
  have hsub : D ⊆ ball z₀ R \ {z₀} := by
    intro z hz
    exact ⟨by simpa [mem_ball, dist_eq_norm] using hz.2.trans_lt hr.2,
      by simpa only [mem_singleton_iff, sub_ne_zero] using (norm_pos_iff.mp hz.1)⟩
  have hsmooth (z : ℂ) (hz : z ∈ D) : ContDiffAt ℝ 2 u z :=
    hu.contDiffAt ((isOpen_ball.sdiff isClosed_singleton).mem_nhds (hsub hz))
  have hD : D = closedBall z₀ r \ {z₀} := by
    ext z
    simp only [D, mem_ofPred_eq, mem_sdiff, mem_closedBall, dist_eq_norm, mem_singleton_iff]
    rw [norm_pos_iff, sub_ne_zero]
    exact and_comm
  have hclosed := volume.addHaar_closedBall_ae_eq_ball z₀ r
  have hae : D =ᵐ[volume] ball z₀ r := by
    rw [hD]
    exact (sdiff_null_ae_eq_self (measure_singleton z₀)).trans hclosed
  have hint : IntegrableOn (fun z ↦ ‖fderiv ℝ u z‖ ^ 2) D := by
    rw [IntegrableOn, Measure.restrict_congr_set hae]
    exact henergy.mono_set (ball_subset_ball hr.2.le)
  have hb := ω.integral_norm_fderiv_one_sq_punctured_disc_le z₀ hg hr.1 hc
    hsmooth (fun z hz ↦ hCR z (hsub hz)) (fun z hz ↦ htame z (hsub hz)) hint
  rw [setIntegral_congr_set hae, le_div_iff₀ (by positivity : 0 < 2 * c)] at hb
  have hmem (θ : ℝ) : circleMap z₀ r θ ∈ D := by
    simpa only [D, mem_ofPred_eq, circleMap_sub_center, norm_circleMap_zero,
      abs_of_pos hr.1] using And.intro hr.1 (le_refl r)
  have ha := angular_energy_le hr.1 (fun θ ↦ (hsmooth _ (hmem θ)).of_le one_le_two)
    (fun θ ↦ hCR _ (hsub (hmem θ))) (fun θ ↦ hJ _ (hsub (hmem θ)))
  rw [(hasDerivAt_integral_norm_fderiv_one_sq_ball (hu.of_le one_le_two) henergy hr).deriv]
  nlinarith

/-- Power decay of finite energy at a puncture: any two positive interior radii satisfy
the explicit bound with exponent `2c / (1 + M)²`. The value of `u` at the puncture
is unrestricted, and the target almost complex structure may vary with `u`. -/
theorem integral_norm_fderiv_one_sq_ball_le_rpow
    (hg : ∀ v w, ω v (J₀ w) = ⟪v, w⟫) (hc : 0 < c)
    (hu : ContDiffOn ℝ 2 u (ball z₀ R \ {z₀}))
    (hCR : ∀ z ∈ ball z₀ R \ {z₀}, fderiv ℝ u z I = J (u z) (fderiv ℝ u z 1))
    (htame : ∀ z ∈ ball z₀ R \ {z₀}, ∀ v, c * ‖v‖ ^ 2 ≤ ω v (J (u z) v))
    (hJ : ∀ z ∈ ball z₀ R \ {z₀}, ‖J (u z)‖ ≤ M)
    (henergy : IntegrableOn (fun z ↦ ‖fderiv ℝ u z‖ ^ 2) (ball z₀ R))
    {r b : ℝ} (hr : 0 < r) (hrb : r ≤ b) (hb : b < R) :
    (∫ z in ball z₀ r, ‖fderiv ℝ u z 1‖ ^ 2) ≤
      (∫ z in ball z₀ b, ‖fderiv ℝ u z 1‖ ^ 2) *
        (r / b) ^ (2 * c / (1 + M) ^ 2) := by
  have hbmem : circleMap z₀ b 0 ∈ ball z₀ R \ {z₀} := by
    have hbpos := hr.trans_le hrb
    constructor
    · simpa only [mem_ball, dist_eq_norm, circleMap_sub_center, norm_circleMap_zero,
        abs_of_pos hbpos] using hb
    · have hn : 0 < ‖circleMap z₀ b 0 - z₀‖ := by
        simpa only [circleMap_sub_center, norm_circleMap_zero, abs_of_pos hbpos] using hbpos
      exact sub_ne_zero.mp (norm_pos_iff.mp hn)
  have hM : 0 ≤ M := (norm_nonneg _).trans (hJ _ hbmem)
  have hden : 0 < (1 + M) ^ 2 := by positivity
  have hmono := monotoneOn_div_rpow_of_mul_le_mul_deriv (f := fun t ↦
      ∫ z in ball z₀ t, ‖fderiv ℝ u z 1‖ ^ 2) (α := 2 * c / (1 + M) ^ 2)
    (f' := fun t ↦ deriv (fun t ↦ ∫ z in ball z₀ t, ‖fderiv ℝ u z 1‖ ^ 2) t)
    (convex_Ioo 0 R) (fun t ht ↦ ht.1)
    (fun t ht ↦ (hasDerivAt_integral_norm_fderiv_one_sq_ball
      (hu.of_le one_le_two) henergy ht).continuousAt.continuousWithinAt)
    (fun t ht ↦ (hasDerivAt_integral_norm_fderiv_one_sq_ball
      (hu.of_le one_le_two) henergy (interior_subset ht)).differentiableAt.hasDerivAt)
    (fun t ht ↦ by
      have h := ω.mul_integral_norm_fderiv_one_sq_ball_le_mul_deriv hg hc hu hCR htame hJ
        henergy (interior_subset ht)
      rw [div_mul_eq_mul_div, div_le_iff₀ hden]
      nlinarith)
  have h := hmono ⟨hr, hrb.trans_lt hb⟩ ⟨hr.trans_le hrb, hb⟩ hrb
  rw [div_le_div_iff₀ (Real.rpow_pos_of_pos hr _) (Real.rpow_pos_of_pos (hr.trans_le hrb) _)] at h
  simpa only [Real.div_rpow hr.le (hr.trans_le hrb).le, ← mul_div_assoc] using
    (le_div_iff₀ (Real.rpow_pos_of_pos (hr.trans_le hrb) _)).mpr h

end TauCeti.SymplecticForm

end
