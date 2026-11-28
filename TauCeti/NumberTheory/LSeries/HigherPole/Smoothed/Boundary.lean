/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Integral.Exp.Undamping
public import TauCeti.NumberTheory.LSeries.HigherPole.DelangeWeight
public import TauCeti.NumberTheory.LSeries.HigherPole.SquaredSinc

/-!
# Removing the time damping in Delange's smoothing argument

`integrableOn_and_integral_delangeWeight_mul_sub_mul_pow_mul_squaredSinc_eq_of_tendsto`
gives integrability of the undamped smoothed term and the value of the model-subtracted integral.
It uses the bound `delangeWeight_mul_pow_lt_one` for the normalized model and applies
`TauCeti.integrableOn_and_integral_sub_eq_of_tendsto_exp_neg_mul` to the two smoothed terms.

See H. Delange, *Généralisation du théorème de Ikehara* (1954), §3.3.4.
-/

public section

open Filter MeasureTheory Set
open scoped Topology

namespace TauCeti.HigherPoleTauberian

/-- The squared-sinc smoothing of the normalized model profile is integrable at each center. -/
theorem integrableOn_delangeWeight_mul_pow_mul_squaredSinc (k : ℕ) (ell T : ℝ) :
    IntegrableOn (fun t ↦ delangeWeight k t * t ^ k * squaredSinc ell (t - T)) (Ioi 0) := by
  have hkernel : Integrable (fun t ↦ squaredSinc ell (t - T)) :=
    (measurePreserving_sub_right volume T).integrable_comp_of_integrable
      (integrable_squaredSinc ell)
  have hmodel : Continuous (fun t : ℝ ↦ delangeWeight k t * t ^ k) :=
    (continuous_delangeWeight k).mul (continuous_id.pow k)
  refine (hkernel.integrableOn (s := Ioi 0)).bdd_mul (c := 1) hmodel.aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t (ht : 0 < t)
  rw [Real.norm_of_nonneg (mul_nonneg (delangeWeight_nonneg ht.le) (pow_nonneg ht.le _))]
  exact (delangeWeight_mul_pow_lt_one ht.le).le

/-- A finite boundary limit of the damped, model-subtracted Delange smoothing establishes
integrability of the undamped smoothed function and identifies the limit. Here `C` is the
coefficient of the normalized model `t ↦ wₖ(t) tᵏ`, equal to `A / k!` for leading coefficient
`A` of the pole. -/
theorem integrableOn_and_integral_delangeWeight_mul_sub_mul_pow_mul_squaredSinc_eq_of_tendsto
    {α : ℝ → ℝ} {a C ell T L : ℝ} (k : ℕ)
    (hα : 0 ≤ᵐ[volume.restrict (Ioi 0)] α)
    (hd : ∀ᶠ ε : ℝ in 𝓝[>] 0, IntegrableOn
      (fun t ↦ Real.exp (-ε * t) *
        ((delangeWeight k t * Real.exp (-a * t) * α t - C * (delangeWeight k t * t ^ k)) *
          squaredSinc ell (t - T))) (Ioi 0))
    (hlim : Tendsto (fun ε : ℝ ↦ ∫ t in Ioi 0, Real.exp (-ε * t) *
      ((delangeWeight k t * Real.exp (-a * t) * α t - C * (delangeWeight k t * t ^ k)) *
        squaredSinc ell (t - T))) (𝓝[>] 0) (𝓝 L)) :
    IntegrableOn (fun t ↦ delangeWeight k t * Real.exp (-a * t) * α t *
      squaredSinc ell (t - T)) (Ioi 0) ∧
    (∫ t in Ioi 0, (delangeWeight k t * Real.exp (-a * t) * α t -
      C * (delangeWeight k t * t ^ k)) * squaredSinc ell (t - T)) = L := by
  by_cases hzero : ell = 0
  · subst ell
    simp only [squaredSinc_zero_left, mul_zero, integral_zero] at hlim ⊢
    exact ⟨integrableOn_zero, tendsto_nhds_unique tendsto_const_nhds hlim⟩
  -- Scaling by the bandwidth makes the kernel nonnegative for either sign.
  have hf : 0 ≤ᵐ[volume.restrict (Ioi 0)] (fun t ↦
      ell * (delangeWeight k t * Real.exp (-a * t) * α t * squaredSinc ell (t - T))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi, hα] with t (ht : 0 < t) hαt
    have hkernel : 0 ≤ ell * squaredSinc ell (t - T) := by
      rw [squaredSinc_def, ← mul_assoc, ← mul_div_assoc, ← sq]
      positivity
    rw [mul_left_comm ell]
    exact mul_nonneg (mul_nonneg (mul_nonneg (delangeWeight_nonneg ht.le)
      (Real.exp_pos _).le) hαt) hkernel
  have hg : IntegrableOn (fun t ↦ (C * (delangeWeight k t * t ^ k)) *
      squaredSinc ell (t - T)) (Ioi 0) := by
    have hmodel := integrableOn_delangeWeight_mul_pow_mul_squaredSinc k ell T
    simpa only [IntegrableOn, mul_assoc] using hmodel.const_mul C
  simp only [sub_mul] at hd hlim ⊢
  have hscale (x y z : ℝ) : x * (ell * y - ell * z) = ell * (x * (y - z)) := by ring
  have hlim' := hlim.const_mul ell
  simp only [← integral_const_mul] at hlim'
  obtain ⟨hi, heq⟩ := integrableOn_and_integral_sub_eq_of_tendsto_exp_neg_mul hf
    (hg.const_mul ell) (hd.mono fun ε h ↦ (h.const_mul ell).congr
      (.of_forall fun t ↦ (hscale _ _ _).symm))
    (by simpa only [hscale] using hlim')
  simp only [← mul_sub, integral_const_mul] at heq
  exact ⟨(integrable_const_mul_iff (isUnit_iff_ne_zero.mpr hzero) _).mp hi,
    (mul_right_inj' hzero).mp heq⟩

end TauCeti.HigherPoleTauberian
