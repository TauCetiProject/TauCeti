/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Caccioppoli.Basic
public import TauCeti.Analysis.PDE.EnergyForm.Restriction

/-!
# Interior L² gradient bounds from the homogeneous weak equation

For a uniformly elliptic measurable coefficient field, a genuine H¹ weak solution of the
homogeneous divergence equation has its gradient L² norm on an inner ball bounded by its
value L² norm on a larger concentric ball. The dimensional constant is fixed before the
coefficient field, solution, ambient open domain, measure and radii are chosen. Both norms
are those of the native Sobolev restrictions.

## References

* L. C. Evans, *Partial Differential Equations*, Chapter 6, §6.3.
-/

public noncomputable section

open MeasureTheory Metric Set TopologicalSpace
open scoped ContDiff Gradient InnerProductSpace

namespace TauCeti.PDE

variable {ι : Type*} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι

private theorem integral_gradient_restrictL_ball_eq
    {μ : Measure E} [μ.IsAddHaarMeasure] {Ω : Opens E} {p : E} {r : ℝ}
    (hB : (⟨ball p r, isOpen_ball⟩ : Opens E) ≤ Ω) (w : W1p μ Ω 2) :
    ∫ x in ball p r, ‖W1p.gradient w x‖ ^ 2 ∂μ =
      ‖W1p.gradient (W1p.restrictL hB w)‖ ^ 2 := by
  rw [← W1p.integral_norm_gradient_sq_eq_norm_gradient_sq]
  refine integral_congr_ae ?_
  filter_upwards [W1p.gradient_restrictL_ae hB w] with x hx
  rw [hx]

private theorem integral_value_restrictL_ball_eq
    {μ : Measure E} [μ.IsAddHaarMeasure] {Ω : Opens E} {p : E} {r : ℝ}
    (hB : (⟨ball p r, isOpen_ball⟩ : Opens E) ≤ Ω) (w : W1p μ Ω 2) :
    ∫ x in ball p r, W1p.value w x ^ 2 ∂μ =
      ‖W1p.value (W1p.restrictL hB w)‖ ^ 2 := by
  rw [← W1p.integral_value_sq_eq_norm_value_sq]
  refine integral_congr_ae ?_
  filter_upwards [W1p.value_restrictL_ae hB w] with x hx
  rw [hx]

variable [DecidableEq ι]

/-- Homogeneous uniformly elliptic weak solutions satisfy an interior L² gradient bound on
native Sobolev restrictions, with a dimensional constant independent of the coefficients. -/
theorem exists_norm_gradient_restrictL_ball_le :
    ∃ c : ℝ, 0 < c ∧ ∀ {μ : Measure E} [μ.IsAddHaarMeasure] {Ω : Opens E}
      {a : E → Matrix ι ι ℝ} {lam Lam : ℝ} {w : W1p μ Ω 2} {p : E} {ρ R : ℝ},
      UniformlyEllipticOn (Ω : Set E) a lam Lam →
      AEStronglyMeasurable a (μ.restrict Ω) →
      (∀ v : W1p0 μ Ω 2, energyFormH1 a 0 0 w (v : W1p μ Ω 2) = 0) →
      ∀ (hρR : ρ < R) (hR : (⟨ball p R, isOpen_ball⟩ : Opens E) ≤ Ω),
      ‖W1p.gradient (W1p.restrictL
        (show (⟨ball p ρ, isOpen_ball⟩ : Opens E) ≤ Ω from
          (ball_subset_ball hρR.le).trans hR) w)‖ ≤
        (2 * Lam / lam) * c / (R - ρ) * ‖W1p.value (W1p.restrictL hR w)‖ := by
  classical
  obtain ⟨c, hc, hC⟩ := exists_setIntegral_ball_norm_gradient_sq_le_of_cutoff (ι := ι)
  refine ⟨c, hc, ?_⟩
  intro μ _ Ω a lam Lam w p ρ R hell ha hw hρR hR
  have hbound := hC w (A := (2 * Lam / lam) ^ 2) (B := 0) (x₀ := p)
    (r := ρ) (R := R) (sq_nonneg _) le_rfl hρR hR (fun ψ hψ hcpt hts ↦ by
      obtain ⟨v, -, -, hstep⟩ :=
        hell.exists_setIntegral_sq_mul_norm_gradient_sq_le_energyFormH1 ha w hψ hcpt (.inl hts)
      simpa only [hw v, mul_zero, add_zero, zero_mul] using hstep)
  rw [integral_gradient_restrictL_ball_eq ((ball_subset_ball hρR.le).trans hR) w,
    integral_value_restrictL_ball_eq hR w] at hbound
  simp only [add_zero] at hbound
  have hlam := hell.pos
  have hLam := hell.upper_nonneg
  have hgap : 0 < R - ρ := sub_pos.mpr hρR
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  calc
    _ ≤ _ := hbound
    _ = _ := by ring

end TauCeti.PDE
