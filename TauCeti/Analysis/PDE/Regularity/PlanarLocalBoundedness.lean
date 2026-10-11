/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Regularity.LocalBoundedness
import TauCeti.Analysis.Sobolev.Trudinger
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Topology.Sets.Opens

/-!
# Local boundedness of planar weak subsolutions

The two-dimensional borderline Sobolev inequality places compactly supported `W^{1,2}` functions
in every finite `Lᵖ` space. Taking `p = 4` supplies the Sobolev input to De Giorgi's local
boundedness iteration. This file records the resulting local estimate on unit balls for weak
subsolutions with measurable, uniformly elliptic coefficients.

The estimate is one step toward the two-dimensional De Giorgi–Nash–Moser theory. It does not yet
give a scale-invariant bound on balls of arbitrary radius or the Hölder estimate.

## References

* E. De Giorgi, *Sulla differenziabilità e l'analiticità delle estremali degli integrali
  multipli regolari*, Mem. Accad. Sci. Torino (1957).
* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Chapter 8.
-/

public section

noncomputable section

open MeasureTheory Matrix Module Set TopologicalSpace
open scoped ENNReal Gradient InnerProductSpace NNReal

namespace TauCeti.PDE

variable {mu : Measure (EuclideanSpace ℝ (Fin 2))} [mu.IsAddHaarMeasure]
  {lam Lam : ℝ}

/-- **Planar local boundedness of weak subsolutions.** There is a constant `D`, depending only on
the ellipticity constants and the normalization of `μ`, such that if `u` is a weak subsolution of
`-div(a ∇u) ≤ 0` on the ball `B(x₀, 2)`, then for every level `k`, `u ≤ k + D ‖(u-k)⁺‖₂` almost
everywhere on `B(x₀, 1/2)`. The estimate uses the `L⁴` Sobolev bound furnished by the borderline
embedding in dimension two. -/
theorem exists_ae_value_le_add_mul_sqrt_setIntegral_ball_half
    : ∃ D : ℝ, 0 < D ∧ ∀ {Omega : Opens (EuclideanSpace ℝ (Fin 2))}
      {a : EuclideanSpace ℝ (Fin 2) → Matrix (Fin 2) (Fin 2) ℝ}
      {u : W1p mu Omega 2} {x₀ : EuclideanSpace ℝ (Fin 2)} {k : ℝ},
      UniformlyEllipticOn (Metric.ball x₀ 2) a lam Lam →
      AEStronglyMeasurable a (mu.restrict (Metric.ball x₀ 2)) →
      (∀ v : W1p0 mu Omega 2,
        (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (v : W1p mu Omega 2) x) →
          energyFormH1 a 0 0 u (v : W1p mu Omega 2) ≤ 0) →
      Metric.ball x₀ 2 ⊆ (Omega : Set (EuclideanSpace ℝ (Fin 2))) →
      ∀ᵐ x ∂mu.restrict (Metric.ball x₀ (1 / 2)),
        W1p.value u x ≤ k + D *
          √(∫ y in Metric.ball x₀ 1, max (W1p.value u y - k) 0 ^ 2 ∂mu) := by
  let C : ℝ≥0∞ := ENNReal.ofReal
      ((finrank ℝ (EuclideanSpace ℝ (Fin 2)) : ℝ)⁻¹ *
        mu.real (Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1) ^
          (-(finrank ℝ (EuclideanSpace ℝ (Fin 2)) : ℝ)⁻¹) *
        ((4 : ℝ≥0) * (1 - (finrank ℝ (EuclideanSpace ℝ (Fin 2)) : ℝ)⁻¹) + 1) ^
          (1 - (finrank ℝ (EuclideanSpace ℝ (Fin 2)) : ℝ)⁻¹ + (4 : ℝ≥0)⁻¹)) *
    mu (Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 2) ^ ((4 : ℝ≥0)⁻¹ : ℝ)
  have hC : C ≠ ∞ := by
    dsimp [C]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.rpow_ne_top_of_nonneg (by norm_num) measure_ball_lt_top.ne)
  let S : ℝ≥0 := C.toNNReal
  obtain ⟨D, hD, hlocal⟩ := exists_ae_value_le_add_mul_rpow_mul_sqrt_setIntegral
    (mu := mu) (lam := lam) (Lam := Lam) (q := 4) (by norm_num) S
  refine ⟨D, hD, fun {Omega a u x₀ k} h ha hu hball => ?_⟩
  let U : Opens (EuclideanSpace ℝ (Fin 2)) := ⟨Metric.ball x₀ 2, Metric.isOpen_ball⟩
  have hU : U ≤ Omega := hball
  have hfinite : mu (U : Set (EuclideanSpace ℝ (Fin 2))) ≠ ∞ := by
    change mu (Metric.ball x₀ 2) ≠ ∞
    exact measure_ball_lt_top.ne
  have hS : ∀ v ∈ w1p0Submodule mu U 2,
      eLpNorm (W1p.value v) 4 (mu.restrict U) ≤ S * ‖W1p.gradient v‖ₑ := by
    intro v hv
    have hsob := W1p.eLpNorm_value_le_mul_measure_rpow_mul_enorm_gradient
      (mu := mu) (Omega := U) (p := 2) (q := 4) (by norm_num) hfinite
      (by norm_num : (finrank ℝ (EuclideanSpace ℝ (Fin 2)) : ℝ≥0) ≤ 4) hv
    have hsob' : eLpNorm (W1p.value v) 4 (mu.restrict U) ≤
        C * ‖W1p.gradient v‖ₑ := by
      simpa [C, U, Measure.addHaar_ball_center] using hsob
    simpa only [S, ENNReal.coe_toNNReal hC] using hsob'
  have hrestrict : W1p.value (W1p.restrictL hU u) =ᵐ[mu.restrict U] W1p.value u :=
    W1p.value_restrictL_ae hU u
  have hrestrict' : W1p.value (W1p.restrictL hU u) =ᵐ[mu.restrict (Metric.ball x₀ 2)]
      W1p.value u := by
    simpa [U] using hrestrict
  have hball1 : Metric.ball x₀ 1 ⊆ (U : Set (EuclideanSpace ℝ (Fin 2))) := by
    simpa [U] using Metric.ball_subset_ball (by norm_num : (1 : ℝ) ≤ 2)
  have hbound := hlocal (k := k) (by simpa [U] using h) (by simpa [U] using ha) hS
    (energyFormH1_restrictL_nonpos hU hu) (by norm_num : (0 : ℝ) < 1) hball1
  have hballMeasure : ∫ y in Metric.ball x₀ 1,
      max (W1p.value (W1p.restrictL hU u) y - k) 0 ^ 2 ∂mu =
      ∫ y in Metric.ball x₀ 1, max (W1p.value u y - k) 0 ^ 2 ∂mu := by
    refine integral_congr_ae ?_
    filter_upwards [ae_restrict_of_ae_restrict_of_subset
      (Metric.ball_subset_ball (by norm_num : (1 : ℝ) ≤ 2)) hrestrict'] with y hy
    rw [hy]
  filter_upwards [hbound, ae_restrict_of_ae_restrict_of_subset
    (Metric.ball_subset_ball (by norm_num : (1 / 2 : ℝ) ≤ 2)) hrestrict'] with y hy hyu
  calc
    W1p.value u y = W1p.value (W1p.restrictL hU u) y := hyu.symm
    _ ≤ k + D * √(∫ z in Metric.ball x₀ 1,
          max (W1p.value (W1p.restrictL hU u) z - k) 0 ^ 2 ∂mu) := by simpa using hy
    _ = k + D * √(∫ z in Metric.ball x₀ 1,
          max (W1p.value u z - k) 0 ^ 2 ∂mu) := by rw [hballMeasure]

end TauCeti.PDE
