/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.RicciFlow.StandardCap.PuncturedMetric

/-!
# Sectional curvature of the punctured standard cap

Every standard cap profile gives a punctured cap with nonnegative sectional curvature
on all tangent planes. Concavity controls the radial Hessian, and the slope bound
`0 ≤ f' ≤ 1` controls the vertical curvature correction to the round sphere.
Near the missing tip the profile is `2 sin (r / 2)`, and every tangent plane has sectional
curvature `1/4`, that of the round sphere of radius `2`.
The conclusion concerns the native Levi-Civita connection of the constructed metric.
Smooth extension across the missing tip and metric completeness are separate questions.

## References

* J. Morgan and G. Tian, *Ricci Flow and the Poincaré Conjecture* (2007), Definition 12.1.
* B. O'Neill, *Semi-Riemannian Geometry* (1983), Chapter 7, Proposition 42.
-/

public noncomputable section

open Bundle CovariantDerivative
open TauCeti.Manifold
open scoped ContDiff InnerProductSpace Manifold

namespace TauCeti.IsStandardCapProfile

variable {f : ℝ → ℝ} (hf : IsStandardCapProfile f)
  {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {n : ℕ}
  [Fact (Module.finrank ℝ V = n + 1)]

/-- The punctured standard cap has nonnegative sectional curvature on every tangent
plane, in any sphere dimension. The assertion includes dependent spanning vectors. -/
theorem sectionalCurvature_puncturedMetric_nonneg
    (p : standardCapRadialDomain × Metric.sphere (0 : V) 1)
    (u v : TangentSpace (𝓘(ℝ).prod (𝓡 n)) p) :
    letI : RiemannianBundle (fun q : standardCapRadialDomain × Metric.sphere (0 : V) 1 ↦
      TangentSpace (𝓘(ℝ).prod (𝓡 n)) q) := ⟨(hf.puncturedMetric (n := n) V).toRiemannianMetric⟩
    0 ≤ (leviCivitaConnection (𝓘(ℝ).prod (𝓡 n))
      (standardCapRadialDomain × Metric.sphere (0 : V) 1)).sectionalCurvature
      (isMetricCompatible_leviCivitaConnection (𝓘(ℝ).prod (𝓡 n))) p u v := by
  rw [hf.puncturedMetric_def]
  apply sectionalCurvature_warpedProdTangentSpace_real_sphere_nonneg (n := n)
    standardCapRadialDomain
    (hf.contDiff.contMDiff.comp contMDiff_subtypeVal)
    (fun r ↦ (hf.apply_pos r.property).ne') p
  · exact mul_nonpos_of_nonneg_of_nonpos (hf.apply_nonneg p.1.property.le)
      (hf.deriv_deriv_nonpos p.1.property.le)
  · have h₀ := hf.deriv_nonneg p.1.property.le
    have h₁ := hf.deriv_le_one p.1.property.le
    nlinarith

/-- Near its missing tip, the punctured standard cap has sectional curvature `1/4` on every
tangent plane, in any sphere dimension: there the profile is `2 sin (r / 2)`, and the metric is
that of the round sphere of radius `2`. -/
theorem exists_hasSectionalCurvatureAt_puncturedMetric_round :
    ∃ r₀ > 0, ∀ p : standardCapRadialDomain × Metric.sphere (0 : V) 1, (p.1 : ℝ) < r₀ →
      letI : RiemannianBundle (fun q : standardCapRadialDomain × Metric.sphere (0 : V) 1 ↦
        TangentSpace (𝓘(ℝ).prod (𝓡 n)) q) :=
        ⟨(hf.puncturedMetric (n := n) V).toRiemannianMetric⟩
      (leviCivitaConnection (𝓘(ℝ).prod (𝓡 n))
        (standardCapRadialDomain × Metric.sphere (0 : V) 1)).HasSectionalCurvatureAt
        (isMetricCompatible_leviCivitaConnection (𝓘(ℝ).prod (𝓡 n))) p (1 / 4) := by
  obtain ⟨r₀, hr₀, h⟩ :=
    hf.exists_eq_two_mul_sin_and_deriv_eq_cos_and_deriv_deriv_eq_neg_sin_div_two
  refine ⟨r₀, hr₀, fun p hp ↦ ?_⟩
  obtain ⟨h₀, h₁, h₂⟩ := h p.1 ⟨p.1.property.le, hp⟩
  rw [hf.puncturedMetric_def]
  apply hasSectionalCurvatureAt_warpedProdTangentSpace_real_sphere (n := n)
    standardCapRadialDomain
  · rw [h₀, h₂]
    ring
  · rw [h₀, h₁]
    linear_combination Real.sin_sq_add_cos_sq ((p.1 : ℝ) / 2)

end TauCeti.IsStandardCapProfile
