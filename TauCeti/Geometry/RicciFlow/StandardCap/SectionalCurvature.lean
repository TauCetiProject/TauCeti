/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.RicciFlow.StandardCap.PuncturedMetric

/-!
# Sectional curvature of the punctured standard cap

Every standard cap profile `f` gives a punctured cap whose mixed radial-spherical tangent planes
have sectional curvature `-f''(r) / f(r)` and whose vertical spherical tangent planes have
sectional curvature `(1 - f'(r)²) / f(r)²`. Concavity controls the radial Hessian, and the slope
bound `0 ≤ f' ≤ 1` controls the vertical curvature correction to the round sphere, so every tangent
plane (including tilted planes) has nonnegative sectional curvature, and near the missing tip the
sectional curvature is identically `1 / 4`. Smooth extension across the missing tip and metric
completeness are established in `TauCeti.Geometry.RicciFlow.StandardCap.Metric`.

## Main results

* `TauCeti.IsStandardCapProfile.sectionalCurvature_puncturedMetric_mixed`,
  `TauCeti.IsStandardCapProfile.sectionalCurvature_puncturedMetric_vertical`: sectional curvature
  of mixed and vertical two-planes on the punctured cap.
* `TauCeti.IsStandardCapProfile.sectionalCurvature_puncturedMetric_nonneg`: nonnegativity on all
  tangent planes (including dependent pairs).
* `TauCeti.IsStandardCapProfile.exists_hasSectionalCurvatureAt_puncturedMetric_round`: constant
  sectional curvature `1 / 4` near the missing tip.

## References

* J. Morgan and G. Tian, *Ricci Flow and the Poincaré Conjecture* (2007), Definition 12.1.
* B. O'Neill, *Semi-Riemannian Geometry* (1983), Chapter 7, Proposition 42.
-/

public noncomputable section

open Bundle CovariantDerivative Real
open TauCeti.Manifold
open scoped ContDiff InnerProductSpace Manifold

namespace TauCeti.IsStandardCapProfile

variable {f : ℝ → ℝ} (hf : IsStandardCapProfile f)
  {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {n : ℕ}
  [Fact (Module.finrank ℝ V = n + 1)]
include hf

private theorem puncturedMetric_eq :
    hf.puncturedMetric (n := n) V =
      (((riemannianMetricVectorSpace ℝ).ofLE (m := ∞) le_top).restrictOpenTangentSpace
        standardCapRadialDomain).warpedProdTangentSpace (fun r ↦ f r)
        (hf.contDiff.contMDiff.comp contMDiff_subtype_val)
        (fun r ↦ (hf.apply_pos r.property).ne')
        ((sphereRoundMetric (E := V) (n := n)).ofLE (m := ∞) le_top) := by
  ext q a b
  rw [hf.puncturedMetric_inner, ContMDiffRiemannianMetric.warpedProdTangentSpace_inner]

/-- Mixed radial-spherical tangent planes of the punctured standard cap have sectional
curvature `-f''(r) / f(r)`. Both spanning vectors must be nonzero. -/
theorem sectionalCurvature_puncturedMetric_mixed
    (p : standardCapRadialDomain × Metric.sphere (0 : V) 1)
    (u : TangentSpace 𝓘(ℝ) p.1) (v : TangentSpace (𝓡 n) p.2) (hu : u ≠ 0) (hv : v ≠ 0) :
    letI : RiemannianBundle
      (fun q : standardCapRadialDomain × Metric.sphere (0 : V) 1 ↦
        TangentSpace (𝓘(ℝ).prod (𝓡 n)) q) :=
      ⟨(hf.puncturedMetric (n := n) V).toRiemannianMetric⟩
    (leviCivitaConnection (𝓘(ℝ).prod (𝓡 n))
        (standardCapRadialDomain × Metric.sphere (0 : V) 1)).sectionalCurvature
      (isMetricCompatible_leviCivitaConnection (𝓘(ℝ).prod (𝓡 n))) p
      ((tangentSpaceProdEquiv p).symm (u, 0))
      ((tangentSpaceProdEquiv p).symm (0, v)) =
      -deriv (deriv f) p.1 / f p.1 := by
  rw [hf.puncturedMetric_eq]
  exact sectionalCurvature_warpedProdTangentSpace_real_sphere_mixed standardCapRadialDomain
    (hf.contDiff.contMDiff.comp contMDiff_subtype_val)
    (fun r ↦ (hf.apply_pos r.property).ne') p u v hu hv

/-- Vertical spherical tangent planes of the punctured standard cap have sectional
curvature `(1 - f'(r)²) / f(r)²`. -/
theorem sectionalCurvature_puncturedMetric_vertical
    (p : standardCapRadialDomain × Metric.sphere (0 : V) 1)
    (v w : TangentSpace (𝓡 n) p.2) (hvw : LinearIndependent ℝ ![v, w]) :
    letI : RiemannianBundle
      (fun q : standardCapRadialDomain × Metric.sphere (0 : V) 1 ↦
        TangentSpace (𝓘(ℝ).prod (𝓡 n)) q) :=
      ⟨(hf.puncturedMetric (n := n) V).toRiemannianMetric⟩
    (leviCivitaConnection (𝓘(ℝ).prod (𝓡 n))
        (standardCapRadialDomain × Metric.sphere (0 : V) 1)).sectionalCurvature
      (isMetricCompatible_leviCivitaConnection (𝓘(ℝ).prod (𝓡 n))) p
      ((tangentSpaceProdEquiv p).symm (0, v))
      ((tangentSpaceProdEquiv p).symm (0, w)) =
      (1 - deriv f p.1 ^ 2) / f p.1 ^ 2 := by
  rw [hf.puncturedMetric_eq]
  exact sectionalCurvature_warpedProdTangentSpace_real_sphere_vertical standardCapRadialDomain
    (hf.contDiff.contMDiff.comp contMDiff_subtype_val)
    (fun r ↦ (hf.apply_pos r.property).ne') p v w hvw

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
  rw [hf.puncturedMetric_eq]
  apply sectionalCurvature_warpedProdTangentSpace_real_sphere_nonneg (n := n)
    standardCapRadialDomain
    (hf.contDiff.contMDiff.comp contMDiff_subtype_val)
    (fun r ↦ (hf.apply_pos r.property).ne') p
  · exact mul_nonpos_of_nonneg_of_nonpos (hf.apply_nonneg p.1.property.le)
      (hf.deriv_deriv_nonpos p.1.property.le)
  · have h₀ := hf.deriv_nonneg p.1.property.le
    have h₁ := hf.deriv_le_one p.1.property.le
    nlinarith

/-- Near its missing tip, the punctured standard cap has constant sectional curvature `1 / 4`,
the sectional curvature of the round sphere of radius `2`. -/
theorem exists_hasSectionalCurvatureAt_puncturedMetric_round :
    letI : RiemannianBundle
      (fun q : standardCapRadialDomain × Metric.sphere (0 : V) 1 ↦
        TangentSpace (𝓘(ℝ).prod (𝓡 n)) q) :=
      ⟨(hf.puncturedMetric (n := n) V).toRiemannianMetric⟩
    ∃ r₀ > 0, ∀ p : standardCapRadialDomain × Metric.sphere (0 : V) 1,
      (p.1 : ℝ) < r₀ →
      (leviCivitaConnection (𝓘(ℝ).prod (𝓡 n))
          (standardCapRadialDomain × Metric.sphere (0 : V) 1)).HasSectionalCurvatureAt
        (isMetricCompatible_leviCivitaConnection (𝓘(ℝ).prod (𝓡 n))) p (1 / 4) := by
  obtain ⟨r₀, hr₀, h⟩ := hf.exists_eq_two_mul_sin_and_deriv
  refine ⟨r₀, hr₀, fun p hp ↦ ?_⟩
  obtain ⟨hf0, hd, hdd⟩ := h p.1 (by rwa [abs_of_pos p.1.property])
  have hsin : sin ((p.1 : ℝ) / 2) ≠ 0 := by
    intro h0; exact (hf.apply_pos p.1.property).ne' (by rw [hf0, h0, mul_zero])
  have htrig : 1 - cos ((p.1 : ℝ) / 2) ^ 2 = sin ((p.1 : ℝ) / 2) ^ 2 := by
    nlinarith [sin_sq_add_cos_sq ((p.1 : ℝ) / 2)]
  rw [hf.puncturedMetric_eq]
  apply hasSectionalCurvatureAt_warpedProdTangentSpace_real_sphere standardCapRadialDomain
    (hf.contDiff.contMDiff.comp contMDiff_subtype_val)
    (fun r ↦ (hf.apply_pos r.property).ne') p
  · rw [hf0, hdd]; field_simp; ring
  · rw [hf0, hd, htrig]; field_simp; ring

end TauCeti.IsStandardCapProfile
