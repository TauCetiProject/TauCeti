/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.RicciFlow.StandardCap.PuncturedMetric
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.WarpedProd.Nonnegative
import TauCeti.Geometry.Manifold.Riemannian.Restriction.Real

/-!
# Nonnegative sectional curvature of the punctured standard cap

Every standard cap profile gives a punctured cap with nonnegative sectional curvature
on all tangent planes. Concavity controls the radial Hessian, and the slope bound
`0 ≤ f' ≤ 1` controls the vertical curvature correction to the round sphere.
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
  (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V] {n : ℕ}
  [Fact (Module.finrank ℝ V = n + 1)]

/-- The punctured standard cap has nonnegative sectional curvature on every tangent
plane, in any sphere dimension. The assertion includes dependent spanning vectors. -/
theorem sectionalCurvature_puncturedMetric_nonneg
    (p : standardCapRadialDomain × Metric.sphere (0 : V) 1)
    (u v : TangentSpace (𝓘(ℝ).prod (𝓡 n)) p) :
    let : RiemannianBundle (fun q : standardCapRadialDomain × Metric.sphere (0 : V) 1 ↦
      TangentSpace (𝓘(ℝ).prod (𝓡 n)) q) := ⟨(hf.puncturedMetric (n := n) V).toRiemannianMetric⟩
    0 ≤ (leviCivitaConnection (𝓘(ℝ).prod (𝓡 n))
      (standardCapRadialDomain × Metric.sphere (0 : V) 1)).sectionalCurvature
      (isMetricCompatible_leviCivitaConnection (𝓘(ℝ).prod (𝓡 n))) p u v := by
  dsimp only
  let g := (riemannianMetricVectorSpace ℝ).ofLE (m := ∞) le_top
  let g₁ := g.restrictOpenTangentSpace standardCapRadialDomain
  let g₂ := (sphereRoundMetric (E := V) (n := n)).ofLE (m := ∞) le_top
  let : RiemannianBundle (fun r : standardCapRadialDomain ↦ TangentSpace 𝓘(ℝ) r) :=
    ⟨g₁.toRiemannianMetric⟩
  let : RiemannianBundle (fun s : Metric.sphere (0 : V) 1 ↦ TangentSpace (𝓡 n) s) :=
    ⟨g₂.toRiemannianMetric⟩
  let : RiemannianBundle (fun q : standardCapRadialDomain × Metric.sphere (0 : V) 1 ↦
    TangentSpace (𝓘(ℝ).prod (𝓡 n)) q) := ⟨(hf.puncturedMetric (n := n) V).toRiemannianMetric⟩
  have h : IsWarpedProduct 𝓘(ℝ) (𝓡 n) (Metric.sphere (0 : V) 1)
      (fun r : standardCapRadialDomain ↦ f r) :=
    ⟨fun q a b ↦ hf.puncturedMetric_inner q a b⟩
  apply h.sectionalCurvature_nonneg_of_finrank_eq_one
    (hf.contDiff.contMDiff.comp contMDiff_subtype_val) (by simp) p (hf.apply_pos p.1.property)
  · rw [laplaceBeltrami_restrictOpenTangentSpace_real_eq_deriv_deriv
      standardCapRadialDomain (hf.contDiff.contDiffAt.of_le (by simp))]
    exact hf.deriv_deriv_nonpos p.1.property.le
  · intro a b
    have hR := g₂.isConstantCurvatureTensor_iff 1 |>.mp
      isConstantCurvatureTensor_sphereRoundMetric_ofLE p.2 a b b
    rw [hR, one_smul]
    simp only [inner_sub_left, real_inner_smul_left]
    rw [sq_norm_mgradient_restrictOpenTangentSpace_real_eq_sq_deriv
      standardCapRadialDomain (hf.differentiable _), Matrix.real_det_gram_fin_two]
    have h₀ := hf.deriv_nonneg p.1.property.le
    have h₁ := hf.deriv_le_one p.1.property.le
    have hgram := (Matrix.posSemidef_gram ℝ ![a, b]).det_nonneg
    rw [Matrix.real_det_gram_fin_two] at hgram
    have hsq : deriv f p.1 ^ 2 ≤ 1 := by nlinarith
    have hbound := mul_le_mul_of_nonneg_right hsq hgram
    simp only [real_inner_comm b a] at *
    nlinarith

end TauCeti.IsStandardCapProfile
