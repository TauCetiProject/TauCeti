/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.ConformallyFlat.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Weyl.Solvability
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Weyl.Divergence
import TauCeti.Geometry.Manifold.IsManifold.Basic

/-!
# Weyl–Schouten on a model space

For an arbitrary smooth Riemannian metric on a finite-dimensional real normed space, vanishing
Weyl and Cotton tensors near a point give a positive smooth conformal factor making the metric
flat near that point. The exponent `φ` can have any prescribed value and gradient at
the point. This uses the local solutions of the conformal flattening equation from
`TauCeti.Manifold.exists_eventually_hessian_eq_model_space` and the curvature decomposition into
Weyl and Schouten tensors.

Consequently a smooth metric on a model space of dimension at least four is locally conformally
flat if and only if its Weyl tensor vanishes. In dimension three the corresponding criterion is
vanishing Cotton tensor: Weyl vanishes identically in that dimension. In higher dimensions the
Cotton condition follows from the divergence identity `div W = (dim M - 3) C`.

These statements concern arbitrary variable metrics on the model space, rather than only the
Euclidean metric. Local conformal flatness here means existence of a flat conformal rescaling;
no Euclidean coordinate isometry is assumed.

## References

* A. L. Besse, *Einstein Manifolds*, Springer (1987), Section 1.G.
* J. M. Lee and T. H. Parker, *The Yamabe problem*, Bull. Amer. Math. Soc. 17 (1987), Section 2.
-/

public section

open Bundle Filter TauCeti.Manifold
open scoped ContDiff Manifold Topology

noncomputable section

namespace Bundle.ContMDiffRiemannianMetric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- Where Weyl and Cotton vanish, a smooth metric on a model space has a flat conformal
rescaling `e^(2φ) g` near the point, with arbitrary prescribed value and gradient of `φ`. -/
theorem exists_eventually_curvatureTensor_rescale_exp_eq_zero_model_space
    (g : ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E (fun x : E ↦ TangentSpace 𝓘(ℝ, E) x))
    (hn : 3 ≤ Module.finrank ℝ E) {x : E}
    (hW : ∀ᶠ y in 𝓝 x, (letI : RiemannianBundle (fun x : E ↦ TangentSpace 𝓘(ℝ, E) x) :=
      ⟨g.toRiemannianMetric⟩;
      (CovariantDerivative.leviCivitaConnection 𝓘(ℝ, E) E).weylTensor y) = 0)
    (hC : ∀ᶠ y in 𝓝 x, (letI : RiemannianBundle (fun x : E ↦ TangentSpace 𝓘(ℝ, E) x) :=
      ⟨g.toRiemannianMetric⟩;
      (CovariantDerivative.leviCivitaConnection 𝓘(ℝ, E) E).cottonTensor y) = 0)
    (c : ℝ) (ξ : TangentSpace 𝓘(ℝ, E) x) :
    ∃ (φ : E → ℝ) (hφ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ φ), φ x = c ∧
      (letI : RiemannianBundle (fun x : E ↦ TangentSpace 𝓘(ℝ, E) x) := ⟨g.toRiemannianMetric⟩;
        mgradient 𝓘(ℝ, E) φ x = ξ) ∧
      ∀ᶠ y in 𝓝 x,
        (letI : RiemannianBundle (fun x : E ↦ TangentSpace 𝓘(ℝ, E) x) :=
          ⟨(g.rescale (fun z ↦ Real.exp (2 * φ z))
            (Real.contDiff_exp.comp_contMDiff (contMDiff_const.mul hφ))
            (fun _ ↦ Real.exp_pos _)).toRiemannianMetric⟩;
          (CovariantDerivative.leviCivitaConnection 𝓘(ℝ, E) E).curvatureTensor y) = 0 := by
  obtain ⟨φ, hφ, hvalue, hgrad, hsol⟩ :=
    (letI : RiemannianBundle (fun x : E ↦ TangentSpace 𝓘(ℝ, E) x) := ⟨g.toRiemannianMetric⟩;
      exists_eventually_hessian_eq_model_space hW hC c ξ)
  refine ⟨φ, hφ, hvalue, hgrad, ?_⟩
  filter_upwards [hW, hsol] with y hyW hy
  exact (g.curvatureTensor_leviCivitaConnection_rescale_eq_zero_iff
    (Real.contDiff_exp.comp_contMDiff (contMDiff_const.mul hφ)) (fun _ ↦ Real.exp_pos _)
    (fun _ ↦ rfl) hn y).2 ⟨hyW, hy⟩

/-- A smooth metric on a model space of dimension at least three is locally conformally flat
exactly when its Weyl and Cotton tensors both vanish. -/
theorem isLocallyConformallyFlat_iff_weylTensor_eq_zero_and_cottonTensor_eq_zero_model_space
    (g : ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E (fun x : E ↦ TangentSpace 𝓘(ℝ, E) x))
    (hn : 3 ≤ Module.finrank ℝ E) :
    g.IsLocallyConformallyFlat ↔
      (letI : RiemannianBundle (fun x : E ↦ TangentSpace 𝓘(ℝ, E) x) := ⟨g.toRiemannianMetric⟩;
        ∀ x, (CovariantDerivative.leviCivitaConnection 𝓘(ℝ, E) E).weylTensor x = 0) ∧
      (letI : RiemannianBundle (fun x : E ↦ TangentSpace 𝓘(ℝ, E) x) := ⟨g.toRiemannianMetric⟩;
        ∀ x, (CovariantDerivative.leviCivitaConnection 𝓘(ℝ, E) E).cottonTensor x = 0) := by
  refine ⟨fun hg ↦ ⟨hg.weylTensor_eq_zero (by omega), hg.cottonTensor_eq_zero (by omega)⟩, ?_⟩
  rintro ⟨hW, hC⟩
  rw [g.isLocallyConformallyFlat_iff]
  intro x
  obtain ⟨φ, hφ, -, -, hflat⟩ :=
    g.exists_eventually_curvatureTensor_rescale_exp_eq_zero_model_space hn
      (Eventually.of_forall hW) (Eventually.of_forall hC) 0 0
  exact ⟨fun y ↦ Real.exp (2 * φ y),
    Real.contDiff_exp.comp_contMDiff (contMDiff_const.mul hφ), fun _ ↦ Real.exp_pos _, hflat⟩

/-- **Weyl–Schouten in dimension at least four, on a model space.** An arbitrary smooth
Riemannian metric is locally conformally flat if and only if its Weyl tensor vanishes. -/
theorem isLocallyConformallyFlat_iff_weylTensor_eq_zero_model_space
    (g : ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E (fun x : E ↦ TangentSpace 𝓘(ℝ, E) x))
    (hn : 4 ≤ Module.finrank ℝ E) :
    g.IsLocallyConformallyFlat ↔
      (letI : RiemannianBundle (fun x : E ↦ TangentSpace 𝓘(ℝ, E) x) := ⟨g.toRiemannianMetric⟩;
        ∀ x, (CovariantDerivative.leviCivitaConnection 𝓘(ℝ, E) E).weylTensor x = 0) := by
  rw [g.isLocallyConformallyFlat_iff_weylTensor_eq_zero_and_cottonTensor_eq_zero_model_space
    (by omega)]
  refine and_iff_left_of_imp fun hW x ↦ ?_
  let _ : RiemannianBundle (fun x : E ↦ TangentSpace 𝓘(ℝ, E) x) := ⟨g.toRiemannianMetric⟩
  have hcov := CovariantDerivative.isMetricCompatible_leviCivitaConnection (I := 𝓘(ℝ, E)) (M := E)
  exact hcov.cottonTensor_eq_zero_of_eventually_weylTensor_eq_zero
    (CovariantDerivative.torsion_leviCivitaConnection_eq_zero 𝓘(ℝ, E)) (by omega) (by omega)
    (Eventually.of_forall hW)

/-- **Weyl–Schouten in dimension three, on a model space.** An arbitrary smooth Riemannian
metric is locally conformally flat if and only if its Cotton tensor vanishes. -/
theorem isLocallyConformallyFlat_iff_cottonTensor_eq_zero_model_space
    (g : ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E (fun x : E ↦ TangentSpace 𝓘(ℝ, E) x))
    (hn : Module.finrank ℝ E = 3) :
    g.IsLocallyConformallyFlat ↔
      (letI : RiemannianBundle (fun x : E ↦ TangentSpace 𝓘(ℝ, E) x) := ⟨g.toRiemannianMetric⟩;
        ∀ x, (CovariantDerivative.leviCivitaConnection 𝓘(ℝ, E) E).cottonTensor x = 0) := by
  rw [g.isLocallyConformallyFlat_iff_weylTensor_eq_zero_and_cottonTensor_eq_zero_model_space
    hn.ge]
  refine and_iff_right ?_
  let _ : RiemannianBundle (fun x : E ↦ TangentSpace 𝓘(ℝ, E) x) := ⟨g.toRiemannianMetric⟩
  intro x
  have hcov := CovariantDerivative.isMetricCompatible_leviCivitaConnection (I := 𝓘(ℝ, E)) (M := E)
  exact CovariantDerivative.IsMetricCompatible.weylTensor_eq_zero_of_finrank_eq_three
    (cov := CovariantDerivative.leviCivitaConnection 𝓘(ℝ, E) E) hcov x
    (by rw [TauCeti.finrank_tangentSpace, hn])

end Bundle.ContMDiffRiemannianMetric
