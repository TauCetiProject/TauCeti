/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Laplacian
public import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.Volume

/-!
# Integrability and product-rule identities for the Riemannian divergence

This module collects general integration helpers for the divergence of a `C¹` vector field on a
Riemannian manifold with or without boundary: integrability of the divergence of a compactly
supported `C¹` vector field against `TauCeti.riemannianVolume`, and the decomposition of
`∫ f div X dV` via the product rule `div (f X) = f div X + df(X)`.

## Main results

* `TauCeti.Manifold.integrable_divergence`: the divergence of a compactly supported `C¹` vector
  field is integrable against the Riemannian volume.
* `TauCeti.Manifold.integral_mul_divergence_eq_integral_divergence_smul_sub`: product-rule
  decomposition `∫ f div X dV = ∫ div (f X) dV - ∫ df(X) dV`, along with the left and right
  compact-support variants.
-/

public section

noncomputable section

open Bundle FiberBundle MeasureTheory
open scoped ContDiff Manifold

namespace TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 2 M] [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]
  [MeasurableSpace M] [BorelSpace M] [LindelofSpace M]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

/-- The divergence of a compactly supported `C¹` vector field is integrable against the Riemannian
volume. -/
theorem integrable_divergence {X : (x : M) → TangentSpace I x}
    (hX : ContMDiff I I.tangent 1 (T% X)) (hc : HasCompactSupport (β := E) X) :
    Integrable (divergence I X) (riemannianVolume I M) :=
  (continuous_divergence hX).integrable_of_hasCompactSupport (hc.divergence I)

/-- Integration-by-parts decomposition for the divergence of `f • X`, assuming `f • X` has
compact support and `f * div X` is integrable. -/
theorem integral_mul_divergence_eq_integral_divergence_smul_sub {f : M → ℝ}
    {X : (x : M) → TangentSpace I x} (hf : ContMDiff I 𝓘(ℝ) 1 f)
    (hX : ContMDiff I I.tangent 1 (T% X))
    (hfXc : HasCompactSupport (β := E) (fun x ↦ f x • X x))
    (hint : Integrable (fun x ↦ f x * divergence I X x) (riemannianVolume I M)) :
    ∫ x, f x * divergence I X x ∂riemannianVolume I M =
      (∫ x, divergence I (fun x ↦ f x • X x) x ∂riemannianVolume I M) -
        ∫ x, mvfderiv I f x (X x) ∂riemannianVolume I M := by
  have hfX : ContMDiff I I.tangent 1 (T% (fun x ↦ f x • X x)) := hf.smul_section hX
  have hpt (x : M) : divergence I (fun x ↦ f x • X x) x =
      f x * divergence I X x + mvfderiv I f x (X x) :=
    divergence_smul_function I f X x ((hf x).mdifferentiableAt one_ne_zero)
      ((hX x).mdifferentiableAt one_ne_zero)
  have hint' : Integrable (fun x ↦ mvfderiv I f x (X x)) (riemannianVolume I M) :=
    ((integrable_divergence hfX hfXc).sub hint).congr
      (Filter.Eventually.of_forall fun x ↦ by simp only [Pi.sub_apply, hpt]; ring)
  have hdiv : ∫ x, divergence I (fun x ↦ f x • X x) x ∂riemannianVolume I M =
      (∫ x, f x * divergence I X x ∂riemannianVolume I M) +
        ∫ x, mvfderiv I f x (X x) ∂riemannianVolume I M := by
    rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_add hint hint']
  linarith

/-- Integration-by-parts decomposition for `f * div X` when `f` has compact support. -/
theorem integral_mul_divergence_eq_integral_divergence_smul_sub_of_hasCompactSupport_left
    {f : M → ℝ} {X : (x : M) → TangentSpace I x} (hf : ContMDiff I 𝓘(ℝ) 1 f)
    (hfc : HasCompactSupport f) (hX : ContMDiff I I.tangent 1 (T% X)) :
    ∫ x, f x * divergence I X x ∂riemannianVolume I M =
      (∫ x, divergence I (fun x ↦ f x • X x) x ∂riemannianVolume I M) -
        ∫ x, mvfderiv I f x (X x) ∂riemannianVolume I M :=
  integral_mul_divergence_eq_integral_divergence_smul_sub hf hX
    (hfc.of_isClosed_subset (isClosed_tsupport _) (tsupport_smul_subset_left _ _))
    ((hf.continuous.mul (continuous_divergence hX)).integrable_of_hasCompactSupport hfc.mul_right)

/-- Integration-by-parts decomposition for `f * div X` when `X` has compact support. -/
theorem integral_mul_divergence_eq_integral_divergence_smul_sub_of_hasCompactSupport_right
    {f : M → ℝ} {X : (x : M) → TangentSpace I x} (hf : ContMDiff I 𝓘(ℝ) 1 f)
    (hX : ContMDiff I I.tangent 1 (T% X)) (hXc : HasCompactSupport (β := E) X) :
    ∫ x, f x * divergence I X x ∂riemannianVolume I M =
      (∫ x, divergence I (fun x ↦ f x • X x) x ∂riemannianVolume I M) -
        ∫ x, mvfderiv I f x (X x) ∂riemannianVolume I M :=
  integral_mul_divergence_eq_integral_divergence_smul_sub hf hX
    (hXc.of_isClosed_subset (isClosed_tsupport _) (tsupport_smul_subset_right _ _))
    ((hf.continuous.mul (continuous_divergence hX)).integrable_of_hasCompactSupport
      (hXc.divergence I).mul_left)

end TauCeti.Manifold
