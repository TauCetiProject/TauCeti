/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Scaling
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Prod
import Mathlib.Analysis.Calculus.Deriv.Add

/-!
# Products of Ricci flows

The product of two families satisfying the Ricci equation satisfies the same equation. In
particular, Einstein metrics with constants `a` and `b` give the explicit product family
`(1 - 2 a t) g₁ × (1 - 2 b t) g₂` on the common positive-scale interval. Its two factors can
shrink, remain stationary, or expand independently. Its scalar curvature is the sum of the
rescaled scalar curvatures of its factors.

## Main results

* `Bundle.ContMDiffRiemannianMetric.hasDerivWithinAt_inner_prodTangentSpace_of_ricciFlow`:
  products preserve the Ricci equation on any time set.
* `Bundle.ContMDiffRiemannianMetric.hasDerivAt_inner_einsteinProductFlow`: independently
  scaled Einstein factors satisfy the Ricci equation.
* `Bundle.ContMDiffRiemannianMetric.scalarCurvature_einsteinProductFlow`: scalar curvature
  is the sum of the separately rescaled factor scalar curvatures.

## References

* P. Topping, *Lectures on the Ricci Flow* (2006), §1.2.1.
* J. Morgan and G. Tian, *Ricci Flow and the Poincaré Conjecture* (2007).
* Public formalizations: [lean-eval-submissions](https://github.com/frenzymath/lean-eval-submissions)
  and [PoincareConjecture](https://github.com/frenzymath/PoincareConjecture).
-/

public noncomputable section

open Bundle CovariantDerivative Filter Set
open scoped ContDiff Manifold Topology

namespace Bundle.ContMDiffRiemannianMetric

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N] [IsManifold J 1 N]

/-- The product Einstein family, with independent Einstein constants. On the common
positive-scale interval it is `(1 - 2 a t) g₁ × (1 - 2 b t) g₂`; elsewhere it is the initial
product metric. -/
def einsteinProductFlow
    (g₁ : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (g₂ : ContMDiffRiemannianMetric J ∞ F (fun y : N ↦ TangentSpace J y)) (a b t : ℝ) :
    ContMDiffRiemannianMetric (I.prod J) ∞ (E × F)
      (fun p : M × N ↦ TangentSpace (I.prod J) p) :=
  if h : 2 * a * t < 1 ∧ 2 * b * t < 1 then
    (g₁.rescale (fun _ ↦ 1 - 2 * a * t) contMDiff_const (fun _ ↦ sub_pos.mpr h.1)).prodTangentSpace
      (g₂.rescale (fun _ ↦ 1 - 2 * b * t) contMDiff_const (fun _ ↦ sub_pos.mpr h.2))
  else g₁.prodTangentSpace g₂

variable
  (g₁ : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
  (g₂ : ContMDiffRiemannianMetric J ∞ F (fun y : N ↦ TangentSpace J y))
  {a b t : ℝ}

/-- The inner product of the product Einstein family on the common positive-scale interval. -/
@[simp]
theorem einsteinProductFlow_inner (ha : 2 * a * t < 1) (hb : 2 * b * t < 1)
    (p : M × N) (u v : TangentSpace (I.prod J) p) :
    (g₁.einsteinProductFlow g₂ a b t).inner p u v =
      (1 - 2 * a * t) * g₁.inner p.1 (TauCeti.Manifold.tangentSpaceProdEquiv p u).1
        (TauCeti.Manifold.tangentSpaceProdEquiv p v).1 +
      (1 - 2 * b * t) * g₂.inner p.2 (TauCeti.Manifold.tangentSpaceProdEquiv p u).2
        (TauCeti.Manifold.tangentSpaceProdEquiv p v).2 := by
  simp [einsteinProductFlow, ha, hb]

/-- Outside the common positive-scale interval the product family is the initial metric. -/
@[simp]
theorem einsteinProductFlow_of_not_lt (h : ¬(2 * a * t < 1 ∧ 2 * b * t < 1)) :
    g₁.einsteinProductFlow g₂ a b t = g₁.prodTangentSpace g₂ := by
  simp [einsteinProductFlow, h]

/-- The product Einstein family starts at the product of its two initial metrics. -/
@[simp]
theorem einsteinProductFlow_zero (a b : ℝ) :
    g₁.einsteinProductFlow g₂ a b 0 = g₁.prodTangentSpace g₂ := by
  ext p u v
  simp

/-- With both Einstein constants zero, the product family is stationary. -/
@[simp]
theorem einsteinProductFlow_zero_zero (t : ℝ) :
    g₁.einsteinProductFlow g₂ 0 0 t = g₁.prodTangentSpace g₂ := by
  ext p u v
  simp

end Bundle.ContMDiffRiemannianMetric

namespace Bundle.ContMDiffRiemannianMetric

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
  {N : Type*} [TopologicalSpace N] [T2Space N] [ChartedSpace G N] [IsManifold J ∞ N]

/-- Products preserve the Ricci equation, including at relative time endpoints. Only the
factor equations on the selected pair of tangent vectors are needed. -/
theorem hasDerivWithinAt_inner_prodTangentSpace_of_ricciFlow
    (g₁ : ℝ → ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (g₂ : ℝ → ContMDiffRiemannianMetric J ∞ F (fun y : N ↦ TangentSpace J y))
    {s : Set ℝ} {t : ℝ} (p : M × N) (u v : TangentSpace (I.prod J) p)
    (h₁ : HasDerivWithinAt
      (fun τ ↦ (g₁ τ).inner p.1 (TauCeti.Manifold.tangentSpaceProdEquiv p u).1
        (TauCeti.Manifold.tangentSpaceProdEquiv p v).1)
      (-2 * (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
        ⟨(g₁ t).toRiemannianMetric⟩;
        (leviCivitaConnection I M).ricciTensor p.1 (TauCeti.Manifold.tangentSpaceProdEquiv p u).1
          (TauCeti.Manifold.tangentSpaceProdEquiv p v).1)) s t)
    (h₂ : HasDerivWithinAt
      (fun τ ↦ (g₂ τ).inner p.2 (TauCeti.Manifold.tangentSpaceProdEquiv p u).2
        (TauCeti.Manifold.tangentSpaceProdEquiv p v).2)
      (-2 * (letI : RiemannianBundle (fun y : N ↦ TangentSpace J y) :=
        ⟨(g₂ t).toRiemannianMetric⟩;
        (leviCivitaConnection J N).ricciTensor p.2 (TauCeti.Manifold.tangentSpaceProdEquiv p u).2
          (TauCeti.Manifold.tangentSpaceProdEquiv p v).2)) s t) :
    HasDerivWithinAt (fun τ ↦ ((g₁ τ).prodTangentSpace (g₂ τ)).inner p u v)
      (-2 * (letI : RiemannianBundle (fun p : M × N ↦ TangentSpace (I.prod J) p) :=
        ⟨((g₁ t).prodTangentSpace (g₂ t)).toRiemannianMetric⟩;
        (leviCivitaConnection (I.prod J) (M × N)).ricciTensor p u v)) s t := by
  convert h₁.add h₂ using 1
  · ext τ
    exact prodTangentSpace_inner (g₁ τ) (g₂ τ) p u v
  · rw [ricciTensor_prodTangentSpace]
    ring

variable
  (g₁ : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
  (g₂ : ContMDiffRiemannianMetric J ∞ F (fun y : N ↦ TangentSpace J y))

/-- Constant scaling of either factor preserves its Ricci tensor, so the product family's
Ricci tensor equals the sum of the two initial Ricci tensors at every time. -/
theorem ricciTensor_einsteinProductFlow (a b t : ℝ)
    (p : M × N) (u v : TangentSpace (I.prod J) p) :
    (letI : RiemannianBundle (fun p : M × N ↦ TangentSpace (I.prod J) p) :=
      ⟨(g₁.einsteinProductFlow g₂ a b t).toRiemannianMetric⟩;
      (leviCivitaConnection (I.prod J) (M × N)).ricciTensor p u v) =
    (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g₁.toRiemannianMetric⟩;
      (leviCivitaConnection I M).ricciTensor p.1 (TauCeti.Manifold.tangentSpaceProdEquiv p u).1
        (TauCeti.Manifold.tangentSpaceProdEquiv p v).1) +
    (letI : RiemannianBundle (fun y : N ↦ TangentSpace J y) := ⟨g₂.toRiemannianMetric⟩;
      (leviCivitaConnection J N).ricciTensor p.2 (TauCeti.Manifold.tangentSpaceProdEquiv p u).2
        (TauCeti.Manifold.tangentSpaceProdEquiv p v).2) := by
  by_cases h : 2 * a * t < 1 ∧ 2 * b * t < 1
  · have hmetric : g₁.einsteinProductFlow g₂ a b t =
        (g₁.rescale (fun _ ↦ 1 - 2 * a * t) contMDiff_const
          (fun _ ↦ sub_pos.mpr h.1)).prodTangentSpace
        (g₂.rescale (fun _ ↦ 1 - 2 * b * t) contMDiff_const
          (fun _ ↦ sub_pos.mpr h.2)) := by
      simp only [einsteinProductFlow, dite_eq_left h]
    rw [hmetric, ricciTensor_prodTangentSpace,
      ricciTensor_leviCivitaConnection_rescale_const,
      ricciTensor_leviCivitaConnection_rescale_const]
  · rw [einsteinProductFlow_of_not_lt g₁ g₂ h]
    exact ricciTensor_prodTangentSpace g₁ g₂ p u v

/-- The scalar curvature of the product Einstein family is the sum of the separately
rescaled scalar curvatures. No Einstein hypothesis on the initial factors is required. -/
@[simp]
theorem scalarCurvature_einsteinProductFlow {a b t : ℝ}
    (ha : 2 * a * t < 1) (hb : 2 * b * t < 1) (p : M × N) :
    (g₁.einsteinProductFlow g₂ a b t).scalarCurvature p =
      (1 - 2 * a * t)⁻¹ * g₁.scalarCurvature p.1 +
      (1 - 2 * b * t)⁻¹ * g₂.scalarCurvature p.2 := by
  simp [einsteinProductFlow, ha, hb]

end Bundle.ContMDiffRiemannianMetric

namespace Bundle.ContMDiffRiemannianMetric

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
  {N : Type*} [TopologicalSpace N] [T2Space N] [ChartedSpace G N] [IsManifold J ∞ N]
  (g₁ : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
  (g₂ : ContMDiffRiemannianMetric J ∞ F (fun y : N ↦ TangentSpace J y))

/-- Two Einstein factors with independent constants evolve by their separate affine scales.
The Einstein equations are required only at the selected factor points. -/
theorem hasDerivAt_inner_einsteinProductFlow {a b t : ℝ}
    (ha : 2 * a * t < 1) (hb : 2 * b * t < 1)
    (p : M × N) (u v : TangentSpace (I.prod J) p)
    (h₁ : (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g₁.toRiemannianMetric⟩;
      (leviCivitaConnection I M).ricciTensor p.1 (TauCeti.Manifold.tangentSpaceProdEquiv p u).1
        (TauCeti.Manifold.tangentSpaceProdEquiv p v).1) =
      a * g₁.inner p.1 (TauCeti.Manifold.tangentSpaceProdEquiv p u).1
        (TauCeti.Manifold.tangentSpaceProdEquiv p v).1)
    (h₂ : (letI : RiemannianBundle (fun y : N ↦ TangentSpace J y) := ⟨g₂.toRiemannianMetric⟩;
      (leviCivitaConnection J N).ricciTensor p.2 (TauCeti.Manifold.tangentSpaceProdEquiv p u).2
        (TauCeti.Manifold.tangentSpaceProdEquiv p v).2) =
      b * g₂.inner p.2 (TauCeti.Manifold.tangentSpaceProdEquiv p u).2
        (TauCeti.Manifold.tangentSpaceProdEquiv p v).2) :
    HasDerivAt (fun τ ↦ (g₁.einsteinProductFlow g₂ a b τ).inner p u v)
      (-2 * (letI : RiemannianBundle (fun p : M × N ↦ TangentSpace (I.prod J) p) :=
        ⟨(g₁.einsteinProductFlow g₂ a b t).toRiemannianMetric⟩;
        (leviCivitaConnection (I.prod J) (M × N)).ricciTensor p u v)) t := by
  rw [ricciTensor_einsteinProductFlow, h₁, h₂]
  have heq : (fun τ ↦ (g₁.einsteinProductFlow g₂ a b τ).inner p u v) =ᶠ[𝓝 t]
      (fun τ ↦ (1 - 2 * a * τ) *
          g₁.inner p.1 (TauCeti.Manifold.tangentSpaceProdEquiv p u).1
            (TauCeti.Manifold.tangentSpaceProdEquiv p v).1 +
        (1 - 2 * b * τ) *
          g₂.inner p.2 (TauCeti.Manifold.tangentSpaceProdEquiv p u).2
            (TauCeti.Manifold.tangentSpaceProdEquiv p v).2) := by
    filter_upwards [(isOpen_lt (continuous_const.mul continuous_id) continuous_const).mem_nhds ha,
      (isOpen_lt (continuous_const.mul continuous_id) continuous_const).mem_nhds hb] with τ hτ₁ hτ₂
    exact einsteinProductFlow_inner g₁ g₂ hτ₁ hτ₂ p u v
  convert (((((hasDerivAt_id t).const_mul (2 * a)).const_sub 1).mul_const
    (g₁.inner p.1 (TauCeti.Manifold.tangentSpaceProdEquiv p u).1
      (TauCeti.Manifold.tangentSpaceProdEquiv p v).1)).add
    ((((hasDerivAt_id t).const_mul (2 * b)).const_sub 1).mul_const
      (g₂.inner p.2 (TauCeti.Manifold.tangentSpaceProdEquiv p u).2
        (TauCeti.Manifold.tangentSpaceProdEquiv p v).2))).congr_of_eventuallyEq heq using 1; ring

end Bundle.ContMDiffRiemannianMetric

namespace Bundle.ContMDiffRiemannianMetric

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
  {N : Type*} [TopologicalSpace N] [T2Space N] [ChartedSpace G N] [IsManifold J ∞ N]
  (g₁ : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
  (g₂ : ContMDiffRiemannianMetric J ∞ F (fun y : N ↦ TangentSpace J y))

/-- If the first factor shrinks faster and has positive initial scalar curvature, the
product scalar curvature tends to infinity at that factor's lifetime. The other factor
may have scalar curvature of either sign. -/
theorem tendsto_scalarCurvature_einsteinProductFlow_nhdsLT_atTop {a b : ℝ}
    (ha : 0 < a) (hba : b < a) (p : M × N) (hR : 0 < g₁.scalarCurvature p.1) :
    Tendsto (fun t ↦ (g₁.einsteinProductFlow g₂ a b t).scalarCurvature p)
      (𝓝[<] (2 * a)⁻¹) atTop := by
  have ha₀ : 2 * a ≠ 0 := ne_of_gt (mul_pos (by norm_num) ha)
  have haT : 2 * a * (2 * a)⁻¹ = 1 := mul_inv_cancel₀ ha₀
  have hnear₁ : ∀ᶠ t in 𝓝[<] (2 * a)⁻¹, 2 * a * t < 1 := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    simp only [Set.mem_Iio] at ht
    have hpos : 0 < 2 * a := by positivity
    have hlt : 2 * a * t < 2 * a * (2 * a)⁻¹ := mul_lt_mul_of_pos_left ht hpos
    simpa only [haT] using hlt
  have hbT : 2 * b * (2 * a)⁻¹ < 1 := by
    have : b / a < 1 := (div_lt_one ha).mpr hba
    convert this using 1; field_simp
  have hnear₂ : ∀ᶠ t in 𝓝[<] (2 * a)⁻¹, 2 * b * t < 1 :=
    ((continuous_const.mul continuous_id).continuousAt.tendsto.eventually_lt_const hbT).filter_mono
      nhdsWithin_le_nhds
  have hden : Tendsto (fun t : ℝ ↦ 1 - 2 * a * t) (𝓝[<] (2 * a)⁻¹) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, hnear₁.mono fun _ ht ↦ sub_pos.mpr ht⟩
    have hc : Continuous (fun t : ℝ ↦ 1 - 2 * a * t) :=
      continuous_const.sub (continuous_const.mul continuous_id)
    simpa only [haT, sub_self] using
      (hc.tendsto ((2 * a)⁻¹)).mono_left nhdsWithin_le_nhds
  have hdiv := hden.inv_tendsto_nhdsGT_zero.atTop_mul_const hR
  have hother : Tendsto (fun t : ℝ ↦ (1 - 2 * b * t)⁻¹ * g₂.scalarCurvature p.2)
      (𝓝[<] (2 * a)⁻¹)
      (𝓝 ((1 - 2 * b * (2 * a)⁻¹)⁻¹ * g₂.scalarCurvature p.2)) :=
    ((((continuous_const.sub (continuous_const.mul continuous_id)).continuousAt.inv₀
      (sub_pos.mpr hbT).ne').tendsto).mul_const _).mono_left nhdsWithin_le_nhds
  apply (hdiv.atTop_add hother).congr'
  filter_upwards [hnear₁, hnear₂] with t ht₁ ht₂
  exact (scalarCurvature_einsteinProductFlow g₁ g₂ ht₁ ht₂ p).symm

end Bundle.ContMDiffRiemannianMetric
