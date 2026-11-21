/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import TauCeti.Geometry.RicciFlow.Product.Basic
public import TauCeti.Geometry.Manifold.Riemannian.Sphere.Radius
import TauCeti.Algebra.Order.Field.Basic

/-!
# Ricci flow on a product of round two-spheres

The product of round two-spheres of initial radii `r₁` and `r₂` evolves by the independent
squared radii `r₁² - 2t` and `r₂² - 2t`. Its scalar curvature is
`2 / (r₁² - 2t) + 2 / (r₂² - 2t)`. This tends to infinity at the smaller factor lifetime.
When the initial radii are unequal, the other factor remains nondegenerate there.

## References

* P. Topping, *Lectures on the Ricci Flow* (2006), §1.2.1.
* Public formalizations: [lean-eval-submissions](https://github.com/frenzymath/lean-eval-submissions)
  and [PoincareConjecture](https://github.com/frenzymath/PoincareConjecture).
-/

public noncomputable section

open Bundle CovariantDerivative Filter Metric Module
open scoped ContDiff Manifold Topology

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Fact (finrank ℝ E = 2 + 1)]
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [Fact (finrank ℝ F = 2 + 1)]

/-- The independently shrinking round metrics on a product of two-spheres. The family is
totalized by the initial product metric outside its positive-scale interval. -/
def sphereProductFlow (r₁ r₂ : ℝ) (hr₁ : 0 < r₁) (hr₂ : 0 < r₂) (t : ℝ) :
    ContMDiffRiemannianMetric ((𝓡 2).prod (𝓡 2)) ∞
      (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2))
      (fun p : sphere (0 : E) 1 × sphere (0 : F) 1 ↦
        TangentSpace ((𝓡 2).prod (𝓡 2)) p) :=
  (sphereRoundMetricOfRadius r₁ hr₁).einsteinProductFlow
    (sphereRoundMetricOfRadius r₂ hr₂) (r₁ ^ 2)⁻¹ (r₂ ^ 2)⁻¹ t

variable {r₁ r₂ t : ℝ} (hr₁ : 0 < r₁) (hr₂ : 0 < r₂)

/-- The initial metric has the prescribed two radii. -/
@[simp]
theorem sphereProductFlow_zero :
    sphereProductFlow (E := E) (F := F) r₁ r₂ hr₁ hr₂ 0 =
      (sphereRoundMetricOfRadius r₁ hr₁).prodTangentSpace
        (sphereRoundMetricOfRadius r₂ hr₂) := by
  simp [sphereProductFlow]

/-- Outside the common positive-scale interval the family is the initial product metric. -/
@[simp]
theorem sphereProductFlow_of_not_lt (h : ¬(t < r₁ ^ 2 / 2 ∧ t < r₂ ^ 2 / 2)) :
    sphereProductFlow (E := E) (F := F) r₁ r₂ hr₁ hr₂ t =
      (sphereRoundMetricOfRadius r₁ hr₁).prodTangentSpace
        (sphereRoundMetricOfRadius r₂ hr₂) := by
  apply ContMDiffRiemannianMetric.einsteinProductFlow_of_not_lt
  rintro ⟨hs₁, hs₂⟩
  exact h ⟨(two_mul_sq_inv_mul_lt_one_iff hr₁.ne').mp hs₁,
    (two_mul_sq_inv_mul_lt_one_iff hr₂.ne').mp hs₂⟩

/-- The product inner product has independently shrinking squared radii. -/
@[simp]
theorem sphereProductFlow_inner (ht₁ : t < r₁ ^ 2 / 2) (ht₂ : t < r₂ ^ 2 / 2)
    (p : sphere (0 : E) 1 × sphere (0 : F) 1)
    (u v : TangentSpace ((𝓡 2).prod (𝓡 2)) p) :
    (sphereProductFlow r₁ r₂ hr₁ hr₂ t).inner p u v =
      (r₁ ^ 2 - 2 * t) * inner ℝ (Manifold.tangentSpaceProdEquiv p u).1
        (Manifold.tangentSpaceProdEquiv p v).1 +
      (r₂ ^ 2 - 2 * t) * inner ℝ (Manifold.tangentSpaceProdEquiv p u).2
        (Manifold.tangentSpaceProdEquiv p v).2 := by
  have hs₁ := (two_mul_sq_inv_mul_lt_one_iff hr₁.ne').mpr ht₁
  have hs₂ := (two_mul_sq_inv_mul_lt_one_iff hr₂.ne').mpr ht₂
  rw [sphereProductFlow, ContMDiffRiemannianMetric.einsteinProductFlow_inner _ _ hs₁ hs₂,
    sphereRoundMetricOfRadius_inner, sphereRoundMetricOfRadius_inner]
  field_simp

/-- The product family satisfies the Ricci equation before either factor collapses. -/
theorem hasDerivAt_inner_sphereProductFlow (ht₁ : t < r₁ ^ 2 / 2) (ht₂ : t < r₂ ^ 2 / 2)
    (p : sphere (0 : E) 1 × sphere (0 : F) 1)
    (u v : TangentSpace ((𝓡 2).prod (𝓡 2)) p) :
    HasDerivAt (fun τ ↦ (sphereProductFlow r₁ r₂ hr₁ hr₂ τ).inner p u v)
      (-2 * (let g := sphereProductFlow r₁ r₂ hr₁ hr₂ t;
        letI : RiemannianBundle (fun p : sphere (0 : E) 1 × sphere (0 : F) 1 ↦
        TangentSpace ((𝓡 2).prod (𝓡 2)) p) :=
        ⟨g.toRiemannianMetric⟩;
        letI : IsContMDiffRiemannianBundle ((𝓡 2).prod (𝓡 2)) 1
          (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2))
          (fun p : sphere (0 : E) 1 × sphere (0 : F) 1 ↦
            TangentSpace ((𝓡 2).prod (𝓡 2)) p) :=
          ⟨g.inner, g.contMDiff.of_le (by simp), fun _ _ _ ↦ rfl⟩;
        (leviCivitaConnection ((𝓡 2).prod (𝓡 2))
          (sphere (0 : E) 1 × sphere (0 : F) 1)).ricciTensor p u v)) t := by
  have hs₁ := (two_mul_sq_inv_mul_lt_one_iff hr₁.ne').mpr ht₁
  have hs₂ := (two_mul_sq_inv_mul_lt_one_iff hr₂.ne').mpr ht₂
  apply ContMDiffRiemannianMetric.hasDerivAt_inner_einsteinProductFlow _ _ hs₁ hs₂
  · have h := ricciTensor_sphereRoundMetricOfRadius hr₁ p.1
      (TauCeti.Manifold.tangentSpaceProdEquiv p u).1 (TauCeti.Manifold.tangentSpaceProdEquiv p v).1
    norm_num only [Nat.cast_ofNat, one_div] at h
    exact h
  · have h := ricciTensor_sphereRoundMetricOfRadius hr₂ p.2
      (TauCeti.Manifold.tangentSpaceProdEquiv p u).2 (TauCeti.Manifold.tangentSpaceProdEquiv p v).2
    norm_num only [Nat.cast_ofNat, one_div] at h
    exact h

/-- The two scalar curvatures add, each with its own shrinking squared radius. -/
@[simp]
theorem scalarCurvature_sphereProductFlow (ht₁ : t < r₁ ^ 2 / 2) (ht₂ : t < r₂ ^ 2 / 2)
    (p : sphere (0 : E) 1 × sphere (0 : F) 1) :
    (sphereProductFlow r₁ r₂ hr₁ hr₂ t).scalarCurvature p =
      2 / (r₁ ^ 2 - 2 * t) + 2 / (r₂ ^ 2 - 2 * t) := by
  have hs₁ := (two_mul_sq_inv_mul_lt_one_iff hr₁.ne').mpr ht₁
  have hs₂ := (two_mul_sq_inv_mul_lt_one_iff hr₂.ne').mpr ht₂
  rw [sphereProductFlow, ContMDiffRiemannianMetric.scalarCurvature_einsteinProductFlow
    _ _ hs₁ hs₂]
  simp only [scalarCurvature_sphereRoundMetricOfRadius, Nat.cast_ofNat]
  have hd₁ : r₁ ^ 2 - 2 * t ≠ 0 := ne_of_gt (by linarith)
  have hd₂ : r₂ ^ 2 - 2 * t ≠ 0 := ne_of_gt (by linarith)
  field_simp
  ring

/-- When the first radius is no larger, scalar curvature blows up at its lifetime `r₁² / 2`.
For strictly smaller radius the second factor still has positive radius there. -/
theorem tendsto_scalarCurvature_sphereProductFlow_nhdsLT_atTop (hrr : r₁ ≤ r₂)
    (p : sphere (0 : E) 1 × sphere (0 : F) 1) :
    Tendsto (fun t ↦ (sphereProductFlow r₁ r₂ hr₁ (hr₁.trans_le hrr) t).scalarCurvature p)
      (𝓝[<] (r₁ ^ 2 / 2)) atTop := by
  have hr₂ : 0 < r₂ := hr₁.trans_le hrr
  rcases hrr.lt_or_eq with hlt | heq
  · have hsq : r₁ ^ 2 < r₂ ^ 2 := by nlinarith
    have hba : (r₂ ^ 2)⁻¹ < (r₁ ^ 2)⁻¹ :=
      (inv_lt_inv₀ (pow_pos hr₂ 2) (pow_pos hr₁ 2)).2 hsq
    have hT : (2 * (r₁ ^ 2)⁻¹)⁻¹ = r₁ ^ 2 / 2 := by simp [mul_inv_rev, div_eq_mul_inv]
    have hR : 0 <
        (sphereRoundMetricOfRadius (E := E) (n := 2) r₁ hr₁).scalarCurvature p.1 := by
      simpa using div_pos (by norm_num : (0 : ℝ) < 2) (pow_pos hr₁ 2)
    simpa only [hT, sphereProductFlow] using
      ContMDiffRiemannianMetric.tendsto_scalarCurvature_einsteinProductFlow_nhdsLT_atTop
        (sphereRoundMetricOfRadius r₁ hr₁) (sphereRoundMetricOfRadius r₂ hr₂)
        (inv_pos.mpr (pow_pos hr₁ 2)) hba p hR
  · subst r₂
    have hden : Tendsto (fun t : ℝ ↦ r₁ ^ 2 - 2 * t) (𝓝[<] (r₁ ^ 2 / 2)) (𝓝[>] 0) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
      · have hc : Continuous (fun t : ℝ ↦ r₁ ^ 2 - 2 * t) := by fun_prop
        have hz : r₁ ^ 2 - 2 * (r₁ ^ 2 / 2) = 0 := by ring
        have hlim : Tendsto (fun t : ℝ ↦ r₁ ^ 2 - 2 * t) (𝓝[<] (r₁ ^ 2 / 2))
            (𝓝 (r₁ ^ 2 - 2 * (r₁ ^ 2 / 2))) :=
          (hc.tendsto (r₁ ^ 2 / 2)).mono_left nhdsWithin_le_nhds
        rwa [hz] at hlim
      · filter_upwards [self_mem_nhdsWithin] with t ht
        simp only [Set.mem_Iio] at ht
        simp only [Set.mem_Ioi]
        linarith
    apply (hden.inv_tendsto_nhdsGT_zero.atTop_mul_const (by norm_num : (0 : ℝ) < 4)).congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    simp only [Set.mem_Iio] at ht
    rw [scalarCurvature_sphereProductFlow hr₁ hr₂ ht ht]
    simp only [Pi.inv_apply]
    ring

/-- Scalar curvature blows up at the smaller factor lifetime, including for equal radii. -/
theorem tendsto_scalarCurvature_sphereProductFlow_nhdsLT_min_atTop
    (p : sphere (0 : E) 1 × sphere (0 : F) 1) :
    Tendsto (fun t ↦ (sphereProductFlow r₁ r₂ hr₁ hr₂ t).scalarCurvature p)
      (𝓝[<] (min (r₁ ^ 2 / 2) (r₂ ^ 2 / 2))) atTop := by
  rcases le_total r₁ r₂ with hle | hge
  · have hT : r₁ ^ 2 / 2 ≤ r₂ ^ 2 / 2 := by nlinarith
    simpa only [min_eq_left hT] using
      tendsto_scalarCurvature_sphereProductFlow_nhdsLT_atTop hr₁ hle p
  · have hT : r₂ ^ 2 / 2 ≤ r₁ ^ 2 / 2 := by nlinarith
    rw [min_eq_right hT]
    apply (tendsto_scalarCurvature_sphereProductFlow_nhdsLT_atTop hr₂ hge p.swap).congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    simp only [Set.mem_Iio] at ht
    rw [scalarCurvature_sphereProductFlow hr₂ hr₁ ht (ht.trans_le hT),
      scalarCurvature_sphereProductFlow hr₁ hr₂ (ht.trans_le hT) ht]
    exact add_comm _ _

end TauCeti
