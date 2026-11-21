/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Sphere.Curvature
public import TauCeti.Geometry.Manifold.Riemannian.PositiveScalarCurvature.Concordance
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Topology.Algebra.Order.Field
import all TauCeti.Geometry.Manifold.Riemannian.Sphere.Basic
import all TauCeti.Geometry.Manifold.Riemannian.Prod.Basic
import all TauCeti.Geometry.Manifold.Riemannian.PositiveScalarCurvature.Concordance
import all TauCeti.Geometry.Manifold.VectorBundle.Riemannian.Basic

/-!
# The shrinking round cylinder

For `n ≥ 2`, the product `Sⁿ × ℝ` with metric
`g(t) = 2(n-1)(1-t)g_round + dz²` is a Ricci flow for `t < 1`. Its Ricci tensor is
`(n-1)g_round` on the sphere factor and zero on the line factor, so its scalar curvature is
`n / (2(1-t))`. This is positive and strictly increases in forward time, diverging at `t = 1`.
In dimension three the scalar curvature is `1 / (1-t)`.

The construction uses the native smooth sphere metric, constant metric rescaling and cylinder
metric. The flow equation is stated pointwise on the native Levi-Civita Ricci tensor, without a
separate notion of metric family. Each time slice is a smooth Riemannian metric; outside `t < 1`
the family is the unit round cylinder by convention.

## References

* J. Morgan and G. Tian, *Ricci Flow and the Poincaré Conjecture*, Clay Mathematics Monographs 3
  (2007), Definitions 2.17–2.18 (the normalized shrinking round cylinder).
* [Poincaré formalization](https://github.com/frenzymath/PoincareConjecture).
* [Lean evaluation submissions](https://github.com/frenzymath/lean-eval-submissions).
-/

public section

open Bundle CovariantDerivative Metric Module Set
open scoped ContDiff Manifold Topology

noncomputable section

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
  [Fact (finrank ℝ E = n + 1)]

local notation "S" => sphere (0 : E) 1
local notation "P" => ModelWithCorners.prod (𝓡 n) 𝓘(ℝ)

/-- The shrinking round cylinder `Sⁿ × ℝ`, with metric `2(n-1)(1-t)g_round + dz²`
for `t < 1`. For other times it is the unit round cylinder by convention. -/
def shrinkingCylinderMetric (hn : 2 ≤ n) (t : ℝ) :
    ContMDiffRiemannianMetric ((𝓡 n).prod 𝓘(ℝ)) ∞ (EuclideanSpace ℝ (Fin n) × ℝ)
      (fun p : sphere (0 : E) 1 × ℝ ↦ TangentSpace ((𝓡 n).prod 𝓘(ℝ)) p) :=
  if ht : t < 1 then
    (((TauCeti.sphereRoundMetric (E := E)).ofLE le_top).rescale
      (fun _ ↦ 2 * ((n : ℝ) - 1) * (1 - t)) contMDiff_const
      (fun _ ↦ by
        have hnNat : 1 < n := by omega
        have hn' : (1 : ℝ) < n := by exact_mod_cast hnNat
        positivity)).cylinder
  else ((TauCeti.sphereRoundMetric (E := E)).ofLE le_top).cylinder

/-- At and after extinction, the shrinking cylinder is the unit round cylinder. -/
@[simp]
theorem shrinkingCylinderMetric_of_one_le (hn : 2 ≤ n) {t : ℝ} (ht : 1 ≤ t) :
    shrinkingCylinderMetric (E := E) hn t =
      ((TauCeti.sphereRoundMetric (E := E)).ofLE le_top).cylinder := by
  rw [shrinkingCylinderMetric, dite_eq_right (not_lt.mpr ht)]

/-- The shrinking cylinder scales the round sphere factor and fixes the line factor. -/
@[simp]
theorem shrinkingCylinderMetric_inner (hn : 2 ≤ n) {t : ℝ} (ht : t < 1)
    (p : sphere (0 : E) 1 × ℝ) (v w : TangentSpace ((𝓡 n).prod 𝓘(ℝ)) p) :
    (shrinkingCylinderMetric (E := E) hn t).inner p v w =
      2 * ((n : ℝ) - 1) * (1 - t) *
          inner ℝ (TauCeti.Manifold.tangentSpaceProdEquiv p v).1
            (TauCeti.Manifold.tangentSpaceProdEquiv p w).1 +
        NormedSpace.fromTangentSpace p.2 (TauCeti.Manifold.tangentSpaceProdEquiv p v).2 *
          NormedSpace.fromTangentSpace p.2 (TauCeti.Manifold.tangentSpaceProdEquiv p w).2 := by
  simp [shrinkingCylinderMetric, ht, ContMDiffRiemannianMetric.cylinder_inner,
    ContMDiffRiemannianMetric.rescale_inner, TauCeti.sphereRoundMetric_inner,
    ContMDiffRiemannianMetric.ofLE_inner, TauCeti.inner_tangentSpace_sphere]

/-- The shrinking cylinder has scalar curvature `n / (2(1-t))`; in dimension three
(`n = 2`) this is `1 / (1-t)`. -/
@[simp]
theorem scalarCurvature_shrinkingCylinderMetric (hn : 2 ≤ n) {t : ℝ} (ht : t < 1)
    (p : sphere (0 : E) 1 × ℝ) :
    (shrinkingCylinderMetric (E := E) hn t).scalarCurvature p = n / (2 * (1 - t)) := by
  have hnNat : 1 < n := by omega
  have hn' : (1 : ℝ) < n := by exact_mod_cast hnNat
  rw [shrinkingCylinderMetric, dite_eq_left ht,
    ContMDiffRiemannianMetric.scalarCurvature_cylinder,
    ContMDiffRiemannianMetric.scalarCurvature_rescale_const _ (by positivity),
    TauCeti.scalarCurvature_sphereRoundMetric_ofLE]
  field_simp [ne_of_gt (sub_pos.mpr hn'), ne_of_gt (sub_pos.mpr ht)]

-- Use the displayed metric's smoothness instance, avoiding recursive product-instance search.
attribute [-instance] Manifold.instIsContMDiffRiemannianBundleProd in
/-- The Ricci tensor of the shrinking cylinder is `(n-1)g_round` on the sphere factor
and vanishes on the line factor. -/
theorem ricciTensor_shrinkingCylinderMetric (hn : 2 ≤ n) (t : ℝ)
    (p : sphere (0 : E) 1 × ℝ)
    (v w : TangentSpace ((𝓡 n).prod 𝓘(ℝ)) p) :
    (letI : RiemannianBundle
        (fun p : sphere (0 : E) 1 × ℝ ↦ TangentSpace ((𝓡 n).prod 𝓘(ℝ)) p) :=
      ⟨(shrinkingCylinderMetric (E := E) hn t).toRiemannianMetric⟩;
      (leviCivitaConnection ((𝓡 n).prod 𝓘(ℝ)) (sphere (0 : E) 1 × ℝ)).ricciTensor p v w) =
      ((n : ℝ) - 1) * inner ℝ (TauCeti.Manifold.tangentSpaceProdEquiv p v).1
        (TauCeti.Manifold.tangentSpaceProdEquiv p w).1 := by
  let g : ContMDiffRiemannianMetric (𝓡 n) ∞ (EuclideanSpace ℝ (Fin n))
      (fun x : S ↦ TangentSpace (𝓡 n) x) :=
    if ht : t < 1 then
      ((TauCeti.sphereRoundMetric (E := E) (n := n)).ofLE le_top).rescale
        (fun _ ↦ 2 * ((n : ℝ) - 1) * (1 - t)) contMDiff_const
        (fun _ ↦ by
          have hnNat : 1 < n := by omega
          have hn' : (1 : ℝ) < n := by exact_mod_cast hnNat
          positivity)
    else (TauCeti.sphereRoundMetric (E := E)).ofLE le_top
  have hmetric : shrinkingCylinderMetric (E := E) hn t = g.cylinder := by
    unfold shrinkingCylinderMetric g
    split <;> rfl
  rw [hmetric]
  let _ : RiemannianBundle (fun x : sphere (0 : E) 1 ↦ TangentSpace (𝓡 n) x) :=
    ⟨g.toRiemannianMetric⟩
  have hg : (⟨g.cylinder.toRiemannianMetric⟩ : RiemannianBundle
      (fun p : sphere (0 : E) 1 × ℝ ↦ TangentSpace ((𝓡 n).prod 𝓘(ℝ)) p)) =
      TauCeti.Manifold.instRiemannianBundleProd := by
    rw [ContMDiffRiemannianMetric.cylinder,
      ContMDiffRiemannianMetric.prodTangentSpace_toRiemannianMetric]
    exact congrArg RiemannianBundle.mk TauCeti.Manifold.riemannianBundleProd_g.symm
  have hprod := TauCeti.Manifold.ricciTensor_leviCivitaConnection_prod
    (I := 𝓡 n) (J := 𝓘(ℝ)) p v w
  -- Align the cylinder metric instance with the sphere instance in the product Ricci law.
  have hproductRicci :
      (letI : RiemannianBundle (fun p : S × ℝ ↦ TangentSpace P p) :=
          ⟨g.cylinder.toRiemannianMetric⟩;
        (leviCivitaConnection P (S × ℝ)).ricciTensor p v w) =
      (letI : RiemannianBundle (fun x : S ↦ TangentSpace (𝓡 n) x) :=
          ⟨g.toRiemannianMetric⟩;
        (leviCivitaConnection (𝓡 n) S).ricciTensor p.1
          (TauCeti.Manifold.tangentSpaceProdEquiv p v).1
          (TauCeti.Manifold.tangentSpaceProdEquiv p w).1) := by
    convert hprod using 3
    · cases hg
      rfl
    · simp
  rw [hproductRicci]
  by_cases ht : t < 1
  · have hbranch : g = _ := dite_eq_left ht
    rw [hbranch]
    rw [ContMDiffRiemannianMetric.ricciTensor_leviCivitaConnection_rescale_const]
    exact TauCeti.ricciTensor_sphere p.1 _ _
  · have hbranch : g = _ := dite_eq_right ht
    rw [hbranch]
    exact TauCeti.ricciTensor_sphere p.1 _ _

attribute [-instance] Manifold.instIsContMDiffRiemannianBundleProd in
/-- The shrinking round cylinder satisfies the Ricci flow equation `∂ₜg = -2 Ric(g)`
at every time before extinction, stated on tangent vectors in the native product model. -/
theorem hasDerivAt_inner_shrinkingCylinderMetric (hn : 2 ≤ n) {t : ℝ} (ht : t < 1)
    (p : sphere (0 : E) 1 × ℝ)
    (v w : TangentSpace ((𝓡 n).prod 𝓘(ℝ)) p) :
    HasDerivAt (fun s ↦ (shrinkingCylinderMetric (E := E) hn s).inner p v w)
      (-2 * (letI : RiemannianBundle (fun p : S × ℝ ↦ TangentSpace P p) :=
        ⟨(shrinkingCylinderMetric (E := E) hn t).toRiemannianMetric⟩;
        (leviCivitaConnection ((𝓡 n).prod 𝓘(ℝ)) (sphere (0 : E) 1 × ℝ)).ricciTensor p v w)) t := by
  rw [ricciTensor_shrinkingCylinderMetric hn t p v w]
  have heq : (fun s ↦ (shrinkingCylinderMetric (E := E) hn s).inner p v w) =ᶠ[𝓝 t]
      (fun s ↦ 2 * ((n : ℝ) - 1) * (1 - s) *
          inner ℝ (TauCeti.Manifold.tangentSpaceProdEquiv p v).1
            (TauCeti.Manifold.tangentSpaceProdEquiv p w).1 +
        NormedSpace.fromTangentSpace p.2 (TauCeti.Manifold.tangentSpaceProdEquiv p v).2 *
          NormedSpace.fromTangentSpace p.2 (TauCeti.Manifold.tangentSpaceProdEquiv p w).2) := by
    filter_upwards [Iio_mem_nhds ht] with s hs
    exact shrinkingCylinderMetric_inner hn hs p v w
  convert (((((hasDerivAt_id t).const_sub 1).const_mul (2 * ((n : ℝ) - 1))).mul_const
    (inner ℝ (TauCeti.Manifold.tangentSpaceProdEquiv p v).1
      (TauCeti.Manifold.tangentSpaceProdEquiv p w).1)).add_const
    (NormedSpace.fromTangentSpace p.2 (TauCeti.Manifold.tangentSpaceProdEquiv p v).2 *
      NormedSpace.fromTangentSpace p.2
        (TauCeti.Manifold.tangentSpaceProdEquiv p w).2)).congr_of_eventuallyEq heq using 1
  ring

/-- The scalar curvature of the shrinking cylinder is strictly increasing in forward time. -/
theorem strictMonoOn_scalarCurvature_shrinkingCylinderMetric (hn : 2 ≤ n)
    (p : sphere (0 : E) 1 × ℝ) :
    StrictMonoOn (fun t ↦ (shrinkingCylinderMetric (E := E) hn t).scalarCurvature p) (Iio 1) := by
  intro s hs t ht hst
  simp only [mem_Iio] at hs ht
  dsimp only
  rw [scalarCurvature_shrinkingCylinderMetric hn hs p,
    scalarCurvature_shrinkingCylinderMetric hn ht p]
  have hnNat : 0 < n := by omega
  have hn' : (0 : ℝ) < n := by exact_mod_cast hnNat
  apply div_lt_div_of_pos_left hn'
  · positivity
  · linarith

/-- Every slice has positive scalar curvature, including the unit-cylinder fallback. -/
theorem hasPositiveScalarCurvature_shrinkingCylinderMetric (hn : 2 ≤ n) (t : ℝ) :
    (shrinkingCylinderMetric (E := E) hn t).HasPositiveScalarCurvature := by
  rw [ContMDiffRiemannianMetric.hasPositiveScalarCurvature_iff]
  intro p
  have hnNat : 1 < n := by omega
  have hn' : (1 : ℝ) < n := by exact_mod_cast hnNat
  by_cases ht : t < 1
  · rw [scalarCurvature_shrinkingCylinderMetric hn ht p]
    exact div_pos (by positivity) (mul_pos two_pos (sub_pos.mpr ht))
  · rw [shrinkingCylinderMetric_of_one_le hn (not_lt.mp ht)]
    simp only [ContMDiffRiemannianMetric.scalarCurvature_cylinder,
      TauCeti.scalarCurvature_sphereRoundMetric_ofLE]
    positivity

/-- The time derivative of scalar curvature on the shrinking cylinder is `n / (2(1-t)²)`. -/
theorem hasDerivAt_scalarCurvature_shrinkingCylinderMetric (hn : 2 ≤ n) {t : ℝ} (ht : t < 1)
    (p : sphere (0 : E) 1 × ℝ) :
    HasDerivAt (fun s ↦ (shrinkingCylinderMetric (E := E) hn s).scalarCurvature p)
      (n / (2 * (1 - t) ^ 2)) t := by
  have ht0 : 1 - t ≠ 0 := ne_of_gt (sub_pos.mpr ht)
  have heq : (fun s ↦ (shrinkingCylinderMetric (E := E) hn s).scalarCurvature p) =ᶠ[𝓝 t]
      (fun s ↦ ((n : ℝ) / 2) * (1 - s)⁻¹) := by
    filter_upwards [Iio_mem_nhds ht] with s hs
    rw [scalarCurvature_shrinkingCylinderMetric hn hs p]
    simp [div_eq_mul_inv, mul_left_comm, mul_comm]
  convert ((((hasDerivAt_id t).const_sub 1).inv ht0).const_mul
    ((n : ℝ) / 2)).congr_of_eventuallyEq heq using 1
  dsimp only [id_eq]
  field_simp

/-- The scalar curvature of the shrinking cylinder diverges at its extinction time `1`. -/
theorem tendsto_scalarCurvature_shrinkingCylinderMetric_nhdsLT_one_atTop (hn : 2 ≤ n)
    (p : sphere (0 : E) 1 × ℝ) :
    Filter.Tendsto (fun t ↦ (shrinkingCylinderMetric (E := E) hn t).scalarCurvature p)
      (𝓝[<] 1) Filter.atTop := by
  have hcontinuous : Continuous (fun s : ℝ ↦ 1 - s) := continuous_const.sub continuous_id
  have hz : Filter.Tendsto (fun s : ℝ ↦ 1 - s) (𝓝[<] 1) (𝓝 0) := by
    simpa using (hcontinuous.tendsto (1 : ℝ)).mono_left nhdsWithin_le_nhds
  have hden : Filter.Tendsto (fun s : ℝ ↦ 1 - s) (𝓝[<] 1) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨hz, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact sub_pos.mpr hs
  have hpos : 0 < (n : ℝ) / 2 := by positivity
  have h := hden.inv_tendsto_nhdsGT_zero.atTop_mul_const hpos
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  rw [scalarCurvature_shrinkingCylinderMetric hn hs p]
  simp [div_eq_mul_inv, mul_left_comm, mul_comm]

end TauCeti
