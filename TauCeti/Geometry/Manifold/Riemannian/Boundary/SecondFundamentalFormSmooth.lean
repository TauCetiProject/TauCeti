/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Boundary.SecondFundamentalForm
public import TauCeti.Geometry.Manifold.Riemannian.Hessian.Regularity
import TauCeti.Geometry.Manifold.Boundary.Charts

/-!
# Smoothness of the second fundamental form of the boundary

Let `M` be a Riemannian manifold with boundary modelled on the half-space `𝓡∂ (n + 1)`. The
second fundamental form `II_q` of the boundary (`TauCeti.boundarySecondFundamentalForm`) is a
bilinear form on the tangent space `T_q∂M` of the boundary manifold at each `q ∈ ∂M`. This file
shows that `q ↦ II_q` is a `C^k` section of the bundle of bilinear forms on `T∂M`, on a
`C^(k + 2)` manifold with a `C^(k + 1)` metric: it pairs two `C^k` tangent fields `U`, `W` of the
boundary manifold to the `C^k` function `q ↦ II_q(U q, W q)`
(`TauCeti.contMDiffAt_boundarySecondFundamentalForm_apply`).

The proof fixes the preferred chart at a point `q₀`. On the boundary points of its source, `II`
is given by the Hessian formula in that one chart
(`TauCeti.boundarySecondFundamentalForm_apply_of_mem_chart_source`), whose ingredients are
regular: the normal coordinate is as smooth as the manifold, its Riemannian Hessian pairs `C^k`
fields along a `C^k` map to a `C^k` function (`TauCeti.Manifold.contMDiffAt_hessian_pair`), the
differential of the boundary inclusion carries `C^k` fields of `T∂M` to `C^k` fields of `TM`
along the inclusion, and the norm of the gradient is `C^(k + 1)` and positive at boundary points.
In particular the coefficients of `II` in Tau Ceti's boundary charts are `C^k`.
-/

public section

noncomputable section

open Bundle Filter
open scoped Manifold ContDiff InnerProductSpace Topology

namespace TauCeti

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (n + 1)) M] [IsManifold (𝓡∂ (n + 1)) 2 M]
  [RiemannianBundle (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x)]
  [IsContMDiffRiemannianBundle (𝓡∂ (n + 1)) 1 (EuclideanSpace ℝ (Fin (n + 1)))
    (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x)]
  {k m l : ℕ∞ω} [IsManifold (𝓡∂ (n + 1)) m M]
  [IsContMDiffRiemannianBundle (𝓡∂ (n + 1)) l (EuclideanSpace ℝ (Fin (n + 1)))
    (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x)]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 1 ((𝓡∂ (n + 1)).boundary M)]

omit [RiemannianBundle (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x)]
  [IsContMDiffRiemannianBundle (𝓡∂ (n + 1)) 1 (EuclideanSpace ℝ (Fin (n + 1)))
    (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x)] in
/-- The differential of the boundary inclusion carries a `C^k` tangent field of the boundary
manifold to a `C^k` field of `TM` along the inclusion, on a `C^(k + 1)` manifold. -/
private theorem contMDiffAt_mfderiv_subtypeVal_boundary_apply (hm : k + 1 ≤ m)
    {U : (q : (𝓡∂ (n + 1)).boundary M) → TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) q}
    {q₀ : (𝓡∂ (n + 1)).boundary M}
    (hU : ContMDiffAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)).tangent k
      (T% U) q₀) :
    ContMDiffAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡∂ (n + 1)).tangent k
      (fun q : (𝓡∂ (n + 1)).boundary M ↦ TotalSpace.mk' (EuclideanSpace ℝ (Fin (n + 1))) (q : M)
        (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡∂ (n + 1))
          (Subtype.val : (𝓡∂ (n + 1)).boundary M → M) q (U q))) q₀ := by
  have : IsManifold (𝓡∂ (n + 1)) 1 M := .of_le (le_add_self.trans hm)
  have hι := (isSmoothEmbedding_subtypeVal_boundary (n := n) (k := m) M).contMDiff
  exact ((hι.contMDiff_tangentMap hm) _).comp q₀ hU

omit [IsContMDiffRiemannianBundle (𝓡∂ (n + 1)) 1 (EuclideanSpace ℝ (Fin (n + 1)))
    (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x)]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 1 ((𝓡∂ (n + 1)).boundary M)] in
/-- The inverse norm of the gradient of minus the normal coordinate of a preferred chart is
`C^k` at the boundary points of the chart source, on a `C^(k + 1)` manifold with a `C^k`
metric. -/
private theorem contMDiffAt_inv_norm_mgradient_neg_chartAt_normal (hm : k + 1 ≤ m) (hl : k ≤ l)
    {α : M} {q : (𝓡∂ (n + 1)).boundary M}
    (hq : (q : M) ∈ (chartAt (EuclideanHalfSpace (n + 1)) α).source) :
    ContMDiffAt (𝓡∂ (n + 1)) 𝓘(ℝ) k
      (fun y ↦ ‖Manifold.mgradient (𝓡∂ (n + 1))
        (fun z ↦ -(chartAt (EuclideanHalfSpace (n + 1)) α z).val 0) y‖⁻¹) (q : M) := by
  have : IsManifold (𝓡∂ (n + 1)) (k + 1) M := .of_le hm
  have : IsContMDiffRiemannianBundle (𝓡∂ (n + 1)) k (EuclideanSpace ℝ (Fin (n + 1)))
      (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x) := .of_le hl
  set φ : M → ℝ := fun z ↦ -(chartAt (EuclideanHalfSpace (n + 1)) α z).val 0
  have hgrad := Manifold.contMDiffAt_mgradient (I := 𝓡∂ (n + 1)) (n := k)
    (contMDiffAt_neg_chartAt_normal (k := k + 1) hq)
  have hsq : ContMDiffAt (𝓡∂ (n + 1)) 𝓘(ℝ) k
      (fun y ↦ ⟪Manifold.mgradient (𝓡∂ (n + 1)) φ y,
        Manifold.mgradient (𝓡∂ (n + 1)) φ y⟫_ℝ) (q : M) :=
    ContMDiffAt.inner_bundle (IB := 𝓡∂ (n + 1)) (F := EuclideanSpace ℝ (Fin (n + 1)))
      (E := fun y : M ↦ TangentSpace (𝓡∂ (n + 1)) y) (b := id) hgrad hgrad
  have hne : Manifold.mgradient (𝓡∂ (n + 1)) φ q ≠ 0 := by
    intro h0
    have hn := (isOutwardUnitNormal_outwardUnitNormal q).norm_eq_one
    rw [outwardUnitNormal_eq_normalize_mgradient (IsManifold.chart_mem_maximalAtlas α) hq] at hn
    simp [φ, h0] at hn
  have hne' : ⟪Manifold.mgradient (𝓡∂ (n + 1)) φ q,
      Manifold.mgradient (𝓡∂ (n + 1)) φ q⟫_ℝ ≠ 0 := by
    rwa [real_inner_self_eq_norm_sq, pow_ne_zero_iff two_ne_zero, norm_ne_zero_iff]
  have hnorm : ContMDiffAt (𝓡∂ (n + 1)) 𝓘(ℝ) k
      (fun y ↦ ‖Manifold.mgradient (𝓡∂ (n + 1)) φ y‖) (q : M) := by
    simpa only [Function.comp_def, real_inner_self_eq_norm_sq, Real.sqrt_sq (norm_nonneg _)] using
      (Real.contDiffAt_sqrt hne').comp_contMDiffAt
        (f := fun y ↦ ⟪Manifold.mgradient (𝓡∂ (n + 1)) φ y,
          Manifold.mgradient (𝓡∂ (n + 1)) φ y⟫_ℝ) hsq
  exact hnorm.inv₀ (norm_ne_zero_iff.mpr hne)

/-- **The second fundamental form of the boundary is a `C^k` section** of the bundle of
bilinear forms on `T∂M`, on a `C^(k + 2)` manifold with a `C^(k + 1)` metric: it pairs two
tangent fields `U`, `W` of the boundary manifold that are `C^k` at `q₀` to a function
`q ↦ II_q(U q, W q)` that is `C^k` at `q₀`. -/
theorem contMDiffAt_boundarySecondFundamentalForm_apply (hm : k + 2 ≤ m) (hl : k + 1 ≤ l)
    {U W : (q : (𝓡∂ (n + 1)).boundary M) → TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) q}
    {q₀ : (𝓡∂ (n + 1)).boundary M}
    (hU : ContMDiffAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)).tangent k
      (T% U) q₀)
    (hW : ContMDiffAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)).tangent k
      (T% W) q₀) :
    ContMDiffAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ) k
      (fun q ↦ boundarySecondFundamentalForm q (U q) (W q)) q₀ := by
  have hm1 : k + 1 ≤ m := (add_le_add_right (by norm_num : (1 : ℕ∞ω) ≤ 2) k).trans hm
  set c := chartAt (EuclideanHalfSpace (n + 1)) (q₀ : M)
  set φ : M → ℝ := fun y ↦ -(c y).val 0
  have hφ : ContMDiffOn (𝓡∂ (n + 1)) 𝓘(ℝ) (k + 2) φ c.source := fun y hy ↦
    ((contMDiffAt_neg_chartAt_normal (k := m) hy).of_le hm).contMDiffWithinAt
  have hι : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡∂ (n + 1)) k
      (Subtype.val : (𝓡∂ (n + 1)).boundary M → M) :=
    ((isSmoothEmbedding_subtypeVal_boundary (n := n) (k := m) M).contMDiff.of_le
      (le_self_add.trans hm))
  have hH := Manifold.contMDiffAt_hessian_pair (n := k) hm hl c.open_source hφ
    (γ := (Subtype.val : (𝓡∂ (n + 1)).boundary M → M)) (x := q₀) (mem_chart_source _ _)
    (contMDiffAt_mfderiv_subtypeVal_boundary_apply hm1 hU)
    (contMDiffAt_mfderiv_subtypeVal_boundary_apply hm1 hW)
  have hN := (contMDiffAt_inv_norm_mgradient_neg_chartAt_normal hm1
    (le_self_add.trans hl) (mem_chart_source _ (q₀ : M))).comp q₀ (hι q₀)
  refine (hN.mul hH).congr_of_eventuallyEq ?_
  filter_upwards [continuous_subtypeVal.continuousAt.preimage_mem_nhds
    (c.open_source.mem_nhds (mem_chart_source _ (q₀ : M)))] with q hq
  exact boundarySecondFundamentalForm_apply_of_mem_chart_source hq (U q) (W q)

/-- **The second fundamental form of the boundary is a `C^k` section**: for `C^k` tangent fields
`U`, `W` of the boundary manifold, `q ↦ II_q(U q, W q)` is `C^k`, on a `C^(k + 2)` manifold with a
`C^(k + 1)` metric. -/
theorem contMDiff_boundarySecondFundamentalForm_apply (hm : k + 2 ≤ m) (hl : k + 1 ≤ l)
    {U W : (q : (𝓡∂ (n + 1)).boundary M) → TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) q}
    (hU : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)).tangent k
      (T% U))
    (hW : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)).tangent k
      (T% W)) :
    ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ) k
      (fun q ↦ boundarySecondFundamentalForm q (U q) (W q)) := fun q₀ ↦
  contMDiffAt_boundarySecondFundamentalForm_apply hm hl (hU q₀) (hW q₀)

end TauCeti
