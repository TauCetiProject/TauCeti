/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Boundary.SecondFundamentalForm.Basic
public import TauCeti.Geometry.Manifold.Riemannian.Hessian.Regularity
import TauCeti.Geometry.Manifold.Boundary.Charts
import TauCeti.Geometry.Manifold.ContMDiff.MFDeriv
import TauCeti.Geometry.Manifold.VectorBundle.LocalFrame

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
along the inclusion (`ContMDiffAt.mfderiv_apply_sectionAlong`), and the norm of
the gradient is positive at boundary points (`TauCeti.mgradient_neg_chartAt_normal_ne_zero`), hence
`C^(k + 1)` there (`TauCeti.Manifold.contMDiffAt_norm_mgradient`).
In particular the coefficients of `II` in Tau Ceti's boundary charts are `C^k`.

Pairing `II` with a local frame of `T∂M` at `k = 0` shows that `II` is a continuous section of the
bundle of bilinear forms on `T∂M` (`TauCeti.continuousAt_boundarySecondFundamentalForm`,
`TauCeti.continuous_boundarySecondFundamentalForm`).
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
  have hne := mgradient_neg_chartAt_normal_ne_zero q.property hq
  exact (Manifold.contMDiffAt_norm_mgradient (contMDiffAt_neg_chartAt_normal (k := k + 1) hq)
    hne).inv₀ (norm_ne_zero_iff.mpr hne)

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
  have hι : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡∂ (n + 1)) m
      (Subtype.val : (𝓡∂ (n + 1)).boundary M → M) :=
    (isSmoothEmbedding_subtypeVal_boundary (n := n) (k := m) M).contMDiff
  have hH := Manifold.contMDiffAt_hessian_pair (n := k) hm hl c.open_source hφ
    (γ := (Subtype.val : (𝓡∂ (n + 1)).boundary M → M)) (x := q₀) (mem_chart_source _ _)
    ((hι q₀).mfderiv_apply_sectionAlong hU hm1)
    ((hι q₀).mfderiv_apply_sectionAlong hW hm1)
  have hN := (contMDiffAt_inv_norm_mgradient_neg_chartAt_normal hm1
    (le_self_add.trans hl) (mem_chart_source _ (q₀ : M))).comp q₀
    ((hι q₀).of_le (le_self_add.trans hm))
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

/-- **Continuity of the second fundamental form**: `q ↦ II_q` is a section of the bundle of bilinear
forms on `T∂M` that is continuous at every point. Its pairings with a local frame of `T∂M` at `q₀`
are continuous on the base set of the frame, by
`TauCeti.contMDiffAt_boundarySecondFundamentalForm_apply` at `k = 0`. -/
theorem continuousAt_boundarySecondFundamentalForm (q₀ : (𝓡∂ (n + 1)).boundary M) :
    ContinuousAt (fun q ↦ TotalSpace.mk'
      (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
      (E := fun q : (𝓡∂ (n + 1)).boundary M ↦ TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) q →L[ℝ]
        TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) q →L[ℝ] ℝ) q
      (boundarySecondFundamentalForm q).toContinuousBilinearMap) q₀ := by
  set e := trivializationAt (EuclideanSpace ℝ (Fin n))
    (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) q₀
  let b := Module.Basis.ofVectorSpace ℝ (EuclideanSpace ℝ (Fin n))
  have hframe (i) {q} (hq : q ∈ e.baseSet) : ContMDiffAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      𝓘(ℝ, EuclideanSpace ℝ (Fin n)).tangent 0 (T% (e.localFrame b i)) q :=
    (e.contMDiffOn_localFrame_baseSet 0 b i).contMDiffAt (e.open_baseSet.mem_nhds hq)
  exact ((Manifold.contMDiffOn_bilinear_of_localFrame (n := 0) b subset_rfl fun i j q hq ↦
    (contMDiffAt_boundarySecondFundamentalForm_apply (k := 0) (m := 2) (l := 1) (by norm_num)
      (by norm_num) (hframe i hq) (hframe j hq)).contMDiffWithinAt).contMDiffAt
    (e.open_baseSet.mem_nhds (FiberBundle.mem_baseSet_trivializationAt' q₀))).continuousAt

variable (n M) in
/-- **Continuity of the second fundamental form**: `q ↦ II_q` is a continuous section of the
bundle of bilinear forms on `T∂M`. -/
theorem continuous_boundarySecondFundamentalForm :
    Continuous (fun q ↦ TotalSpace.mk'
      (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
      (E := fun q : (𝓡∂ (n + 1)).boundary M ↦ TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) q →L[ℝ]
        TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) q →L[ℝ] ℝ) q
      (boundarySecondFundamentalForm q).toContinuousBilinearMap) :=
  continuous_iff_continuousAt.2 continuousAt_boundarySecondFundamentalForm

end TauCeti
