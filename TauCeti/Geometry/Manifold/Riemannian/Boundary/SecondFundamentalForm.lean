/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Boundary.TangentSpace
public import TauCeti.Geometry.Manifold.Riemannian.Laplacian
public import TauCeti.Geometry.Manifold.Riemannian.Boundary.OutwardUnitNormal
import TauCeti.Geometry.Manifold.MFDeriv.Slice

/-!
# The second fundamental form of the boundary

Let `M` be a Riemannian manifold with boundary modelled on the half-space `𝓡∂ (n + 1)`, with a
`C¹` metric on a `C²` manifold, and let `q ∈ ∂M`. The second fundamental form of the boundary at
`q` is the symmetric bilinear form on the tangent space `T_q∂M` of the boundary manifold

`II_q(u, w) = -Hess x⁰(dι u, dι w) / |dx⁰_q|`,

where `ι : ∂M → M` is the inclusion, `x⁰` is the normal coordinate of the preferred half-space
chart at `q` (positive inside, zero on `∂M`), and `Hess` is the Riemannian Hessian
`TauCeti.Manifold.hessian` of `M` at the boundary point `q`. It is written with `φ = -x⁰`, whose
unit gradient at `q` is the outward unit normal `ν_out(q)` (`TauCeti.outwardUnitNormal`):
`II_q(u, w) = Hess φ(dι u, dι w) / |grad φ(q)|`. The same formula holds with the normal coordinate
of every preferred chart whose source contains `q`.

With this sign the closed unit ball has `II = h`, the induced metric. The boundary is convex when
`II` is positive semidefinite, and strictly convex when `II` is positive definite.

## Main declarations

* `TauCeti.boundarySecondFundamentalForm`: the second fundamental form `II_q` as a bilinear form on
  the tangent space of the boundary manifold at `q`.
* `TauCeti.boundarySecondFundamentalForm_isSymm`: it is symmetric.
* `TauCeti.boundarySecondFundamentalForm_apply_eq_neg_inner_outwardUnitNormal`: for every vector
  field `W` differentiable at `q` and tangent to `∂M` along `∂M` near `q`, with `W(q) = dι w`,
  `II_q(u, w) = -⟨∇_{dι u} W, ν_out(q)⟩ = ⟨∇_{dι u} W, ν_in(q)⟩`.
* `TauCeti.boundarySecondFundamentalForm_apply_of_mem_chart_source`: the Hessian formula in every
  preferred chart whose source contains `q`. In particular `II_q` does not depend on the chart used
  to define it.

## References

* G. P. Paternain, M. Salo, G. Uhlmann, *Geometric Inverse Problems, with Emphasis on Two
  Dimensions*, Cambridge University Press (2023), §3.1 (the second fundamental form of the
  boundary and Lemma 3.1.12).
* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018), Chapter 8.
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

/-- The **second fundamental form of the boundary** at `q ∈ ∂M`: the bilinear form
`II_q(u, w) = -Hess x⁰(dι u, dι w) / |dx⁰_q|` on the tangent space of the boundary manifold at `q`,
where `ι : ∂M → M` is the inclusion and `x⁰` is the normal coordinate of the preferred chart at `q`.
It is written with `φ = -x⁰`, as `Hess φ(dι u, dι w) / |grad φ(q)|`. The unit sphere bounding the
closed unit ball has `II = h`. -/
def boundarySecondFundamentalForm (q : (𝓡∂ (n + 1)).boundary M) :
    LinearMap.BilinForm ℝ (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) q) :=
  ‖Manifold.mgradient (𝓡∂ (n + 1))
      (fun y ↦ -(chartAt (EuclideanHalfSpace (n + 1)) (q : M) y).val 0) q‖⁻¹ •
    LinearMap.BilinForm.comp
      ((𝓡∂ (n + 1)).hessianForm
        (fun y ↦ -(chartAt (EuclideanHalfSpace (n + 1)) (q : M) y).val 0) q).toLinearMap₁₂
      (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡∂ (n + 1))
        (Subtype.val : (𝓡∂ (n + 1)).boundary M → M) q).toLinearMap
      (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡∂ (n + 1))
        (Subtype.val : (𝓡∂ (n + 1)).boundary M → M) q).toLinearMap

/-- The defining formula of `TauCeti.boundarySecondFundamentalForm`. -/
theorem boundarySecondFundamentalForm_apply (q : (𝓡∂ (n + 1)).boundary M)
    (u w : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) q) :
    boundarySecondFundamentalForm q u w =
      ‖Manifold.mgradient (𝓡∂ (n + 1))
        (fun y ↦ -(chartAt (EuclideanHalfSpace (n + 1)) (q : M) y).val 0) q‖⁻¹ *
      Manifold.hessian (𝓡∂ (n + 1))
        (fun y ↦ -(chartAt (EuclideanHalfSpace (n + 1)) (q : M) y).val 0) q
        (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡∂ (n + 1))
          (Subtype.val : (𝓡∂ (n + 1)).boundary M → M) q u)
        (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡∂ (n + 1))
          (Subtype.val : (𝓡∂ (n + 1)).boundary M → M) q w) := by
  simp [boundarySecondFundamentalForm]

/-- The second fundamental form of the boundary is symmetric. -/
theorem boundarySecondFundamentalForm_isSymm (q : (𝓡∂ (n + 1)).boundary M) :
    (boundarySecondFundamentalForm q).IsSymm := by
  refine ⟨fun u w ↦ ?_⟩
  rw [boundarySecondFundamentalForm_apply, boundarySecondFundamentalForm_apply,
    Manifold.hessian_symm _ (contMDiffAt_neg_chartAt_normal (mem_chart_source _ _))]

/-- The Hessian formula of `TauCeti.boundarySecondFundamentalForm`, written in a preferred chart
whose source contains `q`, is `-⟨∇_{dι u} W, ν_out(q)⟩` for every vector field `W` differentiable
at `q`, tangent to the boundary at the boundary points near `q`, with `W(q) = dι w`. -/
private theorem inv_norm_mul_hessian_eq_neg_inner_outwardUnitNormal {α : M}
    {q : (𝓡∂ (n + 1)).boundary M} (hq : (q : M) ∈ (chartAt (EuclideanHalfSpace (n + 1)) α).source)
    (u w : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) q)
    {W : (y : M) → TangentSpace (𝓡∂ (n + 1)) y} (hW : MDiffAt (T% W) (q : M))
    (hWq : W q = mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡∂ (n + 1))
      (Subtype.val : (𝓡∂ (n + 1)).boundary M → M) q w)
    (hWt : ∀ᶠ p in 𝓝 q, W p ∈ boundaryTangentSpace p) :
    ‖Manifold.mgradient (𝓡∂ (n + 1))
        (fun y ↦ -(chartAt (EuclideanHalfSpace (n + 1)) α y).val 0) q‖⁻¹ *
      Manifold.hessian (𝓡∂ (n + 1)) (fun y ↦ -(chartAt (EuclideanHalfSpace (n + 1)) α y).val 0) q
        (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡∂ (n + 1))
          (Subtype.val : (𝓡∂ (n + 1)).boundary M → M) q u)
        (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡∂ (n + 1))
          (Subtype.val : (𝓡∂ (n + 1)).boundary M → M) q w) =
      -⟪CovariantDerivative.leviCivitaConnection (𝓡∂ (n + 1)) M W q
        (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡∂ (n + 1))
          (Subtype.val : (𝓡∂ (n + 1)).boundary M → M) q u), outwardUnitNormal q⟫_ℝ := by
  set φ : M → ℝ := fun y ↦ -(chartAt (EuclideanHalfSpace (n + 1)) α y).val 0
  set ι : (𝓡∂ (n + 1)).boundary M → M := Subtype.val
  set V : (y : M) → TangentSpace (𝓡∂ (n + 1)) y :=
    FiberBundle.extend (EuclideanSpace ℝ (Fin (n + 1)))
      (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡∂ (n + 1)) ι q u)
  have hφ : ContMDiffAt (𝓡∂ (n + 1)) 𝓘(ℝ) 2 φ q := contMDiffAt_neg_chartAt_normal hq
  have hV : V q = mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡∂ (n + 1)) ι q u :=
    FiberBundle.extend_apply_self _ _
  have hH := Manifold.hessian_apply_eq_mvfderiv_sub (q : M) hφ V W hW
  rw [hV, hWq] at hH
  -- The function `y ↦ dφ_y (W y)` vanishes on the boundary near `q`, so its derivative along the
  -- boundary vanishes at `q`.
  have hgι : (fun y ↦ mvfderiv (𝓡∂ (n + 1)) φ y (W y)) ∘ ι =ᶠ[𝓝 q] 0 := by
    filter_upwards [hWt, ((chartAt (EuclideanHalfSpace (n + 1)) α).open_source.preimage
      continuous_subtypeVal).mem_nhds hq] with p hp hps
    simp only [Function.comp_apply, Pi.zero_apply, φ, ι]
    rw [mvfderiv_neg_chartAt_normal_apply hps,
      (mem_boundaryTangentSpace_iff_tangentCoordChange (by rwa [extChartAt_source]) _).mp hp,
      neg_zero]
  have hzero := mvfderiv_mfderiv_apply_eq_zero_of_comp_eventuallyEq_zero (I := 𝓡∂ (n + 1)) hgι u
  rw [hH, hzero, outwardUnitNormal_eq_normalize_mgradient
    (IsManifold.chart_mem_maximalAtlas _) hq, real_inner_comm,
    Manifold.inner_normalize_mgradient]
  ring

/-- **The second fundamental form through the connection.** Let `W` be a vector field on `M`,
differentiable at `q ∈ ∂M`, tangent to the boundary at the boundary points near `q`, with
`W(q) = dι w`. Then `II_q(u, w) = -⟨∇_{dι u} W, ν_out(q)⟩`, that is `⟨∇_{dι u} W, ν_in(q)⟩` for the
inward unit normal `ν_in = -ν_out`. -/
theorem boundarySecondFundamentalForm_apply_eq_neg_inner_outwardUnitNormal
    (q : (𝓡∂ (n + 1)).boundary M) (u w : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) q)
    {W : (y : M) → TangentSpace (𝓡∂ (n + 1)) y} (hW : MDiffAt (T% W) (q : M))
    (hWq : W q = mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡∂ (n + 1))
      (Subtype.val : (𝓡∂ (n + 1)).boundary M → M) q w)
    (hWt : ∀ᶠ p in 𝓝 q, W p ∈ boundaryTangentSpace p) :
    boundarySecondFundamentalForm q u w =
      -⟪CovariantDerivative.leviCivitaConnection (𝓡∂ (n + 1)) M W q
        (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡∂ (n + 1))
          (Subtype.val : (𝓡∂ (n + 1)).boundary M → M) q u), outwardUnitNormal q⟫_ℝ := by
  rw [boundarySecondFundamentalForm_apply]
  exact inv_norm_mul_hessian_eq_neg_inner_outwardUnitNormal (mem_chart_source _ _) u w hW hWq hWt

/-- **The second fundamental form in a chart.** For every preferred chart whose source contains
`q`, with normal coordinate `x⁰`,
`II_q(u, w) = -Hess x⁰(dι u, dι w) / |dx⁰_q| = Hess φ(dι u, dι w) / |grad φ(q)|` for `φ = -x⁰`. -/
theorem boundarySecondFundamentalForm_apply_of_mem_chart_source {α : M}
    {q : (𝓡∂ (n + 1)).boundary M} (hq : (q : M) ∈ (chartAt (EuclideanHalfSpace (n + 1)) α).source)
    (u w : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) q) :
    boundarySecondFundamentalForm q u w =
      ‖Manifold.mgradient (𝓡∂ (n + 1))
        (fun y ↦ -(chartAt (EuclideanHalfSpace (n + 1)) α y).val 0) q‖⁻¹ *
      Manifold.hessian (𝓡∂ (n + 1)) (fun y ↦ -(chartAt (EuclideanHalfSpace (n + 1)) α y).val 0) q
        (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡∂ (n + 1))
          (Subtype.val : (𝓡∂ (n + 1)).boundary M → M) q u)
        (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡∂ (n + 1))
          (Subtype.val : (𝓡∂ (n + 1)).boundary M → M) q w) := by
  obtain ⟨W, hW, hWq, hWt⟩ := exists_mdifferentiableAt_extension_mem_boundaryTangentSpace q w
  rw [boundarySecondFundamentalForm_apply_eq_neg_inner_outwardUnitNormal q u w hW hWq hWt,
    inv_norm_mul_hessian_eq_neg_inner_outwardUnitNormal hq u w hW hWq hWt]

end TauCeti
