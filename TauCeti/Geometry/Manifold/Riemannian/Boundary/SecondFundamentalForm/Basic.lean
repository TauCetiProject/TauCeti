/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Boundary.TangentSpace
public import TauCeti.Geometry.Manifold.Riemannian.Laplacian
public import TauCeti.Geometry.Manifold.Riemannian.Boundary.OutwardUnitNormal
public import TauCeti.Geometry.Manifold.Riemannian.InwardUnitNormal
import TauCeti.Analysis.InnerProductSpace.Nondegenerate
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

* `TauCeti.boundaryInducedForm`: the induced metric `h_q(u, w) = ⟨dι u, dι w⟩` on the tangent
  space `T_q∂M` of the boundary manifold, as a bilinear form; it is symmetric and nondegenerate.
* `TauCeti.boundarySecondFundamentalForm`: the second fundamental form `II_q` as a bilinear form on
  the tangent space of the boundary manifold at `q`.
* `TauCeti.boundarySecondFundamentalForm_isSymm`: it is symmetric.
* `TauCeti.boundarySecondFundamentalForm_apply_eq_neg_inner_outwardUnitNormal`: for every vector
  field `W` differentiable at `q` and tangent to `∂M` along `∂M` near `q`, with `W(q) = dι w`,
  `II_q(u, w) = -⟨∇_{dι u} W, ν_out(q)⟩ = ⟨∇_{dι u} W, ν_in(q)⟩`.
* `TauCeti.boundarySecondFundamentalForm_apply_of_mem_chart_source`: the Hessian formula in every
  preferred chart whose source contains `q`. In particular `II_q` does not depend on the chart used
  to define it.
* `TauCeti.IsBoundaryDefiningFunctionOn.boundarySecondFundamentalForm_apply`: for every boundary
  defining function `ρ` on a neighbourhood of `q`, `II_q(u, w) = -Hess ρ(dι u, dι w) / |dρ_q|`.
* `TauCeti.boundarySecondFundamentalForm_apply_eq_inner_of_eq_outwardUnitNormal`: for every vector
  field `N` differentiable at `q` and equal to `ν_out` along `∂M` near `q`,
  `II_q(u, w) = ⟨∇_{dι u} N, dι w⟩`.

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

omit [RiemannianBundle (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x)]
  [IsContMDiffRiemannianBundle (𝓡∂ (n + 1)) 1 (EuclideanSpace ℝ (Fin (n + 1)))
    (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x)] in
/-- The vector `dι u` at `q ∈ ∂M` extends to a vector field `V` on `M`, and every function on `M`
vanishing on the boundary near `q` has zero derivative along `V(q) = dι u`. -/
private theorem exists_extension_mvfderiv_eq_zero (q : (𝓡∂ (n + 1)).boundary M)
    (u : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) q) :
    ∃ V : (y : M) → TangentSpace (𝓡∂ (n + 1)) y,
      V q = mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡∂ (n + 1))
        (Subtype.val : (𝓡∂ (n + 1)).boundary M → M) q u ∧
      ∀ g : M → ℝ, (∀ᶠ p : (𝓡∂ (n + 1)).boundary M in 𝓝 q, g p = 0) →
        mvfderiv (𝓡∂ (n + 1)) g q (V q) = 0 := by
  refine ⟨FiberBundle.extend (EuclideanSpace ℝ (Fin (n + 1))) _,
    FiberBundle.extend_apply_self _ _, fun g hg ↦ ?_⟩
  rw [FiberBundle.extend_apply_self]
  exact mvfderiv_mfderiv_apply_eq_zero_of_comp_eventuallyEq_zero hg u

/-- Let `f` be `C²` at `q ∈ ∂M` and let `W` be a vector field differentiable at `q`, with
`W(q) = dι w`, such that `df(W)` vanishes at the boundary points near `q`. Then
`Hess f(dι u, dι w) = -df_q(∇_{dι u} W)`. -/
private theorem hessian_eq_neg_mvfderiv_of_eventually_mvfderiv_eq_zero {f : M → ℝ}
    {q : (𝓡∂ (n + 1)).boundary M} (hf : ContMDiffAt (𝓡∂ (n + 1)) 𝓘(ℝ) 2 f q)
    (u w : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) q)
    {W : (y : M) → TangentSpace (𝓡∂ (n + 1)) y} (hW : MDiffAt (T% W) (q : M))
    (hWq : W q = mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡∂ (n + 1))
      (Subtype.val : (𝓡∂ (n + 1)).boundary M → M) q w)
    (hfW : ∀ᶠ p : (𝓡∂ (n + 1)).boundary M in 𝓝 q, mvfderiv (𝓡∂ (n + 1)) f p (W p) = 0) :
    Manifold.hessian (𝓡∂ (n + 1)) f q
        (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡∂ (n + 1))
          (Subtype.val : (𝓡∂ (n + 1)).boundary M → M) q u)
        (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡∂ (n + 1))
          (Subtype.val : (𝓡∂ (n + 1)).boundary M → M) q w) =
      -mvfderiv (𝓡∂ (n + 1)) f q (CovariantDerivative.leviCivitaConnection (𝓡∂ (n + 1)) M W q
        (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡∂ (n + 1))
          (Subtype.val : (𝓡∂ (n + 1)).boundary M → M) q u)) := by
  obtain ⟨V, hV, hV0⟩ := exists_extension_mvfderiv_eq_zero q u
  have hH := Manifold.hessian_apply_eq_mvfderiv_sub (q : M) hf V W hW
  -- The function `y ↦ df_y (W y)` vanishes on the boundary near `q`, so its derivative along the
  -- boundary vanishes at `q`.
  rw [hV0 (fun y ↦ mvfderiv (𝓡∂ (n + 1)) f y (W y)) hfW, zero_sub, hV, hWq] at hH
  exact hH

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
  -- The derivative of the normal coordinate vanishes on vectors tangent to the boundary.
  have hφW : ∀ᶠ p : (𝓡∂ (n + 1)).boundary M in 𝓝 q,
      mvfderiv (𝓡∂ (n + 1)) (fun y ↦ -(chartAt (EuclideanHalfSpace (n + 1)) α y).val 0) p
        (W p) = 0 := by
    filter_upwards [hWt, ((chartAt (EuclideanHalfSpace (n + 1)) α).open_source.preimage
      continuous_subtypeVal).mem_nhds hq] with p hp hps
    rw [mvfderiv_neg_chartAt_normal_apply hps,
      (mem_boundaryTangentSpace_iff_tangentCoordChange (by rwa [extChartAt_source]) _).mp hp,
      neg_zero]
  rw [hessian_eq_neg_mvfderiv_of_eventually_mvfderiv_eq_zero
      (contMDiffAt_neg_chartAt_normal hq) u w hW hWq hφW,
    outwardUnitNormal_eq_normalize_mgradient (IsManifold.chart_mem_maximalAtlas _) hq,
    real_inner_comm, Manifold.inner_normalize_mgradient, mul_neg]

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


/-- **The second fundamental form through a boundary defining function.** For a boundary defining
function `ρ` on an open set containing `q ∈ ∂M`, `II_q(u, w) = -Hess ρ(dι u, dι w) / |dρ_q|`. -/
theorem IsBoundaryDefiningFunctionOn.boundarySecondFundamentalForm_apply {ρ : M → ℝ} {U : Set M}
    (hρ : IsBoundaryDefiningFunctionOn n ρ U) {q : (𝓡∂ (n + 1)).boundary M} (hqU : (q : M) ∈ U)
    (u w : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) q) :
    boundarySecondFundamentalForm q u w =
      -Manifold.hessian (𝓡∂ (n + 1)) ρ q
          (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡∂ (n + 1))
            (Subtype.val : (𝓡∂ (n + 1)).boundary M → M) q u)
          (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡∂ (n + 1))
            (Subtype.val : (𝓡∂ (n + 1)).boundary M → M) q w) /
        ‖mvfderiv (𝓡∂ (n + 1)) ρ q‖ := by
  obtain ⟨W, hW, hWq, hWt⟩ := exists_mdifferentiableAt_extension_mem_boundaryTangentSpace q w
  have hρq : ContMDiffAt (𝓡∂ (n + 1)) 𝓘(ℝ) 2 ρ q :=
    ((hρ.contMDiffOn (q : M) hqU).contMDiffAt (hρ.isOpen.mem_nhds hqU)).of_le
      (by simp)
  -- The derivative of `ρ` vanishes on vectors tangent to the boundary.
  have hρW : ∀ᶠ p : (𝓡∂ (n + 1)).boundary M in 𝓝 q, mvfderiv (𝓡∂ (n + 1)) ρ p (W p) = 0 := by
    filter_upwards [hWt, (hρ.isOpen.preimage continuous_subtypeVal).mem_nhds hqU] with p hp hpU
    exact (hρ.mvfderiv_eq_zero_iff hpU (W p)).mpr hp
  have hne : ‖mvfderiv (𝓡∂ (n + 1)) ρ q‖ ≠ 0 :=
    by simpa using hρ.mvfderiv_ne_zero (q : M) hqU q.property
  rw [boundarySecondFundamentalForm_apply_eq_neg_inner_outwardUnitNormal q u w hW hWq hWt,
    hessian_eq_neg_mvfderiv_of_eventually_mvfderiv_eq_zero hρq u w hW hWq hρW,
    ← Manifold.inner_mgradient, hρ.mgradient_eq_norm_smul_inwardUnitNormal hqU,
    inwardUnitNormal_def, real_inner_smul_left, inner_neg_left, real_inner_comm, eq_div_iff hne]
  -- `-⟨ν, ∇W⟩ * |dρ_q| = -(-(|dρ_q| * -⟨ν, ∇W⟩))`
  ring


/-- **The second fundamental form through an extension of the outward normal.** Let `N` be a
vector field on `M`, differentiable at `q ∈ ∂M`, equal to the outward unit normal at the boundary
points near `q`. Then `II_q(u, w) = ⟨∇_{dι u} N, dι w⟩`; with the inward normal `ν_in = -N` this
is `-⟨∇_{dι u} ν_in, dι w⟩`. -/
theorem boundarySecondFundamentalForm_apply_eq_inner_of_eq_outwardUnitNormal
    (q : (𝓡∂ (n + 1)).boundary M) (u w : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) q)
    {N : (y : M) → TangentSpace (𝓡∂ (n + 1)) y} (hN : MDiffAt (T% N) (q : M))
    (hNν : ∀ᶠ p : (𝓡∂ (n + 1)).boundary M in 𝓝 q, N p = outwardUnitNormal p) :
    boundarySecondFundamentalForm q u w =
      ⟪CovariantDerivative.leviCivitaConnection (𝓡∂ (n + 1)) M N q
        (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡∂ (n + 1))
          (Subtype.val : (𝓡∂ (n + 1)).boundary M → M) q u),
        mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡∂ (n + 1))
          (Subtype.val : (𝓡∂ (n + 1)).boundary M → M) q w⟫_ℝ := by
  obtain ⟨W, hW, hWq, hWt⟩ := exists_mdifferentiableAt_extension_mem_boundaryTangentSpace q w
  obtain ⟨V, hV, hV0⟩ := exists_extension_mvfderiv_eq_zero q u
  -- Metric compatibility: `d⟨N, W⟩(V) = ⟨∇_V N, W⟩ + ⟨N, ∇_V W⟩` at `q`.
  have hc :=
    (CovariantDerivative.isMetricCompatible_leviCivitaConnection (𝓡∂ (n + 1)) (M := M)
      ).mvfderiv_inner_eq (x := (q : M)) V hN hW
  -- The function `⟨N, W⟩` vanishes on the boundary near `q`.
  have hgι : ∀ᶠ p : (𝓡∂ (n + 1)).boundary M in 𝓝 q, ⟪N p, W p⟫_ℝ = 0 := by
    filter_upwards [hWt, hNν] with p hp hpN
    rw [hpN]
    exact inner_outwardUnitNormal_of_mem_boundaryTangentSpace hp
  rw [hV0 (fun y ↦ ⟪N y, W y⟫_ℝ) hgι] at hc
  simp only [hV] at hc
  rw [boundarySecondFundamentalForm_apply_eq_neg_inner_outwardUnitNormal q u w hW hWq hWt,
    ← hWq, ← hNν.self_of_nhds, real_inner_comm (N q)]
  linarith

/-! ### The induced metric -/

section InducedForm

omit [IsManifold (𝓡∂ (n + 1)) 2 M]
  [IsContMDiffRiemannianBundle (𝓡∂ (n + 1)) 1 (EuclideanSpace ℝ (Fin (n + 1)))
    (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x)]

/-- The **induced metric** `h_q(u, w) = ⟨dι u, dι w⟩` on the tangent space of the boundary at
`q ∈ ∂M`, as a bilinear form, where `ι : ∂M → M` is the inclusion. -/
def boundaryInducedForm (q : (𝓡∂ (n + 1)).boundary M) :
    LinearMap.BilinForm ℝ (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) q) :=
  (innerₗ (TangentSpace (𝓡∂ (n + 1)) (q : M))).compl₁₂
    (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡∂ (n + 1))
      (Subtype.val : (𝓡∂ (n + 1)).boundary M → M) q).toLinearMap
    (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡∂ (n + 1))
      (Subtype.val : (𝓡∂ (n + 1)).boundary M → M) q).toLinearMap

/-- The defining formula of `TauCeti.boundaryInducedForm`. -/
theorem boundaryInducedForm_apply (q : (𝓡∂ (n + 1)).boundary M)
    (u w : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) q) :
    boundaryInducedForm q u w =
      ⟪mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡∂ (n + 1))
          (Subtype.val : (𝓡∂ (n + 1)).boundary M → M) q u,
        mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡∂ (n + 1))
          (Subtype.val : (𝓡∂ (n + 1)).boundary M → M) q w⟫_ℝ :=
  (rfl)

/-- The induced metric is symmetric. -/
theorem boundaryInducedForm_isSymm (q : (𝓡∂ (n + 1)).boundary M) :
    (boundaryInducedForm q).IsSymm :=
  ⟨fun u w ↦ by rw [boundaryInducedForm_apply, real_inner_comm, ← boundaryInducedForm_apply]⟩

/-- The induced metric is nondegenerate: the differential of the inclusion is injective. -/
theorem boundaryInducedForm_nondegenerate (q : (𝓡∂ (n + 1)).boundary M) :
    (boundaryInducedForm q).Nondegenerate :=
  nondegenerate_inner_comp (injective_mfderiv_subtypeVal_boundary q)

/-- The induced metric is the inner product of `T_q∂M ⊆ T_qM`, transported along
`TauCeti.boundaryTangentEquiv`. -/
theorem boundaryInducedForm_eq_inner_boundaryTangentEquiv (q : (𝓡∂ (n + 1)).boundary M)
    (u w : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) q) :
    boundaryInducedForm q u w = ⟪boundaryTangentEquiv q u, boundaryTangentEquiv q w⟫_ℝ := by
  rw [Submodule.coe_inner, coe_boundaryTangentEquiv_apply, coe_boundaryTangentEquiv_apply,
    boundaryInducedForm_apply]

end InducedForm

end TauCeti
