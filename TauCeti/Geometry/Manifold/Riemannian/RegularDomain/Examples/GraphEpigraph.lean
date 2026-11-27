/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.RegularDomain.Boundary
public import TauCeti.Geometry.Manifold.Riemannian.Boundary.Convexity.Basic
import TauCeti.Analysis.Calculus.Gradient
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace
import TauCeti.Geometry.Manifold.Riemannian.Gradient.NormedSpace
import TauCeti.Geometry.Manifold.Riemannian.Gradient.RegularValue
import TauCeti.Geometry.Manifold.RegularValue.Scalar.Outward
import TauCeti.Geometry.Manifold.Riemannian.Laplacian

/-!
# The region above the graph of a function as a regular domain

Let `w : ℝ → ℝ` be smooth. In the Euclidean plane `ℝ²`, every value of `f(x, y) = w(x) - y`
(`TauCeti.graphSub`) is regular: `df(v) = w'(x) v₀ - v₁` is onto. Its gradient is `(w'(x), -1)`,
of length `√(1 + w'(x)²)` (`TauCeti.mgradient_graphSub`, `TauCeti.norm_mgradient_graphSub`). The
region `M = {y ≥ w(x)} = {f ≤ 0}` above the graph of `w` is therefore a regular sublevel, a manifold
with boundary the graph `{y = w(x)}`
(`TauCeti.graphEpigraph`, `TauCeti.mem_graphEpigraph_iff`, with the atlas
`TauCeti.graphEpigraphChartedSpace`;
`TauCeti.boundary_graphEpigraph`), with the metric pulled back along the inclusion `j : M → ℝ²`.
Since `Hess f(v, v') = w''(x) v₀ v'₀`, the second fundamental form of the boundary at
`q = (x, w(x))` is
`II_q(u, u') = w''(x) (dj dι u)₀ (dj dι u')₀ / |grad f|`
(`TauCeti.boundarySecondFundamentalForm_graphEpigraph_apply`), and a nonzero tangent vector of the
boundary has nonzero first coordinate, since it lies on the line `v₁ = w'(x) v₀`. Hence the boundary
is convex at `q` exactly when `w''(x) ≥ 0` (`TauCeti.isConvexAt_graphEpigraph_iff`), and strictly
convex exactly when `w''(x) > 0` (`TauCeti.isStrictlyConvexAt_graphEpigraph_iff`).
-/

public section

open Bundle Module Set Topology
open scoped ContDiff Manifold RealInnerProductSpace Gradient

noncomputable section

namespace TauCeti

/-- The coordinate projections of the plane. -/
local notation "π₀" => (EuclideanSpace.proj (0 : Fin 2) : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ)
local notation "π₁" => (EuclideanSpace.proj (1 : Fin 2) : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ)

/-- The Euclidean plane. -/
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

/-- The function `f(x, y) = w(x) - y` on the plane, whose sublevel `{f ≤ 0}` is the region above
the graph of `w` and whose zero level is the graph. -/
abbrev graphSub (w : ℝ → ℝ) : ℝ² → ℝ :=
  fun p ↦ w (p 0) - p 1

variable {w : ℝ → ℝ}

/-- The derivative of `f(x, y) = w(x) - y` is `v ↦ w'(x) v₀ - v₁`. -/
theorem hasFDerivAt_graphSub (hw : Differentiable ℝ w) (p : ℝ²) :
    HasFDerivAt (graphSub w) (deriv w (p 0) • π₀ - π₁) p :=
  ((hw (p 0)).hasDerivAt.comp_hasFDerivAt p (π₀).hasFDerivAt).sub (π₁).hasFDerivAt

/-- The smoothness of `f(x, y) = w(x) - y` on the plane, for `w` of class `C^k`. -/
theorem contMDiff_graphSub {k : ℕ∞ω} (hw : ContDiff ℝ k w) :
    ContMDiff 𝓘(ℝ, ℝ²) 𝓘(ℝ) k (graphSub w) :=
  ((hw.comp (π₀).contDiff).sub (π₁).contDiff).contMDiff

/-- On the flat plane, the gradient of `f(x, y) = w(x) - y` is `(w'(x), -1)`. -/
theorem mgradient_graphSub (hw : Differentiable ℝ w) (p : ℝ²) :
    Manifold.mgradient 𝓘(ℝ, ℝ²) (graphSub w) p = !₂[deriv w (p 0), -1] := by
  have h : HasGradientAt (graphSub w) !₂[deriv w (p 0), -1] p := by
    rw [hasGradientAt_iff_hasFDerivAt]
    convert hasFDerivAt_graphSub hw p using 1
    ext v
    simp [EuclideanSpace.inner_eq_star_dotProduct, Fin.sum_univ_two, dotProduct]
    ring
  exact (Manifold.mgradient_eq_gradient_of_eq rfl _ _).trans h.gradient

/-- On the flat plane, the gradient of `f(x, y) = w(x) - y` has length `√(1 + w'(x)²)`. -/
theorem norm_mgradient_graphSub (hw : Differentiable ℝ w) (p : ℝ²) :
    ‖Manifold.mgradient 𝓘(ℝ, ℝ²) (graphSub w) p‖ = √(1 + deriv w (p 0) ^ 2) := by
  rw [Manifold.norm_mgradient_eq_norm_gradient_of_eq rfl,
    ← Manifold.mgradient_eq_gradient_of_eq rfl, mgradient_graphSub hw,
    EuclideanSpace.norm_eq]
  simp [Fin.sum_univ_two, add_comm]

/-- Every value of `f(x, y) = w(x) - y` on the plane is regular: its derivative
`v ↦ w'(x) v₀ - v₁` is onto. -/
theorem isRegularValue_graphSub (hw : Differentiable ℝ w) (a : ℝ) :
    IsRegularValue 𝓘(ℝ, ℝ²) 𝓘(ℝ) (graphSub w) a := by
  rw [isRegularValue_iff]
  intro p _
  rw [isRegularPoint_iff_surjective_fderiv]
  intro t
  refine ⟨EuclideanSpace.single 1 (-t), ?_⟩
  rw [(hasFDerivAt_graphSub hw p).fderiv]
  simp

/-- On the flat plane, the Hessian of `f(x, y) = w(x) - y` is `w''(x) v₀ v'₀`. -/
private theorem hessian_graphSub (hw : ContDiff ℝ 2 w) (p : ℝ²)
    (v v' : TangentSpace 𝓘(ℝ, ℝ²) p) :
    Manifold.hessian 𝓘(ℝ, ℝ²) (graphSub w) p v v' =
      deriv^[2] w (p 0) * π₀ v * π₀ v' := by
  have hf : ContDiffAt ℝ 2 (graphSub w) p :=
    ((hw.comp (π₀).contDiff).sub (π₁).contDiff).contDiffAt
  have hgrad := (hf.gradient_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  rw [Manifold.hessian_eq_iteratedFDeriv_model_space hgrad, iteratedFDeriv_two_apply]
  simp only [Matrix.cons_val, NormedSpace.fromTangentSpace_apply]
  have hd : Differentiable ℝ w := hw.differentiable (by norm_num)
  have hD : fderiv ℝ (graphSub w) = fun q ↦ deriv w (q 0) • π₀ - π₁ :=
    funext fun q ↦ (hasFDerivAt_graphSub hd q).fderiv
  have hd' : DifferentiableAt ℝ (deriv w) (p 0) :=
    ((contDiff_succ_iff_deriv (n := 1)).1 hw).2.2.differentiable one_ne_zero (p 0)
  have h2 : HasFDerivAt (fun q : ℝ² ↦ deriv w (q 0) • π₀ - π₁)
      ((deriv (deriv w) (p 0) • π₀).smulRight π₀) p :=
    ((hd'.hasDerivAt.comp_hasFDerivAt (h₂ := deriv w) p (π₀).hasFDerivAt).smul_const
      π₀).sub_const π₁
  rw [hD, h2.fderiv, Function.iterate_succ_apply, Function.iterate_one]
  have key : ∀ a b : ℝ², ((deriv (deriv w) (p 0) • π₀).smulRight π₀) a b =
      deriv (deriv w) (p 0) * π₀ a * π₀ b := fun a b ↦ by
    simp only [ContinuousLinearMap.smulRight_apply, FunLike.coe_smul, Pi.smul_apply, smul_eq_mul]
  exact key v v'

/-- The closed region `{y ≥ w(x)} = {w(x) - y ≤ 0}` above the graph of `w` in the plane. -/
abbrev graphEpigraph (w : ℝ → ℝ) : Set ℝ² :=
  {p : ℝ² | graphSub w p ≤ 0}

/-- A point lies in the region above the graph of `w` exactly when `y ≥ w(x)`. -/
theorem mem_graphEpigraph_iff {p : ℝ²} : p ∈ graphEpigraph w ↔ w (p 0) ≤ p 1 :=
  sub_nonpos

/-- The half-space atlas of the region `{y ≥ w(x)} = {w(x) - y ≤ 0}` above the graph of `w`:
`TauCeti.scalarRegularSublevelChartedSpace` for `w(x) - y` at its regular value `0`. -/
abbrev graphEpigraphChartedSpace (hw : ContDiff ℝ ∞ w) :
    ChartedSpace (EuclideanHalfSpace (1 + 1)) (graphEpigraph w) :=
  scalarRegularSublevelChartedSpace ((contMDiff_graphSub hw).of_le ENat.LEInfty.out)
    (isRegularValue_graphSub (hw.differentiable (by simp)) 0)
    (finrank_euclideanSpace_fin (𝕜 := ℝ) (n := 2))

/-- The region above the graph of a smooth function is a smooth manifold with boundary. -/
theorem isManifold_graphEpigraph (hw : ContDiff ℝ ∞ w) :
    letI := graphEpigraphChartedSpace hw
    IsManifold (𝓡∂ (1 + 1)) ∞ (graphEpigraph w) :=
  isManifold_scalarRegularSublevel (isRegularValue_graphSub (hw.differentiable (by simp)) 0)
    (finrank_euclideanSpace_fin (𝕜 := ℝ) (n := 2)) ENat.LEInfty.out (contMDiff_graphSub hw)

/-- The boundary of the region above the graph of `w` is the graph `y = w(x)`, the level
`w(x) - y = 0`. -/
theorem boundary_graphEpigraph (hw : ContDiff ℝ ∞ w) :
    letI := graphEpigraphChartedSpace hw
    (𝓡∂ (1 + 1)).boundary (graphEpigraph w) =
      {q : graphEpigraph w | (q : ℝ²) 1 = w ((q : ℝ²) 0)} :=
  (boundary_scalarRegularSublevel (isRegularValue_graphSub (hw.differentiable (by simp)) 0)
    (finrank_euclideanSpace_fin (𝕜 := ℝ) (n := 2)) le_rfl
    (contMDiff_graphSub (hw.of_le (by simp)))).trans
    (Set.ext fun _ ↦ sub_eq_zero.trans eq_comm)

/-- The metric of the region above the graph of `w` pulled back along the inclusion
(`TauCeti.scalarRegularSublevelMetric`), as a Riemannian bundle structure. -/
abbrev graphEpigraphRiemannianBundle (hw : ContDiff ℝ ∞ w) :
    letI := graphEpigraphChartedSpace hw
    haveI := isManifold_graphEpigraph hw
    RiemannianBundle (fun p : graphEpigraph w ↦ TangentSpace (𝓡∂ (1 + 1)) p) :=
  letI := graphEpigraphChartedSpace hw
  haveI := isManifold_graphEpigraph hw
  ⟨(scalarRegularSublevelMetric (contMDiff_graphSub hw)
    (isRegularValue_graphSub (hw.differentiable (by simp)) 0)
    (finrank_euclideanSpace_fin (𝕜 := ℝ) (n := 2))).toRiemannianMetric⟩

/-- The pulled-back metric of the region above the graph of `w` is smooth. -/
theorem isContMDiffRiemannianBundle_graphEpigraph (hw : ContDiff ℝ ∞ w) :
    letI := graphEpigraphChartedSpace hw
    haveI := isManifold_graphEpigraph hw
    letI := graphEpigraphRiemannianBundle hw
    IsContMDiffRiemannianBundle (𝓡∂ (1 + 1)) ∞ (EuclideanSpace ℝ (Fin (1 + 1)))
      (fun p : graphEpigraph w ↦ TangentSpace (𝓡∂ (1 + 1)) p) :=
  letI := graphEpigraphChartedSpace hw
  haveI := isManifold_graphEpigraph hw
  letI := graphEpigraphRiemannianBundle hw
  ⟨(scalarRegularSublevelMetric (contMDiff_graphSub hw)
      (isRegularValue_graphSub (hw.differentiable (by simp)) 0)
      (finrank_euclideanSpace_fin (𝕜 := ℝ) (n := 2))).inner,
    (scalarRegularSublevelMetric (contMDiff_graphSub hw)
      (isRegularValue_graphSub (hw.differentiable (by simp)) 0)
      (finrank_euclideanSpace_fin (𝕜 := ℝ) (n := 2))).contMDiff, fun _ _ _ ↦ rfl⟩

/-- **The second fundamental form of the graph `y = w(x)`** bounding the region above it, at
`q = (x, w(x))`: `II_q(u, u') = w''(x) (dj dι u)₀ (dj dι u')₀ / |grad f|` for
`f(x, y) = w(x) - y`, where `|grad f| = √(1 + w'(x)²)` (`TauCeti.norm_mgradient_graphSub`). -/
theorem boundarySecondFundamentalForm_graphEpigraph_apply (hw : ContDiff ℝ ∞ w)
    (q : letI := graphEpigraphChartedSpace hw
      (𝓡∂ (1 + 1)).boundary (graphEpigraph w))
    (u u' : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) q) :
    letI := graphEpigraphChartedSpace hw
    haveI := isManifold_graphEpigraph hw
    letI := graphEpigraphRiemannianBundle hw
    haveI := isContMDiffRiemannianBundle_graphEpigraph hw
    boundarySecondFundamentalForm q u u' =
      deriv^[2] w ((q : ℝ²) 0) * π₀ (mfderiv (𝓡∂ (1 + 1)) 𝓘(ℝ, ℝ²)
        (Subtype.val : graphEpigraph w → ℝ²) q
        (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) (𝓡∂ (1 + 1))
          (Subtype.val : (𝓡∂ (1 + 1)).boundary (graphEpigraph w) → graphEpigraph w) q u)) *
        π₀ (mfderiv (𝓡∂ (1 + 1)) 𝓘(ℝ, ℝ²)
        (Subtype.val : graphEpigraph w → ℝ²) q
        (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) (𝓡∂ (1 + 1))
          (Subtype.val : (𝓡∂ (1 + 1)).boundary (graphEpigraph w) → graphEpigraph w) q u')) /
      ‖Manifold.mgradient 𝓘(ℝ, ℝ²) (graphSub w) (q : ℝ²)‖ := by
  let := graphEpigraphChartedSpace hw
  have := isManifold_graphEpigraph hw
  let := graphEpigraphRiemannianBundle hw
  have := isContMDiffRiemannianBundle_graphEpigraph hw
  rw [boundarySecondFundamentalForm_scalarRegularSublevel_apply (contMDiff_graphSub hw)
    (isRegularValue_graphSub (hw.differentiable (by simp)) 0)
    (finrank_euclideanSpace_fin (𝕜 := ℝ) (n := 2)) q u u',
    hessian_graphSub (hw.of_le (by simp))]

/-- A tangent vector of the graph `y = w(x)` at `q = (x, w(x))` lies on the tangent line
`v₁ = w'(x) v₀`. -/
theorem proj_one_mfderiv_graphEpigraph (hw : ContDiff ℝ ∞ w)
    (q : letI := graphEpigraphChartedSpace hw
      (𝓡∂ (1 + 1)).boundary (graphEpigraph w))
    (u : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) q) :
    letI := graphEpigraphChartedSpace hw
    haveI := isManifold_graphEpigraph hw
    π₁ (mfderiv (𝓡∂ (1 + 1)) 𝓘(ℝ, ℝ²)
        (Subtype.val : graphEpigraph w → ℝ²) q
        (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) (𝓡∂ (1 + 1))
          (Subtype.val : (𝓡∂ (1 + 1)).boundary (graphEpigraph w) → graphEpigraph w) q u)) =
      deriv w ((q : ℝ²) 0) * π₀ (mfderiv (𝓡∂ (1 + 1)) 𝓘(ℝ, ℝ²)
        (Subtype.val : graphEpigraph w → ℝ²) q
        (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) (𝓡∂ (1 + 1))
          (Subtype.val : (𝓡∂ (1 + 1)).boundary (graphEpigraph w) → graphEpigraph w) q u)) := by
  let := graphEpigraphChartedSpace hw
  have := isManifold_graphEpigraph hw
  have hd : Differentiable ℝ w := hw.differentiable (by simp)
  have h0 := (mvfderiv_mfderiv_subtypeVal_scalarRegularSublevel_eq_zero_iff
    (contMDiff_graphSub (hw.of_le (by simp))) (finrank_euclideanSpace_fin (𝕜 := ℝ) (n := 2))
    (isRegularValue_graphSub hd 0) _).2 (mfderiv_subtypeVal_mem_boundaryTangentSpace q u)
  rw [mvfderiv_eq_fderiv_apply, (hasFDerivAt_graphSub hd _).fderiv] at h0
  have key : ∀ a : ℝ², (deriv w ((q : ℝ²) 0) • π₀ - π₁) a =
      deriv w ((q : ℝ²) 0) * π₀ a - π₁ a := fun a ↦ by simp
  have h3 := h0.symm.trans (key _)
  linarith

/-- A nonzero tangent vector of the graph `y = w(x)` has nonzero first coordinate. -/
theorem proj_zero_mfderiv_graphEpigraph_ne_zero (hw : ContDiff ℝ ∞ w)
    (q : letI := graphEpigraphChartedSpace hw
      (𝓡∂ (1 + 1)).boundary (graphEpigraph w))
    {u : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) q} (hu : u ≠ 0) :
    letI := graphEpigraphChartedSpace hw
    haveI := isManifold_graphEpigraph hw
    π₀ (mfderiv (𝓡∂ (1 + 1)) 𝓘(ℝ, ℝ²)
        (Subtype.val : graphEpigraph w → ℝ²) q
        (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) (𝓡∂ (1 + 1))
          (Subtype.val : (𝓡∂ (1 + 1)).boundary (graphEpigraph w) → graphEpigraph w) q u)) ≠
      0 := by
  let := graphEpigraphChartedSpace hw
  have := isManifold_graphEpigraph hw
  intro h0
  have h1 := proj_one_mfderiv_graphEpigraph hw q u
  rw [h0, mul_zero] at h1
  have key : ∀ a : ℝ², π₀ a = 0 → π₁ a = 0 → a = 0 := by
    intro a ha0 ha1
    ext i
    fin_cases i
    · simpa using ha0
    · simpa using ha1
  have hV := key _ h0 h1
  apply hu
  apply injective_mfderiv_subtypeVal_boundary q
  apply (isInvertible_mfderiv_subtypeVal_scalarRegularSublevel
    (contMDiff_graphSub (hw.of_le (by simp)))
    (isRegularValue_graphSub (hw.differentiable (by simp)) 0)
    (finrank_euclideanSpace_fin (𝕜 := ℝ) (n := 2)) _).injective
  rw [map_zero, map_zero]
  exact hV

/-- On the tangent line of the graph `y = w(x)` at `q = (x, w(x))`, `II_q(u, u) = c b(u, u)` with
`c = w''(x) / |grad f|` and the positive definite form `b(u, u') = (dj dι u)₀ (dj dι u')₀`. -/
private theorem exists_boundarySecondFundamentalForm_graphEpigraph_eq_mul (hw : ContDiff ℝ ∞ w)
    (q : letI := graphEpigraphChartedSpace hw
      (𝓡∂ (1 + 1)).boundary (graphEpigraph w)) :
    letI := graphEpigraphChartedSpace hw
    haveI := isManifold_graphEpigraph hw
    letI := graphEpigraphRiemannianBundle hw
    haveI := isContMDiffRiemannianBundle_graphEpigraph hw
    ∃ b : LinearMap.BilinForm ℝ (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) q),
      (∀ u, u ≠ 0 → 0 < b u u) ∧ ∀ u, boundarySecondFundamentalForm q u u =
        deriv^[2] w ((q : ℝ²) 0) / ‖Manifold.mgradient 𝓘(ℝ, ℝ²)
          (graphSub w) (q : ℝ²)‖ * b u u := by
  let := graphEpigraphChartedSpace hw
  have := isManifold_graphEpigraph hw
  let := graphEpigraphRiemannianBundle hw
  have := isContMDiffRiemannianBundle_graphEpigraph hw
  let φ : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) q →L[ℝ] ℝ :=
    π₀ ∘L mfderiv (𝓡∂ (1 + 1)) 𝓘(ℝ, ℝ²) (Subtype.val : graphEpigraph w → ℝ²) q ∘L
      mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) (𝓡∂ (1 + 1))
        (Subtype.val : (𝓡∂ (1 + 1)).boundary (graphEpigraph w) → graphEpigraph w) q
  let b : LinearMap.BilinForm ℝ (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) q) :=
    (LinearMap.mul ℝ ℝ).compl₁₂ (φ : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) q →ₗ[ℝ] ℝ) φ
  -- `b u u` is `φ u * φ u`, the square of the first coordinate of `dj dι u`.
  have hb (u) : b u u = π₀ (mfderiv (𝓡∂ (1 + 1)) 𝓘(ℝ, ℝ²) (Subtype.val : graphEpigraph w → ℝ²) q
      (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) (𝓡∂ (1 + 1))
        (Subtype.val : (𝓡∂ (1 + 1)).boundary (graphEpigraph w) → graphEpigraph w) q u)) *
      π₀ (mfderiv (𝓡∂ (1 + 1)) 𝓘(ℝ, ℝ²) (Subtype.val : graphEpigraph w → ℝ²) q
      (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) (𝓡∂ (1 + 1))
        (Subtype.val : (𝓡∂ (1 + 1)).boundary (graphEpigraph w) → graphEpigraph w) q u)) := by
    simp only [b, φ, LinearMap.compl₁₂_apply, LinearMap.mul_apply', ContinuousLinearMap.coe_coe,
      ContinuousLinearMap.comp_apply]
    -- The inner composition is between tangent spaces, which `simp` does not match against `ℝ²`.
    exact congrArg (fun a ↦ π₀ a * π₀ a) (ContinuousLinearMap.comp_apply _ _ u)
  refine ⟨b, fun u hu ↦ hb u ▸ mul_self_pos.2 (proj_zero_mfderiv_graphEpigraph_ne_zero hw q hu),
    fun u ↦ ?_⟩
  rw [boundarySecondFundamentalForm_graphEpigraph_apply, hb]
  ring

/-- **Convexity of a graph.** The boundary of the region above the graph of a smooth `w` is convex
at `q = (x, w(x))` exactly when `w''(x) ≥ 0`. -/
theorem isConvexAt_graphEpigraph_iff (hw : ContDiff ℝ ∞ w)
    (q : letI := graphEpigraphChartedSpace hw
      (𝓡∂ (1 + 1)).boundary (graphEpigraph w)) :
    letI := graphEpigraphChartedSpace hw
    haveI := isManifold_graphEpigraph hw
    letI := graphEpigraphRiemannianBundle hw
    haveI := isContMDiffRiemannianBundle_graphEpigraph hw
    IsConvexAt q ↔ 0 ≤ deriv^[2] w ((q : ℝ²) 0) := by
  let := graphEpigraphChartedSpace hw
  have := isManifold_graphEpigraph hw
  let := graphEpigraphRiemannianBundle hw
  have := isContMDiffRiemannianBundle_graphEpigraph hw
  obtain ⟨b, hb, h⟩ := exists_boundarySecondFundamentalForm_graphEpigraph_eq_mul hw q
  rw [isConvexAt_iff_of_eq_mul hb h, le_div_iff₀ (norm_pos_iff.2
    ((isRegularValue_graphSub (hw.differentiable (by simp)) _).isRegularPoint
      rfl).mgradient_ne_zero), zero_mul]

/-- **Strict convexity of a graph.** The boundary of the region above the graph of a smooth `w`
is strictly convex at `q = (x, w(x))` exactly when `w''(x) > 0`. -/
theorem isStrictlyConvexAt_graphEpigraph_iff (hw : ContDiff ℝ ∞ w)
    (q : letI := graphEpigraphChartedSpace hw
      (𝓡∂ (1 + 1)).boundary (graphEpigraph w)) :
    letI := graphEpigraphChartedSpace hw
    haveI := isManifold_graphEpigraph hw
    letI := graphEpigraphRiemannianBundle hw
    haveI := isContMDiffRiemannianBundle_graphEpigraph hw
    IsStrictlyConvexAt q ↔ 0 < deriv^[2] w ((q : ℝ²) 0) := by
  let := graphEpigraphChartedSpace hw
  have := isManifold_graphEpigraph hw
  let := graphEpigraphRiemannianBundle hw
  have := isContMDiffRiemannianBundle_graphEpigraph hw
  obtain ⟨b, hb, h⟩ := exists_boundarySecondFundamentalForm_graphEpigraph_eq_mul hw q
  rw [isStrictlyConvexAt_iff_of_eq_mul hb h, div_pos_iff_of_pos_right (norm_pos_iff.2
    ((isRegularValue_graphSub (hw.differentiable (by simp)) _).isRegularPoint
      rfl).mgradient_ne_zero)]

end TauCeti
