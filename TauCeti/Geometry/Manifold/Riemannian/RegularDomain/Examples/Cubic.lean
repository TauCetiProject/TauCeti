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
import TauCeti.Geometry.Manifold.RegularValue.Scalar.Outward
import TauCeti.Geometry.Manifold.Riemannian.Laplacian

/-!
# The region above the cubic `y = x³` as a regular domain

In the Euclidean plane `ℝ²`, every value of `f(x, y) = x³ - y` is regular: `df(v) = 3x² v₀ - v₁`
is onto. The region `M = {y ≥ x³} = {f ≤ 0}` is therefore a regular sublevel, a manifold with
boundary `{y = x³}` (`TauCeti.cubicEpigraph`, with the atlas `TauCeti.cubicEpigraphChartedSpace`),
with the metric pulled back along the
inclusion `j : M → ℝ²`. Since `Hess f(v, w) = 6x v₀ w₀`, the second fundamental form of the
boundary at `q = (x, x³)` is
`II_q(u, w) = 6x (dj dι u)₀ (dj dι w)₀ / |grad f|`
(`TauCeti.boundarySecondFundamentalForm_cubicEpigraph_apply`), and a nonzero tangent vector of the
boundary has nonzero first coordinate, since it lies on the line `v₁ = 3x² v₀`. Hence:

* the boundary is convex at `q` exactly when `x ≥ 0`
  (`TauCeti.isConvexAt_cubicEpigraph_iff`), and strictly convex exactly when `x > 0`
  (`TauCeti.isStrictlyConvexAt_cubicEpigraph_iff`);
* the set of points of the boundary at which it is convex is not open
  (`TauCeti.not_isOpen_setOf_isConvexAt_cubicEpigraph`): it contains the origin, but not the
  points `(-t, -t³)`, `t > 0`, which tend to it.

This is the Check of RiemannianManifoldsWithConvexBoundary §2.3 that convexity without strictness
is not an open condition, unlike strict convexity.
-/

public section

open Bundle Module Set Topology
open scoped ContDiff Manifold RealInnerProductSpace Gradient

noncomputable section

namespace TauCeti

/-- The coordinate projections of the plane. -/
local notation "π₀" => (EuclideanSpace.proj (0 : Fin 2) : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ)
local notation "π₁" => (EuclideanSpace.proj (1 : Fin 2) : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ)

/-- The derivative of `f(x, y) = x³ - y` is `v ↦ 3x² v₀ - v₁`. -/
private theorem hasFDerivAt_cubicSub (p : EuclideanSpace ℝ (Fin 2)) :
    HasFDerivAt (fun p : EuclideanSpace ℝ (Fin 2) ↦ p 0 ^ (3 : ℕ) - p 1)
      ((3 * p 0 ^ 2) • π₀ - π₁) p := by
  have h := ((π₀).hasFDerivAt.pow 3).sub (π₁).hasFDerivAt (x := p)
  convert h using 2 <;> congr 1
  simp [nsmul_eq_mul]

/-- The smoothness of `f(x, y) = x³ - y` on the plane. -/
theorem contMDiff_cubicSub {k : ℕ∞ω} :
    ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) 𝓘(ℝ) k
      (fun p : EuclideanSpace ℝ (Fin 2) ↦ p 0 ^ (3 : ℕ) - p 1) :=
  (((π₀).contDiff.pow 3).sub (π₁).contDiff).contMDiff

/-- Every value of `f(x, y) = x³ - y` on the plane is regular: its derivative
`v ↦ 3x² v₀ - v₁` is onto. -/
theorem isRegularValue_cubicSub (a : ℝ) :
    IsRegularValue 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) 𝓘(ℝ)
      (fun p : EuclideanSpace ℝ (Fin 2) ↦ p 0 ^ (3 : ℕ) - p 1) a := by
  rw [isRegularValue_iff]
  intro p _
  rw [isRegularPoint_iff_surjective_fderiv]
  intro t
  refine ⟨EuclideanSpace.single 1 (-t), ?_⟩
  rw [(hasFDerivAt_cubicSub p).fderiv]
  simp

/-- On the flat plane, the Hessian of `f(x, y) = x³ - y` is `6x v₀ w₀`. -/
private theorem hessian_cubicSub (p : EuclideanSpace ℝ (Fin 2))
    (v w : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) p) :
    Manifold.hessian 𝓘(ℝ, EuclideanSpace ℝ (Fin 2))
        (fun p : EuclideanSpace ℝ (Fin 2) ↦ p 0 ^ (3 : ℕ) - p 1) p v w =
      6 * p 0 * π₀ v * π₀ w := by
  have hf : ContDiffAt ℝ 2 (fun p : EuclideanSpace ℝ (Fin 2) ↦ p 0 ^ (3 : ℕ) - p 1) p :=
    (((π₀).contDiff.pow 3).sub (π₁).contDiff).contDiffAt
  have hgrad := (hf.gradient_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  rw [Manifold.hessian_eq_iteratedFDeriv_model_space hgrad, iteratedFDeriv_two_apply]
  simp only [Matrix.cons_val, NormedSpace.fromTangentSpace_apply]
  have hD : fderiv ℝ (fun p : EuclideanSpace ℝ (Fin 2) ↦ p 0 ^ (3 : ℕ) - p 1) =
      fun q ↦ (3 * q 0 ^ 2) • π₀ - π₁ :=
    funext fun q ↦ (hasFDerivAt_cubicSub q).fderiv
  have h2 : HasFDerivAt (fun q : EuclideanSpace ℝ (Fin 2) ↦ (3 * q 0 ^ 2) • π₀ - π₁)
      (((3 : ℝ) • ((2 * p 0) • π₀)).smulRight π₀) p := by
    have hc : HasFDerivAt (fun q : EuclideanSpace ℝ (Fin 2) ↦ 3 * q 0 ^ 2)
        ((3 : ℝ) • ((2 * p 0) • π₀)) p := by
      convert ((π₀).hasFDerivAt.pow 2).const_mul (3 : ℝ) (x := p) using 2 <;> congr 1
      simp [nsmul_eq_mul]
    exact (hc.smul_const π₀).sub_const π₁
  rw [hD, h2.fderiv]
  have key : ∀ a b : EuclideanSpace ℝ (Fin 2),
      (((3 : ℝ) • ((2 * p 0) • π₀)).smulRight π₀) a b = 6 * p 0 * π₀ a * π₀ b := by
    intro a b
    simp only [ContinuousLinearMap.smulRight_apply, FunLike.coe_smul,
      Pi.smul_apply, smul_eq_mul]
    ring
  exact key v w

/-- The closed region `{y ≥ x³} = {x³ - y ≤ 0}` above the cubic `y = x³` in the plane. -/
abbrev cubicEpigraph : Set (EuclideanSpace ℝ (Fin 2)) :=
  {p : EuclideanSpace ℝ (Fin 2) | p 0 ^ (3 : ℕ) - p 1 ≤ 0}

/-- The Euclidean plane. -/
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

/-- The half-space atlas of the region `{y ≥ x³} = {x³ - y ≤ 0}` above the cubic:
`TauCeti.scalarRegularSublevelChartedSpace` for `x³ - y` at its regular value `0`. -/
abbrev cubicEpigraphChartedSpace :
    ChartedSpace (EuclideanHalfSpace (1 + 1))
      cubicEpigraph :=
  scalarRegularSublevelChartedSpace (contMDiff_cubicSub (k := ∞).of_le ENat.LEInfty.out)
    (isRegularValue_cubicSub 0) (finrank_euclideanSpace_fin (𝕜 := ℝ) (n := 2))

/-- The region above the cubic is a smooth manifold with boundary. -/
theorem isManifold_cubicEpigraph :
    letI := cubicEpigraphChartedSpace
    IsManifold (𝓡∂ (1 + 1)) ∞ cubicEpigraph :=
  isManifold_scalarRegularSublevel (isRegularValue_cubicSub 0)
    (finrank_euclideanSpace_fin (𝕜 := ℝ) (n := 2)) ENat.LEInfty.out (contMDiff_cubicSub (k := ∞))

/-- The metric of the region above the cubic pulled back along the inclusion
(`TauCeti.scalarRegularSublevelMetric`), as a Riemannian bundle structure. -/
abbrev cubicEpigraphRiemannianBundle :
    letI := cubicEpigraphChartedSpace
    haveI := isManifold_cubicEpigraph
    RiemannianBundle (fun p : cubicEpigraph ↦
      TangentSpace (𝓡∂ (1 + 1)) p) :=
  letI := cubicEpigraphChartedSpace
  haveI := isManifold_cubicEpigraph
  ⟨(scalarRegularSublevelMetric (contMDiff_cubicSub (k := ∞)) (isRegularValue_cubicSub 0)
    (finrank_euclideanSpace_fin (𝕜 := ℝ) (n := 2))).toRiemannianMetric⟩

/-- The pulled-back metric of the region above the cubic is smooth. -/
theorem isContMDiffRiemannianBundle_cubicEpigraph :
    letI := cubicEpigraphChartedSpace
    haveI := isManifold_cubicEpigraph
    letI := cubicEpigraphRiemannianBundle
    IsContMDiffRiemannianBundle (𝓡∂ (1 + 1)) ∞ (EuclideanSpace ℝ (Fin (1 + 1)))
      (fun p : cubicEpigraph ↦
        TangentSpace (𝓡∂ (1 + 1)) p) :=
  letI := cubicEpigraphChartedSpace
  haveI := isManifold_cubicEpigraph
  letI := cubicEpigraphRiemannianBundle
  ⟨(scalarRegularSublevelMetric (contMDiff_cubicSub (k := ∞)) (isRegularValue_cubicSub 0)
      (finrank_euclideanSpace_fin (𝕜 := ℝ) (n := 2))).inner,
    (scalarRegularSublevelMetric (contMDiff_cubicSub (k := ∞)) (isRegularValue_cubicSub 0)
      (finrank_euclideanSpace_fin (𝕜 := ℝ) (n := 2))).contMDiff, fun _ _ _ ↦ rfl⟩

/-- The gradient of `f(x, y) = x³ - y` never vanishes. -/
private theorem norm_mgradient_cubicSub_pos (p : ℝ²) :
    0 < ‖Manifold.mgradient 𝓘(ℝ, ℝ²)
      (fun p : ℝ² ↦ p 0 ^ (3 : ℕ) - p 1) p‖ := by
  refine norm_pos_iff.2 fun h ↦ ?_
  have h1 := Manifold.inner_mgradient_model_space
    (fun p : ℝ² ↦ p 0 ^ (3 : ℕ) - p 1) p (EuclideanSpace.single 1 (-1))
  rw [h, inner_zero_left, (hasFDerivAt_cubicSub p).fderiv] at h1
  simp at h1

/-- **The second fundamental form of the cubic `y = x³`** bounding the region above it, at
`q = (x, x³)`: `II_q(u, w) = 6x (dj dι u)₀ (dj dι w)₀ / |grad f|` for `f(x, y) = x³ - y`. -/
theorem boundarySecondFundamentalForm_cubicEpigraph_apply
    (q : letI := cubicEpigraphChartedSpace
      (𝓡∂ (1 + 1)).boundary cubicEpigraph)
    (u w : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) q) :
    letI := cubicEpigraphChartedSpace
    haveI := isManifold_cubicEpigraph
    letI := cubicEpigraphRiemannianBundle
    haveI := isContMDiffRiemannianBundle_cubicEpigraph
    boundarySecondFundamentalForm q u w =
      6 * (q : ℝ²) 0 * π₀ (mfderiv (𝓡∂ (1 + 1)) 𝓘(ℝ, ℝ²)
        (Subtype.val : cubicEpigraph → ℝ²) q
        (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) (𝓡∂ (1 + 1))
          (Subtype.val : (𝓡∂ (1 + 1)).boundary cubicEpigraph → cubicEpigraph) q u)) *
        π₀ (mfderiv (𝓡∂ (1 + 1)) 𝓘(ℝ, ℝ²)
        (Subtype.val : cubicEpigraph → ℝ²) q
        (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) (𝓡∂ (1 + 1))
          (Subtype.val : (𝓡∂ (1 + 1)).boundary cubicEpigraph → cubicEpigraph) q w)) /
      ‖Manifold.mgradient 𝓘(ℝ, ℝ²)
        (fun p : ℝ² ↦ p 0 ^ (3 : ℕ) - p 1) (q : ℝ²)‖ := by
  let := cubicEpigraphChartedSpace
  have := isManifold_cubicEpigraph
  let := cubicEpigraphRiemannianBundle
  have := isContMDiffRiemannianBundle_cubicEpigraph
  rw [boundarySecondFundamentalForm_scalarRegularSublevel_apply (contMDiff_cubicSub (k := ∞))
    (isRegularValue_cubicSub 0) (finrank_euclideanSpace_fin (𝕜 := ℝ) (n := 2)) q u w,
    hessian_cubicSub]

/-- A tangent vector of the cubic `y = x³` at `q = (x, x³)` lies on the tangent line
`v₁ = 3x² v₀`. -/
theorem proj_one_mfderiv_cubicEpigraph
    (q : letI := cubicEpigraphChartedSpace
      (𝓡∂ (1 + 1)).boundary cubicEpigraph)
    (u : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) q) :
    letI := cubicEpigraphChartedSpace
    haveI := isManifold_cubicEpigraph
    π₁ (mfderiv (𝓡∂ (1 + 1)) 𝓘(ℝ, ℝ²)
        (Subtype.val : cubicEpigraph → ℝ²) q
        (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) (𝓡∂ (1 + 1))
          (Subtype.val : (𝓡∂ (1 + 1)).boundary cubicEpigraph → cubicEpigraph) q u)) =
      3 * (q : ℝ²) 0 ^ 2 * π₀ (mfderiv (𝓡∂ (1 + 1)) 𝓘(ℝ, ℝ²)
        (Subtype.val : cubicEpigraph → ℝ²) q
        (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) (𝓡∂ (1 + 1))
          (Subtype.val : (𝓡∂ (1 + 1)).boundary cubicEpigraph → cubicEpigraph) q u)) := by
  let := cubicEpigraphChartedSpace
  have := isManifold_cubicEpigraph
  have hq : (q : ℝ²) 0 ^ (3 : ℕ) - (q : ℝ²) 1 = 0 :=
    (Set.ext_iff.1 (boundary_scalarRegularSublevel (isRegularValue_cubicSub 0)
      (finrank_euclideanSpace_fin (𝕜 := ℝ) (n := 2)) le_rfl (contMDiff_cubicSub (k := 1))) q).1
      q.property
  set v := mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) (𝓡∂ (1 + 1))
    (Subtype.val : (𝓡∂ (1 + 1)).boundary cubicEpigraph → cubicEpigraph) q u
  have hT : v ∈ boundaryTangentSpace q := mfderiv_subtypeVal_mem_boundaryTangentSpace q u
  have hout := fun w ↦ isOutwardPointing_scalarRegularSublevel_iff_mfderiv
    (contMDiff_cubicSub (k := 1)) (finrank_euclideanSpace_fin (𝕜 := ℝ) (n := 2))
    (isRegularValue_cubicSub 0) hq w
  have h1 := mt (hout v).2 fun h ↦ h.notMem_boundaryTangentSpace hT
  have h2 := mt (hout (-v)).2 fun h ↦ h.notMem_boundaryTangentSpace (neg_mem hT)
  rw [map_neg, map_neg, neg_pos, not_lt] at h2
  have h0 := le_antisymm h2 (not_lt.1 h1)
  rw [mvfderiv_eq_fderiv_apply, (hasFDerivAt_cubicSub _).fderiv] at h0
  have key : ∀ a : ℝ²,
      ((3 * (q : ℝ²) 0 ^ 2) • π₀ - π₁) a = 3 * (q : ℝ²) 0 ^ 2 * π₀ a - π₁ a := fun a ↦ by simp
  have h3 := h0.trans (key _)
  linarith

/-- A nonzero tangent vector of the cubic `y = x³` has nonzero first coordinate. -/
theorem proj_zero_mfderiv_cubicEpigraph_ne_zero
    (q : letI := cubicEpigraphChartedSpace
      (𝓡∂ (1 + 1)).boundary cubicEpigraph)
    {u : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) q} (hu : u ≠ 0) :
    letI := cubicEpigraphChartedSpace
    haveI := isManifold_cubicEpigraph
    π₀ (mfderiv (𝓡∂ (1 + 1)) 𝓘(ℝ, ℝ²)
        (Subtype.val : cubicEpigraph → ℝ²) q
        (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) (𝓡∂ (1 + 1))
          (Subtype.val : (𝓡∂ (1 + 1)).boundary cubicEpigraph → cubicEpigraph) q u)) ≠ 0 := by
  let := cubicEpigraphChartedSpace
  have := isManifold_cubicEpigraph
  intro h0
  have h1 := proj_one_mfderiv_cubicEpigraph q u
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
  apply (isInvertible_mfderiv_subtypeVal_scalarRegularSublevel (contMDiff_cubicSub (k := 1))
    (isRegularValue_cubicSub 0) (finrank_euclideanSpace_fin (𝕜 := ℝ) (n := 2)) _).injective
  rw [map_zero, map_zero]
  exact hV

/-- A nonzero tangent vector of the boundary of the region above the cubic. -/
private theorem exists_ne_zero_tangentSpace_cubicEpigraph
    (q : letI := cubicEpigraphChartedSpace
      (𝓡∂ (1 + 1)).boundary cubicEpigraph) :
    ∃ u : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) q, u ≠ 0 := by
  obtain ⟨u, hu⟩ := exists_ne (0 : EuclideanSpace ℝ (Fin 1))
  exact ⟨u, hu⟩

/-- **Convexity of the cubic `y = x³`.** The boundary of the region above the cubic is convex at
`q = (x, x³)` exactly when `x ≥ 0`. -/
theorem isConvexAt_cubicEpigraph_iff
    (q : letI := cubicEpigraphChartedSpace
      (𝓡∂ (1 + 1)).boundary cubicEpigraph) :
    letI := cubicEpigraphChartedSpace
    haveI := isManifold_cubicEpigraph
    letI := cubicEpigraphRiemannianBundle
    haveI := isContMDiffRiemannianBundle_cubicEpigraph
    IsConvexAt q ↔ 0 ≤ (q : ℝ²) 0 := by
  let := cubicEpigraphChartedSpace
  have := isManifold_cubicEpigraph
  let := cubicEpigraphRiemannianBundle
  have := isContMDiffRiemannianBundle_cubicEpigraph
  have hg := norm_mgradient_cubicSub_pos (q : ℝ²)
  rw [isConvexAt_iff]
  constructor
  · intro h
    obtain ⟨u, hu⟩ := exists_ne_zero_tangentSpace_cubicEpigraph q
    have ha := proj_zero_mfderiv_cubicEpigraph_ne_zero q hu
    have h' := h u
    rw [boundarySecondFundamentalForm_cubicEpigraph_apply, le_div_iff₀ hg, zero_mul] at h'
    have := mul_self_pos.2 ha
    nlinarith
  · intro hx u
    rw [boundarySecondFundamentalForm_cubicEpigraph_apply]
    refine div_nonneg ?_ hg.le
    have := mul_self_nonneg (π₀ (mfderiv (𝓡∂ (1 + 1)) 𝓘(ℝ, ℝ²)
            (Subtype.val : cubicEpigraph → ℝ²) q
            (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) (𝓡∂ (1 + 1))
              (Subtype.val : (𝓡∂ (1 + 1)).boundary cubicEpigraph → cubicEpigraph) q u)))
    nlinarith

/-- **Strict convexity of the cubic `y = x³`.** The boundary of the region above the cubic is
strictly convex at `q = (x, x³)` exactly when `x > 0`. -/
theorem isStrictlyConvexAt_cubicEpigraph_iff
    (q : letI := cubicEpigraphChartedSpace
      (𝓡∂ (1 + 1)).boundary cubicEpigraph) :
    letI := cubicEpigraphChartedSpace
    haveI := isManifold_cubicEpigraph
    letI := cubicEpigraphRiemannianBundle
    haveI := isContMDiffRiemannianBundle_cubicEpigraph
    IsStrictlyConvexAt q ↔ 0 < (q : ℝ²) 0 := by
  let := cubicEpigraphChartedSpace
  have := isManifold_cubicEpigraph
  let := cubicEpigraphRiemannianBundle
  have := isContMDiffRiemannianBundle_cubicEpigraph
  have hg := norm_mgradient_cubicSub_pos (q : ℝ²)
  rw [isStrictlyConvexAt_iff]
  constructor
  · intro h
    obtain ⟨u, hu⟩ := exists_ne_zero_tangentSpace_cubicEpigraph q
    have ha := proj_zero_mfderiv_cubicEpigraph_ne_zero q hu
    have h' := h u hu
    rw [boundarySecondFundamentalForm_cubicEpigraph_apply, lt_div_iff₀ hg, zero_mul] at h'
    have := mul_self_pos.2 ha
    nlinarith
  · intro hx u hu
    rw [boundarySecondFundamentalForm_cubicEpigraph_apply]
    refine div_pos ?_ hg
    have := mul_self_pos.2 (proj_zero_mfderiv_cubicEpigraph_ne_zero q hu)
    nlinarith

/-- **Convexity is not an open condition.** The set of points of the cubic `y = x³` at which the
boundary of the region above it is convex is `{x ≥ 0}`, which is not open in the boundary: the
points `(-t, -t³)`, `t > 0`, are not in it and tend to the origin, which is. -/
theorem not_isOpen_setOf_isConvexAt_cubicEpigraph :
    letI := cubicEpigraphChartedSpace
    haveI := isManifold_cubicEpigraph
    letI := cubicEpigraphRiemannianBundle
    haveI := isContMDiffRiemannianBundle_cubicEpigraph
    ¬IsOpen {q : (𝓡∂ (1 + 1)).boundary cubicEpigraph | IsConvexAt q} := by
  let := cubicEpigraphChartedSpace
  have := isManifold_cubicEpigraph
  let := cubicEpigraphRiemannianBundle
  have := isContMDiffRiemannianBundle_cubicEpigraph
  have hmem : ∀ t : ℝ, (!₂[-t, -t ^ 3] : ℝ²) ∈ cubicEpigraph := fun t ↦ by
    simp only [mem_ofPred_eq]
    simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
      sub_neg_eq_add]
    exact le_of_eq (by ring)
  have hbd : ∀ t : ℝ,
      (⟨!₂[-t, -t ^ 3], hmem t⟩ : cubicEpigraph) ∈ (𝓡∂ (1 + 1)).boundary cubicEpigraph := fun t ↦
    (Set.ext_iff.1 (boundary_scalarRegularSublevel (isRegularValue_cubicSub 0)
      (finrank_euclideanSpace_fin (𝕜 := ℝ) (n := 2)) le_rfl (contMDiff_cubicSub (k := 1))) _).2
      (by simp; ring)
  let γ : ℝ → (𝓡∂ (1 + 1)).boundary cubicEpigraph := fun t ↦ ⟨⟨!₂[-t, -t ^ 3], hmem t⟩, hbd t⟩
  have hγ : Continuous γ := by
    refine Continuous.subtype_mk (Continuous.subtype_mk ?_ _) _
    exact (PiLp.continuous_toLp 2 _).comp (by fun_prop)
  intro hU
  have h0 : (0 : ℝ) ∈ γ ⁻¹' {q | IsConvexAt q} := by
    change IsConvexAt (γ 0)
    rw [isConvexAt_cubicEpigraph_iff]
    simp [γ]
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 (hU.preimage hγ) 0 h0
  have ht : ε / 2 ∈ Metric.ball (0 : ℝ) ε := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos (half_pos hε)]
    exact half_lt_self hε
  have h := hball ht
  change IsConvexAt (γ (ε / 2)) at h
  rw [isConvexAt_cubicEpigraph_iff] at h
  simp only [γ] at h
  simp at h
  linarith

end TauCeti
