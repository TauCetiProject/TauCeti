/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.RegularDomain.Boundary
public import TauCeti.Geometry.Manifold.RegularValue.Scalar.Examples.Sphere
import TauCeti.Geometry.Manifold.Riemannian.Gradient.NormedSpace
import TauCeti.Geometry.Manifold.Riemannian.Laplacian

/-!
# The closed ball of radius `√c` as a regular domain

Let `E` be a real inner product space of dimension `n + 1` with its flat metric, and `c > 0`. The
ball `D = {x | ‖x‖² ≤ c}` is the regular sublevel of the squared norm at its regular value `c`
(`TauCeti.isRegularValue_norm_sq`), with its half-space atlas
`TauCeti.normSqSublevelChartedSpace` and the metric `TauCeti.normSqSublevelMetric` pulled back
along the inclusion `j : D → E`. Its boundary is the sphere of radius `√c`
(`TauCeti.boundary_normSqSublevel`), and the formulas of
`TauCeti.mfderiv_inwardUnitNormal_scalarRegularSublevel` and
`TauCeti.boundarySecondFundamentalForm_scalarRegularSublevel_apply`, with `grad ‖·‖² = 2x`,
`|grad ‖·‖²| = 2√c` on the sphere and `Hess ‖·‖² = 2g`, give:

* `dj(ν_in) = -x / √c` at a boundary point `x`
  (`TauCeti.mfderiv_inwardUnitNormal_normSqSublevel`); for `c = 1` this is `dj(ν_in) = -x`
  (`TauCeti.mfderiv_inwardUnitNormal_normSqSublevel_one`), which agrees with
  `grad ρ / |grad ρ| = -2x / 2` for the defining function `ρ = 1 - |x|²` of the unit ball;
* `II = h / √c`, where `h` is the induced metric of the boundary sphere
  (`TauCeti.boundarySecondFundamentalForm_normSqSublevel_eq_inv_sqrt_smul_boundaryInducedForm`), so
  the sphere of radius `√c` is totally umbilic, and `II = h` for `c = 1`
  (`TauCeti.boundarySecondFundamentalForm_normSqSublevel_one_eq_boundaryInducedForm`).

The sets are written `{x : E | ‖x‖ ^ (2 : ℕ) ≤ c}`: with an unannotated exponent, a numeral whose
type is still pending inside a binder type blocks the instance search for the tangent bundle.
-/

public section

open Bundle Module Set
open scoped ContDiff Manifold RealInnerProductSpace

noncomputable section

namespace TauCeti

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {c : ℝ} (hc : 0 < c) (hn : finrank ℝ E = n + 1)

/-- The flat metric of `E` pulled back to the closed ball `{‖x‖² ≤ c}` along its inclusion, for the
atlas `TauCeti.normSqSublevelChartedSpace`: `TauCeti.scalarRegularSublevelMetric` for the squared
norm at its regular value `c`. -/
abbrev normSqSublevelMetric :
    letI := normSqSublevelChartedSpace hc hn
    haveI := isManifold_normSqSublevel hc hn ENat.LEInfty.out
    ContMDiffRiemannianMetric (𝓡∂ (n + 1)) ∞ (EuclideanSpace ℝ (Fin (n + 1)))
      (fun x : {x : E | ‖x‖ ^ (2 : ℕ) ≤ c} ↦ TangentSpace (𝓡∂ (n + 1)) x) :=
  scalarRegularSublevelMetric (contDiff_norm_sq ℝ).contMDiff (isRegularValue_norm_sq hc.ne') hn

/-- The Riemannian structure of the closed ball `{‖x‖² ≤ c}` given by the pulled-back metric
`TauCeti.normSqSublevelMetric`. -/
abbrev normSqSublevelRiemannianBundle :
    letI := normSqSublevelChartedSpace hc hn
    RiemannianBundle (fun x : {x : E | ‖x‖ ^ (2 : ℕ) ≤ c} ↦ TangentSpace (𝓡∂ (n + 1)) x) :=
  letI := normSqSublevelChartedSpace hc hn
  haveI := isManifold_normSqSublevel hc hn ENat.LEInfty.out
  ⟨(normSqSublevelMetric hc hn).toRiemannianMetric⟩

/-- The pulled-back metric `TauCeti.normSqSublevelMetric` of the closed ball `{‖x‖² ≤ c}` is
smooth. -/
theorem isContMDiffRiemannianBundle_normSqSublevel :
    letI := normSqSublevelChartedSpace hc hn
    haveI := isManifold_normSqSublevel hc hn ENat.LEInfty.out
    letI := normSqSublevelRiemannianBundle hc hn
    IsContMDiffRiemannianBundle (𝓡∂ (n + 1)) ∞ (EuclideanSpace ℝ (Fin (n + 1)))
      (fun x : {x : E | ‖x‖ ^ (2 : ℕ) ≤ c} ↦ TangentSpace (𝓡∂ (n + 1)) x) :=
  letI := normSqSublevelChartedSpace hc hn
  haveI := isManifold_normSqSublevel hc hn ENat.LEInfty.out
  letI := normSqSublevelRiemannianBundle hc hn
  ⟨(normSqSublevelMetric hc hn).inner, (normSqSublevelMetric hc hn).contMDiff, fun _ _ _ ↦ rfl⟩

/-- **The inward unit normal of the ball of radius `√c`.** For the regular sublevel
`D = {‖x‖² ≤ c}` with the pulled-back metric, the differential of the inclusion `j` maps the
inward unit normal at a boundary point `x` to `-x / √c`. -/
theorem mfderiv_inwardUnitNormal_normSqSublevel
    (q : letI := normSqSublevelChartedSpace hc hn
      (𝓡∂ (n + 1)).boundary {x : E | ‖x‖ ^ (2 : ℕ) ≤ c}) :
    letI := normSqSublevelChartedSpace hc hn
    haveI := isManifold_normSqSublevel hc hn ENat.LEInfty.out
    letI := normSqSublevelRiemannianBundle hc hn
    mfderiv (𝓡∂ (n + 1)) 𝓘(ℝ, E) (Subtype.val : {x : E | ‖x‖ ^ (2 : ℕ) ≤ c} → E) q
        (inwardUnitNormal q) =
      -((√c)⁻¹ • ((q : {x : E | ‖x‖ ^ (2 : ℕ) ≤ c}) : E)) := by
  rw [mfderiv_inwardUnitNormal_scalarRegularSublevel (contDiff_norm_sq ℝ).contMDiff
    (isRegularValue_norm_sq hc.ne') hn q, Manifold.norm_mgradient_norm_sq_model_space,
    norm_eq_sqrt_of_mem_boundary_normSqSublevel hc hn q]
  congr 1
  apply (NormedSpace.fromTangentSpace (𝕜 := ℝ) _).injective
  rw [map_smul, Manifold.mgradient_norm_sq_model_space, smul_smul]
  -- The right side applies `fromTangentSpace` to `(√c)⁻¹ • x`, a vector of `E` rather than of
  -- `TangentSpace 𝓘(ℝ, E) x`, so `rw` and `simp` reject the pattern of `fromTangentSpace_apply`
  -- as ill-typed; the equation is used explicitly instead.
  refine Eq.trans ?_ (NormedSpace.fromTangentSpace_apply _ _).symm
  have : √c ≠ 0 := (Real.sqrt_pos.2 hc).ne'
  congr 1
  field_simp

/-- **The inward unit normal of the closed unit ball.** For the regular sublevel `{‖x‖² ≤ 1}`,
the differential of the inclusion `j` maps the inward unit normal at a point `x` of the unit sphere
to `-x`. The atlas is `TauCeti.normSqSublevelChartedSpace` at `c = 1`, the atlas of
`TauCeti.normSqSublevelBoundaryDiffeomorphSphere`. -/
theorem mfderiv_inwardUnitNormal_normSqSublevel_one
    (q : letI := normSqSublevelChartedSpace (E := E) one_pos hn
      (𝓡∂ (n + 1)).boundary {x : E | ‖x‖ ^ (2 : ℕ) ≤ 1}) :
    letI := normSqSublevelChartedSpace (E := E) one_pos hn
    haveI := isManifold_normSqSublevel (E := E) one_pos hn ENat.LEInfty.out
    letI := normSqSublevelRiemannianBundle (E := E) one_pos hn
    mfderiv (𝓡∂ (n + 1)) 𝓘(ℝ, E) (Subtype.val : {x : E | ‖x‖ ^ (2 : ℕ) ≤ 1} → E) q
        (inwardUnitNormal q) = -((q : {x : E | ‖x‖ ^ (2 : ℕ) ≤ 1}) : E) := by
  rw [mfderiv_inwardUnitNormal_normSqSublevel one_pos hn q, Real.sqrt_one, inv_one, one_smul]

/-- **The second fundamental form of the sphere of radius `√c`.** For the regular sublevel
`D = {‖x‖² ≤ c}` with the pulled-back metric, at a boundary point `q`,
`II_q(u, w) = ⟨dj dι u, dj dι w⟩ / √c`, where `j : D → E` and `ι : ∂D → D` are the inclusions. -/
theorem boundarySecondFundamentalForm_normSqSublevel_apply
    (q : letI := normSqSublevelChartedSpace hc hn
      (𝓡∂ (n + 1)).boundary {x : E | ‖x‖ ^ (2 : ℕ) ≤ c})
    (u w : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) q) :
    letI := normSqSublevelChartedSpace hc hn
    haveI := isManifold_normSqSublevel hc hn ENat.LEInfty.out
    letI := normSqSublevelRiemannianBundle hc hn
    haveI := isContMDiffRiemannianBundle_normSqSublevel hc hn
    boundarySecondFundamentalForm q u w =
      ⟪(mfderiv (𝓡∂ (n + 1)) 𝓘(ℝ, E) (Subtype.val : {x : E | ‖x‖ ^ (2 : ℕ) ≤ c} → E) q
            (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡∂ (n + 1))
              (Subtype.val : (𝓡∂ (n + 1)).boundary {x : E | ‖x‖ ^ (2 : ℕ) ≤ c} →
                {x : E | ‖x‖ ^ (2 : ℕ) ≤ c}) q u) : E),
        (mfderiv (𝓡∂ (n + 1)) 𝓘(ℝ, E) (Subtype.val : {x : E | ‖x‖ ^ (2 : ℕ) ≤ c} → E) q
            (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡∂ (n + 1))
              (Subtype.val : (𝓡∂ (n + 1)).boundary {x : E | ‖x‖ ^ (2 : ℕ) ≤ c} →
                {x : E | ‖x‖ ^ (2 : ℕ) ≤ c}) q w) : E)⟫ / √c := by
  rw [boundarySecondFundamentalForm_scalarRegularSublevel_apply (contDiff_norm_sq ℝ).contMDiff
    (isRegularValue_norm_sq hc.ne') hn q u w, Manifold.hessian_norm_sq_model_space,
    Manifold.norm_mgradient_norm_sq_model_space,
    norm_eq_sqrt_of_mem_boundary_normSqSublevel hc hn q, mul_div_mul_left _ _ two_ne_zero,
    TauCeti.Manifold.inner_tangentSpace_vectorSpace]

/-- **`II = h / √c` on the sphere of radius `√c`.** For the regular sublevel `D = {‖x‖² ≤ c}`
with the pulled-back metric, the second fundamental form of the boundary sphere is `1 / √c` times
its induced metric. -/
theorem boundarySecondFundamentalForm_normSqSublevel_eq_inv_sqrt_smul_boundaryInducedForm
    (q : letI := normSqSublevelChartedSpace hc hn
      (𝓡∂ (n + 1)).boundary {x : E | ‖x‖ ^ (2 : ℕ) ≤ c}) :
    letI := normSqSublevelChartedSpace hc hn
    haveI := isManifold_normSqSublevel hc hn ENat.LEInfty.out
    letI := normSqSublevelRiemannianBundle hc hn
    haveI := isContMDiffRiemannianBundle_normSqSublevel hc hn
    boundarySecondFundamentalForm q = (√c)⁻¹ • boundaryInducedForm q := by
  let := normSqSublevelChartedSpace hc hn
  have := isManifold_normSqSublevel hc hn ENat.LEInfty.out
  let := normSqSublevelRiemannianBundle hc hn
  have := isContMDiffRiemannianBundle_normSqSublevel hc hn
  ext u w
  rw [boundarySecondFundamentalForm_normSqSublevel_apply hc hn q u w, LinearMap.smul_apply,
    LinearMap.smul_apply, boundaryInducedForm_apply,
    ← (isLocalRiemannianIsometry_subtypeVal_scalarRegularSublevel (contDiff_norm_sq ℝ).contMDiff
      (isRegularValue_norm_sq hc.ne') hn).inner_mfderiv,
    TauCeti.Manifold.inner_tangentSpace_vectorSpace, smul_eq_mul, div_eq_inv_mul]

/-- **`II = h` on the unit sphere.** For the regular sublevel `{‖x‖² ≤ 1}` with the pulled-back
metric, the second fundamental form of the unit sphere is its induced metric. -/
theorem boundarySecondFundamentalForm_normSqSublevel_one_eq_boundaryInducedForm
    (q : letI := normSqSublevelChartedSpace (E := E) one_pos hn
      (𝓡∂ (n + 1)).boundary {x : E | ‖x‖ ^ (2 : ℕ) ≤ 1}) :
    letI := normSqSublevelChartedSpace (E := E) one_pos hn
    haveI := isManifold_normSqSublevel (E := E) one_pos hn ENat.LEInfty.out
    letI := normSqSublevelRiemannianBundle (E := E) one_pos hn
    haveI := isContMDiffRiemannianBundle_normSqSublevel (E := E) one_pos hn
    boundarySecondFundamentalForm q = boundaryInducedForm q := by
  rw [boundarySecondFundamentalForm_normSqSublevel_eq_inv_sqrt_smul_boundaryInducedForm one_pos hn
    q, Real.sqrt_one, inv_one, one_smul]

end TauCeti
