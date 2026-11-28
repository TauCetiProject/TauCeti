/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.RegularDomain.Boundary
public import TauCeti.Geometry.Manifold.Riemannian.Boundary.Weingarten.Basic
public import TauCeti.Geometry.Manifold.RegularValue.NormSq
import TauCeti.Geometry.Manifold.Riemannian.Gradient.NormedSpace
import TauCeti.Geometry.Manifold.Riemannian.Hessian.NormSq

/-!
# The closed exterior of a ball as a regular domain

Let `E` be a real inner product space of dimension `n + 1` with its flat metric, and `c > 0`. The
closed exterior `D = {x | ‖x‖² ≥ c}` of the open ball of radius `√c` is the regular sublevel
`{-‖x‖² ≤ -c}` of `f = -‖·‖²` at its regular value `-c`, with its half-space atlas
`TauCeti.normSqGeChartedSpace` and the metric pulled back along the inclusion `j : D → E`. Its
boundary is the sphere of radius `√c` (`TauCeti.mem_boundary_normSqGe_iff`). With
`grad f = -2x`, `|grad f| = 2√c` on the sphere and `Hess f = -2g`, the formulas of
`TauCeti.mfderiv_inwardUnitNormal_scalarRegularSublevel` and
`TauCeti.boundarySecondFundamentalForm_scalarRegularSublevel_apply` give:

* `dj(ν_in) = x / √c`: the inward normal of the exterior points away from the origin
  (`TauCeti.mfderiv_inwardUnitNormal_normSqGe`);
* `II = -h / √c`, where `h` is the induced metric of the boundary sphere
  (`TauCeti.boundarySecondFundamentalForm_normSqGe`), so the Weingarten map is `-1/√c` times the
  identity (`TauCeti.boundaryWeingarten_normSqGe`), every principal curvature is `-1/√c`
  (`TauCeti.boundaryPrincipalCurvatures_normSqGe`) and, for `n ≥ 1`, so is the mean curvature
  (`TauCeti.boundaryMeanCurvature_normSqGe`).

For the exterior of the unit ball (`c = 1`) the boundary is the unit sphere, with `II = -h`
(`TauCeti.boundarySecondFundamentalForm_normSqGe_one`), every principal curvature `-1`
(`TauCeti.boundaryPrincipalCurvatures_normSqGe_one`) and mean curvature `H = -1`
(`TauCeti.boundaryMeanCurvature_normSqGe_one`).

The sets are written `{x : E | -‖x‖ ^ (2 : ℕ) ≤ -c}`: with an unannotated exponent, a numeral whose
type is still pending inside a binder type blocks the instance search for the tangent bundle.
-/

public section

open Bundle Module Set
open scoped ContDiff Manifold RealInnerProductSpace Gradient

noncomputable section

namespace TauCeti

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {c : ℝ}

variable (hc : 0 < c) (hn : finrank ℝ E = n + 1)

/-- The half-space atlas of the closed exterior `{‖x‖² ≥ c} = {-‖x‖² ≤ -c}`:
`TauCeti.scalarRegularSublevelChartedSpace` for `-‖·‖²` at its regular value `-c`. -/
abbrev normSqGeChartedSpace :
    ChartedSpace (EuclideanHalfSpace (n + 1)) {x : E | -‖x‖ ^ (2 : ℕ) ≤ -c} :=
  scalarRegularSublevelChartedSpace
    ((contMDiff_neg_norm_sq_model_space (E := E) (k := ∞)).of_le ENat.LEInfty.out)
    (isRegularValue_neg_norm_sq (E := E) (neg_ne_zero.2 hc.ne')) hn

/-- The closed exterior `{‖x‖² ≥ c}` is a smooth manifold with boundary for
`TauCeti.normSqGeChartedSpace`. -/
theorem isManifold_normSqGe :
    letI := normSqGeChartedSpace hc hn
    IsManifold (𝓡∂ (n + 1)) ∞ {x : E | -‖x‖ ^ (2 : ℕ) ≤ -c} :=
  isManifold_scalarRegularSublevel (isRegularValue_neg_norm_sq (E := E) (neg_ne_zero.2 hc.ne')) hn
    ENat.LEInfty.out (contMDiff_neg_norm_sq_model_space (E := E) (k := ∞))

/-- The metric of the closed exterior `{‖x‖² ≥ c}` pulled back along the inclusion
(`TauCeti.scalarRegularSublevelMetric`), as a Riemannian bundle structure. -/
abbrev normSqGeRiemannianBundle :
    letI := normSqGeChartedSpace hc hn
    haveI := isManifold_normSqGe hc hn
    RiemannianBundle
      (fun x : {x : E | -‖x‖ ^ (2 : ℕ) ≤ -c} ↦ TangentSpace (𝓡∂ (n + 1)) x) :=
  letI := normSqGeChartedSpace hc hn
  haveI := isManifold_normSqGe hc hn
  ⟨(scalarRegularSublevelMetric (contMDiff_neg_norm_sq_model_space (E := E) (k := ∞))
    (isRegularValue_neg_norm_sq (E := E) (neg_ne_zero.2 hc.ne')) hn).toRiemannianMetric⟩

/-- The pulled-back metric of the closed exterior `{‖x‖² ≥ c}` is smooth. -/
theorem isContMDiffRiemannianBundle_normSqGe :
    letI := normSqGeChartedSpace hc hn
    haveI := isManifold_normSqGe hc hn
    letI := normSqGeRiemannianBundle hc hn
    IsContMDiffRiemannianBundle (𝓡∂ (n + 1)) ∞ (EuclideanSpace ℝ (Fin (n + 1)))
      (fun x : {x : E | -‖x‖ ^ (2 : ℕ) ≤ -c} ↦ TangentSpace (𝓡∂ (n + 1)) x) :=
  isContMDiffRiemannianBundle_scalarRegularSublevel
    (contMDiff_neg_norm_sq_model_space (E := E) (k := ∞))
    (isRegularValue_neg_norm_sq (E := E) (neg_ne_zero.2 hc.ne')) hn

/-- The boundary of the closed exterior `{‖x‖² ≥ c}` is the sphere `‖x‖² = c`. -/
theorem mem_boundary_normSqGe_iff (x : {x : E | -‖x‖ ^ (2 : ℕ) ≤ -c}) :
    letI := normSqGeChartedSpace hc hn
    x ∈ (𝓡∂ (n + 1)).boundary {x : E | -‖x‖ ^ (2 : ℕ) ≤ -c} ↔ ‖(x : E)‖ ^ 2 = c := by
  rw [boundary_scalarRegularSublevel (isRegularValue_neg_norm_sq (E := E) (neg_ne_zero.2 hc.ne'))
    hn le_rfl (contMDiff_neg_norm_sq_model_space (E := E) (k := 1)), mem_ofPred_eq, neg_inj]

/-- A boundary point of the closed exterior `{‖x‖² ≥ c}` lies on the sphere: `‖x‖² = c`. -/
theorem norm_sq_eq_of_mem_boundary_normSqGe
    (q : letI := normSqGeChartedSpace hc hn
      (𝓡∂ (n + 1)).boundary {x : E | -‖x‖ ^ (2 : ℕ) ≤ -c}) :
    ‖((q : {x : E | -‖x‖ ^ (2 : ℕ) ≤ -c}) : E)‖ ^ 2 = c :=
  (mem_boundary_normSqGe_iff hc hn q).1 q.property

/-- A boundary point of the closed exterior `{‖x‖² ≥ c}` has norm `√c`. -/
theorem norm_eq_sqrt_of_mem_boundary_normSqGe
    (q : letI := normSqGeChartedSpace hc hn
      (𝓡∂ (n + 1)).boundary {x : E | -‖x‖ ^ (2 : ℕ) ≤ -c}) :
    ‖((q : {x : E | -‖x‖ ^ (2 : ℕ) ≤ -c}) : E)‖ = √c := by
  rw [← Real.sqrt_sq (norm_nonneg _), norm_sq_eq_of_mem_boundary_normSqGe hc hn q]

/-- **The inward unit normal of the closed exterior.** For the closed exterior `{‖x‖² ≥ c}` with
the pulled-back metric, the differential of the inclusion `j` maps the inward unit normal at a
boundary point `x` to `x / √c`. -/
theorem mfderiv_inwardUnitNormal_normSqGe
    (q : letI := normSqGeChartedSpace hc hn
      (𝓡∂ (n + 1)).boundary {x : E | -‖x‖ ^ (2 : ℕ) ≤ -c}) :
    letI := normSqGeChartedSpace hc hn
    haveI := isManifold_normSqGe hc hn
    letI := normSqGeRiemannianBundle hc hn
    mfderiv (𝓡∂ (n + 1)) 𝓘(ℝ, E) (Subtype.val : {x : E | -‖x‖ ^ (2 : ℕ) ≤ -c} → E) q
        (inwardUnitNormal q) =
      (√c)⁻¹ • ((q : {x : E | -‖x‖ ^ (2 : ℕ) ≤ -c}) : E) := by
  rw [mfderiv_inwardUnitNormal_scalarRegularSublevel
    (contMDiff_neg_norm_sq_model_space (E := E) (k := ∞))
    (isRegularValue_neg_norm_sq (E := E) (neg_ne_zero.2 hc.ne')) hn q,
    Manifold.norm_mgradient_neg_norm_sq_model_space,
    norm_eq_sqrt_of_mem_boundary_normSqGe hc hn q, Manifold.mgradient_neg_norm_sq_model_space]
  have h : -((2 * √c)⁻¹ • -((2 : ℝ) • ((q : {x : E | -‖x‖ ^ (2 : ℕ) ≤ -c}) : E))) =
      (√c)⁻¹ • ((q : {x : E | -‖x‖ ^ (2 : ℕ) ≤ -c}) : E) := by
    rw [smul_neg, neg_neg, smul_smul]
    congr 1
    have : √c ≠ 0 := (Real.sqrt_pos.2 hc).ne'
    field_simp
  -- The gradient `-2x` lies in the tangent space of `E` at `q`, which is `E` by definition.
  exact h

/-- **The second fundamental form of the closed exterior.** For the closed exterior
`{‖x‖² ≥ c}` with the pulled-back metric, the second fundamental form of the boundary sphere is
`-1/√c` times its induced metric: `II = -h / √c`. -/
theorem boundarySecondFundamentalForm_normSqGe
    (q : letI := normSqGeChartedSpace hc hn
      (𝓡∂ (n + 1)).boundary {x : E | -‖x‖ ^ (2 : ℕ) ≤ -c}) :
    letI := normSqGeChartedSpace hc hn
    haveI := isManifold_normSqGe hc hn
    letI := normSqGeRiemannianBundle hc hn
    haveI := isContMDiffRiemannianBundle_normSqGe hc hn
    boundarySecondFundamentalForm q = -(√c)⁻¹ • boundaryInducedForm q := by
  let := normSqGeChartedSpace hc hn
  have := isManifold_normSqGe hc hn
  let := normSqGeRiemannianBundle hc hn
  have := isContMDiffRiemannianBundle_normSqGe hc hn
  ext u w
  rw [boundarySecondFundamentalForm_scalarRegularSublevel_apply
    (contMDiff_neg_norm_sq_model_space (E := E) (k := ∞))
    (isRegularValue_neg_norm_sq (E := E) (neg_ne_zero.2 hc.ne')) hn q u w]
  simp only [Manifold.hessian_neg_norm_sq_model_space,
    Manifold.norm_mgradient_neg_norm_sq_model_space, norm_eq_sqrt_of_mem_boundary_normSqGe hc hn q,
    LinearMap.smul_apply, boundaryInducedForm_scalarRegularSublevel_apply
      (contMDiff_neg_norm_sq_model_space (E := E) (k := ∞))
      (isRegularValue_neg_norm_sq (E := E) (neg_ne_zero.2 hc.ne')) hn q, smul_eq_mul]
  have : √c ≠ 0 := (Real.sqrt_pos.2 hc).ne'
  field_simp

/-- **The Weingarten map of the closed exterior** is `-1/√c` times the identity. -/
theorem boundaryWeingarten_normSqGe
    (q : letI := normSqGeChartedSpace hc hn
      (𝓡∂ (n + 1)).boundary {x : E | -‖x‖ ^ (2 : ℕ) ≤ -c}) :
    letI := normSqGeChartedSpace hc hn
    haveI := isManifold_normSqGe hc hn
    letI := normSqGeRiemannianBundle hc hn
    haveI := isContMDiffRiemannianBundle_normSqGe hc hn
    boundaryWeingarten q = -(√c)⁻¹ • LinearMap.id :=
  letI := normSqGeChartedSpace hc hn
  haveI := isManifold_normSqGe hc hn
  letI := normSqGeRiemannianBundle hc hn
  haveI := isContMDiffRiemannianBundle_normSqGe hc hn
  (boundaryWeingarten_eq_smul_id_iff q _).2 (boundarySecondFundamentalForm_normSqGe hc hn q)

/-- **Every principal curvature of the closed exterior is `-1/√c`.** -/
theorem boundaryPrincipalCurvatures_normSqGe
    (q : letI := normSqGeChartedSpace hc hn
      (𝓡∂ (n + 1)).boundary {x : E | -‖x‖ ^ (2 : ℕ) ≤ -c}) (i : Fin n) :
    letI := normSqGeChartedSpace hc hn
    haveI := isManifold_normSqGe hc hn
    letI := normSqGeRiemannianBundle hc hn
    haveI := isContMDiffRiemannianBundle_normSqGe hc hn
    boundaryPrincipalCurvatures q i = -(√c)⁻¹ :=
  letI := normSqGeChartedSpace hc hn
  haveI := isManifold_normSqGe hc hn
  letI := normSqGeRiemannianBundle hc hn
  haveI := isContMDiffRiemannianBundle_normSqGe hc hn
  boundaryPrincipalCurvatures_eq_of_boundaryWeingarten_eq_smul
    (boundaryWeingarten_normSqGe hc hn q) i

/-- **The mean curvature of the closed exterior is `-1/√c`**, for `n ≥ 1`. -/
theorem boundaryMeanCurvature_normSqGe [NeZero n]
    (q : letI := normSqGeChartedSpace hc hn
      (𝓡∂ (n + 1)).boundary {x : E | -‖x‖ ^ (2 : ℕ) ≤ -c}) :
    letI := normSqGeChartedSpace hc hn
    haveI := isManifold_normSqGe hc hn
    letI := normSqGeRiemannianBundle hc hn
    haveI := isContMDiffRiemannianBundle_normSqGe hc hn
    boundaryMeanCurvature q = -(√c)⁻¹ :=
  letI := normSqGeChartedSpace hc hn
  haveI := isManifold_normSqGe hc hn
  letI := normSqGeRiemannianBundle hc hn
  haveI := isContMDiffRiemannianBundle_normSqGe hc hn
  boundaryMeanCurvature_eq_of_boundaryWeingarten_eq_smul (boundaryWeingarten_normSqGe hc hn q)

/-- **`II = -h` on the boundary of the closed exterior of the unit ball.** -/
theorem boundarySecondFundamentalForm_normSqGe_one
    (q : letI := normSqGeChartedSpace (E := E) one_pos hn
      (𝓡∂ (n + 1)).boundary {x : E | -‖x‖ ^ (2 : ℕ) ≤ -1}) :
    letI := normSqGeChartedSpace (E := E) one_pos hn
    haveI := isManifold_normSqGe (E := E) one_pos hn
    letI := normSqGeRiemannianBundle (E := E) one_pos hn
    haveI := isContMDiffRiemannianBundle_normSqGe (E := E) one_pos hn
    boundarySecondFundamentalForm q = -boundaryInducedForm q := by
  rw [boundarySecondFundamentalForm_normSqGe one_pos hn q, Real.sqrt_one, inv_one]
  ext u w
  simp

/-- The Weingarten map of the closed exterior of the unit ball is `-id`. -/
theorem boundaryWeingarten_normSqGe_one
    (q : letI := normSqGeChartedSpace (E := E) one_pos hn
      (𝓡∂ (n + 1)).boundary {x : E | -‖x‖ ^ (2 : ℕ) ≤ -1}) :
    letI := normSqGeChartedSpace (E := E) one_pos hn
    haveI := isManifold_normSqGe (E := E) one_pos hn
    letI := normSqGeRiemannianBundle (E := E) one_pos hn
    haveI := isContMDiffRiemannianBundle_normSqGe (E := E) one_pos hn
    boundaryWeingarten q = -LinearMap.id := by
  rw [boundaryWeingarten_normSqGe one_pos hn q, Real.sqrt_one, inv_one, neg_one_smul]

/-- Every principal curvature of the closed exterior of the unit ball is `-1`. -/
theorem boundaryPrincipalCurvatures_normSqGe_one
    (q : letI := normSqGeChartedSpace (E := E) one_pos hn
      (𝓡∂ (n + 1)).boundary {x : E | -‖x‖ ^ (2 : ℕ) ≤ -1}) (i : Fin n) :
    letI := normSqGeChartedSpace (E := E) one_pos hn
    haveI := isManifold_normSqGe (E := E) one_pos hn
    letI := normSqGeRiemannianBundle (E := E) one_pos hn
    haveI := isContMDiffRiemannianBundle_normSqGe (E := E) one_pos hn
    boundaryPrincipalCurvatures q i = -1 := by
  rw [boundaryPrincipalCurvatures_normSqGe one_pos hn q i, Real.sqrt_one, inv_one]

/-- The mean curvature of the closed exterior of the unit ball is `-1`, for `n ≥ 1`. -/
theorem boundaryMeanCurvature_normSqGe_one [NeZero n]
    (q : letI := normSqGeChartedSpace (E := E) one_pos hn
      (𝓡∂ (n + 1)).boundary {x : E | -‖x‖ ^ (2 : ℕ) ≤ -1}) :
    letI := normSqGeChartedSpace (E := E) one_pos hn
    haveI := isManifold_normSqGe (E := E) one_pos hn
    letI := normSqGeRiemannianBundle (E := E) one_pos hn
    haveI := isContMDiffRiemannianBundle_normSqGe (E := E) one_pos hn
    boundaryMeanCurvature q = -1 := by
  rw [boundaryMeanCurvature_normSqGe one_pos hn q, Real.sqrt_one, inv_one]

end TauCeti
