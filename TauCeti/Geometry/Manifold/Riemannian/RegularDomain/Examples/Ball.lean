/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.RegularDomain.Boundary
public import TauCeti.Geometry.Manifold.RegularValue.NormSq
import TauCeti.Analysis.InnerProductSpace.Calculus
import TauCeti.Geometry.Manifold.Riemannian.Gradient.NormedSpace
import TauCeti.Geometry.Manifold.Riemannian.Laplacian

/-!
# The closed ball of radius `√c` as a regular domain

Let `E` be a real inner product space of dimension `n + 1` with its flat metric, and `c > 0`. The
ball `D = {x | ‖x‖² ≤ c}` is the regular sublevel of the squared norm at its regular value `c`
(`TauCeti.isRegularValue_norm_sq`), with its half-space atlas `TauCeti.normSqLeChartedSpace` and
the metric pulled back along the inclusion `j : D → E`.
Its boundary is the sphere of radius `√c`, and the formulas of
`TauCeti.mfderiv_inwardUnitNormal_scalarRegularSublevel` and
`TauCeti.boundarySecondFundamentalForm_scalarRegularSublevel_apply`, with `grad ‖·‖² = 2x`,
`|grad ‖·‖²| = 2√c` on the sphere and `Hess ‖·‖² = 2g`, give:

* `dj(ν_in) = -x / √c` at a boundary point `x`
  (`TauCeti.mfderiv_inwardUnitNormal_normSqSublevel`); for `c = 1` this is `dj(ν_in) = -x`
  (`TauCeti.mfderiv_inwardUnitNormal_normSqSublevel_one`), the closed unit ball Check of a regular
  domain `{ρ ≥ 0}` with `ρ = 1 - |x|²`, where `grad ρ / |grad ρ| = -2x / 2`;
* `II = h / √c`, where `h` is the induced metric of the boundary sphere
  (`TauCeti.boundarySecondFundamentalForm_normSqSublevel`), and `II = h` for `c = 1`
  (`TauCeti.boundarySecondFundamentalForm_normSqSublevel_one`).

These are the closed-ball Checks of RiemannianManifoldsWithConvexBoundary §3.1 (outward
criterion on the unit ball) and §3.2 (the sublevels `{|z|² ≤ c}` of `x = |z|²`, with
`|dx| = 2√c` on the sphere and `II = 2h/(2√c) = h/√c`).

The sets are written `{x : E | ‖x‖ ^ (2 : ℕ) ≤ c}`: with an unannotated exponent, a numeral whose
type is still pending inside a binder type blocks the instance search for the tangent bundle.
-/

public section

open Bundle Module Set
open scoped ContDiff Manifold RealInnerProductSpace Gradient

noncomputable section

namespace TauCeti

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {c : ℝ}

omit [FiniteDimensional ℝ E] in
/-- The squared norm is smooth on the flat space. -/
theorem contMDiff_norm_sq_model_space {k : ℕ∞ω} :
    ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) k fun x : E ↦ ‖x‖ ^ 2 :=
  (contDiff_norm_sq ℝ).contMDiff

/-- On the flat space, the gradient of the squared norm has norm `2 ‖x‖`. -/
private theorem norm_mgradient_norm_sq (x : E) :
    ‖Manifold.mgradient 𝓘(ℝ, E) (fun y : E ↦ ‖y‖ ^ 2) x‖ = 2 * ‖x‖ := by
  rw [Manifold.mgradient_norm_sq_model_space, norm_tangentSpace_vectorSpace,
    NormedSpace.fromTangentSpace_apply]
  change ‖(2 : ℕ) • x‖ = _
  rw [← Nat.cast_smul_eq_nsmul ℝ, norm_smul]
  simp

/-- On the flat space, the Hessian of the squared norm is twice the inner product. -/
private theorem hessian_norm_sq_model_space (x : E) (v w : TangentSpace 𝓘(ℝ, E) x) :
    Manifold.hessian 𝓘(ℝ, E) (fun y : E ↦ ‖y‖ ^ 2) x v w = 2 * ⟪(v : E), (w : E)⟫ := by
  have hgrad : DifferentiableAt ℝ (∇ (fun y : E ↦ ‖y‖ ^ 2)) x := by
    have h : (∇ (fun y : E ↦ ‖y‖ ^ 2)) = fun y ↦ (2 : ℕ) • y := by
      ext1 y
      rw [← Manifold.mgradient_eq_gradient, Manifold.mgradient_norm_sq_model_space]
      rfl
    rw [h]
    fun_prop
  rw [Manifold.hessian_eq_iteratedFDeriv_model_space hgrad, iteratedFDeriv_two_apply]
  simp only [Matrix.cons_val, NormedSpace.fromTangentSpace_apply]
  exact TauCeti.fderiv_fderiv_norm_sq_apply x v w

variable (hc : 0 < c) (hn : finrank ℝ E = n + 1)

/-- The half-space atlas of the regular sublevel `{‖x‖² ≤ c}`, the closed ball of radius `√c`:
`TauCeti.scalarRegularSublevelChartedSpace` for the squared norm at its regular value `c`. -/
abbrev normSqLeChartedSpace :
    ChartedSpace (EuclideanHalfSpace (n + 1)) {x : E | ‖x‖ ^ (2 : ℕ) ≤ c} :=
  scalarRegularSublevelChartedSpace
    ((contMDiff_norm_sq_model_space (E := E) (k := ∞)).of_le ENat.LEInfty.out)
    (isRegularValue_norm_sq (E := E) hc.ne') hn

/-- A boundary point of the regular sublevel `{‖x‖² ≤ c}` lies on the sphere: `‖x‖² = c`. -/
theorem norm_sq_eq_of_mem_boundary_normSqSublevel
    (q : letI := normSqLeChartedSpace hc hn
      (𝓡∂ (n + 1)).boundary {x : E | ‖x‖ ^ (2 : ℕ) ≤ c}) :
    ‖((q : {x : E | ‖x‖ ^ (2 : ℕ) ≤ c}) : E)‖ ^ 2 = c := by
  exact (Set.ext_iff.1 (boundary_scalarRegularSublevel (isRegularValue_norm_sq hc.ne') hn le_rfl
    (contMDiff_norm_sq_model_space (E := E) (k := 1))) q).1 q.property

/-- A boundary point of the regular sublevel `{‖x‖² ≤ c}` has norm `√c`. -/
theorem norm_eq_sqrt_of_mem_boundary_normSqSublevel
    (q : letI := normSqLeChartedSpace hc hn
      (𝓡∂ (n + 1)).boundary {x : E | ‖x‖ ^ (2 : ℕ) ≤ c}) :
    ‖((q : {x : E | ‖x‖ ^ (2 : ℕ) ≤ c}) : E)‖ = √c := by
  rw [← Real.sqrt_sq (norm_nonneg _), norm_sq_eq_of_mem_boundary_normSqSublevel hc hn q]

/-- **The inward unit normal of the ball of radius `√c`.** For the regular sublevel
`D = {‖x‖² ≤ c}` with the pulled-back metric, the differential of the inclusion `j` maps the
inward unit normal at a boundary point `x` to `-x / √c`. -/
theorem mfderiv_inwardUnitNormal_normSqSublevel
    (q : letI := normSqLeChartedSpace hc hn
      (𝓡∂ (n + 1)).boundary {x : E | ‖x‖ ^ (2 : ℕ) ≤ c}) :
    letI := normSqLeChartedSpace hc hn
    haveI := isManifold_scalarRegularSublevel (isRegularValue_norm_sq (E := E) hc.ne') hn
      ENat.LEInfty.out (contMDiff_norm_sq_model_space (E := E) (k := ∞))
    letI : RiemannianBundle (fun x : {x : E | ‖x‖ ^ (2 : ℕ) ≤ c} ↦ TangentSpace (𝓡∂ (n + 1)) x) :=
      ⟨(scalarRegularSublevelMetric (contMDiff_norm_sq_model_space (E := E) (k := ∞))
        (isRegularValue_norm_sq (E := E) hc.ne') hn).toRiemannianMetric⟩
    mfderiv (𝓡∂ (n + 1)) 𝓘(ℝ, E) (Subtype.val : {x : E | ‖x‖ ^ (2 : ℕ) ≤ c} → E) q
        (inwardUnitNormal q) =
      -((√c)⁻¹ • ((q : {x : E | ‖x‖ ^ (2 : ℕ) ≤ c}) : E)) := by
  rw [mfderiv_inwardUnitNormal_scalarRegularSublevel
    (contMDiff_norm_sq_model_space (E := E) (k := ∞))
    (isRegularValue_norm_sq (E := E) hc.ne') hn q, norm_mgradient_norm_sq,
    norm_eq_sqrt_of_mem_boundary_normSqSublevel hc hn q, Manifold.mgradient_norm_sq_model_space]
  congr 1
  change (2 * √c)⁻¹ • ((2 : ℕ) • ((q : {x : E | ‖x‖ ^ (2 : ℕ) ≤ c}) : E)) = _
  rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
  congr 1
  have : √c ≠ 0 := (Real.sqrt_pos.2 hc).ne'
  push_cast
  field_simp

/-- **The inward unit normal of the closed unit ball.** For the regular sublevel `{‖x‖² ≤ 1}`,
the differential of the inclusion `j` maps the inward unit normal at a point `x` of the unit sphere
to `-x`. -/
theorem mfderiv_inwardUnitNormal_normSqSublevel_one
    (q : letI := normSqLeChartedSpace (E := E) one_pos hn
      (𝓡∂ (n + 1)).boundary {x : E | ‖x‖ ^ (2 : ℕ) ≤ 1}) :
    letI := normSqLeChartedSpace (E := E) one_pos hn
    haveI := isManifold_scalarRegularSublevel (isRegularValue_norm_sq (E := E) one_ne_zero) hn
      ENat.LEInfty.out (contMDiff_norm_sq_model_space (E := E) (k := ∞))
    letI : RiemannianBundle (fun x : {x : E | ‖x‖ ^ (2 : ℕ) ≤ 1} ↦ TangentSpace (𝓡∂ (n + 1)) x) :=
      ⟨(scalarRegularSublevelMetric (contMDiff_norm_sq_model_space (E := E) (k := ∞))
        (isRegularValue_norm_sq (E := E) one_ne_zero) hn).toRiemannianMetric⟩
    mfderiv (𝓡∂ (n + 1)) 𝓘(ℝ, E) (Subtype.val : {x : E | ‖x‖ ^ (2 : ℕ) ≤ 1} → E) q
        (inwardUnitNormal q) = -((q : {x : E | ‖x‖ ^ (2 : ℕ) ≤ 1}) : E) := by
  rw [mfderiv_inwardUnitNormal_normSqSublevel one_pos hn q, Real.sqrt_one, inv_one, one_smul]

/-- **The second fundamental form of the sphere of radius `√c`.** For the regular sublevel
`D = {‖x‖² ≤ c}` with the pulled-back metric, at a boundary point `q`,
`II_q(u, w) = ⟨dj dι u, dj dι w⟩ / √c`, where `j : D → E` and `ι : ∂D → D` are the inclusions. -/
theorem boundarySecondFundamentalForm_normSqSublevel_apply
    (q : letI := normSqLeChartedSpace hc hn
      (𝓡∂ (n + 1)).boundary {x : E | ‖x‖ ^ (2 : ℕ) ≤ c})
    (u w : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) q) :
    letI := normSqLeChartedSpace hc hn
    haveI := isManifold_scalarRegularSublevel (isRegularValue_norm_sq (E := E) hc.ne') hn
      ENat.LEInfty.out (contMDiff_norm_sq_model_space (E := E) (k := ∞))
    letI : RiemannianBundle (fun x : {x : E | ‖x‖ ^ (2 : ℕ) ≤ c} ↦ TangentSpace (𝓡∂ (n + 1)) x) :=
      ⟨(scalarRegularSublevelMetric (contMDiff_norm_sq_model_space (E := E) (k := ∞))
        (isRegularValue_norm_sq (E := E) hc.ne') hn).toRiemannianMetric⟩
    haveI : IsContMDiffRiemannianBundle (𝓡∂ (n + 1)) ∞ (EuclideanSpace ℝ (Fin (n + 1)))
        (fun x : {x : E | ‖x‖ ^ (2 : ℕ) ≤ c} ↦ TangentSpace (𝓡∂ (n + 1)) x) :=
      ⟨(scalarRegularSublevelMetric (contMDiff_norm_sq_model_space (E := E) (k := ∞))
          (isRegularValue_norm_sq (E := E) hc.ne') hn).inner,
        (scalarRegularSublevelMetric (contMDiff_norm_sq_model_space (E := E) (k := ∞))
          (isRegularValue_norm_sq (E := E) hc.ne') hn).contMDiff, fun _ _ _ ↦ rfl⟩
    boundarySecondFundamentalForm q u w =
      ⟪(mfderiv (𝓡∂ (n + 1)) 𝓘(ℝ, E) (Subtype.val : {x : E | ‖x‖ ^ (2 : ℕ) ≤ c} → E) q
            (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡∂ (n + 1))
              (Subtype.val : (𝓡∂ (n + 1)).boundary {x : E | ‖x‖ ^ (2 : ℕ) ≤ c} →
                {x : E | ‖x‖ ^ (2 : ℕ) ≤ c}) q u) : E),
        (mfderiv (𝓡∂ (n + 1)) 𝓘(ℝ, E) (Subtype.val : {x : E | ‖x‖ ^ (2 : ℕ) ≤ c} → E) q
            (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡∂ (n + 1))
              (Subtype.val : (𝓡∂ (n + 1)).boundary {x : E | ‖x‖ ^ (2 : ℕ) ≤ c} →
                {x : E | ‖x‖ ^ (2 : ℕ) ≤ c}) q w) : E)⟫ / √c := by
  let := normSqLeChartedSpace hc hn
  have := isManifold_scalarRegularSublevel (isRegularValue_norm_sq (E := E) hc.ne') hn
    ENat.LEInfty.out (contMDiff_norm_sq_model_space (E := E) (k := ∞))
  let : RiemannianBundle (fun x : {x : E | ‖x‖ ^ (2 : ℕ) ≤ c} ↦ TangentSpace (𝓡∂ (n + 1)) x) :=
    ⟨(scalarRegularSublevelMetric (contMDiff_norm_sq_model_space (E := E) (k := ∞))
      (isRegularValue_norm_sq (E := E) hc.ne') hn).toRiemannianMetric⟩
  have : IsContMDiffRiemannianBundle (𝓡∂ (n + 1)) ∞ (EuclideanSpace ℝ (Fin (n + 1)))
      (fun x : {x : E | ‖x‖ ^ (2 : ℕ) ≤ c} ↦ TangentSpace (𝓡∂ (n + 1)) x) :=
    ⟨(scalarRegularSublevelMetric (contMDiff_norm_sq_model_space (E := E) (k := ∞))
        (isRegularValue_norm_sq (E := E) hc.ne') hn).inner,
      (scalarRegularSublevelMetric (contMDiff_norm_sq_model_space (E := E) (k := ∞))
        (isRegularValue_norm_sq (E := E) hc.ne') hn).contMDiff, fun _ _ _ ↦ rfl⟩
  rw [boundarySecondFundamentalForm_scalarRegularSublevel_apply
    (contMDiff_norm_sq_model_space (E := E) (k := ∞)) (isRegularValue_norm_sq (E := E) hc.ne') hn
    q u w, hessian_norm_sq_model_space, norm_mgradient_norm_sq,
    norm_eq_sqrt_of_mem_boundary_normSqSublevel hc hn q, mul_div_mul_left _ _ two_ne_zero]

/-- **`II = h / √c` on the sphere of radius `√c`.** For the regular sublevel `D = {‖x‖² ≤ c}`
with the pulled-back metric, the second fundamental form of the boundary sphere is `1 / √c` times
its induced metric. -/
theorem boundarySecondFundamentalForm_normSqSublevel
    (q : letI := normSqLeChartedSpace hc hn
      (𝓡∂ (n + 1)).boundary {x : E | ‖x‖ ^ (2 : ℕ) ≤ c}) :
    letI := normSqLeChartedSpace hc hn
    haveI := isManifold_scalarRegularSublevel (isRegularValue_norm_sq (E := E) hc.ne') hn
      ENat.LEInfty.out (contMDiff_norm_sq_model_space (E := E) (k := ∞))
    letI : RiemannianBundle (fun x : {x : E | ‖x‖ ^ (2 : ℕ) ≤ c} ↦ TangentSpace (𝓡∂ (n + 1)) x) :=
      ⟨(scalarRegularSublevelMetric (contMDiff_norm_sq_model_space (E := E) (k := ∞))
        (isRegularValue_norm_sq (E := E) hc.ne') hn).toRiemannianMetric⟩
    haveI : IsContMDiffRiemannianBundle (𝓡∂ (n + 1)) ∞ (EuclideanSpace ℝ (Fin (n + 1)))
        (fun x : {x : E | ‖x‖ ^ (2 : ℕ) ≤ c} ↦ TangentSpace (𝓡∂ (n + 1)) x) :=
      ⟨(scalarRegularSublevelMetric (contMDiff_norm_sq_model_space (E := E) (k := ∞))
          (isRegularValue_norm_sq (E := E) hc.ne') hn).inner,
        (scalarRegularSublevelMetric (contMDiff_norm_sq_model_space (E := E) (k := ∞))
          (isRegularValue_norm_sq (E := E) hc.ne') hn).contMDiff, fun _ _ _ ↦ rfl⟩
    boundarySecondFundamentalForm q = (√c)⁻¹ • boundaryInducedForm q := by
  let := normSqLeChartedSpace hc hn
  have := isManifold_scalarRegularSublevel (isRegularValue_norm_sq (E := E) hc.ne') hn
    ENat.LEInfty.out (contMDiff_norm_sq_model_space (E := E) (k := ∞))
  let : RiemannianBundle (fun x : {x : E | ‖x‖ ^ (2 : ℕ) ≤ c} ↦ TangentSpace (𝓡∂ (n + 1)) x) :=
    ⟨(scalarRegularSublevelMetric (contMDiff_norm_sq_model_space (E := E) (k := ∞))
      (isRegularValue_norm_sq (E := E) hc.ne') hn).toRiemannianMetric⟩
  have : IsContMDiffRiemannianBundle (𝓡∂ (n + 1)) ∞ (EuclideanSpace ℝ (Fin (n + 1)))
      (fun x : {x : E | ‖x‖ ^ (2 : ℕ) ≤ c} ↦ TangentSpace (𝓡∂ (n + 1)) x) :=
    ⟨(scalarRegularSublevelMetric (contMDiff_norm_sq_model_space (E := E) (k := ∞))
        (isRegularValue_norm_sq (E := E) hc.ne') hn).inner,
      (scalarRegularSublevelMetric (contMDiff_norm_sq_model_space (E := E) (k := ∞))
        (isRegularValue_norm_sq (E := E) hc.ne') hn).contMDiff, fun _ _ _ ↦ rfl⟩
  ext u w
  rw [boundarySecondFundamentalForm_normSqSublevel_apply hc hn q u w, LinearMap.smul_apply,
    LinearMap.smul_apply, boundaryInducedForm_apply,
    ← (isLocalRiemannianIsometry_subtypeVal_scalarRegularSublevel
      (contMDiff_norm_sq_model_space (E := E) (k := ∞)) (isRegularValue_norm_sq (E := E) hc.ne')
      hn).inner_mfderiv, TauCeti.Manifold.inner_tangentSpace_vectorSpace, smul_eq_mul,
    div_eq_inv_mul]

/-- **`II = h` on the unit sphere.** For the regular sublevel `{‖x‖² ≤ 1}` with the pulled-back
metric, the second fundamental form of the unit sphere is its induced metric. -/
theorem boundarySecondFundamentalForm_normSqSublevel_one
    (q : letI := normSqLeChartedSpace (E := E) one_pos hn
      (𝓡∂ (n + 1)).boundary {x : E | ‖x‖ ^ (2 : ℕ) ≤ 1}) :
    letI := normSqLeChartedSpace (E := E) one_pos hn
    haveI := isManifold_scalarRegularSublevel (isRegularValue_norm_sq (E := E) one_ne_zero) hn
      ENat.LEInfty.out (contMDiff_norm_sq_model_space (E := E) (k := ∞))
    letI : RiemannianBundle (fun x : {x : E | ‖x‖ ^ (2 : ℕ) ≤ 1} ↦ TangentSpace (𝓡∂ (n + 1)) x) :=
      ⟨(scalarRegularSublevelMetric (contMDiff_norm_sq_model_space (E := E) (k := ∞))
        (isRegularValue_norm_sq (E := E) one_ne_zero) hn).toRiemannianMetric⟩
    haveI : IsContMDiffRiemannianBundle (𝓡∂ (n + 1)) ∞ (EuclideanSpace ℝ (Fin (n + 1)))
        (fun x : {x : E | ‖x‖ ^ (2 : ℕ) ≤ 1} ↦ TangentSpace (𝓡∂ (n + 1)) x) :=
      ⟨(scalarRegularSublevelMetric (contMDiff_norm_sq_model_space (E := E) (k := ∞))
          (isRegularValue_norm_sq (E := E) one_ne_zero) hn).inner,
        (scalarRegularSublevelMetric (contMDiff_norm_sq_model_space (E := E) (k := ∞))
          (isRegularValue_norm_sq (E := E) one_ne_zero) hn).contMDiff, fun _ _ _ ↦ rfl⟩
    boundarySecondFundamentalForm q = boundaryInducedForm q := by
  rw [boundarySecondFundamentalForm_normSqSublevel one_pos hn q, Real.sqrt_one, inv_one, one_smul]

end TauCeti
