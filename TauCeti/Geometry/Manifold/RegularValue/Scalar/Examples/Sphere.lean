/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Instances.Sphere
public import TauCeti.Geometry.Manifold.Immersion.Diffeomorph
public import TauCeti.Geometry.Manifold.Immersion.Differential
public import TauCeti.Geometry.Manifold.RegularValue.NormSq
public import TauCeti.Geometry.Manifold.RegularValue.Scalar.Boundary

/-!
# The unit sphere as a regular level and as the boundary of the unit ball

In a real inner product space `E` of dimension `n + 1`, the value `1` of `x ↦ ‖x‖²` is regular
(`TauCeti.isRegularValue_norm_sq`), so the level `{‖x‖² = 1}` carries the level atlas
`TauCeti.regularLevelChartedSpace`, modelled on `Fin n → ℝ`, and the closed unit ball
`{‖x‖² ≤ 1}` carries the half-space atlas `TauCeti.scalarRegularSublevelChartedSpace`, whose
manifold boundary is the unit sphere (`TauCeti.boundary_scalarRegularSublevel_norm_sq`).

More generally, for `c > 0` the closed ball `{‖x‖² ≤ c}` of radius `√c` carries the half-space
atlas `TauCeti.normSqLeChartedSpace`, of which the atlas of the unit ball is the case `c = 1`; its
boundary points have norm `√c` (`TauCeti.norm_eq_sqrt_of_mem_boundary_normSqLe`).

This file compares the level `{‖x‖² = 1}` and the boundary of the closed unit ball with Mathlib's
unit sphere `Metric.sphere (0 : E) 1`, with its stereographic atlas modelled on
`EuclideanSpace ℝ (Fin n)`:

* `TauCeti.normSqLevelDiffeomorphSphere`: the identity of points is a smooth diffeomorphism from
  the level `{‖x‖² = 1}` onto the stereographic sphere;
* `TauCeti.normSqSublevelBoundaryDiffeomorphSphere`: the identity of points is a smooth
  diffeomorphism from the manifold boundary of the closed unit ball onto the stereographic sphere.

For `E = ℝ²` the boundary of the closed disc is the unit circle, with its stereographic atlas.

The diffeomorphisms are recognized through immersions into the ambient space
(`Homeomorph.diffeomorphOfImmersions`): a homeomorphism commuting with two immersions into a
common manifold is a diffeomorphism.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Corollary 5.14 (regular level sets), Proposition 5.47 (regular sublevel sets are
  regular domains).
-/

public section

open Function Metric Module Set
open scoped ContDiff Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {n : ℕ}

section Radius

variable {c : ℝ} (hc : 0 < c) (hn : finrank ℝ E = n + 1)

/-- The sublevel atlas `TauCeti.scalarRegularSublevelChartedSpace` of the closed ball
`{‖x‖² ≤ c}` of radius `√c`, modelled on the half-space of dimension `n + 1`. -/
noncomputable abbrev normSqLeChartedSpace :
    ChartedSpace (EuclideanHalfSpace (n + 1)) {x : E | ‖x‖ ^ 2 ≤ c} :=
  scalarRegularSublevelChartedSpace (contDiff_norm_sq ℝ).contMDiff
    (isRegularValue_norm_sq hc.ne') hn

/-- The closed ball `{‖x‖² ≤ c}` is a `C^m` manifold with boundary for its sublevel atlas, for
every `m ≥ 1`. -/
theorem isManifold_normSqLe {m : ℕ∞ω} (hm : 1 ≤ m) :
    letI := normSqLeChartedSpace hc hn
    IsManifold (𝓡∂ (n + 1)) m {x : E | ‖x‖ ^ 2 ≤ c} :=
  isManifold_scalarRegularSublevel (isRegularValue_norm_sq hc.ne') hn hm
    (contDiff_norm_sq ℝ).contMDiff

/-- A boundary point of the closed ball `{‖x‖² ≤ c}`, for its sublevel atlas, lies on the
sphere: `‖x‖² = c`. -/
theorem norm_sq_eq_of_mem_boundary_normSqLe
    (q : letI := normSqLeChartedSpace hc hn
      (𝓡∂ (n + 1)).boundary {x : E | ‖x‖ ^ 2 ≤ c}) :
    ‖((q : {x : E | ‖x‖ ^ 2 ≤ c}) : E)‖ ^ 2 = c :=
  (Set.ext_iff.1 (boundary_scalarRegularSublevel (isRegularValue_norm_sq hc.ne') hn le_rfl
    (contDiff_norm_sq ℝ).contMDiff) q).1 q.property

/-- A boundary point of the closed ball `{‖x‖² ≤ c}`, for its sublevel atlas, has norm `√c`. -/
theorem norm_eq_sqrt_of_mem_boundary_normSqLe
    (q : letI := normSqLeChartedSpace hc hn
      (𝓡∂ (n + 1)).boundary {x : E | ‖x‖ ^ 2 ≤ c}) :
    ‖((q : {x : E | ‖x‖ ^ 2 ≤ c}) : E)‖ = √c := by
  rw [← Real.sqrt_sq (norm_nonneg _), norm_sq_eq_of_mem_boundary_normSqLe hc hn q]

end Radius

variable [Fact (finrank ℝ E = n + 1)]

variable (E n) in
/-- The level atlas `TauCeti.regularLevelChartedSpace` of the level `{‖x‖² = 1}`, modelled on
`Fin n → ℝ`. -/
noncomputable abbrev normSqLevelChartedSpace : ChartedSpace (Fin n → ℝ) {x : E // ‖x‖ ^ 2 = 1} :=
  regularLevelChartedSpace (fun _ _ ↦ (contDiff_norm_sq ℝ).contMDiff.contMDiffAt)
    (isRegularValue_norm_sq one_ne_zero) (finrank_sub_finrank_real_eq Fact.out)

variable (E n) in
/-- The sublevel atlas of the closed unit ball `{‖x‖² ≤ 1}`, modelled on the half-space of
dimension `n + 1`: `TauCeti.normSqLeChartedSpace` at radius one. -/
noncomputable abbrev normSqSublevelChartedSpace :
    ChartedSpace (EuclideanHalfSpace (n + 1)) {x : E | ‖x‖ ^ 2 ≤ 1} :=
  normSqLeChartedSpace one_pos Fact.out

attribute [local instance] normSqLevelChartedSpace normSqSublevelChartedSpace

/-- The level `{‖x‖² = 1}` is homeomorphic to the unit sphere by the identity of points. -/
private def normSqLevelHomeomorphSphere : {x : E // ‖x‖ ^ 2 = 1} ≃ₜ sphere (0 : E) 1 :=
  (Homeomorph.refl E).subtype fun x ↦ by
    rw [Homeomorph.refl_apply, id, mem_sphere_zero_iff_norm,
      pow_eq_one_iff_of_nonneg (norm_nonneg x) two_ne_zero]

/-- **The unit sphere is the regular level of the squared norm.** The identity of points is a
smooth diffeomorphism from the level `{‖x‖² = 1}`, with its level atlas modelled on `Fin n → ℝ`,
onto the unit sphere with its stereographic atlas, modelled on `EuclideanSpace ℝ (Fin n)`. -/
noncomputable def normSqLevelDiffeomorphSphere :
    {x : E // ‖x‖ ^ 2 = 1} ≃ₘ⟮𝓘(ℝ, Fin n → ℝ), 𝓡 n⟯ sphere (0 : E) 1 :=
  normSqLevelHomeomorphSphere.diffeomorphOfImmersions
    (isImmersionOfComplement_coe_regularLevel (m := ∞) (by simp)
      (fun _ _ ↦ (contDiff_norm_sq ℝ).contMDiff.contMDiffAt) (isRegularValue_norm_sq one_ne_zero)
      (finrank_sub_finrank_real_eq Fact.out)).isImmersion
    (contMDiff_coe_sphere.isImmersion_of_injective_mfderiv (by simp)
      injective_mvfderiv_subtypeVal_sphere) rfl

/-- `TauCeti.normSqLevelDiffeomorphSphere` is the identity of points. -/
@[simp]
theorem coe_normSqLevelDiffeomorphSphere_apply (x : {x : E // ‖x‖ ^ 2 = 1}) :
    (normSqLevelDiffeomorphSphere (n := n) x : E) = x :=
  congrArg Subtype.val (Homeomorph.diffeomorphOfImmersions_apply _ _ _ _ x)

/-- The inverse of `TauCeti.normSqLevelDiffeomorphSphere` is the identity of points. -/
@[simp]
theorem coe_normSqLevelDiffeomorphSphere_symm_apply (x : sphere (0 : E) 1) :
    ((normSqLevelDiffeomorphSphere (n := n)).symm x : E) = x :=
  congrArg Subtype.val (Homeomorph.diffeomorphOfImmersions_symm_apply _ _ _ _ x)

/-- **The boundary of the closed unit ball is the stereographic sphere.** The identity of points is
a smooth diffeomorphism from the manifold boundary of the closed unit ball `{‖x‖² ≤ 1}`, for its
sublevel atlas, onto the unit sphere with its stereographic atlas; both are modelled on
`EuclideanSpace ℝ (Fin n)`. It is the boundary-to-level diffeomorphism
`TauCeti.scalarRegularSublevelBoundaryDiffeomorph` followed by
`TauCeti.normSqLevelDiffeomorphSphere`. -/
noncomputable def normSqSublevelBoundaryDiffeomorphSphere :
    ↥((𝓡∂ (n + 1)).boundary {x : E | ‖x‖ ^ 2 ≤ 1}) ≃ₘ⟮𝓡 n, 𝓡 n⟯ sphere (0 : E) 1 :=
  (scalarRegularSublevelBoundaryDiffeomorph (contDiff_norm_sq ℝ).contMDiff
    (isRegularValue_norm_sq one_ne_zero) Fact.out ∞).trans normSqLevelDiffeomorphSphere

/-- `TauCeti.normSqSublevelBoundaryDiffeomorphSphere` is the identity of points. -/
@[simp]
theorem coe_normSqSublevelBoundaryDiffeomorphSphere_apply
    (x : ↥((𝓡∂ (n + 1)).boundary {x : E | ‖x‖ ^ 2 ≤ 1})) :
    (normSqSublevelBoundaryDiffeomorphSphere x : E) = x.val.val := by
  simp [normSqSublevelBoundaryDiffeomorphSphere]

/-- The inverse of `TauCeti.normSqSublevelBoundaryDiffeomorphSphere` is the identity of points. -/
@[simp]
theorem coe_normSqSublevelBoundaryDiffeomorphSphere_symm_apply (x : sphere (0 : E) 1) :
    ((normSqSublevelBoundaryDiffeomorphSphere (n := n)).symm x).val.val = (x : E) :=
  (coe_normSqSublevelBoundaryDiffeomorphSphere_apply _).symm.trans
    (congrArg Subtype.val (Diffeomorph.apply_symm_apply _ x))

end TauCeti
