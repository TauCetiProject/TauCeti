/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Geometry.Manifold.Instances.Sphere
public import TauCeti.Geometry.Manifold.Immersion.Diffeomorph
public import TauCeti.Geometry.Manifold.Immersion.Differential
public import TauCeti.Geometry.Manifold.Morse.CriticalPoints
public import TauCeti.Geometry.Manifold.RegularValue.Scalar.Boundary

/-!
# Regular levels and sublevel boundaries in examples

This file tests the atlas `TauCeti.regularLevelChartedSpace` of a regular level of a real function,
and the boundary of a regular sublevel `TauCeti.scalarRegularSublevelChartedSpace`, on the standard
examples.

* **A coordinate level.** For the first coordinate `f (x, y) = x` of the plane, every value `c` is
  regular (`TauCeti.isRegularValue_fst`). The level `{x = c}` is modelled on `Fin 1 → ℝ`, the
  differential of its inclusion has range `ker df = span {(0, 1)}`
  (`TauCeti.mem_range_mfderiv_coe_fstLevel_iff`), and the second coordinate is a diffeomorphism
  from the level onto the line (`TauCeti.fstLevelDiffeomorph`).
* **A critical level.** For `f x = x²` on the line, `0` is not a regular value
  (`TauCeti.not_isRegularValue_sq_zero`): `df` vanishes at `0` (`TauCeti.mfderiv_sq_zero`), so its
  kernel is the whole line, while a regular level of a function on the line is modelled on
  `Fin 0 → ℝ`, so no linear map out of that model has range `ker df`
  (`TauCeti.range_ne_ker_mfderiv_sq_zero`). The singleton level `{0}` is therefore not a regular
  level with the tangent-kernel law `TauCeti.range_mfderiv_coe_regularLevel`.
* **Dimension zero.** On a manifold modelled on a zero-dimensional space every point is critical,
  so a value is regular exactly when it is not attained and every regular level is empty
  (`TauCeti.isRegularValue_iff_notMem_range_of_subsingleton`, next to the critical set).
* **The unit sphere.** In a real inner product space `E` of dimension `n + 1`, every nonzero value
  of `f x = ‖x‖²` is regular (`TauCeti.isRegularValue_norm_sq`). The level `{‖x‖² = 1}`, with its
  level atlas modelled on `Fin n → ℝ`, is diffeomorphic to the unit sphere with Mathlib's
  stereographic atlas, modelled on `EuclideanSpace ℝ (Fin n)`, by the identity of points
  (`TauCeti.normSqLevelDiffeomorphSphere`). The manifold boundary of the closed unit ball
  `{‖x‖² ≤ 1}`, with its sublevel atlas, is the unit sphere as a set
  (`TauCeti.boundary_normSqSublevel`), its face chart at a point of the sphere has inward
  coordinate `1 - ‖x‖²` (`TauCeti.normSqSublevelChartAt_apply_zero`), and the boundary is
  diffeomorphic to the stereographic sphere by the identity of points
  (`TauCeti.normSqSublevelBoundaryDiffeomorphSphere`). For `E = ℝ²` the boundary of the closed disc
  is the unit circle, modelled on `EuclideanSpace ℝ (Fin 1)`; the model of the closed disc itself
  is the half-space of dimension `2`.

The diffeomorphisms are recognized through immersions into the ambient space
(`Homeomorph.diffeomorphOfImmersions`): a homeomorphism commuting with two immersions into a
common manifold is a diffeomorphism.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Corollary 5.14 and Proposition 5.38 (regular level sets and their tangent
  spaces), Proposition 5.47 (regular sublevel sets are regular domains).
-/

public section

open Function Metric Module Set
open scoped ContDiff Manifold RealInnerProductSpace

namespace TauCeti

/-! ### The level of a coordinate function of the plane -/

/-- The first coordinate of the plane is `C^m` for every `m`. -/
theorem contMDiffAt_fst_plane {m : ℕ∞ω} (p : ℝ × ℝ) :
    ContMDiffAt 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ) m (Prod.fst : ℝ × ℝ → ℝ) p :=
  contDiff_fst.contMDiff.contMDiffAt

/-- The derivative of the first coordinate of the plane is the first projection. -/
theorem mfderiv_fst_plane_apply (p v : ℝ × ℝ) :
    mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ) (Prod.fst : ℝ × ℝ → ℝ) p v = v.1 := by
  rw [mfderiv_eq_fderiv, fderiv_fst]
  -- The identifications `NormedSpace.fromTangentSpace` of tangent spaces of vector spaces are
  -- identities.
  rfl

/-- Every value of the first coordinate of the plane is a regular value. -/
theorem isRegularValue_fst (c : ℝ) :
    IsRegularValue 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ) (Prod.fst : ℝ × ℝ → ℝ) c :=
  isRegularValue_iff.2 fun p _ ↦ isRegularPoint_iff.2 fun t ↦
    ⟨(t, 0), mfderiv_fst_plane_apply p (t, 0)⟩

/-- The levels of a real function on the plane have dimension `1`. -/
theorem finrank_plane_sub_finrank_real : finrank ℝ (ℝ × ℝ) - finrank ℝ ℝ = 1 := by
  simp

/-- The level atlas `TauCeti.regularLevelChartedSpace` of the level `{x = c}` of the first
coordinate of the plane, modelled on `Fin 1 → ℝ`. -/
noncomputable abbrev fstLevelChartedSpace (c : ℝ) :
    ChartedSpace (Fin 1 → ℝ) {p : ℝ × ℝ // p.1 = c} :=
  regularLevelChartedSpace (fun p _ ↦ contMDiffAt_fst_plane p) (isRegularValue_fst c)
    finrank_plane_sub_finrank_real

attribute [local instance] fstLevelChartedSpace

/-- **The tangent line of a coordinate level.** For the level atlas of the regular level `{x = c}`
of the first coordinate of the plane, the differential of the inclusion at every point has range
`ker df`, the vectors `(u, w)` with `u = 0`, that is, the line spanned by `(0, 1)`. -/
theorem mem_range_mfderiv_coe_fstLevel_iff {c : ℝ} (p : {p : ℝ × ℝ // p.1 = c}) (v : ℝ × ℝ) :
    v ∈ (mfderiv 𝓘(ℝ, Fin 1 → ℝ) 𝓘(ℝ, ℝ × ℝ) (Subtype.val : {p : ℝ × ℝ // p.1 = c} → ℝ × ℝ)
      p).range ↔ v.1 = 0 := by
  rw [range_mfderiv_coe_regularLevel]
  -- Tangent vectors of the plane are pairs of reals, and `df (u, w) = u`.
  exact Iff.trans (LinearMap.mem_ker (M := TangentSpace 𝓘(ℝ, ℝ × ℝ) (p : ℝ × ℝ)))
    (Eq.congr_left (mfderiv_fst_plane_apply p v))

/-- The level `{x = c}` of the first coordinate of the plane is homeomorphic to the line by the
second coordinate. -/
private def fstLevelHomeomorph (c : ℝ) : {p : ℝ × ℝ // p.1 = c} ≃ₜ ℝ where
  toFun p := p.1.2
  invFun y := ⟨(c, y), rfl⟩
  left_inv p := Subtype.ext (Prod.ext p.2.symm rfl)
  right_inv _ := rfl
  continuous_toFun := continuous_snd.comp continuous_subtype_val
  continuous_invFun := (continuous_const.prodMk continuous_id).subtype_mk _

/-- The vertical line `y ↦ (c, y)` is a smooth immersion of the line into the plane. -/
private theorem isImmersion_mk_plane (c : ℝ) :
    Manifold.IsImmersion 𝓘(ℝ) 𝓘(ℝ, ℝ × ℝ) ∞ (fun y : ℝ ↦ (c, y)) :=
  -- The second coordinate is a smooth left inverse.
  (contDiff_const.prodMk contDiff_id).contMDiff.isImmersion_of_leftInverse (by simp)
    (fun _ ↦ (contDiff_snd (n := 1)).contMDiff.mdifferentiableAt one_ne_zero) fun _ ↦ rfl

/-- **A coordinate level is a line.** The second coordinate is a smooth diffeomorphism from the
level `{x = c}` of the first coordinate of the plane, with its level atlas modelled on
`Fin 1 → ℝ`, onto the real line. -/
noncomputable def fstLevelDiffeomorph (c : ℝ) :
    {p : ℝ × ℝ // p.1 = c} ≃ₘ⟮𝓘(ℝ, Fin 1 → ℝ), 𝓘(ℝ)⟯ ℝ :=
  (fstLevelHomeomorph c).diffeomorphOfImmersions
    (isImmersionOfComplement_coe_regularLevel (m := ∞) (by simp)
      (fun p _ ↦ contMDiffAt_fst_plane p) (isRegularValue_fst c)
      finrank_plane_sub_finrank_real).isImmersion
    (isImmersion_mk_plane c) (funext fun p ↦ Prod.ext p.2.symm rfl)

/-- `TauCeti.fstLevelDiffeomorph` is the second coordinate. -/
@[simp]
theorem fstLevelDiffeomorph_apply (c : ℝ) (p : {p : ℝ × ℝ // p.1 = c}) :
    fstLevelDiffeomorph c p = p.1.2 :=
  Homeomorph.diffeomorphOfImmersions_apply _ _ _ _ p

/-- The inverse of `TauCeti.fstLevelDiffeomorph` is `y ↦ (c, y)`. -/
@[simp]
theorem coe_fstLevelDiffeomorph_symm_apply (c y : ℝ) :
    ((fstLevelDiffeomorph c).symm y : ℝ × ℝ) = (c, y) :=
  congrArg Subtype.val (Homeomorph.diffeomorphOfImmersions_symm_apply _ _ _ _ y)

/-! ### A critical level on the line -/

/-- The derivative of `x ↦ x²` vanishes at `0`. -/
theorem mfderiv_sq_zero : mfderiv 𝓘(ℝ) 𝓘(ℝ) (fun x : ℝ ↦ x ^ 2) 0 = 0 := by
  rw [← mem_criticalPoints_iff_mfderiv_eq_zero, criticalPoints_pow le_rfl]
  exact mem_singleton 0

/-- **The level `{x² = 0}` is not regular.** The value `0` of `x ↦ x²` on the line is critical. -/
theorem not_isRegularValue_sq_zero : ¬ IsRegularValue 𝓘(ℝ) 𝓘(ℝ) (fun x : ℝ ↦ x ^ 2) 0 := by
  rw [isRegularValue_iff_notMem_image_criticalPoints, criticalPoints_pow le_rfl, not_not]
  exact ⟨0, mem_singleton 0, by norm_num⟩

/-- **The critical level `{x² = 0}` fails the tangent-kernel law.** A regular level of a function
on the line is modelled on `Fin (1 - 1) → ℝ`, a zero space, so the differential at `0` of an
inclusion from it has range of dimension `0`. At the critical point `0` of `x ↦ x²` the kernel of
`df` is the whole line, of dimension `1`, so no linear map from that model to the tangent line has
range `ker df`: the singleton level cannot carry the conclusion of
`TauCeti.range_mfderiv_coe_regularLevel`. -/
theorem range_ne_ker_mfderiv_sq_zero
    (L : (Fin (finrank ℝ ℝ - finrank ℝ ℝ) → ℝ) →L[ℝ] TangentSpace 𝓘(ℝ) (0 : ℝ)) :
    L.range ≠ (mfderiv 𝓘(ℝ) 𝓘(ℝ) (fun x : ℝ ↦ x ^ 2) 0).ker := by
  intro h
  have h1 := LinearMap.finrank_range_le
    (L : (Fin (finrank ℝ ℝ - finrank ℝ ℝ) → ℝ) →ₗ[ℝ] TangentSpace 𝓘(ℝ) (0 : ℝ))
  rw [h, mfderiv_sq_zero, ContinuousLinearMap.toLinearMap_zero, LinearMap.ker_zero, finrank_top,
    finrank_fin_fun, Nat.sub_self] at h1
  have h2 : finrank ℝ (TangentSpace 𝓘(ℝ) (0 : ℝ)) = 1 := finrank_self ℝ
  omega

/-! ### The unit sphere as a regular level and as the boundary of the unit ball -/

section Sphere

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}

/-- The squared norm is smooth. -/
theorem contMDiff_norm_sq {m : ℕ∞ω} : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) m (fun x : E ↦ ‖x‖ ^ 2) :=
  (contDiff_norm_sq ℝ).contMDiff

/-- **The spheres are regular levels.** Every nonzero value of the squared norm is regular: the
derivative `v ↦ 2 ⟪x, v⟫` at a point `x ≠ 0` does not vanish on `x`. -/
theorem isRegularValue_norm_sq {c : ℝ} (hc : c ≠ 0) :
    IsRegularValue 𝓘(ℝ, E) 𝓘(ℝ) (fun x : E ↦ ‖x‖ ^ 2) c := by
  rw [isRegularValue_iff_notMem_image_criticalPoints]
  rintro ⟨x, hx, rfl⟩
  rw [mem_criticalPoints_iff_fderiv_eq_zero, (hasStrictFDerivAt_norm_sq x).hasFDerivAt.fderiv] at hx
  -- Evaluating the derivative `2 ⟪x, ·⟫` at `x` gives `2 ‖x‖² = 0`.
  have h : (2 : ℕ) • ‖x‖ ^ 2 = 0 := by
    simpa [real_inner_self_eq_norm_sq] using congrArg (fun L : E →L[ℝ] ℝ ↦ L x) hx
  exact hc ((smul_eq_zero.1 h).resolve_left two_ne_zero)

omit [InnerProductSpace ℝ E] in
/-- The level of the squared norm at `1` is the unit sphere. -/
theorem norm_sq_eq_one_iff {x : E} : ‖x‖ ^ 2 = 1 ↔ x ∈ sphere (0 : E) 1 := by
  rw [mem_sphere_zero_iff_norm, pow_eq_one_iff_of_nonneg (norm_nonneg x) two_ne_zero]

variable [FiniteDimensional ℝ E] [Fact (finrank ℝ E = n + 1)]

variable (E n) in
/-- The level atlas `TauCeti.regularLevelChartedSpace` of the level `{‖x‖² = 1}`, modelled on
`Fin n → ℝ`. -/
noncomputable abbrev normSqLevelChartedSpace : ChartedSpace (Fin n → ℝ) {x : E // ‖x‖ ^ 2 = 1} :=
  regularLevelChartedSpace (fun _ _ ↦ contMDiff_norm_sq.contMDiffAt)
    (isRegularValue_norm_sq one_ne_zero) (finrank_sub_finrank_real_eq Fact.out)

variable (E n) in
/-- The sublevel atlas `TauCeti.scalarRegularSublevelChartedSpace` of the closed unit ball
`{‖x‖² ≤ 1}`, modelled on the half-space of dimension `n + 1`. -/
noncomputable abbrev normSqSublevelChartedSpace :
    ChartedSpace (EuclideanHalfSpace (n + 1)) {x : E | ‖x‖ ^ 2 ≤ 1} :=
  scalarRegularSublevelChartedSpace contMDiff_norm_sq (isRegularValue_norm_sq one_ne_zero) Fact.out

attribute [local instance] normSqLevelChartedSpace normSqSublevelChartedSpace

/-- The closed unit ball is a `C¹` manifold with boundary for its sublevel atlas. -/
theorem isManifold_normSqSublevel : IsManifold (𝓡∂ (n + 1)) 1 {x : E | ‖x‖ ^ 2 ≤ 1} :=
  isManifold_scalarRegularSublevel (isRegularValue_norm_sq one_ne_zero) Fact.out le_rfl
    contMDiff_norm_sq

attribute [local instance] isManifold_normSqSublevel

/-- The level `{‖x‖² = 1}` is homeomorphic to the unit sphere by the identity of points. -/
private def normSqLevelHomeomorphSphere : {x : E // ‖x‖ ^ 2 = 1} ≃ₜ sphere (0 : E) 1 where
  toFun x := ⟨x.1, norm_sq_eq_one_iff.1 x.2⟩
  invFun x := ⟨x.1, norm_sq_eq_one_iff.2 x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := continuous_subtype_val.subtype_mk _
  continuous_invFun := continuous_subtype_val.subtype_mk _

/-- **The unit sphere is the regular level of the squared norm.** The identity of points is a
smooth diffeomorphism from the level `{‖x‖² = 1}`, with its level atlas modelled on `Fin n → ℝ`,
onto the unit sphere with its stereographic atlas, modelled on `EuclideanSpace ℝ (Fin n)`. -/
noncomputable def normSqLevelDiffeomorphSphere :
    {x : E // ‖x‖ ^ 2 = 1} ≃ₘ⟮𝓘(ℝ, Fin n → ℝ), 𝓡 n⟯ sphere (0 : E) 1 :=
  normSqLevelHomeomorphSphere.diffeomorphOfImmersions
    (isImmersionOfComplement_coe_regularLevel (m := ∞) (by simp)
      (fun _ _ ↦ contMDiff_norm_sq.contMDiffAt) (isRegularValue_norm_sq one_ne_zero)
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

/-- **The boundary of the closed unit ball is the unit sphere.** For the sublevel atlas of the
closed unit ball `{‖x‖² ≤ 1}`, modelled on the half-space of dimension `n + 1`, the manifold
boundary consists of the points of the unit sphere. -/
theorem boundary_normSqSublevel :
    (𝓡∂ (n + 1)).boundary {x : E | ‖x‖ ^ 2 ≤ 1} =
      {x : {x : E | ‖x‖ ^ 2 ≤ 1} | (x : E) ∈ sphere (0 : E) 1} := by
  rw [boundary_scalarRegularSublevel (isRegularValue_norm_sq (E := E) one_ne_zero) Fact.out le_rfl
    contMDiff_norm_sq]
  ext x
  exact norm_sq_eq_one_iff

/-- **The face chart of the closed unit ball.** At a point `x` of the unit sphere, the preferred
chart of the closed unit ball `{‖x‖² ≤ 1}` has inward coordinate `1 - ‖w‖²` on its source; in
particular it is `0` at `x`. -/
theorem normSqSublevelChartAt_apply_zero {x w : {x : E | ‖x‖ ^ 2 ≤ 1}}
    (hx : (x : E) ∈ sphere (0 : E) 1) (hw : w ∈ (chartAt (EuclideanHalfSpace (n + 1)) x).source) :
    (chartAt (EuclideanHalfSpace (n + 1)) x w).1 0 = 1 - ‖(w : E)‖ ^ 2 := by
  rw [scalarRegularSublevelChartedSpace_chartAt] at hw ⊢
  exact scalarRegularSublevelChartAt_apply_zero_of_eq _ _ _ (norm_sq_eq_one_iff.2 hx) hw

/-- **The boundary of the closed unit ball is the stereographic sphere.** The identity of points is
a smooth diffeomorphism from the manifold boundary of the closed unit ball `{‖x‖² ≤ 1}`, for its
sublevel atlas, onto the unit sphere with its stereographic atlas; both are modelled on
`EuclideanSpace ℝ (Fin n)`. It is the boundary-to-level diffeomorphism
`TauCeti.scalarRegularSublevelBoundaryDiffeomorph` followed by
`TauCeti.normSqLevelDiffeomorphSphere`. -/
noncomputable def normSqSublevelBoundaryDiffeomorphSphere :
    ↥((𝓡∂ (n + 1)).boundary {x : E | ‖x‖ ^ 2 ≤ 1}) ≃ₘ⟮𝓡 n, 𝓡 n⟯ sphere (0 : E) 1 :=
  (scalarRegularSublevelBoundaryDiffeomorph contMDiff_norm_sq
    (isRegularValue_norm_sq one_ne_zero) Fact.out ∞).trans normSqLevelDiffeomorphSphere

/-- `TauCeti.normSqSublevelBoundaryDiffeomorphSphere` is the identity of points. -/
@[simp]
theorem coe_normSqSublevelBoundaryDiffeomorphSphere_apply
    (x : ↥((𝓡∂ (n + 1)).boundary {x : E | ‖x‖ ^ 2 ≤ 1})) :
    (normSqSublevelBoundaryDiffeomorphSphere x : E) = x.1.1 := by
  rw [normSqSublevelBoundaryDiffeomorphSphere, Diffeomorph.coe_trans, comp_apply,
    coe_normSqLevelDiffeomorphSphere_apply, coe_scalarRegularSublevelBoundaryDiffeomorph,
    coe_scalarRegularSublevelBoundaryHomeomorph_apply]

end Sphere

end TauCeti
