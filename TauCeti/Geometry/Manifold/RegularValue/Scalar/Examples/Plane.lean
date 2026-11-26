/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.RegularValue.Level
public import TauCeti.Geometry.Manifold.RegularValue.NormSq
public import TauCeti.Geometry.Manifold.RegularValue.Scalar.Boundary

/-!
# Regular levels and sublevels of functions on the plane

Two functions test the regular-level and boundary-face API of
`TauCeti.Geometry.Manifold.RegularValue.Scalar` in dimension two.

**A coordinate function.** Every value `c` of the first coordinate `(x, y) ↦ x` on `ℝ × ℝ` is
regular (`TauCeti.isRegularValue_fst`), so the level `{p | p.1 = c}` carries the atlas
`TauCeti.regularLevelChartedSpace`, modelled on `Fin 1 → ℝ`
(`TauCeti.regularLevelFstChartedSpace`). For this atlas the level is a copy
of `ℝ`: the second coordinate is a diffeomorphism onto `ℝ`
(`TauCeti.regularLevelFstDiffeomorph`). Its tangent space at every point, the range of the
derivative of the inclusion, is the line spanned by `e₂ = (0, 1)`, which is the kernel of the
derivative of the first coordinate (`TauCeti.range_mfderiv_coe_regularLevel_fst`). Read through
the diffeomorphism with `ℝ`, the inclusion is `y ↦ (c, y)`, with derivative `v ↦ (0, v)`
(`TauCeti.fderiv_coe_regularLevelFstDiffeomorph_symm`).

**The squared norm.** On a real inner product space every nonzero value of `x ↦ ‖x‖²` is regular
(`TauCeti.isRegularValue_norm_sq`). So in dimension `n + 1` the closed unit ball `{‖x‖² ≤ 1}`
carries the half-space atlas `TauCeti.scalarRegularSublevelChartedSpace`, and its manifold boundary
is the unit sphere (`TauCeti.boundary_scalarRegularSublevel_norm_sq`). For the plane, `n = 1`, the
boundary is the unit circle. Its boundary atlas is modelled on `EuclideanSpace ℝ (Fin 1)`, its
regular-level atlas on `Fin 1 → ℝ`, and `TauCeti.scalarRegularSublevelBoundaryDiffeomorph`
identifies the two by the identity of points. At a point of the circle such as `(1, 0)` the
preferred chart of the disc is a face chart, whose zeroth coordinate is the inward coordinate
`1 - ‖x‖²` (`TauCeti.scalarRegularSublevelChartAt_apply_zero_of_eq`), which vanishes on the circle;
an example at the end of the file checks this at `(1, 0)`.
-/

public section

open Set Module Metric
open scoped ContDiff Manifold

namespace TauCeti

/-! ### The levels of a coordinate function -/

section Coordinate

variable (c : ℝ)

/-- The regular-level atlas `TauCeti.regularLevelChartedSpace` on the level `{p | p.1 = c}` of the
first coordinate on `ℝ × ℝ`, modelled on `Fin 1 → ℝ`. -/
noncomputable abbrev regularLevelFstChartedSpace :
    ChartedSpace (Fin 1 → ℝ) {p : ℝ × ℝ // p.1 = c} :=
  regularLevelChartedSpace (fun _ _ ↦ contDiff_fst.contMDiff.contMDiffAt) (isRegularValue_fst c)
    (by simp)

attribute [local instance] regularLevelFstChartedSpace

/-- **The tangent line of a coordinate level.** At every point of the level `{p | p.1 = c}` of the
first coordinate on `ℝ × ℝ`, the derivative of the inclusion, for the regular-level atlas, has
range the line spanned by `(0, 1)`. -/
theorem range_mfderiv_coe_regularLevel_fst (x : {p : ℝ × ℝ // p.1 = c}) :
    (mfderiv 𝓘(ℝ, Fin 1 → ℝ) 𝓘(ℝ, ℝ × ℝ) (Subtype.val : {p : ℝ × ℝ // p.1 = c} → ℝ × ℝ)
        x).range =
      LinearMap.range (LinearMap.inr ℝ ℝ ℝ) := by
  rw [range_mfderiv_coe_regularLevel, mfderiv_eq_fderiv, fderiv_fst]
  exact LinearMap.ker_fst ℝ ℝ ℝ

/-- **A coordinate level is a copy of `ℝ`.** For the regular-level atlas, the second coordinate is a
smooth diffeomorphism from the level `{p | p.1 = c}` of the first coordinate on `ℝ × ℝ` onto `ℝ`,
with inverse `y ↦ (c, y)`. -/
noncomputable def regularLevelFstDiffeomorph :
    {p : ℝ × ℝ // p.1 = c} ≃ₘ⟮𝓘(ℝ, Fin 1 → ℝ), 𝓘(ℝ)⟯ ℝ :=
  have hi := (isSmoothEmbedding_coe_regularLevel (n := 1) (m := ∞) (by simp)
    (fun _ _ ↦ contDiff_fst.contMDiff.contMDiffAt) (isRegularValue_fst c) (by simp)).isImmersion
  { toFun p := p.val.2
    invFun y := ⟨(c, y), rfl⟩
    left_inv p := Subtype.ext (Prod.ext p.property.symm rfl)
    right_inv _ := rfl
    contMDiff_toFun := contDiff_snd.contMDiff.comp hi.contMDiff
    contMDiff_invFun := (ContMDiff.iff_comp_isImmersion hi).2
      ⟨(continuous_const.prodMk continuous_id).subtype_mk _,
        (contDiff_const.prodMk contDiff_id).contMDiff⟩ }

/-- The diffeomorphism of a coordinate level with `ℝ` is the second coordinate. -/
@[simp]
theorem regularLevelFstDiffeomorph_apply (p : {p : ℝ × ℝ // p.1 = c}) :
    regularLevelFstDiffeomorph c p = p.val.2 :=
  (rfl)

/-- The inverse of the diffeomorphism of the level `{p | p.1 = c}` with `ℝ` is `y ↦ (c, y)`. -/
@[simp]
theorem coe_regularLevelFstDiffeomorph_symm_apply (y : ℝ) :
    ((regularLevelFstDiffeomorph c).symm y : ℝ × ℝ) = (c, y) :=
  (rfl)

/-- **The derivative of the inclusion of a coordinate level.** Read through the diffeomorphism of
the level `{p | p.1 = c}` with `ℝ`, the inclusion into `ℝ × ℝ` is `y ↦ (c, y)`, whose derivative is
`v ↦ (0, v)`. -/
theorem fderiv_coe_regularLevelFstDiffeomorph_symm (y : ℝ) :
    fderiv ℝ (fun y ↦ ((regularLevelFstDiffeomorph c).symm y : ℝ × ℝ)) y =
      ContinuousLinearMap.inr ℝ ℝ ℝ := by
  simp only [coe_regularLevelFstDiffeomorph_symm_apply]
  exact ((hasFDerivAt_const c y).prodMk (hasFDerivAt_id y)).fderiv

end Coordinate

/-! ### The sublevels of the squared norm -/

section NormSq

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {n : ℕ} (hn : finrank ℝ E = n + 1)

/-- **The boundary of the unit ball is the unit sphere.** For the half-space atlas of the regular
sublevel `{x | ‖x‖² ≤ 1}` of the squared norm on a real inner product space of dimension `n + 1`,
the manifold boundary consists of the points of the unit sphere. -/
theorem boundary_scalarRegularSublevel_norm_sq :
    letI := scalarRegularSublevelChartedSpace (contDiff_norm_sq ℝ).contMDiff
      (isRegularValue_norm_sq (E := E) one_ne_zero) hn
    (𝓡∂ (n + 1)).boundary {x : E | ‖x‖ ^ 2 ≤ 1} =
      {x : {x : E | ‖x‖ ^ 2 ≤ 1} | (x : E) ∈ sphere 0 1} := by
  rw [boundary_scalarRegularSublevel (isRegularValue_norm_sq one_ne_zero) hn le_rfl
    (contDiff_norm_sq ℝ).contMDiff]
  ext x
  simp only [mem_ofPred_eq, mem_sphere_zero_iff_norm]
  exact pow_eq_one_iff_of_nonneg (norm_nonneg (x : E)) two_ne_zero

end NormSq

/- At the point `(1, 0)` of the unit circle, the preferred chart of the closed unit disc
`{x | ‖x‖² ≤ 1}` of the Euclidean plane is a face chart, whose zeroth coordinate is the inward
coordinate `1 - ‖x‖²`; it vanishes at `(1, 0)`. -/
example :
    letI := scalarRegularSublevelChartedSpace (contDiff_norm_sq ℝ).contMDiff
      (isRegularValue_norm_sq (E := EuclideanSpace ℝ (Fin 2)) one_ne_zero)
      (finrank_euclideanSpace_fin (n := 2))
    (chartAt (EuclideanHalfSpace 2)
        (⟨!₂[1, 0], by simp [EuclideanSpace.norm_sq_eq]⟩ :
          {x : EuclideanSpace ℝ (Fin 2) | ‖x‖ ^ 2 ≤ 1})
        ⟨!₂[1, 0], by simp [EuclideanSpace.norm_sq_eq]⟩).val 0 = 0 := by
  have h : ‖(!₂[1, 0] : EuclideanSpace ℝ (Fin 2))‖ ^ 2 = 1 := by simp [EuclideanSpace.norm_sq_eq]
  rw [scalarRegularSublevelChartedSpace_chartAt,
    scalarRegularSublevelChartAt_apply_zero_of_eq _ _ _ h
      (mem_scalarRegularSublevelChartAt_source _ _ _ _), h, sub_self]

end TauCeti
