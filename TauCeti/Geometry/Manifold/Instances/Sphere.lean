/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Instances.Sphere
public import Mathlib.Analysis.Normed.Module.Normalize
public import Mathlib.Geometry.Manifold.SmoothEmbedding
public import TauCeti.Analysis.InnerProductSpace.LinearIsometry
public import TauCeti.Geometry.Manifold.Immersion.Basic
public import TauCeti.Geometry.Sphere.LinearIsometry

import Mathlib.Analysis.Calculus.Deriv.Linear
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Geometry.Manifold.Algebra.SMul
import TauCeti.Geometry.Manifold.ContMDiff.Subtype
import TauCeti.Geometry.Manifold.Immersion.Differential
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Topology.MetricSpace.HausdorffDimension
import TauCeti.Analysis.InnerProductSpace.Projection.Basic
import TauCeti.Analysis.Normed.Group.BallSphere
import TauCeti.Analysis.SpecialFunctions.Complex.Arg
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace

/-!
# The stereographic charts of the sphere, and the smooth embeddings of spheres induced by
linear isometries

Mathlib charts the unit sphere of an `(n + 1)`-dimensional real inner product space by
stereographic projection, the preferred chart at `v` projecting from the antipode `-v`
(`EuclideanSpace.instChartedSpaceSphere`). This file records the facts about these charts
that computations in a chart at a chosen point use: which stereographic projection the preferred
chart is, that the extended chart at `v` sends `v` to the origin of the model space, and that the
inverse of a stereographic chart is a smooth embedding of the model space into the sphere. Read in
the ambient space, the inverse of stereographic projection has injective derivative, so it is a
regular parametrization of the sphere minus a point. Stereographic projection from `v` is a
diffeomorphism from the sphere minus `v` onto the model space, and from the sphere minus `v` and
`-v` onto the punctured model space, since it sends exactly `-v` to the origin.

It then uses the charts to show that a linear isometry `ι : F →ₗᵢ[ℝ] E` restricts to a smooth
embedding of unit spheres, `LinearIsometry.unitSphereMap`. Stereographic projection is defined
from inner products and orthogonal projections, both of which `ι` preserves, so `ι` carries the
stereographic chart at `v` to the stereographic chart at `ι v`: in those two charts, `ι` reads as a
linear isometry `LinearIsometry.stereographicModelMap` of the model Euclidean spaces, and a linear
isometry is the inclusion of a factor in a product decomposition
(`LinearIsometry.prodOrthogonalRangeEquiv`). That is the normal form Mathlib's
`Manifold.IsImmersionAt` asks for, and together with the isometric embedding of the spheres it
makes the restriction a smooth embedding. Great circles, the geometric presentation of the unknot,
are the case of a linear isometry `ℂ →ₗᵢ[ℝ] E`. A family of linear isometries depending smoothly on
a parameter likewise acts smoothly on the sphere.

Finally, the covering map `Circle.exp : ℝ → S¹` has injective derivative everywhere, so that a
loop and its lift to `ℝ` have the same tangent lines, and its local inverse, the argument, is smooth
away from `-1`. A differentiable path or loop in a sphere of dimension at least two omits a point,
allowing the entire path or loop to be read in one stereographic chart.

## Main results

* `TauCeti.finrank_euclideanSpace_fin_succ_fact`: the dimension of `ℝⁿ⁺¹`, in the form the
  stereographic charts of its unit sphere take it.
* `TauCeti.injective_fderiv_stereoInvFunAux_comp_coe`: the inverse of stereographic projection
  from `v`, as a map from `(ℝ ∙ v)ᗮ` to the ambient space, has injective derivative.
* `TauCeti.fact_finrank_orthogonal_span_singleton_coe_sphere`: the orthogonal complement `v^⊥` of
  a point `v` of `Sⁿ⁺¹` has dimension `n + 1`, so its unit sphere, the sphere of unit tangent
  vectors at `v`, is an `n`-dimensional manifold.
* `LinearIndependent.finCons_mvfderiv_coe_sphere`: a point `u` of the sphere followed by the image
  in the ambient space of a linearly independent family of tangent vectors at `u` is linearly
  independent.
* `TauCeti.chartAt_sphere`: the preferred chart at `v` is `stereographic' n (-v)`.
* `TauCeti.extChartAt_sphere_apply_self`: the preferred extended chart at `v` sends `v` to `0`.
* `TauCeti.isSmoothEmbedding_stereographic'_symm`: the inverse of a stereographic chart is a
  smooth embedding of the model space into the sphere.
* `TauCeti.coe_comp_stereographic'_symm`, `TauCeti.contDiff_coe_comp_stereographic'_symm`,
  `TauCeti.injective_fderiv_coe_comp_stereographic'_symm`: read in the ambient space, the inverse
  of a stereographic chart is `stereoInvFunAux` precomposed with a linear isometry, so it is smooth
  with injective derivative.
* `TauCeti.compl_singleton_sup_compl_singleton_neg_eq_top`: the complements of two antipodal
  points cover the sphere.
* `TauCeti.stereographicDiffeomorph`, `TauCeti.stereographicPuncturedDiffeomorph`: stereographic
  projection from `v` as a diffeomorphism from the sphere minus `v` onto `ℝⁿ`, and from the sphere
  minus `v` and `-v` onto `ℝⁿ \ {0}`.
* `LinearIsometry.stereographic'_unitSphereMap`: the stereographic charts read a linear isometry
  of unit spheres as a linear isometry of the model spaces.
* `LinearIsometry.isSmoothEmbedding_unitSphereMap`: the restriction of a linear isometry to the
  unit spheres is a smooth embedding, at every differentiability order.
* `TauCeti.contMDiff_unitSphereEquiv_apply`: a smooth family of linear isometries acts smoothly
  on the unit sphere.
* `TauCeti.injective_mfderiv_circleExp`, `TauCeti.surjective_mfderiv_circleExp`: the derivative of
  `Circle.exp : ℝ → S¹` is bijective.
* `TauCeti.contMDiffAt_circle_arg`: the argument is smooth on the circle away from `-1`.
* `TauCeti.toSpanSingleton_deriv_comp_circleExp`,
  `TauCeti.toSpanSingleton_deriv_chart_comp_circleExp`: the chain rule for a map of the circle read
  along `Circle.exp`, into a normed space or, through a chart, into a manifold.
* `TauCeti.contDiffOn_chartAt_comp_circleExp`: a smooth map of the circle, read in a chart along
  `Circle.exp` on an arc, is smooth.
* `TauCeti.deriv_chartAt_comp_circleExp_eq`, `TauCeti.deriv_chartAt_comp_circleExp_ne_zero`: two
  maps of the circle agreeing to first order at `1` have the same velocity at `0` when read in a
  chart at their common value along `Circle.exp`, and that velocity is nonzero for an immersion.
* `TauCeti.mfderiv_eq_of_deriv_comp_circleExp_eq`: two maps of the circle into a normed space
  with the same velocity at `t` along `Circle.exp` have the same derivative at `exp (t i)`.
* `TauCeti.deriv_comp_circleExp_ne_zero_and_range_mfderiv`: lifting a `C¹` immersed circle
  along `Circle.exp` gives a nonzero derivative spanning its tangent line.
* `TauCeti.injective_mfderiv_of_deriv_comp_circleExp_ne_zero`: conversely, a map of the circle
  whose lift along `Circle.exp` has nonzero derivative at `t` has injective derivative at
  `exp (t i)`.
* `TauCeti.smul_deriv_coe_comp_circleExp`: the chain rule for a loop in a sphere read along
  `Circle.exp` in the ambient space.
* `TauCeti.inner_deriv_coe_comp_circleExp_eq_zero`,
  `TauCeti.deriv_coe_comp_circleExp_ne_zero`: the velocity of a loop in a sphere, read along
  `Circle.exp` in the ambient space, is tangent to the sphere, and nonzero where the loop is
  immersive.
* `TauCeti.mfderiv_eq_of_deriv_coe_comp_circleExp_eq`,
  `TauCeti.deriv_coe_comp_circleExp_eq_of_mfderiv_eq`: two loops in a sphere through the same point
  have the same derivative there exactly when they have the same velocity, read along
  `Circle.exp`.
* `TauCeti.mfderiv_eq_of_deriv_comp_circleExp_eq_prod`: two maps of `S¹ × ℝ` into `Sⁿ × ℝ` which
  agree on a line `{z₀} × ℝ` have the same derivative at `(z₀, t)` when their slices at time `t`
  have the same velocity at `z₀` along `Circle.exp`.
* `TauCeti.deriv_coe_fst_comp_circleExp_ne_zero`: for such a map which is the line `s ↦ (y, s)`
  over `z₀` and has injective derivative, the sphere component of the slice has nonzero velocity.
* `TauCeti.exists_contMDiff_circle_hasDerivAt`: an arbitrarily small smooth function on the circle
  vanishing at a given point with velocity `1` there along `Circle.exp`.
* `TauCeti.exists_notMem_range_circle_sphere`: a differentiable loop in a sphere of dimension
  at least two omits a point.
* `TauCeti.contMDiff_coe_sphere_compl_zero`, `TauCeti.contMDiff_normalize_sphere`: the inclusion
  of the unit sphere into the punctured space `E \ {0}` and the radial projection
  `x ↦ x / ‖x‖` back onto the sphere are smooth; `TauCeti.contMDiff_normalize_compl_zero` is the
  radial projection read in `E`.
-/

public section

noncomputable section

open Function Manifold Metric Module Set TopologicalSpace
open scoped Manifold InnerProductSpace ContDiff

namespace TauCeti

/-- The dimension of `ℝⁿ⁺¹`, in the form `Fact (finrank ℝ E = n + 1)` taken by the stereographic
charts of the unit sphere of `E`. Installed with `attribute [local instance]`, it lets results
stated for the unit sphere of a general `E` apply to the unit sphere of
`EuclideanSpace ℝ (Fin (n + 1))`. -/
theorem finrank_euclideanSpace_fin_succ_fact (n : ℕ) :
    Fact (finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1) :=
  ⟨finrank_euclideanSpace_fin⟩

section Stereographic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The inverse of stereographic projection from a unit vector `v` has injective derivative at
every point of the hyperplane `(ℝ ∙ v)ᗮ`. -/
theorem injective_fderiv_stereoInvFunAux_comp_coe {v : E} (hv : ‖v‖ = 1) (w : (ℝ ∙ v)ᗮ) :
    Injective (fderiv ℝ (stereoInvFunAux v ∘ ((↑) : (ℝ ∙ v)ᗮ → E)) w) := by
  set ψ := stereoInvFunAux v ∘ ((↑) : (ℝ ∙ v)ᗮ → E)
  have hd : DifferentiableAt ℝ ψ w :=
    (contDiff_stereoInvFunAux.comp (ℝ ∙ v)ᗮ.subtypeL.contDiff).differentiable one_ne_zero w
  -- Stereographic projection is a left inverse of `ψ`, differentiable near `ψ w ≠ v`.
  have hnorm : ‖ψ w‖ = 1 := mem_sphere_zero_iff_norm.1 (stereoInvFunAux_mem hv w.2)
  have hne : innerSL ℝ v (ψ w) ≠ 1 := by
    rw [innerSL_apply_apply, Ne, inner_eq_one_iff_of_norm_eq_one hv hnorm]
    exact fun h => stereoInvFun_ne_north_pole hv w (Subtype.ext h.symm)
  have hst : DifferentiableAt ℝ (stereoToFun v) (ψ w) :=
    ((contDiffOn_stereoToFun (n := 1)).differentiableOn one_ne_zero).differentiableAt
      ((isOpen_ne_fun (innerSL ℝ v).continuous continuous_const).mem_nhds hne)
  have hcomp : fderiv ℝ (stereoToFun v) (ψ w) ∘L fderiv ℝ ψ w = ContinuousLinearMap.id ℝ _ := by
    rw [← fderiv_comp w hst hd, show stereoToFun v ∘ ψ = id from funext (stereo_right_inv hv),
      fderiv_id]
  exact Function.LeftInverse.injective (g := fderiv ℝ (stereoToFun v) (ψ w)) fun u => by
    simpa using congrArg (fun L => L u) hcomp

end Stereographic

section OrthogonalComplement

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
  [Fact (finrank ℝ E = n + 1 + 1)]

/-- The orthogonal complement of a point of the unit sphere of an `(n + 2)`-dimensional space has
dimension `n + 1`, so its own unit sphere is an `n`-dimensional manifold. Through the derivative
of the inclusion, it is the sphere of unit tangent vectors at the point
(`range_mvfderiv_subtypeVal`). -/
instance fact_finrank_orthogonal_span_singleton_coe_sphere (p : sphere (0 : E) 1) :
    Fact (finrank ℝ (ℝ ∙ (p : E))ᗮ = n + 1) :=
  ⟨Submodule.finrank_orthogonal_span_singleton (ne_zero_of_mem_unit_sphere p)⟩

end OrthogonalComplement

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
  [Fact (finrank ℝ E = n + 1)]

/-- A point of the sphere followed by the image of a linearly independent family of tangent
vectors at it is linearly independent in `E`: the derivative of the inclusion is injective with
range `u^⊥`, which does not contain `u`. -/
theorem _root_.LinearIndependent.finCons_mvfderiv_coe_sphere (u : sphere (0 : E) 1)
    {v : Fin n → TangentSpace (𝓡 n) u} (hv : LinearIndependent ℝ v) :
    LinearIndependent ℝ
      (Fin.cons (u : E) fun i ↦ mvfderiv (𝓡 n) ((↑) : sphere (0 : E) 1 → E) u (v i)) :=
  LinearIndependent.finCons_orthogonal_span_singleton (ne_zero_of_mem_unit_sphere u)
    (hv.map' _ (LinearMap.ker_eq_bot_of_injective (injective_mvfderiv_subtypeVal_sphere u)))
    fun _ ↦ range_mvfderiv_subtypeVal (n := n) u ▸ LinearMap.mem_range_self _ _

/-- The preferred chart of the sphere at `v` is the stereographic projection from `-v`. -/
theorem chartAt_sphere (v : sphere (0 : E) 1) :
    chartAt (EuclideanSpace ℝ (Fin n)) v = stereographic' n (-v) :=
  rfl

-- Not `@[simp]`: simp unfolds `extChartAt (𝓡 n) v v` to `chartAt _ v v` before this lemma can
-- fire, so it fails `simpNF`.
/-- The preferred extended chart of the sphere at `v` sends `v` to the origin. -/
theorem extChartAt_sphere_apply_self (v : sphere (0 : E) 1) : extChartAt (𝓡 n) v v = 0 := by
  rw [extChartAt_coe, modelWithCornersSelf_coe, id_comp, chartAt_sphere, stereographic',
    OpenPartialHomeomorph.trans_apply, stereographic_neg_apply,
    Homeomorph.toOpenPartialHomeomorph_apply, LinearIsometryEquiv.coe_toHomeomorph, map_zero]

/-- The inverse of a stereographic chart is a smooth embedding of the model Euclidean space into
the sphere, onto the complement of the centre of projection: read in that same chart it is the
identity. -/
theorem isSmoothEmbedding_stereographic'_symm (v : sphere (0 : E) 1) {k : ℕ∞ω} :
    IsSmoothEmbedding (𝓡 n) (𝓡 n) k (stereographic' n v).symm := by
  refine ⟨IsImmersionOfComplement.isImmersion (F := PUnit.{1}) fun w ↦ ?_,
    ((stereographic' n v).symm.isOpenEmbedding (by simp)).isEmbedding⟩
  refine IsImmersionAtOfComplement.mk_of_charts (ContinuousLinearEquiv.prodUnique ℝ _ _)
    (OpenPartialHomeomorph.refl _) (stereographic' n v) (mem_univ w)
    ((stereographic' n v).map_target (by simp))
    (IsManifold.chart_mem_maximalAtlas (I := 𝓡 n) (n := k) w)
    (IsManifold.subset_maximalAtlas ⟨v, rfl⟩)
    (fun u _ ↦ (stereographic' n v).map_target (by simp)) fun u _ ↦ ?_
  simp

/-- Read in the ambient space, the inverse of the stereographic chart `stereographic' n v` is the
inverse `stereoInvFunAux v` of stereographic projection, precomposed with the linear isometry of
`ℝⁿ` onto the hyperplane `(ℝ ∙ v)ᗮ` that the chart uses. -/
theorem coe_comp_stereographic'_symm (v : sphere (0 : E) 1) :
    ((↑) : sphere (0 : E) 1 → E) ∘ (stereographic' n v).symm =
      stereoInvFunAux (v : E) ∘ ((↑) : (ℝ ∙ (v : E))ᗮ → E) ∘
        (OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := ℝ) n
          (ne_zero_of_mem_unit_sphere v)).repr.symm := by
  funext y
  simp [stereographic'_symm_apply, smul_add]

/-- Read in the ambient space, the inverse of a stereographic chart is smooth. -/
theorem contDiff_coe_comp_stereographic'_symm (v : sphere (0 : E) 1) {k : ℕ∞ω} :
    ContDiff ℝ k (((↑) : sphere (0 : E) 1 → E) ∘ (stereographic' n v).symm) := by
  rw [coe_comp_stereographic'_symm]
  exact contDiff_stereoInvFunAux.comp ((ℝ ∙ (v : E))ᗮ.subtypeL.contDiff.comp
    (OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := ℝ) n
      (ne_zero_of_mem_unit_sphere v)).repr.symm.toContinuousLinearEquiv.contDiff)

/-- Read in the ambient space, the inverse of a stereographic chart has injective derivative at
every point. -/
theorem injective_fderiv_coe_comp_stereographic'_symm (v : sphere (0 : E) 1)
    (y : EuclideanSpace ℝ (Fin n)) :
    Injective (fderiv ℝ (((↑) : sphere (0 : E) 1 → E) ∘ (stereographic' n v).symm) y) := by
  set U := (OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := ℝ) n
    (ne_zero_of_mem_unit_sphere v)).repr
  rw [coe_comp_stereographic'_symm, ← Function.comp_assoc,
    ← LinearIsometryEquiv.coe_toContinuousLinearEquiv U.symm,
    ContinuousLinearEquiv.comp_right_fderiv]
  exact (injective_fderiv_stereoInvFunAux_comp_coe (norm_eq_of_mem_sphere v) _).comp
    U.symm.injective

/-- Stereographic projection from `v` is a chart in the maximal atlas of the sphere, at every
regularity. -/
theorem stereographic'_mem_maximalAtlas (v : sphere (0 : E) 1) {k : ℕ∞ω} :
    stereographic' n v ∈ IsManifold.maximalAtlas (𝓡 n) k (sphere (0 : E) 1) :=
  IsManifold.subset_maximalAtlas ⟨v, rfl⟩

/-- Stereographic projection from `v` sends the antipode `-v` to the origin. -/
@[simp]
theorem stereographic'_apply_neg (v : sphere (0 : E) 1) : stereographic' n v (-v) = 0 := by
  simp [stereographic', stereographic_apply_neg]

/-- Away from the centre `v` of projection, stereographic projection from `v` sends exactly the
antipode `-v` to the origin. -/
theorem stereographic'_eq_zero_iff {v x : sphere (0 : E) 1} (hx : x ≠ v) :
    stereographic' n v x = 0 ↔ x = -v :=
  ⟨fun h ↦ (stereographic' n v).injOn (by simpa using hx)
    (by simpa using (ne_neg_of_mem_unit_sphere ℝ v).symm)
    (h.trans (stereographic'_apply_neg v).symm), fun h ↦ h ▸ stereographic'_apply_neg v⟩

/-- The complements of two antipodal points cover the sphere. -/
theorem compl_singleton_sup_compl_singleton_neg_eq_top (v : sphere (0 : E) 1) :
    (⟨{v}ᶜ, isOpen_compl_singleton⟩ ⊔ ⟨{-v}ᶜ, isOpen_compl_singleton⟩ :
      Opens (sphere (0 : E) 1)) = ⊤ := by
  have := HasUniqueDiv.of_isTorsionFree ℝ E
  ext1
  simpa using compl_singleton_union_compl_singleton_neg one_ne_zero v

/-- Stereographic projection from `v`, as a smooth diffeomorphism from the sphere minus `v` onto the
model space `ℝⁿ`. -/
def stereographicDiffeomorph (v : sphere (0 : E) 1) :
    (⟨{v}ᶜ, isOpen_compl_singleton⟩ : Opens (sphere (0 : E) 1)) ≃ₘ⟮𝓡 n, 𝓡 n⟯
      EuclideanSpace ℝ (Fin n) where
  toFun x := stereographic' n v x
  invFun y := ⟨(stereographic' n v).symm y, by
    simpa using (stereographic' n v).map_target (x := y) (by simp)⟩
  left_inv x := Subtype.ext ((stereographic' n v).left_inv (by simp))
  right_inv y := (stereographic' n v).right_inv (by simp)
  contMDiff_toFun :=
    (contMDiffOn_of_mem_maximalAtlas (stereographic'_mem_maximalAtlas v)).comp_contMDiff
      contMDiff_subtype_val fun x ↦ by simp
  contMDiff_invFun := (ContMDiff.subtypeVal_comp_iff _ _).mp
    (isSmoothEmbedding_stereographic'_symm v).contMDiff

/-- The diffeomorphism `TauCeti.stereographicDiffeomorph v` is stereographic projection from `v`. -/
@[simp]
theorem stereographicDiffeomorph_apply (v : sphere (0 : E) 1)
    (x : (⟨{v}ᶜ, isOpen_compl_singleton⟩ : Opens (sphere (0 : E) 1))) :
    stereographicDiffeomorph v x = stereographic' n v x :=
  (rfl)

/-- The inverse of `TauCeti.stereographicDiffeomorph v` is inverse stereographic projection. -/
@[simp]
theorem coe_stereographicDiffeomorph_symm_apply (v : sphere (0 : E) 1)
    (y : EuclideanSpace ℝ (Fin n)) :
    ((stereographicDiffeomorph v).symm y : sphere (0 : E) 1) = (stereographic' n v).symm y :=
  (rfl)

/-- Stereographic projection from `v`, as a smooth diffeomorphism from the sphere minus `v` and `-v`
onto the punctured model space `ℝⁿ \ {0}`. -/
def stereographicPuncturedDiffeomorph (v : sphere (0 : E) 1) :
    (⟨{v}ᶜ ∩ {-v}ᶜ, isOpen_compl_singleton.inter isOpen_compl_singleton⟩ :
        Opens (sphere (0 : E) 1)) ≃ₘ⟮𝓡 n, 𝓘(ℝ, EuclideanSpace ℝ (Fin n))⟯
      (⟨{0}ᶜ, isOpen_compl_singleton⟩ : Opens (EuclideanSpace ℝ (Fin n))) where
  toFun x := ⟨stereographic' n v x, fun h ↦ x.2.2 ((stereographic'_eq_zero_iff x.2.1).mp h)⟩
  invFun y := ⟨(stereographic' n v).symm y, by
    have hv : (stereographic' n v).symm y ≠ v := by
      simpa using (stereographic' n v).map_target (x := y) (by simp)
    refine ⟨hv, fun h ↦ y.2 ?_⟩
    have := (stereographic'_eq_zero_iff (n := n) hv).mpr (mem_singleton_iff.mp h)
    rwa [(stereographic' n v).right_inv (by simp)] at this⟩
  left_inv x := Subtype.ext ((stereographic' n v).left_inv (by simpa using x.2.1))
  right_inv y := Subtype.ext ((stereographic' n v).right_inv (by simp))
  contMDiff_toFun := (ContMDiff.subtypeVal_comp_iff _ _).mp <|
    (contMDiffOn_of_mem_maximalAtlas (stereographic'_mem_maximalAtlas v)).comp_contMDiff
      contMDiff_subtype_val fun x ↦ by simpa using x.2.1
  contMDiff_invFun := (ContMDiff.subtypeVal_comp_iff _ _).mp
    ((isSmoothEmbedding_stereographic'_symm v).contMDiff.comp contMDiff_subtype_val)

/-- The diffeomorphism `TauCeti.stereographicPuncturedDiffeomorph v` is stereographic projection
from `v`. -/
@[simp]
theorem coe_stereographicPuncturedDiffeomorph_apply (v : sphere (0 : E) 1)
    (x : (⟨{v}ᶜ ∩ {-v}ᶜ, isOpen_compl_singleton.inter isOpen_compl_singleton⟩ :
        Opens (sphere (0 : E) 1))) :
    (stereographicPuncturedDiffeomorph v x :
        (⟨{0}ᶜ, isOpen_compl_singleton⟩ : Opens (EuclideanSpace ℝ (Fin n)))) =
      stereographic' n v x :=
  (rfl)

/-- The inverse of `TauCeti.stereographicPuncturedDiffeomorph v` is inverse stereographic
projection. -/
@[simp]
theorem coe_stereographicPuncturedDiffeomorph_symm_apply (v : sphere (0 : E) 1)
    (y : (⟨{0}ᶜ, isOpen_compl_singleton⟩ : Opens (EuclideanSpace ℝ (Fin n)))) :
    ((stereographicPuncturedDiffeomorph v).symm y : sphere (0 : E) 1) =
      (stereographic' n v).symm y :=
  (rfl)

end TauCeti

/-! ### Smooth embeddings of spheres induced by linear isometries -/

namespace LinearIsometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
  [Fact (finrank ℝ E = n + 1)]
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] {m : ℕ}
  [Fact (finrank ℝ F = m + 1)] (ι : F →ₗᵢ[ℝ] E)

/-- Stereographic projection commutes with a linear isometry `ι`: the projection from `ι v` of the
image of `x` is the image of the projection from `v` of `x`, read in the orthogonal complement
of `ι v` through `LinearIsometry.orthogonalComplementSingletonMap`. -/
theorem stereographic_unitSphereMap (v x : sphere (0 : F) 1) :
    stereographic (norm_eq_of_mem_sphere (ι.unitSphereMap v)) (ι.unitSphereMap x) =
      ι.orthogonalComplementSingletonMap (ι.coe_unitSphereMap_apply v).symm
        (stereographic (norm_eq_of_mem_sphere v) x) := by
  -- `ι` maps the line `ℝ ∙ v` onto the line `ℝ ∙ ι v`, so it commutes with the orthogonal
  -- projections onto the orthogonal complements of these lines.
  have key : (ℝ ∙ (ι v : E))ᗮ.starProjection (ι x) = ι ((ℝ ∙ (v : F))ᗮ.starProjection x) := by
    have h := ι.map_starProjection (ℝ ∙ (v : F)) x
    simp only [Submodule.map_span, Set.image_singleton, coe_toLinearMap] at h
    simp only [Submodule.starProjection_orthogonal_val, map_sub, h]
  apply Subtype.ext
  simp only [stereographic_apply, Submodule.coe_smul, Submodule.coe_orthogonalProjectionOnto_apply,
    coe_unitSphereMap_apply, coe_orthogonalComplementSingletonMap_apply, ι.inner_map_map, key,
    map_smul]

/-- The linear isometry of model Euclidean spaces through which the stereographic charts at `v`
and at `ι v` read the map `ι` of unit spheres: conjugate the restriction of `ι` to the orthogonal
complement of `v` by the orthonormal bases that `stereographic'` uses. -/
def stereographicModelMap (v : sphere (0 : F) 1) :
    EuclideanSpace ℝ (Fin m) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n) :=
  (OrthonormalBasis.fromOrthogonalSpanSingleton n
      (ne_zero_of_mem_unit_sphere (ι.unitSphereMap v))).repr.toLinearIsometry.comp
    ((ι.orthogonalComplementSingletonMap (ι.coe_unitSphereMap_apply v).symm).comp
      (OrthonormalBasis.fromOrthogonalSpanSingleton m
        (ne_zero_of_mem_unit_sphere v)).repr.symm.toLinearIsometry)

/-- In the stereographic charts at `v` and at `ι v`, the map of unit spheres induced by `ι` reads
as the linear isometry `LinearIsometry.stereographicModelMap` of the model spaces. -/
theorem stereographic'_unitSphereMap (v x : sphere (0 : F) 1) :
    stereographic' n (ι.unitSphereMap v) (ι.unitSphereMap x) =
      ι.stereographicModelMap v (stereographic' m v x) := by
  simp only [stereographic', stereographicModelMap, OpenPartialHomeomorph.trans_apply,
    Homeomorph.toOpenPartialHomeomorph_apply, LinearIsometryEquiv.coe_toHomeomorph, coe_comp,
    comp_apply, LinearIsometryEquiv.coe_toLinearIsometry, LinearIsometryEquiv.symm_apply_apply,
    stereographic_unitSphereMap]

variable {k : ℕ∞ω}

/-- The restriction of a linear isometry to the unit spheres is an immersion at every point: in
the preferred stereographic charts it is a linear isometry of model spaces, hence the inclusion
of a factor of a product decomposition of the target model. -/
theorem isImmersionAt_unitSphereMap (x : sphere (0 : F) 1) :
    IsImmersionAt (𝓡 m) (𝓡 n) k ι.unitSphereMap x := by
  refine (IsImmersionAtOfComplement.mk_of_continuousAt_of_extChartAt
    ι.continuous_unitSphereMap.continuousAt (ι.stereographicModelMap (-x)).prodOrthogonalRangeEquiv
    fun u _ ↦ ?_).isImmersionAt
  simp only [comp_apply, extChartAt_coe, extChartAt_coe_symm, modelWithCornersSelf_coe,
    modelWithCornersSelf_coe_symm, id_eq, TauCeti.chartAt_sphere, ← ι.unitSphereMap_neg,
    prodOrthogonalRangeEquiv_apply_zero]
  rw [ι.stereographic'_unitSphereMap (m := m), (stereographic' m (-x)).right_inv (by simp)]

/-- The restriction of a linear isometry to the unit spheres is a `C^k` immersion. -/
theorem isImmersion_unitSphereMap : IsImmersion (𝓡 m) (𝓡 n) k ι.unitSphereMap :=
  TauCeti.isImmersion_iff_forall_isImmersionAt.2 (ι.isImmersionAt_unitSphereMap)

/-- The restriction of a linear isometry to the unit spheres is a `C^k` smooth embedding. -/
theorem isSmoothEmbedding_unitSphereMap : IsSmoothEmbedding (𝓡 m) (𝓡 n) k ι.unitSphereMap :=
  ⟨ι.isImmersion_unitSphereMap, ι.isEmbedding_unitSphereMap⟩

end LinearIsometry

/-! ### Smooth families of linear isometries acting on the sphere -/

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
  [Fact (finrank ℝ E = n + 1)] {EM H M : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM]
  [TopologicalSpace H] {J : ModelWithCorners ℝ EM H} [TopologicalSpace M] [ChartedSpace H M]
  {k : ℕ∞ω} [IsManifold J k M]

/-- A family `R` of linear isometries depending smoothly on a real parameter acts smoothly on the
unit sphere: for smooth `t : M → ℝ` and `x : M → Sⁿ`, the map `p ↦ R (t p) (x p)` into the sphere
is smooth. -/
theorem contMDiff_unitSphereEquiv_apply {R : ℝ → E ≃ₗᵢ[ℝ] E}
    (hR : ContDiff ℝ k fun p : ℝ × E => R p.1 p.2) {t : M → ℝ} {x : M → sphere (0 : E) 1}
    (ht : ContMDiff J 𝓘(ℝ) k t) (hx : ContMDiff J (𝓡 n) k x) :
    ContMDiff J (𝓡 n) k fun p => (R (t p)).unitSphereEquiv (x p) := by
  have h : (fun p => (R (t p)).unitSphereEquiv (x p)) =
      Set.codRestrict (fun p => R (t p) (x p)) (sphere (0 : E) 1) fun p => by simp :=
    funext fun p => Subtype.ext (LinearIsometryEquiv.coe_unitSphereEquiv_apply _ _)
  rw [h]
  exact (hR.contMDiff.comp (ht.prodMk_space (contMDiff_coe_sphere.comp hx))).codRestrict_sphere _

end TauCeti

/-! ### The derivative of the circle exponential -/

namespace TauCeti

attribute [local instance] finrank_real_complex_fact'

/-- The derivative of `Circle.exp : ℝ → S¹` is injective at every point. -/
theorem injective_mfderiv_circleExp (t : ℝ) :
    Injective (mfderiv 𝓘(ℝ, ℝ) (𝓡 1) Circle.exp t : ℝ →L[ℝ] EuclideanSpace ℝ (Fin 1)) := by
  -- Composed with the inclusion `S¹ → ℂ`, it is the derivative `i exp (t i) ≠ 0` of `exp (t i)`.
  have he0 : mfderiv 𝓘(ℝ, ℝ) (𝓡 1) Circle.exp t ≠ 0 := by
    intro h0
    have hcoe : MDifferentiableAt (𝓡 1) 𝓘(ℝ, ℂ) (fun z : Circle => (z : ℂ)) (Circle.exp t) :=
      (contMDiff_coe_sphere (m := 1)).mdifferentiableAt one_ne_zero
    have hcomp := mfderiv_comp t hcoe
      ((contMDiff_circleExp (m := 1)).mdifferentiableAt one_ne_zero)
    rw [h0, ContinuousLinearMap.comp_zero, mfderiv_eq_fderiv] at hcomp
    have hd : HasDerivAt (fun s : ℝ => ((Circle.exp s : Circle) : ℂ))
        (Complex.exp (t * Complex.I) * Complex.I) t := by
      simp only [Circle.coe_exp]
      simpa using ((Complex.ofRealCLM.hasDerivAt (x := t)).mul_const Complex.I).cexp
    have h1 := congrArg (fun L => L (1 : ℝ)) hcomp
    -- `fromTangentSpace` identifies the tangent spaces of `ℝ` and `ℂ` with `ℝ` and `ℂ` by the
    -- identity map, and has no simp lemmas, so `change` unfolds it.
    change fderiv ℝ (fun s : ℝ => ((Circle.exp s : Circle) : ℂ)) t 1 = 0 at h1
    rw [hd.hasFDerivAt.fderiv] at h1
    simp [Complex.exp_ne_zero] at h1
  set e : ℝ →L[ℝ] EuclideanSpace ℝ (Fin 1) := mfderiv 𝓘(ℝ, ℝ) (𝓡 1) Circle.exp t
  have hne : e 1 ≠ 0 := fun h0 => he0 (ContinuousLinearMap.ext_ring (by rw [h0]; rfl))
  refine (injective_iff_map_eq_zero e).mpr fun s hs => ?_
  have hs' : s • e 1 = 0 := by rw [← map_smul, smul_eq_mul, mul_one]; exact hs
  exact (smul_eq_zero.mp hs').resolve_right hne

/-- The derivative of `Circle.exp : ℝ → S¹` is surjective at every point, both spaces being
one-dimensional. -/
theorem surjective_mfderiv_circleExp (t : ℝ) :
    Surjective (mfderiv 𝓘(ℝ, ℝ) (𝓡 1) Circle.exp t : ℝ →L[ℝ] EuclideanSpace ℝ (Fin 1)) :=
  (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (K := ℝ) (V := ℝ)
    (V₂ := EuclideanSpace ℝ (Fin 1)) (by simp)).mp (injective_mfderiv_circleExp t)

/-- The argument is smooth on the circle away from `-1`. -/
theorem contMDiffAt_circle_arg {n : WithTop ℕ∞} {z : Circle} (hz : |Complex.arg z| < Real.pi) :
    ContMDiffAt (𝓡 1) 𝓘(ℝ, ℝ) n (fun w : Circle => Complex.arg w) z := by
  have hslit : (z : ℂ) ∈ Complex.slitPlane :=
    Complex.mem_slitPlane_iff_arg.2 ⟨fun h => by simp [h, abs_of_pos Real.pi_pos] at hz,
      Circle.coe_ne_zero z⟩
  have hc : ContMDiff (𝓡 1) 𝓘(ℝ, ℂ) n (fun w : Circle => (w : ℂ)) := contMDiff_coe_sphere
  exact (Complex.contDiffAt_arg hslit).contMDiffAt.comp z hc.contMDiffAt

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The chain rule for a map `f` of the circle read along `Circle.exp`: the derivative of
`s ↦ f (exp (s i))` at `t`, as a map out of `ℝ`, is the derivative of `f` at `exp (t i)` after that
of `Circle.exp` at `t`. -/
theorem toSpanSingleton_deriv_comp_circleExp {f : Circle → V} {t : ℝ}
    (hf : MDifferentiableAt (𝓡 1) 𝓘(ℝ, V) f (Circle.exp t)) :
    ContinuousLinearMap.toSpanSingleton ℝ (deriv (f ∘ Circle.exp) t) =
      (mfderiv (𝓡 1) 𝓘(ℝ, V) f (Circle.exp t) : EuclideanSpace ℝ (Fin 1) →L[ℝ] V).comp
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 1) Circle.exp t) := by
  have hexp := (contMDiff_circleExp (m := 1)).mdifferentiableAt one_ne_zero (x := t)
  have hγ : DifferentiableAt ℝ (f ∘ Circle.exp) t :=
    mdifferentiableAt_iff_differentiableAt.mp (hf.comp t hexp)
  have hcomp := mfderiv_comp t hf hexp
  rw [mfderiv_eq_fderiv, hγ.hasDerivAt.hasFDerivAt.fderiv] at hcomp
  exact hcomp

/-- The chain rule for a map `f` of the circle into a manifold, read along `Circle.exp` in a chart
`φ` of the maximal atlas at `f (exp (t i))`: the derivative of `s ↦ φ (f (exp (s i)))` at `t`, as a
map out of `ℝ`, is the derivative of `Circle.exp` at `t`, followed by those of `f` and of `φ`. -/
theorem toSpanSingleton_deriv_chart_comp_circleExp {M : Type*} [TopologicalSpace M]
    [ChartedSpace V M] {n : WithTop ℕ∞} (hn : n ≠ 0) {f : Circle → M} {t : ℝ}
    (hf : MDifferentiableAt (𝓡 1) 𝓘(ℝ, V) f (Circle.exp t)) {φ : OpenPartialHomeomorph M V}
    (hφ : φ ∈ IsManifold.maximalAtlas 𝓘(ℝ, V) n M) (hft : f (Circle.exp t) ∈ φ.source) :
    ContinuousLinearMap.toSpanSingleton ℝ (deriv (fun s => φ (f (Circle.exp s))) t) =
      (mfderiv 𝓘(ℝ, V) 𝓘(ℝ, V) φ (f (Circle.exp t))).comp
        ((mfderiv (𝓡 1) 𝓘(ℝ, V) f (Circle.exp t)).comp (mfderiv 𝓘(ℝ, ℝ) (𝓡 1) Circle.exp t)) := by
  have hφd : MDifferentiableAt 𝓘(ℝ, V) 𝓘(ℝ, V) φ (f (Circle.exp t)) :=
    (contMDiffAt_of_mem_maximalAtlas hφ hft).mdifferentiableAt hn
  have h := toSpanSingleton_deriv_comp_circleExp (f := φ ∘ f) (t := t) (hφd.comp _ hf)
  rw [mfderiv_comp _ hφd hf] at h
  exact h

section ChartAlongCircleExp

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {M : Type*} [TopologicalSpace M]
  [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

/-- A smooth map of the circle, read in a chart along `Circle.exp` on an arc, is smooth. -/
theorem contDiffOn_chartAt_comp_circleExp {f : Circle → M} {r : ℝ} (p : M)
    (hf : ContMDiff (𝓡 1) 𝓘(ℝ, E) ∞ f)
    (hfφ : ∀ t, |t| < r → f (Circle.exp t) ∈ (chartAt E p).source) :
    ContDiffOn ℝ ∞ (fun t => chartAt E p (f (Circle.exp t))) (Ioo (-r) r) :=
  contMDiffOn_iff_contDiffOn.1 ((contMDiffOn_chart (x := p)).comp
    (hf.comp contMDiff_circleExp).contMDiffOn fun t ht => hfφ t (abs_lt.2 ht))

/-- If two maps `K` and `L` of the circle, differentiable at `1`, agree to first order there, then
read in a chart at `K 1` along `Circle.exp` they have the same velocity at `0`. -/
theorem deriv_chartAt_comp_circleExp_eq {K L : Circle → M}
    (hK : MDifferentiableAt (𝓡 1) 𝓘(ℝ, E) K 1) (hL : MDifferentiableAt (𝓡 1) 𝓘(ℝ, E) L 1)
    (h₀ : K 1 = L 1) (h₁ : mfderiv (𝓡 1) 𝓘(ℝ, E) K 1 = mfderiv (𝓡 1) 𝓘(ℝ, E) L 1) :
    deriv (fun t => chartAt E (K 1) (K (Circle.exp t))) 0 =
      deriv (fun t => chartAt E (K 1) (L (Circle.exp t))) 0 := by
  have hφ : chartAt E (K 1) ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M :=
    IsManifold.chart_mem_maximalAtlas _
  have hpφ : K 1 ∈ (chartAt E (K 1)).source := mem_chart_source E _
  rw [← Circle.exp_zero] at hK hL
  have hvK := toSpanSingleton_deriv_chart_comp_circleExp (by simp) hK hφ
    (by rwa [Circle.exp_zero])
  have hvL := toSpanSingleton_deriv_chart_comp_circleExp (by simp) hL hφ
    (by rwa [Circle.exp_zero, ← h₀])
  rw [Circle.exp_zero] at hvK hvL
  rw [← h₁, ← h₀] at hvL
  simpa using congrArg (fun T => T 1) (hvK.trans hvL.symm)

/-- A map of the circle which is an immersion at `1`, read in a chart at its value at `1` along
`Circle.exp`, has nonzero velocity at `0`. -/
theorem deriv_chartAt_comp_circleExp_ne_zero {f : Circle → M}
    (hf : IsImmersionAt (𝓡 1) 𝓘(ℝ, E) ∞ f 1) :
    deriv (fun t => chartAt E (f 1) (f (Circle.exp t))) 0 ≠ 0 := fun h0 => by
  have hφ : chartAt E (f 1) ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M :=
    IsManifold.chart_mem_maximalAtlas _
  have hpφ : f 1 ∈ (chartAt E (f 1)).source := mem_chart_source E _
  have hv := toSpanSingleton_deriv_chart_comp_circleExp (by simp)
    (by rw [Circle.exp_zero]; exact hf.contMDiffAt.mdifferentiableAt (by simp)) hφ
    (by rwa [Circle.exp_zero])
  rw [Circle.exp_zero] at hv
  have h1 : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (chartAt E (f 1)) (f 1)
      (mfderiv (𝓡 1) 𝓘(ℝ, E) f 1 (mfderiv 𝓘(ℝ, ℝ) (𝓡 1) Circle.exp 0 (1 : ℝ))) = 0 := by
    have h := (congrArg (fun T => T 1) hv).symm
    simp only [ContinuousLinearMap.toSpanSingleton_apply, one_smul] at h
    exact h.trans h0
  have hφi := (((chartAt E (f 1)).isLocalDiffeomorphAt_of_mem_maximalAtlas hφ hpφ).isDiffImmersionAt
    (by simp)).mfderiv_injective
  have hfi := hf.mfderiv_injective (by simp)
  exact one_ne_zero (α := ℝ) (injective_mfderiv_circleExp 0
    ((hfi ((hφi (h1.trans (map_zero _).symm)).trans (map_zero _).symm)).trans
      (map_zero _).symm))

end ChartAlongCircleExp

/-- For a `C¹` immersion `f` of the circle, the derivative of `t ↦ f (exp (t i))` is nonzero and
spans the range of the derivative of `f`. -/
theorem deriv_comp_circleExp_ne_zero_and_range_mfderiv {f : Circle → V}
    (hf : ContMDiff (𝓡 1) 𝓘(ℝ, V) 1 f) (himm : ∀ z, Injective (mfderiv (𝓡 1) 𝓘(ℝ, V) f z))
    (t : ℝ) :
    deriv (f ∘ Circle.exp) t ≠ 0 ∧
      (mfderiv (𝓡 1) 𝓘(ℝ, V) f (Circle.exp t) : EuclideanSpace ℝ (Fin 1) →L[ℝ] V).range =
        ℝ ∙ deriv (f ∘ Circle.exp) t := by
  set D : EuclideanSpace ℝ (Fin 1) →L[ℝ] V := mfderiv (𝓡 1) 𝓘(ℝ, V) f (Circle.exp t)
  set e : ℝ →L[ℝ] EuclideanSpace ℝ (Fin 1) := mfderiv 𝓘(ℝ, ℝ) (𝓡 1) Circle.exp t
  have he_inj : Injective e := injective_mfderiv_circleExp t
  have he_surj : Surjective e := surjective_mfderiv_circleExp t
  have hD_inj : Injective D := himm _
  have hD : ContinuousLinearMap.toSpanSingleton ℝ (deriv (f ∘ Circle.exp) t) = D.comp e :=
    toSpanSingleton_deriv_comp_circleExp (hf.mdifferentiableAt one_ne_zero)
  have hDe : D (e 1) = deriv (f ∘ Circle.exp) t := by
    simpa using (congrArg (fun L => L 1) hD).symm
  refine ⟨fun h0 => one_ne_zero (he_inj (hD_inj (by rw [hDe, h0, map_zero, map_zero]))), ?_⟩
  rw [← LinearMap.range_toSpanSingleton]
  have := congrArg (fun L : ℝ →L[ℝ] V => (L : ℝ →ₗ[ℝ] V).range) hD
  simp only [ContinuousLinearMap.toLinearMap_comp,
    LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_eq_top.mpr he_surj)] at this
  exact this.symm

/-- **The velocity along `Circle.exp` determines the derivative**, for maps of the circle into a
real normed space. -/
theorem mfderiv_eq_of_deriv_comp_circleExp_eq {f g : Circle → V} {t : ℝ}
    (hf : MDifferentiableAt (𝓡 1) 𝓘(ℝ, V) f (Circle.exp t))
    (hg : MDifferentiableAt (𝓡 1) 𝓘(ℝ, V) g (Circle.exp t))
    (h : deriv (f ∘ Circle.exp) t = deriv (g ∘ Circle.exp) t) :
    mfderiv (𝓡 1) 𝓘(ℝ, V) f (Circle.exp t) = mfderiv (𝓡 1) 𝓘(ℝ, V) g (Circle.exp t) := by
  have hD := (toSpanSingleton_deriv_comp_circleExp hf).symm.trans
    (h ▸ toSpanSingleton_deriv_comp_circleExp hg)
  refine ContinuousLinearMap.ext fun τ => ?_
  obtain ⟨s, rfl⟩ := surjective_mfderiv_circleExp t τ
  exact congrArg (fun L : ℝ →L[ℝ] V => L s) hD

/-- A map `f` of the circle, differentiable at `exp (t i)`, has injective derivative there as soon
as the curve `s ↦ f (exp (s i))` has nonzero derivative at `t`. -/
theorem injective_mfderiv_of_deriv_comp_circleExp_ne_zero {f : Circle → V} {t : ℝ}
    (hf : MDifferentiableAt (𝓡 1) 𝓘(ℝ, V) f (Circle.exp t))
    (ht : deriv (f ∘ Circle.exp) t ≠ 0) :
    Injective (mfderiv (𝓡 1) 𝓘(ℝ, V) f (Circle.exp t)) := by
  set D : EuclideanSpace ℝ (Fin 1) →L[ℝ] V := mfderiv (𝓡 1) 𝓘(ℝ, V) f (Circle.exp t)
  set e : ℝ →L[ℝ] EuclideanSpace ℝ (Fin 1) := mfderiv 𝓘(ℝ, ℝ) (𝓡 1) Circle.exp t
  have hD : ContinuousLinearMap.toSpanSingleton ℝ (deriv (f ∘ Circle.exp) t) = D.comp e :=
    toSpanSingleton_deriv_comp_circleExp hf
  refine (injective_iff_map_eq_zero D).mpr fun v hv => ?_
  -- Every tangent vector at `exp (t i)` is `e s` for some `s : ℝ`, and the chain rule sends it to
  -- `s` times the derivative of the curve.
  obtain ⟨s, rfl⟩ : ∃ s : ℝ, e s = v := surjective_mfderiv_circleExp t v
  have hs : s • deriv (f ∘ Circle.exp) t = 0 := by
    simpa [hv] using congrArg (fun L : ℝ →L[ℝ] V => L s) hD
  rw [(smul_eq_zero.mp hs).resolve_right ht, map_zero]

/-! ### Loops in a sphere read along `Circle.exp` -/

section SphereLoop

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
  [Fact (finrank ℝ E = n + 1)] {f g : Circle → sphere (0 : E) 1} {t : ℝ}

/-- The chain rule for a loop `f` in a sphere read along `Circle.exp` and in the ambient space:
`s` times the derivative of `r ↦ f (exp (r i))` at `t` is the derivative of `f` at `exp (t i)`
applied to the derivative of `Circle.exp` at `t` in the direction `s`, read in the ambient space
through the inclusion of the sphere. -/
theorem smul_deriv_coe_comp_circleExp
    (hf : MDifferentiableAt (𝓡 1) (𝓡 n) f (Circle.exp t)) (s : ℝ) :
    s • deriv (fun r => (f (Circle.exp r) : E)) t =
      mvfderiv (𝓡 n) ((↑) : sphere (0 : E) 1 → E) (f (Circle.exp t))
        (mfderiv (𝓡 1) (𝓡 n) f (Circle.exp t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 1) Circle.exp t s)) := by
  have hc : MDifferentiableAt (𝓡 n) 𝓘(ℝ, E) ((↑) : sphere (0 : E) 1 → E) (f (Circle.exp t)) :=
    (contMDiff_coe_sphere (m := 1)).mdifferentiableAt one_ne_zero
  have h := DFunLike.congr_fun (toSpanSingleton_deriv_comp_circleExp (hc.comp _ hf)) s
  rw [ContinuousLinearMap.toSpanSingleton_apply] at h
  refine h.trans ?_
  rw [← mvfderiv_comp_apply _ hc hf, mvfderiv_apply_eq_mfderiv_apply]
  -- Both sides apply the derivative of `(↑) ∘ f` to the same tangent vector.
  rfl

/-- The velocity of a loop in a sphere, read along `Circle.exp` in the ambient space, is tangent to
the sphere: it is orthogonal to the point of the loop. -/
theorem inner_deriv_coe_comp_circleExp_eq_zero
    (hf : MDifferentiableAt (𝓡 1) (𝓡 n) f (Circle.exp t)) :
    ⟪(f (Circle.exp t) : E), deriv (fun s => (f (Circle.exp s) : E)) t⟫_ℝ = 0 := by
  rw [← one_smul ℝ (deriv _ t), smul_deriv_coe_comp_circleExp hf]
  refine Submodule.inner_right_of_mem_orthogonal (Submodule.mem_span_singleton_self _) ?_
  rw [← range_mvfderiv_subtypeVal (n := n)]
  exact LinearMap.mem_range_self _ _

/-- A loop in a sphere with injective derivative at `exp (t i)`, read along `Circle.exp` in the
ambient space, has nonzero velocity at `t`. -/
theorem deriv_coe_comp_circleExp_ne_zero
    (hf : MDifferentiableAt (𝓡 1) (𝓡 n) f (Circle.exp t))
    (hinj : Injective (mfderiv (𝓡 1) (𝓡 n) f (Circle.exp t))) :
    deriv (fun s => (f (Circle.exp s) : E)) t ≠ 0 := by
  intro h0
  have h := smul_deriv_coe_comp_circleExp hf 1
  rw [h0, smul_zero] at h
  -- The derivatives of the inclusion, of `f` and of `Circle.exp` are injective, so the
  -- composite cannot kill `1`.
  have h₁ := injective_mvfderiv_subtypeVal_sphere _ (h.symm.trans (map_zero _).symm)
  have h₂ := hinj (h₁.trans (map_zero _).symm)
  have h₃ : (1 : ℝ) = 0 := injective_mfderiv_circleExp t (h₂.trans (map_zero _).symm)
  exact one_ne_zero h₃

/-- **The velocity along `Circle.exp` determines the derivative.** Two loops in a sphere which take
the same value at `exp (t i)`, and whose velocities at `t` read along `Circle.exp` in the ambient
space agree, have the same derivative at `exp (t i)`. -/
theorem mfderiv_eq_of_deriv_coe_comp_circleExp_eq
    (hf : MDifferentiableAt (𝓡 1) (𝓡 n) f (Circle.exp t))
    (hg : MDifferentiableAt (𝓡 1) (𝓡 n) g (Circle.exp t))
    (h₀ : f (Circle.exp t) = g (Circle.exp t))
    (h₁ : deriv (fun s => (f (Circle.exp s) : E)) t = deriv (fun s => (g (Circle.exp s) : E)) t) :
    mfderiv (𝓡 1) (𝓡 n) f (Circle.exp t) = mfderiv (𝓡 1) (𝓡 n) g (Circle.exp t) := by
  -- Every tangent vector at `exp (t i)` is the derivative of `Circle.exp` at `t` in some
  -- direction `s`.
  refine ContinuousLinearMap.ext fun τ => ?_
  obtain ⟨s, rfl⟩ : ∃ s : ℝ,
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 1) Circle.exp t : ℝ →L[ℝ] EuclideanSpace ℝ (Fin 1)) s = τ :=
    surjective_mfderiv_circleExp t τ
  have h := (smul_deriv_coe_comp_circleExp hf s).symm.trans
    ((congrArg (s • ·) h₁).trans (smul_deriv_coe_comp_circleExp hg s))
  rw [← h₀] at h
  exact injective_mvfderiv_subtypeVal_sphere _ h

/-- **The derivative determines the velocity along `Circle.exp`.** Two loops in a sphere which take
the same value and have the same derivative at `exp (t i)` have the same velocity at `t`, read along
`Circle.exp` in the ambient space. This is the converse of
`TauCeti.mfderiv_eq_of_deriv_coe_comp_circleExp_eq`. -/
theorem deriv_coe_comp_circleExp_eq_of_mfderiv_eq
    (hf : MDifferentiableAt (𝓡 1) (𝓡 n) f (Circle.exp t))
    (hg : MDifferentiableAt (𝓡 1) (𝓡 n) g (Circle.exp t))
    (h₀ : f (Circle.exp t) = g (Circle.exp t))
    (h₁ : mfderiv (𝓡 1) (𝓡 n) f (Circle.exp t) = mfderiv (𝓡 1) (𝓡 n) g (Circle.exp t)) :
    deriv (fun s => (f (Circle.exp s) : E)) t = deriv (fun s => (g (Circle.exp s) : E)) t := by
  have e₁ := smul_deriv_coe_comp_circleExp hf 1
  have e₂ := smul_deriv_coe_comp_circleExp hg 1
  rw [one_smul] at e₁ e₂
  rw [e₁, e₂]
  congr 1
  · rw [h₀]
  · exact DFunLike.congr_fun h₁ _

end SphereLoop

/-! ### Maps of the cylinder over the circle, read along `Circle.exp` -/

section CircleCylinder

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
  [Fact (finrank ℝ E = n + 1)]

/-- **The first order of a map of the cylinder along a line.** Two maps `f` and `g` of the
cylinder `S¹ × ℝ` into `Sⁿ × ℝ`, differentiable at `(exp (θ i), t)`, which agree on the whole line
`{exp (θ i)} × ℝ`, and whose slices `θ' ↦ f (exp (θ' i), t)` and `θ' ↦ g (exp (θ' i), t)` have the
same velocity at `θ` in `E × ℝ`, have the same derivative at `(exp (θ i), t)`. -/
theorem mfderiv_eq_of_deriv_comp_circleExp_eq_prod {f g : Circle × ℝ → sphere (0 : E) 1 × ℝ}
    {θ t : ℝ} (hf : MDifferentiableAt ((𝓡 1).prod 𝓘(ℝ)) ((𝓡 n).prod 𝓘(ℝ)) f (Circle.exp θ, t))
    (hg : MDifferentiableAt ((𝓡 1).prod 𝓘(ℝ)) ((𝓡 n).prod 𝓘(ℝ)) g (Circle.exp θ, t))
    (hline : ∀ s, f (Circle.exp θ, s) = g (Circle.exp θ, s))
    (h₁ : deriv (fun θ' => ((f (Circle.exp θ', t)).1 : E)) θ =
      deriv (fun θ' => ((g (Circle.exp θ', t)).1 : E)) θ)
    (h₂ : deriv (fun θ' => (f (Circle.exp θ', t)).2) θ =
      deriv (fun θ' => (g (Circle.exp θ', t)).2) θ) :
    mfderiv ((𝓡 1).prod 𝓘(ℝ)) ((𝓡 n).prod 𝓘(ℝ)) f (Circle.exp θ, t) =
      mfderiv ((𝓡 1).prod 𝓘(ℝ)) ((𝓡 n).prod 𝓘(ℝ)) g (Circle.exp θ, t) := by
  have hslice {k : Circle × ℝ → sphere (0 : E) 1 × ℝ}
      (hk : MDifferentiableAt ((𝓡 1).prod 𝓘(ℝ)) ((𝓡 n).prod 𝓘(ℝ)) k (Circle.exp θ, t)) :
      MDifferentiableAt (𝓡 1) ((𝓡 n).prod 𝓘(ℝ)) (fun z => k (z, t)) (Circle.exp θ) :=
    hk.comp (Circle.exp θ) (mdifferentiableAt_id.prodMk mdifferentiableAt_const)
  have hf₁ := hslice hf
  have hg₁ := hslice hg
  rw [mfderiv_prod_eq_add_comp hf, mfderiv_prod_eq_add_comp hg]
  congr 2
  · -- The slices at time `t` agree to first order: compare their two components.
    change mfderiv (𝓡 1) ((𝓡 n).prod 𝓘(ℝ)) (fun z => ((f (z, t)).1, (f (z, t)).2)) _ =
      mfderiv (𝓡 1) ((𝓡 n).prod 𝓘(ℝ)) (fun z => ((g (z, t)).1, (g (z, t)).2)) _
    rw [mfderiv_prodMk hf₁.fst hf₁.snd, mfderiv_prodMk hg₁.fst hg₁.snd]
    congr 1
    · exact mfderiv_eq_of_deriv_coe_comp_circleExp_eq hf₁.fst hg₁.fst
        (congrArg Prod.fst (hline t)) h₁
    · exact mfderiv_eq_of_deriv_comp_circleExp_eq hf₁.snd hg₁.snd h₂
  · -- On the line `{exp (θ i)} × ℝ` the two maps agree.
    rw [show (fun z : ℝ => f (Circle.exp θ, z)) = fun z => g (Circle.exp θ, z) from funext hline]

/-- A map `Γ` of the cylinder `S¹ × ℝ` into `Sⁿ × ℝ` which is the line `s ↦ (y, s)` over
`exp (θ i)`, and has injective derivative at `(exp (θ i), t)`, has a slice
`θ' ↦ Γ (exp (θ' i), t)` whose sphere component has nonzero velocity at `θ`. Otherwise the
derivative of `Γ` would kill a vector `(u, -c)`, with `u` tangent to the circle and `c` the time
component of the slice velocity. -/
theorem deriv_coe_fst_comp_circleExp_ne_zero {Γ : Circle × ℝ → sphere (0 : E) 1 × ℝ}
    {θ t : ℝ} {y : sphere (0 : E) 1}
    (hΓ : MDifferentiableAt ((𝓡 1).prod 𝓘(ℝ)) ((𝓡 n).prod 𝓘(ℝ)) Γ (Circle.exp θ, t))
    (hinj : Injective (mfderiv ((𝓡 1).prod 𝓘(ℝ)) ((𝓡 n).prod 𝓘(ℝ)) Γ (Circle.exp θ, t)))
    (hline : ∀ s, Γ (Circle.exp θ, s) = (y, s)) :
    deriv (fun θ' => ((Γ (Circle.exp θ', t)).1 : E)) θ ≠ 0 := by
  intro h0
  set u : EuclideanSpace ℝ (Fin 1) := mfderiv 𝓘(ℝ, ℝ) (𝓡 1) Circle.exp θ (1 : ℝ)
  have hu : u ≠ 0 := fun h =>
    one_ne_zero (show (1 : ℝ) = 0 from injective_mfderiv_circleExp θ (h.trans (map_zero _).symm))
  have hΓ₁ : MDifferentiableAt (𝓡 1) ((𝓡 n).prod 𝓘(ℝ)) (fun z => Γ (z, t)) (Circle.exp θ) :=
    hΓ.comp (Circle.exp θ) (mdifferentiableAt_id.prodMk mdifferentiableAt_const)
  -- The sphere component of the slice has zero derivative in the direction `u`.
  have h₁ : mfderiv (𝓡 1) (𝓡 n) (fun z => (Γ (z, t)).1) (Circle.exp θ) u = 0 := by
    have h := smul_deriv_coe_comp_circleExp hΓ₁.fst 1
    rw [h0, smul_zero] at h
    exact injective_mvfderiv_subtypeVal_sphere _ (h.symm.trans (map_zero _).symm)
  set c : ℝ := mfderiv (𝓡 1) 𝓘(ℝ) (fun z => (Γ (z, t)).2) (Circle.exp θ) u
  set w : TangentSpace ((𝓡 1).prod 𝓘(ℝ)) (Circle.exp θ, t) := (u, -c)
  -- The two components of the derivative of `Γ` in the direction `w` vanish.
  have ha : mfderiv ((𝓡 1).prod 𝓘(ℝ)) (𝓡 n) (fun q => (Γ q).1) (Circle.exp θ, t) w = 0 := by
    rw [mfderiv_prod_eq_add_apply hΓ.fst]
    have hs : (fun s : ℝ => (Γ (Circle.exp θ, s)).1) = fun _ => y :=
      funext fun s => by rw [hline]
    rw [hs, mfderiv_const]
    exact (add_zero _).trans h₁
  have hb : mfderiv ((𝓡 1).prod 𝓘(ℝ)) 𝓘(ℝ) (fun q => (Γ q).2) (Circle.exp θ, t) w = 0 := by
    rw [mfderiv_prod_eq_add_apply hΓ.snd]
    have hs : (fun s : ℝ => (Γ (Circle.exp θ, s)).2) = fun s => s :=
      funext fun s => by rw [hline]
    have hid : mfderiv 𝓘(ℝ) 𝓘(ℝ) (fun s : ℝ => (Γ (Circle.exp θ, s)).2) t =
        ContinuousLinearMap.id ℝ ℝ := by
      rw [hs]
      exact mfderiv_id
    rw [hid]
    exact add_neg_cancel c
  have hkey : mfderiv ((𝓡 1).prod 𝓘(ℝ)) ((𝓡 n).prod 𝓘(ℝ)) Γ (Circle.exp θ, t) w = 0 := by
    have hdecomp := mfderiv_prodMk hΓ.fst hΓ.snd
    rw [hdecomp]
    exact Prod.ext ha hb
  exact hu (congrArg Prod.fst (hinj (hkey.trans (map_zero _).symm)) :)

/-- A smooth real function on the circle, of absolute value at most `δ`, which vanishes at
`exp (θ₀ i)` and has velocity `1` there along `Circle.exp`: `κ arctan (sin (θ - θ₀) / κ)` with
`κ = δ / 2`. -/
theorem exists_contMDiff_circle_hasDerivAt (θ₀ : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ h : Circle → ℝ, ContMDiff (𝓡 1) 𝓘(ℝ) ∞ h ∧ h (Circle.exp θ₀) = 0 ∧
      HasDerivAt (fun θ => h (Circle.exp θ)) 1 θ₀ ∧ ∀ z, |h z| ≤ δ := by
  set κ := δ / 2
  have hκ : 0 < κ := half_pos hδ
  set g : ℂ → ℝ := fun w => κ * Real.arctan (w.im / κ)
  have hg : ContDiff ℝ ∞ g :=
    contDiff_const.mul (Real.contDiff_arctan.comp (Complex.imCLM.contDiff.div_const κ))
  have hc : ContMDiff (𝓡 1) 𝓘(ℝ, ℂ) ∞ fun z : Circle => (((Circle.exp θ₀)⁻¹ * z : Circle) : ℂ) :=
    contMDiff_coe_sphere.comp contMDiff_mul_left
  have he (θ : ℝ) : g (((Circle.exp θ₀)⁻¹ * Circle.exp θ : Circle) : ℂ) =
      κ * Real.arctan (Real.sin (θ - θ₀) / κ) := by
    simp only [g, inv_mul_eq_div, ← Circle.exp_sub, Circle.coe_exp, Complex.exp_ofReal_mul_I_im]
  refine ⟨fun z => g (((Circle.exp θ₀)⁻¹ * z : Circle) : ℂ), hg.contMDiff.comp hc, ?_, ?_,
    fun z => ?_⟩
  · simp [g]
  · have hs : HasDerivAt (fun θ => Real.sin (θ - θ₀) / κ) (Real.cos (θ₀ - θ₀) * 1 / κ) θ₀ :=
      ((Real.hasDerivAt_sin _).comp θ₀ ((hasDerivAt_id θ₀).sub_const θ₀)).div_const κ
    have hd : HasDerivAt (fun θ => κ * Real.arctan (Real.sin (θ - θ₀) / κ)) 1 θ₀ := by
      convert ((Real.hasDerivAt_arctan _).comp θ₀ hs).const_mul κ using 1
      · rfl
      · rw [sub_self, Real.sin_zero, Real.cos_zero]
        field_simp
        ring
    exact hd.congr_of_eventuallyEq (Filter.Eventually.of_forall he)
  · set x := (((Circle.exp θ₀)⁻¹ * z : Circle) : ℂ).im / κ
    have hx : |Real.arctan x| ≤ 2 := (abs_lt.2 ⟨Real.neg_pi_div_two_lt_arctan x,
      Real.arctan_lt_pi_div_two x⟩).le.trans (by linarith [Real.pi_le_four])
    calc |g (((Circle.exp θ₀)⁻¹ * z : Circle) : ℂ)| = κ * |Real.arctan x| := by
          simp only [g, abs_mul, abs_of_pos hκ, x]
      _ ≤ κ * 2 := mul_le_mul_of_nonneg_left hx hκ.le
      _ = δ := by simp only [κ]; ring

end CircleCylinder

/-! ### Points omitted by differentiable loops -/

/-- A differentiable path `ℝ → Sⁿ` in a sphere of dimension at least two omits a point.
No immersion or injectivity assumption is needed. -/
theorem exists_notMem_range_real_sphere
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {n : ℕ} [Fact (finrank ℝ E = n + 1)] (hn : 2 ≤ n)
    {f : ℝ → sphere (0 : E) 1} (hf : MDifferentiable 𝓘(ℝ) (𝓡 n) f) :
    ∃ p : sphere (0 : E) 1, p ∉ range f := by
  -- The cone over the path is the image of a differentiable map from a plane.
  have hγ : Differentiable ℝ (fun t => (f t : E)) :=
    mdifferentiable_iff_differentiable.mp <|
      ((contMDiff_coe_sphere (m := 1)).mdifferentiable one_ne_zero).comp hf
  let F : ℝ × ℝ → E := fun q => q.1 • (f q.2 : E)
  have hF : Differentiable ℝ F := differentiable_fst.smul (hγ.comp differentiable_snd)
  obtain ⟨a, ha⟩ := (hF.dense_compl_range_of_finrank_lt_finrank (by
    rw [Module.finrank_prod, Module.finrank_self, (Fact.out : finrank ℝ E = n + 1)]
    omega)).nonempty
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact ha ⟨(0, 0), by simp [F]⟩
  have hnorm : ‖‖a‖⁻¹ • a‖ = 1 := norm_smul_inv_norm ha0
  refine ⟨⟨‖a‖⁻¹ • a, mem_sphere_zero_iff_norm.mpr hnorm⟩, ?_⟩
  rintro ⟨t, ht⟩
  refine ha ⟨(‖a‖, t), ?_⟩
  simp only [F, ht, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr ha0), one_smul]

/-- A differentiable loop in a sphere of dimension at least two omits a point.
No immersion or injectivity assumption is needed. -/
theorem exists_notMem_range_circle_sphere
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {n : ℕ} [Fact (finrank ℝ E = n + 1)] (hn : 2 ≤ n)
    {f : Circle → sphere (0 : E) 1} (hf : MDifferentiable (𝓡 1) (𝓡 n) f) :
    ∃ p : sphere (0 : E) 1, p ∉ range f := by
  obtain ⟨p, hp⟩ := exists_notMem_range_real_sphere hn
    (hf.comp ((contMDiff_circleExp (m := 1)).mdifferentiable one_ne_zero))
  rw [range_comp, Circle.exp_surjective.range_eq, image_univ] at hp
  exact ⟨p, hp⟩

/-! ### The unit sphere in the punctured space -/

section Punctured

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {m : ℕ∞ω}

/-- The radial projection `x ↦ x / ‖x‖` is smooth on the punctured space `E \ {0}`, an open subset
of `E`. -/
theorem contMDiff_normalize_compl_zero :
    ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) m
      (fun x : (⟨{0}ᶜ, isOpen_compl_singleton⟩ : Opens E) ↦ NormedSpace.normalize (x : E)) := by
  simp only [NormedSpace.normalize]
  exact fun x ↦ (((contDiffAt_norm ℝ x.2).inv (norm_ne_zero_iff.2 x.2)).contMDiffAt.comp x
    contMDiff_subtype_val.contMDiffAt).smul contMDiff_subtype_val.contMDiffAt

variable {n : ℕ} [Fact (finrank ℝ E = n + 1)]

/-- The inclusion of the unit sphere of `E` into the punctured space `E \ {0}`, an open subset of
`E`, is smooth. -/
theorem contMDiff_coe_sphere_compl_zero :
    ContMDiff (𝓡 n) 𝓘(ℝ, E) m (fun x : sphere (0 : E) 1 ↦
      (⟨x, ne_zero_of_mem_unit_sphere x⟩ : (⟨{0}ᶜ, isOpen_compl_singleton⟩ : Opens E))) := by
  rw [← TauCeti.ContMDiff.subtypeVal_comp_iff]
  exact contMDiff_coe_sphere

/-- The radial projection `x ↦ x / ‖x‖` of the punctured space `E \ {0}`, an open subset of `E`,
onto the unit sphere is smooth. -/
theorem contMDiff_normalize_sphere :
    ContMDiff 𝓘(ℝ, E) (𝓡 n) m (fun x : (⟨{0}ᶜ, isOpen_compl_singleton⟩ : Opens E) ↦
      (⟨NormedSpace.normalize (x : E), mem_sphere_zero_iff_norm.2
        (NormedSpace.norm_normalize_eq_one_iff.2 x.2)⟩ : sphere (0 : E) 1)) :=
  contMDiff_normalize_compl_zero.codRestrict_sphere _

end Punctured

end TauCeti
