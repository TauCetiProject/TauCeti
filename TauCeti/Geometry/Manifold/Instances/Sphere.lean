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
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Topology.MetricSpace.HausdorffDimension
import TauCeti.Analysis.Normed.Group.BallSphere
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
away from `-1`. A differentiable loop in a sphere of dimension
at least two omits a point, allowing the entire loop to be read in one stereographic chart.

## Main results

* `TauCeti.finrank_euclideanSpace_fin_succ_fact`: the dimension of `ℝⁿ⁺¹`, in the form the
  stereographic charts of its unit sphere take it.
* `TauCeti.injective_fderiv_stereoInvFunAux_comp_coe`: the inverse of stereographic projection
  from `v`, as a map from `(ℝ ∙ v)ᗮ` to the ambient space, has injective derivative.
* `TauCeti.chartAt_sphere`: the preferred chart at `v` is `stereographic' n (-v)`.
* `TauCeti.extChartAt_sphere_apply_self`: the preferred extended chart at `v` sends `v` to `0`.
* `TauCeti.isSmoothEmbedding_stereographic'_symm`: the inverse of a stereographic chart is a
  smooth embedding of the model space into the sphere.
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
* `TauCeti.mfderiv_eq_of_deriv_coe_comp_circleExp_eq`: two loops in a sphere through the same point
  with the same velocity there, read along `Circle.exp`, have the same derivative.
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

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
  [Fact (finrank ℝ E = n + 1)]

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
  have h : ContDiffAt ℝ n (fun x : ℂ => (Complex.log x).im) z :=
    Complex.imCLM.contDiff.contDiffAt.comp _ ((Complex.contDiffAt_log hslit).restrict_scalars ℝ)
  have hc : ContMDiff (𝓡 1) 𝓘(ℝ, ℂ) n (fun w : Circle => (w : ℂ)) := contMDiff_coe_sphere
  exact (h.contMDiffAt.comp z hc.contMDiffAt).congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun w => (Complex.log_im w).symm)

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

end SphereLoop

/-! ### Points omitted by differentiable loops -/

/-- A differentiable loop in a sphere of dimension at least two omits a point.
No immersion or injectivity assumption is needed. -/
theorem exists_notMem_range_circle_sphere
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {n : ℕ} [Fact (finrank ℝ E = n + 1)] (hn : 2 ≤ n)
    {f : Circle → sphere (0 : E) 1} (hf : MDifferentiable (𝓡 1) (𝓡 n) f) :
    ∃ p : sphere (0 : E) 1, p ∉ range f := by
  -- The cone over the loop is the image of a differentiable map from a plane.
  have hγ : Differentiable ℝ (fun t => (f (Circle.exp t) : E)) :=
    mdifferentiable_iff_differentiable.mp <|
      ((contMDiff_coe_sphere (m := 1)).mdifferentiable one_ne_zero).comp
        (hf.comp ((contMDiff_circleExp (m := 1)).mdifferentiable one_ne_zero))
  let F : ℝ × ℝ → E := fun q => q.1 • (f (Circle.exp q.2) : E)
  have hF : Differentiable ℝ F := differentiable_fst.smul (hγ.comp differentiable_snd)
  obtain ⟨a, ha⟩ := (hF.dense_compl_range_of_finrank_lt_finrank (by
    rw [Module.finrank_prod, Module.finrank_self, (Fact.out : finrank ℝ E = n + 1)]
    omega)).nonempty
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact ha ⟨(0, 0), by simp [F]⟩
  have hnorm : ‖‖a‖⁻¹ • a‖ = 1 := norm_smul_inv_norm ha0
  refine ⟨⟨‖a‖⁻¹ • a, mem_sphere_zero_iff_norm.mpr hnorm⟩, ?_⟩
  rintro ⟨z, hz⟩
  obtain ⟨t, rfl⟩ := Circle.exp_surjective z
  have hz' := congrArg Subtype.val hz
  refine ha ⟨(‖a‖, t), ?_⟩
  simp only [F, hz', smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr ha0), one_smul]

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
