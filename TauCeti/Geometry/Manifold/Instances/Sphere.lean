/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Instances.Sphere
public import Mathlib.Geometry.Manifold.SmoothEmbedding
public import TauCeti.Analysis.InnerProductSpace.LinearIsometry
public import TauCeti.Geometry.Manifold.Immersion
public import TauCeti.Geometry.Sphere.LinearIsometry

/-!
# The stereographic charts of the sphere, and the smooth embeddings of spheres induced by
linear isometries

Mathlib charts the unit sphere of an `(n + 1)`-dimensional real inner product space by
stereographic projection, the preferred chart at `v` projecting from the antipode `-v`
(`EuclideanSpace.instChartedSpaceSphere`). This file records the two facts about these charts
that computations in a chart at a chosen point use: which stereographic projection the preferred
chart is, and that the extended chart at `v` sends `v` to the origin of the model space.

It then uses the charts to show that a linear isometry `ι : F →ₗᵢ[ℝ] E` restricts to a smooth
embedding of unit spheres, `LinearIsometry.unitSphereMap`. Stereographic projection is defined
from inner products and orthogonal projections, both of which `ι` preserves, so `ι` carries the
stereographic chart at `v` to the stereographic chart at `ι v`: in those two charts, `ι` reads as a
linear isometry `LinearIsometry.stereographicModelMap` of the model Euclidean spaces, and a linear
isometry is the inclusion of a factor in a product decomposition
(`LinearIsometry.prodOrthogonalRangeEquiv`). That is the normal form Mathlib's
`Manifold.IsImmersionAt` asks for, and together with the isometric embedding of the spheres it
makes the restriction a smooth embedding. Great circles, the geometric presentation of the unknot,
are the case of a linear isometry `ℂ →ₗᵢ[ℝ] E`.

## Main results

* `TauCeti.chartAt_sphere`: the preferred chart at `v` is `stereographic' n (-v)`.
* `TauCeti.extChartAt_sphere_apply_self`: the preferred extended chart at `v` sends `v` to `0`.
* `LinearIsometry.stereographic'_unitSphereMap`: the stereographic charts read a linear isometry
  of unit spheres as a linear isometry of the model spaces.
* `LinearIsometry.isSmoothEmbedding_unitSphereMap`: the restriction of a linear isometry to the
  unit spheres is a smooth embedding, at every differentiability order.
-/

public section

noncomputable section

open Function Manifold Metric Module Set
open scoped Manifold InnerProductSpace ContDiff

namespace TauCeti

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
