/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Instances.Comap
public import TauCeti.Geometry.Manifold.Projectivization.Map

/-!
# The atlas of projective space with an arbitrary number of coordinates

The standard atlas `Projectivization.instChartedSpace` makes `ℙ 𝕜 (Fin (n + 1) → 𝕜)` an analytic
manifold modelled on `Fin n → 𝕜`. Projective spaces also arise with homogeneous coordinates indexed
by `Fin N` for a positive `N` that is not syntactically a successor, for instance the target of
the degree-`d` Veronese map, whose coordinates are indexed by the monomials of degree `d`.

For `N ≠ 0`, the canonical identification `finCongr : Fin N ≃ Fin (N - 1 + 1)` reindexes the
homogeneous coordinates, giving a homeomorphism
`Projectivization.finSubOneAddOneHomeomorph 𝕜 N : ℙ 𝕜 (Fin N → 𝕜) ≃ₜ ℙ 𝕜 (Fin (N - 1 + 1) → 𝕜)`.
Pulling the standard atlas back along it gives the charted space structure
`Projectivization.finChartedSpace 𝕜 N`, modelled on `Fin (N - 1) → 𝕜`. It is a `C^r` manifold for
every `r`, including the analytic order `ω`, and a map into it is `C^r` exactly when it is
continuous and its composite with the reindexing is `C^r` for the standard atlas. When
`N = n + 1`, this atlas is compatible with the standard one.

This structure is a definition rather than an instance: for `N = n + 1` it would put on
`ℙ 𝕜 (Fin (n + 1) → 𝕜)` a second atlas, different from the standard one although compatible with
it.

## Main declarations

* `Projectivization.finSubOneAddOneHomeomorph`: the reindexing homeomorphism.
* `Projectivization.finChartedSpace`: the pulled-back atlas.
* `Projectivization.isManifold_finChartedSpace`: it is a `C^r` manifold for every `r`.
* `Projectivization.contMDiff_finChartedSpace_iff`: maps into projective space with this atlas are
  `C^r` exactly when their reindexed composites are.
* `Projectivization.isLocalDiffeomorph_finSubOneAddOneHomeomorph`: the reindexing is a `C^r` local
  diffeomorphism onto projective space with its standard atlas.
* `Projectivization.compatible_finChartedSpace`: for `N = n + 1`, the standard charts are
  compatible with the pulled-back ones.
-/

public section

open Set
open scoped ContDiff Manifold LinearAlgebra.Projectivization

namespace Projectivization

variable (𝕜 : Type*) [NontriviallyNormedField 𝕜] (N : ℕ) [NeZero N]

/-- The reindexing of the coordinates of `𝕜^N` along the canonical identification
`Fin N ≃ Fin (N - 1 + 1)`. -/
noncomputable def finSubOneAddOneLinearEquiv : (Fin N → 𝕜) ≃ₗ[𝕜] Fin (N - 1 + 1) → 𝕜 :=
  LinearEquiv.funCongrLeft 𝕜 𝕜 (finCongr (Nat.sub_one_add_one (NeZero.ne N)))

@[simp]
theorem finSubOneAddOneLinearEquiv_apply (v : Fin N → 𝕜) (i : Fin (N - 1 + 1)) :
    finSubOneAddOneLinearEquiv 𝕜 N v i = v (Fin.cast (Nat.sub_one_add_one (NeZero.ne N)) i) :=
  (rfl)

@[simp]
theorem finSubOneAddOneLinearEquiv_symm_apply (v : Fin (N - 1 + 1) → 𝕜) (i : Fin N) :
    (finSubOneAddOneLinearEquiv 𝕜 N).symm v i =
      v (Fin.cast (Nat.sub_one_add_one (NeZero.ne N)).symm i) :=
  (rfl)

/-- The homeomorphism `ℙ 𝕜 (Fin N → 𝕜) ≃ₜ ℙ 𝕜 (Fin (N - 1 + 1) → 𝕜)` reindexing homogeneous
coordinates along the canonical identification `Fin N ≃ Fin (N - 1 + 1)`. -/
noncomputable def finSubOneAddOneHomeomorph : ℙ 𝕜 (Fin N → 𝕜) ≃ₜ ℙ 𝕜 (Fin (N - 1 + 1) → 𝕜) where
  toFun := map (finSubOneAddOneLinearEquiv 𝕜 N : (Fin N → 𝕜) →ₗ[𝕜] Fin (N - 1 + 1) → 𝕜)
    (LinearEquiv.injective _)
  invFun := map ((finSubOneAddOneLinearEquiv 𝕜 N).symm : (Fin (N - 1 + 1) → 𝕜) →ₗ[𝕜] Fin N → 𝕜)
    (LinearEquiv.injective _)
  left_inv := ind fun v hv ↦ by simp [map_mk]
  right_inv := ind fun v hv ↦ by simp [map_mk]
  continuous_toFun := continuous_map _ (LinearMap.continuous_on_pi _)
  continuous_invFun := continuous_map _ (LinearMap.continuous_on_pi _)

/-- The reindexing homeomorphism is the map of projective spaces induced by the reindexing linear
equivalence. -/
theorem coe_finSubOneAddOneHomeomorph :
    ⇑(finSubOneAddOneHomeomorph 𝕜 N) =
      map (finSubOneAddOneLinearEquiv 𝕜 N : (Fin N → 𝕜) →ₗ[𝕜] Fin (N - 1 + 1) → 𝕜)
        (LinearEquiv.injective _) :=
  (rfl)

/-- The reindexing homeomorphism in homogeneous coordinates. -/
@[simp]
theorem finSubOneAddOneHomeomorph_mk (v : Fin N → 𝕜) (hv : v ≠ 0) :
    finSubOneAddOneHomeomorph 𝕜 N (mk 𝕜 v hv) =
      mk 𝕜 (finSubOneAddOneLinearEquiv 𝕜 N v) ((LinearEquiv.map_ne_zero_iff _).2 hv) :=
  (rfl)

/-- The inverse of the reindexing homeomorphism in homogeneous coordinates. -/
@[simp]
theorem finSubOneAddOneHomeomorph_symm_mk (v : Fin (N - 1 + 1) → 𝕜) (hv : v ≠ 0) :
    (finSubOneAddOneHomeomorph 𝕜 N).symm (mk 𝕜 v hv) =
      mk 𝕜 ((finSubOneAddOneLinearEquiv 𝕜 N).symm v) ((LinearEquiv.map_ne_zero_iff _).2 hv) :=
  (rfl)

/-- The atlas of `ℙ 𝕜 (Fin N → 𝕜)`, for `N ≠ 0`, modelled on `Fin (N - 1) → 𝕜`: the standard
affine charts of `ℙ 𝕜 (Fin (N - 1 + 1) → 𝕜)` pulled back along the reindexing homeomorphism
`finSubOneAddOneHomeomorph 𝕜 N`. -/
@[instance_reducible]
noncomputable def finChartedSpace : ChartedSpace (Fin (N - 1) → 𝕜) (ℙ 𝕜 (Fin N → 𝕜)) :=
  (finSubOneAddOneHomeomorph 𝕜 N).isLocalHomeomorph.chartedSpaceComap

/-- The chart of `finChartedSpace 𝕜 N` at `x` reads `y` as the standard chart at the reindexed
point reads the reindexed `y`. -/
theorem chartAt_finChartedSpace_apply (x y : ℙ 𝕜 (Fin N → 𝕜)) :
    letI := finChartedSpace 𝕜 N
    chartAt (Fin (N - 1) → 𝕜) x y =
      chartAt (Fin (N - 1) → 𝕜) (finSubOneAddOneHomeomorph 𝕜 N x)
        (finSubOneAddOneHomeomorph 𝕜 N y) :=
  (finSubOneAddOneHomeomorph 𝕜 N).isLocalHomeomorph.chartAt_chartedSpaceComap_apply x y

/-- Projective space with the pulled-back atlas `finChartedSpace 𝕜 N` is a `C^r` manifold for
every `r`; for `r = ω` it is an analytic manifold. -/
theorem isManifold_finChartedSpace (r : ℕ∞ω) :
    letI := finChartedSpace 𝕜 N
    IsManifold 𝓘(𝕜, Fin (N - 1) → 𝕜) r (ℙ 𝕜 (Fin N → 𝕜)) :=
  (finSubOneAddOneHomeomorph 𝕜 N).isLocalHomeomorph.isManifold_chartedSpaceComap

variable {𝕜 N}

/-- A map into `ℙ 𝕜 (Fin N → 𝕜)` with the atlas `finChartedSpace 𝕜 N` is `C^r` if and only if it is
continuous and its composite with the reindexing homeomorphism is `C^r` for the standard atlas. -/
theorem contMDiff_finChartedSpace_iff {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
    {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'} {M : Type*}
    [TopologicalSpace M] [ChartedSpace H' M] {r : ℕ∞ω} {f : M → ℙ 𝕜 (Fin N → 𝕜)} :
    letI := finChartedSpace 𝕜 N
    ContMDiff I' 𝓘(𝕜, Fin (N - 1) → 𝕜) r f ↔
      Continuous f ∧ ContMDiff I' 𝓘(𝕜, Fin (N - 1) → 𝕜) r (finSubOneAddOneHomeomorph 𝕜 N ∘ f) :=
  (finSubOneAddOneHomeomorph 𝕜 N).isLocalHomeomorph.contMDiff_chartedSpaceComap_iff

variable (𝕜 N) in
/-- The reindexing homeomorphism is a `C^r` local diffeomorphism from `ℙ 𝕜 (Fin N → 𝕜)` with the
atlas `finChartedSpace 𝕜 N` to `ℙ 𝕜 (Fin (N - 1 + 1) → 𝕜)` with its standard atlas. -/
theorem isLocalDiffeomorph_finSubOneAddOneHomeomorph (r : ℕ∞ω) :
    letI := finChartedSpace 𝕜 N
    IsLocalDiffeomorph 𝓘(𝕜, Fin (N - 1) → 𝕜) 𝓘(𝕜, Fin (N - 1) → 𝕜) r
      (finSubOneAddOneHomeomorph 𝕜 N) :=
  (finSubOneAddOneHomeomorph 𝕜 N).isLocalHomeomorph.isLocalDiffeomorph_chartedSpaceComap

variable (𝕜) in
/-- For `N = n + 1`, the standard affine charts of `ℙ 𝕜 (Fin (n + 1) → 𝕜)` are `C^r` compatible
with the charts of `finChartedSpace 𝕜 (n + 1)`, for every `r`: the two atlases define the same
`C^r` manifold structure. -/
theorem compatible_finChartedSpace (n : ℕ) (r : ℕ∞ω) :
    ∀ e ∈ atlas (Fin n → 𝕜) (ℙ 𝕜 (Fin (n + 1) → 𝕜)),
      ∀ e' ∈ (finChartedSpace 𝕜 (n + 1)).atlas,
        e.symm.trans e' ∈ contDiffGroupoid r 𝓘(𝕜, Fin n → 𝕜) := by
  -- The standard atlas of the reindexed space, read with the model `Fin n → 𝕜`, which is
  -- definitionally `Fin (n + 1 - 1) → 𝕜`.
  let : ChartedSpace (Fin n → 𝕜) (ℙ 𝕜 (Fin (n + 1 - 1 + 1) → 𝕜)) := instChartedSpace
  have : IsManifold 𝓘(𝕜, Fin n → 𝕜) r (ℙ 𝕜 (Fin (n + 1 - 1 + 1) → 𝕜)) := instIsManifold r
  have h := (mapDiffeomorph (finSubOneAddOneLinearEquiv 𝕜 (n + 1)) r).isLocalDiffeomorph
  rw [coe_mapDiffeomorph] at h
  exact (finSubOneAddOneHomeomorph 𝕜 (n + 1)).isLocalHomeomorph.compatible_chartedSpaceComap h

end Projectivization
