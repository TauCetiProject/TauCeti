/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.FiniteRank.CoordinateFunctor
public import TauCeti.Geometry.Manifold.VectorBundle.CoordinateHom

/-!
# Smooth and holomorphic bundle operations from coordinate functors

A continuous coordinate functor `Φ : TauCeti.CoordinateFunctor 𝕜 𝕜` acts on finite-rank bundle
cores by applying `Φ.map` to their transition maps (`TauCeti.CoordinateFunctor.mapCore`) and to
the chart operators of bundle maps (`TauCeti.CoordinateFunctor.mapHom`). When `Φ.map` is itself a
`C^n` map between spaces of operators, this action preserves regularity over any base manifold:

* `TauCeti.CoordinateFunctor.isContMDiff_mapCore`: the image of a `C^n` core is a `C^n` core;
* `TauCeti.CoordinateFunctor.contMDiff_totalSpaceMap_mapHom`: the image of a bundle map between
  `C^n` cores whose map of total spaces is `C^n` again has a `C^n` map of total spaces.

Over a complex manifold, with `𝕜 = ℂ` and `n = ∞`, a functor acting holomorphically on operators
thus turns holomorphic vector bundles and holomorphic bundle maps into holomorphic ones. This is
the case for exterior powers, whose action on operators is polynomial. It is not the case for
complex conjugation: `TauCeti.CoordinateFunctor.conjugate` acts on operators by a real-smooth map
that is not complex differentiable.

## References

* J. W. Milnor and J. D. Stasheff, *Characteristic Classes*, §3 (continuous functors).
* D. Huybrechts, *Complex Geometry: An Introduction*, §2.2.
-/

public section

open Bundle
open scoped Manifold ContDiff

namespace TauCeti.CoordinateFunctor

variable {𝕜 B : Type*} [NontriviallyNormedField 𝕜] [TopologicalSpace B]
  {EB HB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB] [TopologicalSpace HB]
  [ChartedSpace HB B] {I : ModelWithCorners 𝕜 EB HB} {n : ℕ∞ω} (Φ : CoordinateFunctor 𝕜 𝕜)

/-- A coordinate functor whose action on operators is `C^n` sends `C^n` cores to `C^n` cores. -/
theorem isContMDiff_mapCore (A : FiniteRankBundleCore 𝕜 B) [A.core.IsContMDiff I n]
    (hΦ : ContDiff 𝕜 n (Φ.map (m := A.rank) (n := A.rank))) :
    (Φ.mapCore A).core.IsContMDiff I n where
  contMDiffOn_coordChange i j :=
    hΦ.contMDiff.comp_contMDiffOn (A.core.contMDiffOn_coordChange I i j)

/-- If a coordinate functor acts by a `C^n` map on operators between the fibres of two `C^n` cores
whose images are `C^n` cores, then it sends a bundle map with `C^n` map of total spaces to a bundle
map with `C^n` map of total spaces. -/
theorem contMDiff_totalSpaceMap_mapHom [CompleteSpace 𝕜] {A D : FiniteRankBundleCore 𝕜 B}
    [A.core.IsContMDiff I n] [D.core.IsContMDiff I n] [(Φ.mapCore A).core.IsContMDiff I n]
    [(Φ.mapCore D).core.IsContMDiff I n]
    (hΦ : ContDiff 𝕜 n (Φ.map (m := A.rank) (n := D.rank))) (f : A ⟶ D)
    (hf : ContMDiff (I.prod 𝓘(𝕜, Fin A.rank → 𝕜)) (I.prod 𝓘(𝕜, Fin D.rank → 𝕜)) n
      f.totalSpaceMap) :
    ContMDiff (I.prod 𝓘(𝕜, Fin (Φ.mapCore A).rank → 𝕜))
      (I.prod 𝓘(𝕜, Fin (Φ.mapCore D).rank → 𝕜)) n (Φ.mapHom f).totalSpaceMap := by
  rw [VectorBundleCore.CoordinateHom.contMDiff_totalSpaceMap_iff] at hf ⊢
  intro i j
  refine (hΦ.contMDiff.comp_contMDiffOn (hf i j)).congr fun x _ ↦ ?_
  -- In every pair of charts, the transformed fibre map is the image of the original one, since
  -- `Φ.map` preserves the composites with the transition maps.
  rw [Function.comp_apply, VectorBundleCore.inChartCoordinates_def,
    VectorBundleCore.inChartCoordinates_def, fiberMap_mapHom, map_comp, map_comp,
    coordChange_mapCore, coordChange_mapCore]
  -- `Φ.mapCore` keeps the preferred charts of `A` and `D`.
  rfl

end TauCeti.CoordinateFunctor
