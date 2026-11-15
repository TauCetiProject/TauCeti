/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CoordinateHom
public import TauCeti.Geometry.Manifold.VectorBundle.FiniteRank.Basic
public import TauCeti.Topology.VectorBundle.FiniteRank.Biproduct

/-!
# `C^n` and holomorphic Whitney sums of finite-rank bundle cores

If `A` and `D` are point-indexed finite-rank vector-bundle cores over a charted base `B` whose
transition functions are `C^n` (`VectorBundleCore.IsContMDiff IB n`), then the block-diagonal
transition functions of their Whitney sum `whitneySum A D` are `C^n` (`isContMDiff_whitneySum`),
making `(whitneySum A D).core.Fiber` a `C^n` vector bundle. Over a complex model `𝓘(ℂ, EB)` with
`n = ∞`, this equips the Whitney sum of two holomorphic cocycles with its holomorphic vector-bundle
structure while preserving the topological carrier and bundle charts of `whitneySum A D`.

At the level of chart operators, the canonical projections `whitneyFst`, `whitneySnd` and
inclusions `whitneyInl`, `whitneyInr` have `C^n` chart operators whenever the corresponding summand
core is `C^n`, while pairings `whitneyLift`, copairings `whitneyDesc`, and direct sums of morphisms
`whitneyMap` preserve `C^n` chart-operator regularity unconditionally.

On the reconstructed total spaces, no smoothness hypothesis on the base atlas or on the core
transition maps, and no completeness assumption on the scalar field, is needed: in the preferred
chart at each base point the four canonical bicone legs and `whitneySumFiberEquiv` are fixed
continuous linear maps. Accordingly:

* `contMDiff_totalSpaceMap_into_whitneySum_iff` and `contMDiff_totalSpaceMap_from_whitneySum_iff`
  characterize `C^n` total-space maps into and out of a Whitney sum by their compositions with the
  projections and inclusions, yielding `C^n` biproduct universal properties for `whitneyLift`,
  `whitneyDesc`, and `whitneyMap`;
* `whitneyMapIsoDiffeomorph`, `whitneyCommDiffeomorph`, `whitneyAssocDiffeomorph`,
  `whitneyZeroLeftDiffeomorph`, and `whitneyZeroRightDiffeomorph` glue functoriality, symmetry,
  associativity, and rank-zero unit core isomorphisms to `C^n` diffeomorphisms of total spaces;
* `whitneySumTotalSpaceDiffeomorph` upgrades `whitneySumTotalSpaceHomeomorph` to a `C^n` (and in
  particular holomorphic) diffeomorphism between `(whitneySum A D).core.TotalSpace` and the total
  space of Mathlib's direct-sum vector bundle `A.core.Fiber ×ᵇ D.core.Fiber`, over the identity of
  `B` and by `whitneySumFiberEquiv` (`TauCeti.splitCoords`) on each fibre.

## References

* Norman Steenrod, *The Topology of Fibre Bundles*, Princeton University Press, 1951, §2–§3.
* John W. Milnor and James D. Stasheff, *Characteristic Classes*, Princeton University Press, 1974,
  §3.
* Daniel Huybrechts, *Complex Geometry: An Introduction*, Springer, 2005, §2.2.
-/

public section

open Bundle CategoryTheory VectorBundleCore Set
open scoped Manifold ContDiff Topology

namespace TauCeti.FiniteRankBundleCore

variable {𝕜 B : Type*} [NontriviallyNormedField 𝕜] {n : WithTop ℕ∞}
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners 𝕜 EB HB}
  [TopologicalSpace B] [ChartedSpace HB B]

section ChartRegularity

variable {A A' D D' E : FiniteRankBundleCore 𝕜 B}

/-- The Whitney sum of two `C^n` finite-rank bundle cores has `C^n` transition functions, hence its
reconstructed bundle is a `C^n` vector bundle. Over `𝓘(ℂ, EB)` with `n = ∞`, this gives the
holomorphic Whitney sum of holomorphic vector-bundle cores without requiring `IsManifold` or
completeness of `𝕜`. -/
instance isContMDiff_whitneySum (A D : FiniteRankBundleCore 𝕜 B)
    [A.core.IsContMDiff IB n] [D.core.IsContMDiff IB n] :
    (whitneySum A D).core.IsContMDiff IB n where
  contMDiffOn_coordChange i j := by
    -- Unfold the Whitney-sum projections before elaborating the operator-space topology
    -- and the block-diagonal composition.
    dsimp +instances only [whitneySum]
    have hA : ContMDiffOn IB 𝓘(𝕜, (Fin A.rank → 𝕜) →L[𝕜] (Fin A.rank → 𝕜)) n
        (A.core.coordChange i j)
        ((A.core.baseSet i ∩ D.core.baseSet i) ∩ (A.core.baseSet j ∩ D.core.baseSet j)) :=
      (A.core.contMDiffOn_coordChange IB i j).mono fun _ h ↦ ⟨h.1.1, h.2.1⟩
    have hD : ContMDiffOn IB 𝓘(𝕜, (Fin D.rank → 𝕜) →L[𝕜] (Fin D.rank → 𝕜)) n
        (D.core.coordChange i j)
        ((A.core.baseSet i ∩ D.core.baseSet i) ∩ (A.core.baseSet j ∩ D.core.baseSet j)) :=
      (D.core.contMDiffOn_coordChange IB i j).mono fun _ h ↦ ⟨h.1.2, h.2.2⟩
    let S := (splitCoords (𝕜 := 𝕜) (M := 𝕜) A.rank D.rank).toContinuousLinearMap
    let S' := (splitCoords (𝕜 := 𝕜) (M := 𝕜) A.rank D.rank).symm.toContinuousLinearMap
    exact (contMDiffOn_const (c := S')).clm_comp
      ((hA.clm_prodMap hD).clm_comp (contMDiffOn_const (c := S)))

/-- When `A` is a `C^n` core, the chart operators of `whitneyFst A D` are `C^n`. -/
theorem contMDiffOn_inChartCoordinates_whitneyFst (A D : FiniteRankBundleCore 𝕜 B)
    [A.core.IsContMDiff IB n] (i j : B) :
    ContMDiffOn IB 𝓘(𝕜, (Fin (whitneySum A D).rank → 𝕜) →L[𝕜] (Fin A.rank → 𝕜)) n
      (fun x ↦ (whitneySum A D).core.inChartCoordinates A.core i j x
        ((whitneyFst A D).fiberMap x))
      ((whitneySum A D).core.baseSet i ∩ A.core.baseSet j) := by
  let L : (Fin (whitneySum A D).rank → 𝕜) →L[𝕜] (Fin A.rank → 𝕜) :=
    (ContinuousLinearMap.fst 𝕜 (Fin A.rank → 𝕜) (Fin D.rank → 𝕜)).comp
      (splitCoords (𝕜 := 𝕜) A.rank D.rank).toContinuousLinearMap
  refine contMDiffOn_inChartCoordinates_of_coordChange_comp (whitneyFst A D) inter_subset_left L
    fun x _ v ↦ ?_
  calc (whitneyFst A D).fiberMap x ((whitneySum A D).core.coordChange i x x v)
      = (splitCoords (𝕜 := 𝕜) A.rank D.rank ((whitneySum A D).core.coordChange i x x v)).1 :=
        DFunLike.congr_fun (fiberMap_whitneyFst A D x) _
    _ = A.core.coordChange i x x (L v) :=
        congrArg Prod.fst (splitCoords_coordChange_whitneySum A D i x x v)

/-- When `D` is a `C^n` core, the chart operators of `whitneySnd A D` are `C^n`. -/
theorem contMDiffOn_inChartCoordinates_whitneySnd (A D : FiniteRankBundleCore 𝕜 B)
    [D.core.IsContMDiff IB n] (i j : B) :
    ContMDiffOn IB 𝓘(𝕜, (Fin (whitneySum A D).rank → 𝕜) →L[𝕜] (Fin D.rank → 𝕜)) n
      (fun x ↦ (whitneySum A D).core.inChartCoordinates D.core i j x
        ((whitneySnd A D).fiberMap x))
      ((whitneySum A D).core.baseSet i ∩ D.core.baseSet j) := by
  let L : (Fin (whitneySum A D).rank → 𝕜) →L[𝕜] (Fin D.rank → 𝕜) :=
    (ContinuousLinearMap.snd 𝕜 (Fin A.rank → 𝕜) (Fin D.rank → 𝕜)).comp
      (splitCoords (𝕜 := 𝕜) A.rank D.rank).toContinuousLinearMap
  refine contMDiffOn_inChartCoordinates_of_coordChange_comp (whitneySnd A D) inter_subset_right L
    fun x _ v ↦ ?_
  calc (whitneySnd A D).fiberMap x ((whitneySum A D).core.coordChange i x x v)
      = (splitCoords (𝕜 := 𝕜) A.rank D.rank ((whitneySum A D).core.coordChange i x x v)).2 :=
        DFunLike.congr_fun (fiberMap_whitneySnd A D x) _
    _ = D.core.coordChange i x x (L v) :=
        congrArg Prod.snd (splitCoords_coordChange_whitneySum A D i x x v)

/-- When `A` is a `C^n` core, the chart operators of `whitneyInl A D` are `C^n`. -/
theorem contMDiffOn_inChartCoordinates_whitneyInl (A D : FiniteRankBundleCore 𝕜 B)
    [A.core.IsContMDiff IB n] (i j : B) :
    ContMDiffOn IB 𝓘(𝕜, (Fin A.rank → 𝕜) →L[𝕜] (Fin (whitneySum A D).rank → 𝕜)) n
      (fun x ↦ A.core.inChartCoordinates (whitneySum A D).core i j x
        ((whitneyInl A D).fiberMap x))
      (A.core.baseSet i ∩ (whitneySum A D).core.baseSet j) := by
  let S' : ((Fin A.rank → 𝕜) × (Fin D.rank → 𝕜)) →L[𝕜] (Fin (whitneySum A D).rank → 𝕜) :=
    (splitCoords (𝕜 := 𝕜) A.rank D.rank).symm.toContinuousLinearMap
  let L : (Fin A.rank → 𝕜) →L[𝕜] (Fin (whitneySum A D).rank → 𝕜) :=
    S'.comp (ContinuousLinearMap.inl 𝕜 (Fin A.rank → 𝕜) (Fin D.rank → 𝕜))
  refine contMDiffOn_inChartCoordinates_of_comp_coordChange (whitneyInl A D) inter_subset_left L
    fun x _ u ↦ ?_
  calc (whitneySum A D).core.coordChange x j x ((whitneyInl A D).fiberMap x u)
      = (whitneySum A D).core.coordChange x j x
          ((splitCoords (𝕜 := 𝕜) A.rank D.rank).symm (u, 0)) :=
        congrArg ((whitneySum A D).core.coordChange x j x)
          (DFunLike.congr_fun (fiberMap_whitneyInl A D x) u)
    _ = S' (A.core.coordChange x j x u, D.core.coordChange x j x 0) :=
        coordChange_whitneySum_splitCoords_symm A D x j x u 0
    _ = S' (A.core.coordChange x j x u, 0) := by
        rw [map_zero]

/-- When `D` is a `C^n` core, the chart operators of `whitneyInr A D` are `C^n`. -/
theorem contMDiffOn_inChartCoordinates_whitneyInr (A D : FiniteRankBundleCore 𝕜 B)
    [D.core.IsContMDiff IB n] (i j : B) :
    ContMDiffOn IB 𝓘(𝕜, (Fin D.rank → 𝕜) →L[𝕜] (Fin (whitneySum A D).rank → 𝕜)) n
      (fun x ↦ D.core.inChartCoordinates (whitneySum A D).core i j x
        ((whitneyInr A D).fiberMap x))
      (D.core.baseSet i ∩ (whitneySum A D).core.baseSet j) := by
  let S' : ((Fin A.rank → 𝕜) × (Fin D.rank → 𝕜)) →L[𝕜] (Fin (whitneySum A D).rank → 𝕜) :=
    (splitCoords (𝕜 := 𝕜) A.rank D.rank).symm.toContinuousLinearMap
  let L : (Fin D.rank → 𝕜) →L[𝕜] (Fin (whitneySum A D).rank → 𝕜) :=
    S'.comp (ContinuousLinearMap.inr 𝕜 (Fin A.rank → 𝕜) (Fin D.rank → 𝕜))
  refine contMDiffOn_inChartCoordinates_of_comp_coordChange (whitneyInr A D) inter_subset_right L
    fun x _ w ↦ ?_
  calc (whitneySum A D).core.coordChange x j x ((whitneyInr A D).fiberMap x w)
      = (whitneySum A D).core.coordChange x j x
          ((splitCoords (𝕜 := 𝕜) A.rank D.rank).symm (0, w)) :=
        congrArg ((whitneySum A D).core.coordChange x j x)
          (DFunLike.congr_fun (fiberMap_whitneyInr A D x) w)
    _ = S' (A.core.coordChange x j x 0, D.core.coordChange x j x w) :=
        coordChange_whitneySum_splitCoords_symm A D x j x 0 w
    _ = S' (0, D.core.coordChange x j x w) := by
        rw [map_zero]

/-- Pairing two morphisms with `C^n` `(i, j)` chart operators into a Whitney sum yields a `C^n`
`(i, j)` chart operator. -/
theorem contMDiffOn_inChartCoordinates_whitneyLift {f : E ⟶ A} {g : E ⟶ D} {i j : B}
    (hf : ContMDiffOn IB 𝓘(𝕜, (Fin E.rank → 𝕜) →L[𝕜] (Fin A.rank → 𝕜)) n
      (fun x ↦ E.core.inChartCoordinates A.core i j x (f.fiberMap x))
      (E.core.baseSet i ∩ A.core.baseSet j))
    (hg : ContMDiffOn IB 𝓘(𝕜, (Fin E.rank → 𝕜) →L[𝕜] (Fin D.rank → 𝕜)) n
      (fun x ↦ E.core.inChartCoordinates D.core i j x (g.fiberMap x))
      (E.core.baseSet i ∩ D.core.baseSet j)) :
    ContMDiffOn IB 𝓘(𝕜, (Fin E.rank → 𝕜) →L[𝕜] (Fin (whitneySum A D).rank → 𝕜)) n
      (fun x ↦ E.core.inChartCoordinates (whitneySum A D).core i j x
        ((whitneyLift f g).fiberMap x))
      (E.core.baseSet i ∩ (whitneySum A D).core.baseSet j) := by
  let U := E.core.baseSet i ∩ (whitneySum A D).core.baseSet j
  have hf' := hf.mono fun x (h : x ∈ U) ↦ ⟨h.1, h.2.1⟩
  have hg' := hg.mono fun x (h : x ∈ U) ↦ ⟨h.1, h.2.2⟩
  let Δ : (Fin E.rank → 𝕜) →L[𝕜] (Fin E.rank → 𝕜) × (Fin E.rank → 𝕜) :=
    (ContinuousLinearMap.id 𝕜 _).prod (ContinuousLinearMap.id 𝕜 _)
  let S' : ((Fin A.rank → 𝕜) × (Fin D.rank → 𝕜)) →L[𝕜] (Fin (whitneySum A D).rank → 𝕜) :=
    (splitCoords (𝕜 := 𝕜) A.rank D.rank).symm.toContinuousLinearMap
  refine ((contMDiffOn_const (c := S')).clm_comp
    ((hf'.clm_prodMap hg').clm_comp (contMDiffOn_const (c := Δ)))).congr fun x _ ↦ ?_
  ext v : 1
  calc E.core.inChartCoordinates (whitneySum A D).core i j x ((whitneyLift f g).fiberMap x) v
      = (whitneySum A D).core.coordChange x j x
          ((whitneyLift f g).fiberMap x (E.core.coordChange i x x v)) :=
        inChartCoordinates_core_apply E (whitneySum A D) i j x _ v
    _ = (whitneySum A D).core.coordChange x j x
          ((splitCoords (𝕜 := 𝕜) A.rank D.rank).symm
            (f.fiberMap x (E.core.coordChange i x x v),
              g.fiberMap x (E.core.coordChange i x x v))) :=
        congrArg ((whitneySum A D).core.coordChange x j x)
          (DFunLike.congr_fun (fiberMap_whitneyLift f g x) _)
    _ = S' (A.core.coordChange x j x (f.fiberMap x (E.core.coordChange i x x v)),
            D.core.coordChange x j x (g.fiberMap x (E.core.coordChange i x x v))) :=
        coordChange_whitneySum_splitCoords_symm A D x j x _ _
    _ = S' (E.core.inChartCoordinates A.core i j x (f.fiberMap x) v,
            E.core.inChartCoordinates D.core i j x (g.fiberMap x) v) := by
        rw [← inChartCoordinates_core_apply, ← inChartCoordinates_core_apply]

/-- Copairing two morphisms with `C^n` `(i, j)` chart operators out of a Whitney sum yields a `C^n`
`(i, j)` chart operator. -/
theorem contMDiffOn_inChartCoordinates_whitneyDesc {f : A ⟶ E} {g : D ⟶ E} {i j : B}
    (hf : ContMDiffOn IB 𝓘(𝕜, (Fin A.rank → 𝕜) →L[𝕜] (Fin E.rank → 𝕜)) n
      (fun x ↦ A.core.inChartCoordinates E.core i j x (f.fiberMap x))
      (A.core.baseSet i ∩ E.core.baseSet j))
    (hg : ContMDiffOn IB 𝓘(𝕜, (Fin D.rank → 𝕜) →L[𝕜] (Fin E.rank → 𝕜)) n
      (fun x ↦ D.core.inChartCoordinates E.core i j x (g.fiberMap x))
      (D.core.baseSet i ∩ E.core.baseSet j)) :
    ContMDiffOn IB 𝓘(𝕜, (Fin (whitneySum A D).rank → 𝕜) →L[𝕜] (Fin E.rank → 𝕜)) n
      (fun x ↦ (whitneySum A D).core.inChartCoordinates E.core i j x
        ((whitneyDesc f g).fiberMap x))
      ((whitneySum A D).core.baseSet i ∩ E.core.baseSet j) := by
  let U := (whitneySum A D).core.baseSet i ∩ E.core.baseSet j
  have hf' := hf.mono fun x (h : x ∈ U) ↦ ⟨h.1.1, h.2⟩
  have hg' := hg.mono fun x (h : x ∈ U) ↦ ⟨h.1.2, h.2⟩
  let S : (Fin (whitneySum A D).rank → 𝕜) →L[𝕜] (Fin A.rank → 𝕜) × (Fin D.rank → 𝕜) :=
    (splitCoords (𝕜 := 𝕜) A.rank D.rank).toContinuousLinearMap
  let C' : ((Fin E.rank → 𝕜) × (Fin E.rank → 𝕜)) →L[𝕜] (Fin E.rank → 𝕜) :=
    (ContinuousLinearMap.id 𝕜 _).coprod (ContinuousLinearMap.id 𝕜 _)
  refine ((contMDiffOn_const (c := C')).clm_comp
    ((hf'.clm_prodMap hg').clm_comp (contMDiffOn_const (c := S)))).congr fun x _ ↦ ?_
  ext v : 1
  calc (whitneySum A D).core.inChartCoordinates E.core i j x ((whitneyDesc f g).fiberMap x) v
      = E.core.coordChange x j x
          ((whitneyDesc f g).fiberMap x ((whitneySum A D).core.coordChange i x x v)) :=
        inChartCoordinates_core_apply (whitneySum A D) E i j x _ v
    _ = E.core.coordChange x j x
          (f.fiberMap x
              (splitCoords (𝕜 := 𝕜) A.rank D.rank ((whitneySum A D).core.coordChange i x x v)).1 +
            g.fiberMap x
              (splitCoords (𝕜 := 𝕜) A.rank D.rank ((whitneySum A D).core.coordChange i x x v)).2) :=
        congrArg (E.core.coordChange x j x) (fiberMap_whitneyDesc_apply f g x _)
    _ = E.core.coordChange x j x
          (f.fiberMap x (A.core.coordChange i x x (S v).1) +
            g.fiberMap x (D.core.coordChange i x x (S v).2)) :=
        congrArg (fun p : (Fin A.rank → 𝕜) × (Fin D.rank → 𝕜) ↦
          E.core.coordChange x j x (f.fiberMap x p.1 + g.fiberMap x p.2))
          (splitCoords_coordChange_whitneySum A D i x x v)
    _ = A.core.inChartCoordinates E.core i j x (f.fiberMap x) (S v).1 +
          D.core.inChartCoordinates E.core i j x (g.fiberMap x) (S v).2 := by
        rw [map_add, ← inChartCoordinates_core_apply, ← inChartCoordinates_core_apply]

/-- Direct sums of morphisms with `C^n` `(i, j)` chart operators have a `C^n` `(i, j)` chart
operator. -/
theorem contMDiffOn_inChartCoordinates_whitneyMap {f : A ⟶ A'} {g : D ⟶ D'} {i j : B}
    (hf : ContMDiffOn IB 𝓘(𝕜, (Fin A.rank → 𝕜) →L[𝕜] (Fin A'.rank → 𝕜)) n
      (fun x ↦ A.core.inChartCoordinates A'.core i j x (f.fiberMap x))
      (A.core.baseSet i ∩ A'.core.baseSet j))
    (hg : ContMDiffOn IB 𝓘(𝕜, (Fin D.rank → 𝕜) →L[𝕜] (Fin D'.rank → 𝕜)) n
      (fun x ↦ D.core.inChartCoordinates D'.core i j x (g.fiberMap x))
      (D.core.baseSet i ∩ D'.core.baseSet j)) :
    ContMDiffOn IB 𝓘(𝕜, (Fin (whitneySum A D).rank → 𝕜) →L[𝕜] (Fin (whitneySum A' D').rank → 𝕜)) n
      (fun x ↦ (whitneySum A D).core.inChartCoordinates (whitneySum A' D').core i j x
        ((whitneyMap f g).fiberMap x))
      ((whitneySum A D).core.baseSet i ∩ (whitneySum A' D').core.baseSet j) := by
  let U := (whitneySum A D).core.baseSet i ∩ (whitneySum A' D').core.baseSet j
  have hf' := hf.mono fun x (h : x ∈ U) ↦ ⟨h.1.1, h.2.1⟩
  have hg' := hg.mono fun x (h : x ∈ U) ↦ ⟨h.1.2, h.2.2⟩
  let S : (Fin (whitneySum A D).rank → 𝕜) →L[𝕜] (Fin A.rank → 𝕜) × (Fin D.rank → 𝕜) :=
    (splitCoords (𝕜 := 𝕜) A.rank D.rank).toContinuousLinearMap
  let S' : ((Fin A'.rank → 𝕜) × (Fin D'.rank → 𝕜)) →L[𝕜] (Fin (whitneySum A' D').rank → 𝕜) :=
    (splitCoords (𝕜 := 𝕜) A'.rank D'.rank).symm.toContinuousLinearMap
  refine ((contMDiffOn_const (c := S')).clm_comp
    ((hf'.clm_prodMap hg').clm_comp (contMDiffOn_const (c := S)))).congr fun x _ ↦ ?_
  ext v : 1
  calc (whitneySum A D).core.inChartCoordinates (whitneySum A' D').core i j x
        ((whitneyMap f g).fiberMap x) v
      = (whitneySum A' D').core.coordChange x j x
          ((whitneyMap f g).fiberMap x ((whitneySum A D).core.coordChange i x x v)) :=
        inChartCoordinates_core_apply (whitneySum A D) (whitneySum A' D') i j x _ v
    _ = (whitneySum A' D').core.coordChange x j x
          ((splitCoords (𝕜 := 𝕜) A'.rank D'.rank).symm
            (f.fiberMap x
                (splitCoords (𝕜 := 𝕜) A.rank D.rank ((whitneySum A D).core.coordChange i x x v)).1,
              g.fiberMap x
                (splitCoords (𝕜 := 𝕜) A.rank D.rank
                  ((whitneySum A D).core.coordChange i x x v)).2)) :=
        congrArg ((whitneySum A' D').core.coordChange x j x)
          (DFunLike.congr_fun (fiberMap_whitneyMap f g x) _)
    _ = S' (A'.core.coordChange x j x
            (f.fiberMap x
              (splitCoords (𝕜 := 𝕜) A.rank D.rank ((whitneySum A D).core.coordChange i x x v)).1),
          D'.core.coordChange x j x
            (g.fiberMap x
              (splitCoords (𝕜 := 𝕜) A.rank D.rank
                ((whitneySum A D).core.coordChange i x x v)).2)) :=
        coordChange_whitneySum_splitCoords_symm A' D' x j x _ _
    _ = S' (A'.core.coordChange x j x (f.fiberMap x (A.core.coordChange i x x (S v).1)),
          D'.core.coordChange x j x (g.fiberMap x (D.core.coordChange i x x (S v).2))) :=
        congrArg (fun p : (Fin A.rank → 𝕜) × (Fin D.rank → 𝕜) ↦
          S' (A'.core.coordChange x j x (f.fiberMap x p.1),
            D'.core.coordChange x j x (g.fiberMap x p.2)))
          (splitCoords_coordChange_whitneySum A D i x x v)
    _ = S' (A.core.inChartCoordinates A'.core i j x (f.fiberMap x) (S v).1,
          D.core.inChartCoordinates D'.core i j x (g.fiberMap x) (S v).2) := by
        rw [← inChartCoordinates_core_apply, ← inChartCoordinates_core_apply]

end ChartRegularity

section TotalSpaceRegularity

variable {A A' D D' C E : FiniteRankBundleCore 𝕜 B}

/-- The first projection of a Whitney sum glues to a `C^n` map of total spaces, without any `C^n`
assumption on the cores or completeness of `𝕜`. -/
theorem contMDiff_totalSpaceMap_whitneyFst (A D : FiniteRankBundleCore 𝕜 B) :
    ContMDiff (IB.prod 𝓘(𝕜, Fin (whitneySum A D).rank → 𝕜)) (IB.prod 𝓘(𝕜, Fin A.rank → 𝕜)) n
      (whitneyFst A D).totalSpaceMap := by
  let L : (Fin (whitneySum A D).rank → 𝕜) →L[𝕜] (Fin A.rank → 𝕜) :=
    (ContinuousLinearMap.fst 𝕜 (Fin A.rank → 𝕜) (Fin D.rank → 𝕜)).comp
      (splitCoords (𝕜 := 𝕜) A.rank D.rank).toContinuousLinearMap
  refine contMDiff_totalSpaceMap_of_coordChange (whitneyFst A D) L fun x b v ↦ ?_
  calc A.core.coordChange x b x ((whitneyFst A D).fiberMap x v)
      = A.core.coordChange x b x (splitCoords (𝕜 := 𝕜) A.rank D.rank v).1 :=
        congrArg (A.core.coordChange x b x) (DFunLike.congr_fun (fiberMap_whitneyFst A D x) v)
    _ = L ((whitneySum A D).core.coordChange x b x v) :=
        (congrArg Prod.fst (splitCoords_coordChange_whitneySum A D x b x v)).symm

/-- The second projection of a Whitney sum glues to a `C^n` map of total spaces, without any `C^n`
assumption on the cores or completeness of `𝕜`. -/
theorem contMDiff_totalSpaceMap_whitneySnd (A D : FiniteRankBundleCore 𝕜 B) :
    ContMDiff (IB.prod 𝓘(𝕜, Fin (whitneySum A D).rank → 𝕜)) (IB.prod 𝓘(𝕜, Fin D.rank → 𝕜)) n
      (whitneySnd A D).totalSpaceMap := by
  let L : (Fin (whitneySum A D).rank → 𝕜) →L[𝕜] (Fin D.rank → 𝕜) :=
    (ContinuousLinearMap.snd 𝕜 (Fin A.rank → 𝕜) (Fin D.rank → 𝕜)).comp
      (splitCoords (𝕜 := 𝕜) A.rank D.rank).toContinuousLinearMap
  refine contMDiff_totalSpaceMap_of_coordChange (whitneySnd A D) L fun x b v ↦ ?_
  calc D.core.coordChange x b x ((whitneySnd A D).fiberMap x v)
      = D.core.coordChange x b x (splitCoords (𝕜 := 𝕜) A.rank D.rank v).2 :=
        congrArg (D.core.coordChange x b x) (DFunLike.congr_fun (fiberMap_whitneySnd A D x) v)
    _ = L ((whitneySum A D).core.coordChange x b x v) :=
        (congrArg Prod.snd (splitCoords_coordChange_whitneySum A D x b x v)).symm

/-- The first inclusion into a Whitney sum glues to a `C^n` map of total spaces, without any `C^n`
assumption on the cores or completeness of `𝕜`. -/
theorem contMDiff_totalSpaceMap_whitneyInl (A D : FiniteRankBundleCore 𝕜 B) :
    ContMDiff (IB.prod 𝓘(𝕜, Fin A.rank → 𝕜)) (IB.prod 𝓘(𝕜, Fin (whitneySum A D).rank → 𝕜)) n
      (whitneyInl A D).totalSpaceMap := by
  let S' : ((Fin A.rank → 𝕜) × (Fin D.rank → 𝕜)) →L[𝕜] (Fin (whitneySum A D).rank → 𝕜) :=
    (splitCoords (𝕜 := 𝕜) A.rank D.rank).symm.toContinuousLinearMap
  let L : (Fin A.rank → 𝕜) →L[𝕜] (Fin (whitneySum A D).rank → 𝕜) :=
    S'.comp (ContinuousLinearMap.inl 𝕜 (Fin A.rank → 𝕜) (Fin D.rank → 𝕜))
  refine contMDiff_totalSpaceMap_of_coordChange (whitneyInl A D) L fun x b u ↦ ?_
  calc (whitneySum A D).core.coordChange x b x ((whitneyInl A D).fiberMap x u)
      = (whitneySum A D).core.coordChange x b x
          ((splitCoords (𝕜 := 𝕜) A.rank D.rank).symm (u, 0)) :=
        congrArg ((whitneySum A D).core.coordChange x b x)
          (DFunLike.congr_fun (fiberMap_whitneyInl A D x) u)
    _ = S' (A.core.coordChange x b x u, D.core.coordChange x b x 0) :=
        coordChange_whitneySum_splitCoords_symm A D x b x u 0
    _ = S' (A.core.coordChange x b x u, 0) := by
        rw [map_zero]

/-- The second inclusion into a Whitney sum glues to a `C^n` map of total spaces, without any `C^n`
assumption on the cores or completeness of `𝕜`. -/
theorem contMDiff_totalSpaceMap_whitneyInr (A D : FiniteRankBundleCore 𝕜 B) :
    ContMDiff (IB.prod 𝓘(𝕜, Fin D.rank → 𝕜)) (IB.prod 𝓘(𝕜, Fin (whitneySum A D).rank → 𝕜)) n
      (whitneyInr A D).totalSpaceMap := by
  let S' : ((Fin A.rank → 𝕜) × (Fin D.rank → 𝕜)) →L[𝕜] (Fin (whitneySum A D).rank → 𝕜) :=
    (splitCoords (𝕜 := 𝕜) A.rank D.rank).symm.toContinuousLinearMap
  let L : (Fin D.rank → 𝕜) →L[𝕜] (Fin (whitneySum A D).rank → 𝕜) :=
    S'.comp (ContinuousLinearMap.inr 𝕜 (Fin A.rank → 𝕜) (Fin D.rank → 𝕜))
  refine contMDiff_totalSpaceMap_of_coordChange (whitneyInr A D) L fun x b w ↦ ?_
  calc (whitneySum A D).core.coordChange x b x ((whitneyInr A D).fiberMap x w)
      = (whitneySum A D).core.coordChange x b x
          ((splitCoords (𝕜 := 𝕜) A.rank D.rank).symm (0, w)) :=
        congrArg ((whitneySum A D).core.coordChange x b x)
          (DFunLike.congr_fun (fiberMap_whitneyInr A D x) w)
    _ = S' (A.core.coordChange x b x 0, D.core.coordChange x b x w) :=
        coordChange_whitneySum_splitCoords_symm A D x b x 0 w
    _ = S' (0, D.core.coordChange x b x w) := by
        rw [map_zero]

/-- The pairing `whitneyLift f g` glues to a `C^n` total-space map if and only if both `f` and `g`
do. -/
@[simp]
theorem contMDiff_totalSpaceMap_whitneyLift_iff (f : E ⟶ A) (g : E ⟶ D) :
    ContMDiff (IB.prod 𝓘(𝕜, Fin E.rank → 𝕜)) (IB.prod 𝓘(𝕜, Fin (whitneySum A D).rank → 𝕜)) n
        (whitneyLift f g).totalSpaceMap ↔
      ContMDiff (IB.prod 𝓘(𝕜, Fin E.rank → 𝕜)) (IB.prod 𝓘(𝕜, Fin A.rank → 𝕜)) n
          f.totalSpaceMap ∧
        ContMDiff (IB.prod 𝓘(𝕜, Fin E.rank → 𝕜)) (IB.prod 𝓘(𝕜, Fin D.rank → 𝕜)) n
          g.totalSpaceMap := by
  refine ⟨fun h ↦ ⟨?_, ?_⟩, fun ⟨hf, hg⟩ ↦ ?_⟩
  · rw [← whitneyLift_fst f g]
    exact CoordinateHom.contMDiff_totalSpaceMap_comp (contMDiff_totalSpaceMap_whitneyFst A D) h
  · rw [← whitneyLift_snd f g]
    exact CoordinateHom.contMDiff_totalSpaceMap_comp (contMDiff_totalSpaceMap_whitneySnd A D) h
  · rw [whitneyLift_def]
    exact CoordinateHom.contMDiff_totalSpaceMap_add
      (CoordinateHom.contMDiff_totalSpaceMap_comp (contMDiff_totalSpaceMap_whitneyInl A D) hf)
      (CoordinateHom.contMDiff_totalSpaceMap_comp (contMDiff_totalSpaceMap_whitneyInr A D) hg)

/-- A bundle morphism into a Whitney sum glues to a `C^n` total-space map if and only if its two
composites with `whitneyFst` and `whitneySnd` do. -/
theorem contMDiff_totalSpaceMap_into_whitneySum_iff (h : E ⟶ whitneySum A D) :
    ContMDiff (IB.prod 𝓘(𝕜, Fin E.rank → 𝕜)) (IB.prod 𝓘(𝕜, Fin (whitneySum A D).rank → 𝕜)) n
        h.totalSpaceMap ↔
      ContMDiff (IB.prod 𝓘(𝕜, Fin E.rank → 𝕜)) (IB.prod 𝓘(𝕜, Fin A.rank → 𝕜)) n
          (h ≫ whitneyFst A D).totalSpaceMap ∧
        ContMDiff (IB.prod 𝓘(𝕜, Fin E.rank → 𝕜)) (IB.prod 𝓘(𝕜, Fin D.rank → 𝕜)) n
          (h ≫ whitneySnd A D).totalSpaceMap := by
  conv_lhs => rw [eq_whitneyLift h]
  exact contMDiff_totalSpaceMap_whitneyLift_iff _ _

/-- The copairing `whitneyDesc f g` glues to a `C^n` total-space map if and only if both `f` and
`g` do. -/
@[simp]
theorem contMDiff_totalSpaceMap_whitneyDesc_iff (f : A ⟶ E) (g : D ⟶ E) :
    ContMDiff (IB.prod 𝓘(𝕜, Fin (whitneySum A D).rank → 𝕜)) (IB.prod 𝓘(𝕜, Fin E.rank → 𝕜)) n
        (whitneyDesc f g).totalSpaceMap ↔
      ContMDiff (IB.prod 𝓘(𝕜, Fin A.rank → 𝕜)) (IB.prod 𝓘(𝕜, Fin E.rank → 𝕜)) n
          f.totalSpaceMap ∧
        ContMDiff (IB.prod 𝓘(𝕜, Fin D.rank → 𝕜)) (IB.prod 𝓘(𝕜, Fin E.rank → 𝕜)) n
          g.totalSpaceMap := by
  refine ⟨fun h ↦ ⟨?_, ?_⟩, fun ⟨hf, hg⟩ ↦ ?_⟩
  · rw [← whitneyInl_desc f g]
    exact CoordinateHom.contMDiff_totalSpaceMap_comp h (contMDiff_totalSpaceMap_whitneyInl A D)
  · rw [← whitneyInr_desc f g]
    exact CoordinateHom.contMDiff_totalSpaceMap_comp h (contMDiff_totalSpaceMap_whitneyInr A D)
  · rw [whitneyDesc_def]
    exact CoordinateHom.contMDiff_totalSpaceMap_add
      (CoordinateHom.contMDiff_totalSpaceMap_comp hf (contMDiff_totalSpaceMap_whitneyFst A D))
      (CoordinateHom.contMDiff_totalSpaceMap_comp hg (contMDiff_totalSpaceMap_whitneySnd A D))

/-- A bundle morphism out of a Whitney sum glues to a `C^n` total-space map if and only if its
restrictions along `whitneyInl` and `whitneyInr` do. -/
theorem contMDiff_totalSpaceMap_from_whitneySum_iff (h : whitneySum A D ⟶ E) :
    ContMDiff (IB.prod 𝓘(𝕜, Fin (whitneySum A D).rank → 𝕜)) (IB.prod 𝓘(𝕜, Fin E.rank → 𝕜)) n
        h.totalSpaceMap ↔
      ContMDiff (IB.prod 𝓘(𝕜, Fin A.rank → 𝕜)) (IB.prod 𝓘(𝕜, Fin E.rank → 𝕜)) n
          (whitneyInl A D ≫ h).totalSpaceMap ∧
        ContMDiff (IB.prod 𝓘(𝕜, Fin D.rank → 𝕜)) (IB.prod 𝓘(𝕜, Fin E.rank → 𝕜)) n
          (whitneyInr A D ≫ h).totalSpaceMap := by
  conv_lhs => rw [eq_whitneyDesc h]
  exact contMDiff_totalSpaceMap_whitneyDesc_iff _ _

/-- The direct sum `whitneyMap f g` glues to a `C^n` total-space map if and only if both `f` and
`g` do. -/
@[simp]
theorem contMDiff_totalSpaceMap_whitneyMap_iff (f : A ⟶ A') (g : D ⟶ D') :
    ContMDiff (IB.prod 𝓘(𝕜, Fin (whitneySum A D).rank → 𝕜))
        (IB.prod 𝓘(𝕜, Fin (whitneySum A' D').rank → 𝕜)) n (whitneyMap f g).totalSpaceMap ↔
      ContMDiff (IB.prod 𝓘(𝕜, Fin A.rank → 𝕜)) (IB.prod 𝓘(𝕜, Fin A'.rank → 𝕜)) n
          f.totalSpaceMap ∧
        ContMDiff (IB.prod 𝓘(𝕜, Fin D.rank → 𝕜)) (IB.prod 𝓘(𝕜, Fin D'.rank → 𝕜)) n
          g.totalSpaceMap := by
  refine ⟨fun h ↦ ⟨?_, ?_⟩, fun ⟨hf, hg⟩ ↦ ?_⟩
  · have hf' : f = whitneyInl A D ≫ whitneyMap f g ≫ whitneyFst A' D' := by simp
    rw [hf']
    exact CoordinateHom.contMDiff_totalSpaceMap_comp
      (CoordinateHom.contMDiff_totalSpaceMap_comp (contMDiff_totalSpaceMap_whitneyFst A' D') h)
      (contMDiff_totalSpaceMap_whitneyInl A D)
  · have hg' : g = whitneyInr A D ≫ whitneyMap f g ≫ whitneySnd A' D' := by simp
    rw [hg']
    exact CoordinateHom.contMDiff_totalSpaceMap_comp
      (CoordinateHom.contMDiff_totalSpaceMap_comp (contMDiff_totalSpaceMap_whitneySnd A' D') h)
      (contMDiff_totalSpaceMap_whitneyInr A D)
  · rw [whitneyMap_def]
    exact (contMDiff_totalSpaceMap_whitneyLift_iff _ _).2
      ⟨CoordinateHom.contMDiff_totalSpaceMap_comp hf (contMDiff_totalSpaceMap_whitneyFst A D),
        CoordinateHom.contMDiff_totalSpaceMap_comp hg (contMDiff_totalSpaceMap_whitneySnd A D)⟩

end TotalSpaceRegularity

section Diffeomorph

/-- Direct sum of two core isomorphisms with `C^n` forward and inverse total-space maps, realized as
a `C^n` diffeomorphism of Whitney-sum total spaces. -/
def whitneyMapIsoDiffeomorph {A A' D D' : FiniteRankBundleCore 𝕜 B}
    (e₁ : A ≅ A') (e₂ : D ≅ D')
    (he₁ : ContMDiff (IB.prod 𝓘(𝕜, Fin A.rank → 𝕜)) (IB.prod 𝓘(𝕜, Fin A'.rank → 𝕜)) n
      e₁.hom.totalSpaceMap)
    (he₁' : ContMDiff (IB.prod 𝓘(𝕜, Fin A'.rank → 𝕜)) (IB.prod 𝓘(𝕜, Fin A.rank → 𝕜)) n
      e₁.inv.totalSpaceMap)
    (he₂ : ContMDiff (IB.prod 𝓘(𝕜, Fin D.rank → 𝕜)) (IB.prod 𝓘(𝕜, Fin D'.rank → 𝕜)) n
      e₂.hom.totalSpaceMap)
    (he₂' : ContMDiff (IB.prod 𝓘(𝕜, Fin D'.rank → 𝕜)) (IB.prod 𝓘(𝕜, Fin D.rank → 𝕜)) n
      e₂.inv.totalSpaceMap) :
    (whitneySum A D).core.TotalSpace ≃ₘ^n⟮IB.prod 𝓘(𝕜, Fin (whitneySum A D).rank → 𝕜),
      IB.prod 𝓘(𝕜, Fin (whitneySum A' D').rank → 𝕜)⟯ (whitneySum A' D').core.TotalSpace :=
  CoordinateHom.toDiffeomorphOfInv (whitneyMapIso e₁ e₂).hom (whitneyMapIso e₁ e₂).inv
    (whitneyMapIso e₁ e₂).hom_inv_id (whitneyMapIso e₁ e₂).inv_hom_id
    (by simpa only [whitneyMapIso_hom] using
      (contMDiff_totalSpaceMap_whitneyMap_iff e₁.hom e₂.hom).2 ⟨he₁, he₂⟩)
    (by simpa only [whitneyMapIso_inv] using
      (contMDiff_totalSpaceMap_whitneyMap_iff e₁.inv e₂.inv).2 ⟨he₁', he₂'⟩)

@[simp]
theorem coe_whitneyMapIsoDiffeomorph {A A' D D' : FiniteRankBundleCore 𝕜 B}
    (e₁ : A ≅ A') (e₂ : D ≅ D')
    (he₁ : ContMDiff (IB.prod 𝓘(𝕜, Fin A.rank → 𝕜)) (IB.prod 𝓘(𝕜, Fin A'.rank → 𝕜)) n
      e₁.hom.totalSpaceMap)
    (he₁' : ContMDiff (IB.prod 𝓘(𝕜, Fin A'.rank → 𝕜)) (IB.prod 𝓘(𝕜, Fin A.rank → 𝕜)) n
      e₁.inv.totalSpaceMap)
    (he₂ : ContMDiff (IB.prod 𝓘(𝕜, Fin D.rank → 𝕜)) (IB.prod 𝓘(𝕜, Fin D'.rank → 𝕜)) n
      e₂.hom.totalSpaceMap)
    (he₂' : ContMDiff (IB.prod 𝓘(𝕜, Fin D'.rank → 𝕜)) (IB.prod 𝓘(𝕜, Fin D.rank → 𝕜)) n
      e₂.inv.totalSpaceMap) :
    ⇑(whitneyMapIsoDiffeomorph e₁ e₂ he₁ he₁' he₂ he₂') =
      (whitneyMap e₁.hom e₂.hom).totalSpaceMap := by
  simp [whitneyMapIsoDiffeomorph]

@[simp]
theorem coe_whitneyMapIsoDiffeomorph_symm {A A' D D' : FiniteRankBundleCore 𝕜 B}
    (e₁ : A ≅ A') (e₂ : D ≅ D')
    (he₁ : ContMDiff (IB.prod 𝓘(𝕜, Fin A.rank → 𝕜)) (IB.prod 𝓘(𝕜, Fin A'.rank → 𝕜)) n
      e₁.hom.totalSpaceMap)
    (he₁' : ContMDiff (IB.prod 𝓘(𝕜, Fin A'.rank → 𝕜)) (IB.prod 𝓘(𝕜, Fin A.rank → 𝕜)) n
      e₁.inv.totalSpaceMap)
    (he₂ : ContMDiff (IB.prod 𝓘(𝕜, Fin D.rank → 𝕜)) (IB.prod 𝓘(𝕜, Fin D'.rank → 𝕜)) n
      e₂.hom.totalSpaceMap)
    (he₂' : ContMDiff (IB.prod 𝓘(𝕜, Fin D'.rank → 𝕜)) (IB.prod 𝓘(𝕜, Fin D.rank → 𝕜)) n
      e₂.inv.totalSpaceMap) :
    ⇑(whitneyMapIsoDiffeomorph e₁ e₂ he₁ he₁' he₂ he₂').symm =
      (whitneyMap e₁.inv e₂.inv).totalSpaceMap := by
  simp [whitneyMapIsoDiffeomorph]

/-- Symmetry `C^n` diffeomorphism exchanging the two summands of a Whitney sum. -/
def whitneyCommDiffeomorph (IB : ModelWithCorners 𝕜 EB HB) (n : WithTop ℕ∞)
    (A D : FiniteRankBundleCore 𝕜 B) :
    (whitneySum A D).core.TotalSpace ≃ₘ^n⟮IB.prod 𝓘(𝕜, Fin (whitneySum A D).rank → 𝕜),
      IB.prod 𝓘(𝕜, Fin (whitneySum D A).rank → 𝕜)⟯ (whitneySum D A).core.TotalSpace :=
  CoordinateHom.toDiffeomorphOfInv (whitneyCommIso A D).hom (whitneyCommIso A D).inv
    (whitneyCommIso A D).hom_inv_id (whitneyCommIso A D).inv_hom_id
    (by
      rw [whitneyCommIso_hom]
      exact (contMDiff_totalSpaceMap_whitneyLift_iff _ _).2
        ⟨contMDiff_totalSpaceMap_whitneySnd A D, contMDiff_totalSpaceMap_whitneyFst A D⟩)
    (by
      rw [whitneyCommIso_inv]
      exact (contMDiff_totalSpaceMap_whitneyLift_iff _ _).2
        ⟨contMDiff_totalSpaceMap_whitneySnd D A, contMDiff_totalSpaceMap_whitneyFst D A⟩)

@[simp]
theorem coe_whitneyCommDiffeomorph (IB : ModelWithCorners 𝕜 EB HB) (n : WithTop ℕ∞)
    (A D : FiniteRankBundleCore 𝕜 B) :
    ⇑(whitneyCommDiffeomorph IB n A D) =
      (whitneyLift (whitneySnd A D) (whitneyFst A D)).totalSpaceMap := by
  simp [whitneyCommDiffeomorph]

@[simp]
theorem coe_whitneyCommDiffeomorph_symm (IB : ModelWithCorners 𝕜 EB HB) (n : WithTop ℕ∞)
    (A D : FiniteRankBundleCore 𝕜 B) :
    ⇑(whitneyCommDiffeomorph IB n A D).symm =
      (whitneyLift (whitneySnd D A) (whitneyFst D A)).totalSpaceMap := by
  simp [whitneyCommDiffeomorph]

/-- Associativity `C^n` diffeomorphism regrouping a threefold Whitney sum. -/
def whitneyAssocDiffeomorph (IB : ModelWithCorners 𝕜 EB HB) (n : WithTop ℕ∞)
    (A D C : FiniteRankBundleCore 𝕜 B) :
    (whitneySum (whitneySum A D) C).core.TotalSpace
      ≃ₘ^n⟮IB.prod 𝓘(𝕜, Fin (whitneySum (whitneySum A D) C).rank → 𝕜),
        IB.prod 𝓘(𝕜, Fin (whitneySum A (whitneySum D C)).rank → 𝕜)⟯
      (whitneySum A (whitneySum D C)).core.TotalSpace :=
  CoordinateHom.toDiffeomorphOfInv (whitneyAssocIso A D C).hom (whitneyAssocIso A D C).inv
    (whitneyAssocIso A D C).hom_inv_id (whitneyAssocIso A D C).inv_hom_id
    (by
      rw [whitneyAssocIso_hom]
      exact (contMDiff_totalSpaceMap_whitneyLift_iff _ _).2
        ⟨CoordinateHom.contMDiff_totalSpaceMap_comp (contMDiff_totalSpaceMap_whitneyFst A D)
            (contMDiff_totalSpaceMap_whitneyFst _ _),
          (contMDiff_totalSpaceMap_whitneyLift_iff _ _).2
            ⟨CoordinateHom.contMDiff_totalSpaceMap_comp (contMDiff_totalSpaceMap_whitneySnd A D)
                (contMDiff_totalSpaceMap_whitneyFst _ _),
              contMDiff_totalSpaceMap_whitneySnd _ _⟩⟩)
    (by
      rw [whitneyAssocIso_inv]
      exact (contMDiff_totalSpaceMap_whitneyLift_iff _ _).2
        ⟨(contMDiff_totalSpaceMap_whitneyLift_iff _ _).2
            ⟨contMDiff_totalSpaceMap_whitneyFst _ _,
              CoordinateHom.contMDiff_totalSpaceMap_comp (contMDiff_totalSpaceMap_whitneyFst D C)
                (contMDiff_totalSpaceMap_whitneySnd _ _)⟩,
          CoordinateHom.contMDiff_totalSpaceMap_comp (contMDiff_totalSpaceMap_whitneySnd D C)
            (contMDiff_totalSpaceMap_whitneySnd _ _)⟩)

@[simp]
theorem coe_whitneyAssocDiffeomorph (IB : ModelWithCorners 𝕜 EB HB) (n : WithTop ℕ∞)
    (A D C : FiniteRankBundleCore 𝕜 B) :
    ⇑(whitneyAssocDiffeomorph IB n A D C) =
      (whitneyLift (whitneyFst _ _ ≫ whitneyFst A D)
        (whitneyLift (whitneyFst _ _ ≫ whitneySnd A D) (whitneySnd _ _))).totalSpaceMap := by
  simp [whitneyAssocDiffeomorph]

@[simp]
theorem coe_whitneyAssocDiffeomorph_symm (IB : ModelWithCorners 𝕜 EB HB) (n : WithTop ℕ∞)
    (A D C : FiniteRankBundleCore 𝕜 B) :
    ⇑(whitneyAssocDiffeomorph IB n A D C).symm =
      (whitneyLift (whitneyLift (whitneyFst _ _) (whitneySnd _ _ ≫ whitneyFst D C))
        (whitneySnd _ _ ≫ whitneySnd D C)).totalSpaceMap := by
  simp [whitneyAssocDiffeomorph]

/-- Left unit `C^n` diffeomorphism for Whitney sum with the trivial rank-zero core. -/
def whitneyZeroLeftDiffeomorph (IB : ModelWithCorners 𝕜 EB HB) (n : WithTop ℕ∞)
    (A : FiniteRankBundleCore 𝕜 B) :
    (whitneySum (trivial 𝕜 B 0) A).core.TotalSpace
      ≃ₘ^n⟮IB.prod 𝓘(𝕜, Fin (whitneySum (trivial 𝕜 B 0) A).rank → 𝕜),
        IB.prod 𝓘(𝕜, Fin A.rank → 𝕜)⟯ A.core.TotalSpace :=
  CoordinateHom.toDiffeomorphOfInv (whitneyZeroLeftIso A).hom (whitneyZeroLeftIso A).inv
    (whitneyZeroLeftIso A).hom_inv_id (whitneyZeroLeftIso A).inv_hom_id
    (by simpa only [whitneyZeroLeftIso_hom] using
      contMDiff_totalSpaceMap_whitneySnd (trivial 𝕜 B 0) A)
    (by simpa only [whitneyZeroLeftIso_inv] using
      contMDiff_totalSpaceMap_whitneyInr (trivial 𝕜 B 0) A)

@[simp]
theorem coe_whitneyZeroLeftDiffeomorph (IB : ModelWithCorners 𝕜 EB HB) (n : WithTop ℕ∞)
    (A : FiniteRankBundleCore 𝕜 B) :
    ⇑(whitneyZeroLeftDiffeomorph IB n A) =
      (whitneySnd (trivial 𝕜 B 0) A).totalSpaceMap := by
  simp [whitneyZeroLeftDiffeomorph]

@[simp]
theorem coe_whitneyZeroLeftDiffeomorph_symm (IB : ModelWithCorners 𝕜 EB HB) (n : WithTop ℕ∞)
    (A : FiniteRankBundleCore 𝕜 B) :
    ⇑(whitneyZeroLeftDiffeomorph IB n A).symm =
      (whitneyInr (trivial 𝕜 B 0) A).totalSpaceMap := by
  simp [whitneyZeroLeftDiffeomorph]

/-- Right unit `C^n` diffeomorphism for Whitney sum with the trivial rank-zero core. -/
def whitneyZeroRightDiffeomorph (IB : ModelWithCorners 𝕜 EB HB) (n : WithTop ℕ∞)
    (A : FiniteRankBundleCore 𝕜 B) :
    (whitneySum A (trivial 𝕜 B 0)).core.TotalSpace
      ≃ₘ^n⟮IB.prod 𝓘(𝕜, Fin (whitneySum A (trivial 𝕜 B 0)).rank → 𝕜),
        IB.prod 𝓘(𝕜, Fin A.rank → 𝕜)⟯ A.core.TotalSpace :=
  CoordinateHom.toDiffeomorphOfInv (whitneyZeroRightIso A).hom (whitneyZeroRightIso A).inv
    (whitneyZeroRightIso A).hom_inv_id (whitneyZeroRightIso A).inv_hom_id
    (by simpa only [whitneyZeroRightIso_hom] using
      contMDiff_totalSpaceMap_whitneyFst A (trivial 𝕜 B 0))
    (by simpa only [whitneyZeroRightIso_inv] using
      contMDiff_totalSpaceMap_whitneyInl A (trivial 𝕜 B 0))

@[simp]
theorem coe_whitneyZeroRightDiffeomorph (IB : ModelWithCorners 𝕜 EB HB) (n : WithTop ℕ∞)
    (A : FiniteRankBundleCore 𝕜 B) :
    ⇑(whitneyZeroRightDiffeomorph IB n A) =
      (whitneyFst A (trivial 𝕜 B 0)).totalSpaceMap := by
  simp [whitneyZeroRightDiffeomorph]

@[simp]
theorem coe_whitneyZeroRightDiffeomorph_symm (IB : ModelWithCorners 𝕜 EB HB) (n : WithTop ℕ∞)
    (A : FiniteRankBundleCore 𝕜 B) :
    ⇑(whitneyZeroRightDiffeomorph IB n A).symm =
      (whitneyInl A (trivial 𝕜 B 0)).totalSpaceMap := by
  simp [whitneyZeroRightDiffeomorph]

end Diffeomorph

section MathlibProd

private theorem prod_trivializationAt_eq (A D : FiniteRankBundleCore 𝕜 B) (b : B) :
    trivializationAt ((Fin A.rank → 𝕜) × (Fin D.rank → 𝕜)) (A.core.Fiber ×ᵇ D.core.Fiber) b =
      (A.core.localTriv b).prod (D.core.localTriv b) := by
  refine (FiberBundle.prod_trivializationAt' (Fin A.rank → 𝕜) A.core.Fiber
    (Fin D.rank → 𝕜) D.core.Fiber b).trans ?_
  rw [A.trivializationAt_core, D.trivializationAt_core]

/-- `whitneySumTotalSpaceHomeomorph` is `C^n` on total spaces without any `C^n` assumption on the
cores or completeness of `𝕜`. -/
theorem contMDiff_whitneySumTotalSpaceHomeomorph (A D : FiniteRankBundleCore 𝕜 B) :
    ContMDiff (IB.prod 𝓘(𝕜, Fin (whitneySum A D).rank → 𝕜))
      (IB.prod 𝓘(𝕜, (Fin A.rank → 𝕜) × (Fin D.rank → 𝕜))) n
      (whitneySumTotalSpaceHomeomorph A D) :=
  (whitneySum A D).contMDiff_of_localTriv_snd (whitneySumTotalSpaceHomeomorph A D)
    (fun p ↦ by simp) (splitCoords (𝕜 := 𝕜) A.rank D.rank).toContinuousLinearMap fun b p ↦ by
      rw [prod_trivializationAt_eq, whitneySumTotalSpaceHomeomorph_apply]
      exact localTriv_prod_whitneySumFiberEquiv A D b p

/-- The inverse of `whitneySumTotalSpaceHomeomorph` is `C^n` on total spaces without any `C^n`
assumption on the cores or completeness of `𝕜`. -/
theorem contMDiff_whitneySumTotalSpaceHomeomorph_symm (A D : FiniteRankBundleCore 𝕜 B) :
    ContMDiff (IB.prod 𝓘(𝕜, (Fin A.rank → 𝕜) × (Fin D.rank → 𝕜)))
      (IB.prod 𝓘(𝕜, Fin (whitneySum A D).rank → 𝕜)) n
      (whitneySumTotalSpaceHomeomorph A D).symm := by
  intro p₀
  rw [Bundle.contMDiffAt_totalSpace_iff]
  simp only [whitneySumTotalSpaceHomeomorph_symm_apply]
  refine ⟨(contMDiff_proj _).contMDiffAt, ?_⟩
  let S' : ((Fin A.rank → 𝕜) × (Fin D.rank → 𝕜)) →L[𝕜] (Fin (whitneySum A D).rank → 𝕜) :=
    (splitCoords (𝕜 := 𝕜) A.rank D.rank).symm.toContinuousLinearMap
  refine (S'.contDiff.comp_contMDiffAt
    (p₀.contMDiffAt_trivializationAt_snd (IB := IB) (n := n))).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun q ↦ ?_)
  dsimp only [Function.comp_apply]
  rw [(whitneySum A D).trivializationAt_core, prod_trivializationAt_eq]
  exact localTriv_whitneySumFiberEquiv_symm A D p₀.proj q

/-- The reconstructed total space of the Whitney sum is `C^n`-diffeomorphic (and, over `𝓘(ℂ, EB)`
with `n = ∞`, biholomorphic) to the total space of Mathlib's native direct-sum vector bundle
`A.core.Fiber ×ᵇ D.core.Fiber`, over the identity of the base and by `whitneySumFiberEquiv` on each
fibre. -/
def whitneySumTotalSpaceDiffeomorph (IB : ModelWithCorners 𝕜 EB HB) (n : WithTop ℕ∞)
    (A D : FiniteRankBundleCore 𝕜 B) :
    (whitneySum A D).core.TotalSpace
      ≃ₘ^n⟮IB.prod 𝓘(𝕜, Fin (whitneySum A D).rank → 𝕜),
        IB.prod 𝓘(𝕜, (Fin A.rank → 𝕜) × (Fin D.rank → 𝕜))⟯
      TotalSpace ((Fin A.rank → 𝕜) × (Fin D.rank → 𝕜)) (A.core.Fiber ×ᵇ D.core.Fiber) where
  toEquiv := (whitneySumTotalSpaceHomeomorph A D).toEquiv
  contMDiff_toFun := contMDiff_whitneySumTotalSpaceHomeomorph A D
  contMDiff_invFun := contMDiff_whitneySumTotalSpaceHomeomorph_symm A D

@[simp]
theorem whitneySumTotalSpaceDiffeomorph_apply (IB : ModelWithCorners 𝕜 EB HB) (n : WithTop ℕ∞)
    (A D : FiniteRankBundleCore 𝕜 B) (p : (whitneySum A D).core.TotalSpace) :
    whitneySumTotalSpaceDiffeomorph IB n A D p =
      ⟨p.proj, whitneySumFiberEquiv A D p.proj p.2⟩ :=
  whitneySumTotalSpaceHomeomorph_apply A D p

@[simp]
theorem whitneySumTotalSpaceDiffeomorph_symm_apply (IB : ModelWithCorners 𝕜 EB HB) (n : WithTop ℕ∞)
    (A D : FiniteRankBundleCore 𝕜 B)
    (p : TotalSpace ((Fin A.rank → 𝕜) × (Fin D.rank → 𝕜)) (A.core.Fiber ×ᵇ D.core.Fiber)) :
    (whitneySumTotalSpaceDiffeomorph IB n A D).symm p =
      ⟨p.proj, (whitneySumFiberEquiv A D p.proj).symm p.2⟩ :=
  whitneySumTotalSpaceHomeomorph_symm_apply A D p

@[simp]
theorem toHomeomorph_whitneySumTotalSpaceDiffeomorph (IB : ModelWithCorners 𝕜 EB HB)
    (n : WithTop ℕ∞) (A D : FiniteRankBundleCore 𝕜 B) :
    (whitneySumTotalSpaceDiffeomorph IB n A D).toHomeomorph =
      whitneySumTotalSpaceHomeomorph A D :=
  Homeomorph.ext fun _ ↦ rfl

/-- `whitneySumTotalSpaceDiffeomorph` intertwines `whitneyMap f g` on the Whitney sum with the
componentwise action of `f` and `g` on Mathlib's direct-sum bundle. -/
theorem whitneySumTotalSpaceDiffeomorph_naturality (IB : ModelWithCorners 𝕜 EB HB) (n : WithTop ℕ∞)
    {A A' D D' : FiniteRankBundleCore 𝕜 B} (f : A ⟶ A') (g : D ⟶ D')
    (p : (whitneySum A D).core.TotalSpace) :
    whitneySumTotalSpaceDiffeomorph IB n A' D' ((whitneyMap f g).totalSpaceMap p) =
      ⟨p.proj, (f.fiberMap p.proj (whitneySumTotalSpaceDiffeomorph IB n A D p).2.1,
        g.fiberMap p.proj (whitneySumTotalSpaceDiffeomorph IB n A D p).2.2)⟩ :=
  whitneySumTotalSpaceHomeomorph_naturality f g p

end MathlibProd

end TauCeti.FiniteRankBundleCore
