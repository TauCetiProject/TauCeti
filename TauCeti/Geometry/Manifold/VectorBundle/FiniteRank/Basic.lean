/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Trivialization
public import TauCeti.Topology.VectorBundle.FiniteRank.Basic

/-!
# `C^n` local fibre coordinates of finite-rank bundle cores

For a point-indexed finite-rank vector-bundle core `E : FiniteRankBundleCore 𝕜 B` over a charted
space `B`, the preferred trivialization at a base point `x` is the chart `E.core.localTriv x`
(`FiniteRankBundleCore.trivializationAt_core`). Consequently, the fibre coordinate in
`E.core.localTriv p₀.proj` is `C^n` at every total-space point `p₀`, without any smoothness
hypothesis on the base atlas or on the transition functions of `E`.

This yields general `C^n` criteria for morphisms and bundle maps whose local coordinates are
intertwined by a fixed continuous linear map `L`:
* `FiniteRankBundleCore.contMDiff_of_localTriv_snd` and
  `FiniteRankBundleCore.contMDiff_totalSpaceMap_of_coordChange` establish `C^n` regularity on total
  spaces without `C^n` assumptions on the cores;
* `FiniteRankBundleCore.contMDiffOn_inChartCoordinates_of_coordChange_comp` and
  `FiniteRankBundleCore.contMDiffOn_inChartCoordinates_of_comp_coordChange` establish `C^n`
  regularity of chart operators when the relevant core is `C^n`.
-/

public section

open Bundle CategoryTheory
open scoped Manifold ContDiff

namespace TauCeti.FiniteRankBundleCore

variable {𝕜 B : Type*} [NontriviallyNormedField 𝕜] {n : WithTop ℕ∞}
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners 𝕜 EB HB}
  [TopologicalSpace B] [ChartedSpace HB B]

/-- For any point-indexed finite-rank core `E`, the fibre coordinate in the chart at `p₀.proj` is
`C^n` at `p₀`. -/
theorem contMDiffAt_localTriv_snd (E : FiniteRankBundleCore 𝕜 B) (p₀ : E.core.TotalSpace) :
    ContMDiffAt (IB.prod 𝓘(𝕜, Fin E.rank → 𝕜)) 𝓘(𝕜, Fin E.rank → 𝕜) n
      (fun p : E.core.TotalSpace ↦ (E.core.localTriv p₀.proj p).2) p₀ := by
  simpa only [E.trivializationAt_core] using
    p₀.contMDiffAt_trivializationAt_snd (IB := IB) (n := n)

/-- A map from `E.core.TotalSpace` into the total space of a fibre bundle `V` covering the
identity of `B` whose fibre coordinate in every preferred trivialization is a fixed continuous
linear map `L` of the chart coordinate in `E` is `C^n`, without any smoothness hypothesis on the
base or transition functions. -/
theorem contMDiff_of_localTriv_snd {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {V : B → Type*} [TopologicalSpace (TotalSpace F V)] [∀ x, TopologicalSpace (V x)]
    [FiberBundle F V] (E : FiniteRankBundleCore 𝕜 B) (f : E.core.TotalSpace → TotalSpace F V)
    (hf_proj : ∀ p, (f p).proj = p.proj) (L : (Fin E.rank → 𝕜) →L[𝕜] F)
    (hL : ∀ (b : B) (p : E.core.TotalSpace),
      (trivializationAt F V b (f p)).2 = L ((E.core.localTriv b p).2)) :
    ContMDiff (IB.prod 𝓘(𝕜, Fin E.rank → 𝕜)) (IB.prod 𝓘(𝕜, F)) n f := by
  intro p₀
  rw [Bundle.contMDiffAt_totalSpace, hf_proj p₀]
  refine ⟨((contMDiff_proj E.core.Fiber).congr hf_proj).contMDiffAt, ?_⟩
  exact (L.contDiff.comp_contMDiffAt (E.contMDiffAt_localTriv_snd p₀)).congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun p ↦ hL p₀.proj p)

/-- A morphism `a : E ⟶ E'` of point-indexed finite-rank cores whose fibre maps intertwine the
point-to-chart transitions with a fixed continuous linear map `L` glues to a `C^n` map of total
spaces, without any smoothness assumption on the base or on the cores. -/
theorem contMDiff_totalSpaceMap_of_coordChange {E E' : FiniteRankBundleCore 𝕜 B} (a : E ⟶ E')
    (L : (Fin E.rank → 𝕜) →L[𝕜] (Fin E'.rank → 𝕜))
    (hL : ∀ x b v, E'.core.coordChange x b x (a.fiberMap x v) = L (E.core.coordChange x b x v)) :
    ContMDiff (IB.prod 𝓘(𝕜, Fin E.rank → 𝕜)) (IB.prod 𝓘(𝕜, Fin E'.rank → 𝕜)) n
      a.totalSpaceMap := by
  refine E.contMDiff_of_localTriv_snd a.totalSpaceMap a.totalSpaceMap_proj L fun b ⟨x, v⟩ ↦ ?_
  rw [E'.trivializationAt_core]
  simp only [VectorBundleCore.CoordinateHom.totalSpaceMap_mk, VectorBundleCore.localTriv_apply,
    E.indexAt_eq, E'.indexAt_eq]
  exact hL x b v

/-- If `E.core.baseSet i ⊆ E'.core.baseSet i`, `E'` is a `C^n` core, and `a : E ⟶ E'` intertwines
the transitions from `i` to each point `x` with a fixed continuous linear map `L`, then the
`(i, j)` chart operator of `a` is `C^n` on `E.core.baseSet i ∩ E'.core.baseSet j`. -/
theorem contMDiffOn_inChartCoordinates_of_coordChange_comp {E E' : FiniteRankBundleCore 𝕜 B}
    [E'.core.IsContMDiff IB n] (a : E ⟶ E') {i j : B}
    (hbase : E.core.baseSet i ⊆ E'.core.baseSet i)
    (L : (Fin E.rank → 𝕜) →L[𝕜] (Fin E'.rank → 𝕜))
    (hL : ∀ x ∈ E.core.baseSet i ∩ E'.core.baseSet j, ∀ v,
      a.fiberMap x (E.core.coordChange i x x v) = E'.core.coordChange i x x (L v)) :
    ContMDiffOn IB 𝓘(𝕜, (Fin E.rank → 𝕜) →L[𝕜] (Fin E'.rank → 𝕜)) n
      (fun x ↦ E.core.inChartCoordinates E'.core i j x (a.fiberMap x))
      (E.core.baseSet i ∩ E'.core.baseSet j) := by
  -- On the overlap, the `(i, j)` chart operator equals `(E'.core.coordChange i j ·).comp L`.
  have hE' : ContMDiffOn IB 𝓘(𝕜, (Fin E'.rank → 𝕜) →L[𝕜] (Fin E'.rank → 𝕜)) n
      (E'.core.coordChange i j) (E.core.baseSet i ∩ E'.core.baseSet j) :=
    (E'.core.contMDiffOn_coordChange IB i j).mono fun _ h ↦ ⟨hbase h.1, h.2⟩
  refine (hE'.clm_comp (contMDiffOn_const (c := L))).congr fun x hx ↦ ?_
  ext v : 1
  rw [inChartCoordinates_core_apply, hL x hx v, ContinuousLinearMap.comp_apply]
  exact E'.core.coordChange_comp i x j x ⟨⟨hbase hx.1, E'.mem_baseSet_self x⟩, hx.2⟩ (L v)

/-- If `E'.core.baseSet j ⊆ E.core.baseSet j`, `E` is a `C^n` core, and `a : E ⟶ E'` intertwines
the transitions from each point `x` to `j` with a fixed continuous linear map `L`, then the
`(i, j)` chart operator of `a` is `C^n` on `E.core.baseSet i ∩ E'.core.baseSet j`. -/
theorem contMDiffOn_inChartCoordinates_of_comp_coordChange {E E' : FiniteRankBundleCore 𝕜 B}
    [E.core.IsContMDiff IB n] (a : E ⟶ E') {i j : B}
    (hbase : E'.core.baseSet j ⊆ E.core.baseSet j)
    (L : (Fin E.rank → 𝕜) →L[𝕜] (Fin E'.rank → 𝕜))
    (hL : ∀ x ∈ E.core.baseSet i ∩ E'.core.baseSet j, ∀ v,
      E'.core.coordChange x j x (a.fiberMap x v) = L (E.core.coordChange x j x v)) :
    ContMDiffOn IB 𝓘(𝕜, (Fin E.rank → 𝕜) →L[𝕜] (Fin E'.rank → 𝕜)) n
      (fun x ↦ E.core.inChartCoordinates E'.core i j x (a.fiberMap x))
      (E.core.baseSet i ∩ E'.core.baseSet j) := by
  -- On the overlap, the `(i, j)` chart operator equals `L.comp (E.core.coordChange i j ·)`.
  have hE : ContMDiffOn IB 𝓘(𝕜, (Fin E.rank → 𝕜) →L[𝕜] (Fin E.rank → 𝕜)) n
      (E.core.coordChange i j) (E.core.baseSet i ∩ E'.core.baseSet j) :=
    (E.core.contMDiffOn_coordChange IB i j).mono fun _ h ↦ ⟨h.1, hbase h.2⟩
  refine ((contMDiffOn_const (c := L)).clm_comp hE).congr fun x hx ↦ ?_
  ext v : 1
  rw [inChartCoordinates_core_apply, hL x hx, ContinuousLinearMap.comp_apply,
    E.core.coordChange_comp i x j x ⟨⟨hx.1, E.mem_baseSet_self x⟩, hbase hx.2⟩]

end TauCeti.FiniteRankBundleCore
