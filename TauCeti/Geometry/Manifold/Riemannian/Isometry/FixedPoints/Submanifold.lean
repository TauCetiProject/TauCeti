/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.GroupAction.FixedTangentSubspace
public import TauCeti.Geometry.Manifold.Riemannian.Isometry.FixedPoints
public import TauCeti.Geometry.Manifold.LinearSlice
public import TauCeti.Geometry.Manifold.TangentCone.Basic

import TauCeti.Topology.Algebra.ConstMulAction

/-!
# The fixed set of a group of isometries is an embedded submanifold

Let a group `K` act on a Riemannian manifold `M` by smooth isometries. No topology or Lie group
structure on `K` is required. Near each point `p` of the common fixed set `M^K`, the Riemannian
logarithm at `p` is a smooth chart flattening `M^K` onto the subspace

`V_p = {v ∈ T_p M | d(k •)_p v = v for every k ∈ K}`

(`TauCeti.fixedTangentSubspace I K p`, defined for any group action), by
`TauCeti.exists_isSliceChart_fixedPoints`. This file
turns these slice charts into embedded submanifold structures.

* **Local constancy of the dimension.** A chart of the maximal atlas flattening `M^K` onto a
  subspace near a point `z` of `M^K` determines the dimension of the span of the tangent cone of
  `M^K` at `z` (`TauCeti.IsSliceChart.finrank_span_mtangentConeAt`). Comparing the slice chart at
  `p` with the slice chart at a nearby fixed point `z` gives `dim V_z = dim V_p`
  (`TauCeti.finrank_fixedTangentSubspace_eq_of_mem_source`). So `z ↦ dim V_z` is locally constant
  on `M^K` (`TauCeti.isLocallyConstant_finrank_fixedTangentSubspace`), and every connected subset
  of `M^K` lies in one of the sets
  `M^K_d = {p ∈ M^K | dim V_p = d}` (`TauCeti.fixedPointsOfFinrank I K M d`)
  (`TauCeti.subset_fixedPointsOfFinrank_of_isPreconnected`). Different components may have
  different dimensions. Since the fixed set is closed, each `M^K_d` is closed in `M`
  (`TauCeti.isClosed_fixedPointsOfFinrank`).
* **Submanifold structure.** For a subspace `L` of the model of dimension `d`, the set `M^K_d` is a
  smooth manifold modelled on `L` whose inclusion into `M` is a smooth embedding, and the tangent
  image of the inclusion at each point `p` is exactly `V_p`
  (`TauCeti.exists_isSmoothEmbedding_fixedPointsOfFinrank`). The inclusion `⊆` holds because
  every `k •` is the identity on `M^K`, so its differential fixes the tangent image of the
  inclusion; equality follows by counting dimensions, the differential of an embedding being
  injective.

Neither completeness of the metric nor compactness of `M` or `K` is used. The ambient manifold is
modelled on a finite-dimensional real normed space with charts in that space, the setting of the
tangent cones of subsets (`TauCeti.mtangentConeAt`) which detect the dimension, and of the
embedded submanifold structures induced by slice charts
(`TauCeti.exists_isSmoothEmbedding_of_finrankSubspaceCharts`).

## Main results

* `TauCeti.isOpen_preimage_val_fixedPointsOfFinrank`: the sets `M^K_d`, which partition the fixed
  set, are open in it.
* `TauCeti.isClosed_fixedPointsOfFinrank`: each `M^K_d` is closed in `M`.
* `TauCeti.finrank_fixedTangentSubspace_eq_of_mem_source`,
  `TauCeti.isLocallyConstant_finrank_fixedTangentSubspace`: the dimension of the fixed tangent
  subspace is locally constant on the fixed set.
* `TauCeti.subset_fixedPointsOfFinrank_of_isPreconnected`: a connected subset of the fixed set has a
  single dimension.
* `TauCeti.exists_isSmoothEmbedding_fixedPointsOfFinrank`: each `M^K_d` is a smooth embedded
  submanifold with tangent spaces the fixed tangent subspaces.

## References

* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Homework 21, exercise 2.
* S. Kobayashi, *Fixed points of isometries*, Nagoya Mathematical Journal 13 (1958), 63–68.
-/

public section

open Bundle Manifold Set MulAction
open scoped ContDiff Manifold

noncomputable section

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]
  [RiemannianBundle (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, E) ∞ E (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x)]
  {K : Type*} [Group K] [MulAction K M] [ContMDiffConstSMul 𝓘(ℝ, E) ∞ K M]
  (hK : ∀ (k : K) (x : M) (u w : TangentSpace 𝓘(ℝ, E) x),
    inner ℝ (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (k • ·) x u) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (k • ·) x w) =
      inner ℝ u w)

include hK

/-- A slice chart for the fixed set at a fixed point `p`, onto the fixed tangent subspace at `p`,
which is a chart of the maximal smooth atlas. -/
private theorem exists_mem_maximalAtlas_isSliceChart {p : M}
    (hp : p ∈ MulAction.fixedPoints K M) :
    ∃ q : OpenPartialHomeomorph M E, q ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M ∧ p ∈ q.source ∧
      IsSliceChart q (SetLike.coe (fixedTangentSubspace 𝓘(ℝ, E) K p))
        (MulAction.fixedPoints K M) := by
  obtain ⟨φ, hpφ, -, -, hφ⟩ := exists_isSliceChart_fixedPoints hK hp
  -- The chart takes values in `T_p M` with its Riemannian norm; the identity of the underlying
  -- topological vector space compares it with the model `E`.
  let ι : TangentSpace 𝓘(ℝ, E) p →L[ℝ] E := ⟨LinearMap.id, continuous_id⟩
  let ι' : E →L[ℝ] TangentSpace 𝓘(ℝ, E) p := ⟨LinearMap.id, continuous_id⟩
  refine ⟨φ.toOpenPartialHomeomorph,
    OpenPartialHomeomorph.mem_maximalAtlas_of_contMDiffOn _
      (ι.contMDiff.comp_contMDiffOn φ.contMDiffOn_toFun)
      (φ.contMDiffOn_invFun.comp ι'.contMDiff.contMDiffOn fun _ hz ↦ hz), hpφ,
    isSliceChart_iff.2 fun z hz ↦ (isSliceChart_iff.1 hφ z hz).trans
      (mem_fixedTangentSubspace_iff_of_mem_fixedPoints hp).symm⟩

/-- **The dimension of the fixed tangent subspace is constant near a fixed point.** If a chart of
the maximal smooth atlas flattens the fixed set onto the fixed tangent subspace at `p`, then at
every fixed point `z` of its source the fixed tangent subspace has the same dimension as at `p`.
-/
theorem finrank_fixedTangentSubspace_eq_of_mem_source {p z : M} {q : OpenPartialHomeomorph M E}
    (hq : q ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M)
    (hs : IsSliceChart q (SetLike.coe (fixedTangentSubspace 𝓘(ℝ, E) K p))
      (MulAction.fixedPoints K M))
    (hz : z ∈ q.source) (hzK : z ∈ MulAction.fixedPoints K M) :
    Module.finrank ℝ (fixedTangentSubspace 𝓘(ℝ, E) K z) =
      Module.finrank ℝ (fixedTangentSubspace 𝓘(ℝ, E) K p) := by
  obtain ⟨q', hq', hzq', hs'⟩ := exists_mem_maximalAtlas_isSliceChart hK hzK
  -- Both slice charts compute the dimension of the tangent space of the fixed set at `z`. The
  -- fixed tangent subspaces are closed in the topology of `T_p M`, which is that of `E`.
  have hp := hs.finrank_span_mtangentConeAt (E := E)
    (L := fixedTangentSubspace 𝓘(ℝ, E) K p)
    (n := ∞) (by simp) hq
    (by exact (fixedTangentSubspace 𝓘(ℝ, E) K p).isClosed_of_finiteDimensional) hz hzK
  have hz' := hs'.finrank_span_mtangentConeAt (E := E)
    (L := fixedTangentSubspace 𝓘(ℝ, E) K z)
    (n := ∞) (by simp) hq'
    (by exact (fixedTangentSubspace 𝓘(ℝ, E) K z).isClosed_of_finiteDimensional) hzq' hzK
  exact hz'.symm.trans hp

/-- **The dimension of the fixed tangent subspace is locally constant on the fixed set.** -/
theorem isLocallyConstant_finrank_fixedTangentSubspace :
    IsLocallyConstant fun z : MulAction.fixedPoints K M ↦
      Module.finrank ℝ (fixedTangentSubspace 𝓘(ℝ, E) K (z : M)) := by
  refine (IsLocallyConstant.iff_eventually_eq _).2 fun p ↦ ?_
  obtain ⟨q, hq, hpq, hs⟩ := exists_mem_maximalAtlas_isSliceChart hK p.property
  filter_upwards [continuous_subtypeVal.continuousAt.preimage_mem_nhds
    (q.open_source.mem_nhds hpq)] with z hz
  exact finrank_fixedTangentSubspace_eq_of_mem_source hK hq hs hz z.property

/-- Each part of the fixed set of a given dimension is open in the fixed set. -/
theorem isOpen_preimage_val_fixedPointsOfFinrank (d : ℕ) :
    IsOpen ((↑) ⁻¹' fixedPointsOfFinrank 𝓘(ℝ, E) K M d :
      Set (MulAction.fixedPoints K M)) := by
  convert (isLocallyConstant_finrank_fixedTangentSubspace hK).isOpen_fiber d using 1
  ext z
  exact mem_fixedPointsOfFinrank.trans (and_iff_right z.property)

/-- **Each part of the fixed set of a given dimension is closed.** The fixed set is closed, and the
part of it on which the fixed tangent subspace has dimension `d` is a fiber of a locally constant
function on it. -/
theorem isClosed_fixedPointsOfFinrank (d : ℕ) :
    IsClosed (fixedPointsOfFinrank 𝓘(ℝ, E) K M d) := by
  have : ContinuousConstSMul K M :=
    ⟨fun k ↦ (contMDiff_const_smul (I := 𝓘(ℝ, E)) (n := ∞) k).continuous⟩
  have hcl : IsClosed (MulAction.fixedPoints K M) := isClosed_fixedPoints_of_continuousConstSMul
  convert hcl.isClosedEmbedding_subtypeVal.isClosedMap _
    ((isLocallyConstant_finrank_fixedTangentSubspace hK).isClosed_fiber d) using 1
  ext z
  refine ⟨fun hz ↦ ⟨⟨z, (mem_fixedPointsOfFinrank.1 hz).1⟩, (mem_fixedPointsOfFinrank.1 hz).2, rfl⟩,
    ?_⟩
  rintro ⟨y, hy, rfl⟩
  exact mem_fixedPointsOfFinrank.2 ⟨y.property, hy⟩

/-- **A connected part of the fixed set has a single dimension.** A preconnected subset of the
fixed set containing a point `p` lies in the part of the fixed set where the fixed tangent
subspace has the dimension it has at `p`; in particular so does the connected component of `p`
in the fixed set. -/
theorem subset_fixedPointsOfFinrank_of_isPreconnected {C : Set M} (hC : IsPreconnected C)
    (hCK : C ⊆ MulAction.fixedPoints K M) {p : M} (hp : p ∈ C) :
    C ⊆ fixedPointsOfFinrank 𝓘(ℝ, E) K M
      (Module.finrank ℝ (fixedTangentSubspace 𝓘(ℝ, E) K p)) := by
  intro z hz
  have hC' : IsPreconnected ((↑) ⁻¹' C : Set (MulAction.fixedPoints K M)) :=
    Topology.IsInducing.subtypeVal.isPreconnected_image.1 (by
      rwa [Subtype.image_preimage_coe, inter_eq_right.2 hCK])
  exact mem_fixedPointsOfFinrank.2 ⟨hCK hz,
    (isLocallyConstant_finrank_fixedTangentSubspace hK).apply_eq_of_isPreconnected
      hC' (x := ⟨z, hCK hz⟩) (y := ⟨p, hCK hp⟩) hz hp⟩

/-- **The fixed set of a group of isometries is an embedded submanifold.** For a subspace `L` of
the model of dimension `d`, the points of the fixed set at which the fixed tangent subspace has
dimension `d` form a smooth manifold modelled on `L`, whose inclusion into `M` is a smooth
embedding with tangent image the fixed tangent subspace at every point. -/
theorem exists_isSmoothEmbedding_fixedPointsOfFinrank {d : ℕ} {L : Submodule ℝ E}
    (hL : Module.finrank ℝ L = d) :
    ∃ C : ChartedSpace L (fixedPointsOfFinrank 𝓘(ℝ, E) K M d), letI := C
      IsManifold 𝓘(ℝ, L) ∞ (fixedPointsOfFinrank 𝓘(ℝ, E) K M d) ∧
      IsSmoothEmbedding 𝓘(ℝ, L) 𝓘(ℝ, E) ∞
        (Subtype.val : fixedPointsOfFinrank 𝓘(ℝ, E) K M d → M) ∧
      ∀ y : fixedPointsOfFinrank 𝓘(ℝ, E) K M d,
        LinearMap.range (mfderiv 𝓘(ℝ, L) 𝓘(ℝ, E) Subtype.val y).toLinearMap =
          fixedTangentSubspace 𝓘(ℝ, E) K (y : M) := by
  obtain ⟨C, hman, hemb⟩ := exists_isSmoothEmbedding_of_finrankSubspaceCharts (L := L)
    (n := ∞) (t := fixedPointsOfFinrank 𝓘(ℝ, E) K M d) fun y hy ↦ by
      obtain ⟨hyK, hyd⟩ := mem_fixedPointsOfFinrank.1 hy
      obtain ⟨q, hq, hyq, hs⟩ := exists_mem_maximalAtlas_isSliceChart hK hyK
      refine ⟨q, fixedTangentSubspace 𝓘(ℝ, E) K y, hyq,
        fun z hz ↦ (contMDiffOn_of_mem_maximalAtlas hq).contMDiffAt (q.open_source.mem_nhds hz),
        fun z hz ↦ (contMDiffOn_symm_of_mem_maximalAtlas hq).contMDiffAt
          (q.open_target.mem_nhds hz), fun z hz ↦ ?_, hyd.trans hL.symm⟩
      refine ⟨fun hzd ↦ (isSliceChart_iff.1 hs z hz).1 (mem_fixedPointsOfFinrank.1 hzd).1,
        fun hzV ↦ ?_⟩
      have hzK := (isSliceChart_iff.1 hs z hz).2 hzV
      exact mem_fixedPointsOfFinrank.2
        ⟨hzK, (finrank_fixedTangentSubspace_eq_of_mem_source hK hq hs hz hzK).trans hyd⟩
  let := C
  refine ⟨C, hman, hemb, fun y ↦ ?_⟩
  have hle : LinearMap.range (mfderiv 𝓘(ℝ, L) 𝓘(ℝ, E) Subtype.val y).toLinearMap ≤
      fixedTangentSubspace 𝓘(ℝ, E) K (y : M) := by
    rintro _ ⟨u, rfl⟩
    refine mem_fixedTangentSubspace.2 fun k _ ↦ ?_
    -- Every `k •` is the identity on the fixed set, so it fixes the tangent image of `val`.
    have hcomp : ((k • ·) ∘ Subtype.val : fixedPointsOfFinrank 𝓘(ℝ, E) K M d → M) =
        Subtype.val := funext fun z ↦ (mem_fixedPointsOfFinrank.1 z.property).1 k
    have h := mfderiv_comp y
      ((contMDiff_const_smul (I := 𝓘(ℝ, E)) (n := ∞) k).mdifferentiableAt (by simp))
      (hemb.contMDiff.mdifferentiableAt (by simp) (x := y))
    rw [hcomp] at h
    exact (congrArg (fun A ↦ A u) h).symm
  refine Submodule.eq_of_le_of_finrank_eq hle ?_
  rw [LinearMap.finrank_range_of_inj (hemb.isImmersion.mfderiv_injective (by simp) y),
    (mem_fixedPointsOfFinrank.1 y.property).2]
  exact hL

end TauCeti
