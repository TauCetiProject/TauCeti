/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.GroupAction.FixedTangentSubspace
public import TauCeti.Geometry.Manifold.Riemannian.Isometry.FixedPoints
public import TauCeti.Geometry.Manifold.LinearSlice

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

* **Local constancy of the dimension.** If `w ∈ V_p` lies in a normal ball at a fixed point `p`,
  then `q = exp_p w` is fixed, and differentiating the naturality of the exponential map,
  `k • exp_p v = exp_p (d(k •)_p v)`, at `w` shows that the invertible differential
  `D = d(exp_p)_w` conjugates `d(k •)_p` into `d(k •)_q`
  (`TauCeti.mfderiv_smul_mfderiv_riemannianExp`). Hence `D` carries `V_p` onto `V_q`, and the two
  spaces have the same dimension
  (`TauCeti.Manifold.IsNormalDomain.finrank_fixedTangentSubspace_riemannianExp`). So
  `z ↦ dim V_z` is locally constant on `M^K`
  (`TauCeti.isLocallyConstant_finrank_fixedTangentSubspace`), and every connected subset
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
boundaryless and modelled on a finite-dimensional real normed space, the setting of the normal
balls of the exponential map and of the embedded submanifold structures induced by slice charts
(`TauCeti.exists_isSmoothEmbedding_of_finrankSubspaceCharts_of_boundaryless`).

## Main results

* `TauCeti.Manifold.IsNormalDomain.finrank_fixedTangentSubspace_riemannianExp`: `V_{exp_p w}` and
  `V_p` have the same dimension for a fixed vector `w` of a normal domain at a fixed point `p`.
* `TauCeti.isLocallyConstant_finrank_fixedTangentSubspace`: the dimension of the fixed tangent
  subspace is locally constant on the fixed set.
* `TauCeti.isOpen_preimage_val_fixedPointsOfFinrank`: the sets `M^K_d`, which partition the fixed
  set, are open in it.
* `TauCeti.isClosed_fixedPointsOfFinrank`: each `M^K_d` is closed in `M`.
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

open Bundle Manifold Set MulAction Filter Topology
open scoped ContDiff Manifold

noncomputable section

namespace TauCeti

open TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  {K : Type*} [Group K] [MulAction K M] [ContMDiffConstSMul I ∞ K M]
  (hK : ∀ (k : K) (x : M) (u w : TangentSpace I x),
    inner ℝ (mfderiv I I (k • ·) x u) (mfderiv I I (k • ·) x w) = inner ℝ u w)

include hK

/-- **The fixed tangent subspaces along the exponential image of a fixed vector.** For a group
acting by isometries fixing `p`, and a vector `w` of a normal domain at `p` fixed by every
differential `d(k •)_p`, the fixed tangent subspace at `exp_p w` has the same dimension as that
at `p`. -/
theorem Manifold.IsNormalDomain.finrank_fixedTangentSubspace_riemannianExp {p : M}
    {U : Set (TangentSpace I p)} {w : TangentSpace I p} (hU : IsNormalDomain I M p U)
    (hp : p ∈ fixedPoints K M) (hwU : w ∈ U) (hw : ∀ k : K, mfderiv I I (k • ·) p w = w) :
    Module.finrank ℝ (fixedTangentSubspace I K (riemannianExp I M p w)) =
      Module.finrank ℝ (fixedTangentSubspace I K p) := by
  have hq : riemannianExp I M p w ∈ fixedPoints K M := riemannianExp_mem_fixedPoints hK hp hw
  obtain ⟨D, hD⟩ := (hU.isLocalDiffeomorphOn ⟨w, hwU⟩).isInvertible_mfderiv (by simp)
  have hDf : ⇑D = ⇑(mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) w) :=
    congrArg DFunLike.coe hD
  -- The differential of `exp_p` at `w`, as a linear isomorphism `T_p M ≃ T_q M` of the tangent
  -- spaces with their own module structures.
  let De : TangentSpace I p ≃ₗ[ℝ] TangentSpace I (riemannianExp I M p w) := D.toLinearEquiv
  have hDe (v : TangentSpace I p) :
      De v = mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) w v := congrFun hDf v
  -- `De` carries the fixed tangent vectors at `p` onto those at `exp_p w`.
  have hmap : (fixedTangentSubspace I K (riemannianExp I M p w)).comap De.toLinearMap =
      fixedTangentSubspace I K p := by
    ext v
    rw [Submodule.mem_comap, LinearEquiv.coe_coe,
      mem_fixedTangentSubspace_iff_of_mem_fixedPoints hq,
      mem_fixedTangentSubspace_iff_of_mem_fixedPoints hp]
    refine forall_congr' fun k ↦ ?_
    rw [hDe, mfderiv_smul_mfderiv_riemannianExp (hK k) (hp k) (hw k)]
    exact ⟨fun h ↦ De.injective ((hDe _).trans (h.trans (hDe v).symm)),
      fun h ↦ (hDe _).symm.trans ((congrArg De h).trans (hDe v))⟩
  rw [← hmap, Submodule.comap_equiv_eq_map_symm, LinearEquiv.finrank_map_eq]

/-- **The dimension of the fixed tangent subspace is locally constant on the fixed set.** -/
theorem isLocallyConstant_finrank_fixedTangentSubspace :
    IsLocallyConstant fun z : MulAction.fixedPoints K M ↦
      Module.finrank ℝ (fixedTangentSubspace I K (z : M)) := by
  refine (IsLocallyConstant.iff_eventually_eq _).2 fun p ↦ ?_
  obtain ⟨r, -, hU⟩ := exists_isNormalDomain_ball (I := I) (M := M) (p : M)
  filter_upwards [continuous_subtypeVal.continuousAt.preimage_mem_nhds hU.image_mem_nhds]
    with z ⟨w, hw, hwz⟩
  have hz := z.property
  rw [← hwz] at hz ⊢
  exact hU.finrank_fixedTangentSubspace_riemannianExp hK p.property hw
    ((hU.riemannianExp_mem_fixedPoints_iff_of_mem_ball hK p.property hw).1 hz)

/-- Each part of the fixed set of a given dimension is open in the fixed set. -/
theorem isOpen_preimage_val_fixedPointsOfFinrank (d : ℕ) :
    IsOpen ((↑) ⁻¹' fixedPointsOfFinrank I K M d :
      Set (MulAction.fixedPoints K M)) := by
  convert (isLocallyConstant_finrank_fixedTangentSubspace hK).isOpen_fiber d using 1
  ext z
  exact mem_fixedPointsOfFinrank.trans (and_iff_right z.property)

/-- **Each part of the fixed set of a given dimension is closed.** The fixed set is closed, and the
part of it on which the fixed tangent subspace has dimension `d` is a fiber of a locally constant
function on it. -/
theorem isClosed_fixedPointsOfFinrank (d : ℕ) :
    IsClosed (fixedPointsOfFinrank I K M d) := by
  have : ContinuousConstSMul K M :=
    ⟨fun k ↦ (contMDiff_const_smul (I := I) (n := ∞) k).continuous⟩
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
    C ⊆ fixedPointsOfFinrank I K M
      (Module.finrank ℝ (fixedTangentSubspace I K p)) := by
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
    ∃ C : ChartedSpace L (fixedPointsOfFinrank I K M d), letI := C
      IsManifold 𝓘(ℝ, L) ∞ (fixedPointsOfFinrank I K M d) ∧
      IsSmoothEmbedding 𝓘(ℝ, L) I ∞ (Subtype.val : fixedPointsOfFinrank I K M d → M) ∧
      ∀ y : fixedPointsOfFinrank I K M d,
        LinearMap.range (mfderiv 𝓘(ℝ, L) I Subtype.val y).toLinearMap =
          fixedTangentSubspace I K (y : M) := by
  obtain ⟨C, hman, hemb⟩ := exists_isSmoothEmbedding_of_finrankSubspaceCharts_of_boundaryless
    (L := L) (n := ∞) (s := fixedPointsOfFinrank I K M d) (by simp) fun y hy ↦ by
      obtain ⟨hyK, hyd⟩ := mem_fixedPointsOfFinrank.1 hy
      obtain ⟨r, -, hU⟩ := exists_isNormalDomain_ball (I := I) (M := M) y
      let φ := hU.toPartialDiffeomorph.symm
      -- The identity of the model space, from the normed structure of `T_y M` to that of `E`.
      let B : TangentSpace I y ≃L[ℝ] E := ContinuousLinearEquiv.refl ℝ E
      have hφs : φ.source = riemannianExp I M y '' Metric.ball 0 r := by
        simp [φ, PartialDiffeomorph.symm_toPartialEquiv]
      have hφ (z : M) (hz : z ∈ φ.source) : ∃ v ∈ Metric.ball (0 : TangentSpace I y) r,
          riemannianExp I M y v = z ∧ φ z = v := by
        rw [hφs] at hz
        obtain ⟨v, hv, rfl⟩ := hz
        exact ⟨v, hv, rfl, by
          simpa [φ, PartialDiffeomorph.symm_toPartialEquiv] using hU.riemannianLog_riemannianExp hv⟩
      refine ⟨φ.toOpenPartialHomeomorph, fixedTangentSubspace I K y, ?_, fun z hz ↦ ?_,
        fun z hz ↦ ?_, fun z hz ↦ ?_, hyd.trans hL.symm⟩
      · simpa [hφs] using hU.self_mem_image
      · exact B.contDiff.contMDiff.contMDiffAt.comp z
          ((φ.contMDiffOn z hz).contMDiffAt (φ.open_source.mem_nhds hz))
      · exact ((φ.symm.contMDiffOn (B.symm z) hz).contMDiffAt
          (φ.symm.open_source.mem_nhds hz)).comp z B.symm.contDiff.contMDiff.contMDiffAt
      · obtain ⟨v, hv, rfl, hφv⟩ := hφ z hz
        -- Near `y`, the part of dimension `d` is the fixed set, which `φ` flattens onto the fixed
        -- tangent subspace.
        have key : riemannianExp I M y v ∈ fixedPointsOfFinrank I K M d ↔
            ∀ k : K, mfderiv I I (k • ·) y v = v :=
          ⟨fun h ↦ (hU.riemannianExp_mem_fixedPoints_iff_of_mem_ball hK hyK hv).1
            (mem_fixedPointsOfFinrank.1 h).1,
            fun h ↦ mem_fixedPointsOfFinrank.2 ⟨riemannianExp_mem_fixedPoints hK hyK h,
              (hU.finrank_fixedTangentSubspace_riemannianExp hK hyK hv h).trans hyd⟩⟩
        refine key.trans ((mem_fixedTangentSubspace_iff_of_mem_fixedPoints hyK).symm.trans ?_)
        exact Iff.of_eq (congrArg (· ∈ fixedTangentSubspace I K y) hφv.symm)
  let := C
  refine ⟨C, hman, hemb, fun y ↦ ?_⟩
  have hle : LinearMap.range (mfderiv 𝓘(ℝ, L) I Subtype.val y).toLinearMap ≤
      fixedTangentSubspace I K (y : M) := by
    rintro _ ⟨u, rfl⟩
    refine mem_fixedTangentSubspace.2 fun k _ ↦ ?_
    -- Every `k •` is the identity on the fixed set, so it fixes the tangent image of `val`.
    have hcomp : ((k • ·) ∘ Subtype.val : fixedPointsOfFinrank I K M d → M) =
        Subtype.val := funext fun z ↦ (mem_fixedPointsOfFinrank.1 z.property).1 k
    have h := mfderiv_comp y
      ((contMDiff_const_smul (I := I) (n := ∞) k).mdifferentiableAt (by simp))
      (hemb.contMDiff.mdifferentiableAt (by simp) (x := y))
    rw [hcomp] at h
    exact (congrArg (fun A ↦ A u) h).symm
  refine Submodule.eq_of_le_of_finrank_eq hle ?_
  rw [LinearMap.finrank_range_of_inj (hemb.isImmersion.mfderiv_injective (by simp) y),
    (mem_fixedPointsOfFinrank.1 y.property).2]
  exact hL

end TauCeti
