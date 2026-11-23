/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.GroupAction.FixedTangentSubspace
public import TauCeti.Geometry.Manifold.Riemannian.Isometry.FixedPoints
public import TauCeti.Geometry.Manifold.LinearSlice

import TauCeti.Geometry.Manifold.Riemannian.Isometry.FixedPoints.Components
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
  (`TauCeti.mfderiv_smul_mfderiv_riemannianExp`). Hence `D` carries `V_p` onto `V_q`
  (`TauCeti.comap_mfderiv_riemannianExp_fixedTangentSubspace`), and the two
  spaces have the same dimension
  (`TauCeti.Manifold.IsNormalDomain.finrank_fixedTangentSubspace_riemannianExp`). So
  `z ↦ dim V_z` is locally constant on `M^K`
  (`TauCeti.isLocallyConstant_finrank_fixedTangentSubspace`), and every connected subset
  of `M^K` lies in one of the sets
  `M^K_d = {p ∈ M^K | dim V_p = d}` (`TauCeti.fixedPointsOfFinrank I K M d`)
  (`TauCeti.subset_fixedPointsOfFinrank_of_isPreconnected`). Different components may have
  different dimensions. Since the fixed set is closed, each `M^K_d` is closed in `M`
  (`TauCeti.isClosed_fixedPointsOfFinrank`).
* **Submanifold structure.** For a subspace `L` of the model of dimension `d`, every subset of
  `M^K_d` open in `M^K` is a smooth manifold modelled on `L` whose inclusion into `M` is a smooth
  embedding, and the tangent image of the inclusion at each point `p` is exactly `V_p`
  (`TauCeti.exists_isSmoothEmbedding_of_subset_fixedPointsOfFinrank`). Near each of its points
  such a subset is the fixed set, which the Riemannian logarithm flattens. This applies to `M^K_d`
  itself (`TauCeti.exists_isSmoothEmbedding_fixedPointsOfFinrank`) and to each connected component
  of `M^K`, which is open in `M^K` since `M^K` is locally connected
  (`TauCeti.exists_isSmoothEmbedding_connectedComponentIn_fixedPoints`). The inclusion `⊆` of the
  tangent image in `V_p` holds because every `k •` is the identity on `M^K`, so its differential
  fixes the tangent image of the inclusion; equality follows by counting dimensions, the
  differential of an embedding being injective.

Neither completeness of the metric nor compactness of `M` or `K` is used. The ambient manifold is
boundaryless and modelled on a finite-dimensional real normed space, the setting of the normal
balls of the exponential map and of the embedded submanifold structures induced by slice charts
(`TauCeti.exists_isSmoothEmbedding_of_finrankSubspaceCharts`).

## Main results

* `TauCeti.comap_mfderiv_riemannianExp_fixedTangentSubspace`: the differential of `exp_p` at a
  fixed vector `w`, where it is injective, carries exactly the vectors of `V_p` into `V_{exp_p w}`.
* `TauCeti.Manifold.IsNormalDomain.finrank_fixedTangentSubspace_riemannianExp`: `V_{exp_p w}` and
  `V_p` have the same dimension for a fixed vector `w` of a normal domain at a fixed point `p`.
* `TauCeti.isLocallyConstant_finrank_fixedTangentSubspace`: the dimension of the fixed tangent
  subspace is locally constant on the fixed set.
* `TauCeti.isOpen_preimage_val_fixedPointsOfFinrank`: the sets `M^K_d`, which partition the fixed
  set, are open in it.
* `TauCeti.isClosed_fixedPointsOfFinrank`: each `M^K_d` is closed in `M`.
* `TauCeti.subset_fixedPointsOfFinrank_of_isPreconnected`: a connected subset of the fixed set has a
  single dimension.
* `TauCeti.exists_isSmoothEmbedding_of_subset_fixedPointsOfFinrank`: each subset of `M^K_d` open in
  `M^K` is a smooth embedded submanifold with tangent spaces the fixed tangent subspaces.
* `TauCeti.exists_isSmoothEmbedding_fixedPointsOfFinrank`,
  `TauCeti.exists_isSmoothEmbedding_connectedComponentIn_fixedPoints`: so is each `M^K_d`, and so
  is each connected component of `M^K`.

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

/-- **The exponential differential detects fixed tangent vectors.** Let a group act by isometries
fixing `p`, and let `w` be a tangent vector at `p` fixed by every differential `d(k •)_p`, such that
the differential `D` of `exp_p` at `w` is injective. Then a tangent vector `v` at `p` is fixed by
every `d(k •)_p` exactly when `D v` is fixed by every differential at `exp_p w`. -/
theorem comap_mfderiv_riemannianExp_fixedTangentSubspace {p : M} (hp : p ∈ fixedPoints K M)
    {w : TangentSpace I p} (hw : ∀ k : K, mfderiv I I (k • ·) p w = w)
    (hinj : Function.Injective (mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) w)) :
    (fixedTangentSubspace I K (riemannianExp I M p w)).comap
        (mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) w).toLinearMap =
      fixedTangentSubspace I K p := by
  refine Submodule.ext fun (v : TangentSpace I p) ↦ ?_
  -- Unfold `Submodule.mem_comap` and the `toLinearMap` coercion by `change`: `v` lives in
  -- `TangentSpace I p` while the comap is taken over `TangentSpace 𝓘(ℝ, TangentSpace I p) w`.
  -- These agree only after unfolding the semireducible `TangentSpace`, so the goal is not
  -- type-correct at reducible transparency and `rw`/`simp only [Submodule.mem_comap]` fail.
  change mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) w v ∈
    fixedTangentSubspace I K (riemannianExp I M p w) ↔ v ∈ fixedTangentSubspace I K p
  rw [mem_fixedTangentSubspace_iff_of_mem_fixedPoints (riemannianExp_mem_fixedPoints hK hp hw),
    mem_fixedTangentSubspace_iff_of_mem_fixedPoints hp]
  refine forall_congr' fun k ↦ ?_
  rw [mfderiv_smul_mfderiv_riemannianExp (hK k) (hp k) (hw k)]
  exact hinj.eq_iff

/-- **The fixed tangent subspaces along the exponential image of a fixed vector.** For a group
acting by isometries fixing `p`, and a vector `w` of a normal domain at `p` fixed by every
differential `d(k •)_p`, the fixed tangent subspace at `exp_p w` has the same dimension as that
at `p`. -/
theorem Manifold.IsNormalDomain.finrank_fixedTangentSubspace_riemannianExp {p : M}
    {U : Set (TangentSpace I p)} {w : TangentSpace I p} (hU : IsNormalDomain I M p U)
    (hp : p ∈ fixedPoints K M) (hwU : w ∈ U) (hw : ∀ k : K, mfderiv I I (k • ·) p w = w) :
    Module.finrank ℝ (fixedTangentSubspace I K (riemannianExp I M p w)) =
      Module.finrank ℝ (fixedTangentSubspace I K p) := by
  -- On the normal domain the differential of `exp_p` at `w` is a linear isomorphism `D`.
  obtain ⟨D, hD⟩ := (hU.isLocalDiffeomorphOn ⟨w, hwU⟩).isInvertible_mfderiv (by simp)
  have h := comap_mfderiv_riemannianExp_fixedTangentSubspace hK hp hw (hD ▸ D.injective)
  rw [← hD] at h
  rw [← h]
  exact (D.toLinearEquiv.symm.finrank_map_eq _).symm.trans
    (congrArg (fun V : Submodule ℝ (TangentSpace I p) ↦ Module.finrank ℝ V)
      (Submodule.comap_equiv_eq_map_symm D.toLinearEquiv _).symm)

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

/-- A smooth chart near a fixed point `y`, with values in the model vector space, flattening the
fixed set onto the fixed tangent subspace at `y`: the Riemannian logarithm on a normal ball. -/
private theorem exists_sliceChart_fixedPoints {y : M} (hy : y ∈ fixedPoints K M) :
    ∃ q : OpenPartialHomeomorph M E, y ∈ q.source ∧
      (∀ z ∈ q.source, ContMDiffAt I 𝓘(ℝ, E) ∞ q z) ∧
      (∀ z ∈ q.target, ContMDiffAt 𝓘(ℝ, E) I ∞ q.symm z) ∧
      ∀ z ∈ q.source, z ∈ fixedPoints K M ↔ q z ∈ fixedTangentSubspace I K y := by
  obtain ⟨φ, hyφ, -, -, hφ⟩ := exists_isSliceChart_fixedPoints hK hy
  -- The identity of the model space, from the normed structure of `T_y M` to that of `E`.
  let B : TangentSpace I y ≃L[ℝ] E := ContinuousLinearEquiv.refl ℝ E
  refine ⟨φ.toOpenPartialHomeomorph, hyφ, fun z hz ↦ ?_, fun z hz ↦ ?_, fun z hz ↦
    (isSliceChart_iff.1 hφ z hz).trans (mem_fixedTangentSubspace_iff_of_mem_fixedPoints hy).symm⟩
  · exact B.contDiff.contMDiff.contMDiffAt.comp z
      ((φ.contMDiffOn z hz).contMDiffAt (φ.open_source.mem_nhds hz))
  · exact ((φ.symm.contMDiffOn (B.symm z) hz).contMDiffAt
      (φ.symm.open_source.mem_nhds hz)).comp z B.symm.contDiff.contMDiff.contMDiffAt

/-- **Open parts of the fixed set of a single dimension are embedded submanifolds.** Let `s` be a
subset of the fixed set, open in it, at whose points the fixed tangent subspace has dimension
`d`. For a subspace `L` of the model of dimension `d`, `s` is a smooth manifold modelled on `L`,
whose inclusion into `M` is a smooth embedding with tangent image the fixed tangent subspace at
every point. -/
theorem exists_isSmoothEmbedding_of_subset_fixedPointsOfFinrank {s : Set M} {d : ℕ}
    {L : Submodule ℝ E} (hL : Module.finrank ℝ L = d) (hsd : s ⊆ fixedPointsOfFinrank I K M d)
    (hs : IsOpen ((↑) ⁻¹' s : Set (MulAction.fixedPoints K M))) :
    ∃ C : ChartedSpace L s, letI := C
      IsManifold 𝓘(ℝ, L) ∞ s ∧ IsSmoothEmbedding 𝓘(ℝ, L) I ∞ (Subtype.val : s → M) ∧
      ∀ y : s, LinearMap.range (mfderiv 𝓘(ℝ, L) I Subtype.val y).toLinearMap =
        fixedTangentSubspace I K (y : M) := by
  -- `s` is the trace on the fixed set of an open set `O` of `M`.
  obtain ⟨O, hO, hOs⟩ := isOpen_induced_iff.1 hs
  have hmem {z : M} (hzK : z ∈ fixedPoints K M) : z ∈ O ↔ z ∈ s :=
    Iff.of_eq (congrArg (⟨z, hzK⟩ ∈ ·) hOs)
  obtain ⟨C, hman, hemb⟩ := exists_isSmoothEmbedding_of_finrankSubspaceCharts
    (L := L) (n := ∞) (s := s) fun y hy ↦ by
      obtain ⟨hyK, hyd⟩ := mem_fixedPointsOfFinrank.1 (hsd hy)
      obtain ⟨q, hyq, hq, hqs, hqK⟩ := exists_sliceChart_fixedPoints hK hyK
      -- Within `O`, the set `s` is the fixed set, which `q` flattens.
      refine ⟨q.restrOpen O hO, fixedTangentSubspace I K y, ⟨hyq, (hmem hyK).2 hy⟩,
        fun z hz ↦ hq z hz.1, fun z hz ↦ hqs z hz.1, fun z hz ↦ ?_, hyd.trans hL.symm⟩
      exact ⟨fun hzs ↦ (hqK z hz.1).1 (mem_fixedPointsOfFinrank.1 (hsd hzs)).1,
        fun hzV ↦ (hmem ((hqK z hz.1).2 hzV)).1 hz.2⟩
  let := C
  refine ⟨C, hman, hemb, fun y ↦ ?_⟩
  have hle : LinearMap.range (mfderiv 𝓘(ℝ, L) I Subtype.val y).toLinearMap ≤
      fixedTangentSubspace I K (y : M) := by
    rintro _ ⟨u, rfl⟩
    refine mem_fixedTangentSubspace.2 fun k _ ↦ ?_
    -- Every `k •` is the identity on the fixed set, so it fixes the tangent image of `val`.
    have hcomp : ((k • ·) ∘ Subtype.val : s → M) = Subtype.val :=
      funext fun z ↦ (mem_fixedPointsOfFinrank.1 (hsd z.property)).1 k
    have h := mfderiv_comp y
      ((contMDiff_const_smul (I := I) (n := ∞) k).mdifferentiableAt (by simp))
      (hemb.contMDiff.mdifferentiableAt (by simp) (x := y))
    rw [hcomp] at h
    exact (congrArg (fun A ↦ A u) h).symm
  refine Submodule.eq_of_le_of_finrank_eq hle ?_
  rw [LinearMap.finrank_range_of_inj (hemb.isImmersion.mfderiv_injective (by simp) y),
    (mem_fixedPointsOfFinrank.1 (hsd y.property)).2]
  exact hL

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
          fixedTangentSubspace I K (y : M) :=
  exists_isSmoothEmbedding_of_subset_fixedPointsOfFinrank hK hL subset_rfl
    (isOpen_preimage_val_fixedPointsOfFinrank hK d)

/-- **The connected components of the fixed set of a group of isometries are embedded
submanifolds.** For a fixed point `p` and a subspace `L` of the model of the dimension of the fixed
tangent subspace at `p`, the connected component of `p` in the fixed set is a smooth manifold
modelled on `L`, whose inclusion into `M` is a smooth embedding with tangent image the fixed
tangent subspace at every point. -/
theorem exists_isSmoothEmbedding_connectedComponentIn_fixedPoints {p : M}
    (hp : p ∈ fixedPoints K M) {L : Submodule ℝ E}
    (hL : Module.finrank ℝ L = Module.finrank ℝ (fixedTangentSubspace I K p)) :
    ∃ C : ChartedSpace L (connectedComponentIn (fixedPoints K M) p), letI := C
      IsManifold 𝓘(ℝ, L) ∞ (connectedComponentIn (fixedPoints K M) p) ∧
      IsSmoothEmbedding 𝓘(ℝ, L) I ∞
        (Subtype.val : connectedComponentIn (fixedPoints K M) p → M) ∧
      ∀ y : connectedComponentIn (fixedPoints K M) p,
        LinearMap.range (mfderiv 𝓘(ℝ, L) I Subtype.val y).toLinearMap =
          fixedTangentSubspace I K (y : M) :=
  exists_isSmoothEmbedding_of_subset_fixedPointsOfFinrank hK hL
    (subset_fixedPointsOfFinrank_of_isPreconnected hK isPreconnected_connectedComponentIn
      (connectedComponentIn_subset _ _) (mem_connectedComponentIn hp))
    (isOpen_preimage_val_connectedComponentIn_fixedPoints hK hp)

end TauCeti
