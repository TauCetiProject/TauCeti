/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Distribution
public import TauCeti.Analysis.Normed.Module.ContinuousInverse

/-!
# Distributions as vector bundles

A distribution `D` on a manifold `M` assigns to every point `x` a subspace `D x` of the tangent
space. Its total space, the pairs `(x, v)` with `v ∈ D x`, carries the topology of a subspace of
the tangent bundle (`TauCeti.isEmbedding_totalSpace_distribution`). This file shows that over `ℝ`
or `ℂ` a continuous distribution of rank `k` (a `C^n` distribution of rank `k`, for any `n`), with
this topology, is a topological vector bundle with model fibre `Fin k → 𝕜`: a subbundle of the
tangent bundle. Constructions on real vector bundles, such as the Euler class
`TauCeti.eulerClass`, can then be applied to the tangent field of a foliation.

The local trivializations come from local frames. A local frame `X` of `D` on an open set `U`
is a basis of `D y` at each point `y ∈ U` (`TauCeti.IsDistributionFrameOn.basis`), and the
trivialization `TauCeti.IsDistributionFrameOn.trivialization` sends a vector of `D y` to its
coordinates in that basis. The substance is that these coordinates depend continuously on the
vector in the subspace topology. Read in a trivialization of the tangent bundle near `y₀`, the
frame becomes a continuous family of injective operators `A y : 𝕜ᵏ →L[𝕜] E`; an injective
operator out of a finite-dimensional space has a continuous left inverse, and left inverses can
be chosen continuously in families (`ContinuousAt.exists_continuousAt_leftInverse`). The same
argument shows that the coordinate changes between two frames are continuous.

Over a general nontrivially normed field a finite-dimensional subspace of the model space need
not be complemented, which is why the scalars are `ℝ` or `ℂ` (`IsRCLikeNormedField 𝕜`); the model
space `E` is arbitrary.

For a continuous distribution `hD : IsContMDiffDistribution I n k D`, install
`hD.fiberBundle` with `letI`; `hD.vectorBundle` then shows that it is a vector bundle.

## Main definitions

* `TauCeti.instTopologicalSpaceTotalSpaceDistribution`: the subspace topology on the total space
  of a distribution.
* `TauCeti.IsDistributionFrameOn.trivialization`: the local trivialization of `D` given by a local
  frame on an open set.
* `TauCeti.IsContMDiffDistribution.fiberBundle`: a continuous distribution of rank `k` is a fibre
  bundle with fibre `Fin k → 𝕜`.

## Main results

* `TauCeti.isEmbedding_totalSpace_distribution`: the total space of a distribution is a subspace
  of the tangent bundle.
* `TauCeti.IsDistributionFrameOn.continuousOn_coordChangeL`: the coordinate changes between the
  trivializations of two local frames are continuous on the overlap.
* `TauCeti.IsContMDiffDistribution.vectorBundle`: a continuous distribution of rank `k` is a
  topological vector bundle.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218 (2013), Chapter 10
  (the local frame criterion for smooth subbundles, Lemma 10.32, of which this is the continuous
  counterpart) and Chapter 19 (distributions).
-/

public section

noncomputable section

open Set Filter Function Module Bundle Topology
open scoped Manifold ContDiff

namespace TauCeti

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  {n : ℕ∞ω} {k : ℕ} {ι : Type*}

section Topology

/-- The total space of a distribution `D`, the pairs `(x, v)` with `v ∈ D x`, carries the topology
of a subspace of the tangent bundle. The model-fibre parameter `F` of `Bundle.TotalSpace` plays no
role. -/
instance instTopologicalSpaceTotalSpaceDistribution {F : Type*}
    (D : Π x : M, Submodule 𝕜 (TangentSpace I x)) :
    TopologicalSpace (TotalSpace F fun x ↦ D x) :=
  .induced (fun p ↦ (⟨p.proj, p.2⟩ : TangentBundle I M)) inferInstance

/-- The total space of a distribution is embedded in the tangent bundle. -/
theorem isEmbedding_totalSpace_distribution (F : Type*)
    (D : Π x : M, Submodule 𝕜 (TangentSpace I x)) :
    IsEmbedding fun p : TotalSpace F (fun x ↦ D x) ↦ (⟨p.proj, p.2⟩ : TangentBundle I M) := by
  refine ⟨⟨rfl⟩, fun ⟨x, v⟩ ⟨y, w⟩ h ↦ ?_⟩
  obtain rfl : x = y := congrArg TotalSpace.proj h
  exact congrArg (TotalSpace.mk x) (Subtype.ext (TotalSpace.mk_inj.mp h))

/-- The projection of the total space of a distribution is continuous. -/
theorem continuous_proj_totalSpace_distribution (F : Type*)
    (D : Π x : M, Submodule 𝕜 (TangentSpace I x)) :
    Continuous (TotalSpace.proj : TotalSpace F (fun x ↦ D x) → M) :=
  (FiberBundle.continuous_proj E (TangentSpace I)).comp
    (isEmbedding_totalSpace_distribution F D).continuous

end Topology

namespace IsDistributionFrameOn

variable {D : Π x : M, Submodule 𝕜 (TangentSpace I x)} {X : ι → Π x : M, TangentSpace I x}
  {U : Set M}

section Coordinates

variable [Fintype ι] (hX : IsDistributionFrameOn I n D X U)

open scoped Classical in
/-- The coordinates of a vector of `D y` in the frame `X`, extended by zero off `U`. -/
private def coords (y : M) : D y →ₗ[𝕜] ι → 𝕜 :=
  if hy : y ∈ U then (hX.basis hy).equivFun.toLinearMap else 0

open scoped Classical in
/-- The vector of `D y` with given coordinates in the frame `X`, extended by zero off `U`. -/
private def vec (y : M) : (ι → 𝕜) →ₗ[𝕜] D y :=
  if hy : y ∈ U then (hX.basis hy).equivFun.symm.toLinearMap else 0

private theorem coords_of_mem {y : M} (hy : y ∈ U) (v : D y) :
    hX.coords y v = (hX.basis hy).equivFun v := by
  simp [coords, hy]

private theorem vec_of_mem {y : M} (hy : y ∈ U) (c : ι → 𝕜) :
    hX.vec y c = (hX.basis hy).equivFun.symm c := by
  simp [vec, hy]

private theorem vec_coords {y : M} (hy : y ∈ U) (v : D y) : hX.vec y (hX.coords y v) = v := by
  rw [vec_of_mem hX hy, coords_of_mem hX hy, LinearEquiv.symm_apply_apply]

private theorem coords_vec {y : M} (hy : y ∈ U) (c : ι → 𝕜) : hX.coords y (hX.vec y c) = c := by
  rw [vec_of_mem hX hy, coords_of_mem hX hy, LinearEquiv.apply_symm_apply]

private theorem coe_vec {y : M} (hy : y ∈ U) (c : ι → 𝕜) :
    (hX.vec y c : TangentSpace I y) = ∑ i, c i • X i y := by
  simp only [vec_of_mem hX hy, Basis.equivFun_symm_apply, Submodule.coe_sum, Submodule.coe_smul,
    coe_basis]

end Coordinates

section TrivOperator

variable [Fintype ι]

variable (X) in
/-- The frame `X` near `y`, read in the trivialization of the tangent bundle at `y₀`, as an
operator from coordinates to the model space. -/
private def trivOperator (y₀ y : M) : (ι → 𝕜) →L[𝕜] E :=
  ∑ i, (ContinuousLinearMap.proj i).smulRight (trivializationAt E (TangentSpace I) y₀ ⟨y, X i y⟩).2

/-- Over the base set of the trivialization at `y₀`, the operator `trivOperator X y₀ y` sends
coordinates to the corresponding combination of the frame, read in that trivialization. -/
private theorem trivOperator_apply {y₀ y : M}
    (hy : y ∈ (trivializationAt E (TangentSpace I) y₀).baseSet) (c : ι → 𝕜) :
    trivOperator X y₀ y c = (trivializationAt E (TangentSpace I) y₀ ⟨y, ∑ i, c i • X i y⟩).2 := by
  have h := (trivializationAt E (TangentSpace I) y₀).continuousLinearMapAt_apply_of_mem
    (R := 𝕜) hy
  simp only [trivOperator, FunLike.coe_sum, Finset.sum_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.proj_apply, ← h, map_sum, map_smul]

private theorem continuousAt_trivOperator (hX : IsDistributionFrameOn I n D X U) (hU : IsOpen U)
    {y₀ : M} (hy₀ : y₀ ∈ U) : ContinuousAt (trivOperator X y₀) y₀ := by
  refine tendsto_finsetSum _ fun i _ ↦ ?_
  have h := ((FiberBundle.continuousAt_totalSpace E _).mp
    (((hX.contMDiffOn i).continuousOn).continuousAt (hU.mem_nhds hy₀))).2
  exact ((ContinuousLinearMap.smulRightL 𝕜 (ι → 𝕜) E
    (ContinuousLinearMap.proj i)).continuous.continuousAt).comp h

private theorem injective_trivOperator (hX : IsDistributionFrameOn I n D X U) {y₀ : M}
    (hy₀ : y₀ ∈ U) : Injective (trivOperator X y₀ y₀) := by
  intro c c' h
  have hb := FiberBundle.mem_baseSet_trivializationAt' (F := E) (E := TangentSpace I) y₀
  rw [trivOperator_apply hb, trivOperator_apply hb] at h
  have h' := ((trivializationAt E (TangentSpace I) y₀).continuousLinearEquivAt 𝕜 y₀ hb).injective
    (by simpa [Trivialization.continuousLinearEquivAt_apply] using h)
  exact linearIndependent_iff_injective_fintypeLinearCombination.mp (hX.linearIndependent hy₀)
    (by simpa [Fintype.linearCombination_apply] using h')

/-- Read in a trivialization of the tangent bundle, the frame sends the coordinates of a vector of
`D y` back to that vector. -/
private theorem trivOperator_coords (hX : IsDistributionFrameOn I n D X U) {y₀ y : M}
    (hyU : y ∈ U) (hy : y ∈ (trivializationAt E (TangentSpace I) y₀).baseSet) (v : D y) :
    trivOperator X y₀ y (hX.coords y v) = (trivializationAt E (TangentSpace I) y₀ ⟨y, v⟩).2 := by
  rw [trivOperator_apply hy, ← coe_vec hX hyU, vec_coords hX hyU]

/-- Near a point `y₀` of `U`, the coordinates in the frame are a continuously varying operator
applied to the vector read in the trivialization of the tangent bundle at `y₀`. -/
private theorem exists_coords_eq [IsRCLikeNormedField 𝕜] (hX : IsDistributionFrameOn I n D X U)
    (hU : IsOpen U) {y₀ : M} (hy₀ : y₀ ∈ U) :
    ∃ L : M → E →L[𝕜] ι → 𝕜, ContinuousAt L y₀ ∧ ∀ᶠ y in 𝓝 y₀, y ∈ U ∧
      y ∈ (trivializationAt E (TangentSpace I) y₀).baseSet ∧
      ∀ v : D y, hX.coords y v = L y (trivializationAt E (TangentSpace I) y₀ ⟨y, v⟩).2 := by
  have : CompleteSpace 𝕜 := by
    let _ := IsRCLikeNormedField.rclike 𝕜
    infer_instance
  obtain ⟨L, hL, hLinv⟩ := (continuousAt_trivOperator hX hU hy₀).exists_continuousAt_leftInverse
    (.of_injective_of_finiteDimensional_domain (injective_trivOperator hX hy₀))
  refine ⟨L, hL, ?_⟩
  filter_upwards [hLinv, hU.mem_nhds hy₀,
    (trivializationAt E (TangentSpace I) y₀).open_baseSet.mem_nhds
      (FiberBundle.mem_baseSet_trivializationAt' y₀)] with y hy hyU hyb
  exact ⟨hyU, hyb, fun v ↦ by rw [← trivOperator_coords hX hyU hyb, hy]⟩

/-- The coordinates in the frame depend continuously on the vector, in the subspace topology of
the tangent bundle. -/
private theorem continuousAt_coords [IsRCLikeNormedField 𝕜] (hX : IsDistributionFrameOn I n D X U)
    (hU : IsOpen U) {p : TotalSpace (ι → 𝕜) fun x ↦ D x} (hp : p.proj ∈ U) :
    ContinuousAt (fun q : TotalSpace (ι → 𝕜) (fun x ↦ D x) ↦ hX.coords q.proj q.2) p := by
  have hproj := (continuous_proj_totalSpace_distribution (ι → 𝕜) D).continuousAt (x := p)
  obtain ⟨L, hL, hev⟩ := exists_coords_eq hX hU hp
  -- Read in the trivialization of the tangent bundle at `p.proj`, the vector varies continuously.
  have hincl : ContinuousAt
      (fun q : TotalSpace (ι → 𝕜) (fun x ↦ D x) ↦ (⟨q.proj, q.2⟩ : TangentBundle I M)) p :=
    (isEmbedding_totalSpace_distribution _ D).continuous.continuousAt
  have htriv : ContinuousAt (trivializationAt E (TangentSpace I) p.proj)
      (⟨p.proj, p.2⟩ : TangentBundle I M) :=
    (trivializationAt E (TangentSpace I) p.proj).continuousAt
      (FiberBundle.mem_trivializationAt_proj_source (x := (⟨p.proj, p.2⟩ : TangentBundle I M)))
  have hread := (ContinuousAt.comp (f := fun q : TotalSpace (ι → 𝕜) (fun x ↦ D x) ↦
    (⟨q.proj, q.2⟩ : TangentBundle I M)) htriv hincl).snd
  refine ((hL.comp hproj).clm_apply hread).congr ?_
  filter_upwards [hproj.preimage_mem_nhds hev] with q hq
  exact (hq.2.2 q.2).symm

/-- The vector with given coordinates in the frame depends continuously on the base point and the
coordinates, in the subspace topology of the tangent bundle. -/
private theorem continuousAt_vec (hX : IsDistributionFrameOn I n D X U) (hU : IsOpen U)
    {q : M × (ι → 𝕜)} (hq : q.1 ∈ U) :
    ContinuousAt (fun q : M × (ι → 𝕜) ↦
      TotalSpace.mk' (ι → 𝕜) (E := fun x ↦ D x) q.1 (hX.vec q.1 q.2)) q := by
  rw [(isEmbedding_totalSpace_distribution _ D).continuousAt_iff,
    FiberBundle.continuousAt_totalSpace]
  refine ⟨continuousAt_fst, (((continuousAt_trivOperator hX hU hq).comp continuousAt_fst).clm_apply
    continuousAt_snd).congr ?_⟩
  filter_upwards [continuousAt_fst.preimage_mem_nhds (hU.mem_nhds hq),
    continuousAt_fst.preimage_mem_nhds
      ((trivializationAt E (TangentSpace I) q.1).open_baseSet.mem_nhds
        (FiberBundle.mem_baseSet_trivializationAt' q.1))] with q' hq'U hq'b
  exact (congrArg (trivOperator X q.1 q'.1) (coords_vec hX hq'U q'.2)).symm.trans
    (trivOperator_coords hX hq'U hq'b _)

end TrivOperator

section Trivialization

variable [Fintype ι] [IsRCLikeNormedField 𝕜]

/-- The local trivialization of a distribution given by a local frame `X` on an open set `U`: over
`U`, a vector of `D y` is sent to its coordinates in the frame. -/
def trivialization (hX : IsDistributionFrameOn I n D X U) (hU : IsOpen U) :
    Trivialization (ι → 𝕜) (π (ι → 𝕜) fun x ↦ D x) where
  toFun p := (p.proj, hX.coords p.proj p.2)
  invFun q := TotalSpace.mk' (ι → 𝕜) (E := fun x ↦ D x) q.1 (hX.vec q.1 q.2)
  source := π (ι → 𝕜) (fun x ↦ D x) ⁻¹' U
  target := U ×ˢ univ
  map_source' _ hp := ⟨hp, mem_univ _⟩
  map_target' _ hq := hq.1
  left_inv' p hp := by
    dsimp only
    rw [vec_coords hX hp]
  right_inv' q hq := by
    dsimp only
    rw [coords_vec hX hq.1]
  open_source := hU.preimage (continuous_proj_totalSpace_distribution _ D)
  open_target := by exact hU.prod isOpen_univ
  continuousOn_toFun := continuousOn_of_forall_continuousAt fun _ hp ↦
    ((continuous_proj_totalSpace_distribution _ D).continuousAt).prodMk
      (continuousAt_coords hX hU hp)
  continuousOn_invFun := continuousOn_of_forall_continuousAt fun _ hq ↦ continuousAt_vec hX hU hq.1
  baseSet := U
  open_baseSet := hU
  source_eq := rfl
  target_eq := rfl
  proj_toFun _ _ := rfl

variable (hX : IsDistributionFrameOn I n D X U) (hU : IsOpen U)

@[simp]
theorem trivialization_baseSet : (hX.trivialization hU).baseSet = U :=
  (rfl)

private theorem trivialization_apply_eq (p : TotalSpace (ι → 𝕜) fun x ↦ D x) :
    hX.trivialization hU p = (p.proj, hX.coords p.proj p.2) :=
  (rfl)

private theorem trivialization_symm_apply_eq (q : M × (ι → 𝕜)) :
    (hX.trivialization hU).toOpenPartialHomeomorph.symm q =
      TotalSpace.mk' (ι → 𝕜) (E := fun x ↦ D x) q.1 (hX.vec q.1 q.2) :=
  (rfl)

/-- Over `U`, the frame trivialization sends a vector to its coordinates in the frame. -/
@[simp]
theorem trivialization_apply {p : TotalSpace (ι → 𝕜) fun x ↦ D x} (hp : p.proj ∈ U) :
    hX.trivialization hU p = (p.proj, (hX.basis hp).equivFun p.2) := by
  rw [trivialization_apply_eq, coords_of_mem hX hp]

/-- Over `U`, the inverse of the frame trivialization sends coordinates to the corresponding
combination of the frame. -/
@[simp]
theorem trivialization_symm_apply {q : M × (ι → 𝕜)} (hq : q.1 ∈ U) :
    (hX.trivialization hU).toOpenPartialHomeomorph.symm q =
      TotalSpace.mk' (ι → 𝕜) (E := fun x ↦ D x) q.1 ((hX.basis hq).equivFun.symm q.2) := by
  rw [trivialization_symm_apply_eq, vec_of_mem hX hq]

/-- The frame trivialization is fibrewise linear. -/
instance isLinear_trivialization : (hX.trivialization hU).IsLinear 𝕜 where
  linear y _ := by
    simp only [trivialization_apply_eq]
    exact (hX.coords y).isLinear

/-- The coordinate changes between the trivializations of two local frames of `D` are continuous
on the intersection of their domains. -/
theorem continuousOn_coordChangeL {m : ℕ∞ω} {Y : ι → Π x : M, TangentSpace I x} {V : Set M}
    (hY : IsDistributionFrameOn I m D Y V) (hV : IsOpen V) :
    ContinuousOn (fun y ↦ ((hX.trivialization hU).coordChangeL 𝕜 (hY.trivialization hV) y :
      (ι → 𝕜) →L[𝕜] ι → 𝕜)) (U ∩ V) := by
  refine continuousOn_of_forall_continuousAt fun y₀ hy₀ ↦ ?_
  obtain ⟨L, hL, hev⟩ := exists_coords_eq hY hV hy₀.2
  refine (hL.clm_comp (continuousAt_trivOperator hX hU hy₀.1)).congr ?_
  filter_upwards [hev, (hU.inter hV).mem_nhds hy₀] with y hy hyUV
  ext1 c
  -- The coordinate change sends `c` to the coordinates in `Y` of the vector with coordinates `c`
  -- in `X`, which `L y` recovers from that vector read in the tangent bundle.
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    Trivialization.coordChangeL_apply' _ _ hyUV, trivialization_symm_apply_eq,
    trivialization_apply_eq, hy.2.2, ← trivOperator_coords hX hyUV.1 hy.2.1, coords_vec hX hyUV.1]

end Trivialization

end IsDistributionFrameOn

namespace IsContMDiffDistribution

variable [IsRCLikeNormedField 𝕜] {D : Π x : M, Submodule 𝕜 (TangentSpace I x)}

/-- A continuous distribution of rank `k` is a fibre bundle with fibre `Fin k → 𝕜`, the topology of
its total space being that of a subspace of the tangent bundle. Its trivializations are those of
local frames (`TauCeti.IsDistributionFrameOn.trivialization`). Use this definition as a local
instance, which chooses a local frame at every point. -/
@[instance_reducible]
def fiberBundle (hD : IsContMDiffDistribution I n k D) :
    FiberBundle (Fin k → 𝕜) fun x ↦ D x :=
  let U := fun x ↦ (isContMDiffDistribution_iff.mp hD x).choose
  have hU := fun x ↦ (isContMDiffDistribution_iff.mp hD x).choose_spec
  let X := fun x ↦ (hU x).2.2.choose
  have hX := fun x ↦ (hU x).2.2.choose_spec
  { totalSpaceMk_isInducing' := fun x ↦ by
      rw [← (isEmbedding_totalSpace_distribution (Fin k → 𝕜) D).isInducing.of_comp_iff]
      exact (FiberBundle.totalSpaceMk_isInducing E (TangentSpace I) x).comp IsInducing.subtypeVal
    trivializationAtlas' :=
      {e | ∃ (V : Set M) (hV : IsOpen V) (Y : Fin k → Π y : M, TangentSpace I y)
        (hY : IsDistributionFrameOn I n D Y V), hY.trivialization hV = e}
    trivializationAt' := fun x ↦ (hX x).trivialization (hU x).1
    mem_baseSet_trivializationAt' := fun x ↦ (hU x).2.1
    trivialization_mem_atlas' := fun x ↦ ⟨U x, (hU x).1, X x, hX x, rfl⟩ }

/-- The trivializations of `hD.fiberBundle` are the trivializations of local frames of `D`. -/
theorem mem_trivializationAtlas_fiberBundle_iff (hD : IsContMDiffDistribution I n k D)
    (e : Trivialization (Fin k → 𝕜) (π (Fin k → 𝕜) fun x ↦ D x)) :
    letI := hD.fiberBundle
    e ∈ trivializationAtlas (Fin k → 𝕜) (fun x ↦ D x) ↔
      ∃ (V : Set M) (hV : IsOpen V) (Y : Fin k → Π y : M, TangentSpace I y)
        (hY : IsDistributionFrameOn I n D Y V), hY.trivialization hV = e :=
  Iff.rfl

/-- **A continuous distribution of rank `k` is a vector bundle**: with the subspace topology of the
tangent bundle, its local frame trivializations are linear, with continuous coordinate changes. -/
theorem vectorBundle (hD : IsContMDiffDistribution I n k D) :
    letI := hD.fiberBundle
    VectorBundle 𝕜 (Fin k → 𝕜) fun x ↦ D x := by
  let := hD.fiberBundle
  refine { trivialization_linear' := ?_, continuousOn_coordChange' := ?_ }
  · intro e he
    obtain ⟨V, hV, Y, hY, rfl⟩ := (mem_trivializationAtlas_fiberBundle_iff hD e).mp he.out
    infer_instance
  · intro e e' he he'
    obtain ⟨V, hV, Y, hY, rfl⟩ := (mem_trivializationAtlas_fiberBundle_iff hD e).mp he.out
    obtain ⟨V', hV', Y', hY', rfl⟩ := (mem_trivializationAtlas_fiberBundle_iff hD e').mp he'.out
    exact hY.continuousOn_coordChangeL hV hY' hV'

end IsContMDiffDistribution

end TauCeti
