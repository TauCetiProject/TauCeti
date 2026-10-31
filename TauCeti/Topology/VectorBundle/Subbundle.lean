/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.VectorBundle.Basic
public import TauCeti.Analysis.Normed.Module.ContinuousInverse

/-!
# Subbundles spanned by continuous local frames

Let `E` be a topological vector bundle over `B` with model fibre `F`, and let `V` assign to every
point `x` a subspace `V x` of the fibre `E x`. The total space of `V`, the pairs `(x, v)` with
`v ∈ V x`, carries the topology of a subspace of the total space of `E`
(`TauCeti.subbundleTopology`). This file shows that over `ℝ` or `ℂ` a continuous local frame of
`V` gives a local trivialization of `V` for this topology, and that the coordinate changes between
two such trivializations are continuous. For a family of subspaces with a continuous local frame of
a fixed size near every point, these are the data and the two axioms of a topological vector bundle
structure, a subbundle of `E`; `TauCeti.IsContMDiffDistribution.vectorBundle` assembles them for
the distributions of a manifold.

A continuous local frame `X` of `V` on a set `U` (`TauCeti.IsSubbundleFrameOn F V X U`) is a
family of sections of `E`, continuous on `U`, whose values form a basis of `V y` at each point
`y ∈ U` (`TauCeti.IsSubbundleFrameOn.basis`). The trivialization
`TauCeti.IsSubbundleFrameOn.trivialization` sends a vector of `V y` to its coordinates in that
basis. The substance is that these coordinates depend continuously on the vector in the subspace
topology. Read in a trivialization of `E` near `y₀`, the frame becomes a continuous family of
injective operators `A y : 𝕜ᵏ →L[𝕜] F`; an injective operator out of a finite-dimensional space
has a continuous left inverse, and left inverses can be chosen continuously in families
(`ContinuousAt.exists_continuousAt_leftInverse`). The same argument shows that the coordinate
changes between two frames are continuous.

Over a general nontrivially normed field a finite-dimensional subspace of the model space need
not be complemented, which is why the scalars are `ℝ` or `ℂ` (`IsRCLikeNormedField 𝕜`); the model
fibre `F` is an arbitrary normed space and the base an arbitrary topological space. The subspace
topology and the algebraic API of frames (`TauCeti.IsSubbundleFrameOn.basis`) only need a semiring
of scalars.

The model fibre `F` of `E` cannot be recovered from `V`, so the subspace topology is not an
instance; install it with `letI := TauCeti.subbundleTopology F V`.

## Main definitions

* `TauCeti.subbundleTopology`: the subspace topology on the total space of a family of subspaces
  of the fibres of a bundle.
* `TauCeti.IsSubbundleFrameOn F V X U`: the sections `X i` form a continuous local frame of `V` on
  `U`.
* `TauCeti.IsSubbundleFrameOn.basis`: the basis of a fibre of `V` given by a local frame.
* `TauCeti.IsSubbundleFrameOn.trivialization`: the local trivialization of `V` given by a local
  frame on an open set.

## Main results

* `TauCeti.isEmbedding_totalSpace_subbundle`: the total space of `V` is a subspace of the total
  space of `E`.
* `TauCeti.isInducing_totalSpaceMk_subbundle`: each fibre `V x` carries the topology induced from
  the total space of `V`.
* `TauCeti.IsSubbundleFrameOn.continuousOn_coordChangeL`: the coordinate changes between the
  trivializations of two local frames are continuous on the overlap.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218 (2013), Chapter 10
  (the local frame criterion for smooth subbundles, Lemma 10.32, of which this is the continuous
  counterpart).
-/

public section

noncomputable section

open Set Filter Function Module Bundle Topology

namespace TauCeti

variable {𝕜 : Type*} {B : Type*} [TopologicalSpace B] (F : Type*) {E : B → Type*}
  [TopologicalSpace (TotalSpace F E)] {ι : Type*}

section Semiring

variable [Semiring 𝕜] [∀ x, AddCommMonoid (E x)] [∀ x, Module 𝕜 (E x)]

section Topology

/-- The total space of a family `V` of subspaces of the fibres of `E`, the pairs `(x, v)` with
`v ∈ V x`, carries the topology of a subspace of the total space of `E`. The model-fibre parameter
`F'` of `Bundle.TotalSpace` plays no role. Since `F` cannot be recovered from `V`, this is not an
instance; install it with `letI`. -/
@[instance_reducible]
def subbundleTopology {F' : Type*} (V : Π x, Submodule 𝕜 (E x)) :
    TopologicalSpace (TotalSpace F' fun x ↦ V x) :=
  .induced (fun p ↦ (⟨p.proj, p.2⟩ : TotalSpace F E)) inferInstance

omit [TopologicalSpace B] in
/-- The total space of a family of subspaces of the fibres of `E` is embedded in the total space
of `E`. -/
theorem isEmbedding_totalSpace_subbundle (F' : Type*) (V : Π x, Submodule 𝕜 (E x)) :
    letI := subbundleTopology F (F' := F') V
    IsEmbedding fun p : TotalSpace F' (fun x ↦ V x) ↦ (⟨p.proj, p.2⟩ : TotalSpace F E) := by
  let := subbundleTopology F (F' := F') V
  refine ⟨⟨rfl⟩, fun ⟨x, v⟩ ⟨y, w⟩ h ↦ ?_⟩
  obtain rfl : x = y := congrArg TotalSpace.proj h
  exact congrArg (TotalSpace.mk x) (Subtype.ext (TotalSpace.mk_inj.mp h))

variable [TopologicalSpace F] [∀ x, TopologicalSpace (E x)] [FiberBundle F E]

/-- The projection of the total space of a family of subspaces of the fibres of `E` is
continuous. -/
theorem continuous_proj_totalSpace_subbundle (F' : Type*) (V : Π x, Submodule 𝕜 (E x)) :
    letI := subbundleTopology F (F' := F') V
    Continuous (TotalSpace.proj : TotalSpace F' (fun x ↦ V x) → B) :=
  let := subbundleTopology F (F' := F') V
  (FiberBundle.continuous_proj F E).comp (isEmbedding_totalSpace_subbundle F F' V).continuous

/-- Each subspace `V x`, with the topology induced from the fibre `E x`, carries the topology
induced from the total space of `V`. -/
theorem isInducing_totalSpaceMk_subbundle (F' : Type*) (V : Π x, Submodule 𝕜 (E x)) (x : B) :
    letI := subbundleTopology F (F' := F') V
    IsInducing (TotalSpace.mk (F := F') (E := fun x ↦ V x) x) := by
  let := subbundleTopology F (F' := F') V
  rw [← (isEmbedding_totalSpace_subbundle F F' V).isInducing.of_comp_iff]
  exact (FiberBundle.totalSpaceMk_isInducing F E x).comp IsInducing.subtypeVal

end Topology

section Frame

/-- The sections `X i` of `E` form a continuous local frame of the family of subspaces `V` on the
set `U`: each `X i` is continuous on `U` as a map into the total space of `E`, and at every point
`x` of `U` the values `X i x` form a basis of `V x`. -/
structure IsSubbundleFrameOn (V : Π x, Submodule 𝕜 (E x)) (X : ι → Π x, E x) (U : Set B) :
    Prop where
  /-- Each member of the frame is a continuous section on `U`. -/
  continuousOn (i : ι) : ContinuousOn (fun x ↦ TotalSpace.mk' F x (X i x)) U
  /-- The values of the frame at a point of `U` are linearly independent. -/
  linearIndependent {x : B} (hx : x ∈ U) : LinearIndependent 𝕜 (X · x)
  /-- The values of the frame at a point of `U` span the subspace `V` there. -/
  span_eq {x : B} (hx : x ∈ U) : Submodule.span 𝕜 (range (X · x)) = V x

namespace IsSubbundleFrameOn

variable {F} {V : Π x, Submodule 𝕜 (E x)} {X : ι → Π x, E x} {U U' : Set B}

/-- A local frame of `V` on `U` is a local frame of `V` on every subset of `U`. -/
theorem mono (hX : IsSubbundleFrameOn F V X U) (hU : U' ⊆ U) : IsSubbundleFrameOn F V X U' where
  continuousOn i := (hX.continuousOn i).mono hU
  linearIndependent hx := hX.linearIndependent (hU hx)
  span_eq hx := hX.span_eq (hU hx)

/-- Every member of a local frame of `V` on `U` takes values in `V` on `U`. -/
theorem apply_mem (hX : IsSubbundleFrameOn F V X U) (i : ι) {x : B} (hx : x ∈ U) : X i x ∈ V x :=
  hX.span_eq hx ▸ Submodule.subset_span (mem_range_self i)

/-- The subspaces of a family with a local frame indexed by `ι` have dimension `card ι`. -/
theorem finrank_eq [StrongRankCondition 𝕜] [Fintype ι] (hX : IsSubbundleFrameOn F V X U) {x : B}
    (hx : x ∈ U) :
    finrank 𝕜 (V x) = Fintype.card ι := by
  rw [← hX.span_eq hx]
  exact finrank_span_eq_card (hX.linearIndependent hx)

/-- At a point `y` of `U`, a local frame of `V` on `U` is a basis of the subspace `V y`. -/
def basis (hX : IsSubbundleFrameOn F V X U) {y : B} (hy : y ∈ U) : Basis ι 𝕜 (V y) :=
  (Basis.span (hX.linearIndependent hy)).map (LinearEquiv.ofEq _ _ (hX.span_eq hy))

@[simp]
theorem coe_basis (hX : IsSubbundleFrameOn F V X U) {y : B} (hy : y ∈ U) (i : ι) :
    (hX.basis hy i : E y) = X i y := by
  simp [basis]

section Coordinates

variable [Finite ι] (hX : IsSubbundleFrameOn F V X U)

open scoped Classical in
/-- The coordinates of a vector of `V y` in the frame `X`, extended by zero off `U`. -/
private def coords (y : B) : V y →ₗ[𝕜] ι → 𝕜 :=
  if hy : y ∈ U then (hX.basis hy).equivFun.toLinearMap else 0

open scoped Classical in
/-- The vector of `V y` with given coordinates in the frame `X`, extended by zero off `U`. -/
private def vec (y : B) : (ι → 𝕜) →ₗ[𝕜] V y :=
  if hy : y ∈ U then (hX.basis hy).equivFun.symm.toLinearMap else 0

private theorem coords_of_mem {y : B} (hy : y ∈ U) (v : V y) :
    hX.coords y v = (hX.basis hy).equivFun v := by
  simp [coords, hy]

private theorem vec_of_mem {y : B} (hy : y ∈ U) (c : ι → 𝕜) :
    hX.vec y c = (hX.basis hy).equivFun.symm c := by
  simp [vec, hy]

private theorem vec_coords {y : B} (hy : y ∈ U) (v : V y) : hX.vec y (hX.coords y v) = v := by
  rw [vec_of_mem hX hy, coords_of_mem hX hy, LinearEquiv.symm_apply_apply]

private theorem coords_vec {y : B} (hy : y ∈ U) (c : ι → 𝕜) : hX.coords y (hX.vec y c) = c := by
  rw [vec_of_mem hX hy, coords_of_mem hX hy, LinearEquiv.apply_symm_apply]

end Coordinates

private theorem coe_vec [Fintype ι] (hX : IsSubbundleFrameOn F V X U) {y : B} (hy : y ∈ U)
    (c : ι → 𝕜) : (hX.vec y c : E y) = ∑ i, c i • X i y := by
  simp only [vec_of_mem hX hy, Basis.equivFun_symm_apply, Submodule.coe_sum, Submodule.coe_smul,
    coe_basis]

end IsSubbundleFrameOn

end Frame

end Semiring

section Normed

variable [NontriviallyNormedField 𝕜] [∀ x, AddCommMonoid (E x)] [∀ x, Module 𝕜 (E x)]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [∀ x, TopologicalSpace (E x)] [FiberBundle F E]
  [VectorBundle 𝕜 F E]

namespace IsSubbundleFrameOn

variable {F} {V : Π x, Submodule 𝕜 (E x)} {X : ι → Π x, E x} {U : Set B}

section TrivOperator

variable [Fintype ι]

variable (𝕜 F X) in
/-- The frame `X` near `y`, read in the trivialization of `E` at `y₀`, as an operator from
coordinates to the model fibre. -/
def trivOperator (y₀ y : B) : (ι → 𝕜) →L[𝕜] F :=
  ∑ i, (ContinuousLinearMap.proj i).smulRight (trivializationAt F E y₀ ⟨y, X i y⟩).2

omit [∀ x, AddCommMonoid (E x)] [∀ x, Module 𝕜 (E x)] [VectorBundle 𝕜 F E] in
/-- The operator `trivOperator 𝕜 F X y₀ y` is the finite sum over the frame of the frame vectors
read in the trivialization of `E` at `y₀`, each scaled by its coordinate. -/
theorem trivOperator_eq_sum (y₀ y : B) :
    trivOperator 𝕜 F X y₀ y =
      ∑ i, (ContinuousLinearMap.proj i).smulRight (trivializationAt F E y₀ ⟨y, X i y⟩).2 := by
  rw [trivOperator]

/-- Over the base set of the trivialization at `y₀`, the operator `trivOperator 𝕜 F X y₀ y` sends
coordinates to the corresponding combination of the frame, read in that trivialization. -/
theorem trivOperator_apply {y₀ y : B} (hy : y ∈ (trivializationAt F E y₀).baseSet)
    (c : ι → 𝕜) :
    trivOperator 𝕜 F X y₀ y c = (trivializationAt F E y₀ ⟨y, ∑ i, c i • X i y⟩).2 := by
  have h := (trivializationAt F E y₀).continuousLinearMapAt_apply_of_mem (R := 𝕜) hy
  simp only [trivOperator, FunLike.coe_sum, Finset.sum_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.proj_apply, ← h, map_sum, map_smul]

omit [VectorBundle 𝕜 F E] in
private theorem continuousAt_trivOperator (hX : IsSubbundleFrameOn F V X U) (hU : IsOpen U)
    {y₀ : B} (hy₀ : y₀ ∈ U) : ContinuousAt (trivOperator 𝕜 F X y₀) y₀ := by
  refine tendsto_finsetSum _ fun i _ ↦ ?_
  have h := ((FiberBundle.continuousAt_totalSpace F _).mp
    ((hX.continuousOn i).continuousAt (hU.mem_nhds hy₀))).2
  exact ((ContinuousLinearMap.smulRightL 𝕜 (ι → 𝕜) F
    (ContinuousLinearMap.proj i)).continuous.continuousAt).comp h

/-- At a point `y₀` of `U`, the frame read in the trivialization of `E` at `y₀` is injective on
coordinates. -/
theorem injective_trivOperator (hX : IsSubbundleFrameOn F V X U) {y₀ : B}
    (hy₀ : y₀ ∈ U) : Injective (trivOperator 𝕜 F X y₀ y₀) := by
  intro c c' h
  have hb := FiberBundle.mem_baseSet_trivializationAt' (F := F) (E := E) y₀
  rw [trivOperator_apply hb, trivOperator_apply hb] at h
  have h' := ((trivializationAt F E y₀).continuousLinearEquivAt 𝕜 y₀ hb).injective
    (by simpa [Trivialization.continuousLinearEquivAt_apply] using h)
  exact linearIndependent_iff_injective_fintypeLinearCombination.mp (hX.linearIndependent hy₀)
    (by simpa [Fintype.linearCombination_apply] using h')

/-- Read in a trivialization of `E`, the frame sends the coordinates of a vector of `V y` back to
that vector. -/
private theorem trivOperator_coords (hX : IsSubbundleFrameOn F V X U) {y₀ y : B}
    (hyU : y ∈ U) (hy : y ∈ (trivializationAt F E y₀).baseSet) (v : V y) :
    trivOperator 𝕜 F X y₀ y (hX.coords y v) = (trivializationAt F E y₀ ⟨y, v⟩).2 := by
  rw [trivOperator_apply hy, ← coe_vec hX hyU, vec_coords hX hyU]

end TrivOperator

section Continuity

variable [Finite ι]

/-- Near a point `y₀` of `U`, the coordinates in the frame are a continuously varying operator
applied to the vector read in the trivialization of `E` at `y₀`. -/
private theorem exists_coords_eq [IsRCLikeNormedField 𝕜] (hX : IsSubbundleFrameOn F V X U)
    (hU : IsOpen U) {y₀ : B} (hy₀ : y₀ ∈ U) :
    ∃ L : B → F →L[𝕜] ι → 𝕜, ContinuousAt L y₀ ∧ ∀ᶠ y in 𝓝 y₀, y ∈ U ∧
      y ∈ (trivializationAt F E y₀).baseSet ∧
      ∀ v : V y, hX.coords y v = L y (trivializationAt F E y₀ ⟨y, v⟩).2 := by
  let := Fintype.ofFinite ι
  have : CompleteSpace 𝕜 := by
    let _ := IsRCLikeNormedField.rclike 𝕜
    infer_instance
  obtain ⟨L, hL, hLinv⟩ := (continuousAt_trivOperator hX hU hy₀).exists_continuousAt_leftInverse
    (.of_injective_of_finiteDimensional_domain (injective_trivOperator hX hy₀))
  refine ⟨L, hL, ?_⟩
  filter_upwards [hLinv, hU.mem_nhds hy₀,
    (trivializationAt F E y₀).open_baseSet.mem_nhds
      (FiberBundle.mem_baseSet_trivializationAt' y₀)] with y hy hyU hyb
  exact ⟨hyU, hyb, fun v ↦ by rw [← trivOperator_coords hX hyU hyb, hy]⟩

/-- The coordinates in the frame depend continuously on the vector, in the subspace topology of
the total space of `E`. -/
private theorem continuousAt_coords [IsRCLikeNormedField 𝕜] (hX : IsSubbundleFrameOn F V X U)
    (hU : IsOpen U) {p : TotalSpace (ι → 𝕜) fun x ↦ V x} (hp : p.proj ∈ U) :
    letI := subbundleTopology F (F' := ι → 𝕜) V
    ContinuousAt (fun q : TotalSpace (ι → 𝕜) (fun x ↦ V x) ↦ hX.coords q.proj q.2) p := by
  let := subbundleTopology F (F' := ι → 𝕜) V
  let := Fintype.ofFinite ι
  have hproj := (continuous_proj_totalSpace_subbundle F (ι → 𝕜) V).continuousAt (x := p)
  obtain ⟨L, hL, hev⟩ := exists_coords_eq hX hU hp
  -- Read in the trivialization of `E` at `p.proj`, the vector varies continuously.
  have hincl : ContinuousAt
      (fun q : TotalSpace (ι → 𝕜) (fun x ↦ V x) ↦ (⟨q.proj, q.2⟩ : TotalSpace F E)) p :=
    (isEmbedding_totalSpace_subbundle F _ V).continuous.continuousAt
  have htriv : ContinuousAt (trivializationAt F E p.proj) (⟨p.proj, p.2⟩ : TotalSpace F E) :=
    (trivializationAt F E p.proj).continuousAt
      (FiberBundle.mem_trivializationAt_proj_source (x := (⟨p.proj, p.2⟩ : TotalSpace F E)))
  have hread := (ContinuousAt.comp (f := fun q : TotalSpace (ι → 𝕜) (fun x ↦ V x) ↦
    (⟨q.proj, q.2⟩ : TotalSpace F E)) htriv hincl).snd
  refine ((hL.comp hproj).clm_apply hread).congr ?_
  filter_upwards [hproj.preimage_mem_nhds hev] with q hq
  exact (hq.2.2 q.2).symm

/-- The vector with given coordinates in the frame depends continuously on the base point and the
coordinates, in the subspace topology of the total space of `E`. -/
private theorem continuousAt_vec (hX : IsSubbundleFrameOn F V X U) (hU : IsOpen U)
    {q : B × (ι → 𝕜)} (hq : q.1 ∈ U) :
    letI := subbundleTopology F (F' := ι → 𝕜) V
    ContinuousAt (fun q : B × (ι → 𝕜) ↦
      TotalSpace.mk' (ι → 𝕜) (E := fun x ↦ V x) q.1 (hX.vec q.1 q.2)) q := by
  let := subbundleTopology F (F' := ι → 𝕜) V
  let := Fintype.ofFinite ι
  rw [(isEmbedding_totalSpace_subbundle F _ V).continuousAt_iff,
    FiberBundle.continuousAt_totalSpace]
  refine ⟨continuousAt_fst, (((continuousAt_trivOperator hX hU hq).comp continuousAt_fst).clm_apply
    continuousAt_snd).congr ?_⟩
  filter_upwards [continuousAt_fst.preimage_mem_nhds (hU.mem_nhds hq),
    continuousAt_fst.preimage_mem_nhds
      ((trivializationAt F E q.1).open_baseSet.mem_nhds
        (FiberBundle.mem_baseSet_trivializationAt' q.1))] with q' hq'U hq'b
  exact (congrArg (trivOperator 𝕜 F X q.1 q'.1) (coords_vec hX hq'U q'.2)).symm.trans
    (trivOperator_coords hX hq'U hq'b _)

end Continuity

section Trivialization

variable [Finite ι] [IsRCLikeNormedField 𝕜]

/-- The local trivialization of a family of subspaces `V` given by a local frame `X` on an open
set `U`: over `U`, a vector of `V y` is sent to its coordinates in the frame. The total space of
`V` carries the subspace topology `TauCeti.subbundleTopology`. Only finiteness of the index type
is required; no enumeration is chosen as part of the trivialization. -/
def trivialization (hX : IsSubbundleFrameOn F V X U) (hU : IsOpen U) :
    letI := subbundleTopology F (F' := ι → 𝕜) V
    Trivialization (ι → 𝕜) (π (ι → 𝕜) fun x ↦ V x) :=
  letI := subbundleTopology F (F' := ι → 𝕜) V
  { toFun p := (p.proj, hX.coords p.proj p.2)
    invFun q := TotalSpace.mk' (ι → 𝕜) (E := fun x ↦ V x) q.1 (hX.vec q.1 q.2)
    source := π (ι → 𝕜) (fun x ↦ V x) ⁻¹' U
    target := U ×ˢ univ
    map_source' _ hp := ⟨hp, mem_univ _⟩
    map_target' _ hq := hq.1
    left_inv' p hp := by
      dsimp only
      rw [vec_coords hX hp]
    right_inv' q hq := by
      dsimp only
      rw [coords_vec hX hq.1]
    open_source := hU.preimage (continuous_proj_totalSpace_subbundle F _ V)
    open_target := by exact hU.prod isOpen_univ
    continuousOn_toFun := continuousOn_of_forall_continuousAt fun _ hp ↦
      ((continuous_proj_totalSpace_subbundle F _ V).continuousAt).prodMk
        (continuousAt_coords hX hU hp)
    continuousOn_invFun :=
      continuousOn_of_forall_continuousAt fun _ hq ↦ continuousAt_vec hX hU hq.1
    baseSet := U
    open_baseSet := hU
    source_eq := rfl
    target_eq := rfl
    proj_toFun _ _ := rfl }

variable (hX : IsSubbundleFrameOn F V X U) (hU : IsOpen U)

@[simp]
theorem trivialization_baseSet :
    letI := subbundleTopology F (F' := ι → 𝕜) V
    (hX.trivialization hU).baseSet = U :=
  (rfl)

private theorem trivialization_apply_eq (p : TotalSpace (ι → 𝕜) fun x ↦ V x) :
    letI := subbundleTopology F (F' := ι → 𝕜) V
    hX.trivialization hU p = (p.proj, hX.coords p.proj p.2) :=
  (rfl)

private theorem trivialization_symm_apply_eq (q : B × (ι → 𝕜)) :
    letI := subbundleTopology F (F' := ι → 𝕜) V
    (hX.trivialization hU).toOpenPartialHomeomorph.symm q =
      TotalSpace.mk' (ι → 𝕜) (E := fun x ↦ V x) q.1 (hX.vec q.1 q.2) :=
  (rfl)

/-- Over `U`, the frame trivialization sends a vector to its coordinates in the frame. -/
@[simp]
theorem trivialization_apply {p : TotalSpace (ι → 𝕜) fun x ↦ V x} (hp : p.proj ∈ U) :
    letI := subbundleTopology F (F' := ι → 𝕜) V
    hX.trivialization hU p = (p.proj, (hX.basis hp).equivFun p.2) := by
  rw [trivialization_apply_eq, coords_of_mem hX hp]

/-- Over `U`, the inverse of the frame trivialization sends coordinates to the corresponding
combination of the frame. -/
@[simp]
theorem trivialization_symm_apply {q : B × (ι → 𝕜)} (hq : q.1 ∈ U) :
    letI := subbundleTopology F (F' := ι → 𝕜) V
    (hX.trivialization hU).toOpenPartialHomeomorph.symm q =
      TotalSpace.mk' (ι → 𝕜) (E := fun x ↦ V x) q.1 ((hX.basis hq).equivFun.symm q.2) := by
  rw [trivialization_symm_apply_eq, vec_of_mem hX hq]

/-- The frame trivialization is fibrewise linear. -/
instance isLinear_trivialization :
    letI := subbundleTopology F (F' := ι → 𝕜) V
    (hX.trivialization hU).IsLinear 𝕜 :=
  letI := subbundleTopology F (F' := ι → 𝕜) V
  { linear y _ := by
      simp only [trivialization_apply_eq]
      exact (hX.coords y).isLinear }

/-- The coordinate changes between the trivializations of two local frames of `V` are continuous
on the intersection of their domains. -/
theorem continuousOn_coordChangeL {Y : ι → Π x, E x} {U' : Set B}
    (hY : IsSubbundleFrameOn F V Y U') (hU' : IsOpen U') :
    letI := subbundleTopology F (F' := ι → 𝕜) V
    ContinuousOn (fun y ↦ ((hX.trivialization hU).coordChangeL 𝕜 (hY.trivialization hU') y :
      (ι → 𝕜) →L[𝕜] ι → 𝕜)) (U ∩ U') := by
  let := subbundleTopology F (F' := ι → 𝕜) V
  let := Fintype.ofFinite ι
  have : CompleteSpace 𝕜 := by
    let := IsRCLikeNormedField.rclike 𝕜
    infer_instance
  -- In finite dimension, continuity of the operator family follows from pointwise continuity.
  refine continuousOn_clm_apply.mpr fun c ↦ ?_
  refine ((hY.trivialization hU').continuousOn.comp
    ((hX.trivialization hU).toOpenPartialHomeomorph.continuousOn_symm.comp
      (continuousOn_id.prodMk (continuousOn_const (c := c))) (fun y hy ↦ ?_))
    (fun y hy ↦ ?_)).snd.congr fun y hy ↦ ?_
  · exact (hX.trivialization hU).mem_target.mpr hy.1
  · rw [Function.comp_apply, id_eq, (hY.trivialization hU').mem_source,
      (hX.trivialization hU).proj_symm_apply' hy.1]
    exact hy.2
  · exact ((hX.trivialization hU).coordChangeL_apply' (R := 𝕜) (hY.trivialization hU')
      (by simpa only [trivialization_baseSet] using hy) c)

end Trivialization

end IsSubbundleFrameOn

end Normed

end TauCeti
