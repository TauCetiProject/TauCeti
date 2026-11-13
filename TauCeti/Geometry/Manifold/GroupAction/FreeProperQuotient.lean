/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GroupAction.Free
public import TauCeti.Geometry.Manifold.GroupAction.Orbit
public import TauCeti.Geometry.Manifold.GroupAction.TransverseSlice
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic
public import TauCeti.Geometry.Manifold.Submersion.Split
public import TauCeti.Topology.Algebra.ProperAction.TransverseSlice
import TauCeti.Geometry.Manifold.GroupAction.SliceChart
import TauCeti.Topology.Algebra.GroupAction.SliceChart

/-!
# The quotient manifold theorem for free proper actions

Let a finite-dimensional real Lie group `G` act smoothly, freely and properly on a
finite-dimensional boundaryless manifold `M`. This file proves that the orbit space `M ⧸ G`, with
its quotient topology, carries charts modelled on `ℝ^(dim M - dim G)` making it a smooth manifold
for which the orbit projection `M → M ⧸ G` is a submersion
(`TauCeti.exists_freeProperQuotient_isSubmersion`).

The charts are built from slices. A *slice tube* is a smooth map `σ : S → M` and an open set
`U ⊆ S` such that the slice map `Φ (g, s) = g • σ s` is injective on `G × U` and a local
diffeomorphism at each of its points. Then:

* The map `ψ s = ⟦σ s⟧ : U → M ⧸ G` is an open embedding
  (`TauCeti.MulAction.isOpenEmbedding_quotientMk_slice`), so it is an open partial homeomorphism
  `TauCeti.sliceOrbitOpenPartialHomeomorph` with source `U`.
* The slice coordinate of the orbit of a smooth map into `M` is smooth
  (`TauCeti.exists_contMDiffAt_quotientMk_slice_eq_iff`). Applied to the slice of another slice
  tube, this makes the change of orbit charts `ψ₂⁻¹ ∘ ψ₁` smooth
  (`TauCeti.contMDiffOn_sliceOrbitOpenPartialHomeomorph_symm_comp`); applied to the identity, it
  writes the orbit projection near a point as `ψ` composed with a smooth slice coordinate.
* The orbit projection satisfies `⟦·⟧ ∘ Φ = ψ ∘ pr₂`.

Slice tubes exist through every point of a free proper action
(`TauCeti.exists_sliceTube_of_stabilizer_eq_bot`). A free point is locally free, so the chart
slice `v ↦ φ⁻¹ (φ x + L v)` along a linear parametrization `L` of a complement of the orbit tangent
space `𝔤 · x` makes `Φ` a local diffeomorphism at `(1, 0)`
(`TauCeti.isLocalDiffeomorphAt_smul_extChartAt_symm`). This persists along `G × U` for `U` near
`0` (`IsLocalDiffeomorphAt.eventually_forall_smul_slice`), and properness makes `Φ` injective on
`G × U` after shrinking `U` (`ProperSMul.exists_mem_nhds_injOn_smul_slice`). The complement has
dimension `dim M - dim G`, so every slice is parametrized by the same model space.

Neither Hausdorffness nor second countability of `M` or `G` is used, and `M` may be empty. The
charted space `TauCeti.freeProperChartedSpace` is a definition rather than an instance, since
discrete groups acting properly discontinuously already carry the pushed-forward charts of
`MulAction.instChartedSpaceQuotient`, with a different model space.

## Main definitions

* `TauCeti.sliceOrbitOpenPartialHomeomorph`: the orbit chart `s ↦ ⟦σ s⟧` of a slice tube.
* `TauCeti.freeProperChartedSpace`: the charts on the orbit space of a free proper action given by
  inverses of orbit charts of chosen slice tubes.

## Main results

* `IsLocalDiffeomorphAt.exists_sliceTube`: a transverse slice through a free point of a proper
  action can be shrunk to a slice tube.
* `TauCeti.contMDiffOn_sliceOrbitOpenPartialHomeomorph_symm_comp`: orbit charts of slice tubes are
  smoothly compatible.
* `TauCeti.isManifold_freeProperChartedSpace`: the orbit space of a free proper action is a smooth
  manifold.
* `TauCeti.isSubmersion_quotientMk_freeProperChartedSpace`: the orbit projection is a submersion.
* `TauCeti.contMDiff_iff_contMDiff_comp_quotientMk_freeProperChartedSpace`: a map out of the orbit
  space is smooth if and only if its composite with the orbit projection is.
* `TauCeti.exists_freeProperQuotient_isSubmersion`: the quotient manifold theorem.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer, 2013, Theorem 21.10 (the
  quotient manifold theorem) and its proof.
* E. Meinrenken, *Group actions on manifolds*, lecture notes, University of Toronto, 2003,
  Theorem 1.21 and its proof.
-/

public section

noncomputable section

open Function Set Filter Manifold Topology MulAction
open scoped ContDiff Manifold

namespace TauCeti

section SliceTube

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H' M] [MulAction G M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {K : Type*} [TopologicalSpace K] {J : ModelWithCorners ℝ F K}
  {S : Type*} [TopologicalSpace S] [ChartedSpace K S]
  {σ : S → M} {U : Set S} {n : ℕ∞ω}

/-- A slice is as smooth at `s` as its slice map `(g, s) ↦ g • σ s` is at `(1, s)`. -/
theorem contMDiffAt_slice {s : S}
    (h : ContMDiffAt (I.prod J) I' n (fun p : G × S ↦ p.1 • σ p.2) (1, s)) :
    ContMDiffAt J I' n σ s := by
  simpa only [comp_def, one_smul] using h.comp s (contMDiffAt_const.prodMk contMDiffAt_id)

/-- The slice of a slice tube is as smooth as its slice map. -/
theorem contMDiffOn_slice
    (hΦ : IsLocalDiffeomorphOn (I.prod J) I' n (fun p : G × S ↦ p.1 • σ p.2) (univ ×ˢ U)) :
    ContMDiffOn J I' n σ U := fun s hs ↦
  (contMDiffAt_slice (hΦ ⟨(1, s), ⟨mem_univ _, hs⟩⟩).contMDiffAt).contMDiffWithinAt

/-- **Slice tubes from transverse slices.** If the slice map `(g, s) ↦ g • σ s` of a proper action
is a local diffeomorphism at `(1, s₀)` and `σ s₀` has trivial stabilizer, then for some open
neighbourhood `U` of `s₀` the slice map is injective on the tube `G × U` and a local
diffeomorphism at each point of it. -/
theorem _root_.IsLocalDiffeomorphAt.exists_sliceTube [LieGroup I n G] [ContMDiffSMul I I' n G M]
    [ProperSMul G M] {s₀ : S}
    (h : IsLocalDiffeomorphAt (I.prod J) I' n (fun p : G × S ↦ p.1 • σ p.2) (1, s₀))
    (hfree : stabilizer G (σ s₀) = ⊥) :
    ∃ U : Set S, IsOpen U ∧ s₀ ∈ U ∧ InjOn (fun p : G × S ↦ p.1 • σ p.2) (univ ×ˢ U) ∧
      IsLocalDiffeomorphOn (I.prod J) I' n (fun p : G × S ↦ p.1 • σ p.2) (univ ×ˢ U) := by
  have hσ : ContinuousAt σ s₀ := (contMDiffAt_slice h.contMDiffAt).continuousAt
  obtain ⟨N, hN, hinjN⟩ := h.exists_mem_nhds_injOn
  obtain ⟨U₁, hU₁, hinj₁⟩ := ProperSMul.exists_mem_nhds_injOn_smul_slice hσ hfree hN hinjN
  obtain ⟨U, hsub, hU, hs₀⟩ := mem_nhds_iff.mp (inter_mem hU₁ h.eventually_forall_smul_slice)
  refine ⟨U, hU, hs₀, hinj₁.mono (prod_mono subset_rfl fun s hs ↦ (hsub hs).1), ?_⟩
  rintro ⟨⟨g, s⟩, -, hs⟩
  exact (hsub hs).2 g

variable [Nonempty S]

variable (σ) in
/-- **The orbit chart of a slice tube.** For a slice tube `(σ, U)`, the map `s ↦ ⟦σ s⟧` is an open
partial homeomorphism from the slice manifold to the orbit space, with source `U`. -/
def sliceOrbitOpenPartialHomeomorph (hU : IsOpen U)
    (hinj : InjOn (fun p : G × S ↦ p.1 • σ p.2) (univ ×ˢ U))
    (hΦ : IsLocalDiffeomorphOn (I.prod J) I' n (fun p : G × S ↦ p.1 • σ p.2) (univ ×ˢ U)) :
    OpenPartialHomeomorph S (orbitRel.Quotient G M) :=
  OpenPartialHomeomorph.ofContinuousOpenRestrict
    ((MulAction.injOn_quotientMk_slice hinj).toPartialEquiv _ U)
    (continuousOn_iff_continuous_domRestrict.mpr
      (MulAction.isOpenEmbedding_quotientMk_slice hU hinj hΦ.isLocalHomeomorphOn).continuous)
    (MulAction.isOpenEmbedding_quotientMk_slice hU hinj hΦ.isLocalHomeomorphOn).isOpenMap
    hU

variable {hU : IsOpen U} {hinj : InjOn (fun p : G × S ↦ p.1 • σ p.2) (univ ×ˢ U)}
  {hΦ : IsLocalDiffeomorphOn (I.prod J) I' n (fun p : G × S ↦ p.1 • σ p.2) (univ ×ˢ U)}

/-- The orbit chart of a slice tube sends `s` to the orbit of `σ s`. -/
@[simp]
theorem sliceOrbitOpenPartialHomeomorph_apply (s : S) :
    sliceOrbitOpenPartialHomeomorph σ hU hinj hΦ s = Quotient.mk (orbitRel G M) (σ s) := (rfl)

/-- The orbit chart of a slice tube is defined on the slice parameters `U` of the tube. -/
@[simp]
theorem sliceOrbitOpenPartialHomeomorph_source :
    (sliceOrbitOpenPartialHomeomorph σ hU hinj hΦ).source = U :=
  (rfl)

/-- The orbit chart of a slice tube takes values in the orbits through the slice. -/
@[simp]
theorem sliceOrbitOpenPartialHomeomorph_target :
    (sliceOrbitOpenPartialHomeomorph σ hU hinj hΦ).target =
      (fun s ↦ Quotient.mk (orbitRel G M) (σ s)) '' U :=
  (rfl)

variable {S₂ : Type*} [TopologicalSpace S₂] [ChartedSpace K S₂] [Nonempty S₂]
  {σ₂ : S₂ → M} {U₂ : Set S₂} {hU₂ : IsOpen U₂}
  {hinj₂ : InjOn (fun p : G × S₂ ↦ p.1 • σ₂ p.2) (univ ×ˢ U₂)}
  {hΦ₂ : IsLocalDiffeomorphOn (I.prod J) I' n (fun p : G × S₂ ↦ p.1 • σ₂ p.2) (univ ×ˢ U₂)}

/-- **Orbit charts of slice tubes are smoothly compatible.** For two slice tubes, the change of
orbit charts `ψ₂⁻¹ ∘ ψ₁` is smooth on its domain: near each point it is
`s ↦ pr₂ (Φ₂⁻¹ (σ₁ s))`. -/
theorem contMDiffOn_sliceOrbitOpenPartialHomeomorph_symm_comp :
    ContMDiffOn J J n
      ((sliceOrbitOpenPartialHomeomorph σ₂ hU₂ hinj₂ hΦ₂).symm ∘
        sliceOrbitOpenPartialHomeomorph σ hU hinj hΦ)
      ((sliceOrbitOpenPartialHomeomorph σ hU hinj hΦ).trans
        (sliceOrbitOpenPartialHomeomorph σ₂ hU₂ hinj₂ hΦ₂).symm).source := by
  rintro s ⟨hs, hs₂⟩
  simp only [mem_preimage, OpenPartialHomeomorph.symm_source,
    sliceOrbitOpenPartialHomeomorph_target] at hs₂
  -- The orbit of `σ s` meets the second slice; read off the slice coordinate of `σ s'` near `s`.
  obtain ⟨w, hw, hws⟩ := hs₂
  obtain ⟨t, ht, -, hev⟩ := exists_contMDiffAt_quotientMk_slice_eq_iff hU₂ hinj₂ hΦ₂
    ((contMDiffOn_slice hΦ).contMDiffAt (hU.mem_nhds hs)) hw hws
  refine (ht.congr_of_eventuallyEq ?_).contMDiffWithinAt
  filter_upwards [hev] with s' ⟨htU, hiff⟩
  rw [comp_apply, sliceOrbitOpenPartialHomeomorph_apply, ← (hiff _ htU).mpr rfl]
  exact (sliceOrbitOpenPartialHomeomorph σ₂ hU₂ hinj₂ hΦ₂).left_inv htU

end SliceTube

section Quotient

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'} [I'.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H' M] [IsManifold I' ∞ M] [MulAction G M]
  [ContMDiffSMul I I' ∞ G M] [ProperSMul G M]

/-- **Slice tubes through free points.** Through every point `x` with trivial stabilizer of a
smooth proper action there is a slice tube parametrized by `ℝ^(dim M - dim G)`: a map `σ` with
`σ 0 = x` and an open neighbourhood `U` of `0` such that `(g, v) ↦ g • σ v` is injective on
`G × U` and a local diffeomorphism at each point of it. -/
theorem exists_sliceTube_of_stabilizer_eq_bot {x : M} (hx : stabilizer G x = ⊥) :
    ∃ σ : (Fin (Module.finrank ℝ E' - Module.finrank ℝ E) → ℝ) → M,
      ∃ U : Set (Fin (Module.finrank ℝ E' - Module.finrank ℝ E) → ℝ),
      σ 0 = x ∧ IsOpen U ∧ 0 ∈ U ∧ InjOn (fun p : G × _ ↦ p.1 • σ p.2) (univ ×ˢ U) ∧
        IsLocalDiffeomorphOn (I.prod 𝓘(ℝ, Fin (Module.finrank ℝ E' - Module.finrank ℝ E) → ℝ))
          I' ∞ (fun p : G × _ ↦ p.1 • σ p.2) (univ ×ˢ U) := by
  have : CompleteSpace E := FiniteDimensional.completeSpace ℝ E
  have : CompleteSpace E' := FiniteDimensional.completeSpace ℝ E'
  set F := Fin (Module.finrank ℝ E' - Module.finrank ℝ E) → ℝ
  have : T2Space G := I.t2Space_of_lieGroup ∞
  have : T2Space M := t2Space_of_properSMul_of_t1Group (G := G)
  -- A free point is locally free.
  have hloc : (InfinitesimalAction.fundamental I G I' M).isotropy x = ⊥ := by
    have : Subsingleton (stabilizer G x) := by
      rw [hx]
      infer_instance
    exact (Lie.discreteTopology_stabilizer_iff_isotropy_eq_bot (I := I) (I' := I')).1
      inferInstance
  -- Parametrize a complement `W` of the orbit tangent space by `F`.
  obtain ⟨W, hW⟩ : ∃ W : Submodule ℝ E',
      IsCompl ((InfinitesimalAction.fundamental I G I' M).orbitTangent x) W :=
    Submodule.exists_isCompl _
  have hdim : Module.finrank ℝ F = Module.finrank ℝ W := by
    have h₁ : Module.finrank ℝ E + Module.finrank ℝ W = Module.finrank ℝ E' := by
      have h := Submodule.finrank_add_eq_of_isCompl hW
      rw [InfinitesimalAction.finrank_orbitTangent_of_isotropy_eq_bot _ _ hloc] at h
      -- By definition, the Lie algebra of `G` is the model space `E` and `T_x M` is `E'`.
      exact h
    rw [Module.finrank_fin_fun]
    omega
  let e : F ≃L[ℝ] W := ContinuousLinearEquiv.ofFinrankEq hdim
  -- The chart slice `v ↦ φ⁻¹ (φ x + L v)`, where `L` parametrizes `W` by `F`.
  set φ := extChartAt I' x
  let L : F →L[ℝ] E' := W.subtypeL.comp (e : F →L[ℝ] W)
  let σ : F → M := fun v ↦ φ.symm (φ x + L v)
  have hrange : LinearMap.range (L : F →ₗ[ℝ] E') = W :=
    (LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_eq_top.2 e.surjective)).trans
      W.range_subtype
  have h₁ : IsLocalDiffeomorphAt (I.prod 𝓘(ℝ, F)) I' ∞ (fun p : G × F ↦ p.1 • σ p.2) (1, 0) :=
    isLocalDiffeomorphAt_smul_extChartAt_symm (G := G) hloc
      (W.injective_subtype.comp e.injective) (hrange ▸ hW)
  have hσ₀ : σ 0 = x := by simp [σ, φ]
  obtain ⟨U, hU, h0, hinj, hΦ⟩ := h₁.exists_sliceTube (by rwa [hσ₀])
  exact ⟨σ, U, hσ₀, hU, h0, hinj, hΦ⟩

section IsCancelSMul

variable [IsCancelSMul G M]

/-- Through every point `x` of a free proper action there is the inverse of the orbit chart of a
slice tube whose slice passes through `x`. -/
private theorem exists_eq_sliceOrbitOpenPartialHomeomorph_symm (x : M) :
    ∃ ψ : OpenPartialHomeomorph (orbitRel.Quotient G M)
        (Fin (Module.finrank ℝ E' - Module.finrank ℝ E) → ℝ),
      ∃ (σ : (Fin (Module.finrank ℝ E' - Module.finrank ℝ E) → ℝ) → M)
        (U : Set (Fin (Module.finrank ℝ E' - Module.finrank ℝ E) → ℝ)) (hU : IsOpen U)
        (hinj : InjOn (fun p : G × _ ↦ p.1 • σ p.2) (univ ×ˢ U))
        (hΦ : IsLocalDiffeomorphOn
          (I.prod 𝓘(ℝ, Fin (Module.finrank ℝ E' - Module.finrank ℝ E) → ℝ))
          I' ∞ (fun p : G × _ ↦ p.1 • σ p.2) (univ ×ˢ U)),
        σ 0 = x ∧ 0 ∈ U ∧ ψ = (sliceOrbitOpenPartialHomeomorph σ hU hinj hΦ).symm := by
  obtain ⟨σ, U, hσ₀, hU, h0, hinj, hΦ⟩ := exists_sliceTube_of_stabilizer_eq_bot (I := I)
    (I' := I') (IsCancelSMul.stabilizer_eq_bot (G := G) x)
  exact ⟨_, σ, U, hU, hinj, hΦ, hσ₀, h0, rfl⟩

variable (I G I') in
/-- The orbit chart at `x` of a free proper action: the inverse of the orbit chart of a chosen slice
tube through `x`, parametrized by `ℝ^(dim M - dim G)`. -/
def freeProperSliceChart (x : M) :
    OpenPartialHomeomorph (orbitRel.Quotient G M)
      (Fin (Module.finrank ℝ E' - Module.finrank ℝ E) → ℝ) :=
  (exists_eq_sliceOrbitOpenPartialHomeomorph_symm (I := I) (G := G) (I' := I') x).choose

/-- Every orbit chart of a free proper action is the inverse of the orbit chart of a slice tube
whose slice passes through the base point. -/
theorem exists_freeProperSliceChart_eq (x : M) :
    ∃ (σ : (Fin (Module.finrank ℝ E' - Module.finrank ℝ E) → ℝ) → M)
      (U : Set (Fin (Module.finrank ℝ E' - Module.finrank ℝ E) → ℝ)) (hU : IsOpen U)
      (hinj : InjOn (fun p : G × _ ↦ p.1 • σ p.2) (univ ×ˢ U))
      (hΦ : IsLocalDiffeomorphOn (I.prod 𝓘(ℝ, Fin (Module.finrank ℝ E' - Module.finrank ℝ E) → ℝ))
        I' ∞ (fun p : G × _ ↦ p.1 • σ p.2) (univ ×ˢ U)),
      σ 0 = x ∧ 0 ∈ U ∧
        freeProperSliceChart I G I' x = (sliceOrbitOpenPartialHomeomorph σ hU hinj hΦ).symm :=
  (exists_eq_sliceOrbitOpenPartialHomeomorph_symm (I := I) (G := G) (I' := I') x).choose_spec

variable (I G I' M) in
/-- **The charts of the orbit space of a free proper action.** The chart at an orbit `q` is the
orbit chart `TauCeti.freeProperSliceChart` at the representative `q.out`; the atlas consists of
the orbit charts at all points. This is not an instance: see the module docstring. -/
@[instance_reducible]
def freeProperChartedSpace :
    ChartedSpace (Fin (Module.finrank ℝ E' - Module.finrank ℝ E) → ℝ) (orbitRel.Quotient G M) where
  atlas := range (freeProperSliceChart I G I')
  chartAt q := freeProperSliceChart I G I' q.out
  mem_chart_source q := by
    obtain ⟨σ, U, hU, hinj, hΦ, hσ₀, h0, heq⟩ :=
      exists_freeProperSliceChart_eq (I := I) (G := G) (I' := I') q.out
    rw [heq, OpenPartialHomeomorph.symm_source, sliceOrbitOpenPartialHomeomorph_target]
    exact ⟨0, h0, by simp only [hσ₀, Quotient.out_eq]⟩
  chart_mem_atlas q := mem_range_self _

/-- The chart of `TauCeti.freeProperChartedSpace` at an orbit `q` is the orbit chart at its
representative `q.out`. -/
theorem chartAt_freeProperChartedSpace (q : orbitRel.Quotient G M) :
    letI := freeProperChartedSpace I G I' M
    chartAt (Fin (Module.finrank ℝ E' - Module.finrank ℝ E) → ℝ) q =
      freeProperSliceChart I G I' q.out :=
  (rfl)

/-- The atlas of `TauCeti.freeProperChartedSpace` consists of the orbit charts at all points. -/
theorem atlas_freeProperChartedSpace :
    letI := freeProperChartedSpace I G I' M
    atlas (Fin (Module.finrank ℝ E' - Module.finrank ℝ E) → ℝ) (orbitRel.Quotient G M) =
      range (freeProperSliceChart I G I') :=
  (rfl)

/-- **The orbit space of a free proper action is a smooth manifold**, for the charts of
`TauCeti.freeProperChartedSpace`. -/
theorem isManifold_freeProperChartedSpace :
    letI := freeProperChartedSpace I G I' M
    IsManifold 𝓘(ℝ, Fin (Module.finrank ℝ E' - Module.finrank ℝ E) → ℝ) ∞
      (orbitRel.Quotient G M) := by
  let := freeProperChartedSpace I G I' M
  refine isManifold_of_contDiffOn _ _ _ ?_
  rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
  obtain ⟨σ, U, hU, hinj, hΦ, -, -, hx⟩ :=
    exists_freeProperSliceChart_eq (I := I) (G := G) (I' := I') x
  obtain ⟨σ₂, U₂, hU₂, hinj₂, hΦ₂, -, -, hy⟩ :=
    exists_freeProperSliceChart_eq (I := I) (G := G) (I' := I') y
  rw [hx, hy, OpenPartialHomeomorph.symm_symm]
  simp only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, CompTriple.comp_eq,
    preimage_id_eq, id_eq, range_id, inter_univ]
  exact contMDiffOn_iff_contDiffOn.mp contMDiffOn_sliceOrbitOpenPartialHomeomorph_symm_comp

/-- **The orbit projection of a free proper action is a submersion**, for the manifold structure of
`TauCeti.freeProperChartedSpace`. -/
theorem isSubmersion_quotientMk_freeProperChartedSpace :
    letI := freeProperChartedSpace I G I' M
    IsSubmersion I' 𝓘(ℝ, Fin (Module.finrank ℝ E' - Module.finrank ℝ E) → ℝ) ∞
      (Quotient.mk (orbitRel G M)) := by
  let := freeProperChartedSpace I G I' M
  have := isManifold_freeProperChartedSpace (I := I) (G := G) (I' := I') (M := M)
  set F := Fin (Module.finrank ℝ E' - Module.finrank ℝ E) → ℝ
  -- Near `y`, read the projection through the slice tube of the chart at the orbit of `y`.
  have key : ∀ y : M, ContMDiffAt I' 𝓘(ℝ, F) ∞ (Quotient.mk (orbitRel G M)) y ∧
      Surjective (mfderiv I' 𝓘(ℝ, F) (Quotient.mk (orbitRel G M)) y) := by
    intro y
    obtain ⟨σ, U, hU, hinj, hΦ, hσ₀, h0, heq⟩ :=
      exists_freeProperSliceChart_eq (I := I) (G := G) (I' := I') (Quotient.mk (orbitRel G M) y).out
    set ψ := sliceOrbitOpenPartialHomeomorph σ hU hinj hΦ
    set Φ := fun p : G × F ↦ p.1 • σ p.2
    have hψ : ψ.symm ∈ atlas F (orbitRel.Quotient G M) := ⟨_, heq⟩
    -- The orbit chart `ψ` is a local diffeomorphism on `U`, as the inverse of a chart.
    have hψd : ∀ s ∈ U, IsLocalDiffeomorphAt 𝓘(ℝ, F) 𝓘(ℝ, F) ∞ ψ s := fun s hs ↦ by
      simpa only [OpenPartialHomeomorph.symm_symm] using
        ψ.symm.isLocalDiffeomorphAt_symm_of_mem_maximalAtlas
          (IsManifold.subset_maximalAtlas hψ) (by simpa [ψ] using hs)
    -- `y` is a translate `g • σ 0` of the chosen representative of its orbit.
    obtain ⟨g, hg⟩ := MulAction.exists_smul_out_eq (G := G) (y := y) rfl
    set p : G × F := (g, 0)
    have hp : p ∈ univ ×ˢ U := ⟨mem_univ _, h0⟩
    have hΦp : Φ p = y := by simp [p, Φ, hσ₀, hg]
    refine ⟨?_, ?_⟩
    · -- Near `y`, the projection is `ψ ∘ t` for the smooth slice coordinate `t`.
      obtain ⟨t, ht, ht0, hev⟩ := exists_contMDiffAt_quotientMk_slice_eq_iff hU hinj hΦ
        (contMDiffAt_id (x := y)) h0 (by simp [hσ₀])
      refine ((hψd _ h0).contMDiffAt.comp_of_eq ht ht0).congr_of_eventuallyEq ?_
      filter_upwards [hev] with z ⟨htU, hiff⟩
      exact ((hiff _ htU).mpr rfl).symm
    · -- The projection composed with `Φ` is `ψ ∘ pr₂`, whose differential is onto.
      have hcomp : Quotient.mk (orbitRel G M) ∘ Φ = ψ ∘ Prod.snd := funext fun q ↦
        Quotient.sound (orbitRel_apply.mpr (mem_orbit (σ q.2) q.1))
      have hrange := (hΦ ⟨p, hp⟩).range_mfderiv_comp (K := 𝓘(ℝ, F))
        (g := Quotient.mk (orbitRel G M))
        (by simp)
      rw [hcomp, hΦp] at hrange
      have hψp := hψd _ hp.2
      rw [mfderiv_comp p (hψp.mdifferentiableAt (by simp)) mdifferentiableAt_snd, mfderiv_snd]
        at hrange
      refine LinearMap.range_eq_top.mp ?_
      rw [← hrange]
      refine LinearMap.range_eq_top.mpr fun v ↦ ?_
      obtain ⟨u, hu⟩ := (hψp.isInvertible_mfderiv (by simp)).surjective v
      exact ⟨(0, u), hu⟩
  exact (ContMDiff.isSubmersionOfComplement_of_surjective_mfderiv (fun y ↦ (key y).1)
    (by simp) fun y ↦ (key y).2).isSubmersion

/-- **Smooth maps out of the orbit space of a free proper action.** For `n ≤ ∞`, a map `f` out of
the orbit space is `C^n` for the charts of `TauCeti.freeProperChartedSpace` if and only if
`f ∘ ⟦·⟧` is `C^n` on `M`. -/
theorem contMDiff_iff_contMDiff_comp_quotientMk_freeProperChartedSpace
    {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace ℝ E'']
    {H'' : Type*} [TopologicalSpace H''] {I'' : ModelWithCorners ℝ E'' H''}
    {N : Type*} [TopologicalSpace N] [ChartedSpace H'' N] {n : ℕ∞ω} (hn : n ≤ ∞)
    {f : orbitRel.Quotient G M → N} :
    letI := freeProperChartedSpace I G I' M
    ContMDiff 𝓘(ℝ, Fin (Module.finrank ℝ E' - Module.finrank ℝ E) → ℝ) I'' n f ↔
      ContMDiff I' I'' n (f ∘ Quotient.mk (orbitRel G M)) := by
  let := freeProperChartedSpace I G I' M
  have := isManifold_freeProperChartedSpace (I := I) (G := G) (I' := I') (M := M)
  set F := Fin (Module.finrank ℝ E' - Module.finrank ℝ E) → ℝ
  refine ⟨fun hf ↦ hf.comp ((isSubmersion_quotientMk_freeProperChartedSpace (I := I) (G := G)
    (I' := I') (M := M)).contMDiff.of_le hn), fun hf q ↦ ?_⟩
  -- Near `q`, `f` is `f ∘ ⟦·⟧ ∘ σ ∘ ψ⁻¹` for the slice tube `(σ, U)` of the chart `ψ⁻¹` at `q`.
  obtain ⟨σ, U, hU, hinj, hΦ, -, -, heq⟩ :=
    exists_freeProperSliceChart_eq (I := I) (G := G) (I' := I') q.out
  set ψ := sliceOrbitOpenPartialHomeomorph σ hU hinj hΦ
  have : IsManifold 𝓘(ℝ, F) n (orbitRel.Quotient G M) := IsManifold.of_le hn
  have hψ : ContMDiffOn 𝓘(ℝ, F) 𝓘(ℝ, F) n ψ.symm ψ.symm.source :=
    contMDiffOn_of_mem_maximalAtlas (IsManifold.subset_maximalAtlas ⟨_, heq⟩)
  have hσ : ContMDiffOn 𝓘(ℝ, F) I' n σ U := (contMDiffOn_slice hΦ).of_le hn
  have hq : q ∈ ψ.symm.source := by
    rw [← heq]
    exact mem_chart_source F q
  have hopen := ψ.symm.open_source.mem_nhds hq
  refine ((hf.comp_contMDiffOn (hσ.comp hψ fun _ h ↦ ψ.map_target h)).contMDiffAt
    hopen).congr_of_eventuallyEq ?_
  filter_upwards [hopen] with q' hq'
  exact congrArg f (ψ.right_inv hq').symm

end IsCancelSMul

variable (I) in
include I in
/-- **The quotient manifold theorem for free proper actions.** Let a finite-dimensional real Lie
group `G` act smoothly, freely and properly on a finite-dimensional boundaryless manifold `M`.
Then the orbit space, with its quotient topology, admits charts modelled on `ℝ^(dim M - dim G)`
making it a smooth manifold for which the orbit projection is a submersion. -/
theorem exists_freeProperQuotient_isSubmersion (hfree : ∀ (g : G) (x : M), g • x = x → g = 1) :
    ∃ _ : ChartedSpace (Fin (Module.finrank ℝ E' - Module.finrank ℝ E) → ℝ)
        (orbitRel.Quotient G M),
      IsManifold 𝓘(ℝ, Fin (Module.finrank ℝ E' - Module.finrank ℝ E) → ℝ) ∞
          (orbitRel.Quotient G M) ∧
        IsSubmersion I' 𝓘(ℝ, Fin (Module.finrank ℝ E' - Module.finrank ℝ E) → ℝ) ∞
          (Quotient.mk (orbitRel G M)) := by
  have := isCancelSMul_iff_eq_one_of_smul_eq.mpr hfree
  exact ⟨freeProperChartedSpace I G I' M, isManifold_freeProperChartedSpace,
    isSubmersion_quotientMk_freeProperChartedSpace⟩

end Quotient

end TauCeti
