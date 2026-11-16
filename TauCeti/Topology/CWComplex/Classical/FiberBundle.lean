/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.CWComplex.Classical.Basic
public import Mathlib.Topology.FiberBundle.Basic
import Mathlib.Topology.Compactness.LocallyCompact

/-!
# Weak topology of bundles with locally compact fibre over a relative CW complex

Let `(C, D)` be a classical relative CW complex in a Hausdorff space `X`, and let `p : Z → X` be
locally trivial with locally compact fibre `Y`. Then `p ⁻¹' C` carries the weak topology of the
preimages `p ⁻¹' closedCell n j` of the closed cells of `C` together with `p ⁻¹' D`
(`Topology.RelCWComplex.closed_of_forall_exists_trivialization`): a subset `A ⊆ p ⁻¹' C` is closed
in `Z` if and only if its intersections with `p ⁻¹' closedCell n j` and with `p ⁻¹' D` are closed.

This generalizes `Topology.RelCWComplex.closed_prod` from trivial products `X × Y` to arbitrary
locally trivial projections with locally compact fibre, such as unit disc bundles, unit sphere
bundles, and total spaces of finite-rank continuous Riemannian vector bundles. Locally over a point
`z₀ ∉ A` with `p z₀ ∈ C`, local compactness of `Y` chooses a compact fibre neighbourhood `K ⊆ Y`
missing the closed slice of `A` over `p z₀`; by the tube lemma and the weak topology of `(C, D)`,
the base set of points outside the chart together with those whose `K`-tube meets `A` is closed in
`X` and misses `p z₀`, separating `z₀` from `A`.

## Main results

* `Topology.RelCWComplex.closed_of_forall_exists_trivialization`: weak-topology characterization of
  closed subsets of `p ⁻¹' C` for a locally trivial map `p : Z → X` with locally compact fibre.
* `FiberBundle.closed_preimage_proj`: specialization to the projection of a fibre bundle with
  locally compact model fibre over a relative CW complex.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Appendix, Theorem A.6, for weak topologies of products with locally compact spaces.
* J. W. Milnor and J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton University Press, 1974, §18, Lemma 18.1 (cells of Thom spaces and disc bundles over CW
  bases).
-/

public section

open Bundle Filter Set Topology

namespace Topology.RelCWComplex

variable {X : Type*} [TopologicalSpace X] [T2Space X]
  {Y : Type*} [TopologicalSpace Y] [LocallyCompactSpace Y]
  {Z : Type*} [TopologicalSpace Z]

omit [T2Space X] [LocallyCompactSpace Y] in
/-- Over a point of `C` in the base set of a local trivialization `e`, the fibre slice in `Y` of a
set `A` having closed intersections with the preimages of `D` and of every closed cell is closed. -/
private lemma isClosed_slice_of_mem_complex {p : Z → X} (C : Set X) {D : Set X} [RelCWComplex C D]
    {A : Set Z} (hcell : ∀ n (j : cell C n), IsClosed (A ∩ p ⁻¹' closedCell n j))
    (hD : IsClosed (A ∩ p ⁻¹' D)) {x : X} (hxC : x ∈ C) (e : Trivialization Y p)
    (hxe : x ∈ e.baseSet) :
    IsClosed {y : Y | e.toOpenPartialHomeomorph.symm (x, y) ∈ A} := by
  have hg : Continuous fun y : Y ↦ e.toOpenPartialHomeomorph.symm (x, y) :=
    e.toOpenPartialHomeomorph.continuousOn_symm.comp_continuous
      (continuous_const.prodMk continuous_id) fun _ ↦ e.mem_target.2 hxe
  have hsub {K : Set X} (hK : IsClosed (A ∩ p ⁻¹' K)) (hxK : x ∈ K) :
      IsClosed {y : Y | e.toOpenPartialHomeomorph.symm (x, y) ∈ A} := by
    convert hK.preimage hg using 1
    ext y
    simp [e.proj_symm_apply' hxe, hxK]
  rw [← RelCWComplex.union (C := C), mem_union, mem_iUnion₂] at hxC
  obtain hxD | ⟨n, j, hxj⟩ := hxC
  exacts [hsub hD hxD, hsub (hcell n j) hxj]

omit [LocallyCompactSpace Y] in
/-- For a compact fibre set `K ⊆ Y` in a local trivialization `e`, the points of `C` either outside
`e.baseSet` or whose `K`-tube meets `A` form a closed subset of `X`. -/
private lemma isClosed_proj_inter_chart_tube {p : Z → X} (C : Set X) {D : Set X} [RelCWComplex C D]
    {A : Set Z} (hcell : ∀ n (j : cell C n), IsClosed (A ∩ p ⁻¹' closedCell n j))
    (hD : IsClosed (A ∩ p ⁻¹' D)) (e : Trivialization Y p) {K : Set Y} (hKc : IsCompact K) :
    IsClosed (C ∩ (e.baseSetᶜ ∪
      {x ∈ e.baseSet | ∃ y ∈ K, e.toOpenPartialHomeomorph.symm (x, y) ∈ A})) := by
  set B : Set X := C ∩ (e.baseSetᶜ ∪
    {x ∈ e.baseSet | ∃ y ∈ K, e.toOpenPartialHomeomorph.symm (x, y) ∈ A})
  have hM {M : Set X} (hMc : IsClosed M) (hAM : IsClosed (A ∩ p ⁻¹' M)) : IsClosed (B ∩ M) := by
    refine isOpen_compl_iff.1 (isOpen_iff_mem_nhds.2 fun x hx ↦ ?_)
    by_cases hxCM : x ∈ C ∩ M
    · have hxe : x ∈ e.baseSet := not_not.1 fun hnot ↦ hx ⟨⟨hxCM.1, Or.inl hnot⟩, hxCM.2⟩
      have hmiss : ∀ y ∈ K, e.toOpenPartialHomeomorph.symm (x, y) ∉ A :=
        fun y hyK hyA ↦ hx ⟨⟨hxCM.1, Or.inr ⟨hxe, y, hyK, hyA⟩⟩, hxCM.2⟩
      let U : Set (X × Y) := e.target ∩ e.toOpenPartialHomeomorph.symm ⁻¹' (A ∩ p ⁻¹' M)ᶜ
      have hUo : IsOpen U := e.toOpenPartialHomeomorph.isOpen_inter_preimage_symm hAM.isOpen_compl
      have hsub : ({x} : Set X) ×ˢ K ⊆ U := by
        rintro ⟨x', y⟩ ⟨rfl, hyK⟩
        exact ⟨e.mem_target.2 hxe, fun hmem ↦ hmiss y hyK hmem.1⟩
      obtain ⟨V, W, hVo, -, hxV, hKW, hVW⟩ :=
        generalized_tube_lemma isCompact_singleton hKc hUo hsub
      filter_upwards [(hVo.inter e.open_baseSet).mem_nhds ⟨hxV (mem_singleton x), hxe⟩]
        with x' ⟨hx'V, hx'e⟩ hx'BM
      rcases hx'BM.1.2 with hnot | ⟨-, y, hyK, hyA⟩
      · exact hnot hx'e
      · exact (hVW ⟨hx'V, hKW hyK⟩).2 ⟨hyA, by simpa [e.proj_symm_apply' hx'e] using hx'BM.2⟩
    · filter_upwards [((RelCWComplex.isClosed (C := C)).inter hMc).isOpen_compl.mem_nhds hxCM]
        with x' hx' hx'BM
      exact hx' ⟨hx'BM.1.1, hx'BM.2⟩
  exact (RelCWComplex.closed C B inter_subset_left).2
    ⟨fun n j ↦ hM isClosed_closedCell (hcell n j), hM (isClosedBase C) hD⟩

/-- **A locally trivial projection with locally compact fibre preserves the weak topology of a
relative CW complex.** Let `(C, D)` be a relative CW complex in a Hausdorff space `X`, and let
`p : Z → X` admit local trivializations with locally compact fibre `Y` around every point of `X`.
Then `A ⊆ p ⁻¹' C` is closed in `Z` if and only if `A ∩ p ⁻¹' closedCell n j` for every cell of
`C` and `A ∩ p ⁻¹' D` are closed in `Z`. -/
theorem closed_of_forall_exists_trivialization {p : Z → X}
    (ht : ∀ x, ∃ e : Trivialization Y p, x ∈ e.baseSet)
    (C : Set X) {D : Set X} [RelCWComplex C D] (A : Set Z) (hA : A ⊆ p ⁻¹' C) :
    IsClosed A ↔
      (∀ n (j : cell C n), IsClosed (A ∩ p ⁻¹' closedCell n j)) ∧ IsClosed (A ∩ p ⁻¹' D) := by
  have hp : Continuous p := continuous_iff_continuousAt.2 fun z ↦ by
    obtain ⟨e, he⟩ := ht (p z)
    have hz : z ∈ e.source := e.mem_source.2 he
    exact (continuous_fst.continuousAt.comp (e.continuousAt hz)).congr
      (Filter.eventually_of_mem (e.open_source.mem_nhds hz) fun _ hw ↦ e.coe_fst hw)
  refine ⟨fun h ↦ ⟨fun n j ↦ h.inter (isClosed_closedCell.preimage hp),
    h.inter ((isClosedBase C).preimage hp)⟩, fun ⟨hcell, hD⟩ ↦ ?_⟩
  -- Separate any point `z₀ ∉ A` from `A`: outside `p ⁻¹' C` use openness of `Cᶜ`; over `C` choose a
  -- compact fibre neighbourhood `K` missing the slice of `A` and use the closed base set `B`.
  refine isOpen_compl_iff.1 (isOpen_iff_mem_nhds.2 fun z₀ hz₀ ↦ ?_)
  by_cases hx₀ : p z₀ ∈ C
  · obtain ⟨e, he⟩ := ht (p z₀)
    have hz₀_src : z₀ ∈ e.source := e.mem_source.2 he
    have hz₀_slice : (e z₀).2 ∉ {y : Y | e.toOpenPartialHomeomorph.symm (p z₀, y) ∈ A} := by
      intro hmem
      exact hz₀ (e.symm_apply_mk_proj hz₀_src ▸ hmem)
    obtain ⟨K, hK_nhds, hKA, hKc⟩ := local_compact_nhds
      ((isClosed_slice_of_mem_complex C hcell hD hx₀ e he).isOpen_compl.mem_nhds hz₀_slice)
    let B : Set X := C ∩ (e.baseSetᶜ ∪
      {x ∈ e.baseSet | ∃ y ∈ K, e.toOpenPartialHomeomorph.symm (x, y) ∈ A})
    have hBc : IsClosed B := isClosed_proj_inter_chart_tube C hcell hD e hKc
    have hpz₀ : p z₀ ∉ B := by
      rintro ⟨-, hnot | ⟨-, y, hyK, hyA⟩⟩
      · exact hnot he
      · exact hKA hyK hyA
    have hU₁ : p ⁻¹' Bᶜ ∈ 𝓝 z₀ := (hBc.isOpen_compl.preimage hp).mem_nhds hpz₀
    have hU₂ : e.source ∈ 𝓝 z₀ := e.open_source.mem_nhds hz₀_src
    have hU₃ : (fun z ↦ (e z).2) ⁻¹' K ∈ 𝓝 z₀ :=
      (continuous_snd.continuousAt.comp (e.continuousAt hz₀_src)).preimage_mem_nhds hK_nhds
    filter_upwards [inter_mem hU₁ (inter_mem hU₂ hU₃)] with z ⟨hzB, hz_src, hzK⟩ hzA
    exact hzB ⟨hA hzA, Or.inr ⟨e.mem_source.1 hz_src, (e z).2, hzK,
      by rwa [e.symm_apply_mk_proj hz_src]⟩⟩
  · filter_upwards [(RelCWComplex.isClosed (C := C)).isOpen_compl.preimage hp |>.mem_nhds hx₀]
      with z hz hzA
    exact hz (hA hzA)

end Topology.RelCWComplex

/-- **The projection of a fibre bundle with locally compact model fibre preserves the weak topology
of a relative CW complex.** -/
theorem FiberBundle.closed_preimage_proj {B F : Type*} [TopologicalSpace B] [T2Space B]
    [TopologicalSpace F] [LocallyCompactSpace F] (E : B → Type*)
    [TopologicalSpace (TotalSpace F E)] [∀ b, TopologicalSpace (E b)] [FiberBundle F E]
    (C : Set B) {D : Set B} [Topology.RelCWComplex C D]
    (A : Set (TotalSpace F E)) (hA : A ⊆ π F E ⁻¹' C) :
    IsClosed A ↔
      (∀ n (j : Topology.RelCWComplex.cell C n),
        IsClosed (A ∩ π F E ⁻¹' Topology.RelCWComplex.closedCell n j)) ∧
      IsClosed (A ∩ π F E ⁻¹' D) :=
  Topology.RelCWComplex.closed_of_forall_exists_trivialization
    (fun x ↦ ⟨trivializationAt F E x, FiberBundle.mem_baseSet_trivializationAt F E x⟩) C A hA
