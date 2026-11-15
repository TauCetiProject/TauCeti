/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.CWComplex.Classical.Basic
public import TauCeti.Topology.FiberBundle.Proper

/-!
# Weak topology of bundles with compact regular fibre over a relative CW complex

Let `(C, D)` be a classical relative CW complex in a Hausdorff space `X`, and let `p : Z → X` be
locally trivial with compact regular fibre `Y`. Then `p ⁻¹' C` carries the weak topology of the
preimages `p ⁻¹' closedCell n j` of the closed cells of `C` together with `p ⁻¹' D`
(`Topology.RelCWComplex.closed_of_forall_exists_trivialization`): a subset `A ⊆ p ⁻¹' C` is closed
in `Z` if and only if its intersections with `p ⁻¹' closedCell n j` and with `p ⁻¹' D` are closed.

This generalizes `Topology.RelCWComplex.closed_prod` from trivial products `X × Y` to arbitrary
locally trivial projections with compact regular fibre, such as unit disc and unit sphere bundles
of finite-rank continuous Riemannian vector bundles. Because `Y` is compact, `p` is proper
(`TauCeti.isProperMap_of_forall_exists_trivialization`) and therefore a closed map; locally over a
point `z₀ ∉ A` with `p z₀ ∈ C`, regularity of `Y` separates the fibre coordinate of `z₀` in a chart
from the closed slice of `A` by a closed neighbourhood `F ⊆ Y`, and `p` projects the part of `A`
outside the complementary chart tube to a closed subset of `C` missing `p z₀`.

## Main results

* `Topology.RelCWComplex.closed_of_forall_exists_trivialization`: weak-topology characterization of
  closed subsets of `p ⁻¹' C` for a locally trivial map `p : Z → X` with compact regular fibre.
* `FiberBundle.closed_preimage_proj`: specialization to the projection of a fibre bundle with
  compact regular model fibre over a relative CW complex.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Appendix, Theorem A.6, for weak topologies of products with locally compact spaces.
* J. W. Milnor and J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton University Press, 1974, §9–§10 (cells of disc bundles over CW bases).
-/

public section

open Bundle Filter Metric Set Topology

namespace Topology.RelCWComplex

variable {X : Type*} [TopologicalSpace X] [T2Space X]
  {Y : Type*} [TopologicalSpace Y] [CompactSpace Y] [RegularSpace Y]
  {Z : Type*} [TopologicalSpace Z]

omit [T2Space X] [CompactSpace Y] [RegularSpace Y] in
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

private lemma isClosed_image_inter_of_isProperMap {p : Z → X} (hprop : IsProperMap p)
    (C : Set X) {D : Set X} [RelCWComplex C D] {A M : Set Z} (hA : A ⊆ p ⁻¹' C)
    (hcell : ∀ n (j : cell C n), IsClosed (A ∩ p ⁻¹' closedCell n j))
    (hD : IsClosed (A ∩ p ⁻¹' D)) (hM : IsClosed M) :
    IsClosed (p '' (A ∩ M)) := by
  have hK {K : Set X} (hK : IsClosed (A ∩ p ⁻¹' K)) : IsClosed (p '' (A ∩ M) ∩ K) := by
    rw [← image_inter_preimage, inter_right_comm]
    exact hprop.isClosedMap _ (hK.inter hM)
  refine (RelCWComplex.closed C _ ?_).2 ⟨fun n j ↦ hK (hcell n j), hK hD⟩
  rintro _ ⟨z, hz, rfl⟩
  exact hA hz.1

/-- **A locally trivial projection with compact regular fibre preserves the weak topology of a
relative CW complex.** Let `(C, D)` be a relative CW complex in a Hausdorff space `X`, and let
`p : Z → X` admit local trivializations with compact regular fibre `Y` around every point of `X`.
Then `A ⊆ p ⁻¹' C` is closed in `Z` if and only if `A ∩ p ⁻¹' closedCell n j` for every cell of
`C` and `A ∩ p ⁻¹' D` are closed in `Z`. -/
theorem closed_of_forall_exists_trivialization {p : Z → X}
    (ht : ∀ x, ∃ e : Trivialization Y p, x ∈ e.baseSet)
    (C : Set X) {D : Set X} [RelCWComplex C D] (A : Set Z) (hA : A ⊆ p ⁻¹' C) :
    IsClosed A ↔
      (∀ n (j : cell C n), IsClosed (A ∩ p ⁻¹' closedCell n j)) ∧ IsClosed (A ∩ p ⁻¹' D) := by
  have hprop : IsProperMap p := TauCeti.isProperMap_of_forall_exists_trivialization ht
  have hp : Continuous p := hprop.continuous
  refine ⟨fun h ↦ ⟨fun n j ↦ h.inter (isClosed_closedCell.preimage hp),
    h.inter ((isClosedBase C).preimage hp)⟩, fun ⟨hcell, hD⟩ ↦ ?_⟩
  have hproj {M : Set Z} (hM : IsClosed M) : IsClosed (p '' (A ∩ M)) :=
    isClosed_image_inter_of_isProperMap hprop C hA hcell hD hM
  -- Separate any point `z₀ ∉ A` from `A`: outside `p ⁻¹' C` use openness of `Cᶜ`; over `C` choose a
  -- closed fibre neighbourhood `F` missing the slice of `A` and project the remaining part of `A`.
  refine isOpen_compl_iff.1 (isOpen_iff_mem_nhds.2 fun z₀ hz₀ ↦ ?_)
  by_cases hx₀ : p z₀ ∈ C
  · obtain ⟨e, he⟩ := ht (p z₀)
    have hz₀_src : z₀ ∈ e.source := e.mem_source.2 he
    have hz₀_slice : (e z₀).2 ∉ {y : Y | e.toOpenPartialHomeomorph.symm (p z₀, y) ∈ A} := by
      intro hmem
      have hsymm : e.toOpenPartialHomeomorph.symm (p z₀, (e z₀).2) = z₀ := by
        rw [← e.coe_fst hz₀_src, Prod.mk.eta]
        exact e.left_inv hz₀_src
      exact hz₀ (hsymm ▸ hmem)
    obtain ⟨F, hF_nhds, hFc, hFA⟩ := exists_mem_nhds_isClosed_subset
      ((isClosed_slice_of_mem_complex C hcell hD hx₀ e he).isOpen_compl.mem_nhds hz₀_slice)
    let M : Set Z := (e.source ∩ (fun z ↦ (e z).2) ⁻¹' Fᶜ)ᶜ
    have hMc : IsClosed M := isClosed_compl_iff.2 <| isOpen_iff_mem_nhds.2 fun z ⟨hzs, hzF⟩ ↦
      inter_mem (e.open_source.mem_nhds hzs)
        ((continuous_snd.continuousAt.comp (e.continuousAt hzs)).preimage_mem_nhds
          (hFc.isOpen_compl.mem_nhds hzF))
    have hpz₀ : p z₀ ∉ p '' (A ∩ M) := by
      rintro ⟨z, ⟨hzA, hzM⟩, hzz₀⟩
      have hz_src : z ∈ e.source := e.mem_source.2 (hzz₀.symm ▸ he)
      have hzF : (e z).2 ∈ F := not_not.1 fun hzFc ↦ hzM ⟨hz_src, hzFc⟩
      have hsymm : e.toOpenPartialHomeomorph.symm (p z₀, (e z).2) = z := by
        rw [← hzz₀, ← e.coe_fst hz_src, Prod.mk.eta]
        exact e.left_inv hz_src
      exact hFA hzF (show e.toOpenPartialHomeomorph.symm (p z₀, (e z).2) ∈ A from
        hsymm.symm ▸ hzA)
    have hU₁ : p ⁻¹' (p '' (A ∩ M))ᶜ ∈ 𝓝 z₀ :=
      ((hproj hMc).isOpen_compl.preimage hp).mem_nhds hpz₀
    have hU₂ : (fun z ↦ (e z).2) ⁻¹' F ∈ 𝓝 z₀ :=
      (continuous_snd.continuousAt.comp (e.continuousAt hz₀_src)).preimage_mem_nhds hF_nhds
    filter_upwards [inter_mem hU₁ hU₂] with z ⟨hzB, hzF⟩ hzA
    exact hzB ⟨z, ⟨hzA, fun ⟨_, hzFc⟩ ↦ hzFc hzF⟩, rfl⟩
  · filter_upwards [(RelCWComplex.isClosed (C := C)).isOpen_compl.preimage hp |>.mem_nhds hx₀]
      with z hz hzA
    exact hz (hA hzA)

end Topology.RelCWComplex

/-- **The projection of a fibre bundle with compact regular model fibre preserves the weak topology
of a relative CW complex.** -/
theorem FiberBundle.closed_preimage_proj {B F : Type*} [TopologicalSpace B] [T2Space B]
    [TopologicalSpace F] [CompactSpace F] [RegularSpace F] (E : B → Type*)
    [TopologicalSpace (TotalSpace F E)] [∀ b, TopologicalSpace (E b)] [FiberBundle F E]
    (C : Set B) {D : Set B} [Topology.RelCWComplex C D]
    (A : Set (TotalSpace F E)) (hA : A ⊆ π F E ⁻¹' C) :
    IsClosed A ↔
      (∀ n (j : Topology.RelCWComplex.cell C n),
        IsClosed (A ∩ π F E ⁻¹' Topology.RelCWComplex.closedCell n j)) ∧
      IsClosed (A ∩ π F E ⁻¹' D) :=
  Topology.RelCWComplex.closed_of_forall_exists_trivialization
    (exists_trivialization_mem_baseSet F E) C A hA
