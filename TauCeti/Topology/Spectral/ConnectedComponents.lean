/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Connected.Clopen
public import Mathlib.Topology.Spectral.Basic
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.Separation.Regular
import TauCeti.Topology.ConnectedComponents
import TauCeti.Topology.Spectral.PatchCriterion
import TauCeti.Topology.Spectral.ProConstructible

/-!
# Connected components of spectral spaces

Mathlib shows (`ConnectedComponents.t2`) that the connected-components quotient of a compact
Hausdorff space is Hausdorff, hence profinite. A spectral space need not be Hausdorff, so that
instance does not apply to valuation spectra or adic spaces; yet its space of connected components
`ConnectedComponents X` is still profinite, every connected component is still the intersection of
all clopen neighbourhoods containing it, and the quotient projection `X → ConnectedComponents X` is
a spectral map. None of the component results require `T0Space X`, so they hold more generally on
any compact, quasi-sober, quasi-separated prespectral space.

The key replacement for Hausdorff normality is
`TauCeti.exists_disjoint_isOpen_of_isCompact_of_stableUnderGeneralization`:
in a quasi-sober, quasi-separated prespectral space, a compact subset and a disjoint closed subset
that is stable under generalization are separated by disjoint open subsets, because a quasi-compact
open neighbourhood between them is pro-constructible on compact open pieces and its closure consists
solely of specializations (`TauCeti.IsProConstructible.closure_eq_setOfPred_specializes`). Adapting
the clopen-intersection argument of Mathlib's `connectedComponent_eq_iInter_isClopen` with this
separation input yields the clopen-intersection formula, from which total separation, Hausdorffness,
and spectrality of `ConnectedComponents X` follow via `TauCeti.connectedComponentsClopensOrderIso`.

## Main results

* `TauCeti.connectedComponent_eq_iInter_isClopen_of_prespectralSpace`: in a compact, quasi-sober,
  quasi-separated prespectral space, the connected component of `x` is the intersection of the
  clopen subsets containing `x`.
* `TauCeti.totallySeparatedSpace_connectedComponents`, `TauCeti.t2Space_connectedComponents`:
  `ConnectedComponents X` is totally separated and Hausdorff when `X` is compact, quasi-sober,
  quasi-separated, and prespectral (in particular, when `X` is spectral), hence profinite.
* `TauCeti.spectralSpace_connectedComponents`: `ConnectedComponents X` is spectral under the same
  hypotheses.
* `ConnectedComponents.isSpectralMap_coe`: when `X` is compact and `ConnectedComponents X` is
  Hausdorff (in particular, when `X` is spectral),
  `ConnectedComponents.mk : X → ConnectedComponents X` is a spectral map.

## References

* The Stacks Project, Tag 0906.
* P. Scholze, *Étale cohomology of diamonds*, arXiv:1709.07343, §7, proof of Lemmas 7.2 and 7.3.
* B. Bhatt and P. Scholze, *The pro-étale topology for schemes*, Astérisque 369 (2015), §2.1.
-/

public section

namespace TauCeti

open Set Topology TopologicalSpace

universe u

section Prespectral

variable {X : Type u} [TopologicalSpace X] [CompactSpace X] [QuasiSober X] [PrespectralSpace X]
  [QuasiSeparatedSpace X]

/-- In a compact, quasi-sober, quasi-separated prespectral space (in particular, in any spectral
space), the connected component of `x` is the intersection of all clopen subsets containing `x`. -/
theorem connectedComponent_eq_iInter_isClopen_of_prespectralSpace (x : X) :
    connectedComponent x = ⋂ s : {s : Set X // IsClopen s ∧ x ∈ s}, s.1 := by
  refine Subset.antisymm connectedComponent_subset_iInter_isClopen ?_
  let N := {s : Set X // IsClopen s ∧ x ∈ s}
  let Q : Set X := ⋂ s : N, s.1
  have hxQ : x ∈ Q := mem_iInter.2 fun s ↦ s.2.2
  suffices hQ : IsPreconnected Q from hQ.subset_connectedComponent hxQ
  have hQc : IsClosed Q := isClosed_iInter fun s ↦ s.2.1.isClosed
  have hQg : StableUnderGeneralization Q :=
    stableUnderGeneralization_iInter _ fun s ↦ s.2.1.isOpen.stableUnderGeneralization
  refine isPreconnected_closed_iff.2 fun a b ha hb hcov ⟨y₁, hy₁⟩ ⟨y₂, hy₂⟩ ↦ ?_
  by_contra hne
  have hab : Disjoint (Q ∩ a) (Q ∩ b) := disjoint_iff_inter_eq_empty.2 <| by
    rw [not_nonempty_iff_eq_empty] at hne
    grind
  -- `Q ∩ b` inherits stability under generalization because `Q ∩ a` is closed (hence stable under
  -- specialization) and `Q = (Q ∩ a) ∪ (Q ∩ b)`.
  have hbg : StableUnderGeneralization (Q ∩ b) := by
    intro y z hzy hyb
    have hzQ : z ∈ Q := hQg hzy hyb.1
    rcases hcov hzQ with hza | hzb
    · exact (hab.le_bot ⟨(hQc.inter ha).stableUnderSpecialization hzy ⟨hzQ, hza⟩, hyb⟩).elim
    · exact ⟨hzQ, hzb⟩
  obtain ⟨U, V, hUo, hVo, haU, hbV, hUV⟩ :=
    exists_disjoint_isOpen_of_isCompact_of_stableUnderGeneralization
      (hQc.inter ha).isCompact (hQc.inter hb) hbg hab
  have hQUV : Disjoint (U ∪ V)ᶜ Q := disjoint_compl_left_iff_subset.2 fun z hz ↦
    (hcov hz).elim (fun hza ↦ Or.inl (haU ⟨hz, hza⟩)) (fun hzb ↦ Or.inr (hbV ⟨hz, hzb⟩))
  obtain ⟨t, ht⟩ := (hUo.union hVo).isClosed_compl.isCompact.elim_finite_subfamily_closed
    (fun s : N ↦ s.1) (fun s ↦ s.2.1.isClosed) hQUV
  let S : Set X := ⋂ s ∈ t, (s : Set X)
  have hS : IsClopen S := isClopen_biInter_finset fun s _ ↦ s.2.1
  have hxS : x ∈ S := mem_iInter₂.2 fun s _ ↦ s.2.2
  have hSUV : S ⊆ U ∪ V := disjoint_compl_left_iff_subset.1 ht
  rcases hSUV hxS with hxU | hxV
  · have hQSU : Q ⊆ S ∩ U := iInter_subset (fun s : N ↦ s.1)
      ⟨S ∩ U, isClopen_inter_of_disjoint_cover_clopen hS hSUV hUo hVo hUV, hxS, hxU⟩
    exact hUV.le_bot ⟨(hQSU hy₂.1).2, hbV hy₂⟩
  · have hQSV : Q ⊆ S ∩ V := iInter_subset (fun s : N ↦ s.1)
      ⟨S ∩ V, isClopen_inter_of_disjoint_cover_clopen hS (union_comm U V ▸ hSUV) hVo hUo hUV.symm,
        hxS, hxV⟩
    exact hUV.le_bot ⟨haU hy₁, (hQSV hy₁.1).2⟩

variable (X)

/-- The space of connected components of a compact, quasi-sober, quasi-separated prespectral space
(in particular, of any spectral space) is totally separated: distinct components are separated by a
clopen subset of `ConnectedComponents X`. -/
instance totallySeparatedSpace_connectedComponents :
    TotallySeparatedSpace (ConnectedComponents X) := by
  refine totallySeparatedSpace_iff_exists_isClopen.2 ?_
  refine ConnectedComponents.surjective_coe.forall₂.2 fun x y hxy ↦ ?_
  have hy : y ∉ connectedComponent x := fun hy ↦
    hxy (ConnectedComponents.coe_eq_coe.2 (connectedComponent_eq hy))
  rw [connectedComponent_eq_iInter_isClopen_of_prespectralSpace] at hy
  obtain ⟨⟨S, hS, hxS⟩, hyS⟩ := not_forall.1 (mt mem_iInter.2 hy)
  let W := (connectedComponentsClopensOrderIso X).symm ⟨S, hS⟩
  exact ⟨W, W.isClopen, (mem_connectedComponentsClopensOrderIso_symm (V := ⟨S, hS⟩)).2 hxS,
    fun hy' ↦ hyS ((mem_connectedComponentsClopensOrderIso_symm (V := ⟨S, hS⟩)).1 hy')⟩

/-- The space of connected components of a compact, quasi-sober, quasi-separated prespectral space
(in particular, of any spectral space) is Hausdorff, hence profinite with Mathlib's
`Quotient.compactSpace` and `ConnectedComponents.totallyDisconnectedSpace`. -/
instance t2Space_connectedComponents : T2Space (ConnectedComponents X) :=
  inferInstance

/-- The space of connected components of a compact, quasi-sober, quasi-separated prespectral space
(in particular, of any spectral space) is spectral. -/
instance spectralSpace_connectedComponents : SpectralSpace (ConnectedComponents X) :=
  spectralSpace_of_zeroDimensionalSpace (ConnectedComponents X)

end Prespectral

/-- When `X` is compact and `ConnectedComponents X` is Hausdorff (for instance, when `X` is
spectral), the quotient projection `X → ConnectedComponents X` is a spectral map. -/
theorem _root_.ConnectedComponents.isSpectralMap_coe {X : Type u} [TopologicalSpace X]
    [CompactSpace X] [T2Space (ConnectedComponents X)] :
    IsSpectralMap (ConnectedComponents.mk : X → ConnectedComponents X) :=
  ConnectedComponents.continuous_coe.isProperMap.isSpectralMap

end TauCeti
