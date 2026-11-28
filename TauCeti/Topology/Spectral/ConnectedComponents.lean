/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Spectral.Prespectral
public import Mathlib.Topology.QuasiSeparated
public import Mathlib.Topology.Separation.Hausdorff
public import Mathlib.Topology.Spectral.Basic
public import TauCeti.Topology.ConnectedComponents
import Mathlib.Topology.Separation.Regular
import TauCeti.Topology.Spectral.PatchCriterion

/-!
# Connected components of spectral spaces

In a compact Hausdorff space the connected component of a point is the intersection of its clopen
neighbourhoods, and the space of connected components is Hausdorff, hence profinite (Mathlib's
`connectedComponent_eq_iInter_isClopen` and `ConnectedComponents.t2`). A spectral space is
compact but rarely Hausdorff; this file proves both statements for spectral spaces, and more
generally for compact quasi-separated spaces with a basis of compact open sets.

So for a spectral space `X`, `ConnectedComponents X` is profinite: compactness and total
disconnectedness are Mathlib's instances `Quotient.compactSpace` and
`ConnectedComponents.totallyDisconnectedSpace`, and the Hausdorff property is the instance below.
Its clopen subsets are those of `X`, by `ConnectedComponents.clopensEquiv`. This is the
profiniteness of the component space used for spectral spaces in the theory of perfectoid
spaces and diamonds, see the proof of [Sch17, Lemma 7.2].

The proofs follow Mathlib's proofs of `connectedComponent_eq_iInter_isClopen` and
`ConnectedComponents.t2`, with the normality of a compact Hausdorff space replaced by separation by
compact open sets: two disjoint closed subsets `a`, `b` of a compact space with a basis of compact
opens have compact open neighbourhoods `u ⊇ a` missing `b` and `v ⊇ b` missing `a`, and
quasi-separatedness makes `u ∩ v` compact. Quasi-separatedness cannot be dropped: doubling the limit
point `0` of `{0} ∪ {1 / n | n ≥ 1}` gives a compact space with a basis of compact opens, in which
the two copies of `0` are separate components but lie in the same clopen sets.

## Main results

* `PrespectralSpace.connectedComponent_eq_iInter_isClopen`: in a compact quasi-separated space with
  a basis of compact open sets, the connected component of a point is the intersection of its
  clopen neighbourhoods.
* `ConnectedComponents.t2Space_of_prespectralSpace`: the space of connected components of such a
  space, for instance of a spectral space, is Hausdorff.
* `TauCeti.spectralSpace_connectedComponents`, `ConnectedComponents.isSpectralMap_coe`: when `X` is
  compact and `ConnectedComponents X` is Hausdorff (in particular, when `X` is spectral or compact
  Hausdorff), `ConnectedComponents X` is spectral and the quotient projection
  `ConnectedComponents.mk : X → ConnectedComponents X` is a spectral map.

## References

* [Sch17] P. Scholze, *Étale cohomology of diamonds*, arXiv:1709.07343, §7.
-/

public section

open Set Topology

variable {X : Type*} [TopologicalSpace X]

namespace PrespectralSpace

variable [CompactSpace X] [QuasiSeparatedSpace X] [PrespectralSpace X]

/-- In a compact quasi-separated space with a basis of compact open sets (for instance a spectral
space), the connected component of a point is the intersection of all clopen sets containing it:
connected components and quasi-components agree. -/
theorem connectedComponent_eq_iInter_isClopen (x : X) :
    connectedComponent x = ⋂ s : { s : Set X // IsClopen s ∧ x ∈ s }, s := by
  apply Subset.antisymm connectedComponent_subset_iInter_isClopen
  -- It suffices to show that the intersection `T` of the clopen neighbourhoods is preconnected.
  set T := ⋂ s : { s : Set X // IsClopen s ∧ x ∈ s }, (s : Set X)
  have hxT : x ∈ T := mem_iInter.2 fun s => s.property.2
  refine IsPreconnected.subset_connectedComponent ?_ hxT
  rw [isPreconnected_iff_subset_of_fully_disjoint_closed (isClosed_iInter fun s => s.property.1.1)]
  intro a b ha hb hab hdisj
  -- Separate `a` and `b` by compact open sets `u ⊇ a` and `v ⊇ b`, with `u` missing `b` and `v`
  -- missing `a`.
  obtain ⟨u, hu, huo, hau, hub⟩ := exists_isCompact_and_isOpen_between ha.isCompact
    hb.isOpen_compl (subset_compl_iff_disjoint_right.2 hdisj)
  obtain ⟨v, hv, hvo, hbv, hva⟩ := exists_isCompact_and_isOpen_between hb.isCompact
    ha.isOpen_compl (subset_compl_iff_disjoint_right.2 hdisj.symm)
  -- The compact set `(u ∪ v)ᶜ ∪ (u ∩ v)` misses `T`, so a single clopen neighbourhood `s` of `x`
  -- misses it, which means `s ⊆ u ∪ v` and `s ∩ u ∩ v = ∅`.
  have hK : IsCompact ((u ∪ v)ᶜ ∪ (u ∩ v)) :=
    (huo.union hvo).isClosed_compl.isCompact.union (hu.inter_of_isOpen hv huo hvo)
  have hKT : Disjoint ((u ∪ v)ᶜ ∪ (u ∩ v)) T := by
    refine disjoint_right.2 fun y hyT hyK => ?_
    rcases hab hyT with hya | hyb
    · exact hyK.elim (fun h => h (Or.inl (hau hya))) fun h => hva h.2 hya
    · exact hyK.elim (fun h => h (Or.inr (hbv hyb))) fun h => hub h.1 hyb
  obtain ⟨F, hF⟩ := hK.elim_finite_subfamily_closed
    (fun s : { s : Set X // IsClopen s ∧ x ∈ s } => (s : Set X)) (fun s => s.property.1.1) hKT
  set s := ⋂ i ∈ F, (i : Set X)
  have hs : IsClopen s := isClopen_biInter_finset fun i _ => i.property.1
  have hsK : ∀ y ∈ s, y ∈ u ∪ v ∧ y ∉ u ∩ v := fun y hy => by
    simpa [not_or, or_iff_not_imp_left] using disjoint_right.1 hF hy
  have hxs : x ∈ s := mem_iInter₂.2 fun i _ => i.property.2
  -- `T` lies in the clopen neighbourhood `s ∩ u` or `s ∩ v` of `x`, hence in `a` or in `b`.
  have hTs : ∀ w w' : Set X, IsOpen w → IsOpen w' → s ⊆ w ∪ w' → s ∩ w ∩ w' = ∅ → x ∈ w →
      T ⊆ w := fun w w' hw hw' hcover hempty hxw =>
    (iInter_subset (fun s : { s : Set X // IsClopen s ∧ x ∈ s } => (s : Set X))
      ⟨s ∩ w, isClopen_inter_of_disjoint_cover_clopen' hs hcover hw hw' hempty, hxs, hxw⟩).trans
      inter_subset_right
  have hcover : s ⊆ u ∪ v := fun y hy => (hsK y hy).1
  have hempty : s ∩ u ∩ v = ∅ :=
    eq_empty_of_forall_notMem fun y hy => (hsK y hy.1.1).2 ⟨hy.1.2, hy.2⟩
  rcases (hsK x hxs).1 with hxu | hxv
  · exact .inl fun y hyT => (hab hyT).resolve_right
      (hub <| hTs u v huo hvo hcover hempty hxu hyT)
  · exact .inr fun y hyT => (hab hyT).resolve_left (hva <| hTs v u hvo huo
      (union_comm u v ▸ hcover) (by rwa [inter_right_comm]) hxv hyT)

end PrespectralSpace

namespace ConnectedComponents

/-- The space of connected components of a compact quasi-separated space with a basis of compact
open sets, for instance of a spectral space, is Hausdorff. Being also compact and totally
disconnected, it is profinite. -/
instance t2Space_of_prespectralSpace [CompactSpace X] [QuasiSeparatedSpace X]
    [PrespectralSpace X] : T2Space (ConnectedComponents X) := by
  refine ⟨surjective_coe.forall₂.2 fun a b ne => ?_⟩
  rw [coe_ne_coe] at ne
  have h := connectedComponent_disjoint ne
  rw [PrespectralSpace.connectedComponent_eq_iInter_isClopen b] at h
  -- Finitely many clopen neighbourhoods of `b` already miss the compact component of `a`; their
  -- intersection `U` is a clopen union of components, so its image is clopen.
  obtain ⟨F, hF⟩ := isClosed_connectedComponent.isCompact.elim_finite_subfamily_closed
    _ (fun s : { s : Set X // IsClopen s ∧ b ∈ s } => s.property.1.1) h
  set U : Set X := ⋂ i ∈ F, (i : Set X)
  have hU : IsClopen U := isClopen_biInter_finset fun i _ => i.property.1
  have hV : IsClopen (mk '' U : Set (ConnectedComponents X)) := by
    simpa using (clopensEquiv.symm ⟨U, hU⟩).isClopen
  refine ⟨(mk '' U)ᶜ, mk '' U, hV.compl.isOpen, hV.isOpen, ?_,
    mem_image_of_mem _ (mem_iInter₂.2 fun i _ => i.property.2), disjoint_compl_left⟩
  rintro ⟨c, hc, hca⟩
  rw [coe_eq_coe] at hca
  have hcU : c ∈ connectedComponent a ∩ U := ⟨hca ▸ mem_connectedComponent, hc⟩
  rw [hF.inter_eq] at hcU
  exact hcU

end ConnectedComponents

namespace TauCeti

universe u

/-- When `X` is compact and `ConnectedComponents X` is Hausdorff (for instance, when `X` is
spectral or compact Hausdorff), `ConnectedComponents X` is spectral. -/
instance spectralSpace_connectedComponents (X : Type u) [TopologicalSpace X]
    [CompactSpace X] [T2Space (ConnectedComponents X)] :
    SpectralSpace (ConnectedComponents X) :=
  spectralSpace_of_zeroDimensionalSpace (ConnectedComponents X)

/-- When `X` is compact and `ConnectedComponents X` is Hausdorff (for instance, when `X` is
spectral), the quotient projection `X → ConnectedComponents X` is a spectral map. -/
theorem _root_.ConnectedComponents.isSpectralMap_coe {X : Type u} [TopologicalSpace X]
    [CompactSpace X] [T2Space (ConnectedComponents X)] :
    IsSpectralMap (ConnectedComponents.mk : X → ConnectedComponents X) :=
  ConnectedComponents.continuous_coe.isProperMap.isSpectralMap

end TauCeti
