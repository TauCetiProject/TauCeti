/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Constructions

/-!
# Inducing maps glued along a closed cover of the target

A continuous map `f : X → Y` is inducing as soon as it is inducing over each of two closed sets
`s`, `t` of `Y` covering its range, that is, as soon as `f` restricted to `f ⁻¹' s` and to
`f ⁻¹' t` is inducing. This is the closed-cover counterpart of
`TopologicalSpace.IsOpenCover.isInducing_iff_restrictPreimage`, and the analogue for inducing
maps of the pasting lemma `ContinuousOn.union_of_isClosed`. It is how a map defined piecewise on
two closed pieces of its source, with the pieces landing in two closed pieces of the target, is
seen to be an embedding without any compactness.
-/

public section

open Set

namespace Topology

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {f : X → Y} {s t : Set Y}

/-- A continuous map is inducing if it is inducing over each of two closed sets covering its
range. -/
theorem IsInducing.of_isClosed_cover (hf : Continuous f) (hs : IsClosed s) (ht : IsClosed t)
    (hst : range f ⊆ s ∪ t) (hfs : IsInducing (f ∘ ((↑) : f ⁻¹' s → X)))
    (hft : IsInducing (f ∘ ((↑) : f ⁻¹' t → X))) : IsInducing f := by
  -- Every closed set `c` of `X` is the preimage of a closed set of `Y`: over each piece, `c` is
  -- cut out by a closed set of `Y`, and the two closed sets glue.
  have key : ∀ c : Set X, IsClosed c → ∃ T : Set Y, IsClosed T ∧ f ⁻¹' T = c := fun c hc => by
    obtain ⟨c₁, hc₁, hc₁c⟩ := hfs.isClosed_iff.1 (hc.preimage continuous_subtype_val)
    obtain ⟨c₂, hc₂, hc₂c⟩ := hft.isClosed_iff.1 (hc.preimage continuous_subtype_val)
    refine ⟨c₁ ∩ s ∪ c₂ ∩ t, (hc₁.inter hs).union (hc₂.inter ht), ?_⟩
    ext x
    have h₁ : ∀ hx : f x ∈ s, f x ∈ c₁ ↔ x ∈ c := fun hx =>
      Set.ext_iff.1 hc₁c (⟨x, hx⟩ : f ⁻¹' s)
    have h₂ : ∀ hx : f x ∈ t, f x ∈ c₂ ↔ x ∈ c := fun hx =>
      Set.ext_iff.1 hc₂c (⟨x, hx⟩ : f ⁻¹' t)
    simp only [mem_preimage, mem_union, mem_inter_iff]
    refine ⟨fun h => h.elim (fun h => (h₁ h.2).1 h.1) fun h => (h₂ h.2).1 h.1, fun h => ?_⟩
    rcases hst (mem_range_self x) with hx | hx
    · exact .inl ⟨(h₁ hx).2 h, hx⟩
    · exact .inr ⟨(h₂ hx).2 h, hx⟩
  refine ⟨le_antisymm (continuous_iff_le_induced.1 hf) (TopologicalSpace.le_def.2 fun U hU => ?_)⟩
  obtain ⟨T, hT, hTU⟩ := key Uᶜ (isClosed_compl_iff.2 hU)
  exact isOpen_induced_iff.2 ⟨Tᶜ, hT.isOpen_compl, by rw [preimage_compl, hTU, compl_compl]⟩

/-- A continuous injective map is an embedding if it is inducing over each of two closed sets
covering its range. -/
theorem IsEmbedding.of_isClosed_cover (hf : Continuous f) (hinj : Function.Injective f)
    (hs : IsClosed s) (ht : IsClosed t) (hst : range f ⊆ s ∪ t)
    (hfs : IsInducing (f ∘ ((↑) : f ⁻¹' s → X))) (hft : IsInducing (f ∘ ((↑) : f ⁻¹' t → X))) :
    IsEmbedding f :=
  ⟨.of_isClosed_cover hf hs ht hst hfs hft, hinj⟩

end Topology
