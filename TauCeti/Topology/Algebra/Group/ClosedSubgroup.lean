/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.Zorn
public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Topology.Compactness.Compact

/-!
# Closed subgroups of a product with a compact factor

A closed subgroup `H` of `A × G` projecting onto `G`, that is with `∀ g, ∃ a, (a, g) ∈ H`, is a
closed relation from `G` to `A` defined everywhere. When `A` is compact, the fibre
`{a | (a, g) ∈ H}` over each `g` is compact, so along a chain of such subgroups the fibres of the
intersection are nonempty, and Zorn's lemma supplies a minimal such subgroup below any given one.

## Main results

* `Subgroup.forall_exists_mem_sInf_of_isChain`: the intersection of a chain of closed subgroups
  of `A × G` projecting onto `G` still projects onto `G`.
* `Subgroup.exists_minimal_isClosed_le`: a closed subgroup of `A × G` projecting onto `G` contains
  a minimal closed subgroup projecting onto `G`.
-/

public section

namespace TauCeti

variable {A : Type*} [Group A] [TopologicalSpace A] [CompactSpace A]
variable {G : Type*} [Group G] [TopologicalSpace G]

/-- The intersection of a nonempty chain of closed subgroups of `A × G`, each projecting onto `G`,
projects onto `G` when `A` is compact: the fibre over `g` is a directed intersection of nonempty
compact sets. -/
theorem _root_.Subgroup.forall_exists_mem_sInf_of_isChain {c : Set (Subgroup (A × G))}
    (hne : c.Nonempty) (hchain : IsChain (· ≤ ·) c) (hclosed : ∀ K ∈ c, IsClosed (K : Set (A × G)))
    (hsurj : ∀ K ∈ c, ∀ g : G, ∃ a : A, (a, g) ∈ K) (g : G) : ∃ a : A, (a, g) ∈ sInf c := by
  let F : c → Set A := fun K ↦ {a | (a, g) ∈ K.1}
  have : Nonempty c := hne.to_subtype
  have hFclosed (K : c) : IsClosed (F K) :=
    (hclosed K K.2).preimage (continuous_id.prodMk continuous_const)
  have hdir : Directed (· ⊇ ·) F := by
    intro K L
    rcases hchain.total K.2 L.2 with hKL | hLK
    · exact ⟨K, Set.Subset.rfl, fun _ ha ↦ hKL ha⟩
    · exact ⟨L, fun _ ha ↦ hLK ha, Set.Subset.rfl⟩
  obtain ⟨a, ha⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed F hdir
    (fun K ↦ hsurj K K.2 g) (fun K ↦ (hFclosed K).isCompact) hFclosed
  exact ⟨a, Subgroup.mem_sInf.mpr fun K hK ↦ Set.mem_iInter.mp ha ⟨K, hK⟩⟩

/-- A closed subgroup of `A × G` projecting onto `G`, with `A` compact, contains a minimal closed
subgroup projecting onto `G`. -/
theorem _root_.Subgroup.exists_minimal_isClosed_le (R : Subgroup (A × G))
    (hclosed : IsClosed (R : Set (A × G))) (hsurj : ∀ g : G, ∃ a : A, (a, g) ∈ R) :
    ∃ H : Subgroup (A × G), Minimal (fun H : Subgroup (A × G) ↦
      H ≤ R ∧ IsClosed (H : Set (A × G)) ∧ ∀ g : G, ∃ a : A, (a, g) ∈ H) H := by
  refine zorn_ge₀ _ fun c hcs hchain ↦ ?_
  rcases c.eq_empty_or_nonempty with rfl | hne
  · exact ⟨R, ⟨le_rfl, hclosed, hsurj⟩, by simp⟩
  obtain ⟨K, hK⟩ := hne
  refine ⟨sInf c, ⟨(sInf_le hK).trans (hcs hK).1, ?_, ?_⟩, fun K hK ↦ sInf_le hK⟩
  · rw [Subgroup.coe_sInf]
    exact isClosed_biInter fun K hK ↦ (hcs hK).2.1
  · exact Subgroup.forall_exists_mem_sInf_of_isChain ⟨K, hK⟩ hchain.symm
      (fun K hK ↦ (hcs hK).2.1) fun K hK ↦ (hcs hK).2.2

end TauCeti
