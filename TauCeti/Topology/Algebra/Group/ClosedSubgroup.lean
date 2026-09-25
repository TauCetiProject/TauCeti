/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.Order.Zorn
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Topology.Algebra.Group.ClosedSubgroup
public import Mathlib.Topology.Compactness.Compact

/-!
# Closed subgroups of topological groups

This file collects constructions on closed subgroups of a topological group.

An isomorphism of topological groups carries closed subgroups to closed subgroups.  This is
packaged as an order isomorphism, together with its compatibility with normality and quotients:
a normal closed subgroup can be transported without changing the topological quotient it defines.

A closed subgroup `H` of `A × G` projecting onto `G`, that is with `∀ g, ∃ a, (a, g) ∈ H`, is a
closed relation from `G` to `A` defined everywhere. When `A` is compact, the fibre
`{a | (a, g) ∈ H}` over each `g` is compact, so along a chain of such subgroups the fibres of the
intersection are nonempty, and Zorn's lemma supplies a minimal such subgroup below any given one.

## Main definitions

* `ContinuousMulEquiv.closedSubgroupOrderIso`: transport of closed subgroups along an isomorphism
  of topological groups.
* `ContinuousMulEquiv.quotient`: the induced isomorphism of topological quotient groups.

## Main results

* `Subgroup.forall_exists_mem_sInf_of_isChain`: the intersection of a chain of closed subgroups
  of `A × G` projecting onto `G` still projects onto `G`.
* `Subgroup.exists_minimal_isClosed_le`: a closed subgroup of `A × G` projecting onto `G` contains
  a minimal closed subgroup projecting onto `G`.
-/

public section

namespace TauCeti

section Transport

universe u v

variable {G : Type u} {H : Type v} [Group G] [Group H]
  [TopologicalSpace G] [TopologicalSpace H]

/-- A topological group isomorphism transports closed subgroups, preserving inclusion. -/
def _root_.ContinuousMulEquiv.closedSubgroupOrderIso (e : G ≃ₜ* H) :
    ClosedSubgroup G ≃o ClosedSubgroup H where
  toFun K :=
    { toSubgroup := e.toMulEquiv.mapSubgroup K.toSubgroup
      isClosed' := by
        -- The carrier of `Subgroup.map` is stored as an existential rather than an image.
        change IsClosed (e '' (K : Set G))
        exact e.toHomeomorph.isClosed_image.mpr K.isClosed' }
  invFun L :=
    { toSubgroup := e.toMulEquiv.mapSubgroup.symm L.toSubgroup
      isClosed' := by
        -- The carrier of `Subgroup.map` is stored as an existential rather than an image.
        change IsClosed (e.symm '' (L : Set H))
        exact e.symm.toHomeomorph.isClosed_image.mpr L.isClosed' }
  left_inv K :=
    ClosedSubgroup.toSubgroup_injective (e.toMulEquiv.mapSubgroup.left_inv K.toSubgroup)
  right_inv L :=
    ClosedSubgroup.toSubgroup_injective (e.toMulEquiv.mapSubgroup.right_inv L.toSubgroup)
  map_rel_iff' := e.toMulEquiv.mapSubgroup.map_rel_iff

/-- The underlying subgroup transported by `ContinuousMulEquiv.closedSubgroupOrderIso` is the
image of the original subgroup. -/
@[simp]
theorem _root_.ContinuousMulEquiv.closedSubgroupOrderIso_apply_toSubgroup
    (e : G ≃ₜ* H) (K : ClosedSubgroup G) :
    (e.closedSubgroupOrderIso K).toSubgroup =
      K.toSubgroup.map e.toMulEquiv.toMonoidHom :=
  (rfl)

/-- The inverse transport of a closed subgroup is its image under the inverse topological group
isomorphism. -/
@[simp]
theorem _root_.ContinuousMulEquiv.closedSubgroupOrderIso_symm_apply_toSubgroup
    (e : G ≃ₜ* H) (L : ClosedSubgroup H) :
    (e.closedSubgroupOrderIso.symm L).toSubgroup =
      L.toSubgroup.map e.symm.toMulEquiv.toMonoidHom :=
  (rfl)

/-- Normality is preserved when a closed subgroup is transported along a topological group
isomorphism. -/
instance _root_.ContinuousMulEquiv.instNormalClosedSubgroupOrderIso
    (e : G ≃ₜ* H) (K : ClosedSubgroup G) [K.toSubgroup.Normal] :
    (e.closedSubgroupOrderIso K).toSubgroup.Normal :=
  Subgroup.Normal.map inferInstance e.toMulEquiv.toMonoidHom e.surjective

/-- A topological group isomorphism induces an isomorphism between the quotients by corresponding
normal closed subgroups. -/
def _root_.ContinuousMulEquiv.quotient (e : G ≃ₜ* H) (N : ClosedSubgroup G)
    [N.toSubgroup.Normal] :
    G ⧸ N.toSubgroup ≃ₜ* H ⧸ (e.closedSubgroupOrderIso N).toSubgroup :=
  ContinuousMulEquiv.mk
    (QuotientGroup.congr N.toSubgroup (e.closedSubgroupOrderIso N).toSubgroup e.toMulEquiv rfl)
    ((QuotientGroup.isQuotientMap_mk N.toSubgroup).continuous_iff.mpr <| by
      exact (QuotientGroup.continuous_mk.comp e.continuous).congr fun g ↦
        (QuotientGroup.congr_mk N.toSubgroup (e.closedSubgroupOrderIso N).toSubgroup
          e.toMulEquiv rfl g).symm)
    ((QuotientGroup.isQuotientMap_mk
      (e.closedSubgroupOrderIso N).toSubgroup).continuous_iff.mpr <| by
        exact (QuotientGroup.continuous_mk.comp e.symm.continuous).congr fun h ↦
          (QuotientGroup.congr_mk (e.closedSubgroupOrderIso N).toSubgroup N.toSubgroup
            e.toMulEquiv.symm ((Subgroup.map_symm_eq_iff_map_eq _).mpr rfl) h).symm)

/-- The quotient isomorphism sends the class of an element to the class of its image. -/
@[simp]
theorem _root_.ContinuousMulEquiv.quotient_mk (e : G ≃ₜ* H) (N : ClosedSubgroup G)
    [N.toSubgroup.Normal] (g : G) :
    e.quotient N (g : G ⧸ N.toSubgroup) =
      (e g : H ⧸ (e.closedSubgroupOrderIso N).toSubgroup) :=
  (rfl)

/-- The inverse quotient isomorphism sends the class of an element to the class of its inverse
image. -/
@[simp]
theorem _root_.ContinuousMulEquiv.quotient_symm_mk (e : G ≃ₜ* H) (N : ClosedSubgroup G)
    [N.toSubgroup.Normal] (h : H) :
    (e.quotient N).symm (h : H ⧸ (e.closedSubgroupOrderIso N).toSubgroup) =
      (e.symm h : G ⧸ N.toSubgroup) :=
  (rfl)

end Transport

section CompactFactor

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


end CompactFactor

end TauCeti
