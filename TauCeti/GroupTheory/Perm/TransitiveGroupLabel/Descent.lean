/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.GroupAction.Primitive
public import Mathlib.GroupTheory.Perm.Basic
import TauCeti.Algebra.Group.Subgroup.Conjugates
import TauCeti.GroupTheory.Perm.PermCongr

/-!
# Completeness of a list of transitive groups by descent

To show that a list `𝓡` of transitive subgroups of `Equiv.Perm α` represents every transitive
subgroup up to conjugacy, it suffices to look at maximal subgroups. If `⊤ ∈ 𝓡` and, for every
member `R` of `𝓡`, every maximal subgroup of `R` acting transitively on `α` is conjugate to a
member of `𝓡`, then every transitive subgroup is conjugate to a member of `𝓡`
(`TauCeti.exists_map_conj_mem_of_isPretransitive`). Indeed a transitive subgroup lies in a
conjugate of `⊤`; if it is properly contained in a conjugate of a member `R`, it lies in a
maximal subgroup of that conjugate, which is still transitive and is conjugate to a member of
smaller order. This is `Subgroup.exists_map_conj_mem_of_forall_covBy` for the property of being
transitive.

For instance, in degree three `𝓡 = {S₃, A₃}` satisfies the hypothesis, since the maximal
subgroups of order two of `S₃` fix a point and the trivial maximal subgroup of `A₃` is not
transitive. In degree four `{S₄, A₄, D₄, C₄}` does not: the normal Klein four-group is a
transitive maximal subgroup of `A₄` and of `D₄` conjugate to no member.

The other half of a classification, that distinct members of `𝓡` are not conjugate, is checked
on invariants of conjugacy classes of subgroups of `Equiv.Perm α`. Since conjugation by `τ` is
`τ.permCongrHom` (`Equiv.conj_eq_permCongrHom`), the order (`Subgroup.card_map_of_injective`),
parity (`Equiv.map_permCongrHom_le_alternatingGroup_iff`) and primitivity
(`Equiv.isPreprimitive_map_permCongrHom_iff`) are invariants. So is the number of elements of each
cycle type, since conjugate subgroups are almost conjugate (`Subgroup.almostConjugate_conj_smul`)
and almost-conjugacy in `Equiv.Perm α` is equality of these numbers
(`Subgroup.almostConjugate_iff_forall_natCard_cycleType_eq`).

## Main results

* `TauCeti.exists_map_conj_mem_of_isPretransitive`: completeness by descent through transitive
  maximal subgroups.

## References

* J. H. Conway, A. Hulpke and J. McKay, *On transitive permutation groups*, LMS J. Comput. Math.
  1 (1998), 1–8.
-/

public section

open Equiv MulAction

namespace TauCeti

variable {α : Type*} [Finite α]

/-- **Completeness by descent through transitive maximal subgroups.** Let `𝓡` be a family of
subgroups of `Equiv.Perm α` containing `⊤`, such that for every member `R` of `𝓡`, every maximal
subgroup of `R` acting transitively on `α` is conjugate to a member of `𝓡`. Then every transitive
subgroup of `Equiv.Perm α` is conjugate to a member of `𝓡`. -/
theorem exists_map_conj_mem_of_isPretransitive {𝓡 : Set (Subgroup (Perm α))} (htop : ⊤ ∈ 𝓡)
    (h𝓡 : ∀ R ∈ 𝓡, ∀ M : Subgroup (Perm α), M ⋖ R → IsPretransitive M α →
      ∃ τ : Perm α, M.map (MulAut.conj τ).toMonoidHom ∈ 𝓡)
    {G : Subgroup (Perm α)} (hG : IsPretransitive G α) :
    ∃ τ : Perm α, G.map (MulAut.conj τ).toMonoidHom ∈ 𝓡 := by
  refine Subgroup.exists_map_conj_mem_of_forall_covBy (P := fun H ↦ IsPretransitive H α)
    (fun H K hHK hH ↦ ⟨fun x y ↦ ?_⟩) (fun τ H hH ↦ ?_) htop h𝓡 hG
  · obtain ⟨g, hg⟩ := hH.exists_smul_eq x y
    exact ⟨Subgroup.inclusion hHK g, hg⟩
  · rwa [conj_eq_permCongrHom, isPretransitive_map_permCongrHom_iff]

end TauCeti
