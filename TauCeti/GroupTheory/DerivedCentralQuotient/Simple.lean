/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.GroupAction.Iwasawa
public import TauCeti.GroupTheory.DerivedCentralQuotient

/-!
# Simplicity of the derived central quotient

Write `D = [G, G]`. If every normal subgroup of `D` is central or all of `D`, then
`D / Z(D)` is simple provided `D` is noncommutative. The normal-subgroup conclusion for the
quotient is proved separately from nontriviality.

An Iwasawa structure supplies the normal-subgroup hypothesis when `D` is perfect and acts
quasiprimitively with central kernel. This allows the centre to act trivially, as it does in
the actions used to prove simplicity of central quotients.

These are prerequisites for T0 of the roadmap on finiteness and simplicity of the CFSG list.
The split BN-pair normal-subgroup theorem and its group-specific hypotheses are separate
from the criteria here.
-/

public section

namespace TauCeti.DerivedCentralQuotient

open _root_.Subgroup

variable {G : Type*} [Group G]

/-- Noncommutativity of the derived subgroup is exactly the nontriviality needed for simplicity
of its central quotient. -/
theorem nontrivial_iff :
    Nontrivial (DerivedCentralQuotient G) ↔ ¬ IsMulCommutative ↥(commutator G) := by
  rw [QuotientGroup.nontrivial_iff, ne_eq, center_eq_top_iff]

/-- Pulling a normal subgroup back along `D → D / Z(D)` turns a central-or-whole criterion
on `D` into the normal-subgroup dichotomy on the quotient. No nontriviality is needed here. -/
theorem normal_eq_bot_or_eq_top
    (hnormal : ∀ N : Subgroup ↥(commutator G), N.Normal →
      N ≤ center ↥(commutator G) ∨ N = ⊤)
    (N : Subgroup (DerivedCentralQuotient G)) [N.Normal] : N = ⊥ ∨ N = ⊤ := by
  rcases hnormal (N.comap (QuotientGroup.mk' _)) inferInstance with hN | hN
  · left
    apply le_antisymm _ bot_le
    apply (comap_le_comap_of_surjective (QuotientGroup.mk'_surjective _)).mp
    simpa only [MonoidHom.comap_bot, QuotientGroup.ker_mk'] using hN
  · right
    apply comap_injective (QuotientGroup.mk'_surjective (center ↥(commutator G)))
    simpa only [comap_top] using hN

/-- The derived central quotient is simple if its derived subgroup is noncommutative and
every normal subgroup of that derived subgroup is central or the whole subgroup. -/
theorem isSimpleGroup_of_normal_subgroups
    (hnoncomm : ¬ IsMulCommutative ↥(commutator G))
    (hnormal : ∀ N : Subgroup ↥(commutator G), N.Normal →
      N ≤ center ↥(commutator G) ∨ N = ⊤) :
    IsSimpleGroup (DerivedCentralQuotient G) := by
  have : Nontrivial (DerivedCentralQuotient G) := nontrivial_iff.mpr hnoncomm
  exact ⟨normal_eq_bot_or_eq_top hnormal⟩

section Iwasawa

variable [Group.IsPerfect ↥(commutator G)] {α : Type*}
variable [MulAction ↥(commutator G) α]
variable [MulAction.IsQuasiPreprimitive ↥(commutator G) α]

/-- In a quasiprimitive Iwasawa action of a perfect derived subgroup with central kernel,
every normal subgroup is central or whole. The action need not be faithful on the derived
subgroup itself. -/
theorem normal_le_center_or_eq_top_of_iwasawa
    (I : MulAction.IwasawaStructure ↥(commutator G) α)
    (hker : (MulAction.toPermHom ↥(commutator G) α).ker ≤ center ↥(commutator G))
    (N : Subgroup ↥(commutator G)) [N.Normal] :
    N ≤ center ↥(commutator G) ∨ N = ⊤ := by
  by_cases hfixed : MulAction.fixedPoints N α = Set.univ
  · left
    intro n hn
    apply hker
    apply Equiv.Perm.ext
    intro x
    exact Set.eq_univ_iff_forall.mp hfixed x ⟨n, hn⟩
  · right
    simpa only [Group.IsPerfect.commutator_eq_top, top_le_iff] using I.commutator_le N hfixed

/-- An Iwasawa action of the perfect derived subgroup proves simplicity of the exact
derived central quotient when the action kernel is central and the derived subgroup is
noncommutative. -/
theorem isSimpleGroup_of_iwasawa
    (hnoncomm : ¬ IsMulCommutative ↥(commutator G))
    (I : MulAction.IwasawaStructure ↥(commutator G) α)
    (hker : (MulAction.toPermHom ↥(commutator G) α).ker ≤ center ↥(commutator G)) :
    IsSimpleGroup (DerivedCentralQuotient G) :=
  isSimpleGroup_of_normal_subgroups hnoncomm fun N _ ↦
    normal_le_center_or_eq_top_of_iwasawa I hker N

end Iwasawa

end TauCeti.DerivedCentralQuotient
