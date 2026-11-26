/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.SetLike.Fintype
public import Mathlib.GroupTheory.Index
public import Mathlib.Order.JordanHolder
public import Mathlib.Order.RelSeries
public import TauCeti.Algebra.Category.Grp.FiniteGrp
public import TauCeti.GroupTheory.NormalSubgroup.Lattice

/-!
# Chief series and the Jordan–Hölder theorem for chief factors

Here a **chief series** of a group `G` is a composition series in the modular lattice
`TauCeti.NormalSubgroup G` of normal subgroups: a finite chain of normal subgroups of `G` in which
each term is covered, among normal subgroups of `G`, by the next. Its first and last terms are
arbitrary; chief series in the usual sense are those with `s.head = ⊥` and `s.last = ⊤`. Its
**chief factors** are the successive quotients. For a finite group, `TauCeti.chiefFactors s` is
the multiset of their isomorphism classes, as elements of `TauCeti.IsoClass`.

The Jordan–Hölder theorem for chief series says that this multiset does not depend on the chief
series. It is Mathlib's `CompositionSeries.jordan_holder` for the modular lattice of normal
subgroups, combined with the second isomorphism theorem: the elementary isomorphisms of intervals
`[x, x ⊔ y] ≅ [x ⊓ y, y]` in that lattice are realized by the group isomorphisms
`(x ⊔ y) ⧸ x ≃* y ⧸ (x ⊓ y)`. This is Jordan–Hölder for `G` acting on itself by conjugation.

## Main definitions

* `TauCeti.ChiefSeries G`: chief series of `G`, as composition series of normal subgroups.
* `TauCeti.NormalSubgroup.factor M N`: the isomorphism class of the quotient `N ⧸ M` of normal
  subgroups.
* `TauCeti.chiefFactors s`: the multiset of chief factors of a chief series `s`.

## Main results

* `TauCeti.exists_chiefSeries`: a group with both chain conditions on normal subgroups, for instance
  a finite group, has a chief series from `⊥` to `⊤`.
* `TauCeti.chiefFactors_eq`: **Jordan–Hölder for chief series**: two chief series of a finite
  group with the same first and last terms have the same multiset of chief factors.

## References

* [J. S. Milne, *Group Theory*, version 4.01][milne2025gt], Example 6.29(a).
-/

public section

open Subgroup

namespace TauCeti

variable {G : Type*} [Group G]

variable (G) in
/-- A **chief series** of `G`: a composition series in the modular lattice of normal subgroups of
`G`, each term covered by the next among the normal subgroups of `G`. -/
abbrev ChiefSeries : Type _ :=
  CompositionSeries (NormalSubgroup G)

/-- A group satisfying both chain conditions on normal subgroups, for instance a finite group, has
a chief series from `⊥` to `⊤`. -/
theorem exists_chiefSeries [WellFoundedLT (NormalSubgroup G)] [WellFoundedGT (NormalSubgroup G)] :
    ∃ s : ChiefSeries G, s.head = ⊥ ∧ s.last = ⊤ := by
  obtain ⟨f, f0, n, hn⟩ := exists_covBy_seq_of_wellFoundedLT_wellFoundedGT (NormalSubgroup G)
  exact ⟨⟨n, fun i ↦ f i, fun i ↦ hn.2 i i.isLt⟩, f0.eq_bot, hn.1.eq_top⟩

namespace NormalSubgroup

variable [Finite G]

/-- The isomorphism class of the quotient `N ⧸ M` of two normal subgroups of a finite group, that
is, of `N ⧸ M.subgroupOf N`. When `M ≤ N` this is the factor `N ⧸ M` of the pair `M ≤ N`. -/
noncomputable def factor (M N : NormalSubgroup G) : IsoClass :=
  IsoClass.mk (N ⧸ (M : Subgroup G).subgroupOf N)

theorem factor_def (M N : NormalSubgroup G) :
    factor M N = IsoClass.mk (N ⧸ (M : Subgroup G).subgroupOf N) :=
  (rfl)

/-- The **second isomorphism theorem** for factors of normal subgroups: `(x ⊔ y) ⧸ x` and
`y ⧸ (x ⊓ y)` are isomorphic. -/
theorem factor_sup_left (x y : NormalSubgroup G) : factor x (x ⊔ y) = factor (x ⊓ y) y := by
  rw [sup_comm]
  exact (IsoClass.mk_eq_mk_of_mulEquiv <|
    (QuotientGroup.quotientMulEquivOfEq (by rw [coe_inf, inf_subgroupOf_right])).trans
      (QuotientGroup.quotientInfEquivProdNormalQuotient (y : Subgroup G) x)).symm

/-- Isomorphic intervals of normal subgroups, in the sense of the Jordan–Hölder lattice of normal
subgroups, have the same factor. -/
theorem factor_eq_of_iso {p q : NormalSubgroup G × NormalSubgroup G}
    (h : JordanHolderLattice.Iso p q) : factor p.1 p.2 = factor q.1 q.2 :=
  JordanHolderLattice.Iso.rel (fun p q ↦ factor p.1 p.2 = factor q.1 q.2) rfl Eq.symm Eq.trans
    (fun _ ↦ factor_sup_left _ _) h

end NormalSubgroup

variable [Finite G]

/-- The **chief factors** of a chief series `s` of a finite group: the multiset of the isomorphism
classes of its successive quotients `s (i + 1) ⧸ s i`. -/
noncomputable def chiefFactors (s : ChiefSeries G) : Multiset IsoClass :=
  Finset.univ.val.map fun i : Fin s.length ↦ (s i.castSucc).factor (s i.succ)

theorem chiefFactors_def (s : ChiefSeries G) :
    chiefFactors s = Finset.univ.val.map fun i : Fin s.length ↦ (s i.castSucc).factor (s i.succ) :=
  (rfl)

/-- A chief series has as many chief factors as its length. -/
@[simp]
theorem card_chiefFactors (s : ChiefSeries G) : Multiset.card (chiefFactors s) = s.length := by
  simp [chiefFactors_def]

/-- **Jordan–Hölder for chief series.** Two chief series of a finite group with the same first and
last terms, for instance two chief series from `⊥` to `⊤`, have the same multiset of chief
factors. -/
theorem chiefFactors_eq (s t : ChiefSeries G) (h₁ : s.head = t.head) (h₂ : s.last = t.last) :
    chiefFactors s = chiefFactors t := by
  obtain ⟨e, he⟩ := CompositionSeries.jordan_holder s t h₁ h₂
  rw [chiefFactors_def, chiefFactors_def, ← Finset.univ_map_equiv_to_embedding e, Finset.map_val,
    Multiset.map_map]
  exact Multiset.map_congr rfl fun i _ ↦ NormalSubgroup.factor_eq_of_iso (he i)

end TauCeti
