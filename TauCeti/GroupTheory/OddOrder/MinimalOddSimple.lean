/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.IsPerfect
public import Mathlib.GroupTheory.QuotientGroup.Defs
public import Mathlib.GroupTheory.Solvable
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.GroupTheory.Index
import TauCeti.GroupTheory.DerivedCentralQuotient
import TauCeti.GroupTheory.Subgroup.Simple

/-!
# Minimal odd simple groups

A **minimal odd simple group** is a nonabelian simple group of odd order all of whose proper
subgroups are solvable. It is the minimal counterexample to the Feit–Thompson odd order theorem:
the standing hypothesis of Bender–Glauberman, Chapter II, and of Peterfalvi, Part I, §8, under
which the local analysis and the character theory of the proof are carried out.

This file defines the predicate and proves the reduction to it. A finite nonsolvable group of odd
order has a section, a quotient of a subgroup, that is a minimal odd simple group: a nonsolvable
section of least order is simple, since otherwise a proper normal subgroup or the corresponding
quotient would be a smaller nonsolvable section, and it is nonabelian because abelian groups are
solvable. Consequently three forms of the odd order theorem are equivalent, universe by universe:
there is no finite minimal odd simple group, every finite group of odd order is solvable, and every
finite nonabelian simple group has even order. The equivalence does not assume any of the three.

The elementary properties of a minimal odd simple group `G` used later are stated on the predicate:
its centre is trivial, it is perfect, the centralizer of a nontrivial element is proper, its maximal
subgroups are self-normalizing, and every proper subgroup lies in a maximal subgroup. The first
four are those of a nonabelian simple group, and the last holds because `G` is finite. Every proper
subgroup is solvable by the field `IsMinimalOddSimple.proper_solvable`.

## Main definitions

* `TauCeti.IsMinimalOddSimple`: a nonabelian simple group of odd order whose proper subgroups are
  solvable.

## Main results

* `TauCeti.IsMinimalOddSimple.not_isSolvable`: a minimal odd simple group is not solvable.
* `TauCeti.IsMinimalOddSimple.center_eq_bot`, `TauCeti.IsMinimalOddSimple.commutator_eq_top`,
  `TauCeti.IsMinimalOddSimple.centralizer_ne_top`,
  `TauCeti.IsMinimalOddSimple.normalizer_eq_self_of_isCoatom` and
  `TauCeti.IsMinimalOddSimple.exists_isCoatom_le`: the elementary properties of a minimal odd simple
  group.
* `TauCeti.exists_isMinimalOddSimple_quotient_of_not_isSolvable`: a nonsolvable group of odd order
  has a minimal odd simple section.
* `TauCeti.not_isMinimalOddSimple_tfae`: the nonexistence of minimal odd simple groups, the
  solvability of groups of odd order, and the even order of nonabelian simple groups are
  equivalent.

## References

* H. Bender and G. Glauberman, *Local Analysis for the Odd Order Theorem*, London Mathematical
  Society Lecture Note Series 188, Cambridge University Press, 1994, Chapter II.
* T. Peterfalvi, *Character Theory for the Odd Order Theorem*, London Mathematical Society Lecture
  Note Series 272, Cambridge University Press, 2000, Part I, §8.
* G. Gonthier et al., *A Machine-Checked Proof of the Odd Order Theorem*, ITP 2013, where the
  corresponding notion is `minSimpleOddGroupType`.
-/

public section

namespace TauCeti

universe u

open _root_.Subgroup

variable (G : Type*) [Group G]

/-- A **minimal odd simple group**: a nonabelian simple group of odd order all of whose proper
subgroups are solvable. This is the minimal counterexample to the odd order theorem. Finiteness is
not a separate field: `Odd (Nat.card G)` forces `G` to be finite (`IsMinimalOddSimple.finite`). -/
structure IsMinimalOddSimple : Prop where
  /-- A minimal odd simple group has odd order. -/
  odd : Odd (Nat.card G)
  /-- A minimal odd simple group is simple. -/
  simple : IsSimpleGroup G
  /-- A minimal odd simple group is not commutative. -/
  nonabelian : ¬ IsMulCommutative G
  /-- Every proper subgroup of a minimal odd simple group is solvable. -/
  proper_solvable : ∀ H : Subgroup G, H ≠ ⊤ → Group.IsSolvable H

namespace IsMinimalOddSimple

variable {G}

/-- A minimal odd simple group is finite, since its order is odd and so nonzero. -/
theorem finite (h : IsMinimalOddSimple G) : Finite G :=
  Nat.finite_of_card_ne_zero h.odd.pos.ne'

/-- A minimal odd simple group is not solvable: a solvable simple group is commutative. -/
theorem not_isSolvable (h : IsMinimalOddSimple G) : ¬ Group.IsSolvable G :=
  have := h.simple
  have := IsSimpleGroup.isPerfect_of_not_isMulCommutative h.nonabelian
  Group.IsPerfect.not_isSolvable G

/-- Being a minimal odd simple group is invariant under isomorphism. -/
theorem of_mulEquiv {H : Type*} [Group H] (h : IsMinimalOddSimple H) (e : G ≃* H) :
    IsMinimalOddSimple G where
  odd := Nat.card_congr e.toEquiv ▸ h.odd
  simple := have := h.simple; e.isSimpleGroup
  nonabelian hG := h.nonabelian (e.isMulCommutative.mp hG)
  proper_solvable K hK :=
    have := h.proper_solvable (K.map e.toMonoidHom) fun hK' ↦ hK <| by
      rw [← comap_map_eq_self_of_injective (f := e.toMonoidHom) e.injective K, hK', comap_top]
    Group.isSolvable_of_isSolvable_injective
      (f := (K.equivMapOfInjective e.toMonoidHom e.injective).toMonoidHom) (MulEquiv.injective _)

/-- A minimal odd simple group has trivial centre. -/
theorem center_eq_bot (h : IsMinimalOddSimple G) : center G = ⊥ :=
  have := h.simple
  IsSimpleGroup.center_eq_bot_of_not_isMulCommutative h.nonabelian

/-- A minimal odd simple group is perfect: its commutator subgroup is the whole group. -/
theorem commutator_eq_top (h : IsMinimalOddSimple G) : commutator G = ⊤ :=
  have := h.simple
  (IsSimpleGroup.isPerfect_of_not_isMulCommutative h.nonabelian).commutator_eq_top

/-- In a minimal odd simple group, the centralizer of a nontrivial element is a proper
subgroup. -/
theorem centralizer_ne_top (h : IsMinimalOddSimple G) {x : G} (hx : x ≠ 1) :
    centralizer {x} ≠ ⊤ := fun hc ↦ by
  have hx' := centralizer_eq_top_iff_subset.mp hc (Set.mem_singleton x)
  rw [SetLike.mem_coe, h.center_eq_bot, mem_bot] at hx'
  exact hx hx'

/-- Every maximal subgroup of a minimal odd simple group is its own normalizer. -/
theorem normalizer_eq_self_of_isCoatom (h : IsMinimalOddSimple G) {M : Subgroup G}
    (hM : IsCoatom M) : normalizer (M : Set G) = M :=
  have := h.simple
  _root_.IsSimpleGroup.normalizer_eq_self_of_isCoatom h.nonabelian hM

/-- Every proper subgroup of a minimal odd simple group lies in a maximal subgroup. -/
theorem exists_isCoatom_le (h : IsMinimalOddSimple G) {H : Subgroup G} (hH : H ≠ ⊤) :
    ∃ M : Subgroup G, IsCoatom M ∧ H ≤ M :=
  have := h.finite
  (eq_top_or_exists_le_coatom H).resolve_left hH

end IsMinimalOddSimple

/-- The reduction in surjection form, by strong induction on the order: a finite nonsolvable group
of odd order maps a subgroup onto a minimal odd simple group in the same universe. -/
private theorem exists_surjective_isMinimalOddSimple_of_not_isSolvable :
    ∀ (n : ℕ) (G : Type u) [Group G] [Finite G], Nat.card G = n → Odd (Nat.card G) →
      ¬ Group.IsSolvable G → ∃ (H : Subgroup G) (S : Type u) (_ : Group S) (f : H →* S),
        Function.Surjective f ∧ IsMinimalOddSimple S := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro G _ _ hn hodd hG
  -- A nonsolvable proper subgroup is a smaller counterexample; its section is a section of `G`.
  by_cases hsub : ∃ K : Subgroup G, K ≠ ⊤ ∧ ¬ Group.IsSolvable K
  · obtain ⟨K, hK, hKs⟩ := hsub
    have hlt : Nat.card K < n := hn ▸ card_top (G := G) ▸ card_lt_of_lt hK.lt_top
    obtain ⟨H, S, _, f, hf, hS⟩ :=
      ih _ hlt K rfl (hodd.of_dvd_nat K.card_subgroup_dvd_card) hKs
    let e := H.equivMapOfInjective K.subtype K.subtype_injective
    exact ⟨H.map K.subtype, S, inferInstance, f.comp e.symm.toMonoidHom,
      hf.comp e.symm.surjective, hS⟩
  push Not at hsub
  have : Nontrivial G := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    exact hG inferInstance
  by_cases hsimple : IsSimpleGroup G
  -- A simple group all of whose proper subgroups are solvable is its own section.
  · refine ⟨⊤, G, inferInstance, (topEquiv : (⊤ : Subgroup G) ≃* G).toMonoidHom,
      topEquiv.surjective, hodd, hsimple, fun hc ↦ hG ?_, hsub⟩
    exact (IsSimpleGroup.comm_iff_isSolvable).mp (isMulCommutative_iff.mp hc)
  -- Otherwise a proper nontrivial normal subgroup `N` is solvable, so `G ⧸ N` is a smaller
  -- nonsolvable group of odd order, and its section lifts to a section of `G`.
  obtain ⟨N, hN, hbot, htop⟩ : ∃ N : Subgroup G, N.Normal ∧ N ≠ ⊥ ∧ N ≠ ⊤ := by
    by_contra! h
    exact hsimple ⟨fun N _ ↦ or_iff_not_imp_left.mpr (h N ‹_›)⟩
  have := hsub N htop
  have hQ : ¬ Group.IsSolvable (G ⧸ N) := fun _ ↦ hG (Group.isSolvable_of_subgroup_quotient N)
  have hlt : Nat.card (G ⧸ N) < n := by
    rw [← hn, card_eq_card_quotient_mul_card_subgroup N]
    exact lt_mul_of_one_lt_right (Nat.card_pos (α := G ⧸ N)) (N.one_lt_card_iff_ne_bot.mpr hbot)
  obtain ⟨H, S, _, f, hf, hS⟩ :=
    ih _ hlt (G ⧸ N) rfl (hodd.of_dvd_nat N.card_quotient_dvd_card) hQ
  exact ⟨H.comap (QuotientGroup.mk' N), S, inferInstance,
    f.comp ((QuotientGroup.mk' N).subgroupComap H),
    hf.comp ((QuotientGroup.mk' N).subgroupComap_surjective H (QuotientGroup.mk'_surjective N)),
    hS⟩

variable {G} in
/-- **Reduction to minimal odd simple groups.** A nonsolvable group of odd order, necessarily
finite, has a section, the quotient `H ⧸ N` of a subgroup `H` by a normal subgroup `N` of `H`, that
is a minimal odd simple group. -/
theorem exists_isMinimalOddSimple_quotient_of_not_isSolvable (hodd : Odd (Nat.card G))
    (hG : ¬ Group.IsSolvable G) :
    ∃ (H : Subgroup G) (N : Subgroup H) (_ : N.Normal), IsMinimalOddSimple (H ⧸ N) := by
  have := Nat.finite_of_card_ne_zero hodd.pos.ne'
  obtain ⟨H, S, _, f, hf, hS⟩ :=
    exists_surjective_isMinimalOddSimple_of_not_isSolvable _ G rfl hodd hG
  exact ⟨H, f.ker, inferInstance, hS.of_mulEquiv (QuotientGroup.quotientKerEquivOfSurjective f hf)⟩

/-- **Three equivalent forms of the odd order theorem.** For groups in a fixed universe, the
following are equivalent: no group is a minimal odd simple group; every group of odd order is
solvable; every nonabelian simple group has even order. No finiteness assumption is needed: a group
of odd order is finite, and an infinite group has `Nat.card` equal to `0`, which is even. -/
theorem not_isMinimalOddSimple_tfae : List.TFAE
    [∀ (G : Type u) [Group G], ¬ IsMinimalOddSimple G,
      ∀ (G : Type u) [Group G], Odd (Nat.card G) → Group.IsSolvable G,
      ∀ (G : Type u) [Group G] [IsSimpleGroup G], ¬ IsMulCommutative G → Even (Nat.card G)] := by
  tfae_have 1 → 2 := fun h G _ hodd ↦ by
    by_contra hG
    obtain ⟨H, N, _, hS⟩ := exists_isMinimalOddSimple_quotient_of_not_isSolvable hodd hG
    exact h _ hS
  tfae_have 2 → 3 := fun h G _ _ hG ↦ by
    by_contra hodd
    have := h G (Nat.not_even_iff_odd.mp hodd)
    exact hG (isMulCommutative_iff.mpr (IsSimpleGroup.comm_iff_isSolvable.mpr this))
  tfae_have 3 → 1 := fun h G _ hG ↦
    have := hG.simple
    Nat.not_even_iff_odd.mpr hG.odd (h G hG.nonabelian)
  tfae_finish

end TauCeti
