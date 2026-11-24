/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.NormalSubgroup.Lattice
public import Mathlib.GroupTheory.IsSubnormal
public import Mathlib.Order.RelSeries

import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.Data.SetLike.Fintype
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Order.Atoms.Finite

/-!
# Composition series of groups

A group composition series is a finite strictly increasing chain from the trivial subgroup to
the whole group, with each term normal in the next and each successive quotient simple.

`exists_groupCompositionSeries_between` refines any normal inclusion into a finite subgroup.
In particular, every finite group has a composition series. Every term of a composition series is
subnormal in the ambient group.
-/

public section

namespace Subgroup

variable {G : Type*} [Group G]

/-- A composition step is a proper normal inclusion with simple quotient. -/
structure IsCompositionStep (H K : Subgroup G) : Prop where
  lt : H < K
  normal : (H.subgroupOf K).Normal
  isSimple : letI := normal; IsSimpleGroup (K ⧸ H.subgroupOf K)

end Subgroup

namespace TauCeti

variable (G : Type*) [Group G]

/-- A composition series of a group, indexed from the trivial subgroup to the whole group. -/
structure GroupCompositionSeries extends
    RelSeries {p : Subgroup G × Subgroup G | p.1.IsCompositionStep p.2} where
  head_eq_bot : toRelSeries.head = ⊥
  last_eq_top : toRelSeries.last = ⊤

variable {G}

/-- A finite normal interval admits a series of composition steps. -/
theorem exists_groupCompositionSeries_between {A B : Subgroup G} [Finite B]
    (hAB : A ≤ B) (hN : (A.subgroupOf B).Normal) :
    ∃ s : RelSeries {p : Subgroup G × Subgroup G | p.1.IsCompositionStep p.2},
      s.head = A ∧ s.last = B := by
  induction n : Nat.card B using Nat.strong_induction_on generalizing A B with
  | ind n ih =>
    by_cases h : A = B
    · subst A
      exact ⟨.singleton _ B, rfl, rfl⟩
    let NA : NormalSubgroup B := ⟨A.subgroupOf B, mem_normalSubgroups.mpr hN⟩
    have hNA : NA ≠ ⊤ := by
      intro he
      exact h (le_antisymm hAB (Subgroup.subgroupOf_eq_top.mp congr(Subtype.val $he)))
    obtain ⟨M, hM, hAM⟩ := (eq_top_or_exists_le_coatom NA).resolve_left hNA
    let C : Subgroup G := (M : Subgroup B).map B.subtype
    have hCB : C ≤ B := Subgroup.map_subtype_le _
    have hCM : C.subgroupOf B = (M : Subgroup B) :=
      Subgroup.comap_map_eq_self_of_injective B.subtype_injective _
    have hCBlt : C < B := lt_of_le_of_ne hCB fun he ↦ hM.1 (Subtype.ext (by
      rw [← hCM, he, Subgroup.subgroupOf_self, CompleteSublattice.coe_top]))
    have hAC : A ≤ C := by
      simpa only [Subgroup.map_subgroupOf_eq_of_le hAB] using
        (Subgroup.map_mono hAM : (A.subgroupOf B).map B.subtype ≤ C)
    have hNC : (A.subgroupOf C).Normal := by
      simpa only [Subgroup.comap_inclusion_subgroupOf] using
        hN.comap (Subgroup.inclusion hCB)
    have : Finite C := ((Set.toFinite (B : Set G)).subset hCB).to_subtype
    obtain ⟨s, hsA, hsC⟩ := ih (Nat.card C) (n ▸ Subgroup.card_lt_of_lt hCBlt) hAC hNC rfl
    have hstep : Subgroup.IsCompositionStep C B := by
      have : (C.subgroupOf B).Normal := hCM ▸ inferInstance
      refine ⟨hCBlt, this, ?_⟩
      exact (QuotientGroup.quotientMulEquivOfEq hCM).isSimpleGroup_congr.mpr
        (NormalSubgroup.isCoatom_iff_isSimpleGroup.mp hM)
    exact ⟨s.snoc B (hsC ▸ hstep), by simpa using hsA, by simp⟩

/-- Every finite group has a composition series. -/
theorem nonempty_groupCompositionSeries [Finite G] : Nonempty (GroupCompositionSeries G) := by
  obtain ⟨s, h0, h1⟩ := exists_groupCompositionSeries_between (G := G) bot_le
    (inferInstance : ((⊥ : Subgroup G).subgroupOf ⊤).Normal)
  exact ⟨⟨s, h0, h1⟩⟩

namespace GroupCompositionSeries

instance : CoeFun (GroupCompositionSeries G)
    (fun s ↦ Fin (s.toRelSeries.length + 1) → Subgroup G) :=
  ⟨fun s ↦ s.toRelSeries⟩

/-- The first indexed term is the trivial subgroup. -/
@[simp]
theorem apply_zero (s : GroupCompositionSeries G) : s 0 = ⊥ :=
  (RelSeries.apply_zero s.toRelSeries).trans s.head_eq_bot

/-- The last indexed term is the whole group. -/
@[simp]
theorem apply_last (s : GroupCompositionSeries G) : s (Fin.last s.length) = ⊤ :=
  (RelSeries.apply_last s.toRelSeries).trans s.last_eq_top

/-- The terms of a composition series are strictly increasing. -/
theorem strictMono (s : GroupCompositionSeries G) : StrictMono s :=
  LTSeries.strictMono (s.toRelSeries.ofLE fun _ h ↦ h.lt)

/-- Each term of a composition series is normal in its successor. -/
theorem normal (s : GroupCompositionSeries G) (i : Fin s.length) :
    ((s i.castSucc).subgroupOf (s i.succ)).Normal :=
  (s.step i).normal

/-- The successive quotients of a composition series are simple, on their actual carriers. -/
theorem isSimple (s : GroupCompositionSeries G) (i : Fin s.length) :
    letI := s.normal i
    IsSimpleGroup (s i.succ ⧸ (s i.castSucc).subgroupOf (s i.succ)) :=
  (s.step i).isSimple

/-- Every term of a composition series is subnormal in the ambient group. -/
theorem isSubnormal (s : GroupCompositionSeries G) (i : Fin (s.length + 1)) :
    (s i).IsSubnormal := by
  induction i using Fin.reverseInduction with
  | last =>
    simpa only [s.apply_last] using (Subgroup.IsSubnormal.top (G := G))
  | cast i ih =>
    exact Subgroup.IsSubnormal.step _ _ (s.step i).lt.le ih (s.step i).normal

end GroupCompositionSeries

end TauCeti
