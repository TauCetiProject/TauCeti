/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.NormalSubgroup.Lattice
public import Mathlib.Data.SetLike.Fintype
public import Mathlib.GroupTheory.IsSubnormal
public import Mathlib.Order.RelSeries
import TauCeti.Algebra.Group.Subgroup.Map

/-!
# Composition series of groups

A group composition series is a finite strictly increasing chain from the trivial subgroup to
the whole group, with each term normal in the next and each successive quotient simple.

`exists_relSeries_isCompositionStep_between` refines any normal inclusion whose upper subgroup
satisfies both chain conditions on subgroups. In particular, every finite group has a composition
series. The terminal step uses `TauCeti.NormalSubgroup.isCoatom_iff_isSimpleGroup` to characterize
simple quotients. Every term of a composition series is subnormal in the ambient group.
-/

public section

namespace Subgroup

variable {G : Type*} [Group G]

/-- A composition step is a proper normal inclusion with simple quotient. -/
structure IsCompositionStep (H K : Subgroup G) : Prop where
  lt : H < K
  normal : (H.subgroupOf K).Normal
  isSimpleGroup_quotient : letI := normal; IsSimpleGroup (K ⧸ H.subgroupOf K)

/-- A normal inclusion is a composition step exactly when its lower term is a coatom in the
lattice of normal subgroups of the upper term. -/
theorem isCompositionStep_iff_isCoatom {H K : Subgroup G} (hHK : H ≤ K)
    (hNormal : (H.subgroupOf K).Normal) :
    H.IsCompositionStep K ↔
      IsCoatom (⟨H.subgroupOf K, TauCeti.mem_normalSubgroups.mpr hNormal⟩ :
        TauCeti.NormalSubgroup K) := by
  have := hNormal
  refine ⟨fun h ↦ TauCeti.NormalSubgroup.isCoatom_iff_isSimpleGroup.mpr
    h.isSimpleGroup_quotient, fun h ↦ ⟨?_, hNormal,
      TauCeti.NormalSubgroup.isCoatom_iff_isSimpleGroup.mp h⟩⟩
  exact lt_of_le_of_ne hHK fun he ↦ h.1 (Subtype.ext (by simp [he]))

end Subgroup

namespace TauCeti

variable (G : Type*) [Group G]

/-- A composition series of a group, indexed from the trivial subgroup to the whole group. -/
structure GroupCompositionSeries extends
    RelSeries {p : Subgroup G × Subgroup G | p.1.IsCompositionStep p.2} where
  head_eq_bot : toRelSeries.head = ⊥
  last_eq_top : toRelSeries.last = ⊤

variable {G}

/-- A proper normal inclusion has a terminal composition step when subgroups satisfy the
ascending chain condition. -/
private theorem exists_terminal_isCompositionStep {A B : Subgroup G}
    [WellFoundedGT (Subgroup B)] (hAB : A < B) (hN : (A.subgroupOf B).Normal) :
    ∃ C : Subgroup G, A ≤ C ∧ (A.subgroupOf C).Normal ∧ C.IsCompositionStep B := by
  let NA : NormalSubgroup B := ⟨A.subgroupOf B, mem_normalSubgroups.mpr hN⟩
  have hNA : NA ≠ ⊤ := by
    intro he
    exact hAB.ne (le_antisymm hAB.le
      (Subgroup.subgroupOf_eq_top.mp congr(Subtype.val $he)))
  obtain ⟨M, hM, hAM⟩ := (eq_top_or_exists_le_coatom NA).resolve_left hNA
  let C : Subgroup G := (M : Subgroup B).map B.subtype
  have hCM : C.subgroupOf B = (M : Subgroup B) := by
    simpa only [C, Subgroup.MapSubtype.orderIso_symm_apply,
      Subgroup.MapSubtype.orderIso_apply_coe] using
      (Subgroup.MapSubtype.orderIso B).symm_apply_apply (M : Subgroup B)
  have hCBlt : C < B := by
    simpa only [Subgroup.map_top, Subgroup.range_subtype] using
      (Subgroup.map_subtype_lt_map_subtype.mpr
        (show (M : Subgroup B) < ⊤ from Subtype.coe_lt_coe.mpr hM.lt_top))
  have hCB : C ≤ B := hCBlt.le
  have hAC : A ≤ C := by
    simpa only [Subgroup.map_subgroupOf_eq_of_le hAB.le] using
      (Subgroup.map_mono hAM : (A.subgroupOf B).map B.subtype ≤ C)
  have hNC : (A.subgroupOf C).Normal := by
    simpa only [Subgroup.comap_inclusion_subgroupOf] using
      hN.comap (Subgroup.inclusion hCB)
  have hNormal : (C.subgroupOf B).Normal := hCM ▸ inferInstance
  refine ⟨C, hAC, hNC, (Subgroup.isCompositionStep_iff_isCoatom hCB hNormal).mpr ?_⟩
  convert hM using 1
  exact Subtype.ext hCM

/-- A normal interval admits a series of composition steps when the upper subgroup satisfies
both the ascending and descending chain conditions on subgroups. -/
theorem exists_relSeries_isCompositionStep_between {A B : Subgroup G}
    [WellFoundedLT (Subgroup B)] [WellFoundedGT (Subgroup B)]
    (hAB : A ≤ B) (hN : (A.subgroupOf B).Normal) :
    ∃ s : RelSeries {p : Subgroup G × Subgroup G | p.1.IsCompositionStep p.2},
      s.head = A ∧ s.last = B := by
  have : WellFoundedLT {C : Subgroup G // C ≤ B} :=
    (Subgroup.MapSubtype.orderIso B).symm.toOrderEmbedding.wellFoundedLT
  suffices ∀ C : {C : Subgroup G // C ≤ B}, ∀ A ≤ C.val, (A.subgroupOf C.val).Normal →
      ∃ s : RelSeries {p : Subgroup G × Subgroup G | p.1.IsCompositionStep p.2},
        s.head = A ∧ s.last = C.val from this ⟨B, le_rfl⟩ A hAB hN
  intro C
  induction C using WellFoundedLT.induction with
  | ind C ih =>
    intro A hAC hN
    by_cases h : A = C.val
    · subst A
      exact ⟨.singleton _ C.val, RelSeries.head_singleton _, RelSeries.last_singleton _⟩
    have := (Subgroup.inclusion C.property).wellFoundedGT_subgroup
      (Subgroup.inclusion_injective _)
    obtain ⟨D, hAD, hND, hstep⟩ := exists_terminal_isCompositionStep (lt_of_le_of_ne hAC h) hN
    obtain ⟨s, hsA, hsD⟩ := ih ⟨D, hstep.lt.le.trans C.property⟩ hstep.lt A hAD hND
    exact ⟨s.snoc C.val (hsD ▸ hstep), by simpa using hsA, by simp⟩

/-- Every group satisfying both chain conditions on subgroups has a composition series.
In particular, this applies to every finite group. -/
theorem nonempty_groupCompositionSeries [WellFoundedLT (Subgroup G)]
    [WellFoundedGT (Subgroup G)] : Nonempty (GroupCompositionSeries G) := by
  have := (⊤ : Subgroup G).subtype.wellFoundedLT_subgroup (Subgroup.subtype_injective _)
  have := (⊤ : Subgroup G).subtype.wellFoundedGT_subgroup (Subgroup.subtype_injective _)
  obtain ⟨s, h0, h1⟩ := exists_relSeries_isCompositionStep_between (G := G) bot_le
    (inferInstance : ((⊥ : Subgroup G).subgroupOf ⊤).Normal)
  exact ⟨⟨s, h0, h1⟩⟩

namespace GroupCompositionSeries

instance : CoeFun (GroupCompositionSeries G)
    (fun s ↦ Fin (s.toRelSeries.length + 1) → Subgroup G) :=
  ⟨fun s ↦ s.toRelSeries⟩

/-- A bundled composition series has the same indexed terms as the series used to construct it. -/
@[simp]
theorem coe_mk (s : RelSeries {p : Subgroup G × Subgroup G | p.1.IsCompositionStep p.2})
    (h0 : s.head = ⊥) (h1 : s.last = ⊤) : ⇑(GroupCompositionSeries.mk s h0 h1) = ⇑s :=
  (rfl)

/-- A composition series is determined by its length and its indexed terms. -/
@[ext (iff := false)]
theorem ext {s t : GroupCompositionSeries G} (hl : s.length = t.length)
    (hf : ∀ i, s i = t (i.cast (by rw [hl]))) : s = t := by
  have h : s.toRelSeries = t.toRelSeries := RelSeries.ext hl (funext hf)
  cases s
  cases t
  cases h
  rfl

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
theorem normal_subgroupOf_succ (s : GroupCompositionSeries G) (i : Fin s.length) :
    ((s i.castSucc).subgroupOf (s i.succ)).Normal :=
  (s.step i).normal

/-- The successive quotients of a composition series are simple, on their actual carriers. -/
theorem isSimpleGroup_quotient (s : GroupCompositionSeries G) (i : Fin s.length) :
    letI := s.normal_subgroupOf_succ i
    IsSimpleGroup (s i.succ ⧸ (s i.castSucc).subgroupOf (s i.succ)) :=
  (s.step i).isSimpleGroup_quotient

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
