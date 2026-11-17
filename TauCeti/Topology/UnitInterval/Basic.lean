/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.UnitInterval

/-!
# Basic lemmas and open inclusions for the unit interval

This file collects elementary facts about the unit interval `I = [0, 1]` and its open subintervals:

* `TauCeti.sub_div_sub_mem_unitInterval`: the normalized height `(r - a) / (b - a)` of `r ∈ [a, b]`
  lies in `unitInterval`, including in the degenerate case `a = b`, where Lean's convention
  `x / 0 = 0` makes it `0`.
* `TauCeti.iocToUnitInterval`, `TauCeti.iocOne`, and `TauCeti.iooToIoc`: canonical open embeddings
  `(0, 1] → [0, 1]` (missing only `0`) and `(0, 1) → (0, 1]` (missing only `1 = iocOne`), together
  with their ranges and continuity lemmas.
-/

public section

open Set Topology unitInterval

namespace TauCeti

/-- The normalized height of `r ∈ [a, b]` lies in `[0, 1]`, also when `a = b`. -/
theorem sub_div_sub_mem_unitInterval {a b r : ℝ} (har : a ≤ r) (hrb : r ≤ b) :
    (r - a) / (b - a) ∈ unitInterval :=
  unitInterval.div_mem (sub_nonneg.mpr har) (sub_nonneg.mpr (har.trans hrb))
    (sub_le_sub_right hrb a)

/-- Canonical inclusion `(0, 1] → [0, 1]`. -/
def iocToUnitInterval (x : Ioc (0 : ℝ) 1) : I := ⟨x.1, Ioc_subset_Icc_self x.2⟩

@[simp]
theorem coe_iocToUnitInterval (x : Ioc (0 : ℝ) 1) : (iocToUnitInterval x : ℝ) = x.1 := (rfl)

theorem continuous_iocToUnitInterval : Continuous iocToUnitInterval :=
  continuous_subtype_val.subtype_mk _

theorem range_iocToUnitInterval : range iocToUnitInterval = {(0 : I)}ᶜ :=
  Set.ext fun t => by
    simp only [mem_range, mem_compl_iff, mem_singleton_iff]
    exact ⟨fun ⟨x, hx⟩ h0 => x.2.1.ne' (congrArg Subtype.val (hx.trans h0)),
      fun ht0 => ⟨⟨t.1, lt_of_le_of_ne t.2.1 fun h => ht0 (Subtype.ext h.symm), t.2.2⟩, rfl⟩⟩

theorem notMem_range_iocToUnitInterval_iff (t : I) :
    t ∉ range iocToUnitInterval ↔ t = 0 := by
  rw [range_iocToUnitInterval, mem_compl_iff, mem_singleton_iff, not_not]

theorem isOpenEmbedding_iocToUnitInterval : IsOpenEmbedding iocToUnitInterval :=
  ⟨IsEmbedding.of_comp continuous_iocToUnitInterval continuous_subtype_val IsEmbedding.subtypeVal,
    range_iocToUnitInterval ▸ isOpen_compl_singleton⟩

/-- The endpoint `1` of `Set.Ioc (0 : ℝ) 1`. -/
def iocOne : Ioc (0 : ℝ) 1 := ⟨1, right_mem_Ioc.mpr zero_lt_one⟩

@[simp]
theorem coe_iocOne : (iocOne : ℝ) = 1 := (rfl)

@[simp]
theorem iocToUnitInterval_iocOne : iocToUnitInterval iocOne = 1 := (rfl)

/-- Canonical inclusion `(0, 1) → (0, 1]`. -/
def iooToIoc (x : Ioo (0 : ℝ) 1) : Ioc (0 : ℝ) 1 := ⟨x.1, Ioo_subset_Ioc_self x.2⟩

@[simp]
theorem coe_iooToIoc (x : Ioo (0 : ℝ) 1) : (iooToIoc x : ℝ) = x.1 := (rfl)

theorem continuous_iooToIoc : Continuous iooToIoc :=
  continuous_subtype_val.subtype_mk _

theorem range_iooToIoc : range iooToIoc = {iocOne}ᶜ :=
  Set.ext fun t => by
    simp only [mem_range, mem_compl_iff, mem_singleton_iff]
    exact ⟨fun ⟨x, hx⟩ h1 => x.2.2.ne (congrArg Subtype.val (hx.trans h1)),
      fun ht1 => ⟨⟨t.1, t.2.1, lt_of_le_of_ne t.2.2 fun h => ht1 (Subtype.ext h)⟩, rfl⟩⟩

theorem notMem_range_iooToIoc_iff (t : Ioc (0 : ℝ) 1) :
    t ∉ range iooToIoc ↔ t = iocOne := by
  rw [range_iooToIoc, mem_compl_iff, mem_singleton_iff, not_not]

theorem isOpenEmbedding_iooToIoc : IsOpenEmbedding iooToIoc :=
  ⟨IsEmbedding.of_comp continuous_iooToIoc continuous_subtype_val IsEmbedding.subtypeVal,
    range_iooToIoc ▸ isOpen_compl_singleton⟩

end TauCeti
