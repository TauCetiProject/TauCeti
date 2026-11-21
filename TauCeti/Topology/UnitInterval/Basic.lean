/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.UnitInterval

/-!
# Basic constructions on the unit interval

Elementary maps, membership lemmas, and open inclusions for `I = Set.Icc (0 : ℝ) 1`:

* The normalized height `(r - a) / (b - a)` of a point `r ∈ [a, b]` lies in the unit interval,
  including in the degenerate case `a = b`, where Lean's convention `x / 0 = 0` makes it `0`
  (`TauCeti.sub_div_sub_mem_unitInterval`).
* The tent map `TauCeti.tent : I → I`, `t ↦ min (2 t) (2 - 2 t)`, which rises linearly from `0`
  to `1` on `[0, 1 / 2]` and falls back to `0` on `[1 / 2, 1]`, together with its real-value
  formula, continuity, and endpoint values.
* `TauCeti.iocToUnitInterval`, `TauCeti.iocOne`, and `TauCeti.iooToIoc`: canonical open embeddings
  `(0, 1] → [0, 1]` (missing only `0`) and `(0, 1) → (0, 1]` (missing only `1 = iocOne`), together
  with their ranges and continuity lemmas.

## Main declarations

* `TauCeti.sub_div_sub_mem_unitInterval`: the normalized height `(r - a) / (b - a)` of `r ∈ [a, b]`
  lies in `unitInterval`, including when `a = b`.
* `TauCeti.tent`: the tent map `t ↦ min (2 t) (2 - 2 t)` on the unit interval.
* `TauCeti.coe_tent`, `TauCeti.continuous_tent`, `TauCeti.tent_zero`, `TauCeti.tent_one`: the
  coercion formula, continuity, and vanishing at `0` and `1` of `TauCeti.tent`.
* `TauCeti.iocToUnitInterval`, `TauCeti.iocOne`, `TauCeti.iooToIoc`: canonical open inclusions
  `(0, 1] → [0, 1]` and `(0, 1) → (0, 1]`.
-/

public section

open Set Topology
open scoped unitInterval

namespace TauCeti

/-- The normalized height of `r ∈ [a, b]` lies in `[0, 1]`, also when `a = b`. -/
theorem sub_div_sub_mem_unitInterval {a b r : ℝ} (har : a ≤ r) (hrb : r ≤ b) :
    (r - a) / (b - a) ∈ unitInterval :=
  unitInterval.div_mem (sub_nonneg.mpr har) (sub_nonneg.mpr (har.trans hrb))
    (sub_le_sub_right hrb a)

/-- The tent map `t ↦ min (2 t) (2 - 2 t)` on the unit interval, which rises from `0` to `1` on
`[0, 1/2]` and falls back to `0` on `[1/2, 1]`. -/
noncomputable def tent (t : I) : I :=
  ⟨min (2 * t) (2 - 2 * t), le_min (by linarith [t.property.1]) (by linarith [t.property.2]),
    min_le_iff.2 <| (le_total (t : ℝ) (1 / 2)).imp (fun h ↦ by linarith) fun h ↦ by linarith⟩

/-- The real value of `TauCeti.tent t` is `min (2 t) (2 - 2 t)`. -/
@[simp]
theorem coe_tent (t : I) : (tent t : ℝ) = min (2 * (t : ℝ)) (2 - 2 * t) := (rfl)

/-- The tent map on the unit interval is continuous. -/
@[fun_prop]
theorem continuous_tent : Continuous tent := by
  unfold tent
  fun_prop

/-- The tent map vanishes at `0`. -/
@[simp]
theorem tent_zero : tent 0 = 0 := by
  ext
  simp

/-- The tent map vanishes at `1`. -/
@[simp]
theorem tent_one : tent 1 = 0 := by
  ext
  norm_num

/-- Canonical inclusion `(0, 1] → [0, 1]`. -/
def iocToUnitInterval (x : Ioc (0 : ℝ) 1) : I := ⟨x.val, Ioc_subset_Icc_self x.property⟩

@[simp]
theorem coe_iocToUnitInterval (x : Ioc (0 : ℝ) 1) : (iocToUnitInterval x : ℝ) = x.val := (rfl)

theorem continuous_iocToUnitInterval : Continuous iocToUnitInterval :=
  continuous_subtypeVal.subtype_mk _

theorem range_iocToUnitInterval : range iocToUnitInterval = {(0 : I)}ᶜ :=
  Set.ext fun t => by
    simp only [mem_range, mem_compl_iff, mem_singleton_iff]
    exact ⟨fun ⟨x, hx⟩ h0 => x.property.1.ne' (congrArg Subtype.val (hx.trans h0)),
      fun ht0 => ⟨⟨t.val, lt_of_le_of_ne t.property.1 fun h => ht0 (Subtype.ext h.symm),
        t.property.2⟩, rfl⟩⟩

theorem notMem_range_iocToUnitInterval_iff (t : I) :
    t ∉ range iocToUnitInterval ↔ t = 0 := by
  rw [range_iocToUnitInterval, mem_compl_iff, mem_singleton_iff, not_not]

theorem isOpenEmbedding_iocToUnitInterval : IsOpenEmbedding iocToUnitInterval :=
  ⟨IsEmbedding.of_comp continuous_iocToUnitInterval continuous_subtypeVal IsEmbedding.subtypeVal,
    range_iocToUnitInterval ▸ isOpen_compl_singleton⟩

/-- The endpoint `1` of `Set.Ioc (0 : ℝ) 1`. -/
def iocOne : Ioc (0 : ℝ) 1 := ⟨1, right_mem_Ioc.mpr zero_lt_one⟩

@[simp]
theorem coe_iocOne : (iocOne : ℝ) = 1 := (rfl)

@[simp]
theorem iocToUnitInterval_iocOne : iocToUnitInterval iocOne = 1 := (rfl)

/-- Canonical inclusion `(0, 1) → (0, 1]`. -/
def iooToIoc (x : Ioo (0 : ℝ) 1) : Ioc (0 : ℝ) 1 := ⟨x.val, Ioo_subset_Ioc_self x.property⟩

@[simp]
theorem coe_iooToIoc (x : Ioo (0 : ℝ) 1) : (iooToIoc x : ℝ) = x.val := (rfl)

theorem continuous_iooToIoc : Continuous iooToIoc :=
  continuous_subtypeVal.subtype_mk _

theorem range_iooToIoc : range iooToIoc = {iocOne}ᶜ :=
  Set.ext fun t => by
    simp only [mem_range, mem_compl_iff, mem_singleton_iff]
    exact ⟨fun ⟨x, hx⟩ h1 => x.property.2.ne (congrArg Subtype.val (hx.trans h1)),
      fun ht1 => ⟨⟨t.val, t.property.1, lt_of_le_of_ne t.property.2 fun h => ht1 (Subtype.ext h)⟩,
        rfl⟩⟩

theorem notMem_range_iooToIoc_iff (t : Ioc (0 : ℝ) 1) :
    t ∉ range iooToIoc ↔ t = iocOne := by
  rw [range_iooToIoc, mem_compl_iff, mem_singleton_iff, not_not]

theorem isOpenEmbedding_iooToIoc : IsOpenEmbedding iooToIoc :=
  ⟨IsEmbedding.of_comp continuous_iooToIoc continuous_subtypeVal IsEmbedding.subtypeVal,
    range_iooToIoc ▸ isOpen_compl_singleton⟩

end TauCeti
