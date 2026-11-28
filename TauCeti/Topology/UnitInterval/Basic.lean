/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.UnitInterval
import TauCeti.Data.Set.Function

/-!
# Basic constructions on the unit interval

Elementary maps, membership lemmas, and open inclusions for `I = Set.Icc (0 : ℝ) 1`:

* The normalized height `(r - a) / (b - a)` of a point `r ∈ [a, b]` lies in the unit interval,
  including in the degenerate case `a = b`, where Lean's convention `x / 0 = 0` makes it `0`
  (`TauCeti.sub_div_sub_mem_unitInterval`).
* The tent map `TauCeti.tent : I → I`, `t ↦ min (2 t) (2 - 2 t)`, which rises linearly from `0`
  to `1` on `[0, 1 / 2]` and falls back to `0` on `[1 / 2, 1]`, together with its real-value
  formula, continuity, and endpoint values.
* `TauCeti.iocOne`, `TauCeti.inclusion_Ioc_Icc_iocOne`,
  `TauCeti.notMem_range_inclusion_Ioc_Icc_iff`, `TauCeti.notMem_range_inclusion_Ioo_Ioc_iff`,
  `TauCeti.isOpenEmbedding_inclusion_Ioc_Icc`, `TauCeti.isOpenEmbedding_inclusion_Ioo_Ioc`,
  `TauCeti.eq_of_zero_of_inclusion_Ioc_Icc`, and `TauCeti.eq_of_iocOne_of_inclusion_Ioo_Ioc`:
  endpoint `1` of `(0, 1]`, open embeddings, complement characterizations, and extensionality for
  the canonical `Set.inclusion` maps `(0, 1) ↪ (0, 1] ↪ [0, 1]`.

## Main declarations

* `TauCeti.sub_div_sub_mem_unitInterval`: the normalized height `(r - a) / (b - a)` of `r ∈ [a, b]`
  lies in `unitInterval`, including when `a = b`.
* `TauCeti.tent`: the tent map `t ↦ min (2 t) (2 - 2 t)` on the unit interval.
* `TauCeti.coe_tent`, `TauCeti.continuous_tent`, `TauCeti.tent_zero`, `TauCeti.tent_one`: the
  coercion formula, continuity, and vanishing at `0` and `1` of `TauCeti.tent`.
* `TauCeti.iocOne`, `TauCeti.inclusion_Ioc_Icc_iocOne`,
  `TauCeti.notMem_range_inclusion_Ioc_Icc_iff`, `TauCeti.notMem_range_inclusion_Ioo_Ioc_iff`,
  `TauCeti.isOpenEmbedding_inclusion_Ioc_Icc`, `TauCeti.isOpenEmbedding_inclusion_Ioo_Ioc`,
  `TauCeti.eq_of_zero_of_inclusion_Ioc_Icc`, `TauCeti.eq_of_iocOne_of_inclusion_Ioo_Ioc`: endpoint
  `1` of `(0, 1]`, open embeddings, complement characterizations, and extensionality for
  `Set.inclusion Ioc_subset_Icc_self` and `Set.inclusion Ioo_subset_Ioc_self`.
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

/-- The endpoint `1` of `Set.Ioc (0 : ℝ) 1`. -/
def iocOne : Ioc (0 : ℝ) 1 := ⟨1, right_mem_Ioc.mpr zero_lt_one⟩

@[simp]
theorem coe_iocOne : (iocOne : ℝ) = 1 := (rfl)

@[simp]
theorem inclusion_Ioc_Icc_iocOne : Set.inclusion Ioc_subset_Icc_self iocOne = (1 : I) :=
  Subtype.ext (by simp)

/-- The canonical inclusion `(0, 1] → [0, 1]` omits only `0`. -/
theorem notMem_range_inclusion_Ioc_Icc_iff (t : I) :
    t ∉ range (Set.inclusion Ioc_subset_Icc_self) ↔ t = 0 := by
  simp only [Set.range_inclusion, mem_ofPred_eq, mem_Ioc, t.property.2, and_true, not_lt]
  exact ⟨fun h => Subtype.ext (le_antisymm h t.property.1), fun h => h ▸ le_rfl⟩

/-- The canonical inclusion `(0, 1) → (0, 1]` omits only `iocOne`. -/
theorem notMem_range_inclusion_Ioo_Ioc_iff (t : Ioc (0 : ℝ) 1) :
    t ∉ range (Set.inclusion Ioo_subset_Ioc_self) ↔ t = iocOne := by
  simp only [Set.range_inclusion, mem_ofPred_eq, mem_Ioo, t.property.1, true_and, not_lt]
  exact ⟨fun h => Subtype.ext (le_antisymm t.property.2 h), fun h => h ▸ le_rfl⟩

/-- The canonical inclusion `(0, 1] → [0, 1]` is an open embedding. -/
theorem isOpenEmbedding_inclusion_Ioc_Icc :
    IsOpenEmbedding (Set.inclusion (Ioc_subset_Icc_self : Ioc (0 : ℝ) 1 ⊆ I)) :=
  Topology.IsOpenEmbedding.inclusion Ioc_subset_Icc_self <| by
    convert (isOpen_Ioi : IsOpen (Ioi (0 : ℝ))).preimage continuous_subtypeVal using 1
    ext x
    exact and_iff_left x.property.2

/-- The canonical inclusion `(0, 1) → (0, 1]` is an open embedding. -/
theorem isOpenEmbedding_inclusion_Ioo_Ioc :
    IsOpenEmbedding (Set.inclusion (Ioo_subset_Ioc_self : Ioo (0 : ℝ) 1 ⊆ Ioc 0 1)) :=
  Topology.IsOpenEmbedding.inclusion Ioo_subset_Ioc_self <| by
    convert (isOpen_Iio : IsOpen (Iio (1 : ℝ))).preimage continuous_subtypeVal using 1
    ext x
    exact and_iff_right x.property.1

/-- Two functions on `[0, 1]` agreeing at `0` and on `(0, 1]` are equal. -/
theorem eq_of_zero_of_inclusion_Ioc_Icc {β : Type*} {g₁ g₂ : I → β}
    (h0 : g₁ 0 = g₂ 0)
    (h : ∀ x : Ioc (0 : ℝ) 1,
      g₁ (Set.inclusion Ioc_subset_Icc_self x) = g₂ (Set.inclusion Ioc_subset_Icc_self x)) :
    g₁ = g₂ :=
  Function.eq_of_comp_eq_of_eqOn_compl (Set.inclusion Ioc_subset_Icc_self) (funext h)
    fun t ht => by rw [(notMem_range_inclusion_Ioc_Icc_iff t).mp ht]; exact h0

/-- Two functions on `(0, 1]` agreeing at `1` and on `(0, 1)` are equal. -/
theorem eq_of_iocOne_of_inclusion_Ioo_Ioc {β : Type*} {g₁ g₂ : Ioc (0 : ℝ) 1 → β}
    (h1 : g₁ iocOne = g₂ iocOne)
    (h : ∀ x : Ioo (0 : ℝ) 1,
      g₁ (Set.inclusion Ioo_subset_Ioc_self x) = g₂ (Set.inclusion Ioo_subset_Ioc_self x)) :
    g₁ = g₂ :=
  Function.eq_of_comp_eq_of_eqOn_compl (Set.inclusion Ioo_subset_Ioc_self) (funext h)
    fun t ht => by rw [(notMem_range_inclusion_Ioo_Ioc_iff t).mp ht]; exact h1

end TauCeti
