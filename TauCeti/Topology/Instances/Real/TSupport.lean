/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.MetricSpace.ProperSpace.Lemmas
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Topology.Algebra.Support

/-!
# Supports inside an open interval and a strip

A function on `ℝ` whose topological support is contained in `(0, R)` has its support inside
`(0, R')` for some `R' < R`: the support is closed and the interval is a ball in a proper space.

A function on a strip `ℝ × X` vanishing whenever the first coordinate lies outside `(a, b)` has
its topological support in the closed strip `[a, b] × X`, so it vanishes near every point outside
that strip.

A function whose positive closed support `tsupport f ∩ Ioi 0` is compact has that support inside
an interval `[a, b]` with `0 < a`, and the reflection `y ↦ f y⁻¹` again has compact positive
closed support. Such a function vanishes eventually at `∞` and on a right neighbourhood of `0`.

## Main results

* `TauCeti.exists_lt_tsupport_subset_Ioo`: the support shrinks to `(0, R')` with `R' < R`.
* `TauCeti.eventuallyEq_zero_of_forall_notMem_Ioo_of_fst_notMem_Icc`: a function on `ℝ × X`
  vanishing for `s ∉ (a, b)` vanishes near every point whose first coordinate is outside `[a, b]`.
* `IsCompact.exists_pos_tsupport_inter_Ioi_subset_Icc`: a compact positive closed support lies in
  some `[a, b]` with `0 < a`.
* `IsCompact.eventuallyEq_zero_atTop_of_tsupport_inter_Ioi`,
  `IsCompact.eventuallyEq_zero_nhdsGT_of_tsupport_inter_Ioi`: such a function vanishes
  eventually at `∞` and on a right neighbourhood of `0`.
* `IsCompact.tsupport_comp_inv_inter_Ioi`: reflecting by `y ↦ y⁻¹` preserves compactness
  of the positive closed support.
-/

public section

namespace TauCeti

open Metric Set
open scoped Topology

variable {R : ℝ} {F : Type*} [Zero F]

/-- A test function `ψ` supported in `(0, R)` is supported in some `(0, R')` with `R' < R`. -/
lemma exists_lt_tsupport_subset_Ioo (hR : 0 < R) {ψ : ℝ → F}
    (hψs : tsupport ψ ⊆ Ioo 0 R) : ∃ R', 0 < R' ∧ R' < R ∧ tsupport ψ ⊆ Ioo 0 R' := by
  have hball : Ioo (0 : ℝ) R = ball (R / 2) (R / 2) := by
    rw [Real.ball_eq_Ioo]
    congr 1 <;> ring
  obtain ⟨r, hr, hψr⟩ :=
    exists_pos_lt_subset_ball (half_pos hR) (isClosed_tsupport ψ) (hball ▸ hψs)
  rw [Real.ball_eq_Ioo] at hψr
  exact ⟨R / 2 + r, by linarith [hr.1], by linarith [hr.2],
    hψr.trans (Ioo_subset_Ioo (by linarith [hr.2]) le_rfl)⟩

/-- A function on `ℝ × X` vanishing for `s ∉ (a, b)` vanishes near every point with `s ∉ [a, b]`,
outside the closed strip `[a, b] × X` containing its support. -/
theorem eventuallyEq_zero_of_forall_notMem_Ioo_of_fst_notMem_Icc {X : Type*} [TopologicalSpace X]
    {f : ℝ × X → F} {a b : ℝ} (hf : ∀ s x, s ∉ Ioo a b → f (s, x) = 0) {z : ℝ × X}
    (hz : z.1 ∉ Icc a b) : f =ᶠ[𝓝 z] 0 :=
  notMem_tsupport_iff_eventuallyEq.1 fun h ↦ hz <|
    closure_minimal (t := Prod.fst ⁻¹' Icc a b) (Function.support_subset_iff'.2 fun w hw ↦
      hf w.1 w.2 fun h ↦ hw (Ioo_subset_Icc_self h)) (isClosed_Icc.preimage continuous_fst) h

/-- A compact positive closed support `tsupport f ∩ Ioi 0` lies in an interval `[a, b]` with
`0 < a`. -/
theorem _root_.IsCompact.exists_pos_tsupport_inter_Ioi_subset_Icc {f : ℝ → F}
    (hc : IsCompact (tsupport f ∩ Ioi 0)) : ∃ a b : ℝ, 0 < a ∧ tsupport f ∩ Ioi 0 ⊆ Icc a b := by
  rcases (tsupport f ∩ Ioi 0).eq_empty_or_nonempty with he | hne
  · exact ⟨1, 0, one_pos, he ▸ empty_subset _⟩
  · obtain ⟨a, ⟨-, ha⟩, hmin⟩ := hc.exists_isLeast hne
    obtain ⟨b, hb⟩ := hc.bddAbove
    exact ⟨a, b, ha, fun t ht ↦ ⟨hmin ht, hb ht⟩⟩

/-- A function with compact positive closed support vanishes eventually at `∞`. -/
theorem _root_.IsCompact.eventuallyEq_zero_atTop_of_tsupport_inter_Ioi {f : ℝ → F}
    (hc : IsCompact (tsupport f ∩ Ioi 0)) : f =ᶠ[Filter.atTop] 0 := by
  obtain ⟨a, b, -, hab⟩ := hc.exists_pos_tsupport_inter_Ioi_subset_Icc
  filter_upwards [Filter.eventually_gt_atTop (max b 0)] with t ht
  refine image_eq_zero_of_notMem_tsupport fun h ↦ ?_
  exact (lt_of_le_of_lt (le_max_left b 0) ht).not_ge
    (hab ⟨h, lt_of_le_of_lt (le_max_right b 0) ht⟩).2

/-- A function with compact positive closed support vanishes on a right neighbourhood of `0`. -/
theorem _root_.IsCompact.eventuallyEq_zero_nhdsGT_of_tsupport_inter_Ioi {f : ℝ → F}
    (hc : IsCompact (tsupport f ∩ Ioi 0)) : f =ᶠ[𝓝[>] 0] 0 := by
  obtain ⟨a, b, ha, hab⟩ := hc.exists_pos_tsupport_inter_Ioi_subset_Icc
  filter_upwards [Ioo_mem_nhdsGT ha] with t ht
  exact image_eq_zero_of_notMem_tsupport fun h ↦ ht.2.not_ge (hab ⟨h, ht.1⟩).1

/-- Reflecting a function by `y ↦ y⁻¹` preserves compactness of its positive closed support. -/
theorem _root_.IsCompact.tsupport_comp_inv_inter_Ioi {f : ℝ → F}
    (hc : IsCompact (tsupport f ∩ Ioi 0)) : IsCompact (tsupport (fun y ↦ f y⁻¹) ∩ Ioi 0) := by
  set K : Set ℝ := Inv.inv '' (tsupport f ∩ Ioi 0)
  have hK : IsCompact K :=
    hc.image_of_continuousOn (continuousOn_inv₀.mono fun y hy ↦ ne_of_gt hy.2)
  have hKpos : K ⊆ Ioi 0 := by
    rintro _ ⟨y, ⟨-, hy⟩, rfl⟩
    exact inv_pos.mpr hy
  have hsupp : tsupport (fun y ↦ f y⁻¹) ⊆ K ∪ Iic 0 := by
    refine closure_minimal (fun y hy ↦ ?_) (hK.isClosed.union isClosed_Iic)
    rcases le_or_gt y 0 with h | h
    · exact Or.inr h
    · exact Or.inl ⟨y⁻¹, ⟨subset_tsupport f hy, inv_pos.mpr h⟩, inv_inv y⟩
  have heq : tsupport (fun y ↦ f y⁻¹) ∩ Ioi 0 = tsupport (fun y ↦ f y⁻¹) ∩ K := by
    ext y
    refine ⟨fun hy ↦ ⟨hy.1, ?_⟩, fun hy ↦ ⟨hy.1, hKpos hy.2⟩⟩
    rcases hsupp hy.1 with h | h
    · exact h
    · exact absurd h (not_le.mpr hy.2)
  rw [heq]
  exact hK.inter_left (isClosed_tsupport _)

end TauCeti
