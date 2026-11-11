/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.Filter.AtTopBot.Archimedean
public import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Order.Filter.AtTopBot.Field
import Mathlib.Topology.Algebra.Module.Cardinality

/-!
# Grids separating a finite set of reals

A finite set `C` of real numbers can be separated by a bi-infinite arithmetic progression
`a q = t + q h`, `q ∈ ℤ`: choose the step `h` smaller than the distance between any two points
of `C`, so that each closed interval `[a q, a (q + 1)]` contains at most one point of `C`, and
choose the offset `t` outside the countable set `C - hℤ`, so that no grid point lies in `C`
(`Set.Finite.exists_strictMono_notMem_subsingleton_inter_Icc`).

For the critical values of a function this is a sequence of regular values whose consecutive
bands each contain at most one critical value; the sublevels at these values filter the space by
its critical levels.
-/

public section

open Filter Set Topology

/-- **A grid separating a finite set of reals.** For a finite set `C ⊆ ℝ` there is a strictly
increasing sequence `a : ℤ → ℝ`, tending to `-∞` and to `∞`, which avoids `C` and whose
consecutive closed intervals `[a q, a (q + 1)]` each contain at most one point of `C`. -/
theorem Set.Finite.exists_strictMono_notMem_subsingleton_inter_Icc {C : Set ℝ} (hC : C.Finite) :
    ∃ a : ℤ → ℝ, StrictMono a ∧ Tendsto a atBot atBot ∧ Tendsto a atTop atTop ∧
      (∀ q, a q ∉ C) ∧ ∀ q, (C ∩ Icc (a q) (a (q + 1))).Subsingleton := by
  -- A step `h` smaller than the distance between any two distinct points of `C`.
  obtain ⟨h, hsep, hh⟩ : ∃ h : ℝ, (∀ c ∈ C, ∀ c' ∈ C, c ≠ c' → h < |c - c'|) ∧ 0 < h := by
    have : ∀ᶠ h in 𝓝[>] (0 : ℝ), ∀ c ∈ C, ∀ c' ∈ C, c ≠ c' → h < |c - c'| := by
      refine (eventually_all_finite hC).2 fun c _ ↦ (eventually_all_finite hC).2 fun c' _ ↦ ?_
      by_cases hcc : c = c'
      · exact Eventually.of_forall fun _ hne ↦ absurd hcc hne
      · filter_upwards [nhdsWithin_le_nhds
          (eventually_lt_nhds (abs_pos.2 (sub_ne_zero.2 hcc)))] with _ hlt _ using hlt
    exact (this.and self_mem_nhdsWithin).exists
  -- The offsets `t` for which the grid `t + q h` meets `C` form a countable set.
  have hbad : (⋃ c ∈ C, range fun q : ℤ ↦ c - q * h).Countable :=
    hC.countable.biUnion fun _ _ ↦ countable_range _
  obtain ⟨t, ht⟩ := (hbad.dense_compl ℝ).nonempty
  refine ⟨fun q ↦ t + q * h, fun q q' hqq' ↦ ?_, ?_, ?_, fun q hq ↦ ?_, fun q ↦ ?_⟩
  · have : (q : ℝ) < q' := Int.cast_lt.2 hqq'
    dsimp only
    nlinarith
  · exact tendsto_atBot_add_const_left _ t
      ((tendsto_intCast_atBot_iff.2 tendsto_id).atBot_mul_const hh)
  · exact tendsto_atTop_add_const_left _ t (tendsto_intCast_atTop_atTop.atTop_mul_const hh)
  · exact ht (mem_biUnion hq ⟨q, by ring⟩)
  · rintro x ⟨hx, hx₁, hx₂⟩ y ⟨hy, hy₁, hy₂⟩
    by_contra hxy
    push_cast at hx₂ hy₂
    have := hsep x hx y hy hxy
    have : |x - y| ≤ h := abs_sub_le_iff.2 ⟨by linarith, by linarith⟩
    linarith
