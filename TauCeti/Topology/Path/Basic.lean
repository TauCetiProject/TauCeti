/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Path
import TauCeti.Data.Set.Function

/-!
# Basic facts about paths

## Main declarations

* `Path.trans_mem_of_mem`: a concatenation of two paths lying in a set lies in that set.
* `Path.image_Ioo_eq_range_sdiff_endpoints`: an injective path carries `(0, 1)` onto its range
  minus its endpoints.
* `Path.injective_symm_iff`: reversing a path preserves injectivity.
* `Path.injective_trans`: concatenating two injective paths that meet only at their shared endpoint
  yields an injective path.
* `Path.injective_trans_trans`: concatenating three injective paths whose adjacent pairs meet only
  at their shared endpoints and whose outer ranges are disjoint yields an injective path.
-/

public section

open Function Set

namespace Path

variable {X : Type*} [TopologicalSpace X]

/-- A concatenation of two paths lying in a set lies in that set. -/
theorem trans_mem_of_mem {x y z : X} (P : Path x y) (Q : Path y z) {s : Set X}
    (hP : ∀ t, P t ∈ s) (hQ : ∀ t, Q t ∈ s) : ∀ t, P.trans Q t ∈ s :=
  range_subset_iff.1 <| (Path.trans_range _ _).trans_subset <|
    union_subset (range_subset_iff.2 hP) (range_subset_iff.2 hQ)

variable {x y : X}

/-- The image of the open unit interval `(0, 1)` under an injective path is its range minus its
endpoints. -/
theorem image_Ioo_eq_range_sdiff_endpoints {γ : Path x y} (hγ : Injective γ) :
    γ '' Ioo 0 1 = range γ \ {x, y} := by
  have h : (Ioo 0 1 : Set unitInterval) = univ \ {0, 1} := by
    rw [unitInterval.univ_eq_Icc, Set.Icc_sdiff_both]
  rw [h, Set.image_sdiff hγ]
  simp

/-- Reversing a path preserves injectivity. -/
@[simp]
theorem injective_symm_iff {γ : Path x y} : Injective γ.symm ↔ Injective γ := by
  have h : (γ.symm : unitInterval → X) = γ ∘ unitInterval.symmHomeomorph.toEquiv :=
    funext γ.symm_apply
  rw [h]
  exact unitInterval.symmHomeomorph.toEquiv.injective_comp γ

/-- Concatenating two injective paths whose ranges meet only at their shared endpoint gives an
injective path. -/
theorem injective_trans {z : X} {α : Path x y} {β : Path y z} (hα : Injective α)
    (hβ : Injective β) (hmeet : range α ∩ range β = {y}) : Injective (α.trans β) := by
  have hmeet' : range β ∩ range α ⊆ {y} := inter_comm _ _ ▸ hmeet.subset
  intro s t hst
  rw [Path.trans_apply, Path.trans_apply] at hst
  split_ifs at hst with hs ht ht
  · have h : (2 : ℝ) * s = 2 * t := congrArg Subtype.val (hα hst)
    exact Subtype.ext (by linarith)
  · have h2t : 2 * (t : ℝ) - 1 = 0 := congrArg Subtype.val
      (hβ.eq_of_apply_eq_of_range_inter_subset_singleton hmeet' β.source hst.symm)
    exact absurd (by linarith : (t : ℝ) ≤ 1 / 2) ht
  · have h2s : 2 * (s : ℝ) - 1 = 0 := congrArg Subtype.val
      (hβ.eq_of_apply_eq_of_range_inter_subset_singleton hmeet' β.source hst)
    exact absurd (by linarith : (s : ℝ) ≤ 1 / 2) hs
  · have h : 2 * (s : ℝ) - 1 = 2 * (t : ℝ) - 1 := congrArg Subtype.val (hβ hst)
    exact Subtype.ext (by linarith)

/-- Concatenating three injective paths whose adjacent pairs meet only at their shared endpoints
and whose outer ranges are disjoint yields an injective path. -/
theorem injective_trans_trans {a b c d : X} {α : Path a b} {β : Path b c} {γ : Path c d}
    (hα : Injective α) (hβ : Injective β) (hγ : Injective γ)
    (hαβ : range α ∩ range β = {b}) (hβγ : range β ∩ range γ = {c})
    (hαγ : Disjoint (range α) (range γ)) :
    Injective ((α.trans β).trans γ) := by
  refine injective_trans (injective_trans hα hβ hαβ) hγ ?_
  rwa [Path.trans_range, union_inter_distrib_right, hαγ.inter_eq, empty_union]

end Path
