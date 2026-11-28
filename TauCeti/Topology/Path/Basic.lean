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
* `Path.firstHalf`, `Path.secondHalf`: the two halves of a path, cut at its midpoint, with
  `Path.firstHalf_trans_secondHalf`: their concatenation is the path itself.
* `Path.exists_last_mem_of_isClosed`: if a path meets a closed set, there is a last parameter in
  that set and every later parameter avoids it.
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

section Halves

variable {a b m : X}

/-- The first half of a path `γ`, ending at its midpoint `m`: at time `t` it is `γ (t / 2)`. Unlike
`Path.subpath`, it has the prescribed endpoint `m`, and it concatenates with `Path.secondHalf` to
`γ` itself rather than to a path homotopic to `γ`. -/
noncomputable def firstHalf (γ : Path a b) (hm : γ ⟨1 / 2, by norm_num, by norm_num⟩ = m) :
    Path a m where
  toFun t := γ ⟨(t : ℝ) / 2, by have := t.property.1; positivity,
    by have := t.property.2; linarith⟩
  continuous_toFun := γ.continuous.comp (by fun_prop)
  source' := by
    convert γ.source using 2
    ext
    simp
  target' := by
    convert hm using 2

/-- The second half of a path `γ`, starting at its midpoint `m`: at time `t` it is
`γ ((1 + t) / 2)`. -/
noncomputable def secondHalf (γ : Path a b) (hm : γ ⟨1 / 2, by norm_num, by norm_num⟩ = m) :
    Path m b where
  toFun t := γ ⟨(1 + (t : ℝ)) / 2, by have := t.property.1; positivity,
    by have := t.property.2; linarith⟩
  continuous_toFun := γ.continuous.comp (by fun_prop)
  source' := by
    convert hm using 2
    ext
    simp
  target' := by
    convert γ.target using 2
    ext
    norm_num

/-- The first half of `γ` at time `t` is `γ` at time `t / 2`. -/
@[simp]
theorem firstHalf_apply (γ : Path a b) (hm : γ ⟨1 / 2, by norm_num, by norm_num⟩ = m)
    (t : unitInterval) :
    γ.firstHalf hm t =
      γ ⟨(t : ℝ) / 2, by have := t.property.1; positivity, by have := t.property.2; linarith⟩ :=
  (rfl)

/-- The second half of `γ` at time `t` is `γ` at time `(1 + t) / 2`. -/
@[simp]
theorem secondHalf_apply (γ : Path a b) (hm : γ ⟨1 / 2, by norm_num, by norm_num⟩ = m)
    (t : unitInterval) :
    γ.secondHalf hm t =
      γ ⟨(1 + (t : ℝ)) / 2, by have := t.property.1; positivity,
        by have := t.property.2; linarith⟩ :=
  (rfl)

/-- A path is the concatenation of its two halves. -/
@[simp]
theorem firstHalf_trans_secondHalf (γ : Path a b)
    (hm : γ ⟨1 / 2, by norm_num, by norm_num⟩ = m) :
    (γ.firstHalf hm).trans (γ.secondHalf hm) = γ := by
  ext t
  rw [Path.trans_apply]
  split_ifs with h
  · rw [firstHalf_apply]
    congr 1
    ext
    simp only
    ring
  · rw [secondHalf_apply]
    congr 1
    ext
    simp only
    ring

end Halves

/-- If a path meets a closed set, there is a last parameter in that set and every later parameter
avoids it. -/
theorem exists_last_mem_of_isClosed (γ : Path x y) {s : Set X} (hs : IsClosed s)
    (hne : (range γ ∩ s).Nonempty) :
    ∃ t : unitInterval, γ t ∈ s ∧ ∀ r : unitInterval, t < r → γ r ∉ s := by
  have hcomp : IsCompact (γ ⁻¹' s) :=
    isCompact_univ.of_isClosed_subset (hs.preimage γ.continuous) (subset_univ _)
  have hne' : (γ ⁻¹' s).Nonempty := by
    obtain ⟨_, ⟨t, rfl⟩, hts⟩ := hne
    exact ⟨t, hts⟩
  obtain ⟨t, hts, htmax⟩ := hcomp.exists_isMaxOn hne' continuous_id.continuousOn
  exact ⟨t, hts, fun r hr hrs => not_le_of_gt hr (htmax hrs)⟩

end Path
