/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Path

/-!
# Basic facts about paths

## Main declarations

* `Path.trans_mem_of_mem` -- a concatenation of two paths lying in a set lies in that set.
* `Path.firstHalf`, `Path.secondHalf` -- the two halves of a path, cut at its midpoint, with
  `Path.firstHalf_trans_secondHalf`: their concatenation is the path itself.
-/

public section

open Set

namespace Path

variable {X : Type*} [TopologicalSpace X]

/-- A concatenation of two paths lying in a set lies in that set. -/
theorem trans_mem_of_mem {x y z : X} (P : Path x y) (Q : Path y z) {s : Set X}
    (hP : ∀ t, P t ∈ s) (hQ : ∀ t, Q t ∈ s) : ∀ t, P.trans Q t ∈ s :=
  range_subset_iff.1 <| (Path.trans_range _ _).trans_subset <|
    union_subset (range_subset_iff.2 hP) (range_subset_iff.2 hQ)

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
theorem firstHalf_apply (γ : Path a b) (hm : γ ⟨1 / 2, by norm_num, by norm_num⟩ = m)
    (t : unitInterval) :
    γ.firstHalf hm t =
      γ ⟨(t : ℝ) / 2, by have := t.property.1; positivity, by have := t.property.2; linarith⟩ :=
  (rfl)

/-- The second half of `γ` at time `t` is `γ` at time `(1 + t) / 2`. -/
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

end Path
