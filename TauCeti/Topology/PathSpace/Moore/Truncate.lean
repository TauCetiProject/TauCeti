/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.PathSpace.Moore

/-!
# Truncating and dropping the start of Moore paths

For a Moore path `γ` and a time `s`, the **truncation** `γ.truncate s` is the initial piece of `γ`
up to time `s`: it has length `min s γ.length` and is stopped from time `s` on.  The **drop**
`γ.drop s` is the remaining piece, `t ↦ γ (s + t)`, of length `γ.length - s`.  The two pieces
concatenate back to `γ` (`MoorePath.truncate_trans_drop`), with no reparametrization, and both
depend continuously on the path and the time (`Continuous.moorePath_truncate`,
`Continuous.moorePath_drop`).

These are the pieces from which the lifting function of a Moore-path replacement and the
shrinking homotopies of the fibre are built.

## Main definitions

* `TauCeti.MoorePath.truncate γ s`: the initial piece of `γ` up to time `s`.
* `TauCeti.MoorePath.drop γ s`: the piece of `γ` from time `s` on.

## Main results

* `TauCeti.MoorePath.truncate_trans_drop`: `γ.truncate s` followed by `γ.drop s` is `γ`.
* `TauCeti.MoorePath.truncate_trans_of_le`, `TauCeti.MoorePath.truncate_trans_length_add`: the
  truncations of a concatenation.
-/

public section

open scoped NNReal

namespace TauCeti

namespace MoorePath

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-! ### Truncation -/

/-- The **truncation** of a Moore path at time `s`: the path `t ↦ γ (min t s)`, of length
`min s γ.length`. -/
def truncate (γ : MoorePath X) (s : ℝ≥0) : MoorePath X where
  toFun t := γ (min t s)
  continuous_toFun := γ.continuous.comp (continuous_id.min continuous_const)
  length := min s γ.length
  apply_of_length_le' t ht := by
    rcases le_total s γ.length with hs | hs
    · rw [min_eq_left hs] at ht ⊢
      rw [min_eq_right ht, min_self]
    · rw [min_eq_right hs] at ht ⊢
      rw [γ.apply_of_length_le (le_min ht hs), min_eq_left hs, target_def]

@[simp]
theorem truncate_apply (γ : MoorePath X) (s t : ℝ≥0) : γ.truncate s t = γ (min t s) :=
  (rfl)

@[simp]
theorem length_truncate (γ : MoorePath X) (s : ℝ≥0) : (γ.truncate s).length = min s γ.length :=
  (rfl)

@[simp]
theorem source_truncate (γ : MoorePath X) (s : ℝ≥0) : (γ.truncate s).source = γ.source := by
  rw [source_def, truncate_apply, min_eq_left zero_le, source_def]

@[simp]
theorem target_truncate (γ : MoorePath X) (s : ℝ≥0) : (γ.truncate s).target = γ s := by
  rw [target_def, truncate_apply, length_truncate, min_eq_left (min_le_left _ _), apply_min_length]

@[simp]
theorem truncate_zero (γ : MoorePath X) : γ.truncate 0 = refl γ.source :=
  ext (by simp) fun t ↦ by rw [truncate_apply, min_eq_right zero_le, refl_apply, source_def]

/-- Truncating a Moore path at a time after its length changes nothing. -/
theorem truncate_of_length_le (γ : MoorePath X) {s : ℝ≥0} (hs : γ.length ≤ s) :
    γ.truncate s = γ := by
  refine ext (min_eq_right hs) fun t ↦ ?_
  rw [truncate_apply]
  rcases le_total t s with ht | ht
  · rw [min_eq_left ht]
  · rw [min_eq_right ht, γ.apply_of_length_le hs, γ.apply_of_length_le (hs.trans ht)]

@[simp]
theorem truncate_length (γ : MoorePath X) : γ.truncate γ.length = γ :=
  γ.truncate_of_length_le le_rfl

@[simp]
theorem map_truncate (f : C(X, Y)) (γ : MoorePath X) (s : ℝ≥0) :
    (γ.truncate s).map f = (γ.map f).truncate s :=
  ext (by simp) fun _ ↦ by simp

/-- Truncations form a continuous family in the path and the time. -/
@[fun_prop]
theorem _root_.Continuous.moorePath_truncate {f : Y → MoorePath X} {g : Y → ℝ≥0}
    (hf : Continuous f) (hg : Continuous g) : Continuous fun y ↦ (f y).truncate (g y) := by
  refine continuous_iff.2 ⟨by simp only [length_truncate]; fun_prop, ?_⟩
  simp only [truncate_apply]
  fun_prop

/-- Truncating a concatenation before the end of its first piece truncates the first piece. -/
theorem truncate_trans_of_le (γ δ : MoorePath X) (h : γ.target = δ.source) {s : ℝ≥0}
    (hs : s ≤ γ.length) : (γ.trans δ h).truncate s = γ.truncate s := by
  refine ext (by simp [min_eq_left hs, min_eq_left (hs.trans le_self_add)]) fun t ↦ ?_
  rw [truncate_apply, truncate_apply, trans_apply_of_le _ _ _ ((min_le_right _ _).trans hs)]

/-- Truncating a concatenation after the end of its first piece concatenates the first piece with
a truncation of the second. -/
theorem truncate_trans_length_add (γ δ : MoorePath X) (h : γ.target = δ.source) (u : ℝ≥0) :
    (γ.trans δ h).truncate (γ.length + u) =
      γ.trans (δ.truncate u) (by rw [source_truncate, h]) := by
  refine ext (by simp [min_add_add_left]) fun t ↦ ?_
  rw [truncate_apply]
  rcases le_total t γ.length with ht | ht
  · rw [min_eq_left (ht.trans le_self_add), trans_apply_of_le _ _ _ ht,
      trans_apply_of_le _ _ _ ht]
  · obtain ⟨v, rfl⟩ := exists_add_of_le ht
    rw [min_add_add_left, trans_apply_length_add, trans_apply_length_add, truncate_apply]

/-! ### Dropping an initial piece -/

/-- The Moore path `γ` from time `s` on: the path `t ↦ γ (s + t)`, of length `γ.length - s`. -/
def drop (γ : MoorePath X) (s : ℝ≥0) : MoorePath X where
  toFun t := γ (s + t)
  continuous_toFun := γ.continuous.comp (continuous_const.add continuous_id)
  length := γ.length - s
  apply_of_length_le' t ht := by
    have h₁ : γ.length ≤ s + t := by
      rw [add_comm]; exact tsub_le_iff_right.1 ht
    have h₂ : γ.length ≤ s + (γ.length - s) := le_add_tsub
    rw [γ.apply_of_length_le h₁, γ.apply_of_length_le h₂]

@[simp]
theorem drop_apply (γ : MoorePath X) (s t : ℝ≥0) : γ.drop s t = γ (s + t) :=
  (rfl)

@[simp]
theorem length_drop (γ : MoorePath X) (s : ℝ≥0) : (γ.drop s).length = γ.length - s :=
  (rfl)

@[simp]
theorem source_drop (γ : MoorePath X) (s : ℝ≥0) : (γ.drop s).source = γ s := by
  rw [source_def, drop_apply, add_zero]

@[simp]
theorem target_drop (γ : MoorePath X) (s : ℝ≥0) : (γ.drop s).target = γ.target := by
  rw [target_def, drop_apply, length_drop, γ.apply_of_length_le le_add_tsub]

@[simp]
theorem drop_zero (γ : MoorePath X) : γ.drop 0 = γ :=
  ext (tsub_zero _) fun t ↦ by rw [drop_apply, zero_add]

/-- Dropping a Moore path from a time after its length leaves the constant path at its target. -/
theorem drop_of_length_le (γ : MoorePath X) {s : ℝ≥0} (hs : γ.length ≤ s) :
    γ.drop s = refl γ.target :=
  ext (by simp [tsub_eq_zero_of_le hs]) fun t ↦ by
    rw [drop_apply, refl_apply, γ.apply_of_length_le (hs.trans le_self_add)]

@[simp]
theorem drop_length (γ : MoorePath X) : γ.drop γ.length = refl γ.target :=
  γ.drop_of_length_le le_rfl

@[simp]
theorem map_drop (f : C(X, Y)) (γ : MoorePath X) (s : ℝ≥0) :
    (γ.drop s).map f = (γ.map f).drop s :=
  ext (by simp) fun _ ↦ by simp

/-- The pieces of a Moore path form a continuous family in the path and the time. -/
@[fun_prop]
theorem _root_.Continuous.moorePath_drop {f : Y → MoorePath X} {g : Y → ℝ≥0}
    (hf : Continuous f) (hg : Continuous g) : Continuous fun y ↦ (f y).drop (g y) := by
  refine continuous_iff.2 ⟨by simp only [length_drop]; fun_prop, ?_⟩
  simp only [drop_apply]
  fun_prop

/-- A Moore path is the concatenation of its truncation at `s` with its piece from `s` on. -/
theorem truncate_trans_drop (γ : MoorePath X) (s : ℝ≥0) :
    (γ.truncate s).trans (γ.drop s) (by rw [target_truncate, source_drop]) = γ := by
  refine ext ?_ fun t ↦ ?_
  · rw [length_trans, length_truncate, length_drop]
    rcases le_total s γ.length with hs | hs
    · rw [min_eq_left hs, add_tsub_cancel_of_le hs]
    · rw [min_eq_right hs, tsub_eq_zero_of_le hs, add_zero]
  rcases le_total t (min s γ.length) with ht | ht
  · rw [trans_apply_of_le _ _ _ ht, truncate_apply, min_eq_left (ht.trans (min_le_left _ _))]
  · rw [trans_apply_of_length_le _ _ _ ht, drop_apply, length_truncate]
    rcases le_total s γ.length with hs | hs
    · rw [min_eq_left hs] at ht ⊢
      rw [add_tsub_cancel_of_le ht]
    · rw [min_eq_right hs] at ht ⊢
      rw [γ.apply_of_length_le (hs.trans le_self_add), γ.apply_of_length_le ht]

end MoorePath

end TauCeti
