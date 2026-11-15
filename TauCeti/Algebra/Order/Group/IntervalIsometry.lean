/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Group.Pointwise.Interval

/-!
# Isometric maps of an interval into a linearly ordered group

Let `Λ` be a linearly ordered additive group, with the distance `|s - t|`. A map `h : Λ → Λ`
preserving this distance on an interval `[0, E]` is a translation or a reflection there: either
`h s = h 0 + s` for every `s ∈ [0, E]`, or `h s = h 0 - s` for every `s ∈ [0, E]`. In particular
the image of `[0, E]` is the unordered interval `[[h 0, h E]]`.

These facts identify the segments of `Λ`, viewed as a `Λ`-metric space, with its closed intervals.

## Main results

* `TauCeti.eq_add_or_eq_sub_of_abs_sub_eq`: an isometric map of `[0, E]` into `Λ` is a translation
  or a reflection.
* `TauCeti.image_Icc_eq_uIcc_of_abs_sub_eq`: the image of `[0, E]` under such a map is
  `[[h 0, h E]]`.
-/

public section

namespace TauCeti

open Set

variable {Λ : Type*} [AddCommGroup Λ] [LinearOrder Λ] [IsOrderedAddMonoid Λ]

/-- A map preserving the distance `|s - t|` on `[0, E]` is, on `[0, E]`, either the translation
`s ↦ h 0 + s` or the reflection `s ↦ h 0 - s`. -/
theorem eq_add_or_eq_sub_of_abs_sub_eq {h : Λ → Λ} {E : Λ}
    (hh : ∀ s ∈ Icc 0 E, ∀ t ∈ Icc 0 E, |h s - h t| = |s - t|) :
    (∀ s ∈ Icc 0 E, h s = h 0 + s) ∨ ∀ s ∈ Icc 0 E, h s = h 0 - s := by
  by_cases hE : 0 ≤ E
  · have h0 : (0 : Λ) ∈ Icc 0 E := ⟨le_rfl, hE⟩
    have hE' : E ∈ Icc 0 E := ⟨hE, le_rfl⟩
    -- `s` is at distance `s` from `0` and `E - s` from `E`, which pins `h s` down once the
    -- direction `h E - h 0 = ± E` is known.
    have key : ∀ s ∈ Icc 0 E, |h s - h 0| = s ∧ |h E - h s| = E - s := fun s hs => by
      rw [hh s hs 0 h0, hh E hE' s hs, sub_zero, abs_of_nonneg hs.1,
        abs_of_nonneg (sub_nonneg.2 hs.2)]
      exact ⟨rfl, rfl⟩
    have hEE := (key E hE').1
    rcases le_total 0 (h E - h 0) with hpos | hneg
    · refine .inl fun s hs => ?_
      have := key s hs
      rw [abs_of_nonneg hpos] at hEE
      grind [le_abs_self]
    · refine .inr fun s hs => ?_
      have := key s hs
      rw [abs_of_nonpos hneg] at hEE
      grind [neg_abs_le]
  · refine .inl fun s hs => absurd (hs.1.trans hs.2) hE

/-- The image of `[0, E]` under a map preserving the distance `|s - t|` on it is the unordered
interval between the images of the endpoints. -/
theorem image_Icc_eq_uIcc_of_abs_sub_eq {h : Λ → Λ} {E : Λ} (hE : 0 ≤ E)
    (hh : ∀ s ∈ Icc 0 E, ∀ t ∈ Icc 0 E, |h s - h t| = |s - t|) :
    h '' Icc 0 E = uIcc (h 0) (h E) := by
  rcases eq_add_or_eq_sub_of_abs_sub_eq hh with hadd | hsub
  · rw [image_congr hadd, image_const_add_Icc, add_zero, hadd E ⟨hE, le_rfl⟩,
      uIcc_of_le (le_add_of_nonneg_right hE)]
  · rw [image_congr hsub, image_const_sub_Icc, sub_zero, hsub E ⟨hE, le_rfl⟩,
      uIcc_of_ge (sub_le_self _ hE)]

end TauCeti
