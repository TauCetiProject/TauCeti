/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.RealAlgebraic.Stack.Basic
import Mathlib.Data.Fintype.Fin

/-!
# Root-count characterizations of stack cells

For a strictly ordered finite stack, a point is on section `i` exactly when its height is
one of the section values and exactly `i` section values are below it. It is in sector `j`
exactly when its height is not a section value and exactly `j` section values are below it.
These descriptions identify stack cells with uniform polynomial shared-root formulas.
The order-theoretic statements allow any linearly ordered height type and include the empty
stack and both unbounded sectors.
-/

public section

namespace TauCeti

variable {X α : Type*} [LinearOrder α] {k : ℕ} {θ : Fin k → X → α}

/-- A section is characterized by membership in the finite set of section heights and the
number of section heights strictly below the point. Indices are counted from zero. -/
theorem mem_sectionSet_iff_mem_image_card_lt
    (i : Fin k) (z : X × α) (hθ : StrictMono fun l ↦ θ l z.1) :
    z ∈ sectionSet θ i ↔
      z.2 ∈ Finset.univ.image (fun l ↦ θ l z.1) ∧
        ((Finset.univ.image (fun l ↦ θ l z.1)).filter (· < z.2)).card = i.val := by
  classical
  have hcard (l : Fin k) :
      ((Finset.univ.image (fun m ↦ θ m z.1)).filter (· < θ l z.1)).card = l.val := by
    rw [Finset.filter_image, Finset.card_image_of_injective _ hθ.injective]
    simp only [hθ.lt_iff_lt]
    simpa only [Finset.filter_gt_eq_Iio] using Fin.card_Iio l
  simp only [mem_sectionSet]
  constructor
  · intro hi
    rw [← hi]
    exact ⟨Finset.mem_image_of_mem _ (Finset.mem_univ i), hcard i⟩
  · rintro ⟨ht, hc⟩
    obtain ⟨l, _, hl⟩ := Finset.mem_image.1 ht
    have hli : l = i := Fin.ext ((hcard l).symm.trans (hl ▸ hc))
    simpa only [hli] using hl

/-- A sector is characterized by avoiding the finite set of section heights and the
number of section heights strictly below the point. This includes the empty stack. -/
theorem mem_sectorSet_iff_notMem_image_card_lt
    (j : Fin (k + 1)) (z : X × α) (hθ : StrictMono fun l ↦ θ l z.1) :
    z ∈ sectorSet θ j ↔
      z.2 ∉ Finset.univ.image (fun l ↦ θ l z.1) ∧
        ((Finset.univ.image (fun l ↦ θ l z.1)).filter (· < z.2)).card = j.val := by
  classical
  have hcard : ((Finset.univ.image (fun l ↦ θ l z.1)).filter (· < z.2)).card =
      (Finset.univ.filter fun l ↦ θ l z.1 < z.2).card := by
    rw [Finset.filter_image, Finset.card_image_of_injective _ hθ.injective]
  rw [hcard, mem_sectorSet]
  constructor
  · rintro ⟨hlo, hhi⟩
    have hlt (i : Fin k) : θ i z.1 < z.2 ↔ i.val < j.val := by
      constructor
      · intro h
        by_contra! h'
        exact (hhi i h').not_gt h
      · exact hlo i
    refine ⟨?_, ?_⟩
    · simp only [Finset.mem_image, Finset.mem_univ, true_and, not_exists]
      intro i hi
      rcases lt_or_ge i.castSucc j with hij | hij
      · exact (hlo i hij).ne hi
      · exact (hhi i hij).ne hi.symm
    · simp only [hlt, Fin.card_filter_val_lt, Nat.min_eq_right (Nat.le_of_lt_succ j.isLt)]
  · rintro ⟨hne, hc⟩
    have hlt (i : Fin k) : θ i z.1 < z.2 ↔ i.val < j.val := by
      rw [← hc]
      exact (Fin.lt_card_filter_univ_iff_apply_of_imp (fun l ↦ θ l z.1 < z.2)
        (fun l m hml hl ↦ (hθ.monotone hml).trans_lt hl)).symm
    refine ⟨fun i hi ↦ (hlt i).2 hi, fun i hi ↦ ?_⟩
    have hni : θ i z.1 ≠ z.2 := by
      intro h
      apply hne
      rw [← h]
      exact Finset.mem_image_of_mem _ (Finset.mem_univ i)
    exact lt_of_le_of_ne (le_of_not_gt fun h ↦ hi.not_gt ((hlt i).1 h)) hni.symm

end TauCeti
