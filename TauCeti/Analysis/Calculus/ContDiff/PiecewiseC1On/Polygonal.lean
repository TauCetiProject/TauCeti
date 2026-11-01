/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.ContDiff.PiecewiseC1On
public import TauCeti.MeasureTheory.Function.AbsolutelyContinuous.Gluing
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Polygonal curves are piecewise `C¹`

A polygonal curve (`TauCeti.IsPolygonalOnInterval`) is affine on each cell of a finite
subdivision of its parameter interval. Taking the interior subdivision points as breakpoints, it
is therefore piecewise `C¹`: every closed interval with no breakpoint in its interior lies in a
single cell, where the curve is affine.

## Main results

* `TauCeti.IsPolygonalOnInterval.isPiecewiseC1On`: a polygonal curve is piecewise `C¹`.
-/

public section

open Set

namespace TauCeti

/-- If `s` subdivides `[a, b]` and `c < d` are points of `[a, b]` such that no interior
subdivision point lies strictly between them, then `[c, d]` lies in a single cell of the
subdivision. -/
private theorem exists_Icc_subset_cell {N : ℕ} {s : Fin (N + 1) → ℝ} {a b c d : ℝ}
    (ha : s 0 = a) (hb : s (Fin.last N) = b) (hcd : c < d) (hac : a ≤ c) (hdb : d ≤ b)
    (hdisj : ∀ i, s i ∈ Ioo a b → s i ∉ Ioo c d) :
    ∃ i : Fin N, Icc c d ⊆ Icc (s i.castSucc) (s i.succ) := by
  -- The cell starts at the last subdivision point at or below the midpoint of `[c, d]`.
  obtain ⟨m, hcm, hmd⟩ := exists_between hcd
  let S := Finset.univ.filter fun j : Fin (N + 1) ↦ s j ≤ m
  have hS : S.Nonempty := ⟨0, Finset.mem_filter.2 ⟨Finset.mem_univ _, by linarith⟩⟩
  set j := S.max' hS
  have hj : s j ≤ m := (Finset.mem_filter.1 (S.max'_mem hS)).2
  have hjmax : ∀ k, s k ≤ m → k ≤ j := fun k hk ↦ S.le_max' k (by simp [S, hk])
  have hjlast : j ≠ Fin.last N := by
    intro h
    rw [h, hb] at hj
    linarith
  have hlo : s j ≤ c := by
    by_contra! h
    exact hdisj j ⟨by linarith, by linarith⟩ ⟨h, by linarith⟩
  have hmi : m < s (j.castPred hjlast).succ := by
    by_contra! h
    have hlt : (j.castPred hjlast).castSucc < (j.castPred hjlast).succ := Fin.castSucc_lt_succ
    rw [Fin.castSucc_castPred] at hlt
    exact (hjmax _ h).not_gt hlt
  have hhi : d ≤ s (j.castPred hjlast).succ := by
    by_contra! h
    exact hdisj _ ⟨by linarith, by linarith⟩ ⟨by linarith, h⟩
  refine ⟨j.castPred hjlast, fun t ht ↦ ⟨?_, ht.2.trans hhi⟩⟩
  rw [Fin.castSucc_castPred]
  exact hlo.trans ht.1

/-- **A polygonal curve is piecewise `C¹`**, with the interior points of its subdivision as
breakpoints. -/
theorem IsPolygonalOnInterval.isPiecewiseC1On {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : ℝ → E} {a b : ℝ} (h : IsPolygonalOnInterval f a b) :
    IsPiecewiseC1On f a b := by
  have hcont := h.absolutelyContinuousOnInterval.continuousOn
  obtain ⟨N, -, s, hs, ha, hb, hseg⟩ := h
  have hab : a ≤ b := ha ▸ hb ▸ hs.monotone (Fin.zero_le _)
  refine .of_breakpoints hcont ((Finset.univ.image s).filter (· ∈ Ioo a b)) ?_
    fun c d hcd hdisj ↦ ?_
  · intro t ht
    rw [min_eq_left hab, max_eq_right hab]
    exact (Finset.mem_filter.1 ht).2
  rcases le_or_gt d c with hdc | hcd'
  · -- A degenerate interval is at most a point.
    intro t ht
    have hpt : Icc c d = {t} := by
      ext u
      simp only [mem_Icc, mem_singleton_iff]
      constructor
      · rintro ⟨h₁, h₂⟩
        linarith [ht.1, ht.2]
      · rintro rfl
        exact ht
    rw [hpt]
    exact contDiffWithinAt_singleton
  rw [uIcc_of_le hab] at hcd
  obtain ⟨i, hi⟩ := exists_Icc_subset_cell ha hb hcd' (hcd ⟨le_rfl, hcd'.le⟩).1
    (hcd ⟨hcd'.le, le_rfl⟩).2 fun j hj hjcd ↦
      disjoint_left.1 hdisj (Finset.mem_coe.2 (Finset.mem_filter.2
        ⟨Finset.mem_image_of_mem s (Finset.mem_univ j), hj⟩)) hjcd
  refine (ContDiff.contDiffOn (s := Icc c d) (by fun_prop) :
    ContDiffOn ℝ 1 (fun t ↦ f (s i.castSucc) + ((t - s i.castSucc) / (s i.succ - s i.castSucc)) •
      (f (s i.succ) - f (s i.castSucc))) _).congr fun t ht ↦ hseg i t (hi ht)

end TauCeti
