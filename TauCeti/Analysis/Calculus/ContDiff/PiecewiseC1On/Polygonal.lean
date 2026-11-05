/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.ContDiff.PiecewiseC1On
public import TauCeti.MeasureTheory.Function.AbsolutelyContinuous.Gluing
import Mathlib.Analysis.Calculus.ContDiff.Operations
import TauCeti.Order.Interval.Set.Subdivision

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
  have hac : a ≤ c := (hcd ⟨le_rfl, hcd'.le⟩).1
  have hdb : d ≤ b := (hcd ⟨hcd'.le, le_rfl⟩).2
  obtain ⟨i, hi⟩ := exists_Icc_subset_Icc_castSucc_succ (ha ▸ hac) hcd' (hb ▸ hdb) fun j hjcd ↦
    disjoint_left.1 hdisj (Finset.mem_coe.2 (Finset.mem_filter.2
      ⟨Finset.mem_image_of_mem s (Finset.mem_univ j),
        hac.trans_lt hjcd.1, hjcd.2.trans_le hdb⟩)) hjcd
  refine (ContDiff.contDiffOn (s := Icc c d) (by fun_prop) :
    ContDiffOn ℝ 1 (fun t ↦ f (s i.castSucc) + ((t - s i.castSucc) / (s i.succ - s i.castSucc)) •
      (f (s i.succ) - f (s i.castSucc))) _).congr fun t ht ↦ hseg i t (hi ht)

end TauCeti
