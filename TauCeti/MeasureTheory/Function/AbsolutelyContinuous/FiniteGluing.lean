/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Function.AbsolutelyContinuous.Gluing
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Finite gluing of absolutely continuous curves

Absolute continuity on successive cells of a finite subdivision implies absolute continuity
between its first and last nodes. The nodes need not be ordered.
-/

public section

namespace AbsolutelyContinuousOnInterval

variable {X : Type*} [PseudoMetricSpace X] {γ : ℝ → X}

/-- Glue absolute continuity on all successive cells of a finite subdivision. -/
theorem of_subdivision {N : ℕ} {s : Fin (N + 1) → ℝ}
    (h : ∀ i : Fin N, AbsolutelyContinuousOnInterval γ (s i.castSucc) (s i.succ)) :
    AbsolutelyContinuousOnInterval γ (s 0) (s (Fin.last N)) := by
  induction N with
  | zero => exact .refl γ _
  | succ N ih =>
    have hprev : ∀ i : Fin N, AbsolutelyContinuousOnInterval γ
        (s i.castSucc.castSucc) (s i.succ.castSucc) := by
      intro i
      simpa only [Fin.castSucc_succ] using h i.castSucc
    have hp : AbsolutelyContinuousOnInterval γ (s 0) (s (Fin.last N).castSucc) :=
      ih (s := fun j ↦ s j.castSucc) hprev
    exact hp.trans (h (Fin.last N))

/-- A finite increasing subdivision with affine interpolation on every cell gives an absolutely
continuous curve. The subdivision may have no cells. -/
theorem of_affine_subdivision {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} {a b : ℝ} {N : ℕ} {s : Fin (N + 1) → ℝ}
    (hs : StrictMono s) (ha : s 0 = a) (hb : s (Fin.last N) = b)
    (hsegments : ∀ i : Fin N, ∀ t ∈ Set.Icc (s i.castSucc) (s i.succ),
      f t = f (s i.castSucc) +
        ((t - s i.castSucc) / (s i.succ - s i.castSucc)) •
          (f (s i.succ) - f (s i.castSucc))) :
    AbsolutelyContinuousOnInterval f a b := by
  have hedge (i : Fin N) :
      AbsolutelyContinuousOnInterval f (s i.castSucc) (s i.succ) := by
    have hc : ContDiffOn ℝ 1
        (fun t : ℝ ↦ f (s i.castSucc) +
          ((t - s i.castSucc) / (s i.succ - s i.castSucc)) •
            (f (s i.succ) - f (s i.castSucc)))
        (Set.uIcc (s i.castSucc) (s i.succ)) := by fun_prop
    apply hc.absolutelyContinuousOnInterval.congr
    intro t ht
    rw [Set.uIcc_of_le (hs i.castSucc_lt_succ).le] at ht
    exact (hsegments i t ht).symm
  simpa only [ha, hb] using of_subdivision hedge

end AbsolutelyContinuousOnInterval
