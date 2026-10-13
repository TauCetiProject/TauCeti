/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Function.AbsolutelyContinuous.Gluing

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

end AbsolutelyContinuousOnInterval
