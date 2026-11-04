/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.LSPath.RootOperator
public import TauCeti.RepresentationTheory.LSPath.Reparametrization

/-!
# Minimum heights of timed paths

The combinatorial minimum height of a path is the minimum of every timed parametrization
with positive segment durations, including the empty presentation. In particular, testing that a
translated path stays in a half-space is equivalent to testing its minimum height. These
comparisons connect the root-operator height criteria with chamber conditions on parametrized paths.
-/

public section

namespace TauCeti.PLPath

variable {𝕜 V : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [AddCommGroup V] [Module 𝕜 V] {f : Module.Dual 𝕜 V} {p : List (𝕜 × V)}

/-- Every height of a timed path is bounded below by its combinatorial minimum height,
including times outside the presentation's duration, when the path is constant. -/
theorem listMinHeight_le_apply_evalTimed (hp : IsTimed p) (t : 𝕜) :
    listMinHeight f (p.map Prod.snd) ≤ f (evalTimed p t) := by
  induction p generalizing t with
  | nil => simp
  | cons y p ih =>
    obtain ⟨d, v⟩ := y
    obtain ⟨hd, hp⟩ := isTimed_cons.mp hp
    rw [List.map_cons, listMinHeight_cons]
    rcases le_or_gt t d with ht | ht
    · rw [evalTimed_cons, evalTimed_of_nonpos hp.nonneg (sub_nonpos.mpr ht),
        add_zero, map_smul, smul_eq_mul]
      have hc₀ : 0 ≤ max 0 (min t d) / d := div_nonneg (le_max_left _ _) hd.le
      have hc₁ : max 0 (min t d) / d ≤ 1 := (div_le_one hd).mpr
        (max_le hd.le (min_le_right _ _))
      have hm := listMinHeight_nonpos (f := f) (p.map Prod.snd)
      have h₀ := min_le_left (0 : 𝕜) (f v + listMinHeight f (p.map Prod.snd))
      have h₁ := min_le_right (0 : 𝕜) (f v + listMinHeight f (p.map Prod.snd))
      rcases le_total 0 (f v) with hv | hv <;> nlinarith
    · rw [evalTimed_cons_of_le hd ht.le, map_add]
      have h := ih hp (t - d)
      exact (min_le_right _ _).trans (add_le_add_right h (f v))

/-- The minimum height is attained during any timed presentation, even when
some vector segments or their heights vanish. -/
theorem exists_apply_evalTimed_eq_listMinHeight (hp : IsTimed p) :
    ∃ t ∈ Set.Icc 0 (duration p),
      f (evalTimed p t) = listMinHeight f (p.map Prod.snd) := by
  induction p with
  | nil => exact ⟨0, by simp, by simp⟩
  | cons y p ih =>
    obtain ⟨d, v⟩ := y
    obtain ⟨hd, hp⟩ := isTimed_cons.mp hp
    rw [List.map_cons, listMinHeight_cons]
    by_cases h : 0 ≤ f v + listMinHeight f (p.map Prod.snd)
    · refine ⟨0, ⟨le_rfl, duration_nonneg (isTimed_cons.mpr ⟨hd, hp⟩).nonneg⟩, ?_⟩
      rw [evalTimed_zero (isTimed_cons.mpr ⟨hd, hp⟩).nonneg, map_zero, min_eq_left h]
    · obtain ⟨t, ht, he⟩ := ih hp
      refine ⟨d + t, ?_, ?_⟩
      · rw [duration_cons]
        exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
      · rw [evalTimed_cons_of_le hd (by linarith [ht.1]), add_sub_cancel_left,
          map_add, he, min_eq_right (le_of_not_ge h)]

/-- A lower bound on all heights during a timed presentation is exactly a lower bound on
the minimum height of the represented path. -/
theorem le_minHeight_ofSegments_iff (hp : IsTimed p) (c : 𝕜) :
    c ≤ (ofSegments 𝕜 (p.map Prod.snd)).minHeight f ↔
      ∀ t ∈ Set.Icc 0 (duration p), c ≤ f (evalTimed p t) := by
  rw [minHeight_ofSegments]
  constructor
  · intro h t _
    exact h.trans (listMinHeight_le_apply_evalTimed hp t)
  · intro h
    obtain ⟨t, ht, he⟩ := exists_apply_evalTimed_eq_listMinHeight (f := f) hp
    simpa only [he] using h t ht

end TauCeti.PLPath
