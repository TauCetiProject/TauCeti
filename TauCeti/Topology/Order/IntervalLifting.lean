/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Pasting lifts on adjacent intervals

Continuous lifts agreeing at the common endpoint can be pasted while preserving the
whole first interval. No separation condition on the source is required.

## References

* https://github.com/frenzymath/lean-eval-submissions
* https://github.com/frenzymath/PoincareConjecture
-/

public section

open Set Filter Function
open scoped Topology

/-- Paste two lifts on adjacent real intervals. The explicit construction
preserves the entire first interval; separation and ordering hypotheses are unnecessary. -/
theorem ContinuousOn.exists_lift_piecewise_Icc
    {X Y : Type*} [TopologicalSpace X] {f : X → Y} {c : ℝ → Y}
    {a b d : ℝ} {l₁ l₂ : ℝ → X}
    (h₁ : ContinuousOn l₁ (Icc a b)) (h₂ : ContinuousOn l₂ (Icc b d))
    (hjoin : l₁ b = l₂ b) (hp₁ : EqOn (f ∘ l₁) c (Icc a b))
    (hp₂ : EqOn (f ∘ l₂) c (Icc b d)) :
    ∃ l : ℝ → X, ContinuousOn l (Icc a d) ∧ EqOn l l₁ (Icc a b) ∧
      EqOn (f ∘ l) c (Icc a d) := by
  classical
  refine ⟨(Iic b).piecewise l₁ l₂, ?_,
    fun t ht ↦ piecewise_eq_of_mem _ _ _ ht.2, ?_⟩
  · apply ContinuousOn.piecewise
    · intro t ht
      have : t = b := by simpa only [frontier_Iic, mem_singleton_iff] using ht.2
      subst t
      exact hjoin
    · exact h₁.mono fun t ht ↦ ⟨ht.1.1, by simpa only [closure_Iic, mem_Iic] using ht.2⟩
    · exact h₂.mono fun t ht ↦
        ⟨by simpa only [compl_Iic, closure_Ioi, mem_Ici] using ht.2, ht.1.2⟩
  · intro t ht
    by_cases htb : t ∈ Iic b
    · simpa only [comp_apply, piecewise_eq_of_mem _ _ _ htb] using hp₁ ⟨ht.1, htb⟩
    · simpa only [comp_apply, piecewise_eq_of_notMem _ _ _ htb] using
        hp₂ ⟨(lt_of_not_ge htb).le, ht.2⟩
