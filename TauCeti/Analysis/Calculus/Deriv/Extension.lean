/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Derivative-preserving extension from a closed interval

A real-valued function with a derivative within a closed interval admits an extension
with the same values and ordinary derivatives throughout that interval. This allows
results that require two-sided derivatives to be applied to data on a closed interval.
-/

public section

namespace TauCeti

open Set

/-- A function with derivative `g' t` within `[a, b]` at each point `t` of the interval
has an extension that agrees there with `g` and has ordinary derivative `g' t` there. -/
theorem exists_hasDerivAt_extension {g g' : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hg : ∀ t ∈ Icc a b, HasDerivWithinAt g (g' t) (Icc a b) t) :
    ∃ G : ℝ → ℝ, EqOn G g (Icc a b) ∧ ∀ t ∈ Icc a b, HasDerivAt G (g' t) t := by
  let L (t : ℝ) := g a + g' a * (t - a)
  let R (t : ℝ) := g b + g' b * (t - b)
  let G (t : ℝ) := if t < a then L t else if b < t then R t else g t
  have hG : EqOn G g (Icc a b) := fun t ht ↦
    by simp [G, not_lt_of_ge ht.1, not_lt_of_ge ht.2]
  have hD (t : ℝ) (ht : t ∈ Icc a b) :
      HasDerivWithinAt G (g' t) (Icc a b) t := (hg t ht).congr_of_mem hG ht
  refine ⟨G, hG, fun t ht ↦ ?_⟩
  obtain hat | hat := ht.1.eq_or_lt
  · subst t
    have hL : HasDerivAt L (g' a) a := by
      simpa [L] using (((hasDerivAt_id a).sub_const a).const_mul (g' a)).const_add (g a)
    have hleft : HasDerivWithinAt G (g' a) (Iic a) a :=
      hL.hasDerivWithinAt.congr_of_mem (fun y hy ↦ by
        obtain hy | rfl := hy.lt_or_eq
        · simp [G, hy]
        · simp [G, L, hab.not_gt]) le_rfl
    have hright := (hD a ⟨le_rfl, hab.le⟩).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE hab)
    simpa only [Iic_union_Ici, hasDerivWithinAt_univ] using hleft.union hright
  obtain htb | htb := ht.2.eq_or_lt
  · subst t
    have hR : HasDerivAt R (g' b) b := by
      simpa [R] using (((hasDerivAt_id b).sub_const b).const_mul (g' b)).const_add (g b)
    have hright : HasDerivWithinAt G (g' b) (Ici b) b :=
      hR.hasDerivWithinAt.congr_of_mem (fun y hy ↦ by
        obtain hy | hy := hy.eq_or_lt
        · subst y
          simp [G, hab.not_gt, R]
        · simp [G, hy, (hab.trans hy).not_gt]) le_rfl
    have hleft := (hD b ⟨hab.le, le_rfl⟩).mono_of_mem_nhdsWithin (Icc_mem_nhdsLE hab)
    simpa only [Iic_union_Ici, hasDerivWithinAt_univ] using hleft.union hright
  exact (hD t ht).hasDerivAt (Icc_mem_nhds hat htb)

end TauCeti
