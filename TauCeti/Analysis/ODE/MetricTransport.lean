/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import TauCeti.Analysis.ODE.DysonSeries
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Linear transport preserving an evolving bilinear form

A continuous linear equation on a closed interval has an invertible fundamental solution
initialized at any included time. If the time derivative of a bilinear form cancels its two
coefficient terms, the fundamental solution preserves the evolving form. Neither symmetry,
positivity, nor finite dimensionality is required.

## References

* B. Cook and B. Kotschwar, *The full holonomy group under the Ricci flow*, Section 2.1.
* Formalization references: https://github.com/frenzymath/lean-eval-submissions and
  https://github.com/frenzymath/PoincareConjecture.
-/

public noncomputable section

open Set

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Invertible linear transport preserves a time-dependent bilinear form when the derivative
of the form cancels the two coefficient terms. This includes both endpoints and arbitrary
initial times of the interval. -/
theorem exists_pairing_preserving_transport_Icc {a b t₀ : ℝ}
    (ht₀ : t₀ ∈ Icc a b) (A : ℝ → E →L[ℝ] E) (hA : ContinuousOn A (Icc a b))
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (G G' : ℝ → E →L[ℝ] E →L[ℝ] F)
    (hG : ∀ t ∈ Icc a b, HasDerivWithinAt G (G' t) (Icc a b) t)
    (hcompat : ∀ t ∈ Icc a b, ∀ v w,
      G' t v w + G t (A t v) w + G t v (A t w) = 0) :
    ∃ P : ℝ → E →L[ℝ] E,
      P t₀ = 1 ∧ (∀ t ∈ Icc a b, HasDerivAt P (A t * P t) t) ∧
      (∀ t, (P t).IsInvertible) ∧
      ∀ t ∈ Icc a b, ∀ v w, G t (P t v) (P t w) = G t₀ v w := by
  obtain ⟨P, hi, hd, hinv⟩ := exists_isInvertible_hasDerivAt_clm_Icc ht₀ A hA
  refine ⟨P, hi, hd, hinv, ?_⟩
  intro t ht v w
  let q : ℝ → F := fun s ↦ G s (P s v) (P s w)
  have hq (s : ℝ) (hs : s ∈ Icc a b) : HasDerivWithinAt q 0 (Icc a b) s := by
    have hv := (hd s hs).hasDerivWithinAt.clm_apply (hasDerivWithinAt_const s (Icc a b) v)
    have hw := (hd s hs).hasDerivWithinAt.clm_apply (hasDerivWithinAt_const s (Icc a b) w)
    refine (((hG s hs).clm_apply hv).clm_apply hw).congr_deriv ?_
    simpa only [smul_apply, add_apply, map_zero, add_zero, mul_apply_eq_comp] using
      hcompat s hs (P s v) (P s w)
  by_cases hab : a < b
  · have hc := constant_of_derivWithin_zero
      (fun s hs ↦ (hq s hs).differentiableWithinAt)
      (fun s hs ↦ (hq s (Ico_subset_Icc_self hs)).derivWithin
        (uniqueDiffOn_Icc hab s (Ico_subset_Icc_self hs)))
    simpa only [q, hi, one_apply_eq_self] using
      (hc t ht).trans (hc t₀ ht₀).symm
  · have heq : t = t₀ := by
      have hab' : a = b := le_antisymm (ht₀.1.trans ht₀.2) (not_lt.mp hab)
      exact (le_antisymm (ht.2.trans (hab' ▸ ht₀.1)) (ht₀.2.trans (hab' ▸ ht.1)))
    simp only [heq, hi, one_apply_eq_self]

end TauCeti
