/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.Skellam.Basic
public import TauCeti.Probability.Distributions.Poisson.Support
import Mathlib.Data.Nat.Cast.SetInterval
import Mathlib.Topology.Instances.Int

/-!
# Topological support of Skellam laws

The difference of two positive-rate Poisson counts has support all integers. When the first
rate vanishes, only nonpositive integers remain; when the second vanishes, only nonnegative
integers remain. Both zero rates give the singleton zero. The support after casting to the
reals retains the integer lattice, including at the one-sided boundaries.

`support_skellamMeasure` and `support_map_intCast_skellamMeasure` express all four cases
without requiring a separate choice of parameter range.

## References

* J. G. Skellam, *The frequency distribution of the difference between two Poisson variates
  belonging to different populations*, Journal of the Royal Statistical Society 109 (1946), 296.
-/

public section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal

namespace TauCeti.Probability

/-- The exact native support of a Skellam law. A zero first rate imposes nonpositivity, and a
zero second rate imposes nonnegativity; together they restrict the support to zero. -/
@[simp]
theorem support_skellamMeasure (r₁ r₂ : ℝ≥0) :
    (skellamMeasure r₁ r₂).support =
      {k : ℤ | (r₁ = 0 → k ≤ 0) ∧ (r₂ = 0 → 0 ≤ k)} := by
  by_cases h₁ : r₁ = 0
  · subst r₁
    by_cases h₂ : r₂ = 0
    · subst r₂
      simp [le_antisymm_iff]
    · rw [skellamMeasure_zero_left,
        Measure.support_map_eq_closure_image _ Measure.support_mem_ae (by fun_prop),
        support_poissonMeasure]
      simp only [h₂, ↓reduceIte, image_univ, (isClosed_discrete _).closure_eq]
      rw [range_comp' Neg.neg (Nat.cast : ℕ → ℤ), Nat.range_cast_int, image_neg_Ici]
      ext k
      simp
  · by_cases h₂ : r₂ = 0
    · subst r₂
      rw [skellamMeasure_zero_right,
        Measure.support_map_eq_closure_image _ Measure.support_mem_ae (by fun_prop),
        support_poissonMeasure]
      simp only [h₁, ↓reduceIte, image_univ, (isClosed_discrete _).closure_eq,
        Nat.range_cast_int]
      ext k
      simp
    · rw [Measure.support_eq_setOf_singleton_ne_zero]
      ext k
      simp only [mem_ofPred_eq, h₁, h₂, false_implies, and_self, iff_true]
      exact (skellamMeasure_singleton_pos (pos_iff_ne_zero.mpr h₁)
        (pos_iff_ne_zero.mpr h₂) k).ne'

/-- The exact real-cast Skellam support consists of integer points satisfying the same
zero-rate sign restrictions as the native support. In particular, it contains no nonintegers. -/
@[simp]
theorem support_map_intCast_skellamMeasure (r₁ r₂ : ℝ≥0) :
    ((skellamMeasure r₁ r₂).map (Int.cast : ℤ → ℝ)).support =
      {x : ℝ | x ∈ range (Int.cast : ℤ → ℝ) ∧
        (r₁ = 0 → x ≤ 0) ∧ (r₂ = 0 → 0 ≤ x)} := by
  rw [Measure.support_map_eq_closure_image _ Measure.support_mem_ae (by fun_prop),
    (Int.isClosedEmbedding_coe_real.isClosedMap _ Measure.isClosed_support).closure_eq,
    support_skellamMeasure]
  ext x
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨⟨k, rfl⟩, by exact_mod_cast hk.1, by exact_mod_cast hk.2⟩
  · rintro ⟨⟨k, rfl⟩, h₁, h₂⟩
    exact ⟨k, ⟨by exact_mod_cast h₁, by exact_mod_cast h₂⟩, rfl⟩

end TauCeti.Probability
