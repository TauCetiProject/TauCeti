/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.GeneralLinear.HighestWeight

/-!
# Dominance of weights lowered by a coordinate weight

For a dominant `gl N` weight `μ`, subtracting the coordinate weight `εₜ` preserves dominance
exactly when the consecutive difference at `t` is positive (when `t` has a successor). This is the
indexing condition for the summands in the dual-standard Pieri rule: its prospective highest
weights are `μ - εₜ` for precisely these indices.

This criterion isolates the combinatorial part of the Pieri decomposition from its representation
theory. It also handles the final coordinate uniformly, where there is no following difference to
constrain.

## References

* W. Fulton and J. Harris, *Representation Theory: A First Course*, GTM 129 (1991), §15.
-/

public section

namespace TauCeti

variable {K : Type*} [Field K] [CharZero K] {N : ℕ} {μ : Fin N → K}

omit [CharZero K] in
private theorem sub_single_adjacent_diff (t i j : Fin N) :
    (μ - (Pi.single t (1 : K) : Fin N → K)) i -
        (μ - (Pi.single t (1 : K) : Fin N → K)) j =
      (μ i - μ j) - (if i = t then 1 else 0) + (if j = t then 1 else 0) := by
  simp only [Pi.sub_apply, Pi.single_apply]
  ring

/-- **Dominance after lowering one coordinate.** For a dominant integral weight `μ`, the weight
`μ - εₜ` is dominant exactly when, if `t` has a successor, the difference `μₜ - μₜ₊₁` is a
positive natural number. The final coordinate is always allowed. This is the precise index
condition for the summands of the `gl N` dual-standard Pieri rule. -/
theorem isGlDominantIntegral_sub_single_iff
    (hμ : IsGlDominantIntegral μ) (t : Fin N) :
    IsGlDominantIntegral (μ - (Pi.single t (1 : K) : Fin N → K)) ↔
      ∀ j : Fin N, (t : ℕ) + 1 = (j : ℕ) →
        ∃ k : ℕ, μ t - μ j = ((k + 1 : ℕ) : K) := by
  constructor
  · intro h j hj
    have hjne : j ≠ t := by
      intro hEq
      subst j
      omega
    obtain ⟨k, hk⟩ := (isGlDominantIntegral_iff.mp h) t j hj
    rw [sub_single_adjacent_diff (μ := μ) t t j] at hk
    simp only [↓reduceIte, ite_eq_right hjne, add_zero] at hk
    refine ⟨k, ?_⟩
    have hgap : μ t - μ j = ((k + 1 : ℕ) : K) := by
      push_cast at hk ⊢
      linear_combination hk
    exact hgap
  · intro h
    rw [isGlDominantIntegral_iff]
    intro i j hij
    by_cases hi : i = t
    · subst i
      have hjne : j ≠ t := by
        intro hEq
        subst j
        omega
      obtain ⟨k, hk⟩ := h j hij
      refine ⟨k, ?_⟩
      rw [sub_single_adjacent_diff (μ := μ) t t j]
      simp only [↓reduceIte, ite_eq_right hjne]
      push_cast at hk ⊢
      linear_combination hk
    · by_cases hj : j = t
      · subst j
        obtain ⟨k, hk⟩ := (isGlDominantIntegral_iff.mp hμ) i t hij
        refine ⟨k + 1, ?_⟩
        rw [sub_single_adjacent_diff (μ := μ) t i t]
        simp only [↓reduceIte, ite_eq_right hi]
        push_cast at hk ⊢
        linear_combination hk
      · obtain ⟨k, hk⟩ := (isGlDominantIntegral_iff.mp hμ) i j hij
        refine ⟨k, ?_⟩
        rw [sub_single_adjacent_diff (μ := μ) t i j]
        simp only [ite_eq_right hi, ite_eq_right hj, sub_zero, add_zero, hk]

end TauCeti
