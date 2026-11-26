/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.HomogeneousSymbol

/-!
# Fréchet and mixed derivatives of homogeneous symbols

At a nonzero frequency a homogeneous symbol is smooth, so its Fréchet derivatives in the position
and the frequency behave like those of a smooth function there. This file records the pointwise
facts used to compare the jets of homogeneous symbols.

## Main results

* `TauCeti.HomogeneousSymbol.iteratedFDeriv_coefficient_sub`: at a nonzero frequency, the higher
  derivatives of `a - b` are the differences of those of `a` and `b`.
* `TauCeti.HomogeneousSymbol.norm_mixedDeriv_coefficient_le`: at a nonzero frequency, the mixed
  derivative `∂_x^α ∂_ξ^β a` is bounded by the Fréchet derivative of order `|α| + |β|`.
* `TauCeti.HomogeneousSymbol.norm_iteratedFDeriv_coefficient_le_sum`: conversely, the Fréchet
  derivative of order `k` is bounded by the sum of the mixed derivatives along the words of length
  `k` in position and frequency letters.
-/

public section

namespace TauCeti

namespace HomogeneousSymbol

variable {X E V W : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup E]
  [NormedSpace ℝ E] [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W]
  [NormedSpace ℂ W] {m : ℝ}

/-- At a nonzero frequency, the higher derivatives of a difference of homogeneous symbols are the
differences of their higher derivatives. -/
theorem iteratedFDeriv_coefficient_sub (a b : HomogeneousSymbol X E V W m) (k : ℕ) {x : X}
    {ξ : E} (hξ : ξ ≠ 0) :
    iteratedFDeriv ℝ k (a - b).coefficient (x, ξ) =
      iteratedFDeriv ℝ k a.coefficient (x, ξ) - iteratedFDeriv ℝ k b.coefficient (x, ξ) := by
  rw [coefficient_sub]
  exact iteratedFDeriv_sub_apply (contDiffAt_infty.1 (a.contDiffAt_coefficient (p := (x, ξ)) hξ) _)
    (contDiffAt_infty.1 (b.contDiffAt_coefficient (p := (x, ξ)) hξ) _)

variable {n : ℕ}

/-- At a nonzero frequency, the mixed derivative `∂_x^α ∂_ξ^β a(x, ξ)` of a homogeneous symbol is
bounded by the norm of its Fréchet derivative of order `|α| + |β|` in `(x, ξ)`. -/
theorem norm_mixedDeriv_coefficient_le
    (a : HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W m) (α β : List (Fin n))
    (x : CoordinateSpace n) {ξ : CoordinateSpace n} (hξ : ξ ≠ 0) :
    ‖mixedDeriv α β a.coefficient x ξ‖ ≤
      ‖iteratedFDeriv ℝ (α.length + β.length) a.coefficient (x, ξ)‖ := by
  -- Both sides only depend on the germ of the coefficient at `(x, ξ)`, which is smooth.
  obtain ⟨f, hf, hfa⟩ := a.exists_contDiff_eventuallyEq_coefficient hξ
  rw [← (hfa x).mixedDeriv_eq, ← ((hfa x).iteratedFDeriv ℝ _).eq_of_nhds]
  exact norm_mixedDeriv_le α β (contDiff_infty.1 hf _) x ξ

/-- At a nonzero frequency, the Fréchet derivative of order `k` of a homogeneous symbol in
`(x, ξ)` is bounded by the sum of the norms of its mixed derivatives along the words of length `k`
in position and frequency letters. -/
theorem norm_iteratedFDeriv_coefficient_le_sum
    (a : HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W m) (k : ℕ)
    (x : CoordinateSpace n) {ξ : CoordinateSpace n} (hξ : ξ ≠ 0) :
    ‖iteratedFDeriv ℝ k a.coefficient (x, ξ)‖ ≤ ∑ w : Fin k → Fin n ⊕ Fin n,
      ‖mixedDeriv ((List.ofFn w).filterMap Sum.getLeft?) ((List.ofFn w).filterMap Sum.getRight?)
        a.coefficient x ξ‖ := by
  -- Both sides only depend on the germ of the coefficient at `(x, ξ)`, which is smooth.
  obtain ⟨f, hf, hfa⟩ := a.exists_contDiff_eventuallyEq_coefficient hξ
  simp only [← (hfa x).mixedDeriv_eq, ← ((hfa x).iteratedFDeriv ℝ k).eq_of_nhds]
  exact norm_iteratedFDeriv_le_sum_mixedDeriv (contDiff_infty.1 hf k) (x, ξ)

end HomogeneousSymbol

end TauCeti
