/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Operator.SNumbers.Approximation
public import TauCeti.Analysis.Normed.Operator.SNumbers.Hilbert
import TauCeti.Analysis.Normed.Operator.SNumbers.Uniqueness

/-!
# Extremal s-number sequences

Hilbert numbers are pointwise minimal among s-number sequences on normed spaces over `ℝ` or `ℂ`.
Together with `TauCeti.SNumbers.IsSNumberSequence.le_singularValue`, this gives the sandwich
`hₙ(T) ≤ sₙ(T) ≤ aₙ(T)` for every s-number sequence `s`.

Each compression `B ∘ T ∘ A` to `ℓ²(ℕ, 𝕜)` has equal s-numbers and approximation numbers by
Hilbert-space uniqueness. The ideal axiom then bounds its s-numbers by those of `T` when `A` and
`B` are contractions, giving the lower bound after taking the supremum.

## References

* M. Ullrich, *Inequalities between s-numbers*, Adv. Oper. Theory 9 (2024), art. 82,
  Proposition 2 and its proof in Section 3.
-/

public section

universe u

namespace TauCeti.SNumbers.IsSNumberSequence

variable {𝕜 : Type u} [RCLike 𝕜] {s : SNumberFamily 𝕜}

/-- The Hilbert numbers are bounded by every s-number sequence. -/
theorem hilbertNumber_le (hs : IsSNumberSequence s) {X Y : Type u}
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    (T : X →L[𝕜] Y) (n : ℕ) : T.hilbertNumber n ≤ s T n := by
  refine ContinuousLinearMap.hilbertNumber_le_iff.mpr fun A B hA hB ↦ ?_
  rw [← hs.eq_singularValue]
  exact hs.comp_comp_le_of_norm_le_one B T A n hB hA

end TauCeti.SNumbers.IsSNumberSequence
