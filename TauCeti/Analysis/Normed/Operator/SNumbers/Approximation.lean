/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Operator.SNumbers.Basic
public import TauCeti.Analysis.OperatorIdeal.ApproximationNumber.MinMax

/-!
# The approximation numbers as an s-number sequence

The approximation numbers `aₙ(T) = inf {‖T - R‖ : rank R ≤ n}` are
`ContinuousLinearMap.singularValue`. This file places them in the axiomatic theory of s-numbers:
they form a strict s-number sequence over every nontrivially normed field, and they are the
largest s-number sequence.

The axioms (S1)–(S4) are the elementary calculus of the approximation numbers. The strict
normalization (S5′) is `ContinuousLinearMap.singularValue_id`: a bounded map of rank at most
`n < rank X` kills a nonzero vector, so it stays at operator-norm distance at least `1` from the
identity of `X`, while the zero map is at distance at most `1`.

## Main declarations

* `TauCeti.isStrictSNumberSequence_singularValue`: the approximation numbers are a strict
  s-number sequence.
* `TauCeti.IsSNumberSequence.le_singularValue`: every s-number sequence satisfies `s T n ≤ aₙ(T)`.

## References

* A. Pietsch, *s-Numbers of operators in Banach spaces*, Studia Math. **51** (1974), 201–223,
  §§1–2.
* A. Pietsch, *Eigenvalues and s-Numbers*, Cambridge Studies in Advanced Mathematics 13,
  Cambridge University Press (1987), §2.3.
* M. Ullrich, *Lean-SNumbers*, https://github.com/mario-ullrich/Lean-SNumbers (Apache-2.0),
  `Approximation.lean`: an earlier Lean formalization of the approximation numbers as an
  s-number sequence.
-/

public section

universe u

namespace TauCeti

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]

/-- **The approximation numbers are a strict s-number sequence.** -/
theorem isStrictSNumberSequence_singularValue :
    IsStrictSNumberSequence (𝕜 := 𝕜) fun T ↦ T.singularValue :=
  .of_id_of_lt_rank ContinuousLinearMap.singularValue_zero
    ContinuousLinearMap.antitone_singularValue ContinuousLinearMap.singularValue_add_le
    ContinuousLinearMap.singularValue_comp_comp_le
    (fun _ _ ↦ ContinuousLinearMap.singularValue_eq_zero_of_rank_le) fun hn ↦ by simp [hn]

/-- **The approximation numbers are the largest s-number sequence.** Every s-number sequence
satisfies `s T n ≤ aₙ(T)`. -/
theorem IsSNumberSequence.le_singularValue {s : SNumberFamily 𝕜} (hs : IsSNumberSequence s)
    {X Y : Type u} [NormedAddCommGroup X] [NormedSpace 𝕜 X] [NormedAddCommGroup Y]
    [NormedSpace 𝕜 Y] (T : X →L[𝕜] Y) (n : ℕ) : s T n ≤ T.singularValue n :=
  ContinuousLinearMap.le_singularValue_iff.mpr fun R hR ↦ by
    simpa [hs.eq_zero_of_rank_le R hR] using hs.le_add_nnnorm_sub T R n

end TauCeti
