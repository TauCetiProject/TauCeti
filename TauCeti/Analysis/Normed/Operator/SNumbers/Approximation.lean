/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Operator.SNumbers.Basic
public import TauCeti.Analysis.OperatorIdeal.ApproximationNumber.MinMax

/-!
# Approximation numbers as s-numbers

The approximation numbers form a strict s-number sequence. They also dominate every
s-number sequence: perturbation by a rank-at-most-`n` operator bounds the `n`-th term by
the approximation error.

The approximation family uses the existing `ContinuousLinearMap.singularValue` directly,
without a second name, infimum or parallel calculus. The strict normalization is supplied by
`ContinuousLinearMap.singularValue_id`, whose rank-nullity proof does not require
completeness of the scalar field.

## References

* A. Pietsch, *s-Numbers of operators in Banach spaces*, Studia Math. 51 (1974), §§1–2.
* A. Pietsch, *Eigenvalues and s-Numbers*, Cambridge University Press (1987), Chapter 2.
-/

public section

open scoped NNReal

universe u

namespace TauCeti.SNumbers

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]

/-- The family of approximation numbers on all normed spaces over the scalar field. -/
noncomputable def approximation : SNumberFamily 𝕜 :=
  fun T ↦ T.singularValue

/-- Evaluation of the approximation family is the existing approximation number. -/
@[simp]
theorem approximation_apply {X Y : Type u}
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    (T : X →L[𝕜] Y) (n : ℕ) : approximation T n = T.singularValue n := (rfl)

/-- Approximation numbers satisfy Pietsch's s-number axioms over every nontrivially
normed field. -/
theorem isSNumberSequence_approximation : IsSNumberSequence (approximation (𝕜 := 𝕜)) where
  norm T := T.singularValue_zero
  antitone T := T.antitone_singularValue
  add_le S T n := S.singularValue_add_le T n
  comp_le B T A n := B.singularValue_comp_comp_le T A n
  eq_zero_of_rank_le hT := ContinuousLinearMap.singularValue_eq_zero_of_rank_le hT
  normalize n := by
    have hrank : Module.rank 𝕜 (EuclideanSpace 𝕜 (Fin (n + 1))) = (n + 1 : ℕ) := by
      rw [(WithLp.linearEquiv 2 𝕜 (Fin (n + 1) → 𝕜)).rank_eq]
      simp
    simp [approximation_apply, ContinuousLinearMap.singularValue_id, hrank]

/-- Approximation numbers are strict: every identity is normalized below the dimension.
No completeness assumption on the field or the space is needed. -/
theorem isStrictSNumberSequence_approximation :
    IsStrictSNumberSequence (approximation (𝕜 := 𝕜)) where
  toIsSNumberSequence := isSNumberSequence_approximation
  normalize_of_lt_rank n hn := by
    simp [approximation_apply, ContinuousLinearMap.singularValue_id, hn]

/-- Approximation numbers are the largest s-number sequence, pointwise on every operator. -/
theorem IsSNumberSequence.le_singularValue {s : SNumberFamily 𝕜}
    (hs : IsSNumberSequence s) {X Y : Type u}
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    (T : X →L[𝕜] Y) (n : ℕ) : s T n ≤ T.singularValue n := by
  refine ContinuousLinearMap.le_singularValue_iff.mpr fun R hR ↦ ?_
  have h := hs.add_le R (T - R) n
  simpa [hs.eq_zero_of_rank_le hR] using h

end TauCeti.SNumbers
