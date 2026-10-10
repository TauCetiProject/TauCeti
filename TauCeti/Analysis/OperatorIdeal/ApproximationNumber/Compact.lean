/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import TauCeti.Analysis.Normed.Operator.FiniteRankCompact
public import TauCeti.Analysis.OperatorIdeal.ApproximationNumber.Basic

/-!
# Approximation numbers, finite-rank approximability, and compactness

Staged for Tau Ceti, roadmap topic T09.  The boundary §A4 of that roadmap asks
for: an operator's approximation numbers tend to zero exactly when it is a norm
limit of finite-rank operators, and such an operator is compact.

* `tendsto_approximationNumber_atTop_iff_exists_finiteRank_approx` — the
  characterisation, stated **directly as a sequence of finite-rank operators**.
  The roadmap rules out a named `ApproximableOperator` predicate until multiple
  consumers justify one, so there is no new definition here.
* `isCompactOperator_of_tendsto_approximationNumber` — approximation numbers
  tending to zero force compactness, unconditionally over a proper scalar field.
  The closure argument is Mathlib's (`isCompactOperator_of_tendsto`) and the
  approximating sequence is the one above.  **The finite-rank input used to be an
  explicit hypothesis**, because Mathlib has no *finite rank ⇒ compact* lemma;
  it is now `ContinuousLinearMap.isCompactOperator_of_rank_lt_aleph0` in
  `ForTauCeti/Analysis/Normed/Operator/FiniteRankCompact.lean`, written there
  rather than here because it is a general fact about compact operators and has
  nothing to do with operator ideals — which is what this docstring previously
  said should happen.

**The converse over a general Banach space is deliberately absent.**  A compact
operator between Banach spaces need not be a norm limit of finite-rank operators
without an approximation-property hypothesis, so the implication
*compact ⇒ `aₙ → 0`* belongs to the Hilbert-space development and is not stated
here.  Recording that in this docstring rather than proving a false generalisation
is the point.

## Sources

*Follows nothing in particular*: the statements are the standard finite-rank
approximation boundary, and the proofs go through this library's own
approximation-number API and Mathlib's compact-operator closure lemma.

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Original module: authored directly in `ForTauCeti`.
* Extraction class: **authored in place**, for Tau Ceti.
* Original authors / copyright: Jon Crall, Claude Opus 5; Copyright (c) 2026
  Kitware, Inc.; Apache 2.0.
* Spectra influence: **none** — imports only Mathlib and the sibling `Basic`
  staging module.
-/

public section

namespace ContinuousLinearMap

open Filter Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- **Approximation numbers measure finite-rank approximability.**  `aₙ(T) → 0`
exactly when `T` is a norm limit of operators of finite rank, with the `n`-th term
of rank at most `n`.

Stated as an explicit sequence rather than through a predicate: roadmap topic T09
§A4 asks for the sequence form until a named `ApproximableOperator` has several
consumers to justify it. -/
theorem tendsto_approximationNumber_atTop_iff_exists_finiteRank_approx
    (T : E →L[𝕜] F) :
    Tendsto (T.approximationNumber) atTop (𝓝 0) ↔
      ∃ R : ℕ → (E →L[𝕜] F), (∀ n, (R n).rank ≤ (n : Cardinal)) ∧
        Tendsto (fun n => ‖T - R n‖) atTop (𝓝 0) := by
  constructor
  · intro h
    -- pick an `R n` within `1 / (n + 1)` of the infimum
    choose R hR hlt using fun n : ℕ =>
      T.exists_rank_le_norm_sub_lt_approximationNumber_add n
        (ε := (1 : ℝ) / (n + 1)) (by positivity)
    refine ⟨R, hR, ?_⟩
    have hone : Tendsto (fun n : ℕ => (1 : ℝ) / (n + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have hsum : Tendsto (fun n => T.approximationNumber n + (1 : ℝ) / (n + 1))
        atTop (𝓝 0) := by simpa using h.add hone
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => (hlt n).le) hsum
  · rintro ⟨R, hR, hconv⟩
    refine squeeze_zero (fun n => T.approximationNumber_nonneg n)
      (fun n => T.approximationNumber_le_norm_sub (hR n)) hconv

/-- **Approximable operators are compact.**  This is the implication roadmap
topic T09 §A4 asks for: `aₙ(T) → 0` forces `T` compact.

The argument is two Mathlib-shaped halves.  The approximating sequence is
`tendsto_approximationNumber_atTop_iff_exists_finiteRank_approx`, and the closure
step is Mathlib's `isCompactOperator_of_tendsto`; what sits between them is that
each `R n` is compact, which is
`ContinuousLinearMap.isCompactOperator_of_rank_lt_aleph0`.

**That last lemma is not Mathlib's** — Mathlib has no *finite rank ⇒ compact*
statement — so it is proved in
`ForTauCeti/Analysis/Normed/Operator/FiniteRankCompact.lean`, a module about
compact operators, rather than here.  An earlier version of this theorem carried
it as an explicit hypothesis with a docstring saying exactly that it should move;
it has moved.

`[ProperSpace 𝕜]` is what the finite-rank lemma needs, and it is the only new
scalar hypothesis.  Completeness of `F` is Mathlib's, for the closure step. -/
theorem isCompactOperator_of_tendsto_approximationNumber [ProperSpace 𝕜]
    [CompleteSpace F] (T : E →L[𝕜] F)
    (h : Tendsto (T.approximationNumber) atTop (𝓝 0)) :
    IsCompactOperator T := by
  obtain ⟨R, hR, hconv⟩ :=
    (T.tendsto_approximationNumber_atTop_iff_exists_finiteRank_approx).mp h
  have htend : Tendsto R atTop (𝓝 T) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    simpa only [norm_sub_rev] using hconv
  refine isCompactOperator_of_tendsto htend (Eventually.of_forall fun n => ?_)
  exact (R n).isCompactOperator_of_rank_lt_aleph0
    (lt_of_le_of_lt (hR n) (Cardinal.natCast_lt_aleph0))

end ContinuousLinearMap
