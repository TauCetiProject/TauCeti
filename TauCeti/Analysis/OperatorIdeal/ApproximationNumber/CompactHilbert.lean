/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5

Staged for Tau Ceti, roadmap topic T09, Milestone A3.  Mathlib is not the
destination (`ForTauCeti/README.md`); what follows is where this material would
have gone on the closed Mathlib track — addition to
`Mathlib/Analysis/InnerProductSpace/`, alongside the orthogonal projection.

Formalized by Claude Opus 5 (claude-opus-5[1m]).
-/
module

public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import TauCeti.Analysis.Normed.Operator.FiniteRankCompact
public import TauCeti.Analysis.OperatorIdeal.ApproximationNumber.Basic
public import TauCeti.Analysis.OperatorIdeal.ApproximationNumber.Compact
public import TauCeti.LinearAlgebra.Dimension.RankComp

/-!
# Compact operators into a Hilbert space are approximable

The last edge of the approximable/compact boundary: a compact operator whose
**target** is a Hilbert space has `aₙ(T) → 0`.  The other three edges are
elsewhere in this directory — the characterisation of `aₙ(T) → 0` as
finite-rank approximability, and approximable ⇒ compact — and the four together
say that on a Hilbert target, compactness *is* the vanishing of the
approximation numbers.

* `ContinuousLinearMap.exists_rank_le_natCast_norm_sub_le_of_isCompactOperator`:
  the quantitative form — a compact operator is within `ε` of an operator of
  finite rank, for every `ε > 0`.
* `ContinuousLinearMap.tendsto_approximationNumber_atTop_nhds_zero_of_isCompactOperator`:
  the roadmap statement, `aₙ(T) → 0`.
* `ContinuousLinearMap.isCompactOperator_iff_tendsto_approximationNumber`: the
  boundary as a single equivalence, on a complete Hilbert target.

## The hypothesis is on the target, not on the pair

The roadmap asks for compact operators *between* Hilbert spaces.  What the proof
uses is an orthogonal projection onto a finite-dimensional subspace of the
**codomain**, so the domain `E` is an arbitrary normed space over `𝕜` and only
`F` carries an inner product.  Stating it that way is not a speculative
generalisation: it is what the argument proves, and the asymmetry is the content
— the counterexamples that make *compact ⇒ approximable* false in general are
about the target's approximation property, so this is where the Hilbert
hypothesis has to sit.  A reader who wants the roadmap's symmetric statement
gets it by instantiating `E`.

**Completeness of `F` is not needed either**, and is deliberately absent from the
first two results: a finite-dimensional subspace of an inner-product space is
complete on its own, which is what makes its orthogonal projection exist.  Only
the reverse implication of the final equivalence needs `[CompleteSpace F]`, for
Mathlib's closure argument.

## The proof

Total boundedness, not the spectral theorem.  A compact `T` sends the closed unit
ball into a totally bounded set, so for `ε > 0` finitely many `ε`-balls centred at
points `y ∈ s` cover its image; let `P` be the orthogonal projection onto
`span 𝕜 s`, which is finite-dimensional.  For a unit vector `x`, the point `P (T x)`
is the nearest point of the span to `T x` (`Submodule.starProjection_minimal`) and
some `y ∈ s` is within `ε`, so `‖T x - P (T x)‖ ≤ ε`; hence `‖T - P ∘L T‖ ≤ ε` and
`P ∘L T` has rank at most `finrank 𝕜 (span 𝕜 s)`.

The spectral theorem for compact self-adjoint operators applied to `T⋆T` is the
textbook route and was the predicted one; it proves a strictly weaker statement
(it needs both spaces to be Hilbert, and `F` complete) through a much larger
prerequisite.  The nearest-point argument is recorded here because it is the one
that fits the API this directory already has.

## Sources

*Follows nothing in particular*: the finite-`ε`-net argument is the standard
textbook proof that a Hilbert space has the approximation property, specialised
to what the approximation-number API needs.

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Original module: authored directly in `ForTauCeti`.
* Extraction class: **authored in place**, for Tau Ceti.
* Original authors / copyright: Jon Crall, Claude Opus 5; Copyright (c) 2026
  Kitware, Inc.; Apache 2.0.
* Spectra influence: **none** — imports only Mathlib and sibling staging modules.
-/

public section

noncomputable section

namespace ContinuousLinearMap

open Filter Topology

universe u v w

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E : Type v} {F : Type w}
variable [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- **A compact operator into a Hilbert space is uniformly approximable by
operators of finite rank.**  For every `ε > 0` there is an `R` of rank at most
some `n` with `‖T - R‖ ≤ ε`.

The rank bound is delivered as `R.rank ≤ (n : Cardinal)` with `n` existentially
quantified, which is the shape `approximationNumber_le_norm_sub` consumes; the
value of `n` is `finrank 𝕜` of the span of an `ε`-net of `T '' closedBall 0 1`,
and no statement downstream depends on which `n` it is. -/
theorem exists_rank_le_natCast_norm_sub_le_of_isCompactOperator (T : E →L[𝕜] F)
    (hT : IsCompactOperator T) {ε : ℝ} (hε : 0 < ε) :
    ∃ (n : ℕ) (R : E →L[𝕜] F), R.rank ≤ (n : Cardinal) ∧ ‖T - R‖ ≤ ε := by
  classical
  -- the image of the closed unit ball is totally bounded, so it has a finite `ε`-net
  have htb : TotallyBounded (T '' Metric.closedBall (0 : E) 1) :=
    (hT.isCompact_closure_image_closedBall 1).totallyBounded.subset subset_closure
  obtain ⟨s, hsfin, hs⟩ := Metric.totallyBounded_iff.mp htb ε hε
  set U : Submodule 𝕜 F := Submodule.span 𝕜 s with hU
  have : FiniteDimensional 𝕜 U := FiniteDimensional.span_of_finite 𝕜 hsfin
  set R : E →L[𝕜] F := U.starProjection ∘L T with hR
  -- `R` lands in `U`, which is finite-dimensional, so its rank is some natural number
  have hrange : LinearMap.range (R : E →ₗ[𝕜] F) ≤ U := by
    rintro _ ⟨x, rfl⟩
    exact U.starProjection_apply_mem _
  have : FiniteDimensional 𝕜 (LinearMap.range (R : E →ₗ[𝕜] F)) :=
    Submodule.finiteDimensional_of_le hrange
  obtain ⟨n, hn⟩ :=
    Cardinal.lt_aleph0.mp (Module.rank_lt_aleph0 𝕜 (LinearMap.range (R : E →ₗ[𝕜] F)))
  refine ⟨n, R, hn.le, ?_⟩
  -- on a unit vector, `R x` is the nearest point of `U` to `T x`, and the net puts a
  -- point of `U` within `ε` of `T x`
  refine opNorm_le_of_unit_norm hε.le fun x hx => ?_
  have hxmem : T x ∈ T '' Metric.closedBall (0 : E) 1 :=
    Set.mem_image_of_mem _ (by simpa [Metric.mem_closedBall] using hx.le)
  obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp (hs hxmem)
  have hbdd : BddBelow (Set.range fun u : U => ‖T x - (u : F)‖) :=
    ⟨0, by rintro _ ⟨u, rfl⟩; positivity⟩
  calc ‖(T - R) x‖ = ‖T x - U.starProjection (T x)‖ := by simp [hR]
    _ = ⨅ u : U, ‖T x - (u : F)‖ := U.starProjection_minimal (T x)
    _ ≤ ‖T x - y‖ := ciInf_le hbdd (⟨y, Submodule.subset_span hy⟩ : U)
    _ ≤ ε := by rw [← dist_eq_norm]; exact (Metric.mem_ball.mp hxy).le

/-- **A compact operator into a Hilbert space has vanishing approximation
numbers.**  This is the roadmap's Milestone A3 and the last of the four edges of
the approximable/compact boundary.

Given `ε > 0`, the previous theorem supplies an `R` of rank at most `n` with
`‖T - R‖ ≤ ε / 2`; every index `m ≥ n` then admits `R` as a competitor, so
`aₘ(T) ≤ ε / 2 < ε`.  Antitonicity of `aₙ` is not needed — the rank bound
`R.rank ≤ n ≤ m` is what makes `R` admissible at `m`. -/
theorem tendsto_approximationNumber_atTop_nhds_zero_of_isCompactOperator (T : E →L[𝕜] F)
    (hT : IsCompactOperator T) : Tendsto (T.approximationNumber) atTop (𝓝 0) := by
  refine Metric.tendsto_atTop.2 fun ε hε => ?_
  obtain ⟨n, R, hrank, hle⟩ :=
    T.exists_rank_le_natCast_norm_sub_le_of_isCompactOperator hT (half_pos hε)
  refine ⟨n, fun m hm => ?_⟩
  have hadm : R.rank ≤ (m : Cardinal) := hrank.trans (by exact_mod_cast hm)
  have hbound : T.approximationNumber m ≤ ‖T - R‖ := T.approximationNumber_le_norm_sub hadm
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (T.approximationNumber_nonneg m)]
  linarith

/-- **On a complete Hilbert target, compactness is the vanishing of the approximation
numbers.**  Both implications are in this directory; the equivalence is stated because
it is the boundary the roadmap describes, and reading it off the two halves requires
knowing that the hypotheses line up.

`[CompleteSpace F]` is used only by the reverse implication, through Mathlib's closure
argument for compact operators; the forward implication needs neither it nor an inner
product on the domain. -/
theorem isCompactOperator_iff_tendsto_approximationNumber [CompleteSpace F] (T : E →L[𝕜] F) :
    IsCompactOperator T ↔ Tendsto (T.approximationNumber) atTop (𝓝 0) :=
  ⟨T.tendsto_approximationNumber_atTop_nhds_zero_of_isCompactOperator,
    T.isCompactOperator_of_tendsto_approximationNumber⟩

end ContinuousLinearMap
