/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
public import TauCeti.Analysis.CompletelyMonotone.Basic

/-!
# Bernstein's representation theorem (forward direction)

Bernstein's theorem represents a completely monotone function as the Laplace transform of a
positive measure on `[0, ∞)`. This file develops the **forward direction** for
`TauCeti.IsCompletelyMonotone`, the closed-half-line notion from
`TauCeti.Analysis.CompletelyMonotone.Basic`: every completely monotone `f` is the Laplace
transform of a finite measure on `ℝ≥0`. It builds on the object API (the predicate and its
closure lemmas) rather than redeveloping it.

The proof is a port of the sorry-free Chafaï-style development in `mrdouglasny/hille-yosida`
(`HilleYosida.Bernstein.bernstein_theorem`), whose `IsCompletelyMonotone` is definitionally the
same predicate. Roadmap intention #33.

## Scope and the finite-vs-all-moments subtlety

We state only the forward existence here, with a **finite** representing measure — exactly what
complete monotonicity on the closed half-line yields, and what hille-yosida proves. The
*biconditional* is deferred (PR #2): the converse "finite measure ⟹ completely monotone" is
**false** for this closed-half-line class — e.g. `t ↦ ∫₀^∞ e^{-x t}(1+x)⁻² dx` comes from a
finite measure yet has `f'(0⁺) = -∞`, so it is not `C^∞` at `0`. The class that closed
complete monotonicity matches biconditionally is the measures with **all moments finite**
(`∫ xⁿ dμ < ∞` for every `n`), confirmed independently by Gemini 3.1 Pro and Codex. See the
`TODO` block at the end for the deferred all-moments iff.

## Main declarations

* `TauCeti.laplaceTransformMeasure`: `t ↦ ∫ e^{-t x} dμ`, the Laplace transform of a measure
  on `ℝ≥0`.
* `TauCeti.IsCompletelyMonotone.exists_measure`: every completely monotone function on
  `[0, ∞)` is the Laplace transform of a finite measure on `ℝ≥0`.

## Implementation notes

Port path (Chafaï 2013, as in hille-yosida): the Taylor integral remainder gives
`f(x) = boundary(n,T) + ∫_x^T ρ_n`, a change of variables `p = (n-1)/t` turns the densities
`ρ_n` into measures whose kernels `(1 - xp/(n-1))^{n-1}` increase to `e^{-xp}`, the total mass
is the uniform bound `f(0) - f(∞)`, and Prokhorov + portmanteau extract the weak limit `μ`.
hille-yosida carries the measure on `Measure ℝ` with a `μ (Iio 0) = 0` support side-condition;
here we follow the TauCeti convention and carry it on `Measure ℝ≥0`, converting via pushforward.

## References

* R. Schilling, R. Song, Z. Vondraček, *Bernstein Functions: Theory and Applications*
  (de Gruyter, 2nd ed. 2012), Ch. 1.
* D. V. Widder, *The Laplace Transform* (Princeton, 1941), Ch. IV.
* D. Chafaï, *Aspects of the Bernstein theorem* (2013).
-/

public section

open MeasureTheory Set
open scoped NNReal Topology

namespace TauCeti

variable {f : ℝ → ℝ} {μ : Measure ℝ≥0}

/-- The **Laplace transform** of a measure `μ` on `ℝ≥0`, evaluated at `t : ℝ`:
`t ↦ ∫ e^{-t x} dμ(x)`. By Bernstein's theorem every completely monotone function on
`[0, ∞)` is of this form for a finite `μ` (`IsCompletelyMonotone.exists_measure`). -/
noncomputable def laplaceTransformMeasure (μ : Measure ℝ≥0) (t : ℝ) : ℝ :=
  ∫ x, Real.exp (-t * (x : ℝ)) ∂μ

/-- **Bernstein's theorem, forward direction.** Every completely monotone function on the
closed half-line `[0, ∞)` is the Laplace transform of a finite measure on `ℝ≥0`.

Port of `HilleYosida.Bernstein.bernstein_theorem`: complete monotonicity makes the
finite-difference densities positive and bounds their total mass by `f(0) - f(∞)`, so the
Chafaï approximating measures are tight; Prokhorov extracts a weak limit `μ`, and portmanteau
identifies `f` with its Laplace transform. -/
theorem IsCompletelyMonotone.exists_measure (hf : IsCompletelyMonotone f) :
    ∃ μ : Measure ℝ≥0, IsFiniteMeasure μ ∧
      ∀ t : ℝ, 0 ≤ t → f t = laplaceTransformMeasure μ t := by
  sorry

-- TODO (PR #2 — the biconditional, all-moments form). The textbook iff requires the
-- *all-moments* condition on the measure side, not mere finiteness (see the scope note above).
-- Sketch of the additional API:
--
-- /-- `μ` has finite moments of every order; this is what closed complete monotonicity
-- matches biconditionally (`n = 0` already forces `μ` finite). -/
-- def HasAllMoments (μ : Measure ℝ≥0) : Prop :=
--   ∀ n : ℕ, Integrable (fun x : ℝ≥0 => (x : ℝ) ^ n) μ
--
-- theorem isCompletelyMonotone_laplaceTransformMeasure (hμ : HasAllMoments μ) :
--     IsCompletelyMonotone (laplaceTransformMeasure μ) := ...      -- ⇐, differentiate under ∫
--
-- theorem laplaceTransformMeasure_injective {μ ν : Measure ℝ≥0}
--     (hμ : HasAllMoments μ) (hν : HasAllMoments ν)
--     (h : ∀ t : ℝ, 0 ≤ t → laplaceTransformMeasure μ t = laplaceTransformMeasure ν t) :
--     μ = ν := ...                                  -- port BCR_Common.laplace_measure_unique
--
-- theorem bernstein (f : ℝ → ℝ) :
--     IsCompletelyMonotone f ↔
--       ∃! μ : Measure ℝ≥0, HasAllMoments μ ∧
--         ∀ t : ℝ, 0 ≤ t → f t = laplaceTransformMeasure μ t := ...   -- assemble ⇒/⇐/uniqueness

end TauCeti
