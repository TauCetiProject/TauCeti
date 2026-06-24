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
# Bernstein's representation theorem

The Hausdorff–Bernstein–Widder theorem represents a completely monotone function as the
Laplace transform of a positive measure on `[0, ∞)`. This file develops the representation
for `TauCeti.IsCompletelyMonotone`, the *closed*-half-line notion from
`TauCeti.Analysis.CompletelyMonotone.Basic`, building on the object API (the predicate, its
closure lemmas, and the building block `t ↦ e^{-x t}`) rather than redeveloping it here.

## ⚠ Statement note — which measures correspond to `IsCompletelyMonotone`

The classical theorem matches complete monotonicity on the **open** half-line `(0, ∞)` with
*arbitrary* (possibly infinite) positive measures, and the bounded/`f(0⁺) < ∞` subclass with
**finite** measures. Our `IsCompletelyMonotone` is stronger still: it demands `C^∞` up to the
boundary point `0`. As `CompletelyMonotone/Basic.lean` records, that is a genuine
strengthening — it excludes some Laplace transforms of finite measures, e.g.
`t ↦ ∫₀^∞ e^{-x t} (1 + x)⁻² dx`, which is finite at `0` yet has `f'(0⁺) = -∞`.

So the naïve `IsCompletelyMonotone f ↔ ∃! finite μ, …` (as written in the roadmap milestone)
is **false in the `⇐` direction**. The class that closed complete monotonicity actually
matches is the measures with **all moments finite**: `∫ xⁿ dμ < ∞` for every `n`,
equivalently `f⁽ⁿ⁾(0⁺)` finite for every `n` (note `n = 0` already forces `μ` finite). The
main statement below is phrased that way, via `HasAllMoments`.

If instead we want the textbook finite-measure biconditional, the right left-hand side is the
*continuous-at-0* relaxation `IsCompletelyMonotoneOnIoi f ∧ ContinuousWithinAt f (Ici 0) 0`
rather than `IsCompletelyMonotone f`. That variant is left as a TODO; see the commented
`bernstein_finite` statement at the end.

## Main declarations

* `TauCeti.laplaceTransformMeasure`: `t ↦ ∫ e^{-t x} dμ`, the Laplace transform of a measure
  on `ℝ≥0`.
* `TauCeti.HasAllMoments`: every power `x ↦ xⁿ` is `μ`-integrable.
* `TauCeti.isCompletelyMonotone_laplaceTransformMeasure`: the Laplace transform of an
  all-moments measure is completely monotone (the easy `⇐` direction).
* `TauCeti.IsCompletelyMonotone.exists_measure`: every completely monotone function arises this
  way (the hard `⇒` direction — measure extraction via tightness).
* `TauCeti.bernstein`: the representation biconditional with uniqueness.

## Implementation notes

The `⇒` direction is the substance: extract a measure from the sequence of finite
approximations and pass to the limit (Prokhorov tightness), with uniqueness from injectivity
of the Laplace transform. The port source is the sorry-free `mrdouglasny/hille-yosida`
development (roadmap intention #33).

## References

* R. Schilling, R. Song, Z. Vondraček, *Bernstein Functions: Theory and Applications*
  (de Gruyter, 2nd ed. 2012), Ch. 1.
* D. V. Widder, *The Laplace Transform* (Princeton, 1941), Ch. IV.
-/

public section

open MeasureTheory Set
open scoped NNReal Topology

namespace TauCeti

variable {f : ℝ → ℝ} {μ : Measure ℝ≥0}

/-- The **Laplace transform** of a measure `μ` on `ℝ≥0`, evaluated at `t : ℝ`:
`t ↦ ∫ e^{-t x} dμ(x)`. The completely monotone functions on `[0, ∞)` are exactly these
transforms for measures with all moments finite (`bernstein`). -/
noncomputable def laplaceTransformMeasure (μ : Measure ℝ≥0) (t : ℝ) : ℝ :=
  ∫ x, Real.exp (-t * (x : ℝ)) ∂μ

/-- A measure on `ℝ≥0` **has all moments** when every monomial `x ↦ xⁿ` is integrable. This is
the measure-side condition that matches closed-half-line complete monotonicity: it forces
`μ` to be finite (the `n = 0` case) and `f⁽ⁿ⁾(0⁺) = (-1)ⁿ ∫ xⁿ dμ` to be finite for all `n`,
i.e. the Laplace transform is `C^∞` up to the boundary. -/
def HasAllMoments (μ : Measure ℝ≥0) : Prop :=
  ∀ n : ℕ, Integrable (fun x : ℝ≥0 => (x : ℝ) ^ n) μ

/-- A measure with all moments finite is finite (the zeroth moment is its mass). -/
theorem HasAllMoments.isFiniteMeasure (hμ : HasAllMoments μ) : IsFiniteMeasure μ := by
  sorry

/-! ### The easy direction: Laplace transforms are completely monotone -/

/-- The Laplace transform of a measure with all moments finite is completely monotone on the
closed half-line `[0, ∞)`. Differentiating under the integral sign `n` times brings down a
factor `(-x)ⁿ`, so `(-1)ⁿ` times the `n`-th derivative is `∫ xⁿ e^{-t x} dμ ≥ 0`; the
all-moments hypothesis is exactly what licenses differentiation up to and including `t = 0`. -/
theorem isCompletelyMonotone_laplaceTransformMeasure (hμ : HasAllMoments μ) :
    IsCompletelyMonotone (laplaceTransformMeasure μ) := by
  sorry

/-! ### The hard direction: every completely monotone function is a Laplace transform -/

/-- **Measure extraction.** Every completely monotone function on `[0, ∞)` is the Laplace
transform of a (unique) measure on `ℝ≥0` with all moments finite.

Proof path (Hausdorff–Bernstein–Widder): the finite differences of `f` define a sequence of
discrete approximating measures; complete monotonicity makes them positive and the bound at
`t = 0` makes the family tight, so Prokhorov gives a weak limit `μ`, and passing to the limit
identifies `f` with its Laplace transform. Smoothness at the boundary upgrades finiteness to
all-moments. -/
theorem IsCompletelyMonotone.exists_measure (hf : IsCompletelyMonotone f) :
    ∃ μ : Measure ℝ≥0, HasAllMoments μ ∧
      ∀ t : ℝ, 0 ≤ t → f t = laplaceTransformMeasure μ t := by
  sorry

/-- **Uniqueness.** Two all-moments measures with the same Laplace transform on `[0, ∞)` agree,
by injectivity of the Laplace transform on measures. -/
theorem laplaceTransformMeasure_injective {μ ν : Measure ℝ≥0}
    (hμ : HasAllMoments μ) (hν : HasAllMoments ν)
    (h : ∀ t : ℝ, 0 ≤ t → laplaceTransformMeasure μ t = laplaceTransformMeasure ν t) :
    μ = ν := by
  sorry

/-! ### Bernstein's theorem -/

/-- **Bernstein's representation theorem.** A function `f : ℝ → ℝ` is completely monotone on
the closed half-line `[0, ∞)` if and only if it is the Laplace transform of a unique measure
on `ℝ≥0` whose moments are all finite.

See the statement note in the module docstring: the all-moments condition (not mere
finiteness) is what closed complete monotonicity matches. -/
theorem bernstein (f : ℝ → ℝ) :
    IsCompletelyMonotone f ↔
      ∃! μ : Measure ℝ≥0, HasAllMoments μ ∧
        ∀ t : ℝ, 0 ≤ t → f t = laplaceTransformMeasure μ t := by
  constructor
  · intro hf
    obtain ⟨μ, hμ, hrep⟩ := hf.exists_measure
    refine ⟨μ, ⟨hμ, hrep⟩, ?_⟩
    rintro ν ⟨hν, hrep'⟩
    refine laplaceTransformMeasure_injective hν hμ (fun t ht => ?_)
    rw [← hrep' t ht, ← hrep t ht]
  · rintro ⟨μ, ⟨hμ, hrep⟩, -⟩
    have hcm := isCompletelyMonotone_laplaceTransformMeasure hμ
    exact hcm.congr (fun t ht => hrep t ht)

-- TODO (textbook finite-measure variant). With the continuous-at-0 relaxation of the
-- left-hand side, the representing measure is merely finite:
--
-- theorem bernstein_finite (f : ℝ → ℝ)
--     (hf : IsCompletelyMonotoneOnIoi f) (hf0 : ContinuousWithinAt f (Ici 0) 0) :
--     ∃! μ : Measure ℝ≥0, IsFiniteMeasure μ ∧
--       ∀ t : ℝ, 0 ≤ t → f t = laplaceTransformMeasure μ t := by
--   sorry

end TauCeti
