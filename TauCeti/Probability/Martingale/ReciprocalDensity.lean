/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Function.ConditionalExpectation.WithDensity
public import Mathlib.Probability.Martingale.Basic

/-!
# The reverse density martingale

Let `Q = μ.withDensity w` be a finite measure equivalent to a finite measure `μ`.
If `Z_t = E_μ[w.toReal | ℱ_t]`, then `1 / Z_t` is a `Q`-martingale, closed by the
reciprocal terminal density `1 / w.toReal`. Neither the density nor its reciprocal needs
a deterministic bound. This supplies the reverse density process when transferring
martingale representations between equivalent measures.

These are fixed-time conditional-expectation identities. No path regularity or
simultaneous-in-time strict positivity of a chosen density version is asserted here.
In particular, a continuous density version still needs a separate nonattainment-of-zero
argument before its reciprocal can be used in a stochastic product formula.

## References

* I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Springer, 1991, §3.5.
-/

public section

open scoped ENNReal

namespace MeasureTheory

variable {Ω ι : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
  [Preorder ι] [IsFiniteMeasure μ] {ℱ : Filtration ι mΩ} {w : Ω → ℝ≥0∞}

/-- The reciprocal conditional density is a martingale under the equivalent changed
measure. It is the conditional expectation of the reciprocal terminal density, not an
inverse taken inside the original-measure conditional expectation. -/
theorem martingale_inv_condExp_toReal_withDensity (hw : AEMeasurable w μ)
    [IsFiniteMeasure (μ.withDensity w)] (hpos : ∀ᵐ x ∂μ, w x ≠ 0) :
    Martingale (fun t x ↦ (μ[fun y ↦ (w y).toReal | ℱ t] x)⁻¹) ℱ
      (μ.withDensity w) := by
  apply (martingale_condExp (fun x ↦ ((w x).toReal)⁻¹) ℱ (μ.withDensity w)).congr
    (fun t ↦ (stronglyMeasurable_condExp (μ := μ)
      (f := fun y ↦ (w y).toReal) (m := ℱ t)).inv₀)
  intro t
  exact condExp_inv_toReal_withDensity hw hpos

end MeasureTheory
