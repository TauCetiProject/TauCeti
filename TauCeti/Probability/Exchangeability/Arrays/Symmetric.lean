/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Exchangeability.Arrays.Extreme

/-!
# Jointly exchangeable laws carried by the symmetric arrays

The jointly exchangeable probability laws on `ℕ × ℕ → α` whose complement of the symmetric arrays
with constant diagonal `d` is null. They are a face of all jointly exchangeable probability laws,
so the extreme-point characterisation of joint dissociation restricts to them unchanged: such a
law is jointly dissociated if and only if it is extreme among the laws so carried. For `α = Bool`
and `d = false` the carrier is the set of adjacency arrays of simple graphs on `ℕ`, and these are
the laws of exchangeable random graphs read as arrays.

The carrier `symmetricArraysWithDiag α d` is measurable when `[MeasurableEq α]`
(`measurableSet_symmetricArraysWithDiag`); the null-complement condition itself needs no
measurability.

## Main results

* `TauCeti.Probability.jointlyExchangeableProbabilityMeasuresOnSymmetric`, with its membership,
  convexity, face and extreme-point lemmas.
* `TauCeti.Probability.jointlyDissociated_iff_mem_extremePoints_onSymmetric` — **joint
  dissociation is extremality** among the jointly exchangeable laws carried by the symmetric
  arrays.

## References

* P. Diaconis, S. Janson, *Graph limits and exchangeable random graphs*, Rend. Mat. Appl. (7) 28
  (2008), 33–61, Section 5: exchangeable random graphs as symmetric zero-diagonal arrays, and
  dissociated laws as the extreme ones.
* O. Kallenberg, *Probabilistic Symmetries and Invariance Principles*, Springer, 2005, Chapter 7.
-/

public section

open MeasureTheory TauCeti.MeasureTheory Set
open scoped ENNReal

namespace TauCeti

namespace Probability

variable {α : Type*} [MeasurableSpace α]

/-- The jointly exchangeable probability laws carried by the symmetric arrays with diagonal `d`. -/
def jointlyExchangeableProbabilityMeasuresOnSymmetric (α : Type*) [MeasurableSpace α] (d : α) :
    Set (Measure (ℕ × ℕ → α)) :=
  jointlyExchangeableProbabilityMeasuresOn α (symmetricArraysWithDiag α d)

/-- Membership in the jointly exchangeable laws carried by the symmetric arrays. -/
@[simp]
theorem mem_jointlyExchangeableProbabilityMeasuresOnSymmetric_iff {d : α}
    {ν : Measure (ℕ × ℕ → α)} :
    ν ∈ jointlyExchangeableProbabilityMeasuresOnSymmetric α d
      ↔ ν ∈ jointlyExchangeableProbabilityMeasures α ∧ ν (symmetricArraysWithDiag α d)ᶜ = 0 :=
  mem_jointlyExchangeableProbabilityMeasuresOn_iff

/-- The jointly exchangeable laws carried by the symmetric arrays are a face of all jointly
exchangeable probability laws. -/
theorem isExtreme_jointlyExchangeableProbabilityMeasuresOnSymmetric (d : α) :
    IsExtreme ℝ≥0∞ (jointlyExchangeableProbabilityMeasures α)
      (jointlyExchangeableProbabilityMeasuresOnSymmetric α d) :=
  isExtreme_jointlyExchangeableProbabilityMeasuresOn _

/-- The jointly exchangeable laws carried by the symmetric arrays form a convex set. -/
theorem convex_jointlyExchangeableProbabilityMeasuresOnSymmetric (d : α) :
    Convex ℝ≥0∞ (jointlyExchangeableProbabilityMeasuresOnSymmetric α d) :=
  convex_jointlyExchangeableProbabilityMeasuresOn _

/-- The extreme points of the jointly exchangeable laws carried by the symmetric arrays are the
extreme jointly exchangeable laws so carried. -/
theorem extremePoints_jointlyExchangeableProbabilityMeasuresOnSymmetric (d : α) :
    extremePoints ℝ≥0∞ (jointlyExchangeableProbabilityMeasuresOnSymmetric α d)
      = jointlyExchangeableProbabilityMeasuresOnSymmetric α d
        ∩ extremePoints ℝ≥0∞ (jointlyExchangeableProbabilityMeasures α) :=
  extremePoints_jointlyExchangeableProbabilityMeasuresOn _

/-- **Joint dissociation is extremality among the laws carried by the symmetric arrays.** -/
theorem jointlyDissociated_iff_mem_extremePoints_onSymmetric {d : α} {ρ : Measure (ℕ × ℕ → α)}
    [IsProbabilityMeasure ρ] (hexch : JointlyExchangeable ρ fun p x => x p)
    (hsym : ρ (symmetricArraysWithDiag α d)ᶜ = 0) :
    JointlyDissociated ρ (fun p x => x p)
      ↔ ρ ∈ extremePoints ℝ≥0∞ (jointlyExchangeableProbabilityMeasuresOnSymmetric α d) :=
  jointlyDissociated_iff_mem_extremePoints_on hexch hsym

/-- The coordinate array of an extreme point of the jointly exchangeable laws carried by the
symmetric arrays is jointly dissociated. -/
theorem jointlyDissociated_of_mem_extremePoints_onSymmetric {d : α} {ρ : Measure (ℕ × ℕ → α)}
    (h : ρ ∈ extremePoints ℝ≥0∞ (jointlyExchangeableProbabilityMeasuresOnSymmetric α d)) :
    JointlyDissociated ρ fun p x => x p :=
  jointlyDissociated_of_mem_extremePoints_on h

end Probability

end TauCeti
