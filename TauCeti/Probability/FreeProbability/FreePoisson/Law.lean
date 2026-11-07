/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.FreePoisson
public import TauCeti.Probability.FreeProbability.FreePoisson.Basic
public import TauCeti.Probability.FreeProbability.Law.Basic

/-!
# Scalar laws and realizations of free Poisson elements

A selfadjoint element in a C⋆-algebra has scalar law `freePoisson r c` exactly when it satisfies
the normalized moment condition `IsFreePoisson`. For a normalized functional, this is equivalent
to free cumulants `r * c ^ n` in positive degrees. Compact moment determinacy supplies the
comparison. Every nonnegative rate and real jump size has a positive,
bounded commutative realization: the coordinate function on the compact support of this measure,
with integration as state. No trace or faithfulness of a given state is required.

## Main results

* `PositiveLinearMap.law_eq_freePoisson_iff`: equality of scalar laws is equivalent to the
  algebraic free Poisson moment/cumulant condition.
* `TauCeti.isFreePoisson_integralPositiveLinearMap_freePoisson`: bounded positive realizations
  for all parameters, including negative and zero jumps.
* `TauCeti.IsSemicircular.law_sq`: the square of a selfadjoint semicircular element has rate-one
  free Poisson law.

## References

* A. Nica, R. Speicher, *Lectures on the Combinatorics of Free Probability*, Lecture 12.
-/

public section

open MeasureTheory TauCeti TauCeti.Probability
open scoped NNReal ComplexOrder

namespace PositiveLinearMap

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  (φ : A →ₚ[ℂ] ℂ) {a : A}

/-- The scalar law of a selfadjoint element is free Poisson of rate `r` and jump size `c`
exactly when it satisfies the normalized free Poisson moment condition. For a normalized `φ`,
this is equivalent to free cumulants `r * c ^ n` in positive degrees. -/
theorem law_eq_freePoisson_iff (ha : IsSelfAdjoint a) (r : ℝ≥0) (c : ℝ) :
    law φ a = freePoisson r c ↔ IsFreePoisson φ.toLinearMap a ((r : ℝ) : ℂ) (c : ℂ) := by
  rw [eq_comm, eq_law_iff_forall_integral_pow ha (isCompact_support_freePoisson r c)
    Measure.measure_compl_support, isFreePoisson_iff_apply_pow]
  refine forall_congr' fun n => ?_
  simp [integral_pow_freePoisson, eq_comm]

end PositiveLinearMap

namespace TauCeti

/-- A positive, bounded commutative realization of the free Poisson moments: the coordinate
function on the compact support of `freePoisson r c`, with the integration state. -/
theorem isFreePoisson_integralPositiveLinearMap_freePoisson (r : ℝ≥0) (c : ℝ) :
    let K := (Probability.freePoisson r c).support
    let : CompactSpace K :=
      isCompact_iff_compactSpace.mp (Probability.isCompact_support_freePoisson r c)
    IsFreePoisson (ContinuousMap.integralPositiveLinearMap
        ((Probability.freePoisson r c).comap ((↑) : K → ℝ))).toLinearMap
      ((ContinuousMap.restrict K (ContinuousMap.id ℝ)).realToRCLike ℂ)
      ((r : ℝ) : ℂ) (c : ℂ) := by
  let : CompactSpace (Probability.freePoisson r c).support :=
    isCompact_iff_compactSpace.mp (Probability.isCompact_support_freePoisson r c)
  dsimp only
  exact (PositiveLinearMap.law_eq_freePoisson_iff _
    (ContinuousMap.isSelfAdjoint_realToRCLike ℂ) r c).1
      (PositiveLinearMap.law_integralPositiveLinearMap_comap_restrict_id
        Measure.measure_compl_support)

/-- The square of a selfadjoint semicircular element of variance `v` has the free Poisson law
of rate one and jump size `v`. This includes variance zero. -/
theorem IsSemicircular.law_sq {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    {φ : A →ₚ[ℂ] ℂ} {a : A} {v : ℝ≥0}
    (h : IsSemicircular φ.toLinearMap a ((v : ℝ) : ℂ)) (ha : IsSelfAdjoint a) :
    φ.law (a ^ 2) = Probability.freePoisson 1 v := by
  exact (φ.law_eq_freePoisson_iff (ha.pow 2) 1 v).2 (by simpa using h.isFreePoisson_sq)

end TauCeti
