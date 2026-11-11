/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.FreePoisson.Basic
public import TauCeti.Probability.FreeProbability.FreePoisson.Basic
public import TauCeti.Probability.FreeProbability.Law.Basic

/-!
# The law of a free Poisson element

Let `φ` be a positive linear functional on a C⋆-algebra `A` and `a` a selfadjoint element of `A`.
The element `a` is free Poisson of rate `r ≥ 0` and jump size `c ∈ ℝ` for `φ` exactly when its law
`μ_a` is the free Poisson law `freePoissonReal r c`. Both are determined by their moments, which
agree. Together with the cumulant characterization `TauCeti.isFreePoisson_iff_freeCumulant_const`
of free Poisson elements, this identifies the free Poisson law, the free cumulant sequence
`κ_n = r c ^ n`, and the moment sequence `c ^ n ∑_{π ∈ NC(n)} r ^ |π|`.

Every rate `r ≥ 0` and jump size `c` is realized: in the commutative C⋆-algebra of continuous
functions on a compact interval carrying `freePoissonReal r c`, with integration against this
law, the coordinate function is free Poisson of rate `r` and jump size `c`, so by
`TauCeti.isFreePoisson_iff_freeCumulant_const` its free cumulants are `κ_n = r c ^ n`.

## Main results

* `PositiveLinearMap.law_eq_freePoissonReal_iff` — for selfadjoint `a`,
  `μ_a = freePoissonReal r c` if and only if `a` is free Poisson of rate `r` and jump size `c`.
* `TauCeti.isFreePoisson_integralPositiveLinearMap_freePoissonReal` — a commutative realization
  of a free Poisson element of every rate `r ≥ 0` and jump size `c`.

## References

* A. Nica, R. Speicher, *Lectures on the Combinatorics of Free Probability*, Lecture 12.
-/

public section

open MeasureTheory NNReal TauCeti TauCeti.Probability
open scoped ComplexOrder

namespace PositiveLinearMap

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] (φ : A →ₚ[ℂ] ℂ)
  {a : A}

/-- *The law of a free Poisson element*: a selfadjoint element `a` of a C⋆-algebra has the free
Poisson law of rate `r` and jump size `c` with respect to `φ` if and only if it is free Poisson of
rate `r` and jump size `c` for `φ`. -/
theorem law_eq_freePoissonReal_iff (ha : IsSelfAdjoint a) (r : ℝ≥0) (c : ℝ) :
    law φ a = freePoissonReal r c ↔ IsFreePoisson φ.toLinearMap a ((r : ℝ) : ℂ) (c : ℂ) := by
  rw [eq_comm, eq_law_iff_forall_integral_pow ha isCompact_Icc (freePoissonReal_compl_Icc r c),
    isFreePoisson_iff_apply_pow]
  simp [integral_pow_freePoissonReal, eq_comm (a := φ _)]

end PositiveLinearMap

namespace TauCeti

/-- *Free Poisson elements of every rate and jump size exist*: in the commutative C⋆-algebra of
complex continuous functions on `K = [-R, R]`, where `R = |c| (1 + √r)²`, with the state given by
integration against the free Poisson law of rate `r` and jump size `c`, the coordinate function
`x ↦ x` is free Poisson of rate `r` and jump size `c`. -/
theorem isFreePoisson_integralPositiveLinearMap_freePoissonReal (r : ℝ≥0) (c : ℝ) :
    IsFreePoisson (ContinuousMap.integralPositiveLinearMap ((freePoissonReal r c).comap
        ((↑) : Set.Icc (-(|c| * (1 + √(r : ℝ)) ^ 2)) (|c| * (1 + √(r : ℝ)) ^ 2) → ℝ))).toLinearMap
      ((ContinuousMap.restrict (Set.Icc (-(|c| * (1 + √(r : ℝ)) ^ 2)) (|c| * (1 + √(r : ℝ)) ^ 2))
        (ContinuousMap.id ℝ)).realToRCLike ℂ) ((r : ℝ) : ℂ) (c : ℂ) :=
  (PositiveLinearMap.law_eq_freePoissonReal_iff _ (ContinuousMap.isSelfAdjoint_realToRCLike ℂ)
    r c).1 (PositiveLinearMap.law_integralPositiveLinearMap_comap_restrict_id
      (freePoissonReal_compl_Icc r c))

end TauCeti
