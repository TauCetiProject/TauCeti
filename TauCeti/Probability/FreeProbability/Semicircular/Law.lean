/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Semicircle.Moments
public import TauCeti.Probability.FreeProbability.Law.Basic
public import TauCeti.Probability.FreeProbability.Semicircular.Basic

/-!
# The law of a semicircular element

Let `φ` be a positive linear functional on a C⋆-algebra `A` and `a` a selfadjoint element of `A`.
The element `a` is semicircular of variance `v ≥ 0` for `φ` exactly when its law `μ_a` is the
centred semicircle law `semicircleReal 0 v`, the measure with density `(2π v)⁻¹ √(4v - t²)` on
`[-2√v, 2√v]` for `v > 0` and the Dirac mass at `0` for `v = 0`. Both are determined by their
moments, which agree. Together with the cumulant characterization of semicircular elements, this
identifies the semicircle law, the free cumulant sequence `κ₂ = v`, `κ_n = 0` for `n ≠ 2`, and the
moment sequence `v ^ k * catalan k`.

Every variance `v ≥ 0` is realized: in the commutative C⋆-algebra `C([-2√v, 2√v], ℂ)` with
integration against the semicircle law, the coordinate function is semicircular of variance `v`.

## Main results

* `PositiveLinearMap.law_eq_semicircleReal_iff` — for selfadjoint `a`, `μ_a = semicircleReal 0 v`
  if and only if `a` is semicircular of variance `v`.
* `TauCeti.isSemicircular_integralPositiveLinearMap_semicircleReal` — a commutative
  realization of a semicircular element of any variance `v ≥ 0`.

## References

* A. Nica, R. Speicher, *Lectures on the Combinatorics of Free Probability*, Lectures 2 and 3.
-/

public section

open MeasureTheory NNReal TauCeti TauCeti.Probability
open scoped ComplexOrder

namespace PositiveLinearMap

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] (φ : A →ₚ[ℂ] ℂ)
  {a : A}

/-- *The law of a semicircular element*: a selfadjoint element `a` of a C⋆-algebra has the centred
semicircle law of variance `v` with respect to `φ` if and only if it is semicircular of variance
`v` for `φ`. -/
theorem law_eq_semicircleReal_iff (ha : IsSelfAdjoint a) (v : ℝ≥0) :
    law φ a = semicircleReal 0 v ↔ IsSemicircular φ.toLinearMap a ((v : ℝ) : ℂ) := by
  rw [eq_comm, eq_law_iff_forall_integral_pow ha isCompact_Icc
      (by simpa only [zero_sub, zero_add, Set.ofPred_mem_eq] using
        mem_ae_iff.1 (ae_mem_Icc_semicircleReal 0 v)),
    isSemicircular_iff_apply_pow]
  refine forall_congr' fun n => ?_
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' n <;> simp [eq_comm]

end PositiveLinearMap

namespace TauCeti

/-- *Semicircular elements of every variance exist*: in the commutative C⋆-algebra of complex
continuous functions on `K = [-2√v, 2√v]`, with the state given by integration against the
semicircle law of variance `v`, the coordinate function `x ↦ x` is semicircular of variance `v`. -/
theorem isSemicircular_integralPositiveLinearMap_semicircleReal (v : ℝ≥0) :
    IsSemicircular (ContinuousMap.integralPositiveLinearMap ((semicircleReal 0 v).comap
        ((↑) : Set.Icc (-(2 * √(v : ℝ))) (2 * √(v : ℝ)) → ℝ))).toLinearMap
      ((ContinuousMap.restrict (Set.Icc (-(2 * √(v : ℝ))) (2 * √(v : ℝ)))
        (ContinuousMap.id ℝ)).realToRCLike ℂ) ((v : ℝ) : ℂ) :=
  (PositiveLinearMap.law_eq_semicircleReal_iff _ (ContinuousMap.isSelfAdjoint_realToRCLike ℂ) v).1
    (PositiveLinearMap.law_integralPositiveLinearMap_comap_restrict_id
      (by simpa only [zero_sub, zero_add, Set.ofPred_mem_eq] using
        mem_ae_iff.1 (ae_mem_Icc_semicircleReal 0 v)))

end TauCeti
