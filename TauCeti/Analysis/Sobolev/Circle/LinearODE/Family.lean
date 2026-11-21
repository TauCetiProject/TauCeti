/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Circle.LinearODE.Basic
import TauCeti.Analysis.Normed.Operator.CompactFamily

/-!
# Uniform inverses for compact families of periodic differential operators

For continuous families of real-linear coefficient loops `S p` and `J p`, invertibility of
`ζ ↦ ζ' - S p ζ` on a compact parameter set persists for `S p - δ • J p`, on a common closed
interval of weights about zero. The inverses are uniformly bounded from `H⁰` to `H¹`.
The period can be any positive real number. These are estimates for periodic loop operators;
they do not assert invertibility of a differential operator on an entire cylinder.

The weighted coefficient `S - δ J` is the end-operator perturbation occurring in Floer theory.
The Sobolev realization is the existing `CircleSobolev.loopOperator`; the uniformity follows
from operator-norm continuity and compactness.

## References

* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), Lecture 2, for the periodic asymptotic operator at a nondegenerate orbit.
-/

public section

open Filter Set Topology

namespace TauCeti.CircleSobolev

variable {P E : Type*} [TopologicalSpace P]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  (T : ℝ) [Fact (0 < T)]

/-- On a compact parameter set where the unweighted periodic operators are invertible,
all sufficiently small positive or negative weights have uniformly bounded inverses
`H⁰(E) →L[ℝ] H¹(E)`. No positivity or complex-linearity assumption on `J` is needed. -/
theorem exists_pos_isInvertible_loopOperator_sub_smul_norm_inverse_le
    {K : Set P} (hK : IsCompact K)
    (S J : P → C(AddCircle T, E →L[ℝ] E)) (hS : ContinuousOn S K) (hJ : ContinuousOn J K)
    (hinv : ∀ p ∈ K, (loopOperator T (S p)).IsInvertible) :
    ∃ ε > 0, ∃ C ≥ 0, ∀ p ∈ K, ∀ δ : ℝ, |δ| ≤ ε →
      (loopOperator T (S p - δ • J p)).IsInvertible ∧
        ‖(loopOperator T (S p - δ • J p)).inverse‖ ≤ C := by
  let : CompleteSpace E := FiniteDimensional.completeSpace ℂ E
  exact hK.exists_pos_isInvertible_map_sub_smul_norm_inverse_le (continuous_loopOperator T)
    S J hS hJ hinv

end TauCeti.CircleSobolev
