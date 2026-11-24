/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Dynamics.BirkhoffSum.Average
import Mathlib.Algebra.BigOperators.Pi

/-!
# Function-level identities for Birkhoff averages

Complements `Mathlib.Dynamics.BirkhoffSum.Average` with function-level expressions for
`birkhoffAverage`, requiring no normed structure or measure theory.

## Main results

* `TauCeti.birkhoffAverage_eq_smul_sum_comp_iterate` — expresses `birkhoffAverage R T f n` as
  `(n : R)⁻¹ • ∑ k ∈ Finset.range n, f ∘ T^[k]`.
-/

public section

namespace TauCeti

/-- Function-level formula for a Birkhoff average as a scaled sum of composed iterates. -/
theorem birkhoffAverage_eq_smul_sum_comp_iterate {R Ω M : Type*} [DivisionSemiring R]
    [AddCommMonoid M] [Module R M] (T : Ω → Ω) (f : Ω → M) (n : ℕ) :
    birkhoffAverage R T f n = (n : R)⁻¹ • ∑ k ∈ Finset.range n, f ∘ T^[k] := by
  ext x
  simp [birkhoffAverage, birkhoffSum, Finset.sum_apply]

end TauCeti
