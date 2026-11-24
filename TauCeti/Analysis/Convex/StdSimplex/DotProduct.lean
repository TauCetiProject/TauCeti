/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Matrix.Mul
public import TauCeti.Analysis.Convex.StdSimplex.ProbabilitySimplex
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import TauCeti.Algebra.BigOperators.Ring.Finset

/-!
# Expected values over the probability simplex

For a point `p` of the probability simplex `TauCeti.simplex ι`, a mixed strategy over `ι`, the dot
product `p ⬝ᵥ v` is the expected value of `v` under `p`. It lies between any lower and upper
bounds of the values.

## Main results

* `TauCeti.le_dotProduct_of_mem_simplex`, `TauCeti.dotProduct_le_of_mem_simplex`: an expected
  value lies between any lower and upper bounds of the values.
-/

public section

open Finset Matrix

namespace TauCeti

variable {ι : Type*}

/-- The expected value under a mixed strategy is at least any lower bound of the values. -/
theorem le_dotProduct_of_mem_simplex [Fintype ι] {p v : ι → ℝ} {c : ℝ} (hp : p ∈ simplex ι)
    (hv : ∀ i, c ≤ v i) : c ≤ p ⬝ᵥ v := by
  obtain ⟨hp0, hp1⟩ := mem_simplex_iff.1 hp
  rw [dotProduct]
  calc c = ∑ i, p i * c := (sum_mul_const_of_sum_eq_one hp1 c).symm
    _ ≤ ∑ i, p i * v i := sum_le_sum fun i _ ↦ mul_le_mul_of_nonneg_left (hv i) (hp0 i)

/-- The expected value under a mixed strategy is at most any upper bound of the values. -/
theorem dotProduct_le_of_mem_simplex [Fintype ι] {p v : ι → ℝ} {c : ℝ} (hp : p ∈ simplex ι)
    (hv : ∀ i, v i ≤ c) : p ⬝ᵥ v ≤ c := by
  obtain ⟨hp0, hp1⟩ := mem_simplex_iff.1 hp
  rw [dotProduct]
  calc ∑ i, p i * v i ≤ ∑ i, p i * c :=
        sum_le_sum fun i _ ↦ mul_le_mul_of_nonneg_left (hv i) (hp0 i)
    _ = c := sum_mul_const_of_sum_eq_one hp1 c

end TauCeti
