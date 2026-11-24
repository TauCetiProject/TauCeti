/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Matrix.Mul
public import Mathlib.Geometry.Convex.ConvexSpace.CompactSpaceStdSimplex
public import TauCeti.Analysis.Convex.StdSimplex.Faces
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.Order.Compact
import TauCeti.Algebra.BigOperators.Ring.Finset

/-!
# The probability simplex and expected values

The probability simplex `TauCeti.simplex ι` is the set of weight vectors of
`Convexity.StdSimplex ℝ ι` in `ι → ℝ`, the nonnegative vectors of sum `1`. Its points are the
probability distributions, or mixed strategies, over `ι`, and the dot product `p ⬝ᵥ v` is the
expected value of `v` under `p`.

## Main results

* `TauCeti.mem_simplex_iff`: the simplex consists of the nonnegative vectors of sum `1`.
* `TauCeti.convex_simplex`, `TauCeti.isCompact_simplex`: the simplex is convex, and compact over
  a finite type.
* `TauCeti.le_dotProduct_of_mem_simplex`, `TauCeti.dotProduct_le_of_mem_simplex`: an expected
  value lies between any lower and upper bounds of the values.
-/

public section

open Finset Matrix Convexity

namespace TauCeti

variable {ι : Type*}

variable (ι) in
/-- The probability simplex in `ι → ℝ`, the weight vectors of `Convexity.StdSimplex ℝ ι`. Its
points are the mixed strategies over the actions `ι`. -/
def simplex : Set (ι → ℝ) :=
  Set.range fun p : StdSimplex ℝ ι ↦ ⇑p.weights

variable (ι) in
/-- The probability simplex is the set of weight vectors of `Convexity.StdSimplex ℝ ι`. -/
theorem simplex_def : simplex ι = Set.range fun p : StdSimplex ℝ ι ↦ ⇑p.weights := (rfl)

/-- A vector is a mixed strategy exactly when its coordinates are nonnegative and sum to `1`. -/
@[simp]
theorem mem_simplex_iff [Fintype ι] {p : ι → ℝ} :
    p ∈ simplex ι ↔ (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1 :=
  StdSimplex.mem_range_toFun_comp_weights_iff

variable (ι) in
/-- The probability simplex is convex. -/
theorem convex_simplex : Convex ℝ (simplex ι) :=
  StdSimplex.convex_range_toFun_comp_weights ℝ ι

variable (ι) in
/-- The probability simplex over finitely many actions is compact. -/
theorem isCompact_simplex [Finite ι] : IsCompact (simplex ι) :=
  isCompact_range (StdSimplex.isEmbedding_toFun_comp_weights ℝ ι).continuous

/-- The pure strategy playing `i` is a mixed strategy. -/
theorem single_mem_simplex [DecidableEq ι] (i : ι) : Pi.single i 1 ∈ simplex ι :=
  StdSimplex.pi_single_mem_range_toFun_comp_weights i

variable (ι) in
/-- There is a mixed strategy as soon as there is an action. -/
theorem simplex_nonempty [Nonempty ι] : (simplex ι).Nonempty :=
  Set.range_nonempty _

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
