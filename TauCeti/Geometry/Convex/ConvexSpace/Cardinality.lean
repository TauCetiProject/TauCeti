/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Basic.Real.Basic
public import TauCeti.Geometry.Convex.ConvexSpace.Defs
import Mathlib.Analysis.Real.Cardinality
import Mathlib.Order.Interval.Set.Infinite

/-!
# Cardinality instances for standard simplices

Standard simplices on a vertex type with at least two elements contain an embedded copy of the
closed unit interval `[0, 1]`, so they are infinite over densely ordered strict ordered rings and
uncountable over `ℝ`.

## Main results

* `Convexity.StdSimplex.instInfinite`: `Infinite (StdSimplex R X)` over a densely ordered strict
  ordered ring when `X` is nontrivial.
* `Convexity.StdSimplex.instUncountableReal`: `Uncountable (StdSimplex ℝ X)` when `X` is
  nontrivial.
-/

public section

namespace Convexity.StdSimplex

/-- Embed the closed unit interval `[0, 1]` injectively as the edge between two distinct vertices
of `StdSimplex R X`. -/
private theorem exists_injective_icc_to_stdSimplex {R X : Type*} [Ring R] [PartialOrder R]
    [IsStrictOrderedRing R] [Nontrivial X] :
    ∃ g : Set.Icc (0 : R) 1 → StdSimplex R X, Function.Injective g := by
  obtain ⟨x, y, hxy⟩ := exists_pair_ne X
  have hinj : Function.Injective ![x, y] := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  exact ⟨fun t ↦ (equivIcc.symm t).map ![x, y], (map_injective hinj).comp equivIcc.symm.injective⟩

/-- Over a densely ordered strict ordered ring (such as `ℚ` or `ℝ`), any standard simplex on a
type with at least two vertices is infinite. -/
instance instInfinite {R X : Type*} [Ring R] [PartialOrder R] [IsStrictOrderedRing R]
    [DenselyOrdered R] [Nontrivial X] : Infinite (StdSimplex R X) := by
  obtain ⟨g, hg⟩ := exists_injective_icc_to_stdSimplex (R := R) (X := X)
  have : Infinite (Set.Icc (0 : R) 1) := Set.Icc.infinite zero_lt_one
  exact Infinite.of_injective g hg

/-- Over `ℝ`, any standard simplex on a type with at least two vertices is uncountable. -/
instance instUncountableReal {X : Type*} [Nontrivial X] : Uncountable (StdSimplex ℝ X) := by
  obtain ⟨g, hg⟩ := exists_injective_icc_to_stdSimplex (R := ℝ) (X := X)
  refine ⟨fun hcount ↦ ?_⟩
  have hIcc : (Set.Icc (0 : ℝ) 1).Countable := Set.countable_coe_iff.mp hg.countable
  exact (Cardinal.Real.Icc_countable_iff.mp hIcc).not_gt zero_lt_one

end Convexity.StdSimplex
