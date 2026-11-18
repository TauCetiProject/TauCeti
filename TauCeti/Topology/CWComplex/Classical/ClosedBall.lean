/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Connected
public import TauCeti.Topology.CWComplex.Classical.FiniteCWType

/-!
# Closed balls and closed intervals have finite CW type

A closed ball of nonnegative radius in a real normed space is contractible, and a closed ball of
negative radius is empty, so closed balls have finite CW type for every radius. A closed interval
of `ℝ` is a closed ball, so it has finite CW type for all endpoints.

## Main declarations

* `TauCeti.finiteCWType_closedBall`: every closed ball of a real normed space has finite CW type.
* `TauCeti.finiteCWType_Icc`: every closed interval of `ℝ` has finite CW type.
-/

public section

open Metric

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A closed ball in a real normed space has finite CW type: it is contractible for a nonnegative
radius and empty otherwise. -/
instance finiteCWType_closedBall (x : E) (r : ℝ) : FiniteCWType (closedBall x r) := by
  rcases le_or_gt 0 r with hr | hr
  · have := contractibleSpace_closedBall (x := x) hr
    infer_instance
  · have : IsEmpty (closedBall x r) := by
      rw [Set.isEmpty_coe_sort, closedBall_eq_empty]
      exact hr
    exact FiniteCWType.of_discreteTopology _

/-- A closed interval of `ℝ` has finite CW type, being a closed ball. -/
instance finiteCWType_Icc (a b : ℝ) : FiniteCWType (Set.Icc a b) := by
  rw [Real.Icc_eq_closedBall]
  infer_instance

end TauCeti
