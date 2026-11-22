/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Valued.NormedValued
public import Mathlib.Topology.Algebra.Valued.ValuationTopology
public import TauCeti.RingTheory.Valuation.Continuous.Basic

/-!
# The canonical valuation of a valued or normed ring is continuous

A `Valued R Γ₀` structure carries the topology defined by its valuation, and `Valued.isOpen_ball`
gives that every ball `{a | v a < γ}` is open. In particular the sets `{a | v a < v b}` cut out by
the *attained* values are open, which is exactly `Valuation.IsContinuous` for `Valued.v`.

For an ultrametric normed field `K`, `NormedField.toValued` identifies the norm topology with the
valuation topology of `NormedField.valuation`, so `NormedField.valuation` is continuous as well.

## Main results

* `Valued.isContinuous_v` : the valuation of a `Valued` ring is continuous.
* `NormedField.isContinuous_valuation` : the norm valuation on an ultrametric normed field is
  continuous.
-/

public section

namespace Valued

open Valuation

variable {R : Type*} [Ring R] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] [Valued R Γ₀]

/-- The valuation of a `Valued` ring is continuous for the topology it defines. -/
theorem isContinuous_v : (Valued.v : Valuation R Γ₀).IsContinuous :=
  isContinuous_def.mpr fun b ↦ by simpa using Valued.isOpen_ball R (Valued.v.restrict b)

end Valued

namespace NormedField

open Valuation
open scoped NNReal

/-- The norm valuation on an ultrametric normed field is continuous for the norm topology. -/
theorem isContinuous_valuation {K : Type*} [NormedField K] [IsUltrametricDist K] :
    (NormedField.valuation (K := K)).IsContinuous := by
  let : Valued K ℝ≥0 := NormedField.toValued
  exact Valued.isContinuous_v (R := K) (Γ₀ := ℝ≥0)

end NormedField
