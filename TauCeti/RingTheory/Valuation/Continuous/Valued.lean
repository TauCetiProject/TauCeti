/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Valued.ValuationTopology
public import TauCeti.RingTheory.Valuation.Continuous.Basic

/-!
# The canonical valuation of a valued ring is continuous

A `Valued R Γ₀` structure carries the topology defined by its valuation, and `Valued.isOpen_ball`
gives that every ball `{a | v a < γ}` is open. In particular the sets `{a | v a < v b}` cut out by
the *attained* values are open, which is exactly `Valuation.IsContinuous` for `Valued.v`.

## Main results

* `Valued.isContinuous_v` : the valuation of a `Valued` ring is continuous.
-/

public section

namespace Valued

open Valuation

variable {R : Type*} [Ring R] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] [Valued R Γ₀]

/-- The valuation of a `Valued` ring is continuous for the topology it defines. -/
theorem isContinuous_v : (Valued.v : Valuation R Γ₀).IsContinuous :=
  isContinuous_def.mpr fun b ↦ by simpa using Valued.isOpen_ball R (Valued.v.restrict b)

end Valued
