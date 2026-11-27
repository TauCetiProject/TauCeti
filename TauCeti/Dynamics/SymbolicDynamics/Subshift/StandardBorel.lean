/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Dynamics.SymbolicDynamics.Subshift
public import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-!
# Standard Borel structure on subshifts

A subshift is a measurable subset of its configuration space whenever open sets of that space
are measurable. If the configuration space is standard Borel, its subshift is therefore standard
Borel as well. In particular, this applies over countably many sites with a Polish Borel alphabet,
and with a countable discrete alphabet equipped with its discrete σ-algebra.
-/

public section

namespace TauCeti.Subshift

variable {Γ I S : Type*} [Group Γ] [MulAction Γ I] [TopologicalSpace S] [MeasurableSpace S]
  {X : Subshift Γ I S}

/-- A subshift is standard Borel when its configuration space is standard Borel and its open sets
are measurable. -/
instance instStandardBorelSpace [StandardBorelSpace (I → S)]
    [OpensMeasurableSpace (I → S)] : StandardBorelSpace X :=
  X.measurableSet_coe.standardBorel

end TauCeti.Subshift
