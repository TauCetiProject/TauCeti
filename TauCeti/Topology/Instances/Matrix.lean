/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.Metrizable.Basic

/-!
# Metrizability of the space of matrices

Mathlib gives `Matrix m n R` the product topology of `m → n → R`, but registers only some of the
topological instances that the product carries. This file adds pseudo-metrizability, for
finite index types. With it, a continuous matrix-valued function is almost everywhere strongly
measurable (`Continuous.aestronglyMeasurable`), which is how continuous coefficient fields of
partial differential operators enter integral estimates.
-/

public section

namespace TauCeti

variable {m n R : Type*} [TopologicalSpace R]

/-- Matrices over a pseudo-metrizable space, indexed by finite types, form a
pseudo-metrizable space: their topology is the product topology of `m → n → R`. -/
instance [Finite m] [Finite n] [TopologicalSpace.PseudoMetrizableSpace R] :
    TopologicalSpace.PseudoMetrizableSpace (Matrix m n R) :=
  inferInstanceAs (TopologicalSpace.PseudoMetrizableSpace (m → n → R))

end TauCeti
