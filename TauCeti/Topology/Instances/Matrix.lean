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

Mathlib gives `Matrix m n α` the product topology of `m → n → α`, so for finite index types it is
pseudo-metrizable whenever `α` is. This makes metrizable-codomain results, such as measurability
of pointwise limits of measurable maps, available for matrix-valued functions without choosing a
matrix norm.
-/

public section

namespace TauCeti

/-- A space of matrices with finitely many rows and columns over a pseudo-metrizable space is
pseudo-metrizable. -/
instance {m n α : Type*} [Finite m] [Finite n] [TopologicalSpace α]
    [TopologicalSpace.PseudoMetrizableSpace α] :
    TopologicalSpace.PseudoMetrizableSpace (Matrix m n α) :=
  -- The topology of `Matrix m n α` is by definition the product topology on `m → n → α`.
  inferInstanceAs (TopologicalSpace.PseudoMetrizableSpace (m → n → α))

end TauCeti
