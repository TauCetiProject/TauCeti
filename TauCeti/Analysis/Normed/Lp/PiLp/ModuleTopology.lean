/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Lp.PiLp
public import Mathlib.Topology.Algebra.Module.ModuleTopology

/-!
# The module topology on finite `Lᵖ` products

The product topology carried by `PiLp` is the module topology whenever the index type is
finite and each factor carries its module topology. This follows by transport along
`PiLp.continuousLinearEquiv` from the module topology on the corresponding product.
-/

public section

open scoped ENNReal

namespace PiLp

/-- A finite `Lᵖ` product of spaces with the module topology carries the module topology. -/
instance instIsModuleTopology {R ι : Type*} [Semiring R] [TopologicalSpace R] [Finite ι]
    {β : ι → Type*} [∀ i, AddCommGroup (β i)] [∀ i, Module R (β i)]
    [∀ i, TopologicalSpace (β i)] [∀ i, IsModuleTopology R (β i)] (p : ℝ≥0∞) :
    IsModuleTopology R (PiLp p β) :=
  IsModuleTopology.iso (PiLp.continuousLinearEquiv p R β).symm

end PiLp
