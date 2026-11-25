/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.BaseChange.Semisimple
public import TauCeti.RepresentationTheory.Continuous.ContinuousRep

/-!
# Semisimple continuous representations stay semisimple under base change

Over a perfect topological field `k`, the base change of a finite-dimensional continuous
representation whose underlying representation is semisimple has semisimple underlying
representation (`TauCeti.ContinuousRep.isSemisimpleRepresentation_baseChange`), by
`Representation.isSemisimpleRepresentation_baseChange`.

## Main results

* `TauCeti.ContinuousRep.isSemisimpleRepresentation_baseChange`.
-/

public section

open scoped TensorProduct

namespace TauCeti.ContinuousRep

variable {Γ k V : Type*} [Monoid Γ] [TopologicalSpace Γ] [Field k] [PerfectField k]
  [TopologicalSpace k] [AddCommGroup V] [Module k V] [TopologicalSpace V] [IsModuleTopology k V]
  [FiniteDimensional k V]

/-- **Semisimplicity of a continuous representation is preserved by base change over a perfect
field**: the underlying representation of `ρ.baseChange L` is semisimple when that of `ρ` is. -/
instance isSemisimpleRepresentation_baseChange (ρ : ContinuousRep Γ k V)
    [ρ.toRepresentation.IsSemisimpleRepresentation] (L : Type*) [Field L] [TopologicalSpace L]
    [IsTopologicalSemiring L] [Algebra k L] [ContinuousSMul k L] [TopologicalSpace (L ⊗[k] V)]
    [IsModuleTopology L (L ⊗[k] V)] :
    (ρ.baseChange L).toRepresentation.IsSemisimpleRepresentation := by
  rw [toRepresentation_baseChange]
  infer_instance

end TauCeti.ContinuousRep
