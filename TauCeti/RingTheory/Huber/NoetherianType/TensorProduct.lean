/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.NoetherianType.Basic
public import TauCeti.RingTheory.Huber.TensorProduct.FiniteAlgebra
import TauCeti.RingTheory.Huber.NoetherianType.ModuleTopology

/-!
# Completed base change of finite algebras over noetherian-type rings

For a module-finite `A`-algebra `B` carrying its natural `A`-module topology and a complete
Hausdorff Huber `A`-algebra `C` of noetherian type, the canonical comparison
`C ⊗[A] B → CompletedTensor A C B` is bijective
(`TauCeti.Huber.CompletedTensor.toCompletion_bijective_of_isNoetherianType`).
-/

public section

open TensorProduct

namespace TauCeti.Huber

/-- For a module-finite `A`-algebra `B` carrying the `A`-module topology and a complete Hausdorff
Huber `A`-algebra `C` of noetherian type, the canonical map
`C ⊗[A] B → CompletedTensor A C B` is bijective. -/
theorem CompletedTensor.toCompletion_bijective_of_isNoetherianType
    (A C B : Type*) [CommRing A] [CommRing C] [CommRing B] [Algebra A C] [Algebra A B]
    [TopologicalSpace A] [IsTopologicalRing A] [UniformSpace C] [IsUniformAddGroup C]
    [IsTopologicalRing C] [IsHuberRing C] [CompleteSpace C] [T0Space C] [IsNoetherianType C]
    [TopologicalSpace B] [IsTopologicalRing B] [IsModuleTopology A B] [Module.Finite A B]
    [IsAdicHom (algebraMap A C)] [IsAdicHom (algebraMap A B)] :
    Function.Bijective (CompletedTensor.toCompletion A C B) :=
  CompletedTensor.toCompletion_bijective_of_isNaturallyComplete A C B
    (IsNoetherianType.isNaturallyComplete (A := C) (M := C ⊗[A] B))

end TauCeti.Huber
