/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Homotopy.Contractible

/-!
# Contractible spaces

The lift `ULift X` of a contractible space `X` to a higher universe is contractible, since
`Homeomorph.ulift` identifies it with `X`.

Any two continuous maps into a contractible space are homotopic
(`ContinuousMap.homotopic_of_contractibleSpace`): both are homotopic to the constant map at the
point the identity contracts onto.
-/

public section

universe u v

namespace ULift

variable {X : Type u} [TopologicalSpace X]

/-- The lift of a contractible space to a higher universe is contractible. -/
instance contractibleSpace [ContractibleSpace X] : ContractibleSpace (ULift.{v} X) :=
  Homeomorph.ulift.contractibleSpace

end ULift

namespace ContinuousMap

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- Any two continuous maps into a contractible space are homotopic. -/
theorem homotopic_of_contractibleSpace [ContractibleSpace Y] (f g : C(X, Y)) : f.Homotopic g := by
  obtain ⟨c, hc⟩ := id_nullhomotopic Y
  have h (f : C(X, Y)) : f.Homotopic (const X c) := by
    have := hc.comp (Homotopic.refl f)
    rwa [id_comp, const_comp] at this
  exact (h f).trans (h g).symm

end ContinuousMap
