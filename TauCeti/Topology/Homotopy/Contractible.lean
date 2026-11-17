/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Homotopy.Contractible

/-!
# Maps into a contractible space

Any two continuous maps into a contractible space are homotopic
(`ContinuousMap.homotopic_of_contractibleSpace`): both are homotopic to the constant map at the
point the identity contracts onto.
-/

public section

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
