/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Homotopy.Contractible

/-!
# Contractibility of lifts to higher universes

The lift `ULift X` of a contractible space `X` to a higher universe is contractible, since
`Homeomorph.ulift` identifies it with `X`.
-/

public section

universe u v

namespace ULift

variable {X : Type u} [TopologicalSpace X]

/-- The lift of a contractible space to a higher universe is contractible. -/
instance contractibleSpace [ContractibleSpace X] : ContractibleSpace (ULift.{v} X) :=
  Homeomorph.ulift.contractibleSpace

end ULift
