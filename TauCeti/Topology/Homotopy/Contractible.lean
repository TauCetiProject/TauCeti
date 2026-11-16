/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Homotopy.Contractible
public import Mathlib.Topology.UnitInterval

import Mathlib.Analysis.Convex.Contractible
import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Additional `ContractibleSpace` instances

This file supplies two missing `ContractibleSpace` instances for Mathlib types:

* `unitInterval` is contractible, being a nonempty convex subset of `ℝ`
  (`Convex.contractibleSpace`).
* `ULift X` is contractible whenever `X` is contractible, via the homeomorphism
  `Homeomorph.ulift`.

Combined with Mathlib's product instance `ContractibleSpace (X × Y)`, these immediately yield
contractibility of universe-lifted intervals and cubes such as `ULift unitInterval` and
`ULift (unitInterval × unitInterval)`.
-/

public section

universe u v

namespace TauCeti

/-- The unit interval `unitInterval` is contractible. -/
instance : ContractibleSpace unitInterval :=
  (convex_Icc (0 : ℝ) 1).contractibleSpace ⟨0, unitInterval.zero_mem⟩

/-- A universe lift `ULift X` of a contractible space `X` is contractible. -/
instance {X : Type v} [TopologicalSpace X] [ContractibleSpace X] :
    ContractibleSpace (ULift.{u} X) :=
  Homeomorph.ulift.contractibleSpace

end TauCeti
