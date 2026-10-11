/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import TauCeti.Analysis.Complex.Circle
public import TauCeti.Topology.CWComplex.Classical.Sphere

/-!
# The circle has finite CW type

The unit circle `Circle` is the unit sphere of `ℂ` (`Circle.homeomorphSphere`), and an additive
circle `AddCircle p` of nonzero period is homeomorphic to it (`AddCircle.homeomorphCircle`).  The
minimal CW structure on spheres (`TauCeti.finiteCWType_sphere`) therefore gives both finite CW
type, and with `TauCeti.FiniteCWType.pi` so does every torus `∀ i, AddCircle (p i)` over a finite
index type.

## Main declarations

* `TauCeti.finiteCWType_circle`: `Circle` has finite CW type.
* `TauCeti.finiteCWType_addCircle`: `AddCircle p` has finite CW type for `p ≠ 0`.
-/

public section

namespace TauCeti

/-- The unit circle `Circle` has finite CW type, being the unit sphere of `ℂ`. -/
instance finiteCWType_circle : FiniteCWType Circle :=
  Circle.homeomorphSphere.finiteCWType

/-- An additive circle `AddCircle p` of nonzero period has finite CW type, being homeomorphic to
the unit circle. -/
instance finiteCWType_addCircle (p : ℝ) [NeZero p] : FiniteCWType (AddCircle p) :=
  (AddCircle.homeomorphCircle (NeZero.ne p)).finiteCWType

end TauCeti
