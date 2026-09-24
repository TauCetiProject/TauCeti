/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Lipschitz.Norm
public import TauCeti.LinearAlgebra.CliffordAlgebra.Pin.Basic
import TauCeti.LinearAlgebra.CliffordAlgebra.Basic

/-!
# The Clifford norm on the Pin group

The Clifford norm of a Pin element is one after including it in the Lipschitz group. This module
compares the general Lipschitz norm with the Pin inclusion, supplying the norm-one input used to
descend the Clifford norm to a spinor norm and to characterize the image of Spin in the special
orthogonal group.
-/

public section

namespace CliffordAlgebra

universe u v

variable {R : Type u} {V : Type v} [CommRing R] [AddCommGroup V] [Module R V]
  [Invertible (2 : R)]

/-- The Clifford norm of a Pin element is one. -/
@[simp]
theorem lipschitzNorm_pinToLipschitz (Q : QuadraticForm R V) (p : pinGroup Q) :
    lipschitzNorm Q (pinToLipschitz Q p) = 1 := by
  apply Units.ext
  apply algebraMap_injective Q
  rw [← star_mul_self_eq_algebraMap_lipschitzNorm]
  simpa only [coe_pinToLipschitz_apply, Units.val_one, map_one] using
    pinGroup.coe_star_mul_self p

end CliffordAlgebra
