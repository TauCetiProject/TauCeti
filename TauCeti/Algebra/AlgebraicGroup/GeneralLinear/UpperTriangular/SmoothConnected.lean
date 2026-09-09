/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Dynamic.Weight.Parabolic.Geometry
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.UpperTriangular.Basic

/-!
# Geometry of the upper-triangular subgroup scheme

The standard upper-triangular subgroup of `GL_n` is the weight parabolic for the strictly
decreasing weights `i ↦ n - 1 - i`. This file specializes the general geometry of weight
parabolics to establish smoothness and geometric connectedness of the upper-triangular group
over an arbitrary commutative ring for smoothness and over a field for geometric connectedness.

## Main declarations

* `TauCeti.GeneralLinear.UpperTriangular.smoothCommHopfAlgProperty_coordinateHopfAlgebra`:
  the upper-triangular coordinate Hopf algebra is smooth.
* `TauCeti.GeneralLinear.UpperTriangular.
    geometricallyConnectedCommHopfAlgProperty_coordinateHopfAlgebra`:
  the upper-triangular coordinate Hopf algebra is geometrically connected.

## References

* J. S. Milne, *Algebraic Groups* (2017), Chapters 12--13 and 17.
* T. A. Springer, *Linear Algebraic Groups*, Sections 6.2--6.3.
-/

public section

namespace TauCeti.GeneralLinear

universe u

noncomputable section

namespace UpperTriangular

variable (n : ℕ)

/-- **The standard upper-triangular subgroup of `GL_n` is smooth over every commutative ring.** -/
theorem smoothCommHopfAlgProperty_coordinateHopfAlgebra
    (R : Type u) [CommRing R] :
    smoothCommHopfAlgProperty R (coordinateHopfAlgebra R n) :=
  smoothCommHopfAlgProperty_weightParabolicCoordinateHopfAlgebra
    R (weights n)

/-- **The standard upper-triangular subgroup of `GL_n` is geometrically connected over every
field.** -/
theorem geometricallyConnectedCommHopfAlgProperty_coordinateHopfAlgebra
    (k : Type u) [Field k] :
    geometricallyConnectedCommHopfAlgProperty k (coordinateHopfAlgebra k n) :=
  geometricallyConnectedCommHopfAlgProperty_weightParabolicCoordinateHopfAlgebra
    k (weights n)

end UpperTriangular

end

end TauCeti.GeneralLinear
