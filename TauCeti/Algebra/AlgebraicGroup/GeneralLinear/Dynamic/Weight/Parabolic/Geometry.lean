/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Dynamic.Weight.Levi.SemidirectProduct
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Weight.Levi.Geometry
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Weight.Unipotent.Geometry
import TauCeti.RingTheory.Smooth.GeometricallyReduced

/-!
# Geometry of general-linear weight parabolics

Every weight Levi has a localized block-coordinate presentation that makes it smooth and
geometrically connected. Combining these facts with the represented weight-parabolic Levi
decomposition

```text
U(w) ⋊ L(w) ≅ P(w)
```

shows that every weight parabolic is smooth over a commutative ring and geometrically connected
over a field. In particular, its coordinate Hopf algebra is reduced over a reduced ring.

## Main declarations

* `TauCeti.GeneralLinear.smoothCommHopfAlgProperty_weightParabolicCoordinateHopfAlgebra`:
  smoothness of a weight parabolic.
* `TauCeti.GeneralLinear.isReduced_weightParabolicCoordinateHopfAlgebra`: reducedness of a
  weight parabolic over a reduced ring.
* `TauCeti.GeneralLinear.
  geometricallyConnectedCommHopfAlgProperty_weightParabolicCoordinateHopfAlgebra`:
  geometric connectedness of a weight parabolic.

## References

* J. S. Milne, *Algebraic Groups* (2017), Chapters 12--13 and 17.
* T. A. Springer, *Linear Algebraic Groups*, Sections 6.2--6.3.
-/

public section

open CategoryTheory TauCeti.GeneralLinear.Dynamic

namespace TauCeti.GeneralLinear

universe u

noncomputable section

variable {N : ℕ}

/-- The coordinate Hopf algebra of a weight parabolic is smooth over every commutative ring. -/
theorem smoothCommHopfAlgProperty_weightParabolicCoordinateHopfAlgebra
    (R : Type u) [CommRing R] (w : Fin N → ℤ) :
    smoothCommHopfAlgProperty R (weightParabolicCoordinateHopfAlgebra R w) := by
  apply (smoothCommHopfAlgProperty R).prop_of_iso
    (Dynamic.weightParabolicSemidirectProductCoordinateIso R w).symm
  apply Dynamic.smoothCommHopfAlgProperty_weightParabolicSemidirectProductCoordinateHopfAlgebra
  · rw [smoothCommHopfAlgProperty_iff]
    infer_instance
  · rw [smoothCommHopfAlgProperty_iff]
    infer_instance

/-- The coordinate Hopf algebra of a weight parabolic over a reduced ring is reduced, since it
is smooth. -/
instance isReduced_weightParabolicCoordinateHopfAlgebra
    (R : Type u) [CommRing R] [IsReduced R] (w : Fin N → ℤ) :
    IsReduced (weightParabolicCoordinateHopfAlgebra R w) := by
  have := (smoothCommHopfAlgProperty_iff _).mp
    (smoothCommHopfAlgProperty_weightParabolicCoordinateHopfAlgebra R w)
  exact isReduced_of_smooth R _

/-- The coordinate Hopf algebra of a weight parabolic is geometrically connected over every
field. -/
theorem geometricallyConnectedCommHopfAlgProperty_weightParabolicCoordinateHopfAlgebra
    (k : Type u) [Field k] (w : Fin N → ℤ) :
    geometricallyConnectedCommHopfAlgProperty k
      (weightParabolicCoordinateHopfAlgebra k w) := by
  apply (geometricallyConnectedCommHopfAlgProperty k).prop_of_iso
    (Dynamic.weightParabolicSemidirectProductCoordinateIso k w).symm
  exact
    geometricallyConnectedCommHopfAlgProperty_weightParabolicSemidirectProductCoordinateHopfAlgebra
      k w (geometricallyConnectedCommHopfAlgProperty_weightUnipotentCoordinateHopfAlgebra k w)
      (geometricallyConnectedCommHopfAlgProperty_weightLeviCoordinateHopfAlgebra k w)

end

end TauCeti.GeneralLinear
