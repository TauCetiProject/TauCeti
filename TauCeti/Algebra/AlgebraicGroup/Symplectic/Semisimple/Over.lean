/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Semisimple.Over
public import TauCeti.Algebra.AlgebraicGroup.Symplectic.Basic
import TauCeti.Algebra.AlgebraicGroup.Symplectic.BaseChange
import TauCeti.Algebra.AlgebraicGroup.Symplectic.Semisimple.Basic
import TauCeti.Algebra.AlgebraicGroup.Symplectic.Smooth

/-!
# The symplectic group is semisimple over a ring

The standard symplectic group `Sp₂ₘ` is a semisimple group scheme over every commutative ring, in
every rank and without a restriction on characteristic. Its coordinate algebra is smooth over the
base, and every geometric fiber is identified with the symplectic group over that field, which is
semisimple by `TauCeti.Symplectic.semisimpleCommHopfAlgProperty_finiteTypeCoordinateHopfAlgebra`.

## References

* B. Conrad, *Reductive Group Schemes* (2014), Definition 3.1.1 and Example 3.2.3.
* J. S. Milne, *Algebraic Groups* (2017), §24.6.
-/

public section

open CategoryTheory

namespace TauCeti.Symplectic

universe u

/-- **The standard symplectic group is semisimple over every commutative base ring**, in every
rank and without a restriction on characteristic: it is smooth over the base and each geometric
fiber is the standard symplectic group over that field. -/
theorem semisimpleCommHopfAlgPropertyOver_finiteTypeCoordinateHopfAlgebra
    (R : Type u) [CommRing R] (m : ℕ) :
    semisimpleCommHopfAlgPropertyOver R (finiteTypeCoordinateHopfAlgebra R m) := by
  rw [semisimpleCommHopfAlgPropertyOver_iff]
  refine ⟨?_, fun k _ _ _ ↦ ?_⟩
  · exact (smoothCommHopfAlgProperty_iff _).mp
      (smoothCommHopfAlgProperty_finiteTypeCoordinateHopfAlgebra R m)
  · exact (semisimpleCommHopfAlgProperty k).prop_of_iso
      (finiteTypeCoordinateHopfAlgebraBaseChangeIso R k m).symm
      (semisimpleCommHopfAlgProperty_finiteTypeCoordinateHopfAlgebra k m)

end TauCeti.Symplectic
