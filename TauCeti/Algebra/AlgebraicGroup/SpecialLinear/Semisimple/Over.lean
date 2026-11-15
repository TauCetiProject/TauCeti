/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Semisimple.Over
public import TauCeti.Algebra.AlgebraicGroup.SpecialLinear.Basic
import TauCeti.Algebra.AlgebraicGroup.SpecialLinear.BaseChange
import TauCeti.Algebra.AlgebraicGroup.SpecialLinear.Semisimple.Basic
import TauCeti.Algebra.AlgebraicGroup.SpecialLinear.Smooth

/-!
# The special linear group is semisimple over a ring

`SL_n` is a semisimple group scheme over every commutative ring, in every rank and without a
restriction on characteristic. Its coordinate algebra is smooth over the base, and every
geometric fiber is identified with the special linear group over that field, which is semisimple
by `TauCeti.SpecialLinear.semisimpleCommHopfAlgProperty_finiteTypeCoordinateHopfAlgebra`.

## References

* B. Conrad, *Reductive Group Schemes* (2014), Definition 3.1.1.
* J. E. Humphreys, *Linear Algebraic Groups*, §§19 and 27.
-/

public section

open CategoryTheory

namespace TauCeti.SpecialLinear

universe u

/-- **The special linear group is semisimple over every commutative base ring**, in every rank and
without a restriction on characteristic: it is smooth over the base and each geometric fiber is
the special linear group over that field. -/
theorem semisimpleCommHopfAlgPropertyOver_finiteTypeCoordinateHopfAlgebra
    (R : Type u) [CommRing R] (n : ℕ) :
    semisimpleCommHopfAlgPropertyOver R (finiteTypeCoordinateHopfAlgebra R n) := by
  rw [semisimpleCommHopfAlgPropertyOver_iff]
  refine ⟨?_, fun k _ _ _ ↦ ?_⟩
  · exact (smoothCommHopfAlgProperty_iff _).mp
      (smoothCommHopfAlgProperty_finiteTypeCoordinateHopfAlgebra R n)
  · exact (semisimpleCommHopfAlgProperty k).prop_of_iso
      (finiteTypeCoordinateHopfAlgebraBaseChangeIso R k n).symm
      (semisimpleCommHopfAlgProperty_finiteTypeCoordinateHopfAlgebra k n)

end TauCeti.SpecialLinear
