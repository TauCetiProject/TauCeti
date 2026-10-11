/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Reductive.Over
public import TauCeti.Algebra.AlgebraicGroup.Symplectic.Reductive.Basic
import TauCeti.Algebra.AlgebraicGroup.Symplectic.BaseChange
import TauCeti.Algebra.AlgebraicGroup.Symplectic.Smooth

/-!
# The symplectic group is reductive over a ring

The standard symplectic group `Sp₂ₘ` is reductive over every commutative base ring, including
in characteristic two. Its coordinate algebra is smooth over the base, and every geometric
fiber is identified with the symplectic group constructed over that field. This supplies the
reductivity certificate for an integral symplectic pinning and its specializations.

The proof combines `Symplectic.smoothCommHopfAlgProperty_finiteTypeCoordinateHopfAlgebra`,
`Symplectic.finiteTypeCoordinateHopfAlgebraBaseChangeIso`, and the fieldwise reductivity theorem.
The assembly follows `TauCeti.Algebra.AlgebraicGroup.SpecialLinear.Reductive.Over`.

## References

* B. Conrad, *Reductive Group Schemes* (2014), Definition 3.1.1 and Example 3.2.3.
* J. S. Milne, *Algebraic Groups* (2017), §24.6.
-/

public section

open CategoryTheory

namespace TauCeti.Symplectic

universe u

/-- The standard symplectic group is reductive over every commutative base ring, in every
rank and without a restriction on characteristic. -/
theorem reductiveCommHopfAlgPropertyOver_finiteTypeCoordinateHopfAlgebra
    (R : Type u) [CommRing R] (m : ℕ) :
    reductiveCommHopfAlgPropertyOver R (finiteTypeCoordinateHopfAlgebra R m) := by
  rw [reductiveCommHopfAlgPropertyOver_iff]
  refine ⟨?_, ?_⟩
  · exact (smoothCommHopfAlgProperty_iff _).mp
      (smoothCommHopfAlgProperty_finiteTypeCoordinateHopfAlgebra R m)
  · intro k _ _ _
    exact (reductiveCommHopfAlgProperty k).prop_of_iso
      (finiteTypeCoordinateHopfAlgebraBaseChangeIso R k m).symm
      (reductiveCommHopfAlgProperty_finiteTypeCoordinateHopfAlgebra k m)

end TauCeti.Symplectic
