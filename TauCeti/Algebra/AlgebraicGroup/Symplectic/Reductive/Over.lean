/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Reductive.Over
public import TauCeti.Algebra.AlgebraicGroup.Symplectic.Reductive.Basic
import TauCeti.Algebra.AlgebraicGroup.Symplectic.Semisimple.Over

/-!
# The symplectic group is reductive over a ring

The standard symplectic group `Sp₂ₘ` is reductive over every commutative base ring, including
in characteristic two. Its coordinate algebra is smooth over the base, and every geometric
fiber is identified with the symplectic group constructed over that field. This supplies the
reductivity certificate for an integral symplectic pinning and its specializations.

The proof deduces it from semisimplicity over the base,
`Symplectic.semisimpleCommHopfAlgPropertyOver_finiteTypeCoordinateHopfAlgebra`, as in
`TauCeti.Algebra.AlgebraicGroup.SpecialLinear.Reductive.Over`.

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
    reductiveCommHopfAlgPropertyOver R (finiteTypeCoordinateHopfAlgebra R m) :=
  (semisimpleCommHopfAlgPropertyOver_finiteTypeCoordinateHopfAlgebra R m).reductive

end TauCeti.Symplectic
