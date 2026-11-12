/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Reductive.Basic
public import TauCeti.Algebra.AlgebraicGroup.Reductive.Over

/-!
# The general linear group is reductive over a ring

The general linear group `GL_n` is a reductive affine group scheme over every commutative
base ring, in every natural rank. In particular, the integral general linear group and all
its specializations satisfy the reductivity condition used by a pinning.

Smoothness over the base is supplied by `GeneralLinear.instSmoothCoordinateHopfAlgebra`.
The canonical `GeneralLinear.finiteTypeCoordinateHopfAlgebraBaseChangeIso` identifies every
geometric fiber with the general linear group over that field, where
`GeneralLinear.reductiveCommHopfAlgProperty_finiteTypeCoordinateHopfAlgebra` proves
reductivity in arbitrary characteristic. No reducedness or connectedness of the base ring
is required.

The assembly follows `TauCeti.Algebra.AlgebraicGroup.SpecialLinear.Reductive.Over` and
`TauCeti.Algebra.AlgebraicGroup.Symplectic.Reductive.Over`.

## References

* B. Conrad, *Reductive Group Schemes* (2014), Definition 3.1.1 and Example 3.2.3.
* J. S. Milne, *Algebraic Groups* (2017), Chapter 19.
-/

public section

open CategoryTheory

namespace TauCeti.GeneralLinear

universe u

/-- The general linear group is reductive over every commutative base ring, in every rank
and without a restriction on characteristic. -/
theorem reductiveCommHopfAlgPropertyOver_finiteTypeCoordinateHopfAlgebra
    (R : Type u) [CommRing R] (n : ℕ) :
    reductiveCommHopfAlgPropertyOver R (finiteTypeCoordinateHopfAlgebra R n) := by
  rw [reductiveCommHopfAlgPropertyOver_iff]
  refine ⟨?_, ?_⟩
  · rw [← smoothCommHopfAlgProperty_iff, finiteTypeCoordinateHopfAlgebra_obj]
    exact (smoothCommHopfAlgProperty_iff _).mpr inferInstance
  · intro k _ _ _
    exact (reductiveCommHopfAlgProperty k).prop_of_iso
      (finiteTypeCoordinateHopfAlgebraBaseChangeIso R k n).symm
      (reductiveCommHopfAlgProperty_finiteTypeCoordinateHopfAlgebra k n)

end TauCeti.GeneralLinear
