/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.LinearlyReductive
public import TauCeti.Algebra.AlgebraicGroup.ProjectiveGeneralLinear.Basic
import TauCeti.Algebra.AlgebraicGroup.SpecialLinear.CentralIsogeny
import TauCeti.Algebra.AlgebraicGroup.SpecialLinear.LinearlyReductive

/-!
# Complete reducibility for projective general linear groups in characteristic zero

Over a field of characteristic zero, every finite-dimensional representation of `PGLₙ`, the
automorphism group scheme of the matrix algebra `Mₙ`, is completely reducible, in every rank
including `n = 0`, that is, `PGLₙ` is linearly reductive. So its finite-dimensional
representations, such as its conjugation action on `Mₙ`, split into irreducible summands. In
positive characteristic this fails as soon as `n ≥ 2`.

## Main declaration

* `TauCeti.ProjectiveGeneralLinear.linearlyReductiveCommHopfAlgProperty_coordinateHopfAlgebra`:
  the coordinate Hopf algebra of `PGLₙ` is linearly reductive in characteristic zero.

## References

* J. S. Milne, *Algebraic Groups* (2017), Example 5.49 and §12.
-/

public section

namespace TauCeti

namespace ProjectiveGeneralLinear

universe u

variable (n : ℕ) (k : Type u) [Field k] [CharZero k]

/-- **`PGLₙ` is linearly reductive in characteristic zero.** Every finite-dimensional comodule
over its coordinate Hopf algebra is completely reducible. -/
theorem linearlyReductiveCommHopfAlgProperty_coordinateHopfAlgebra :
    linearlyReductiveCommHopfAlgProperty k (coordinateHopfAlgebra n k) :=
  .of_injective (SpecialLinear.conjugationMap n k) (SpecialLinear.injective_conjugationMap n k)
    (SpecialLinear.linearlyReductiveCommHopfAlgProperty_coordinateHopfAlgebra k n)

end ProjectiveGeneralLinear

end TauCeti
