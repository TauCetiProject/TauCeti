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

In characteristic zero every finite-dimensional representation of `PGLₙ` is completely reducible.
The conjugation homomorphism `SLₙ → PGLₙ` is schematically dominant over every base ring, that
is, its coordinate morphism `O(PGLₙ) → O(SLₙ)` is injective
(`TauCeti.SpecialLinear.injective_conjugationMap`). A representation of `PGLₙ` is therefore a
representation of `SLₙ` with the same subrepresentations, and `SLₙ` is linearly reductive in
characteristic zero by
`TauCeti.SpecialLinear.linearlyReductiveCommHopfAlgProperty_coordinateHopfAlgebra`. The transfer
along an injective coordinate morphism is
`TauCeti.linearlyReductiveCommHopfAlgProperty.of_injective`.

No Lie-algebraic input is needed beyond the special linear case, and the statement holds in every
rank, including `n = 0`.

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
