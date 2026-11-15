/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basis
public import Mathlib.RingTheory.RegularLocalRing.Polynomial

/-!
# The symmetric algebra of a finite free module over a regular ring is regular

Let `M` be a finite free module over a regular ring `R`. A basis of `M` identifies the symmetric
algebra `Sym M` with a polynomial ring over `R` in finitely many variables
(`SymmetricAlgebra.equivMvPolynomial`), which is regular
(`MvPolynomial.isRegularRing_of_isRegularRing`).
Over a field `k` this says that the polynomial functions `Sym(V*)` on a finite-dimensional vector
space `V` form a regular ring, so that their local ring at every point, in particular at the
origin, is a regular local ring. This is the regularity that descends to the invariants of a finite
group along a faithfully flat extension.
-/

public section

namespace TauCeti.SymmetricAlgebra

/-- The symmetric algebra of a finite free module over a regular ring is a regular ring. -/
instance isRegularRing (R M : Type*) [CommRing R] [IsRegularRing R] [AddCommMonoid M]
    [Module R M] [Module.Free R M] [Module.Finite R M] :
    IsRegularRing (_root_.SymmetricAlgebra R M) :=
  IsRegularRing.of_ringEquiv
    (_root_.SymmetricAlgebra.equivMvPolynomial (Module.Free.chooseBasis R M)).toRingEquiv.symm

end TauCeti.SymmetricAlgebra
