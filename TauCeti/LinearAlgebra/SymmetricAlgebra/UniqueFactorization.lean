/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basis
public import Mathlib.RingTheory.Polynomial.UniqueFactorization

/-!
# Unique factorization in a symmetric algebra

The symmetric algebra of a free module over a unique factorization domain is a unique
factorization domain. This allows relatively prime homogeneous factors to be combined in
polynomial divisibility arguments. The instance transports Mathlib's multivariate polynomial
instance along `SymmetricAlgebra.equivMvPolynomial`; the basis need not be finite.
-/

public section

namespace SymmetricAlgebra

/-- The symmetric algebra of a free module over a UFD is a UFD. -/
noncomputable instance uniqueFactorizationMonoid {R M : Type*} [CommRing R]
    [UniqueFactorizationMonoid R] [AddCommGroup M] [Module R M] [Module.Free R M] :
    UniqueFactorizationMonoid (SymmetricAlgebra R M) :=
  (equivMvPolynomial (Module.Free.chooseBasis R M)).symm.toMulEquiv.uniqueFactorizationMonoid
    inferInstance

end SymmetricAlgebra
