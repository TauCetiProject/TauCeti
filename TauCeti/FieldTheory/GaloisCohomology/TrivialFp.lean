/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.AbsoluteGaloisGroup
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import TauCeti.RepresentationTheory.Homological.ContCohomology.TrivialFp.Zero

/-!
# Absolute Galois cohomology with trivial `ZMod p` coefficients

Zeroth continuous cohomology of the absolute Galois group with trivial coefficients has
dimension one. The canonical coefficient identification is
`TauCeti.cohomFpZeroLinearEquiv p (Field.absoluteGaloisGroup K)`, and finite generation is
provided by the corresponding `Module.Finite` instance. At prime `p`, this is the
finite-dimensional `𝔽_p`-vector space `H⁰(G_K, 𝔽_p)`.
-/

public section

namespace TauCeti

universe u

variable (p : ℕ) (K : Type u) [Field K]

/-- Zeroth absolute Galois cohomology with trivial `ZMod p` coefficients has dimension one. -/
theorem finrank_cohomFp_zero_absoluteGaloisGroup :
    Module.finrank (ZMod p) (cohomFp p (Field.absoluteGaloisGroup K) 0) = 1 :=
  (cohomFpZeroLinearEquiv p (Field.absoluteGaloisGroup K)).finrank_eq.trans
    (CommSemiring.finrank_self (ZMod p))

end TauCeti
