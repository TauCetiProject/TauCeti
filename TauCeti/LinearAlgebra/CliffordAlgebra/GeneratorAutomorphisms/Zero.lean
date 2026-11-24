/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.GeneratorAutomorphisms.Basic
public import TauCeti.LinearAlgebra.CliffordAlgebra.Zero

/-!
# Vector-preserving automorphisms on the zero module

When `M` is subsingleton, the Clifford algebra `CliffordAlgebra Q` is `R`: the identity is its
only automorphism, and it lies in the vector stabilizer
(`CliffordAlgebra.vectorStabilizer_eq_top_of_subsingleton`).
-/

public section

universe u v

namespace CliffordAlgebra

/-- **The case `M = 0`.** When `M` is subsingleton, the only automorphism of `CliffordAlgebra Q`
is the identity, and it maps the vectors onto themselves. -/
theorem vectorStabilizer_eq_top_of_subsingleton {R : Type u} [CommRing R] {M : Type v}
    [AddCommGroup M] [Module R M] [Subsingleton M] (Q : QuadraticForm R M) :
    vectorStabilizer Q = ⊤ :=
  Subsingleton.elim _ _

end CliffordAlgebra
