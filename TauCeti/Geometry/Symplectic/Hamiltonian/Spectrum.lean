/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.Quadratic
public import TauCeti.Geometry.Symplectic.Spectrum

/-!
# The characteristic polynomial of a quadratic Hamiltonian

The Hamiltonian endomorphism of a quadratic Hamiltonian lies in the symplectic Lie algebra, so
its characteristic polynomial is even. The general symplectic spectral results are in
`TauCeti.Geometry.Symplectic.Spectrum`.
-/

public section

open Polynomial

namespace TauCeti.SymplecticForm

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
  (ω : SymplecticForm V)

/-- The Hamiltonian endomorphism of a quadratic Hamiltonian has an even characteristic
polynomial. -/
theorem charpoly_hamiltonianEnd_comp_neg_X (Q : QuadraticForm ℝ V) :
    (ω.hamiltonianEnd Q).charpoly.comp (-X) = (ω.hamiltonianEnd Q).charpoly :=
  ω.charpoly_comp_neg_X (ω.hamiltonianEnd_mem_skewAdjointLieSubalgebra Q)

end TauCeti.SymplecticForm
