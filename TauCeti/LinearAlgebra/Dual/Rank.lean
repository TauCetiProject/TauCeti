/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
public import TauCeti.LinearAlgebra.Dual.BaseChange

/-!
# Local rank of the dual of a finite projective module

The linear dual of a finite projective module has the same rank at every prime of the base
ring. This is the module-theoretic rank identity underlying preservation of rank by Cartier
duality, including over disconnected and nonreduced bases.

The argument uses the scalar-extension evaluation equivalence from
`TauCeti.LinearAlgebra.Dual.BaseChange` and Mathlib's dimension formula for linear duals.
-/

public section

namespace TauCeti.Module

/-- A finite projective module and its linear dual have the same rank at every prime. -/
@[simp]
theorem rankAtStalk_dual (R M : Type*) [CommRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Module.Projective R M] :
    Module.rankAtStalk (R := R) (Module.Dual R M) = Module.rankAtStalk M := by
  ext p
  rw [Module.rankAtStalk_eq, Module.rankAtStalk_eq]
  exact (Dual.baseChangeEvaluationEquiv
    (R := R) (A := p.asIdeal.ResidueField) (M := M)).finrank_eq.trans
      Subspace.dual_finrank_eq

end TauCeti.Module
