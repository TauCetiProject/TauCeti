/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.ZLattice.ModelShell
public import TauCeti.NumberTheory.ModularForms.ThetaSeries.QExpansion

/-!
# Theta coefficients of a rational lattice's real model

For a positive definite integral lattice `M`, the coefficients of the theta series of
`M.realModel hM` are the rational lattice's existing representation numbers. For an even lattice
the coefficient of `q^m`, with `q = exp (2 π i τ)`, is `M.representationNumber (2 * m)`.
For any integral lattice the period-two coefficient is `M.representationNumber m`.

These statements combine the real theta expansion with the shell comparison under scalar
extension. They let computations in the rational model supply coefficients for analytic theta
identities without choosing Euclidean coordinates or recounting vectors.

## References

* W. Ebeling, *Lattices and Codes*, Chapter 2.
-/

public section

open scoped UpperHalfPlane

namespace TauCeti.IntegralLattice

variable {V : Type*} [AddCommGroup V] [Module ℚ V]
  (M : IntegralLattice V) (hM : M.IsPosDef)

/-- The period-two theta coefficients of the real model count rational lattice vectors of norm
`m`. This applies to odd as well as even integral lattices. -/
theorem qExpansion_two_thetaSeries_realModel_coeff (m : ℕ) :
    (UpperHalfPlane.qExpansion 2 (ZLattice.thetaSeries (M.realModel hM))).coeff m =
      (M.representationNumber m : ℂ) := by
  rw [(M.isIntegral_realModel hM).qExpansion_two_thetaSeries_coeff]
  norm_cast
  exact_mod_cast M.representationNumber_realModel hM (m : ℚ)

/-- For an even rational lattice, the coefficient of `q^m` in the theta series of its real
model counts vectors of rational norm `2 * m`. -/
theorem IsEven.qExpansion_thetaSeries_realModel_coeff {M : IntegralLattice V} (hE : M.IsEven)
    (hM : M.IsPosDef) (m : ℕ) :
    (UpperHalfPlane.qExpansion 1 (ZLattice.thetaSeries (M.realModel hM))).coeff m =
      (M.representationNumber (2 * m) : ℂ) := by
  rw [((M.isEven_realModel_iff hM).mpr hE).qExpansion_thetaSeries_coeff]
  norm_cast
  exact_mod_cast M.representationNumber_realModel hM (2 * m : ℚ)

end TauCeti.IntegralLattice
