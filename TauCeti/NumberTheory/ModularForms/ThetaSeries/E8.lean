/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.ZLattice.ModelShell
public import TauCeti.LinearAlgebra.IntegralLattice.RootLattice.TypeE.Basic
public import TauCeti.NumberTheory.ModularForms.ThetaSeries.Eisenstein

/-!
# The theta series of E₈

The real model of `TauCeti.IntegralLattice.typeE₈RootLattice` has theta series `E₄`.
Consequently its rational norm shells satisfy `r(2m) = 240 σ₃(m)` for every positive `m`.
In particular, the value `240` at norm two follows from the Eisenstein coefficients, without
using the enumeration of E₈ roots.

The lattice is the existing Cartan-matrix lattice, not a new coordinate construction. Its
positive definiteness, evenness and unimodularity pass through `IntegralLattice.realModel`;
the identity then follows from `ZLattice.IsEven.thetaSeries_eq_E₄` for arbitrary even
unimodular lattices of rank eight. The shell comparison
`IntegralLattice.representationNumber_realModel` transfers the coefficients back to the
rational lattice.

## Main results

* `TauCeti.IntegralLattice.thetaSeries_realModel_typeE₈RootLattice`: `Θ_{E₈} = E₄`.
* `TauCeti.IntegralLattice.representationNumber_typeE₈RootLattice_two_mul`:
  `r_{E₈}(2m) = 240 σ₃(m)` for `m ≠ 0`.

## References

* J.-P. Serre, *A Course in Arithmetic*, Chapter VII, §6.
* J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, Chapter 2, §2.3.
-/

public section

open Module ModularForm
open scoped ArithmeticFunction.sigma

namespace TauCeti.IntegralLattice

/-- The theta series of the real model of the E₈ root lattice is the normalized Eisenstein
series `E₄`. -/
@[simp]
theorem thetaSeries_realModel_typeE₈RootLattice :
    ZLattice.thetaSeries (typeE₈RootLattice.realModel isPosDef_typeE₈RootLattice) = E₄ := by
  apply ZLattice.IsEven.thetaSeries_eq_E₄
  · exact (typeE₈RootLattice.isEven_realModel_iff _).mpr isEven_typeE₈RootLattice
  · exact (typeE₈RootLattice.isUnimodular_realModel_iff _).mpr isUnimodular_typeE₈RootLattice
  · simp [RealModelSpace.finrank_eq, finrank_carrier]

/-- The E₈ root lattice has `240 σ₃(m)` vectors of rational norm `2m` for every `m ≥ 1`. -/
theorem representationNumber_typeE₈RootLattice_two_mul {m : ℕ} (hm : m ≠ 0) :
    typeE₈RootLattice.representationNumber (2 * m) = 240 * σ 3 m := by
  have h := ZLattice.IsEven.representationNumber_two_mul_of_finrank_eq_eight
    ((typeE₈RootLattice.isEven_realModel_iff isPosDef_typeE₈RootLattice).mpr
      isEven_typeE₈RootLattice)
    ((typeE₈RootLattice.isUnimodular_realModel_iff isPosDef_typeE₈RootLattice).mpr
      isUnimodular_typeE₈RootLattice)
    (by simp [RealModelSpace.finrank_eq, finrank_carrier]) hm
  rw [← typeE₈RootLattice.representationNumber_realModel isPosDef_typeE₈RootLattice (2 * m)]
  simpa only [Rat.cast_mul, Rat.cast_ofNat, Rat.cast_natCast] using h

end TauCeti.IntegralLattice
