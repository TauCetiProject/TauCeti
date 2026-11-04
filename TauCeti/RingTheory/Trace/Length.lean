/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Trace.IntegralBasis
public import Mathlib.RingTheory.OrderOfVanishing.Basic
import TauCeti.LinearAlgebra.Matrix.SmithNormalForm.Length

/-!
# Discriminants as complementary-module lengths

For a finite free order over a principal ideal domain, the order of the discriminant equals
the length of the complementary module modulo the order. This holds for nonmaximal orders
and does not require separable residue fields. In the discrete valuation ring case, it is
the discriminant valuation formula.

`Module.Basis.traceDualQuotientEquiv` identifies this quotient with the cokernel of the
trace Gram matrix. The matrix cokernel-length formula then computes its length.

## References

* J.-P. Serre, *Local Fields*, Chapter III, Section 3 (the complementary module and discriminant).
-/

public section

open scoped nonZeroDivisors

namespace Module.Basis

variable {A K B L ι : Type*} [CommRing A] [IsDomain A] [IsPrincipalIdealRing A] [Field K]
  [CommRing B] [Field L] [Algebra A K] [Algebra A B] [Algebra B L]
  [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsScalarTower A B L]
  [IsFractionRing A K]
  [IsLocalization (Algebra.algebraMapSubmonoid B A⁰) L]
  [FiniteDimensional K L] [Algebra.IsSeparable K L] [Fintype ι] [DecidableEq ι]

/-- The complementary module modulo a finite free order over a principal ideal domain has
length equal to the order of the discriminant of an integral basis. No maximality of the
order or separability of residue extensions is assumed. -/
theorem length_traceDual_quotient_eq_ord_discr (b : Basis ι A B) :
    Module.length A
      (((Algebra.traceForm K L).dualSubmodule ((1 : Submodule B L).restrictScalars A)) ⧸
        LinearMap.range (b.algebraToTraceDual (K := K) (L := L))) =
      Ring.ord A (Algebra.discr A b) := by
  have hdiscr : Algebra.discr A b ≠ 0 := by
    intro h
    have hz := Algebra.discr_localizationLocalization A A⁰ L (Rₘ := K) b
    rw [h, map_zero] at hz
    exact Algebra.discr_not_zero_of_basis K (b.localizationLocalization K A⁰ L) hz
  rw [(b.traceDualQuotientEquiv (K := K) (L := L)).length_eq, Algebra.discr_def]
  apply Matrix.length_quotient_range_mulVecLin_eq_ord_det
  simpa only [Algebra.discr_def] using hdiscr

end Module.Basis
