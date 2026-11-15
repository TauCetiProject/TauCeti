/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Trace.IntegralBasis
public import Mathlib.RingTheory.OrderOfVanishing.Basic
import TauCeti.RingTheory.Length.Determinant

/-!
# Discriminants as complementary-module lengths

For a finite free order over a principal ideal domain, the order of the discriminant equals
the length of the complementary module modulo the order. This holds for nonmaximal orders
and does not require separable residue fields. In the discrete valuation ring case, it is
the discriminant valuation formula.

`Module.Basis.traceDualQuotientEquiv` identifies this quotient with the cokernel of the
trace Gram matrix. The matrix cokernel-length formula then computes its length.
`Module.Basis.length_traceDual_quotient_eq_length_quotient_range_algebraToTraceDual` transfers
this length to the quotient of `Submodule.traceDual A K 1` by the integral elements, the
presentation used by the different-ideal length formulas.

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

omit [IsDomain A] [IsPrincipalIdealRing A] [FiniteDimensional K L] [Algebra.IsSeparable K L]
  [Fintype ι] [DecidableEq ι] in
/-- The quotient of the complementary module `Submodule.traceDual A K 1` by the integral elements
has the same length as its integral-basis presentation, the quotient by the range of
`Module.Basis.algebraToTraceDual`. -/
theorem length_traceDual_quotient_eq_length_quotient_range_algebraToTraceDual [Finite ι]
    (b : Basis ι A B) :
    Module.length A ((Submodule.traceDual A K (1 : Submodule B L)) ⧸
        (1 : Submodule B L).comap (Submodule.traceDual A K (1 : Submodule B L)).subtype) =
      Module.length A
        (((Algebra.traceForm K L).dualSubmodule ((1 : Submodule B L).restrictScalars A)) ⧸
          LinearMap.range (b.algebraToTraceDual (K := K) (L := L))) := by
  set C := Submodule.traceDual A K (1 : Submodule B L)
  set N := (1 : Submodule B L).comap C.subtype
  -- `Submodule.restrictScalars_traceDual` is definitional, so `C` is the dual submodule over `A`.
  let e : C ≃ₗ[A] (Algebra.traceForm K L).dualSubmodule ((1 : Submodule B L).restrictScalars A) :=
    ((C.restrictScalarsEquiv A).restrictScalars A).symm
  have hrange : (N.restrictScalars A).map e.toLinearMap =
      LinearMap.range (b.algebraToTraceDual (K := K) (L := L)) := by
    ext x
    simp only [Submodule.mem_map, Submodule.restrictScalars_mem]
    constructor
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨z, hz⟩ := Submodule.mem_one.mp (Submodule.mem_comap.mp hy)
      exact ⟨z, Subtype.ext ((b.coe_algebraToTraceDual z).trans hz)⟩
    · rintro ⟨z, rfl⟩
      exact ⟨e.symm (b.algebraToTraceDual z),
        Submodule.mem_comap.mpr (Submodule.mem_one.mpr ⟨z, (b.coe_algebraToTraceDual z).symm⟩),
        e.apply_symm_apply _⟩
  exact ((Submodule.Quotient.restrictScalarsEquiv A N).symm.trans
    (Submodule.Quotient.equiv _ _ e hrange)).length_eq

end Module.Basis
