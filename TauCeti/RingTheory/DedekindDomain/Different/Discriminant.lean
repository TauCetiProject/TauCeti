/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.DedekindDomain.Different.Length
public import TauCeti.RingTheory.Trace.Length

/-!
# The discriminant, the different exponent and the residue degree

Let `A ⊆ B` be an extension of discrete valuation rings, with `B` the integral closure of `A` in a
finite separable extension `L` of the fraction field `K` of `A`, and let `b` be an `A`-basis of
`B`. The trace Gram matrix `Tᵢⱼ = Tr_{B/A}(bᵢ bⱼ)` has determinant the discriminant
`Algebra.discr A b`, and `Module.Basis.length_traceDual_quotient_eq_ord_discr` computes the length
of the complementary module `C = Submodule.traceDual A K 1` modulo `B` as its order of vanishing.
The complementary-module length formula
`TauCeti.length_traceDual_quotient_eq_multiplicity_mul_finrank` turns this into

  `ord_A (discr A b) = d * f`,

where `d` is the different exponent and `f` the full residue degree, including its inseparable
factor. Thus the discriminant, the residue degree and the different exponent are related on the
rings themselves, with no separability of residue fields and no monogenic generator.

## Main results

* `TauCeti.ord_discr_eq_multiplicity_mul_finrank`: `ord_A (discr A b) = d * f` for an extension
  of discrete valuation rings.

## References

* J.-P. Serre, *Local Fields*, Chapter III, §§2–3 (the discriminant, the complementary module
  and the different).
-/

public section

open scoped nonZeroDivisors

namespace TauCeti

variable {A B K L : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [Field K] [Field L]
  [Algebra A B] [Algebra A K] [Algebra K L] [Algebra A L] [Algebra B L]
  [IsScalarTower A K L] [IsScalarTower A B L] [IsFractionRing A K] [IsFractionRing B L]
  [IsIntegralClosure B A L] [Algebra.IsSeparable K L] [Module.IsTorsionFree A B]
  [IsLocalHom (algebraMap A B)] {ι : Type*} [Fintype ι] [DecidableEq ι]

variable (K L) in
include K L in
/-- **The discriminant is the different exponent times the full residue degree.** For an
`A`-basis `b` of an extension `B` of discrete valuation rings, with `B` the integral closure of `A`
in a finite separable extension `L` of the fraction field `K`, the valuation of the discriminant
of `b` is `d * f`, where `d` is the multiplicity of the maximal ideal of `B` in the different and
`f` is the residue degree, including its inseparable factor. -/
theorem ord_discr_eq_multiplicity_mul_finrank (b : Module.Basis ι A B) :
    Ring.ord A (Algebra.discr A b) =
      (multiplicity (IsLocalRing.maximalIdeal B) (differentIdeal A B) : ℕ∞) *
        Module.finrank (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B) := by
  have : Module.Finite A B := .of_basis b
  have := IsIntegralClosure.isLocalization A K L B
  have : FiniteDimensional K L := .of_basis (b.localizationLocalization K A⁰ L)
  rw [← b.length_traceDual_quotient_eq_ord_discr (K := K) (L := L),
    ← b.length_traceDual_quotient_eq_length_quotient_range_algebraToTraceDual,
    length_traceDual_quotient_eq_multiplicity_mul_finrank]

end TauCeti
