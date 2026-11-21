/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Length.Endomorphism
public import TauCeti.RingTheory.OrderOfVanishing
import Mathlib.Data.ENat.BigOperators
import TauCeti.RingTheory.QuasiFinite.Basic

/-!
# The local projection formula for finite maps of curves

Let `A` be a local Noetherian domain of dimension at most one and `B` a domain finite
over `A`, with injective structure map. For `a ≠ 0` in `A`, the pullback of the Cartier
equation `a` satisfies

`∑ m, [κ(m) : κ(A)] * ord_{Bₘ}(a) = rank_A B * ord_A(a)`.

The sum is over the maximal ideals of `B`. Only the finitely many containing the image
of `a` contribute. The residue degree is expressed as `length_A (B ⧸ m)`, which
`MaximalSpectrum.length_quotient_eq_length_residueField` rewrites as `[κ(Bₘ) : κ(A)]`, and
`rank_A B` is also the degree of the extension of fraction fields, by
`IsFractionRing.finrank_eq`. Neither ring needs to be normal and `B` need not be flat
over `A`: this includes finite birational maps onto singular curves.

This is the local multiplicity comparison used to compare the degree of a pulled-back
Cartier divisor with the degree of the original divisor. On the semilocal inverse image
of a point of the target curve, its left-hand side is the sum of the multiplicities at
the points above it, weighted by their residue degrees.

The proof computes the length of `B/aB` in two ways. The torsion-free module formula
`TauCeti.length_quotient_lsmul_eq_finrank_mul_ord` computes it using the generic rank;
`TauCeti.length_quotient_span_singleton_eq_finsum_ord` decomposes it into local orders.
The localizations may be chosen arbitrarily, so the result applies to scheme stalks
without requiring them to be the concrete `Localization.AtPrime` types.

## References

* Q. Liu, *Algebraic Geometry and Arithmetic Curves*, Section 7.3, degrees under finite
  morphisms of curves, and Section 9.2, the projection formula on arithmetic surfaces.
* W. Fulton, *Intersection Theory*, Appendix A.2–A.3, lengths of cokernels and their
  decomposition into local contributions.
-/

public section

noncomputable section

namespace TauCeti

variable {A B : Type*} [CommRing A] [IsNoetherianRing A]
  [Ring.KrullDimLE 1 A] [IsLocalRing A] [CommRing B] [IsDomain B]
  [Algebra A B] [Module.Finite A B] [FaithfulSMul A B]
  (S : MaximalSpectrum B → Type*) [∀ m, CommRing (S m)]
  [∀ m, Algebra B (S m)] [∀ m, IsLocalization.AtPrime (S m) m.asIdeal]

/-- The local projection formula for a nonzero Cartier equation under a finite injective
map of domains of dimension at most one. The multiplicity at each point above the closed point
is weighted by its residue degree, expressed as the length of `B ⧸ m` over `A`.
The natural-number right-hand side also asserts finiteness of the sum. -/
theorem finsum_ord_algebraMap_mul_length_quotient_eq_finrank_mul_ord {a : A} (ha : a ≠ 0) :
    (∑ᶠ m : MaximalSpectrum B,
      Ring.ord (S m) (algebraMap B (S m) (algebraMap A B a)) *
        Module.length A (B ⧸ m.asIdeal)) =
      ((Module.finrank A B * (Ring.ord A a).toNat : ℕ) : ℕ∞) := by
  have : IsDomain A := .of_faithfulSMul A B
  rw [Nat.cast_mul, ENat.natCast_toNat (Ring.ord_ne_top (mem_nonZeroDivisors_of_ne_zero ha))]
  have hab : algebraMap A B a ≠ 0 := (FaithfulSMul.algebraMap_eq_zero_iff A B).not.mpr ha
  have hlen := length_quotient_lsmul_eq_finrank_mul_ord (M := B) ha
  rw [range_lsmul_eq_smul_top, ← Submodule.ideal_span_singleton_smul, Ideal.smul_top_eq_map,
    Ideal.map_span, Set.image_singleton, (Submodule.Quotient.restrictScalarsEquiv A _).length_eq,
    length_quotient_span_singleton_eq_finsum_ord hab] at hlen
  refine (finsum_congr fun m ↦ ?_).trans hlen
  rw [Ring.ord_algebraMap_isLocalization m.asIdeal.primeCompl (Localization.AtPrime m.asIdeal),
    m.length_residueField_localization_eq]

/-- The local projection formula as an equality of natural numbers. All summands of the
extended-natural formula are finite, so conversion to natural numbers preserves the sum. -/
theorem finsum_toNat_ord_algebraMap_mul_length_quotient_eq_finrank_mul_ord
    {a : A} (ha : a ≠ 0) :
    (∑ᶠ m : MaximalSpectrum B,
      (Ring.ord (S m) (algebraMap B (S m) (algebraMap A B a))).toNat *
        (Module.length A (B ⧸ m.asIdeal)).toNat) =
      Module.finrank A B * (Ring.ord A a).toNat := by
  have : Finite (MaximalSpectrum B) := finite_maximalSpectrum_of_isIntegral_of_quasiFinite A
  have := Fintype.ofFinite (MaximalSpectrum B)
  have h := finsum_ord_algebraMap_mul_length_quotient_eq_finrank_mul_ord S ha
  rw [finsum_eq_sum_of_fintype] at h ⊢
  have hfin := ENat.sum_ne_top.mp (h ▸ ENat.natCast_ne_top _)
  simpa only [ENat.toNat_mul, ENat.toNat_natCast] using
    (ENat.toNat_sum hfin).symm.trans (congrArg ENat.toNat h)

end TauCeti
