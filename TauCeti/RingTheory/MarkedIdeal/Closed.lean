/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Derivation.Order
public import TauCeti.RingTheory.MarkedIdeal.Basic

/-!
# Zariski closedness of marked ideal cosupports

Over a characteristic-zero field `k`, on a regular `k`-algebra `R` with finitely generated
projective Kähler differentials `Ω[R⁄k]` — in particular on a smooth `k`-algebra or a regular
`k`-algebra of finite type — the cosupport of every marked ideal `(I, d)` is Zariski closed, cut
out by the `(d - 1)`-st iterated derivation ideal of `I`.

## Main results

* `TauCeti.MarkedIdeal.cosupport_eq_zeroLocus_iterate_derivationIdeal`: over a characteristic-zero
  field, on a regular ring with finitely generated projective differentials, the cosupport of `M`
  is `PrimeSpectrum.zeroLocus ((Ideal.derivationIdeal k)^[M.mark - 1] M.ideal)`.
* `TauCeti.MarkedIdeal.isClosed_cosupport`: Zariski closedness under finitely generated projective
  differentials and regularity.
* `TauCeti.MarkedIdeal.isClosed_cosupport_of_smooth`: Zariski closedness for smooth algebras over
  a characteristic-zero field.
* `TauCeti.MarkedIdeal.isClosed_cosupport_of_finiteType`: Zariski closedness for regular algebras
  of finite type over a characteristic-zero field.

## References

* E. Bierstone and P. D. Milman, *Canonical desingularization in characteristic zero by blowing
  up the maximum strata of a local invariant*, Invent. Math. 128 (1997), §4.1–4.2 and
  Proposition 4.12.
-/

public section

namespace TauCeti.MarkedIdeal

open scoped KaehlerDifferential

variable (k : Type*) {R : Type*} [Field k] [CharZero k] [CommRing R] [Algebra k R]

/-- Over a characteristic-zero field, on a regular ring with finitely generated projective
differentials, the cosupport of a marked ideal `M` is the zero locus of the `(M.mark - 1)`-st
iterated derivation ideal of `M.ideal`. -/
theorem cosupport_eq_zeroLocus_iterate_derivationIdeal [Module.Projective R Ω[R⁄k]]
    [Module.Finite R Ω[R⁄k]] [IsRegularRing R] (M : MarkedIdeal R) :
    M.cosupport =
      PrimeSpectrum.zeroLocus (((Ideal.derivationIdeal k)^[M.mark - 1] M.ideal) : Set R) := by
  have hmark : M.mark - 1 + 1 = M.mark := Nat.sub_add_cancel M.mark_pos
  rw [cosupport_def, ← hmark]
  exact Ideal.setOf_natCast_add_one_le_orderAt_eq_zeroLocus k M.ideal (M.mark - 1)

/-- Over a characteristic-zero field, on a regular ring with finitely generated projective
differentials, the cosupport of every marked ideal is Zariski closed. -/
theorem isClosed_cosupport [Module.Projective R Ω[R⁄k]] [Module.Finite R Ω[R⁄k]]
    [IsRegularRing R] (M : MarkedIdeal R) :
    IsClosed M.cosupport := by
  rw [cosupport_def]
  exact Ideal.isClosed_setOf_le_orderAt k M.ideal M.mark

/-- On a smooth algebra over a characteristic-zero field, the cosupport of every marked ideal is
Zariski closed. -/
theorem isClosed_cosupport_of_smooth [Algebra.Smooth k R] (M : MarkedIdeal R) :
    IsClosed M.cosupport := by
  rw [cosupport_def]
  exact Ideal.isClosed_setOf_le_orderAt_of_smooth k M.ideal M.mark

/-- On a regular algebra of finite type over a characteristic-zero field, the cosupport of every
marked ideal is Zariski closed. -/
theorem isClosed_cosupport_of_finiteType [Algebra.FiniteType k R] [IsRegularRing R]
    (M : MarkedIdeal R) :
    IsClosed M.cosupport := by
  rw [cosupport_def]
  exact Ideal.isClosed_setOf_le_orderAt_of_finiteType k M.ideal M.mark

end TauCeti.MarkedIdeal
