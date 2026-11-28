/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.Ideal.Span
public import Mathlib.RingTheory.Length
import TauCeti.RingTheory.MatlisDuality.PrincipalIdealRing

/-!
# Length of linear maps from a cyclic torsion module to a principal quotient

Over an integral domain `O`, if `d ∣ a` with `a ≠ 0`, then `O / d` is annihilated by `a` and
`d ≠ 0`, so the Matlis duality identifications
(`TauCeti.linearMapQuotientSpanEquivFractionRingQuotient`,
`Ideal.quotientLinearMapEquivTorsionBySet`,
and `TauCeti.quotientEquivTorsionBySet`) identify `Hom_O(O / d, O / a)` with `O / d`, giving equal
`O`-module length (`TauCeti.length_linearMap_quotSpan_of_dvd`).

## Main results

* `TauCeti.length_linearMap_quotSpan_of_dvd`: for `d ∣ a` with `a ≠ 0` in an integral domain `O`,
  `Module.length O ((O ⧸ Ideal.span {d}) →ₗ[O] (O ⧸ Ideal.span {a})) =
   Module.length O (O ⧸ Ideal.span {d})`.

## Provenance

Adapted from `grh-lean` (<https://github.com/lsernau/grh-lean>, commit
`72fead102f663d5c7a407964a13dc0cf9d977207`), `src/Lib/General/Algebra/SharpMinors.lean`
(`New.Selmer.length_linearMap_quotSpan_of_dvd`).
-/

public section

namespace TauCeti

open Module Submodule

/-- In an integral domain `O`, if `d ∣ a` with `a ≠ 0`, then the module of `O`-linear maps
`(O ⧸ Ideal.span {d}) →ₗ[O] (O ⧸ Ideal.span {a})` has the same length as `O ⧸ Ideal.span {d}`. -/
theorem length_linearMap_quotSpan_of_dvd {O : Type*} [CommRing O] [IsDomain O] {a d : O}
    (ha : a ≠ 0) (hd : d ∣ a) :
    Module.length O ((O ⧸ Ideal.span {d}) →ₗ[O] (O ⧸ Ideal.span {a})) =
      Module.length O (O ⧸ Ideal.span {d}) := by
  have hd_ne : d ≠ 0 := ne_zero_of_dvd_ne_zero ha hd
  have h_kill : ∀ x : O ⧸ Ideal.span {d}, a • x = 0 := fun x ↦ by
    rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq,
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr hd), zero_mul]
  let e := (linearMapQuotientSpanEquivFractionRingQuotient (K := FractionRing O) ha h_kill).trans
    (((Ideal.span {d}).quotientLinearMapEquivTorsionBySet _).trans
      (quotientEquivTorsionBySet (K := FractionRing O) hd_ne).symm)
  exact e.length_eq

end TauCeti
