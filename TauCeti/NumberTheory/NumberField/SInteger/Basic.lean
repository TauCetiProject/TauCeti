/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.Basic
public import TauCeti.RingTheory.DedekindDomain.SInteger.Basic

/-!
# Rings of `S`-integers of a number field

For a number field `F` and a finite set `S : Finset (HeightOneSpectrum (𝓞 F))` of height-one primes
of its ring of integers `𝓞 F`, this file defines the subalgebra `TauCeti.SIntegers F S` of
`S`-integers `𝒪_{F,S} = (S : Set (HeightOneSpectrum (𝓞 F))).integer F`.

Because `SIntegers F S` is an `abbrev` for `(S : Set _).integer F`, it inherits the Dedekind-domain
instances from `TauCeti.RingTheory.DedekindDomain.SInteger.Basic` and the inclusion API
(`Set.integer_mono`, `Set.integerAlgebraOfSubset`, `Set.isScalarTower_integerAlgebraOfSubset`,
`Set.toAlgHom_integer_injective`) from `TauCeti.RingTheory.DedekindDomain.SInteger.Inclusion` via
`Finset.coe_subset.mpr`. For the local-global completion characterization and local integer
subalgebras, see `TauCeti.NumberTheory.NumberField.SInteger.Completion`.

## Main declarations

* `TauCeti.SIntegers`: the subalgebra `𝒪_{F,S}` of `S`-integers of a number field `F`.

## References

* J. W. S. Cassels and A. Fröhlich, eds., *Algebraic Number Theory*, Chapter II, §§14–15.
* J. Neukirch, *Algebraic Number Theory*, Chapter II, §4 and Chapter VI, §1.
-/

public section

open IsDedekindDomain NumberField

namespace TauCeti

variable (F : Type*) [Field F] [NumberField F]

/-- The subalgebra `𝒪_{F,S}` of `S`-integers of `F`, consisting of elements with `v`-adic valuation
at most `1` at every height-one prime `v ∉ S`. -/
noncomputable abbrev SIntegers (S : Finset (HeightOneSpectrum (𝓞 F))) : Subalgebra (𝓞 F) F :=
  (S : Set (HeightOneSpectrum (𝓞 F))).integer F

end TauCeti

end
