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
instances and monotonicity (`Set.integer_mono`) from
`TauCeti.RingTheory.DedekindDomain.SInteger.Basic`. Import
`TauCeti.RingTheory.DedekindDomain.SInteger.Inclusion` separately for the scalar-tower inclusion
helpers (`Set.integerAlgebraOfSubset`, `Set.isScalarTower_integerAlgebraOfSubset`,
`Set.integerAlgebraOfSubset_eq`, `Set.integerValOfSubset`, `Set.toAlgHom_integer_injective`),
applied via `Finset.coe_subset.mpr`, and `TauCeti.NumberTheory.NumberField.SInteger.Completion` for
the local-global completion characterization and local integer subalgebras.

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
