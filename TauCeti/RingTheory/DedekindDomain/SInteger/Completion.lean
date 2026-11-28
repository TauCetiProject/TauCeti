/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.SInteger
import TauCeti.RingTheory.DedekindDomain.SInteger.Basic

/-!
# Adic-completion characterization of `S`-integers

Let `R` be a Dedekind domain with fraction field `K` and `S` a set of height-one primes of `R`. An
element `x ∈ K` lies in the subalgebra `S.integer K` of `S`-integers if and only if its image in
every `v`-adic completion `v.adicCompletion K` for `v ∉ S` lies in the valuation subring
`v.adicCompletionIntegers K` (`Set.mem_integer_iff_forall_adicCompletionIntegers`).

This local-global characterization bridges global `S`-integrality with valuation-ring membership in
individual nonarchimedean completions, without passing through the finite adele ring. For
number-field specializations, see `TauCeti.NumberTheory.NumberField.SInteger.Basic` and
`TauCeti.NumberTheory.NumberField.SInteger.Completion`.

## Main declarations

* `Set.mem_integer_iff_forall_adicCompletionIntegers`: adic-completion characterization of
  `x ∈ S.integer K` over any Dedekind domain `R`.

## References

* J. W. S. Cassels and A. Fröhlich, eds., *Algebraic Number Theory*, Chapter II, §§14–15.
* J. Neukirch, *Algebraic Number Theory*, Chapter II, §4 and Chapter VI, §1.
-/

public section

open IsDedekindDomain

namespace IsDedekindDomain

variable {R : Type*} [CommRing R] [IsDedekindDomain R] {K : Type*} [Field K] [Algebra R K]
  [IsFractionRing R K] {S : Set (HeightOneSpectrum R)}

/-- An element of `K` is an `S`-integer if and only if its image in the `v`-adic completion
`v.adicCompletion K` lies in the valuation ring `v.adicCompletionIntegers K` for every height-one
prime `v ∉ S`. -/
theorem _root_.Set.mem_integer_iff_forall_adicCompletionIntegers {x : K} :
    x ∈ S.integer K ↔
      ∀ v ∉ S, algebraMap K (v.adicCompletion K) x ∈ v.adicCompletionIntegers K := by
  simp [Set.mem_integer_iff, HeightOneSpectrum.mem_adicCompletionIntegers,
    HeightOneSpectrum.algebraMap_adicCompletion]

end IsDedekindDomain

end
