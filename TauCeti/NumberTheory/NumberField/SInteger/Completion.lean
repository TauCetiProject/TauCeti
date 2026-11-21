/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.SInteger.Basic
public import TauCeti.RingTheory.DedekindDomain.SInteger.Completion

/-!
# Adic-completion characterization of `S`-integers of a number field

For a number field `F` and a finite set `S : Finset (HeightOneSpectrum (𝓞 F))` of height-one primes
of `𝓞 F`, this file specializes `Set.mem_integer_iff_forall_adicCompletionIntegers` to characterize
membership in `TauCeti.SIntegers F S` in terms of membership in the local valuation subrings
`v.adicCompletionIntegers F` at all places `v ∉ S`.

## Main declarations

* `TauCeti.mem_sIntegers_iff_forall_adicCompletionIntegers`: an element of `F` lies in
  `SIntegers F S` if and only if its image in `v.adicCompletion F` lies in
  `v.adicCompletionIntegers F` for every `v ∉ S`.

## References

* J. W. S. Cassels and A. Fröhlich, eds., *Algebraic Number Theory*, Chapter II, §§14–15.
* J. Neukirch, *Algebraic Number Theory*, Chapter II, §4 and Chapter VI, §1.
-/

public section

open IsDedekindDomain NumberField

namespace TauCeti

variable {F : Type*} [Field F] [NumberField F]

/-- An element of `F` is an `S`-integer if and only if its image in `F_v` is `v`-integral for every
`v ∉ S`. -/
theorem mem_sIntegers_iff_forall_adicCompletionIntegers
    {S : Finset (HeightOneSpectrum (𝓞 F))} {x : F} :
    x ∈ SIntegers F S ↔
      ∀ v ∉ S, algebraMap F (v.adicCompletion F) x ∈ v.adicCompletionIntegers F := by
  simpa only [Finset.mem_coe] using
    (Set.mem_integer_iff_forall_adicCompletionIntegers (R := 𝓞 F) (S := (S : Set _)) (x := x))

end TauCeti

end
