/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ArithmeticDirichletSeries.NaturalDensity
public import TauCeti.NumberTheory.ArithmeticDirichletSeries.ResidueDegree

/-!
# Natural density of primes of residue degree greater than one

The `O(√x)` bound for primes of residue degree greater than one, proved in
`TauCeti.NumberTheory.ArithmeticDirichletSeries.ResidueDegree`, is `o(x / log x)`.
The prime ideal theorem then shows that these primes have natural density zero.
Their complement has density one, and removing them preserves any natural density.

For Dirichlet density of prime ideals in number fields, see J. Neukirch,
*Algebraic Number Theory*, Chapter VII, §13.
-/

public section

open IsDedekindDomain NumberField NumberField.Set

namespace TauCeti

variable {K : Type*} [Field K] [NumberField K]

/-- **The primes of residue degree greater than one have natural density zero**: there are
`O(√x)` of them of norm at most `x`, which is `o(x / log x)`. -/
theorem hasNaturalDensity_higherDegreePrimes : HasNaturalDensity (higherDegreePrimes K) 0 :=
  hasNaturalDensity_zero_iff_isLittleO.2 primeCount_higherDegreePrimes_isLittleO

/-- **The primes of residue degree one have natural density one.** -/
theorem hasNaturalDensity_compl_higherDegreePrimes :
    HasNaturalDensity (higherDegreePrimes K)ᶜ 1 := by
  simpa using hasNaturalDensity_higherDegreePrimes.compl

/-- **Natural density only sees primes of residue degree one.** A set `S` of primes has natural
density `δ` if and only if its primes of residue degree one do. -/
theorem hasNaturalDensity_inter_compl_higherDegreePrimes_iff
    {S : Set (HeightOneSpectrum (𝓞 K))} {δ : ℝ} :
    HasNaturalDensity (S ∩ (higherDegreePrimes K)ᶜ) δ ↔ HasNaturalDensity S δ := by
  refine hasNaturalDensity_iff_of_symmDiff <|
    hasNaturalDensity_higherDegreePrimes.zero_of_subset fun 𝔭 h𝔭 => ?_
  simp only [Set.mem_symmDiff, Set.mem_inter_iff, Set.mem_compl_iff] at h𝔭
  tauto

end TauCeti
