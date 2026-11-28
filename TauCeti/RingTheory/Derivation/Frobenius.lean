/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.CharP.Frobenius
public import Mathlib.Algebra.Field.Subfield.Basic
public import TauCeti.RingTheory.Derivation.Basic
public import TauCeti.RingTheory.Derivation.IntermediateField

/-!
# Derivations and the Frobenius subfield

Every derivation out of a field `k` of prime characteristic `p` vanishes on the Frobenius subfield
`k ^ p = (frobenius k p).fieldRange`. Consequently, any `R`-derivation out of `k` maps
`k ^ p(range b)` into the `k`-span of its values on `b`, and two `R`-derivations out of `k`
agreeing on a family generating `k` over `k ^ p` are equal.

## Main results

* `Derivation.map_eq_zero_of_mem_fieldRange_frobenius`: any derivation out of `k` vanishes on
  `k ^ p`.
* `Derivation.map_mem_span_of_mem_adjoin`: derivatives on `k ^ p(range b)` lie in the `k`-span of
  the derivatives of `b`.
* `Derivation.ext_of_adjoin_fieldRange_frobenius_eq_top`: two `R`-derivations out of `k` into a
  `k`-module that agree on a generating family over `k ^ p` are equal.
-/

public section

namespace Derivation

/-- Every element of the Frobenius subfield `k ^ p` is annihilated by any derivation out of `k`. -/
theorem map_eq_zero_of_mem_fieldRange_frobenius {p : ℕ} [Fact p.Prime] {R k M : Type*}
    [CommSemiring R] [Field k] [ExpChar k p] [Algebra R k] [AddCommMonoid M] [Module R M]
    [Module k M] (d : Derivation R k M) {x : k} (hx : x ∈ (frobenius k p).fieldRange) :
    d x = 0 := by
  have : CharP k p := (expChar_prime_iff k Fact.out).mp ‹_›
  obtain ⟨a, rfl⟩ := hx
  rw [frobenius_def, d.map_pow_eq_zero_of_charP]

/-- For any family `b : ι → k` and any `R`-derivation `d : Derivation R k M` into a `k`-module,
every element of the intermediate field `k ^ p(range b)` has derivative in the `k`-linear span of
`{d (b i)}`. -/
theorem map_mem_span_of_mem_adjoin {p : ℕ} [Fact p.Prime] {R k M : Type*} [CommRing R]
    [Field k] [ExpChar k p] [Algebra R k] [AddCommGroup M] [Module R M] [Module k M]
    {ι : Type*} (d : Derivation R k M) (b : ι → k) {x : k}
    (hx : x ∈ IntermediateField.adjoin (frobenius k p).fieldRange (Set.range b)) :
    d x ∈ Submodule.span k (Set.range fun i ↦ d (b i)) :=
  d.map_mem_of_mem_adjoin _ (fun c ↦ d.map_eq_zero_of_mem_fieldRange_frobenius c.property)
    (by rintro _ ⟨i, rfl⟩; exact Submodule.subset_span ⟨i, rfl⟩) hx

/-- Two `R`-derivations out of `k` into a `k`-module that agree on a family generating `k` over
`k ^ p` are equal. -/
theorem ext_of_adjoin_fieldRange_frobenius_eq_top {p : ℕ} [Fact p.Prime] {R k M : Type*}
    [CommRing R] [Field k] [ExpChar k p] [Algebra R k] [AddCommGroup M] [Module R M]
    [Module k M] {ι : Type*} {b : ι → k}
    (hadj : IntermediateField.adjoin (frobenius k p).fieldRange (Set.range b) = ⊤)
    {d₁ d₂ : Derivation R k M} (h : ∀ i, d₁ (b i) = d₂ (b i)) : d₁ = d₂ :=
  ext_of_intermediateField_adjoin_eq_top hadj
    (fun e ↦ (d₁.map_eq_zero_of_mem_fieldRange_frobenius e.property).trans
      (d₂.map_eq_zero_of_mem_fieldRange_frobenius e.property).symm)
    (by rintro _ ⟨i, rfl⟩; exact h i)

end Derivation
