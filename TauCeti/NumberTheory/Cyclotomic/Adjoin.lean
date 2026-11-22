/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Cyclotomic.Basic

/-!
# Adjoining roots of unity as an intermediate field

Adjoining one primitive `m`-th root of unity to `K` inside `M` gives the same intermediate field as
adjoining all the `m`-th roots of unity, and that intermediate field `K(ζ)` is an `m`-th cyclotomic
extension of `K`.

The statements live in the `IntermediateField` lattice, which is where the Galois correspondence
needs them. That `K(ζ)` itself is an `m`-th cyclotomic extension of `K` is Mathlib's
`IsPrimitiveRoot.intermediateField_adjoin_isCyclotomicExtension`; this file transports it to
`K(μ_m)`.

## Main results

* `IsPrimitiveRoot.adjoin_singleton_eq_adjoin_nth_roots`: `K(ζ) = K(μ_m)`.
* `IsPrimitiveRoot.isCyclotomicExtension_adjoin_nth_roots`: `K(μ_m)` is an `m`-th cyclotomic
  extension of `K`.
-/

public section

open IntermediateField

/-- **Adjoining one primitive `m`-th root adjoins them all.** `K(ζ) = K(μ_m)` inside any
field extension of `K` containing a primitive `m`-th root of unity `ζ`: every `m`-th root of unity
is a power of `ζ`. -/
theorem IsPrimitiveRoot.adjoin_singleton_eq_adjoin_nth_roots {K M : Type*} [Field K] [Field M]
    [Algebra K M] {m : ℕ} [NeZero m] {ζ : M}
    (hζ : IsPrimitiveRoot ζ m) : adjoin K {ζ} = adjoin K {b : M | b ^ m = 1} :=
  le_antisymm (adjoin_simple_le_iff.mpr <| subset_adjoin K _ hζ.pow_eq_one) <|
    adjoin_le_iff.mpr fun _ hb ↦ by
      obtain ⟨i, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one hb
      exact pow_mem (mem_adjoin_simple_self K ζ) i

/-- **`K(μ_m)` is an `m`-th cyclotomic extension of `K`** inside any extension of `K` containing a
primitive `m`-th root of unity. -/
theorem IsPrimitiveRoot.isCyclotomicExtension_adjoin_nth_roots {K M : Type*} [Field K] [Field M]
    [Algebra K M] {m : ℕ} [NeZero m] {ζ : M} (hζ : IsPrimitiveRoot ζ m) :
    IsCyclotomicExtension {m} K (adjoin K {b : M | b ^ m = 1}) :=
  hζ.adjoin_singleton_eq_adjoin_nth_roots (K := K) ▸
    hζ.intermediateField_adjoin_isCyclotomicExtension K
