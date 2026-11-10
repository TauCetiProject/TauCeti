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
needs them; the cyclotomic one is transported from Mathlib's `Algebra.adjoin` statement
`IsPrimitiveRoot.adjoin_isCyclotomicExtension`. Unlike Mathlib's
`IsPrimitiveRoot.intermediateField_adjoin_isCyclotomicExtension`, nothing is asked of the ambient
extension `M / K`, since a root of unity is integral over `K` on its own.

## Main results

* `IsPrimitiveRoot.adjoin_singleton_eq_adjoin_nth_roots`: `K(ζ) = K(μ_m)`.
* `IsPrimitiveRoot.isCyclotomicExtension_adjoin_singleton` and
  `IsPrimitiveRoot.isCyclotomicExtension_adjoin_nth_roots`: `K(ζ) = K(μ_m)` is an `m`-th cyclotomic
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

/-- **`K(ζ)` is an `m`-th cyclotomic extension of `K`.** Mathlib's
`IsPrimitiveRoot.intermediateField_adjoin_isCyclotomicExtension` asks the whole ambient extension
`M / K` to be integral; only `ζ` needs to be, and a root of unity always is, being a root of
`X ^ m - 1`. -/
theorem IsPrimitiveRoot.isCyclotomicExtension_adjoin_singleton {K M : Type*} [Field K] [Field M]
    [Algebra K M] {m : ℕ} [NeZero m] {ζ : M} (hζ : IsPrimitiveRoot ζ m) :
    IsCyclotomicExtension {m} K (adjoin K {ζ}) := by
  -- `K(ζ)` and `Algebra.adjoin K {ζ}` have the same carrier because `ζ` is algebraic over `K`.
  change IsCyclotomicExtension {m} K (adjoin K {ζ}).toSubalgebra
  rw [adjoin_simple_toSubalgebra_of_isAlgebraic
    (hζ.isIntegral (NeZero.pos m)).tower_top.isAlgebraic]
  exact hζ.adjoin_isCyclotomicExtension K

/-- **`K(μ_m)` is an `m`-th cyclotomic extension of `K`** inside any extension of `K` containing a
primitive `m`-th root of unity. -/
theorem IsPrimitiveRoot.isCyclotomicExtension_adjoin_nth_roots {K M : Type*} [Field K] [Field M]
    [Algebra K M] {m : ℕ} [NeZero m] {ζ : M} (hζ : IsPrimitiveRoot ζ m) :
    IsCyclotomicExtension {m} K (adjoin K {b : M | b ^ m = 1}) :=
  hζ.adjoin_singleton_eq_adjoin_nth_roots (K := K) ▸ hζ.isCyclotomicExtension_adjoin_singleton
