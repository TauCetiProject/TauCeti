/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.Different.Basic
import TauCeti.RingTheory.DedekindDomain.Different.Trace

/-!
# The trace of the powers of the maximal ideal of a local field extension

Let `L/K` be a finite separable extension of nonarchimedean local fields, with ramification index
`e = e(L/K)` and different exponent `d = d(L/K)`. This file computes the image of the powers of
the maximal ideal of `𝒪[L]` under the integral trace `Tr = Algebra.intTrace 𝒪[K] 𝒪[L]`:

`Tr(𝓂[L] ^ m) = 𝓂[K] ^ ((m + d) / e)`,

with the division of natural numbers. It is the specialization of
`TauCeti.map_intTrace_pow_eq_maximalIdeal_pow` to the discrete valuation rings `𝒪[K]` and
`𝒪[L]`, where `𝓂[K] · 𝒪[L] = 𝓂[L] ^ e`. At `m = 0` it says that the trace maps `𝒪[L]` onto
`𝒪[K]` exactly when `d < e`, that is, exactly when `L/K` is tamely ramified.

The formula is the input to the computation of the norm on the unit filtration: the expansion
`N(1 + x) = 1 + Tr(x) + ⋯ + N(x)` for `x ∈ 𝓂[L] ^ m` has trace terms whose valuations it bounds
(Serre, *Local Fields*, Chapter V, §3).

## Main results

* `TauCeti.map_intTrace_maximalIdeal_pow`: `Tr(𝓂[L] ^ m) = 𝓂[K] ^ ((m + d(L/K)) / e(L/K))`.
* `TauCeti.intTrace_mem_maximalIdeal_pow_of_mem`: the element form, `Tr(x) ∈ 𝓂[K] ^ r` for
  `x ∈ 𝓂[L] ^ m` whenever `e(L/K) r ≤ m + d(L/K)`.
* `TauCeti.range_intTrace`: `Tr(𝒪[L]) = 𝓂[K] ^ (d(L/K) / e(L/K))`.
* `TauCeti.intTrace_surjective_iff_isTamelyRamified`: the trace maps `𝒪[L]` onto `𝒪[K]` exactly
  when `L/K` is tamely ramified.

## References

* J.-P. Serre, *Local Fields*, Chapter III (the different) and Chapter V, §3.
-/

public section

open ValuativeRel IsLocalRing

namespace TauCeti

variable (K L : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L] [Algebra.IsSeparable K L]

/-- **The trace of a power of the maximal ideal**: the integral trace carries `𝓂[L] ^ m` onto
`𝓂[K] ^ ((m + d(L/K)) / e(L/K))`, with the division of natural numbers. -/
@[simp]
theorem map_intTrace_maximalIdeal_pow (m : ℕ) :
    ((𝓂[L] ^ m).restrictScalars 𝒪[K]).map (Algebra.intTrace 𝒪[K] 𝒪[L]) =
      𝓂[K] ^ ((m + differentExponent K L) / ramificationIndex K L) := by
  rw [differentExponent_def]
  exact map_intTrace_pow_eq_maximalIdeal_pow 𝒪[K] (IsDiscreteValuationRing.not_a_field 𝒪[L])
    (map_maximalIdeal_eq_maximalIdeal_pow K L) m

variable {K L}

/-- The integral trace of an element of `𝓂[L] ^ m` lies in `𝓂[K] ^ r` as soon as
`e(L/K) r ≤ m + d(L/K)`. -/
theorem intTrace_mem_maximalIdeal_pow_of_mem {m r : ℕ} {x : 𝒪[L]} (hx : x ∈ 𝓂[L] ^ m)
    (h : ramificationIndex K L * r ≤ m + differentExponent K L) :
    Algebra.intTrace 𝒪[K] 𝒪[L] x ∈ 𝓂[K] ^ r := by
  rw [differentExponent_def] at h
  exact (map_intTrace_pow_le_pow_iff 𝒪[K] (IsDiscreteValuationRing.not_a_field 𝒪[L])
    (map_maximalIdeal_eq_maximalIdeal_pow K L) m r).mpr h
    (Submodule.mem_map_of_mem ((Submodule.restrictScalars_mem ..).mpr hx))

variable (K L)

/-- **The trace of the ring of integers**: the image of `𝒪[L]` under the integral trace is
`𝓂[K] ^ (d(L/K) / e(L/K))`. -/
@[simp]
theorem range_intTrace :
    LinearMap.range (Algebra.intTrace 𝒪[K] 𝒪[L]) =
      𝓂[K] ^ (differentExponent K L / ramificationIndex K L) := by
  have := map_intTrace_maximalIdeal_pow K L 0
  rwa [pow_zero, Ideal.one_eq_top, Submodule.restrictScalars_top, ← LinearMap.range_eq_map,
    zero_add] at this

/-- **The trace is surjective exactly in the tame case**: the integral trace maps `𝒪[L]` onto
`𝒪[K]` if and only if `L/K` is tamely ramified. -/
@[simp]
theorem intTrace_surjective_iff_isTamelyRamified :
    Function.Surjective (Algebra.intTrace 𝒪[K] 𝒪[L]) ↔ IsTamelyRamified K L := by
  rw [← LinearMap.range_eq_top, range_intTrace, ← Ideal.one_eq_top, ← pow_zero 𝓂[K],
    (Ideal.pow_right_strictAnti 𝓂[K] (IsDiscreteValuationRing.not_a_field 𝒪[K])
      (maximalIdeal.isMaximal 𝒪[K]).ne_top).injective.eq_iff,
    Nat.div_eq_zero_iff_lt (ramificationIndex_pos (K := K) (L := L)), ← not_le,
    ramificationIndex_le_differentExponent_iff K L, not_isWildlyRamified_iff]

end TauCeti
