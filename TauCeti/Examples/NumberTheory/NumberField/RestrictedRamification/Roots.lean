/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.RestrictedRamification.Basic
import TauCeti.NumberTheory.NumberField.RestrictedRamification.Roots

/-!
# Checks: roots in `ℚ_S` for `S` the places above `2`

Let `S` be the set of finite places of `ℚ` above `2`, that is the height-one primes of `𝓞 ℚ`
containing `2`, and `Ω` any field extension of `ℚ`. Then a root of `X² + 1`, a root of `X² - 2`
and every `2^k`-th root of unity in `Ω` lie in the maximal extension `ℚ_S` unramified outside `S`.
-/

public section

open IsDedekindDomain

open scoped NumberField

namespace TauCeti.Examples.RestrictedRamification

open TauCeti.RestrictedRamification

variable {Ω : Type*} [Field Ω] [Algebra ℚ Ω] {x : Ω}

/-- A place not above `2` contains no power of `2`. -/
theorem two_pow_notMem {v : HeightOneSpectrum (𝓞 ℚ)} (hv : (2 : 𝓞 ℚ) ∉ v.asIdeal)
    (k : ℕ) : ((2 ^ k : ℕ) : 𝓞 ℚ) ∉ v.asIdeal := by
  push_cast
  exact fun h ↦ hv (v.isPrime.mem_of_pow_mem k h)

/-- Every `2^k`-th root of unity lies in `ℚ_S`, `S` the places above `2`. -/
example (k : ℕ) (hx : x ^ 2 ^ k = 1) :
    x ∈ maxUnramifiedOutside ℚ Ω {v | (2 : 𝓞 ℚ) ∈ v.asIdeal} :=
  mem_maxUnramifiedOutside_of_pow_eq_one (n := 2 ^ k) (by exact_mod_cast hx)
    (pow_ne_zero k two_ne_zero) fun _ hv ↦ two_pow_notMem hv k

/-- A root `i` of `X² + 1` lies in `ℚ_S`, `S` the places above `2`. -/
example (hx : x ^ 2 = -1) : x ∈ maxUnramifiedOutside ℚ Ω {v | (2 : 𝓞 ℚ) ∈ v.asIdeal} :=
  mem_maxUnramifiedOutside_of_pow_eq_one (n := 2 ^ 2)
    (by rw [show 2 ^ 2 = 2 * 2 from rfl, pow_mul, hx]; norm_num) (by norm_num)
    fun _ hv ↦ two_pow_notMem hv 2

/-- A root `√2` of `X² - 2` lies in `ℚ_S`, `S` the places above `2`. -/
example (hx : x ^ 2 = 2) : x ∈ maxUnramifiedOutside ℚ Ω {v | (2 : 𝓞 ℚ) ∈ v.asIdeal} := by
  refine mem_maxUnramifiedOutside_of_pow_eq (a := algebraMap (𝓞 ℚ) ℚ 2) (n := 2) ?_ two_ne_zero
    fun v hv ↦ ⟨by exact_mod_cast hv, ?_⟩
  · rw [map_ofNat, map_ofNat, hx]
  · exact (HeightOneSpectrum.valuation_eq_one_iff_notMem v).2 hv

end TauCeti.Examples.RestrictedRamification
