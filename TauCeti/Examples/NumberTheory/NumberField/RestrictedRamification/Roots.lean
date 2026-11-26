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
Hence so do the compositum `ℚ(i) ⊔ ℚ(√2)` and all its subfields.
-/

public section

open IntermediateField IsDedekindDomain

open scoped NumberField

namespace TauCeti.Examples.RestrictedRamification

open TauCeti.RestrictedRamification

variable {Ω : Type*} [Field Ω] [Algebra ℚ Ω] {x : Ω}

/-- Every `2^k`-th root of unity lies in `ℚ_S`, `S` the places above `2`. -/
example (k : ℕ) (hx : x ^ 2 ^ k = 1) :
    x ∈ maxUnramifiedOutside ℚ Ω {v | (2 : 𝓞 ℚ) ∈ v.asIdeal} :=
  mem_maxUnramifiedOutside_of_pow_eq_one (n := 2 ^ k) (by exact_mod_cast hx)
    (pow_ne_zero k two_ne_zero) fun v hv h ↦ hv (v.isPrime.mem_of_pow_mem k (by exact_mod_cast h))

/-- A root `i` of `X² + 1` lies in `ℚ_S`, `S` the places above `2`. -/
theorem mem_maxUnramifiedOutside_two_of_sq_eq_neg_one (hx : x ^ 2 = -1) :
    x ∈ maxUnramifiedOutside ℚ Ω {v | (2 : 𝓞 ℚ) ∈ v.asIdeal} :=
  mem_maxUnramifiedOutside_of_pow_eq_one (n := 2 ^ 2)
    (by linear_combination (x ^ 2 - 1) * hx) (by norm_num)
    fun v hv h ↦ hv (v.isPrime.mem_of_pow_mem 2 (by exact_mod_cast h))

/-- A root `√2` of `X² - 2` lies in `ℚ_S`, `S` the places above `2`. -/
theorem mem_maxUnramifiedOutside_two_of_sq_eq_two (hx : x ^ 2 = 2) :
    x ∈ maxUnramifiedOutside ℚ Ω {v | (2 : 𝓞 ℚ) ∈ v.asIdeal} := by
  refine mem_maxUnramifiedOutside_of_pow_eq (a := algebraMap (𝓞 ℚ) ℚ 2) (n := 2) ?_ two_ne_zero
    fun v hv ↦ ⟨by exact_mod_cast hv, ?_⟩
  · rw [map_ofNat, map_ofNat, hx]
  · exact (HeightOneSpectrum.valuation_eq_one_iff_notMem v).2 hv

/-- The compositum `ℚ(i) ⊔ ℚ(√2)` lies in `ℚ_S`, `S` the places above `2`: it is unramified
outside `S` (`le_maxUnramifiedOutside_iff`). -/
theorem sup_le_maxUnramifiedOutside_two {y : Ω} (hx : x ^ 2 = -1) (hy : y ^ 2 = 2) :
    ℚ⟮x⟯ ⊔ ℚ⟮y⟯ ≤ maxUnramifiedOutside ℚ Ω {v | (2 : 𝓞 ℚ) ∈ v.asIdeal} :=
  sup_le (adjoin_simple_le_iff.2 (mem_maxUnramifiedOutside_two_of_sq_eq_neg_one hx))
    (adjoin_simple_le_iff.2 (mem_maxUnramifiedOutside_two_of_sq_eq_two hy))

/-- Every subfield of `ℚ(i) ⊔ ℚ(√2)` lies in `ℚ_S`, `S` the places above `2`, so a finite one is
unramified outside `S` (`le_maxUnramifiedOutside_iff`). -/
example {y : Ω} (hx : x ^ 2 = -1) (hy : y ^ 2 = 2) (L : IntermediateField ℚ Ω)
    (hL : L ≤ ℚ⟮x⟯ ⊔ ℚ⟮y⟯) : L ≤ maxUnramifiedOutside ℚ Ω {v | (2 : 𝓞 ℚ) ∈ v.asIdeal} :=
  hL.trans (sup_le_maxUnramifiedOutside_two hx hy)

end TauCeti.Examples.RestrictedRamification
