/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.Padic
import TauCeti.NumberTheory.LocalField.InertiaDegree
import TauCeti.RingTheory.DiscreteValuationRing.Basic

/-!
# The index of a rational integer in a local integer ring

For a nonarchimedean local field `K` and a natural number `n` nonzero in `K`, the quotient
`𝒪[K] / n 𝒪[K]` has order `q ^ v_K(n)`, where `q` is the residue-field cardinality.
For a compatible extension `K/ℚ_p` and a nonzero natural number `n`, the quotient
`𝒪[K] / n 𝒪[K]` has order `p ^ ([K : ℚ_p] v_p(n))`. This identifies the integer-ring
index with the correction in the local Euler characteristic formula. It applies to ramified
extensions and to integers divisible by the residue prime.

The maximal-ideal filtration computes the order as `q ^ v_K(n)`. The identities
`q = p^f`, `v_K(n) = e v_p(n)` and `ef = [K : ℚ_p]` then give the stated formula.

## References

* J.-P. Serre, *Local Fields*, Chapter II, §§1–2.
-/

public section

open ValuativeRel

namespace TauCeti

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- The index of `n 𝒪[K]` in `𝒪[K]` is the residue-field cardinality raised to the
normalized valuation of `n`, provided `n` is nonzero in `K`. -/
theorem natCard_integerRing_quotient_span_natCast_eq_pow_natCastValuation
    (n : ℕ) (hn : (n : K) ≠ 0) :
    Nat.card (𝒪[K] ⧸ Ideal.span {(n : 𝒪[K])}) =
      Nat.card 𝓀[K] ^ natCastValuation K n hn := by
  rw [span_natCast_eq_maximalIdeal_pow K n hn,
    IsDiscreteValuationRing.natCard_quotient_maximalIdeal_pow]

variable (p : ℕ) [Fact p.Prime] [Algebra ℚ_[p] K] [ValuativeExtension ℚ_[p] K]

/-- For a finite extension `K/ℚ_p`, the index of `n 𝒪[K]` in `𝒪[K]` is
`p ^ ([K : ℚ_p] v_p(n))` for every nonzero natural number `n`. -/
theorem natCard_integerRing_quotient_span_natCast (n : ℕ) (hn : n ≠ 0) :
    Nat.card (𝒪[K] ⧸ Ideal.span {(n : 𝒪[K])}) =
      p ^ (Module.finrank ℚ_[p] K * padicValNat p n) := by
  have := charZero_of_injective_algebraMap (algebraMap ℚ_[p] K).injective
  rw [natCard_integerRing_quotient_span_natCast_eq_pow_natCastValuation K n
      (Nat.cast_ne_zero.mpr hn),
    natCastValuation_eq_ramificationIndex_mul (K := ℚ_[p]) n (Nat.cast_ne_zero.mpr hn),
    Padic.natCastValuation_eq_padicValNat,
    natCard_residueField ℚ_[p] K, Padic.natCard_residueField, ← pow_mul]
  congr 1
  rw [← ramificationIndex_mul_inertiaDegree ℚ_[p] K]
  ring

end TauCeti
