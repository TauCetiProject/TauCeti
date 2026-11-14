/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.AbsoluteRamificationIndex
import TauCeti.NumberTheory.LocalField.InertiaDegree
import TauCeti.RingTheory.DiscreteValuationRing.Basic

/-!
# The index of a rational integer in a local integer ring

For a finite compatible extension `K/ℚ_p` and a nonzero natural number `n`, the quotient
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
  [IsNonarchimedeanLocalField K] (p : ℕ) [Fact p.Prime] [FinitePadicExtension K p]

/-- For a finite extension `K/ℚ_p`, the index of `n 𝒪[K]` in `𝒪[K]` is
`p ^ ([K : ℚ_p] v_p(n))` for every nonzero natural number `n`. -/
theorem natCard_integerRing_quotient_span_natCast (n : ℕ) (hn : n ≠ 0) :
    Nat.card (𝒪[K] ⧸ Ideal.span {(n : 𝒪[K])}) =
      p ^ (Module.finrank ℚ_[p] K * padicValNat p n) := by
  have := FinitePadicExtension.charZero K p
  have he : absoluteRamificationIndex K p = ramificationIndex ℚ_[p] K := by
    simpa only [absoluteRamificationIndex_padic, mul_one] using
      absoluteRamificationIndex_tower ℚ_[p] p K
  rw [span_natCast_eq_maximalIdeal_pow K n (Nat.cast_ne_zero.mpr hn),
    IsDiscreteValuationRing.natCard_quotient_maximalIdeal_pow,
    natCastValuation_eq_absoluteRamificationIndex_mul_padicValNat K p n hn,
    natCard_residueField ℚ_[p] K, Padic.natCard_residueField, ← pow_mul]
  congr 1
  rw [← ramificationIndex_mul_inertiaDegree ℚ_[p] K, he]
  ring

end TauCeti
