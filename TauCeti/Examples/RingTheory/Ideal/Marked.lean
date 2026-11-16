/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.RingTheory.DualNumber
import TauCeti.RingTheory.Ideal.Marked

/-!
# Examples of affine ideal order and marked ideals

These examples exercise `Ideal.orderAt`, `TauCeti.MarkedIdeal`, rescaling, and marked sums:

* the unit ideal has order `0` at every prime and empty positive-mark cosupport;
* the zero ideal has order `⊤` at every prime and full positive-mark cosupport;
* over the dual numbers `k[ε] / (ε²)` of a field `k`, the maximal ideal `𝔪` has order `1` whereas
  `𝔪² = ⊥` has order `⊤`; hence `(𝔪, 2)` has empty cosupport while its rescaling `(𝔪², 4)` has
  full nonempty cosupport, showing that the regularity hypothesis in `Ideal.localOrder_pow` and
  `TauCeti.MarkedIdeal.cosupport_rescale` cannot be omitted;
* summing `(⟨y²⟩, 2)` and `(⟨x³⟩, 2)` gives `(⟨y⁴, x⁶⟩, 4)`;
* a unit summand produces the unit ideal and empty cosupport;
* two zero summands produce the zero ideal and full cosupport with the positive product mark.

## References

* E. Bierstone and P. D. Milman, *Canonical desingularization in characteristic zero by blowing up
  the maximum strata of a local invariant*, Invent. Math. 128 (1997), §4.1–4.2 and
  Construction 4.23.
-/

open IsLocalRing TauCeti TauCeti.MarkedIdeal

/-! ### Unit and zero ideals -/

section UnitZero

variable {R : Type*} [CommRing R]

-- The unit ideal has order `0` at every prime and empty positive-mark cosupport.
example (p : PrimeSpectrum R) (d : ℕ) (hd : 0 < d) :
    (⊤ : Ideal R).orderAt p = 0 ∧ (⟨⊤, d, hd⟩ : MarkedIdeal R).cosupport = ∅ :=
  ⟨Ideal.orderAt_top p, cosupport_top d hd⟩

-- The zero ideal has order `⊤` at every prime and full positive-mark cosupport.
example (p : PrimeSpectrum R) (d : ℕ) (hd : 0 < d) :
    (⊥ : Ideal R).orderAt p = ⊤ ∧ (⟨⊥, d, hd⟩ : MarkedIdeal R).cosupport = Set.univ :=
  ⟨Ideal.orderAt_bot p, cosupport_bot d hd⟩

end UnitZero

/-! ### Non-regular counterexample: dual numbers `k[ε] / (ε²)` -/

section DualNumbers

variable {k : Type*} [Field k]

-- On `k[ε] / (ε²)`, `𝔪` has local order `1` while `𝔪²` has local order `⊤`.
example :
    (maximalIdeal (DualNumber k)).localOrder = 1 ∧
      (maximalIdeal (DualNumber k) ^ 2).localOrder = ⊤ := by
  have hsq : maximalIdeal (DualNumber k) ^ 2 = ⊥ := by
    rw [DualNumber.maximalIdeal_eq_span_singleton_eps, Ideal.span_singleton_pow, sq,
      DualNumber.eps_mul_eps, Ideal.span_singleton_zero]
  refine ⟨le_antisymm ?_ ?_, ?_⟩
  · apply le_of_not_gt
    intro hlt
    have h2 : ((2 : ℕ) : ℕ∞) ≤ (maximalIdeal (DualNumber k)).localOrder := by
      have : ((1 : ℕ) : ℕ∞) + 1 ≤ (maximalIdeal (DualNumber k)).localOrder :=
        ENat.natCast_add_one_le_iff.mpr (by simpa using hlt)
      exact_mod_cast this
    rw [Ideal.natCast_le_localOrder_iff, hsq,
      DualNumber.maximalIdeal_eq_span_singleton_eps, Ideal.span_singleton_le_iff_mem,
      Ideal.mem_bot] at h2
    have : (1 : k) = 0 := by simpa using congrArg TrivSqZeroExt.snd h2
    exact one_ne_zero this
  · rw [← Nat.cast_one, Ideal.natCast_le_localOrder_iff, pow_one]
  · rw [hsq, Ideal.localOrder_bot]

-- On `k[ε] / (ε²)`, `(𝔪, 2)` has empty cosupport, whereas rescaling by `2` gives `(𝔪², 4)` with
-- full nonempty cosupport.
example :
    let M : MarkedIdeal (DualNumber k) := ⟨maximalIdeal (DualNumber k), 2, Nat.two_pos⟩
    M.cosupport = ∅ ∧
      (M.rescale 2 Nat.two_pos).cosupport = Set.univ ∧
      (M.rescale 2 Nat.two_pos).cosupport ≠ M.cosupport := by
  intro M
  have hsq : maximalIdeal (DualNumber k) ^ 2 = ⊥ := by
    rw [DualNumber.maximalIdeal_eq_span_singleton_eps, Ideal.span_singleton_pow, sq,
      DualNumber.eps_mul_eps, Ideal.span_singleton_zero]
  have hprime (p : PrimeSpectrum (DualNumber k)) :
      p = ⟨maximalIdeal (DualNumber k), (maximalIdeal.isMaximal _).isPrime⟩ := by
    ext1
    rcases DualNumber.ideal_trichotomy p.asIdeal with h | h | h
    · exfalso
      have hmem : (DualNumber.eps : DualNumber k) ∈ p.asIdeal := by
        have hmul : (DualNumber.eps : DualNumber k) * DualNumber.eps ∈ p.asIdeal := by
          rw [DualNumber.eps_mul_eps]
          exact p.asIdeal.zero_mem
        exact (p.isPrime.mem_or_mem hmul).elim id id
      rw [h, Ideal.mem_bot] at hmem
      have : (1 : k) = 0 := by simpa using congrArg TrivSqZeroExt.snd hmem
      exact one_ne_zero this
    · exact h.trans DualNumber.maximalIdeal_eq_span_singleton_eps.symm
    · exact absurd h p.isPrime.ne_top
  have h1 : M.cosupport = ∅ := by
    ext p
    rw [mem_cosupport_iff, hprime p, Ideal.orderAt_maximalIdeal]
    simp only [M, Set.mem_empty_iff_false, iff_false]
    intro h2
    rw [Ideal.natCast_le_localOrder_iff, hsq,
      DualNumber.maximalIdeal_eq_span_singleton_eps, Ideal.span_singleton_le_iff_mem,
      Ideal.mem_bot] at h2
    have : (1 : k) = 0 := by simpa using congrArg TrivSqZeroExt.snd h2
    exact one_ne_zero this
  have h2 : (M.rescale 2 Nat.two_pos).cosupport = Set.univ :=
    cosupport_eq_univ_of_ideal_eq_bot (by rw [rescale_ideal]; exact hsq)
  refine ⟨h1, h2, ?_⟩
  rw [h1, h2]
  exact Set.Nonempty.ne_empty ⟨⟨maximalIdeal (DualNumber k), (maximalIdeal.isMaximal _).isPrime⟩,
    trivial⟩

end DualNumbers

/-! ### Marked sums -/

section MarkedSums

variable {R : Type*} [CommRing R]

-- Summing `(⟨y²⟩, 2)` and `(⟨x³⟩, 2)` gives `(⟨y⁴, x⁶⟩, 4)`.
example (x y : R) :
    (⟨Ideal.span {y ^ 2}, 2, Nat.two_pos⟩ : MarkedIdeal R).sum
        ⟨Ideal.span {x ^ 3}, 2, Nat.two_pos⟩ =
      ⟨Ideal.span {y ^ 4, x ^ 6}, 4, by decide⟩ := by
  rw [sum_span_singleton]
  exact MarkedIdeal.ext (by simp [← pow_mul]) rfl

-- A unit summand produces the unit ideal and empty cosupport.
example (d : ℕ) (hd : 0 < d) (M : MarkedIdeal R) :
    ((⟨⊤, d, hd⟩ : MarkedIdeal R).sum M).ideal = ⊤ ∧
      ((⟨⊤, d, hd⟩ : MarkedIdeal R).sum M).cosupport = ∅ ∧
      (M.sum ⟨⊤, d, hd⟩).ideal = ⊤ ∧
      (M.sum ⟨⊤, d, hd⟩).cosupport = ∅ := by
  simp

-- Two zero summands produce the zero ideal and full cosupport with the positive product mark.
example (d₁ d₂ : ℕ) (hd₁ : 0 < d₁) (hd₂ : 0 < d₂) :
    ((⟨⊥, d₁, hd₁⟩ : MarkedIdeal R).sum ⟨⊥, d₂, hd₂⟩) = ⟨⊥, d₁ * d₂, Nat.mul_pos hd₁ hd₂⟩ ∧
      ((⟨⊥, d₁, hd₁⟩ : MarkedIdeal R).sum ⟨⊥, d₂, hd₂⟩).cosupport = Set.univ := by
  simp [mul_comm]

end MarkedSums
