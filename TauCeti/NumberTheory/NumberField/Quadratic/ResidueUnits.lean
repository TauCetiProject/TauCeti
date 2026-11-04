/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Multiquadratic.Quadratic.Character
public import TauCeti.NumberTheory.NumberField.ResidueUnits
import TauCeti.NumberTheory.NumberField.Quadratic.TotalRamification
import TauCeti.NumberTheory.RamificationInertia.Inert
import TauCeti.NumberTheory.RamificationInertia.Splitting

/-!
# Residue units of a quadratic field modulo a rational integer

Let `K` be a quadratic number field with discriminant `D` and quadratic character
`χ_D = TauCeti.Multiquadratic.fundamentalDiscriminantChar D`. For a rational prime `p`, the ring
`𝓞 K ⧸ p 𝓞 K` has `p²` elements, and its units are counted by the decomposition of `p`:

* if `p` splits, `p 𝓞 K = 𝔭 𝔭'` with `N 𝔭 = N 𝔭' = p`, and there are `(p - 1)²` units;
* if `p` is inert, `p 𝓞 K` is prime of norm `p²`, and there are `p² - 1` units;
* if `p` ramifies, `p 𝓞 K = 𝔭²` with `N 𝔭 = p`, and there are `p (p - 1)` units.

Since `χ_D(p) = 1, -1, 0` in these three cases, all three counts are `(p - 1) (p - χ_D(p))`.
Combined with the reduction to primes
`TauCeti.NumberField.card_units_quotient_span_natCast_mul_prod_pow`, this gives, for every
positive integer `f`,

```text
#(𝓞 K ⧸ f 𝓞 K)ˣ = f² ∏_{p ∣ f} (1 - 1/p) (1 - χ_D(p)/p),
```

stated here without denominators. This is the residue-unit factor in the class number formula
for the order `ℤ + f 𝓞 K` of conductor `f`.

## Main results

* `TauCeti.NumberField.card_units_quotient_span_natCast_of_prime`:
  `#(𝓞 K ⧸ p 𝓞 K)ˣ = (p - 1) (p - χ_D(p))`.
* `TauCeti.NumberField.card_units_quotient_span_natCast_mul_prod`:
  `#(𝓞 K ⧸ f 𝓞 K)ˣ · ∏_{p ∣ f} p² = f² ∏_{p ∣ f} (p - 1) (p - χ_D(p))`.

## References

* D. A. Cox, *Primes of the Form x² + ny²*, §7, proof of Theorem 7.24.
-/

public section

open Ideal Module
open scoped NumberField
open TauCeti.Multiquadratic (fundamentalDiscriminantChar isFundamentalDiscr_discr
  fundamentalDiscriminantChar_isQuadratic)

namespace TauCeti.NumberField

variable {K : Type*} [Field K] [NumberField K]

/-- If the primes of a quadratic field above `p` all have norm `p ^ k` and there are `g` of them,
then `#(𝓞 K ⧸ p 𝓞 K)ˣ · p ^ (k g) = p² (p ^ k - 1) ^ g`. -/
private theorem card_units_quotient_span_mul_pow_eq (hK : finrank ℚ K = 2) {p : ℕ}
    [hp : Fact p.Prime] {k g : ℕ}
    (hN : ∀ 𝔭 : (span {(p : ℤ)} : Ideal ℤ).primesOver (𝓞 K), absNorm 𝔭.1 = p ^ k)
    (hg : ((span {(p : ℤ)} : Ideal ℤ).primesOver (𝓞 K)).ncard = g) :
    (Nat.card (𝓞 K ⧸ span {(p : 𝓞 K)})ˣ : ℤ) * (p : ℤ) ^ (k * g) =
      p ^ 2 * ((p : ℤ) ^ k - 1) ^ g := by
  have h := card_units_quotient_span_natCast_mul_prod_absNorm (K := K) (p := p)
  simp only [hN, Finset.prod_const, Finset.card_univ] at h
  rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq, hg, hK, ← pow_mul] at h
  have h1 : 1 ≤ p ^ k := Nat.one_le_pow _ _ hp.out.pos
  have := congrArg (Nat.cast : ℕ → ℤ) h
  push_cast [Nat.cast_sub h1] at this
  exact this

/-- **Residue units modulo a rational prime in a quadratic field.** For a quadratic field `K`
with discriminant `D` and a rational prime `p`, `#(𝓞 K ⧸ p 𝓞 K)ˣ = (p - 1) (p - χ_D(p))`: this is
`(p - 1)²`, `p² - 1` or `p (p - 1)` according as `p` splits, is inert or ramifies. -/
theorem card_units_quotient_span_natCast_of_prime (hK : finrank ℚ K = 2) (p : ℕ)
    [hp : Fact p.Prime] :
    (Nat.card (𝓞 K ⧸ span {(p : 𝓞 K)})ˣ : ℤ) =
      (p - 1) *
        (p - fundamentalDiscriminantChar (NumberField.discr K) (isFundamentalDiscr_discr hK)
          p) := by
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  rcases fundamentalDiscriminantChar_isQuadratic (isFundamentalDiscr_discr hK) p with h | h | h
  · -- `p` ramifies: one prime above `p`, of norm `p`.
    have hmem := (Multiquadratic.fundamentalDiscriminantChar_discr_eq_zero_iff hK p).mp h
    have key := card_units_quotient_span_mul_pow_eq (K := K) hK (k := 1)
      (fun 𝔭 ↦ by rw [pow_one]; exact NumberField.absNorm_eq_of_mem_ramifiedPrimes hK hmem 𝔭.1)
      (NumberField.ncard_primesOver_eq_one_of_mem_ramifiedPrimes hK hmem)
    rw [h]
    refine mul_right_cancel₀ (pow_ne_zero (1 * 1) hp0) ?_
    push_cast
    linear_combination key
  · -- `p` splits: two primes above `p`, each of residue degree `1`, hence of norm `p`.
    have hg := (Multiquadratic.fundamentalDiscriminantChar_discr_eq_one_iff hK p).mp h
    have key := card_units_quotient_span_mul_pow_eq (K := K) hK (k := 1) (fun 𝔭 ↦ ?_) hg
    · rw [h]
      refine mul_right_cancel₀ (pow_ne_zero (1 * 2) hp0) ?_
      push_cast
      linear_combination key
    open RamificationInertia in
    rw [← Ideal.pow_inertiaDeg p 𝔭.1,
      (ramificationIdx_eq_one_and_inertiaDeg_eq_one_of_ncard_primesOver_eq_finrank _ 𝔭.1
        (by rw [hg, NumberField.RingOfIntegers.rank, hK])).2]
  · -- `p` is inert: one unramified prime above `p`, of residue degree `2`, hence of norm `p²`.
    obtain ⟨hram, hg⟩ := (Multiquadratic.fundamentalDiscriminantChar_discr_eq_neg_one_iff hK p).mp h
    have hunr : Algebra.IsUnramifiedIn (𝓞 K) (span {(p : ℤ)}) := by
      by_contra hcon
      exact hram (NumberField.mem_ramifiedPrimes_iff.mpr ⟨hp.out, hcon⟩)
    have key := card_units_quotient_span_mul_pow_eq (K := K) hK (k := 2) (fun 𝔭 ↦ ?_) hg
    · rw [h]
      refine mul_right_cancel₀ (pow_ne_zero (2 * 1) hp0) ?_
      push_cast
      linear_combination key
    rw [← Ideal.pow_inertiaDeg p 𝔭.1,
      RamificationInertia.inertiaDeg_eq_finrank_of_ncard_primesOver_eq_one _ 𝔭.1 hg
        (Algebra.isUnramifiedIn_iff_forall_ramificationIdx_eq_one.mp hunr 𝔭.1 inferInstance),
      NumberField.RingOfIntegers.rank, hK]

/-- **Residue units modulo `f` in a quadratic field.** For a quadratic field `K` with
discriminant `D` and a positive integer `f`,
`#(𝓞 K ⧸ f 𝓞 K)ˣ · ∏_{p ∣ f} p² = f² ∏_{p ∣ f} (p - 1) (p - χ_D(p))`, that is,
`#(𝓞 K ⧸ f 𝓞 K)ˣ = f² ∏_{p ∣ f} (1 - 1/p) (1 - χ_D(p)/p)`. -/
theorem card_units_quotient_span_natCast_mul_prod (hK : finrank ℚ K = 2) {f : ℕ} (hf : f ≠ 0) :
    (Nat.card (𝓞 K ⧸ span {(f : 𝓞 K)})ˣ : ℤ) * ∏ p ∈ f.primeFactors, (p : ℤ) ^ 2 =
      f ^ 2 * ∏ p ∈ f.primeFactors,
        ((p : ℤ) - 1) *
          (p - fundamentalDiscriminantChar (NumberField.discr K) (isFundamentalDiscr_discr hK)
            p) := by
  have h := congrArg (Nat.cast : ℕ → ℤ) (card_units_quotient_span_natCast_mul_prod_pow (K := K) hf)
  rw [hK] at h
  push_cast at h
  rw [h]
  congr 1
  refine Finset.prod_congr rfl fun p hp ↦ ?_
  have := Fact.mk (Nat.prime_of_mem_primeFactors hp)
  exact card_units_quotient_span_natCast_of_prime hK p

end TauCeti.NumberField
