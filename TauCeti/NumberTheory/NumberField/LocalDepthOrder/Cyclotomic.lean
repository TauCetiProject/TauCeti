/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal
public import Mathlib.RingTheory.RootsOfUnity.CyclotomicUnits
public import TauCeti.NumberTheory.NumberField.LocalDepthOrder.Basic

/-!
# The local-depth order in a prime-power cyclotomic field

Let `K = ℚ(ζ)` with `ζ` a primitive `p ^ (k + 1)`-th root of unity, `p` prime. The prime `p` has
exactly one prime above it, `𝔓 = (ζ - 1)`, totally ramified with `e(𝔓 | p) = p ^ k (p - 1)`, and
`K` contains exactly `p ^ (k + 1)` roots of unity, doubled when `p` is odd. Along the levels
`𝔓 ^ h` the local-depth order therefore depends only on the `p`-part:

`r(𝔓 ^ h) = p ^ min(k + 1, max(0, ⌊h / (p ^ k (p - 1)) - 1 / (p - 1)⌋))`.

For the Gaussian field `ℚ(i)` (`p = 2`, `k = 1`, `𝔓 = (1 + i)` up to a unit) this is `1` for
`h ≤ 3`, `2` for `h = 4, 5` and `4 = |μ(ℚ(i))|` for `h ≥ 6`; the ramification index `2` enters
through the denominator.

## Main results

* `TauCeti.NumberField.localDepthExponent_span_zeta_sub_one_pow`: the exponent at `p` of the level
  `𝔓 ^ h`.
* `TauCeti.NumberField.localDepthExponent_span_zeta_sub_one_pow_eq_zero_of_ne`: the exponent at
  every other `q` vanishes.
* `TauCeti.NumberField.localDepthOrder_span_zeta_sub_one_pow`: the local-depth order of `𝔓 ^ h`.

## References

* H. Bass, J. Milnor and J.-P. Serre, *Solution of the congruence subgroup problem for `SLₙ`
  (`n ≥ 3`) and `Sp₂ₙ` (`n ≥ 2`)*, Publ. Math. IHÉS 33 (1967), (3.3) and Theorem 3.6.
-/

public section

open Ideal UniqueFactorizationMonoid IsDedekindDomain NumberField NumberField.Units
  IsCyclotomicExtension.Rat

namespace TauCeti.NumberField

variable {p k : ℕ} [hp : Fact p.Prime] {K : Type*} [Field K] [NumberField K]
  [IsCyclotomicExtension {p ^ (k + 1)} ℚ K] {ζ : K} (hζ : IsPrimitiveRoot ζ (p ^ (k + 1)))

/-- The truncated local-depth exponent at `p` of the level `(ζ - 1) ^ h` of
`ℚ(ζ_{p ^ (k + 1)})` is `min(k + 1, max(0, ⌊h / (p ^ k (p - 1)) - 1 / (p - 1)⌋))`. -/
theorem localDepthExponent_span_zeta_sub_one_pow (h : ℕ) :
    localDepthExponent K (span {hζ.toInteger - 1} ^ h) p =
      min (k + 1) ⌊(h : ℚ) / (p ^ k * (p - 1) : ℕ) - 1 / ((p : ℚ) - 1)⌋.toNat := by
  -- `K` has `p ^ (k + 1)` roots of unity, doubled for odd `p`
  have hm : (torsionOrder K).factorization p = k + 1 := by
    rw [torsionOrder_eq (n := p ^ (k + 1))]
    split_ifs with he
    · simp [hp.out.factorization_self]
    · have hp2 : p ≠ 2 := by
        rintro rfl
        exact he (even_two.pow_of_ne_zero k.succ_ne_zero)
      rw [Nat.factorization_mul two_ne_zero (pow_ne_zero _ hp.out.ne_zero)]
      simp [hp.out.factorization_self, Nat.prime_two.factorization, Finsupp.single_eq_of_ne hp2]
  -- `(ζ - 1)` is the only prime above `p`
  have hP {P : Ideal (𝓞 K)} :
      P ∈ (span {(p : ℤ)}).primesOver (𝓞 K) ↔ P = span {hζ.toInteger - 1} := by
    refine ⟨fun ⟨_, _⟩ ↦ eq_span_zeta_sub_one_of_liesOver p k K hζ P, ?_⟩
    rintro rfl
    exact ⟨isPrime_span_zeta_sub_one p k hζ, liesOver_span_zeta_sub_one p k hζ⟩
  -- `(ζ - 1)` occurs `h` times in `(ζ - 1) ^ h`
  have hcount :
      (normalizedFactors (span {hζ.toInteger - 1} ^ h)).count (span {hζ.toInteger - 1}) = h := by
    have hprime : Prime (span {hζ.toInteger - 1}) :=
      prime_of_isPrime (span_zeta_sub_one_ne_bot p k hζ) (isPrime_span_zeta_sub_one p k hζ)
    rw [hprime.irreducible.normalizedFactors_pow, normalize_eq, Multiset.count_replicate_self]
  refine eq_of_forall_le_iff fun j ↦ ?_
  simp only [le_localDepthExponent_iff, hP, forall_eq, hm, hcount,
    ramificationIdx_span_zeta_sub_one p k hζ, le_min_iff]

omit [IsCyclotomicExtension {p ^ (k + 1)} ℚ K] in
/-- At a prime `q ≠ p`, the truncated local-depth exponent of the level `(ζ - 1) ^ h` vanishes,
for `ζ` a primitive `p ^ (k + 1)`-th root of unity in any number field `K`. -/
theorem localDepthExponent_span_zeta_sub_one_pow_eq_zero_of_ne (h : ℕ) {q : ℕ} (hqp : q ≠ p) :
    localDepthExponent K (span {hζ.toInteger - 1} ^ h) q = 0 := by
  by_cases hq : q.Prime
  · have : Fact q.Prime := ⟨hq⟩
    obtain ⟨Q, hQ⟩ := nonempty_primesOver (S := 𝓞 K) (span {(q : ℤ)})
    have : Q.IsPrime := hQ.1
    have : Q.LiesOver (span {(q : ℤ)}) := hQ.2
    refine localDepthExponent_eq_zero_of_not_le hQ fun hle ↦ hqp ?_
    -- `ζ - 1` divides `p ^ (k + 1)`, so `(ζ - 1) ^ h ≤ Q` puts `p ^ (k + 1)` in `Q`
    have hmem : ((p ^ (k + 1) : ℕ) : 𝓞 K) ∈ Q :=
      Q.mem_of_dvd (hζ.toInteger_isPrimitiveRoot.sub_one_dvd_natCast
        (Nat.one_lt_pow k.succ_ne_zero hp.out.one_lt))
        (IsPrime.le_of_pow_le hle (mem_span_singleton_self _))
    have hdvd : ((p ^ (k + 1) : ℕ) : ℤ) ∈ span {(q : ℤ)} := by
      rw [Q.over_def (span {(q : ℤ)}), mem_comap]
      simpa using hmem
    rw [mem_span_singleton, Int.natCast_dvd_natCast] at hdvd
    exact (Nat.prime_dvd_prime_iff_eq hq hp.out).1 (hq.dvd_of_dvd_pow hdvd)
  · exact localDepthExponent_eq_zero_of_notMem_primeFactors _
      fun h ↦ hq (Nat.prime_of_mem_primeFactors h)

/-- The local-depth order of the level `(ζ - 1) ^ h` of `ℚ(ζ_{p ^ (k + 1)})` is
`p ^ min(k + 1, max(0, ⌊h / (p ^ k (p - 1)) - 1 / (p - 1)⌋))`. -/
theorem localDepthOrder_span_zeta_sub_one_pow (h : ℕ) :
    localDepthOrder K (span {hζ.toInteger - 1} ^ h) =
      p ^ min (k + 1) ⌊(h : ℚ) / (p ^ k * (p - 1) : ℕ) - 1 / ((p : ℚ) - 1)⌋.toNat := by
  refine Nat.eq_of_factorization_eq (localDepthOrder_pos _).ne'
    (pow_ne_zero _ hp.out.ne_zero) fun q ↦ ?_
  rw [factorization_localDepthOrder, hp.out.factorization_pow]
  by_cases hqp : q = p
  · subst hqp
    rw [localDepthExponent_span_zeta_sub_one_pow hζ, Finsupp.single_eq_same]
  · rw [localDepthExponent_span_zeta_sub_one_pow_eq_zero_of_ne hζ h hqp,
      Finsupp.single_eq_of_ne hqp]

end TauCeti.NumberField
