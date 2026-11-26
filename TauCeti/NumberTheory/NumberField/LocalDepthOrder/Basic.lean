/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.Units.Basic
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.RamificationInertia.Ramification
public import Mathlib.RingTheory.Ideal.Int
public import Mathlib.Algebra.Order.Floor.Ring

/-!
# The truncated local-depth order of a level in a number field

Let `F` be a number field with `m = |μ(F)|` roots of unity and let `I` be a nonzero ideal of
`𝓞 F`. For a prime `p`, the **truncated local-depth exponent** of `I` at `p` is

`j(I, p) = min_{P ∣ p} min(ord_p m, max(0, ⌊ord_P(I) / e(P | p) - 1 / (p - 1)⌋))`,

the minimum running over all primes `P` of `𝓞 F` above `p`, including those not dividing `I`,
where `e(P | p) = ord_P(p)` is the ramification index. The **local-depth order** of `I` is

`r(I) = ∏_{p ∣ m} p ^ j(I, p)`,

a divisor of `m`. Bass, Milnor and Serre prove that for a totally imaginary `F` the universal
Mennicke group of level `I` is the cyclic group `μ_{r(I)}` of `r(I)`-th roots of unity, the
`r(I)`-th power residue symbol being the universal Mennicke symbol; it is trivial at the unit
ideal and equals `μ(F)` at sufficiently deep levels. This file sets up the numerical invariant
and its arithmetic.

The quantity `ord_P(I) / e(P | p) - 1 / (p - 1)` is the depth of the level `I` at `P`, measured
in the normalization of the `p`-adic valuation and shifted by the depth `1 / (p - 1)` of the
`p`-th roots of unity; the `p`-primary part of `μ(F)` which survives at level `I` is cut out by
the shallowest prime above `p`.

## Main definitions

* `TauCeti.NumberField.localDepthExponent F I p`: the exponent `j(I, p)`.
* `TauCeti.NumberField.localDepthOrder F I`: the order `r(I) = ∏_{p ∣ m} p ^ j(I, p)`.

## Main results

* `TauCeti.NumberField.le_localDepthExponent_iff`: `k ≤ j(I, p)` exactly when `k ≤ ord_p m` and
  `k` is at most the truncated depth at every prime above `p`.
* `TauCeti.NumberField.localDepthExponent_eq_zero_of_not_le`: `j(I, p) = 0` as soon as some
  prime above `p` does not divide `I`.
* `TauCeti.NumberField.factorization_localDepthOrder`: `j(I, p)` is the `p`-adic valuation of
  `r(I)`.
* `TauCeti.NumberField.localDepthOrder_dvd_torsionOrder`: `r(I) ∣ m`.
* `TauCeti.NumberField.localDepthOrder_top`: `r(𝓞 F) = 1`.
* `TauCeti.NumberField.localDepthOrder_dvd_of_le`: `r(I) ∣ r(J)` for nonzero `J ≤ I`.
* `TauCeti.NumberField.localDepthOrder_eq_torsionOrder`: the full-depth criterion, `r(I) = m`
  when `ord_P(I) ≥ e(P | p) (ord_p m + 1 / (p - 1))` for every `p ∣ m` and every `P` above `p`.

## Implementation notes

The minimum over the primes above `p` is a fold of `min` over Mathlib's
`IsDedekindDomain.primesOverFinset`, started at `ord_p m`; it does not depend on an enumeration
of these primes, and `le_localDepthExponent_iff` characterizes it in terms of
`Ideal.primesOver`. The order `ord_P(I)` is the multiplicity of `P` in the normalized
factorization of `I`. The definitions make sense for every ideal and every natural number `p`:
`j(I, p) = 0` unless `p` is a prime dividing `m`, and the zero ideal, which has no factorization,
gets the junk value `r(⊥) = 1`.

## References

* H. Bass, J. Milnor and J.-P. Serre, *Solution of the congruence subgroup problem for `SLₙ`
  (`n ≥ 3`) and `Sp₂ₙ` (`n ≥ 2`)*, Publ. Math. IHÉS 33 (1967), (3.3) and Theorem 3.6.
-/

public section

open Ideal UniqueFactorizationMonoid IsDedekindDomain NumberField NumberField.Units

namespace TauCeti.NumberField

variable (F : Type*) [Field F] [NumberField F]

/-- The **truncated local-depth exponent** `j(I, p)` of an ideal `I` of `𝓞 F` at `p`: the
minimum, over all primes `P` of `𝓞 F` above `p`, of
`min(ord_p m, max(0, ⌊ord_P(I) / e(P | p) - 1 / (p - 1)⌋))`, where `m` is the number of roots of
unity of `F` and `e(P | p)` is the ramification index. It vanishes unless `p` is a prime dividing
`m`. -/
noncomputable def localDepthExponent (I : Ideal (𝓞 F)) (p : ℕ) : ℕ :=
  (primesOverFinset (span {(p : ℤ)}) (𝓞 F)).fold min ((torsionOrder F).factorization p)
    fun P ↦ ⌊((normalizedFactors I).count P : ℚ) / P.ramificationIdx ℤ - 1 / ((p : ℚ) - 1)⌋.toNat

/-- The **local-depth order** `r(I) = ∏_{p ∣ m} p ^ j(I, p)` of an ideal `I` of `𝓞 F`, where `m`
is the number of roots of unity of `F` and `j(I, p)` is the truncated local-depth exponent. It is a
divisor of `m`, equal to `1` at the unit ideal and to `m` at sufficiently deep levels. -/
noncomputable def localDepthOrder (I : Ideal (𝓞 F)) : ℕ :=
  ∏ p ∈ (torsionOrder F).primeFactors, p ^ localDepthExponent F I p

variable {F} {I J : Ideal (𝓞 F)} {p : ℕ}

/-- The truncated local-depth exponent at `p` is at most the `p`-adic valuation `ord_p m` of the
number `m` of roots of unity. -/
theorem localDepthExponent_le_factorization (I : Ideal (𝓞 F)) (p : ℕ) :
    localDepthExponent F I p ≤ (torsionOrder F).factorization p :=
  (Finset.fold_min_le _).2 (.inl le_rfl)

/-- The truncated local-depth exponent at `p` vanishes unless `p` is a prime dividing the number
`m` of roots of unity. -/
theorem localDepthExponent_eq_zero_of_notMem_primeFactors (I : Ideal (𝓞 F))
    (hp : p ∉ (torsionOrder F).primeFactors) : localDepthExponent F I p = 0 :=
  Nat.le_zero.1 <| (localDepthExponent_le_factorization I p).trans_eq <| by
    rwa [← Finsupp.notMem_support_iff, Nat.support_factorization]

/-- The truncated local-depth exponent at `p` is at most the truncated depth at any prime in the
finite set `IsDedekindDomain.primesOverFinset` of prime factors of `p`. -/
private theorem localDepthExponent_le_of_mem_primesOverFinset {P : Ideal (𝓞 F)}
    (hP : P ∈ primesOverFinset (span {(p : ℤ)}) (𝓞 F)) :
    localDepthExponent F I p ≤
      ⌊((normalizedFactors I).count P : ℚ) / P.ramificationIdx ℤ - 1 / ((p : ℚ) - 1)⌋.toNat :=
  (Finset.fold_min_le _).2 (.inr ⟨P, hP, le_rfl⟩)

/-- **Characterization of the truncated local-depth exponent.** A natural number `k` is at most
`j(I, p)` exactly when `k ≤ ord_p m` and `k` is at most `⌊ord_P(I) / e(P | p) - 1 / (p - 1)⌋` at
every prime `P` above `p`. -/
theorem le_localDepthExponent_iff {k : ℕ} :
    k ≤ localDepthExponent F I p ↔ k ≤ (torsionOrder F).factorization p ∧
      ∀ P ∈ (span {(p : ℤ)}).primesOver (𝓞 F),
        k ≤ ⌊((normalizedFactors I).count P : ℚ) / P.ramificationIdx ℤ -
          1 / ((p : ℚ) - 1)⌋.toNat := by
  by_cases hp : p.Prime
  · have : Fact p.Prime := ⟨hp⟩
    have hp0 : span {(p : ℤ)} ≠ ⊥ := by simpa using hp.ne_zero
    simp only [localDepthExponent, Finset.le_fold_min, mem_primesOverFinset_iff hp0 (𝓞 F)]
  · -- both sides say `k = 0`, since `ord_p m = 0`
    have h0 := Nat.factorization_eq_zero_of_not_prime (torsionOrder F) hp
    rw [localDepthExponent_eq_zero_of_notMem_primeFactors I
      fun h ↦ hp (Nat.prime_of_mem_primeFactors h), h0]
    exact ⟨fun hk ↦ ⟨hk, fun _ _ ↦ (Nat.le_zero.1 hk).trans_le (Nat.zero_le _)⟩, And.left⟩

/-- The truncated local-depth exponent at `p` is at most the truncated depth at every prime
above `p`. -/
theorem localDepthExponent_le {P : Ideal (𝓞 F)} (hP : P ∈ (span {(p : ℤ)}).primesOver (𝓞 F)) :
    localDepthExponent F I p ≤
      ⌊((normalizedFactors I).count P : ℚ) / P.ramificationIdx ℤ - 1 / ((p : ℚ) - 1)⌋.toNat :=
  (le_localDepthExponent_iff.1 le_rfl).2 P hP

/-- The truncated local-depth exponent vanishes as soon as some prime above `p` does not divide
the level: the shallowest prime above `p` decides. -/
theorem localDepthExponent_eq_zero_of_not_le {P : Ideal (𝓞 F)}
    (hP : P ∈ (span {(p : ℤ)}).primesOver (𝓞 F)) (hIP : ¬I ≤ P) :
    localDepthExponent F I p = 0 := by
  by_cases hp : p.Prime
  · have hcount : (normalizedFactors I).count P = 0 :=
      Multiset.count_eq_zero.2 fun h ↦ hIP (dvd_iff_le.1 (dvd_of_mem_normalizedFactors h))
    have hp1 : (1 : ℚ) ≤ p := mod_cast hp.one_lt.le
    refine Nat.le_zero.1 ((localDepthExponent_le hP).trans_eq ?_)
    rw [hcount, Int.toNat_eq_zero, Int.floor_le_iff, Nat.cast_zero, zero_div, zero_sub]
    have : 0 ≤ 1 / ((p : ℚ) - 1) := one_div_nonneg.2 (sub_nonneg.2 hp1)
    push_cast
    linarith
  · exact localDepthExponent_eq_zero_of_notMem_primeFactors I
      fun h ↦ hp (Nat.prime_of_mem_primeFactors h)

/-- The truncated local-depth exponent of the unit ideal vanishes. -/
@[simp]
theorem localDepthExponent_top (p : ℕ) : localDepthExponent F ⊤ p = 0 := by
  by_cases hp : p.Prime
  · have : Fact p.Prime := ⟨hp⟩
    obtain ⟨P, hP⟩ := nonempty_primesOver (S := 𝓞 F) (span {(p : ℤ)})
    exact localDepthExponent_eq_zero_of_not_le hP fun h ↦ hP.1.ne_top (top_le_iff.1 h)
  · exact localDepthExponent_eq_zero_of_notMem_primeFactors ⊤
      fun h ↦ hp (Nat.prime_of_mem_primeFactors h)

/-- The truncated local-depth exponent grows with the depth of the level: a nonzero ideal `J ≤ I`
has `j(I, p) ≤ j(J, p)`. -/
theorem localDepthExponent_le_of_le (hJ : J ≠ ⊥) (hJI : J ≤ I) (p : ℕ) :
    localDepthExponent F I p ≤ localDepthExponent F J p := by
  have hle : normalizedFactors I ≤ normalizedFactors J :=
    (dvd_iff_normalizedFactors_le_normalizedFactors (ne_bot_of_le_ne_bot hJ hJI) hJ).1
      (dvd_iff_le.2 hJI)
  refine (Finset.le_fold_min _).2 ⟨localDepthExponent_le_factorization I p, fun P hP ↦ ?_⟩
  refine (localDepthExponent_le_of_mem_primesOverFinset hP).trans
    (Int.toNat_le_toNat (Int.floor_mono ?_))
  gcongr

/-- **The full-depth criterion at one prime.** If `ord_P(I) ≥ e(P | p) (ord_p m + 1 / (p - 1))`
at every prime `P` above `p`, then `j(I, p) = ord_p m`. -/
theorem localDepthExponent_eq_factorization
    (h : ∀ P ∈ (span {(p : ℤ)}).primesOver (𝓞 F),
      (P.ramificationIdx ℤ : ℚ) * ((torsionOrder F).factorization p + 1 / ((p : ℚ) - 1)) ≤
        (normalizedFactors I).count P) :
    localDepthExponent F I p = (torsionOrder F).factorization p := by
  refine le_antisymm (localDepthExponent_le_factorization I p)
    (le_localDepthExponent_iff.2 ⟨le_rfl, fun P hP ↦ ?_⟩)
  have : P.IsPrime := hP.1
  have he : (0 : ℚ) < P.ramificationIdx ℤ := mod_cast ramificationIdx_pos ℤ P
  have hle : ((torsionOrder F).factorization p : ℚ) ≤
      (normalizedFactors I).count P / P.ramificationIdx ℤ - 1 / ((p : ℚ) - 1) := by
    rw [le_sub_iff_add_le, le_div_iff₀ he, mul_comm]
    exact h P hP
  rw [← Int.toNat_natCast ((torsionOrder F).factorization p)]
  exact Int.toNat_le_toNat (Int.le_floor.2 (mod_cast hle))

/-- The local-depth order is positive. -/
theorem localDepthOrder_pos (I : Ideal (𝓞 F)) : 0 < localDepthOrder F I :=
  Finset.prod_pos fun _ hq ↦ pow_pos (Nat.pos_of_mem_primeFactors hq) _

/-- The `p`-adic valuation of the local-depth order `r(I)` is the truncated local-depth exponent
`j(I, p)`, for every `p`. -/
@[simp]
theorem factorization_localDepthOrder (I : Ideal (𝓞 F)) (p : ℕ) :
    (localDepthOrder F I).factorization p = localDepthExponent F I p := by
  rw [localDepthOrder, Nat.factorization_prod fun q hq ↦
    pow_ne_zero _ (Nat.pos_of_mem_primeFactors hq).ne', Finsupp.finsetSum_apply]
  by_cases hp : p ∈ (torsionOrder F).primeFactors
  · rw [Finset.sum_eq_single p (fun q hq hqp ↦ ?_) (absurd hp),
      (Nat.prime_of_mem_primeFactors hp).factorization_pow, Finsupp.single_eq_same]
    rw [(Nat.prime_of_mem_primeFactors hq).factorization_pow, Finsupp.single_eq_of_ne hqp.symm]
  · refine (Finset.sum_eq_zero fun q hq ↦ ?_).trans
      (localDepthExponent_eq_zero_of_notMem_primeFactors I hp).symm
    rw [(Nat.prime_of_mem_primeFactors hq).factorization_pow,
      Finsupp.single_eq_of_ne (ne_of_mem_of_not_mem hq hp).symm]

/-- The local-depth order `r(I)` divides the number `m` of roots of unity of `F`. -/
theorem localDepthOrder_dvd_torsionOrder (I : Ideal (𝓞 F)) :
    localDepthOrder F I ∣ torsionOrder F :=
  (Nat.factorization_le_iff_dvd (localDepthOrder_pos I).ne' (torsionOrder_ne_zero F)).1
    fun p ↦ by simpa using localDepthExponent_le_factorization I p

/-- The local-depth order of the unit ideal is `1`. -/
@[simp]
theorem localDepthOrder_top : localDepthOrder F ⊤ = 1 :=
  Finset.prod_eq_one fun p _ ↦ by rw [localDepthExponent_top, pow_zero]

/-- The local-depth order grows with the depth of the level: `r(I) ∣ r(J)` for a nonzero ideal
`J ≤ I`. -/
theorem localDepthOrder_dvd_of_le (hJ : J ≠ ⊥) (hJI : J ≤ I) :
    localDepthOrder F I ∣ localDepthOrder F J :=
  Finset.prod_dvd_prod_of_dvd _ _ fun p _ ↦ pow_dvd_pow p (localDepthExponent_le_of_le hJ hJI p)

/-- **The full-depth criterion.** If `ord_P(I) ≥ e(P | p) (ord_p m + 1 / (p - 1))` for every prime
`p` dividing the number `m` of roots of unity of `F` and every prime `P` above `p`, then the
local-depth order of `I` is `m`. -/
theorem localDepthOrder_eq_torsionOrder
    (h : ∀ p ∈ (torsionOrder F).primeFactors, ∀ P ∈ (span {(p : ℤ)}).primesOver (𝓞 F),
      (P.ramificationIdx ℤ : ℚ) * ((torsionOrder F).factorization p + 1 / ((p : ℚ) - 1)) ≤
        (normalizedFactors I).count P) :
    localDepthOrder F I = torsionOrder F := by
  rw [localDepthOrder, Finset.prod_congr rfl fun p hp ↦ by
      rw [localDepthExponent_eq_factorization (h p hp)],
    ← Nat.prod_primeFactors_pow_factorization (torsionOrder_ne_zero F)]

end TauCeti.NumberField
