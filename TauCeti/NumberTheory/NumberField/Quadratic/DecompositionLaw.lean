/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Multiquadratic.Quadratic.Character
public import TauCeti.NumberTheory.NumberField.Quadratic.PrimeDecomposition
import TauCeti.NumberTheory.NumberField.Quadratic.Radicand
import TauCeti.RingTheory.Ideal.Maps

/-!
# The quadratic character and the explicit factorization of primes in `ℚ(√d)`

Let `d ≠ 1` be a squarefree (hence nonsquare) integer, `K = QuadraticAlgebra ℚ d 0` the model of
`ℚ(√d)` and `D` its discriminant, with quadratic character
`χ_D = TauCeti.Multiquadratic.fundamentalDiscriminantChar D`.
The decomposition law `TauCeti.Multiquadratic.fundamentalDiscriminantChar_discr_eq_zero_iff` and its
companions read `χ_D(p)` off the number of primes of `𝓞 K` above `p` and off ramification. This
file reads it off the explicit prime ideals of
`QuadraticAlgebra.isPrime_and_natCast_mem_iff_of_mod_four_ne_one` and
`QuadraticAlgebra.isPrime_and_natCast_mem_iff_of_mod_four_eq_one`. For every rational prime `p`,
the prime `2` included, write `√d ∈ 𝓞 K` for `NumberField.integralSqrt` and
`η = (1 + √d)/2` for `NumberField.halfGen`.

* For `d ≢ 1 (mod 4)`, so `D = 4d`:
  `χ_D(p) = 0` iff `p 𝓞 K = (p, √d - r) ^ 2` for some `r` with `r² ≡ d (mod p)`;
  `χ_D(p) = 1` iff `p 𝓞 K = (p, √d - r) (p, √d + r)` with distinct factors for such an `r`;
  `χ_D(p) = -1` iff `p 𝓞 K` is prime, which holds for every quadratic field `K`.
* For `d ≡ 1 (mod 4)`, so `D = d`, the same holds with the primes `(p, η - r)` and
  `(p, η - (1 - r))` for the roots `r` of `X² - X - (d - 1)/4` modulo `p`.

## Main results

* `QuadraticAlgebra.fundamentalDiscriminantChar_discr_eq_zero_iff_of_mod_four_ne_one`,
  `QuadraticAlgebra.fundamentalDiscriminantChar_discr_eq_one_iff_of_mod_four_ne_one`:
  ramified and split primes for `d ≢ 1 (mod 4)`.
* `QuadraticAlgebra.fundamentalDiscriminantChar_discr_eq_zero_iff_of_mod_four_eq_one`,
  `QuadraticAlgebra.fundamentalDiscriminantChar_discr_eq_one_iff_of_mod_four_eq_one`:
  the same for `d ≡ 1 (mod 4)`.
* `TauCeti.Multiquadratic.fundamentalDiscriminantChar_discr_eq_neg_one_iff_isPrime`: inert primes,
  for every quadratic field `K`: `χ_D(p) = -1` iff `p 𝓞 K` is prime.

## References

* D. A. Cox, *Primes of the Form x² + ny²*, §5.B.
* D. A. Marcus, *Number Fields*, Chapter 3, Theorem 25.
-/

public section

open NumberField Ideal Module
open TauCeti.Multiquadratic (fundamentalDiscriminantChar isFundamentalDiscr_discr
  fundamentalDiscriminantChar_isQuadratic fundamentalDiscriminantChar_discr_eq_zero_iff
  fundamentalDiscriminantChar_discr_eq_one_iff fundamentalDiscriminantChar_discr_eq_neg_one_iff)

namespace QuadraticAlgebra

/-! ### The decomposition law from an explicit factorization -/

section General

/-! Throughout this section `K` is a quadratic field and `p` a prime. The hypotheses describe an
explicit factorization of `p`: for each integer `r` with `root r`, `p 𝓞 K = P r * P' r` is a product
of maximal ideals, equal exactly when `p` divides the discriminant; `p 𝓞 K` is maximal exactly when
there is no such `r`; and such an `r` exists when `p` divides the discriminant. -/

variable {K : Type*} [Field K] [NumberField K] {p : ℕ} [Fact p.Prime] (hK : finrank ℚ K = 2)
  {root : ℤ → Prop} {P P' : ℤ → Ideal (𝓞 K)}
  (hmax : (span {(p : 𝓞 K)}).IsMaximal ↔ ∀ r, ¬ root r)
  (hPmax : ∀ r, root r → (P r).IsMaximal) (hP'max : ∀ r, root r → (P' r).IsMaximal)
  (hprod : ∀ r, root r → P r * P' r = span {(p : 𝓞 K)})
  (heq : ∀ r, root r → (P r = P' r ↔ (p : ℤ) ∣ NumberField.discr K))
  (hram : (p : ℤ) ∣ NumberField.discr K → ∃ r, root r)

/-- `p 𝓞 K` is prime exactly when it is maximal: `𝓞 K` has dimension one and `p ≠ 0`. -/
private theorem isPrime_span_natCast_iff_isMaximal :
    (span {(p : 𝓞 K)}).IsPrime ↔ (span {(p : 𝓞 K)}).IsMaximal := by
  refine ⟨fun h => h.isMaximal ?_, IsMaximal.isPrime⟩
  rw [Ne, span_singleton_eq_bot]
  exact_mod_cast (Fact.out : p.Prime).ne_zero

/-- The character `χ_D` of a quadratic field vanishes at `p` exactly when `p` divides `D`. -/
private theorem fundamentalDiscriminantChar_discr_eq_zero_iff_dvd :
    fundamentalDiscriminantChar (NumberField.discr K) (isFundamentalDiscr_discr hK) p = 0 ↔
      (p : ℤ) ∣ NumberField.discr K :=
  (fundamentalDiscriminantChar_discr_eq_zero_iff hK p).trans
    (mem_ramifiedPrimes_iff_dvd_discr Fact.out)

include hmax hPmax hP'max hprod heq hram in
/-- **Inert primes from an explicit factorization.** `χ_D(p) = -1` exactly when `p 𝓞 K` is prime:
then `p 𝓞 K` is the only prime above `p`, while over a root `r` lie the two primes `P r ≠ P' r`. -/
private theorem fundamentalDiscriminantChar_discr_eq_neg_one_iff_isPrime_of_factorization :
    fundamentalDiscriminantChar (NumberField.discr K) (isFundamentalDiscr_discr hK) p = -1 ↔
      (span {(p : 𝓞 K)}).IsPrime := by
  have hzero := fundamentalDiscriminantChar_discr_eq_zero_iff_dvd (p := p) hK
  -- A prime of `𝓞 K` lies over `p` exactly when it contains `p`.
  have hover : ∀ Q : Ideal (𝓞 K), Q.IsPrime →
      (Q ∈ primesOver (span {(p : ℤ)}) (𝓞 K) ↔ (p : 𝓞 K) ∈ Q) := fun Q hQ => by
    have h := liesOver_span_iff hQ.ne_top (Nat.prime_iff_prime_int.mp (Fact.out : p.Prime))
    simp only [algebraMap_int_eq, eq_intCast, Int.cast_natCast] at h
    exact ⟨fun h' => h.mp h'.2, fun h' => ⟨hQ, h.mpr h'⟩⟩
  rw [isPrime_span_natCast_iff_isMaximal, hmax]
  constructor
  · -- Over a root `r` lie the two primes `P r ≠ P' r`, but an inert `p` has a single prime over it.
    intro h r hr
    have hnd : ¬ (p : ℤ) ∣ NumberField.discr K := fun hd => by
      rw [hzero.mpr hd] at h
      exact absurd h (by decide)
    have hmem : ∀ Q, Q.IsMaximal → span {(p : 𝓞 K)} ≤ Q →
        Q ∈ primesOver (span {(p : ℤ)}) (𝓞 K) := fun Q hQ hle =>
      (hover Q hQ.isPrime).mpr (hle (mem_span_singleton_self _))
    obtain ⟨Q, hQ⟩ := Set.ncard_eq_one.mp
      ((fundamentalDiscriminantChar_discr_eq_neg_one_iff hK p).mp h).2
    have h1 := hQ ▸ hmem (P r) (hPmax r hr) (hprod r hr ▸ mul_le_left)
    have h2 := hQ ▸ hmem (P' r) (hP'max r hr) (hprod r hr ▸ mul_le_right)
    exact hnd ((heq r hr).mp ((Set.mem_singleton_iff.mp h1).trans
      (Set.mem_singleton_iff.mp h2).symm))
  · -- Without a root, `p 𝓞 K` is maximal, so it is the only prime above `p`, and `p` is
    -- unramified.
    intro hno
    have hmax' := hmax.mpr hno
    have h0 : fundamentalDiscriminantChar (NumberField.discr K) (isFundamentalDiscr_discr hK) p ≠
        0 := fun h => by
      obtain ⟨r, hr⟩ := hram (hzero.mp h)
      exact hno r hr
    have h1 : fundamentalDiscriminantChar (NumberField.discr K) (isFundamentalDiscr_discr hK) p ≠
        1 := by
      intro h
      have hsub : primesOver (span {(p : ℤ)}) (𝓞 K) ⊆ {span {(p : 𝓞 K)}} := fun Q hQ =>
        (hmax'.eq_of_le hQ.1.ne_top
          (span_singleton_le_iff_mem _ |>.mpr ((hover Q hQ.1).mp hQ))).symm
      have := Set.ncard_le_ncard hsub
      rw [(fundamentalDiscriminantChar_discr_eq_one_iff hK p).mp h, Set.ncard_singleton] at this
      omega
    rcases fundamentalDiscriminantChar_isQuadratic _ p with h | h | h
    · exact absurd h h0
    · exact absurd h h1
    · exact h

include hPmax hprod heq hram in
/-- **Ramified primes from an explicit factorization.** `χ_D(p) = 0` exactly when
`p 𝓞 K = (P r) ^ 2` for a root `r`. -/
private theorem fundamentalDiscriminantChar_discr_eq_zero_iff_exists_sq :
    fundamentalDiscriminantChar (NumberField.discr K) (isFundamentalDiscr_discr hK) p = 0 ↔
      ∃ r, root r ∧ P r ^ 2 = span {(p : 𝓞 K)} := by
  rw [fundamentalDiscriminantChar_discr_eq_zero_iff_dvd hK]
  refine ⟨fun h => ?_, fun ⟨r, hr, hsq⟩ => (heq r hr).mp ?_⟩
  · obtain ⟨r, hr⟩ := hram h
    exact ⟨r, hr, by rw [sq, ← hprod r hr, (heq r hr).mpr h]⟩
  · rw [← hprod r hr, sq] at hsq
    exact mul_right_inj' (hPmax r hr).ne_bot_of_isIntegral_int |>.mp hsq

include hmax hPmax hP'max hprod heq hram in
/-- **Split primes from an explicit factorization.** `χ_D(p) = 1` exactly when
`p 𝓞 K = P r * P' r` with `P r ≠ P' r` for a root `r`. -/
private theorem fundamentalDiscriminantChar_discr_eq_one_iff_exists_mul :
    fundamentalDiscriminantChar (NumberField.discr K) (isFundamentalDiscr_discr hK) p = 1 ↔
      ∃ r, root r ∧ P r ≠ P' r ∧ P r * P' r = span {(p : 𝓞 K)} := by
  have h0 := fundamentalDiscriminantChar_discr_eq_zero_iff_dvd (p := p) hK
  have h1 := (fundamentalDiscriminantChar_discr_eq_neg_one_iff_isPrime_of_factorization hK hmax
    hPmax hP'max hprod heq hram).trans (isPrime_span_natCast_iff_isMaximal.trans hmax)
  constructor
  · -- `χ_D(p) = 1` rules out the inert case, giving a root `r`, and the ramified case.
    intro h
    obtain ⟨r, hr⟩ : ∃ r, root r := by
      by_contra hno
      rw [h1.mpr (by simpa using hno)] at h
      exact absurd h (by decide)
    refine ⟨r, hr, fun he => ?_, hprod r hr⟩
    rw [h0.mpr ((heq r hr).mp he)] at h
    exact absurd h (by decide)
  · rintro ⟨r, hr, hne, -⟩
    rcases fundamentalDiscriminantChar_isQuadratic _ p with h | h | h
    · exact absurd ((heq r hr).mpr (h0.mp h)) hne
    · exact h
    · exact absurd hr (h1.mp h r)

end General

variable {d : ℤ} [Fact (¬ IsSquare d)] (hsf : Squarefree d) (p : ℕ) [Fact p.Prime]

/-! ### The case `d ≢ 1 (mod 4)` -/

section ModFourNeOne

variable (hd4 : d % 4 ≠ 1)
include hsf hd4

/-- A prime dividing the discriminant `4d` divides `r² - d` for `r = d`. -/
private theorem dvd_sq_sub_of_dvd_discr_of_mod_four_ne_one
    (hp : (p : ℤ) ∣ NumberField.discr (QuadraticAlgebra ℚ (d : ℚ) 0)) : (p : ℤ) ∣ d ^ 2 - d := by
  have hp' : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp Fact.out
  rw [discr_eq_four_mul_of_mod_four_ne_one hsf hd4] at hp
  rw [show d ^ 2 - d = d * (d - 1) by ring]
  rcases hp'.dvd_or_dvd hp with h4 | hd
  · -- `p ∣ 4` forces `p ∣ 2`, and `d (d - 1)` is even.
    have h2 : (p : ℤ) ∣ 2 := hp'.dvd_of_dvd_pow (n := 2) (by norm_num at h4 ⊢; exact h4)
    exact h2.trans (Int.even_mul_pred_self d).two_dvd
  · exact dvd_mul_of_dvd_left hd _

/-- For `d ≢ 1 (mod 4)` and a square root `r` of `d` modulo `p`, the ideal `(p, √d + r)` is
maximal: it is `(p, √d - (-r))`. -/
private theorem isMaximal_span_natCast_integralSqrt_add {r : ℤ} (hr : (p : ℤ) ∣ r ^ 2 - d) :
    (span {(p : 𝓞 (QuadraticAlgebra ℚ (d : ℚ) 0)),
      integralSqrt (omega_sq_eq_algebraMap_int (d := d)) + r}).IsMaximal := by
  simpa [sub_eq_add_neg] using
    isMaximal_span_natCast_integralSqrt_sub hsf hd4 (p := p) (r := -r) (by simpa using hr)

/-- **Ramified primes for `d ≢ 1 (mod 4)`.** The character `χ_D` of `ℚ(√d)` vanishes at a prime
`p` exactly when `p 𝓞 ℚ(√d) = (p, √d - r) ^ 2` for some square root `r` of `d` modulo `p`. -/
theorem fundamentalDiscriminantChar_discr_eq_zero_iff_of_mod_four_ne_one :
    fundamentalDiscriminantChar (NumberField.discr (QuadraticAlgebra ℚ (d : ℚ) 0))
        (isFundamentalDiscr_discr (finrank_eq_two (d : ℚ) 0)) p = 0 ↔
      ∃ r : ℤ, (p : ℤ) ∣ r ^ 2 - d ∧
        span {(p : 𝓞 (QuadraticAlgebra ℚ (d : ℚ) 0)),
          integralSqrt (omega_sq_eq_algebraMap_int (d := d)) - r} ^ 2 =
          span {(p : 𝓞 (QuadraticAlgebra ℚ (d : ℚ) 0))} :=
  fundamentalDiscriminantChar_discr_eq_zero_iff_exists_sq (finrank_eq_two (d : ℚ) 0)
    (fun _ hr => isMaximal_span_natCast_integralSqrt_sub hsf hd4 hr)
    (fun _ hr => span_natCast_integralSqrt_sub_mul_span_natCast_integralSqrt_add hsf hd4 hr)
    (fun _ hr => span_natCast_integralSqrt_sub_eq_span_natCast_integralSqrt_add_iff hsf hd4 hr)
    (fun h => ⟨d, dvd_sq_sub_of_dvd_discr_of_mod_four_ne_one hsf p hd4 h⟩)

/-- **Split primes for `d ≢ 1 (mod 4)`.** The character `χ_D` of `ℚ(√d)` takes the value `1` at a
prime `p` exactly when `p 𝓞 ℚ(√d)` is the product `(p, √d - r) (p, √d + r)` of two distinct
primes for some square root `r` of `d` modulo `p`. -/
theorem fundamentalDiscriminantChar_discr_eq_one_iff_of_mod_four_ne_one :
    fundamentalDiscriminantChar (NumberField.discr (QuadraticAlgebra ℚ (d : ℚ) 0))
        (isFundamentalDiscr_discr (finrank_eq_two (d : ℚ) 0)) p = 1 ↔
      ∃ r : ℤ, (p : ℤ) ∣ r ^ 2 - d ∧
        span {(p : 𝓞 (QuadraticAlgebra ℚ (d : ℚ) 0)),
            integralSqrt (omega_sq_eq_algebraMap_int (d := d)) - r} ≠
          span {(p : 𝓞 (QuadraticAlgebra ℚ (d : ℚ) 0)),
            integralSqrt (omega_sq_eq_algebraMap_int (d := d)) + r} ∧
        span {(p : 𝓞 (QuadraticAlgebra ℚ (d : ℚ) 0)),
            integralSqrt (omega_sq_eq_algebraMap_int (d := d)) - r} *
          span {(p : 𝓞 (QuadraticAlgebra ℚ (d : ℚ) 0)),
            integralSqrt (omega_sq_eq_algebraMap_int (d := d)) + r} =
          span {(p : 𝓞 (QuadraticAlgebra ℚ (d : ℚ) 0))} :=
  fundamentalDiscriminantChar_discr_eq_one_iff_exists_mul (finrank_eq_two (d : ℚ) 0)
    (isMaximal_span_natCast_iff_of_mod_four_ne_one hsf hd4)
    (fun _ hr => isMaximal_span_natCast_integralSqrt_sub hsf hd4 hr)
    (fun _ hr => isMaximal_span_natCast_integralSqrt_add hsf p hd4 hr)
    (fun _ hr => span_natCast_integralSqrt_sub_mul_span_natCast_integralSqrt_add hsf hd4 hr)
    (fun _ hr => span_natCast_integralSqrt_sub_eq_span_natCast_integralSqrt_add_iff hsf hd4 hr)
    (fun h => ⟨d, dvd_sq_sub_of_dvd_discr_of_mod_four_ne_one hsf p hd4 h⟩)

/-- Inert primes for `d ≢ 1 (mod 4)`: `χ_D(p) = -1` exactly when `p 𝓞 ℚ(√d)` is prime. The
statement holds for every quadratic field
(`TauCeti.Multiquadratic.fundamentalDiscriminantChar_discr_eq_neg_one_iff_isPrime`). -/
private theorem fundamentalDiscriminantChar_discr_eq_neg_one_iff_of_mod_four_ne_one :
    fundamentalDiscriminantChar (NumberField.discr (QuadraticAlgebra ℚ (d : ℚ) 0))
        (isFundamentalDiscr_discr (finrank_eq_two (d : ℚ) 0)) p = -1 ↔
      (span {(p : 𝓞 (QuadraticAlgebra ℚ (d : ℚ) 0))}).IsPrime :=
  fundamentalDiscriminantChar_discr_eq_neg_one_iff_isPrime_of_factorization
    (finrank_eq_two (d : ℚ) 0)
    (isMaximal_span_natCast_iff_of_mod_four_ne_one hsf hd4)
    (fun _ hr => isMaximal_span_natCast_integralSqrt_sub hsf hd4 hr)
    (fun _ hr => isMaximal_span_natCast_integralSqrt_add hsf p hd4 hr)
    (fun _ hr => span_natCast_integralSqrt_sub_mul_span_natCast_integralSqrt_add hsf hd4 hr)
    (fun _ hr => span_natCast_integralSqrt_sub_eq_span_natCast_integralSqrt_add_iff hsf hd4 hr)
    (fun h => ⟨d, dvd_sq_sub_of_dvd_discr_of_mod_four_ne_one hsf p hd4 h⟩)

end ModFourNeOne

/-! ### The case `d ≡ 1 (mod 4)` -/

section ModFourEqOne

variable (hd4 : d % 4 = 1)
include hsf hd4

omit [Fact p.Prime] in
/-- A prime dividing the discriminant `d = 4k + 1` divides `r² - r - (d - 1)/4 = k d` for
`r = 2k + 1`. -/
private theorem dvd_sq_sub_sub_of_dvd_discr_of_mod_four_eq_one
    (hp : (p : ℤ) ∣ NumberField.discr (QuadraticAlgebra ℚ (d : ℚ) 0)) :
    (p : ℤ) ∣ (2 * ((d - 1) / 4) + 1) ^ 2 - (2 * ((d - 1) / 4) + 1) - (d - 1) / 4 := by
  rw [discr_eq_of_mod_four_eq_one hsf hd4] at hp
  obtain ⟨k, hk⟩ : ∃ k, (d - 1) / 4 = k := ⟨_, rfl⟩
  have hd : d = 4 * k + 1 := by omega
  rw [hk, show (2 * k + 1) ^ 2 - (2 * k + 1) - k = k * d by rw [hd]; ring]
  exact dvd_mul_of_dvd_right hp _

/-- For `d ≡ 1 (mod 4)` and a root `r` of `X² - X - (d - 1)/4` modulo `p`, the ideal
`(p, η - (1 - r))` is maximal: `1 - r` is the other root. -/
private theorem isMaximal_span_natCast_halfGen_sub_one_sub {r : ℤ}
    (hr : (p : ℤ) ∣ r ^ 2 - r - (d - 1) / 4) :
    (span {(p : 𝓞 (QuadraticAlgebra ℚ (d : ℚ) 0)),
      halfGen minpoly_integralSqrt_omega hd4 - (1 - r : ℤ)}).IsMaximal :=
  isMaximal_span_natCast_halfGen_sub hsf hd4 <| by
    rwa [show (1 - r) ^ 2 - (1 - r) - (d - 1) / 4 = r ^ 2 - r - (d - 1) / 4 by ring]

/-- **Ramified primes for `d ≡ 1 (mod 4)`.** The character `χ_D` of `ℚ(√d)` vanishes at a prime
`p` exactly when `p 𝓞 ℚ(√d) = (p, η - r) ^ 2` for some root `r` of `X² - X - (d - 1)/4` modulo
`p`, where `η = (1 + √d)/2`. -/
theorem fundamentalDiscriminantChar_discr_eq_zero_iff_of_mod_four_eq_one :
    fundamentalDiscriminantChar (NumberField.discr (QuadraticAlgebra ℚ (d : ℚ) 0))
        (isFundamentalDiscr_discr (finrank_eq_two (d : ℚ) 0)) p = 0 ↔
      ∃ r : ℤ, (p : ℤ) ∣ r ^ 2 - r - (d - 1) / 4 ∧
        span {(p : 𝓞 (QuadraticAlgebra ℚ (d : ℚ) 0)),
          halfGen minpoly_integralSqrt_omega hd4 - r} ^ 2 =
          span {(p : 𝓞 (QuadraticAlgebra ℚ (d : ℚ) 0))} :=
  fundamentalDiscriminantChar_discr_eq_zero_iff_exists_sq (finrank_eq_two (d : ℚ) 0)
    (fun _ hr => isMaximal_span_natCast_halfGen_sub hsf hd4 hr)
    (fun _ hr => span_natCast_halfGen_sub_mul_span_natCast_halfGen_sub hsf hd4 hr)
    (fun _ hr => span_natCast_halfGen_sub_eq_span_natCast_halfGen_sub_iff hsf hd4 hr)
    (fun h => ⟨_, dvd_sq_sub_sub_of_dvd_discr_of_mod_four_eq_one hsf p hd4 h⟩)

/-- **Split primes for `d ≡ 1 (mod 4)`.** The character `χ_D` of `ℚ(√d)` takes the value `1` at a
prime `p` exactly when `p 𝓞 ℚ(√d)` is the product `(p, η - r) (p, η - (1 - r))` of two distinct
primes for some root `r` of `X² - X - (d - 1)/4` modulo `p`, where `η = (1 + √d)/2`. -/
theorem fundamentalDiscriminantChar_discr_eq_one_iff_of_mod_four_eq_one :
    fundamentalDiscriminantChar (NumberField.discr (QuadraticAlgebra ℚ (d : ℚ) 0))
        (isFundamentalDiscr_discr (finrank_eq_two (d : ℚ) 0)) p = 1 ↔
      ∃ r : ℤ, (p : ℤ) ∣ r ^ 2 - r - (d - 1) / 4 ∧
        span {(p : 𝓞 (QuadraticAlgebra ℚ (d : ℚ) 0)),
            halfGen minpoly_integralSqrt_omega hd4 - r} ≠
          span {(p : 𝓞 (QuadraticAlgebra ℚ (d : ℚ) 0)),
            halfGen minpoly_integralSqrt_omega hd4 - (1 - r : ℤ)} ∧
        span {(p : 𝓞 (QuadraticAlgebra ℚ (d : ℚ) 0)),
            halfGen minpoly_integralSqrt_omega hd4 - r} *
          span {(p : 𝓞 (QuadraticAlgebra ℚ (d : ℚ) 0)),
            halfGen minpoly_integralSqrt_omega hd4 - (1 - r : ℤ)} =
          span {(p : 𝓞 (QuadraticAlgebra ℚ (d : ℚ) 0))} :=
  fundamentalDiscriminantChar_discr_eq_one_iff_exists_mul (finrank_eq_two (d : ℚ) 0)
    (isMaximal_span_natCast_iff_of_mod_four_eq_one hsf hd4)
    (fun _ hr => isMaximal_span_natCast_halfGen_sub hsf hd4 hr)
    (fun _ hr => isMaximal_span_natCast_halfGen_sub_one_sub hsf p hd4 hr)
    (fun _ hr => span_natCast_halfGen_sub_mul_span_natCast_halfGen_sub hsf hd4 hr)
    (fun _ hr => span_natCast_halfGen_sub_eq_span_natCast_halfGen_sub_iff hsf hd4 hr)
    (fun h => ⟨_, dvd_sq_sub_sub_of_dvd_discr_of_mod_four_eq_one hsf p hd4 h⟩)

/-- Inert primes for `d ≡ 1 (mod 4)`: `χ_D(p) = -1` exactly when `p 𝓞 ℚ(√d)` is prime. The
statement holds for every quadratic field
(`TauCeti.Multiquadratic.fundamentalDiscriminantChar_discr_eq_neg_one_iff_isPrime`). -/
private theorem fundamentalDiscriminantChar_discr_eq_neg_one_iff_of_mod_four_eq_one :
    fundamentalDiscriminantChar (NumberField.discr (QuadraticAlgebra ℚ (d : ℚ) 0))
        (isFundamentalDiscr_discr (finrank_eq_two (d : ℚ) 0)) p = -1 ↔
      (span {(p : 𝓞 (QuadraticAlgebra ℚ (d : ℚ) 0))}).IsPrime :=
  fundamentalDiscriminantChar_discr_eq_neg_one_iff_isPrime_of_factorization
    (finrank_eq_two (d : ℚ) 0)
    (isMaximal_span_natCast_iff_of_mod_four_eq_one hsf hd4)
    (fun _ hr => isMaximal_span_natCast_halfGen_sub hsf hd4 hr)
    (fun _ hr => isMaximal_span_natCast_halfGen_sub_one_sub hsf p hd4 hr)
    (fun _ hr => span_natCast_halfGen_sub_mul_span_natCast_halfGen_sub hsf hd4 hr)
    (fun _ hr => span_natCast_halfGen_sub_eq_span_natCast_halfGen_sub_iff hsf hd4 hr)
    (fun h => ⟨_, dvd_sq_sub_sub_of_dvd_discr_of_mod_four_eq_one hsf p hd4 h⟩)

end ModFourEqOne

end QuadraticAlgebra

/-! ### Inert primes in an arbitrary quadratic field -/

namespace TauCeti.Multiquadratic

variable {K : Type*} [Field K] [NumberField K]

/-- **`χ_D(p) = -1` exactly when `p` stays prime.** For a quadratic field `K` with discriminant `D`
and a prime `p`, the character `χ_D` takes the value `-1` at `p` iff `p 𝓞 K` is a prime ideal. -/
theorem fundamentalDiscriminantChar_discr_eq_neg_one_iff_isPrime (hK : finrank ℚ K = 2) (p : ℕ)
    [Fact p.Prime] :
    fundamentalDiscriminantChar (NumberField.discr K) (isFundamentalDiscr_discr hK) p = -1 ↔
      (span {(p : 𝓞 K)}).IsPrime := by
  -- Transport to the model `ℚ(√d)` of `K`, which has the same `χ_D` and the same ideal `p 𝓞 K`.
  obtain ⟨θ, d, hmin, -, hsf⟩ := exists_minpoly_eq_X_sq_sub_C_and_adjoin_eq_top hK
  have : Fact (¬ IsSquare d) := ⟨Rat.isSquare_intCast_iff.not.mp (not_isSquare_radicand hmin)⟩
  obtain ⟨σ⟩ := nonempty_algEquiv_quadraticAlgebra hK hmin
  have hχ := fundamentalDiscriminantChar_discr_apply_eq_of_algEquiv hK σ p
  rw [Int.cast_natCast, Int.cast_natCast] at hχ
  have hspan : (span {(p : 𝓞 K)}).map (RingOfIntegers.mapRingEquiv σ.toRingEquiv) =
      span {(p : 𝓞 (QuadraticAlgebra ℚ (d : ℚ) 0))} := by
    rw [map_span, Set.image_singleton, map_natCast]
  rw [hχ, ← isPrime_map_iff_of_bijective _ (RingOfIntegers.mapRingEquiv σ.toRingEquiv).bijective,
    hspan]
  by_cases hd4 : d % 4 = 1
  · exact QuadraticAlgebra.fundamentalDiscriminantChar_discr_eq_neg_one_iff_of_mod_four_eq_one
      hsf p hd4
  · exact QuadraticAlgebra.fundamentalDiscriminantChar_discr_eq_neg_one_iff_of_mod_four_ne_one
      hsf p hd4

end TauCeti.Multiquadratic
