/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.NumberTheory.LegendreSymbol.Basic
public import TauCeti.NumberTheory.Padics.Basic
public import TauCeti.NumberTheory.QuadraticOrder.ComplexEmbedding
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# The numbers attached to a prime in `ℚ(√-d)`

Let `d` be a prime, `K = ℚ(√-d) ⊆ ℂ` with `√-d = i √d`, and `χ_K = (· / d)`, the Legendre symbol
`legendreSym d`. When `d ≡ 3 (mod 4)`, as for the primes `d ≡ 7 (mod 8)` of the applications,
quadratic reciprocity makes `χ_K` the splitting character of `K`: a prime `p` splits in `K` when
`(p / d) = 1`, is inert when `(p / d) = -1`, and ramifies when `p = d`. The Taylor coefficients of
the theta function of an elliptic curve with complex multiplication by the integers of `K`, and
its formal group, are studied at `p` through the following numbers.

* `piPrime d p = π_p`: `√-d` if `p = d` and `p` otherwise, an element of the integers of `K`.
* `piPrimeValuation d p = v(π_p)`: `1 / 2` if `p = d` and `1` otherwise, the valuation of `π_p`
  normalised by `v(p) = 1`.
* `primeNorm d p = q_p`: `p²` if `(p / d) = -1` and `p` otherwise; for `d ≡ 3 (mod 4)` and a prime
  `p`, the norm of a prime of `K` above `p`.
* `rhoPrime d p = ρ_p = v(π_p) / (q_p - 1)`, the valuation of the scale that turns the formal
  parameter of the curve into a Lubin–Tate parameter for `π_p`.
* `gammaPrime d p = γ_p = 1 / (p - 1) - ρ_p`, the rate per derivative at which the Taylor
  coefficients of theta functions are divisible at `p`.
* `partnerExponents d p = I_p°`: all `e ≥ 0` if `p = d`, the odd `e ≥ 0` if `(p / d) = -1`, and no
  `e` otherwise; `positivePartnerExponents d p = I_p` is its subset of positive exponents.

This file computes `ρ_p` and `γ_p` in the three cases and bounds them
(`rhoPrime_of_ne_of_legendreSym_ne_neg_one`, `gammaPrime_of_legendreSym_eq_neg_one`,
`gammaPrime_self`, `gammaPrime_le_one`, …); it expresses `γ_p` as the series
`v(π_p) · ∑_{e ∈ I_p} p ^ (-e)` (`hasSum_gammaPrime`, `hasSum_div_pow_positivePartnerExponents`);
it shows that `q_p` is a positive power of `p`, greater than `1` and with `q_p - 1` prime to `p`
(`exists_primeNorm_eq_pow`, `one_lt_primeNorm`, `coprime_primeNorm_sub_one`); and it proves that
`π_p` lies in the integers `complexOrder (-d)` of `K`, that `π_p · conj π_p = q_p` when the prime
`p` does not split, and that `π_p` has absolute value `p ^ (-v(π_p)) < 1` under every ring
homomorphism from `ℂ` to a normed division ring over `ℚ_p`, such as `ℂ_p`
(`piPrime_mem_complexOrder`, `piPrime_mul_conj`, `norm_map_piPrime`, `norm_map_piPrime_lt_one`).

## Main definitions

* `TauCeti.ComplexMultiplication.piPrime`, `TauCeti.ComplexMultiplication.piPrimeValuation`,
  `TauCeti.ComplexMultiplication.primeNorm`, `TauCeti.ComplexMultiplication.rhoPrime`,
  `TauCeti.ComplexMultiplication.gammaPrime`, `TauCeti.ComplexMultiplication.partnerExponents`,
  `TauCeti.ComplexMultiplication.positivePartnerExponents`.

## References

* J. Lubin, J. Tate, *Formal complex multiplication in local fields*, Ann. of Math. 81 (1965).
* The definitions follow the formal proof in the folder `grh` of
  https://github.com/lsernau/grh-lean at commit 72fead102f663d5c7a407964a13dc0cf9d977207, file
  `src/Lib/CM/FormalGroup/PrimeNotation.lean` (`New.piPrime`, `New.piPrimeValuation`,
  `New.varpiValuation`, `New.gammaPrime`, `New.partnerExponents`,
  `New.positivePartnerExponents`); `q_p` is `New.primeNorm` of
  `src/Lib/General/NumberTheory/ImaginaryQuadraticField.lean`.
-/

public section

open Complex

namespace TauCeti.ComplexMultiplication

variable (d p : ℕ)

/-- `π_p`: the square root `√-d = i √d` of `-d` if `p = d`, and `p` otherwise. -/
noncomputable def piPrime : ℂ := if p = d then I * (√(d : ℝ) : ℂ) else p

/-- `v(π_p)`: `1 / 2` if `p = d` and `1` otherwise, the valuation of `π_p` at `p` normalised by
`v(p) = 1` (`norm_map_piPrime`). -/
noncomputable def piPrimeValuation : ℝ := if p = d then 1 / 2 else 1

section Basic

variable {d p}

theorem piPrime_self : piPrime d d = I * (√(d : ℝ) : ℂ) := by
  simp [piPrime]

theorem piPrime_of_ne (h : p ≠ d) : piPrime d p = p := by
  simp [piPrime, h]

@[simp] theorem piPrimeValuation_self : piPrimeValuation d d = 1 / 2 := by
  simp [piPrimeValuation]

theorem piPrimeValuation_of_ne (h : p ≠ d) : piPrimeValuation d p = 1 := by
  simp [piPrimeValuation, h]

theorem piPrimeValuation_pos : 0 < piPrimeValuation d p := by
  unfold piPrimeValuation
  split_ifs <;> norm_num

theorem piPrimeValuation_le_one : piPrimeValuation d p ≤ 1 := by
  unfold piPrimeValuation
  split_ifs <;> norm_num

/-- The square of `√-d` is `-d`. -/
@[simp] theorem piPrime_self_sq : piPrime d d ^ 2 = -d := by
  rw [piPrime_self, mul_pow, I_sq, ← ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg d)]
  push_cast
  ring

/-- `π_p ≠ 0` for `p ≠ 0`. -/
theorem piPrime_ne_zero (hp : p ≠ 0) : piPrime d p ≠ 0 := by
  by_cases h : p = d
  · subst h
    rw [piPrime_self]
    exact mul_ne_zero I_ne_zero (ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr (by positivity)))
  · rw [piPrime_of_ne h]
    exact_mod_cast hp

/-- `π_p` lies in the order `ℤ[(-d + √-d) / 2] ⊆ ℂ`, which is the ring of integers of `ℚ(√-d)`
when `d` is a prime with `d ≡ 3 (mod 4)`. -/
theorem piPrime_mem_complexOrder (h0 : -(d : ℤ) ≤ 0) (hD : -(d : ℤ) % 4 = 0 ∨ -(d : ℤ) % 4 = 1) :
    piPrime d p ∈ QuadraticOrder.complexOrder (-d) h0 hD := by
  rw [QuadraticOrder.mem_complexOrder_iff]
  by_cases h : p = d
  · subst h
    refine ⟨p, 2, ?_⟩
    rw [piPrime_self, QuadraticOrder.complexGenerator_def]
    push_cast
    rw [neg_neg]
    ring
  · exact ⟨p, 0, by rw [piPrime_of_ne h]; simp⟩

/-- Under every ring homomorphism from `ℂ` to a normed division ring over `ℚ_p`, such as `ℂ_p`,
`π_p` has absolute value `p ^ (-v(π_p))`. -/
theorem norm_map_piPrime [Fact p.Prime] {K : Type*} [NormedDivisionRing K]
    [NormedAlgebra ℚ_[p] K] (ι : ℂ →+* K) :
    ‖ι (piPrime d p)‖ = (p : ℝ) ^ (-piPrimeValuation d p) := by
  by_cases h : p = d
  · subst h
    have hsq : ‖ι (piPrime p p)‖ ^ 2 = (p : ℝ)⁻¹ := by
      rw [← norm_pow, ← map_pow, piPrime_self_sq, map_neg, map_natCast, norm_neg,
        norm_natCast_p]
    rw [piPrimeValuation_self, Real.rpow_neg (Nat.cast_nonneg p), ← Real.sqrt_eq_rpow,
      ← Real.sqrt_inv, ← hsq, Real.sqrt_sq (norm_nonneg _)]
  · rw [piPrime_of_ne h, piPrimeValuation_of_ne h, map_natCast, norm_natCast_p, Real.rpow_neg_one]

/-- Under every ring homomorphism from `ℂ` to a normed division ring over `ℚ_p`, `π_p` has
absolute value less than `1`. -/
theorem norm_map_piPrime_lt_one [Fact p.Prime] {K : Type*} [NormedDivisionRing K]
    [NormedAlgebra ℚ_[p] K] (ι : ℂ →+* K) : ‖ι (piPrime d p)‖ < 1 := by
  rw [norm_map_piPrime]
  exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast (Fact.out : p.Prime).one_lt)
    (neg_lt_zero.mpr piPrimeValuation_pos)

end Basic

variable [Fact d.Prime]

/-- `q_p`: `p²` if `(p / d) = -1` and `p` otherwise. For `d ≡ 3 (mod 4)` and a prime `p`, it is the
norm of a prime of `ℚ(√-d)` above `p`. -/
def primeNorm : ℕ := if legendreSym d p = -1 then p ^ 2 else p

/-- `ρ_p = v(π_p) / (q_p - 1)`. -/
noncomputable def rhoPrime : ℝ := piPrimeValuation d p / ((primeNorm d p : ℝ) - 1)

/-- `γ_p = 1 / (p - 1) - ρ_p`. -/
noncomputable def gammaPrime : ℝ := 1 / ((p : ℝ) - 1) - rhoPrime d p

/-- `I_p°`: all `e` if `p = d`, the odd `e` if `(p / d) = -1`, and no `e` otherwise. -/
def partnerExponents : Set ℕ := {e | p = d ∨ legendreSym d p = -1 ∧ Odd e}

/-- `I_p`: the positive elements of `I_p°`. -/
def positivePartnerExponents : Set ℕ := {e | e ∈ partnerExponents d p ∧ 0 < e}

variable {d p}

theorem rhoPrime_def : rhoPrime d p = piPrimeValuation d p / ((primeNorm d p : ℝ) - 1) := by
  rw [rhoPrime]

theorem gammaPrime_def : gammaPrime d p = 1 / ((p : ℝ) - 1) - rhoPrime d p := by
  rw [gammaPrime]

theorem mem_partnerExponents_iff {e : ℕ} :
    e ∈ partnerExponents d p ↔ p = d ∨ legendreSym d p = -1 ∧ Odd e := by
  rw [partnerExponents, Set.mem_ofPred_eq]

theorem mem_positivePartnerExponents_iff {e : ℕ} :
    e ∈ positivePartnerExponents d p ↔ e ∈ partnerExponents d p ∧ 0 < e := by
  rw [positivePartnerExponents, Set.mem_ofPred_eq]

/-- A `p` with `(p / d) = -1` is not `d`, since `(d / d) = 0`. -/
private theorem ne_of_legendreSym_eq_neg_one (h : legendreSym d p = -1) : p ≠ d := by
  rintro rfl
  rw [(legendreSym.eq_zero_iff p p).mpr (by simp)] at h
  exact absurd h (by decide)

/-- A `p` with `(p / d) = -1` satisfies `2 ≤ p`, since `(0 / d) = 0` and `(1 / d) = 1`. -/
private theorem two_le_of_legendreSym_eq_neg_one (h : legendreSym d p = -1) : (2 : ℝ) ≤ p := by
  have : 2 ≤ p := by
    by_contra! hlt
    interval_cases p
    · rw [Nat.cast_zero, legendreSym.at_zero] at h; exact absurd h (by decide)
    · rw [Nat.cast_one, legendreSym.at_one] at h; exact absurd h (by decide)
  exact_mod_cast this

theorem primeNorm_of_legendreSym_eq_neg_one (h : legendreSym d p = -1) : primeNorm d p = p ^ 2 := by
  simp [primeNorm, h]

theorem primeNorm_of_legendreSym_ne_neg_one (h : legendreSym d p ≠ -1) : primeNorm d p = p := by
  simp [primeNorm, h]

@[simp] theorem primeNorm_self : primeNorm d d = d :=
  primeNorm_of_legendreSym_ne_neg_one fun h ↦ ne_of_legendreSym_eq_neg_one h rfl

/-- `ρ_p = 1 / (p - 1)` when `p ≠ d` and `(p / d) ≠ -1`, in particular when `p` splits. -/
theorem rhoPrime_of_ne_of_legendreSym_ne_neg_one (h₁ : p ≠ d) (h₂ : legendreSym d p ≠ -1) :
    rhoPrime d p = 1 / ((p : ℝ) - 1) := by
  rw [rhoPrime, piPrimeValuation_of_ne h₁, primeNorm_of_legendreSym_ne_neg_one h₂]

/-- `ρ_p = 1 / (p² - 1)` when `p` is inert. -/
theorem rhoPrime_of_legendreSym_eq_neg_one (h : legendreSym d p = -1) :
    rhoPrime d p = 1 / ((p : ℝ) ^ 2 - 1) := by
  rw [rhoPrime, piPrimeValuation_of_ne (ne_of_legendreSym_eq_neg_one h),
    primeNorm_of_legendreSym_eq_neg_one h, Nat.cast_pow]

theorem rhoPrime_self : rhoPrime d d = 1 / (2 * (d : ℝ) - 2) := by
  rw [rhoPrime, piPrimeValuation_self, primeNorm_self, div_div, mul_sub, mul_one]

/-- `γ_p = 0` when `p ≠ d` and `(p / d) ≠ -1`, in particular when `p` splits. -/
theorem gammaPrime_of_ne_of_legendreSym_ne_neg_one (h₁ : p ≠ d) (h₂ : legendreSym d p ≠ -1) :
    gammaPrime d p = 0 := by
  rw [gammaPrime, rhoPrime_of_ne_of_legendreSym_ne_neg_one h₁ h₂, sub_self]

/-- `γ_p = p / (p² - 1)` when `p` is inert. -/
theorem gammaPrime_of_legendreSym_eq_neg_one (h : legendreSym d p = -1) :
    gammaPrime d p = p / ((p : ℝ) ^ 2 - 1) := by
  have hp := two_le_of_legendreSym_eq_neg_one h
  have h1 : (p : ℝ) - 1 ≠ 0 := by linarith
  have h2 : (p : ℝ) ^ 2 - 1 ≠ 0 := by nlinarith
  rw [gammaPrime, rhoPrime_of_legendreSym_eq_neg_one h]
  field_simp
  ring

theorem gammaPrime_self : gammaPrime d d = 1 / (2 * (d : ℝ) - 2) := by
  have hd : (2 : ℝ) ≤ d := by exact_mod_cast (Fact.out : d.Prime).two_le
  have h1 : (d : ℝ) - 1 ≠ 0 := by linarith
  rw [gammaPrime, rhoPrime_self]
  field_simp
  ring

/-- `0 ≤ ρ_p` for `p ≠ 0`. -/
theorem rhoPrime_nonneg (hp : p ≠ 0) : 0 ≤ rhoPrime d p := by
  have : 1 ≤ primeNorm d p := by
    unfold primeNorm
    split_ifs
    · exact Nat.one_le_pow _ _ (Nat.pos_of_ne_zero hp)
    · exact Nat.one_le_iff_ne_zero.mpr hp
  exact div_nonneg piPrimeValuation_pos.le (by rw [sub_nonneg]; exact_mod_cast this)

theorem rhoPrime_le_one_div : rhoPrime d p ≤ 1 / ((p : ℝ) - 1) := by
  by_cases h₁ : p = d
  · subst h₁
    have hp : (2 : ℝ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).two_le
    rw [rhoPrime_self]
    exact one_div_le_one_div_of_le (by linarith) (by linarith)
  by_cases h₂ : legendreSym d p = -1
  · have hp := two_le_of_legendreSym_eq_neg_one h₂
    rw [rhoPrime_of_legendreSym_eq_neg_one h₂]
    exact one_div_le_one_div_of_le (by linarith) (by nlinarith)
  · rw [rhoPrime_of_ne_of_legendreSym_ne_neg_one h₁ h₂]

theorem gammaPrime_nonneg : 0 ≤ gammaPrime d p :=
  sub_nonneg.mpr rhoPrime_le_one_div

/-- `γ_p ≤ 1 / (p - 1)` for `p ≠ 0`. -/
theorem gammaPrime_le_one_div (hp : p ≠ 0) : gammaPrime d p ≤ 1 / ((p : ℝ) - 1) :=
  sub_le_self _ (rhoPrime_nonneg hp)

theorem gammaPrime_le_one : gammaPrime d p ≤ 1 := by
  rcases Nat.lt_or_ge p 2 with hp | hp
  · -- `p = 0` or `p = 1`: then `p ≠ d` and `(p / d) = p`, so `γ_p = 0`
    have h₁ : p ≠ d := by have := (Fact.out : d.Prime).two_le; omega
    have h₂ : legendreSym d p ≠ -1 := by
      interval_cases p
      · rw [Nat.cast_zero, legendreSym.at_zero]; decide
      · rw [Nat.cast_one, legendreSym.at_one]; decide
    rw [gammaPrime_of_ne_of_legendreSym_ne_neg_one h₁ h₂]
    exact zero_le_one
  · have hp' : (2 : ℝ) ≤ p := by exact_mod_cast hp
    refine (gammaPrime_le_one_div (by omega)).trans ?_
    rw [div_le_one (by linarith)]
    linarith

/-- `q_p` is a positive power of `p`. -/
theorem exists_primeNorm_eq_pow : ∃ k, 0 < k ∧ primeNorm d p = p ^ k := by
  by_cases h : legendreSym d p = -1
  · exact ⟨2, two_pos, primeNorm_of_legendreSym_eq_neg_one h⟩
  · exact ⟨1, one_pos, by rw [primeNorm_of_legendreSym_ne_neg_one h, pow_one]⟩

theorem one_lt_primeNorm (hp : 1 < p) : 1 < primeNorm d p := by
  obtain ⟨k, hk, hq⟩ := exists_primeNorm_eq_pow (d := d) (p := p)
  rw [hq]
  exact Nat.one_lt_pow hk.ne' hp

/-- `p` is prime to `q_p - 1`. -/
theorem coprime_primeNorm_sub_one (hp : p ≠ 0) : p.Coprime (primeNorm d p - 1) := by
  obtain ⟨k, hk, hq⟩ := exists_primeNorm_eq_pow (d := d) (p := p)
  have h1 : 1 ≤ p ^ k := Nat.one_le_pow _ _ (Nat.pos_of_ne_zero hp)
  rw [hq]
  have : (p ^ k - 1).Coprime (p ^ k) :=
    (Nat.coprime_self_sub_left h1).mpr (Nat.coprime_one_left _)
  exact (this.coprime_dvd_right (dvd_pow_self p hk.ne')).symm

/-- `v(π_p) = (q_p - 1) · ρ_p`. -/
theorem piPrimeValuation_eq_mul_rhoPrime (hp : 1 < p) :
    piPrimeValuation d p = ((primeNorm d p : ℝ) - 1) * rhoPrime d p := by
  have : (1 : ℝ) < primeNorm d p := by exact_mod_cast one_lt_primeNorm hp
  rw [rhoPrime, mul_div_cancel₀ _ (by linarith)]

/-- If the prime `p` does not split in `ℚ(√-d)`, that is `(p / d) ≠ 1`, then
`π_p · conj π_p = q_p`. -/
theorem piPrime_mul_conj (hp : p.Prime) (h : legendreSym d p ≠ 1) :
    piPrime d p * (starRingEnd ℂ) (piPrime d p) = primeNorm d p := by
  by_cases h₁ : p = d
  · subst h₁
    rw [primeNorm_self, piPrime_self, map_mul, conj_I, conj_ofReal]
    have h2 : (√(p : ℝ) : ℂ) ^ 2 = p := by
      rw [← ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg p), ofReal_natCast]
    linear_combination h2 - (√(p : ℝ) : ℂ) ^ 2 * I_sq
  · -- `p ≠ d` is prime, so `(p / d) = ±1`, and it is not `1`
    have h₂ : legendreSym d p = -1 := by
      refine (legendreSym.eq_one_or_neg_one d ?_).resolve_left h
      rw [Int.cast_natCast, ne_eq, ZMod.natCast_eq_zero_iff,
        Nat.prime_dvd_prime_iff_eq (Fact.out : d.Prime) hp]
      exact Ne.symm h₁
    rw [piPrime_of_ne h₁, conj_natCast, primeNorm_of_legendreSym_eq_neg_one h₂]
    push_cast
    ring

theorem partnerExponents_of_ne_of_legendreSym_ne_neg_one (h₁ : p ≠ d)
    (h₂ : legendreSym d p ≠ -1) : partnerExponents d p = ∅ := by
  ext e
  simp [mem_partnerExponents_iff, h₁, h₂]

theorem positivePartnerExponents_of_ne_of_legendreSym_ne_neg_one (h₁ : p ≠ d)
    (h₂ : legendreSym d p ≠ -1) : positivePartnerExponents d p = ∅ := by
  ext e
  simp [mem_positivePartnerExponents_iff, partnerExponents_of_ne_of_legendreSym_ne_neg_one h₁ h₂]

theorem partnerExponents_of_legendreSym_eq_neg_one (h : legendreSym d p = -1) :
    partnerExponents d p = {e | Odd e} := by
  ext e
  simp [mem_partnerExponents_iff, ne_of_legendreSym_eq_neg_one h, h]

/-- When `p` is inert, `I_p` is the set of odd exponents `2k + 1`. -/
theorem positivePartnerExponents_of_legendreSym_eq_neg_one (h : legendreSym d p = -1) :
    positivePartnerExponents d p = Set.range (fun k : ℕ ↦ 2 * k + 1) := by
  ext e
  rw [mem_positivePartnerExponents_iff, partnerExponents_of_legendreSym_eq_neg_one h,
    Set.mem_ofPred_eq, Set.mem_range]
  exact ⟨fun ⟨⟨k, hk⟩, _⟩ ↦ ⟨k, hk.symm⟩, by rintro ⟨k, rfl⟩; exact ⟨⟨k, rfl⟩, Nat.succ_pos _⟩⟩

@[simp] theorem partnerExponents_self : partnerExponents d d = Set.univ := by
  ext e
  simp [mem_partnerExponents_iff]

/-- For `p = d`, `I_p` is the set of exponents `k + 1`. -/
theorem positivePartnerExponents_self :
    positivePartnerExponents d d = Set.range (fun k : ℕ ↦ k + 1) := by
  ext e
  rw [mem_positivePartnerExponents_iff, partnerExponents_self, Set.mem_range]
  exact ⟨fun ⟨_, he⟩ ↦ ⟨e - 1, Nat.sub_add_cancel he⟩,
    by rintro ⟨k, rfl⟩; exact ⟨trivial, Nat.succ_pos _⟩⟩

/-- `∑_{e ∈ I_p} c · p ^ (-e) = c · γ_p / v(π_p)` for every real `c`. -/
theorem hasSum_div_pow_positivePartnerExponents (c : ℝ) :
    HasSum (fun e : positivePartnerExponents d p ↦ c / (p : ℝ) ^ (e : ℕ))
      (c * gammaPrime d p / piPrimeValuation d p) := by
  by_cases h₁ : p = d
  · -- `p = d`: `∑_{e ≥ 1} c p⁻ᵉ = c / (p - 1)`
    subst h₁
    have hp : (2 : ℝ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).two_le
    rw [positivePartnerExponents_self,
      (add_left_injective 1).hasSum_range_iff (f := fun e ↦ c / (p : ℝ) ^ e)]
    have hg := (hasSum_geometric_of_lt_one (r := (p : ℝ)⁻¹) (by positivity)
      (inv_lt_one_of_one_lt₀ (by linarith))).mul_left (c / p)
    convert hg using 1
    · ext k
      simp only [Function.comp_apply, pow_succ, inv_pow]
      field_simp
    · have h1 : (p : ℝ) - 1 ≠ 0 := by linarith
      rw [gammaPrime_self, piPrimeValuation_self]
      field_simp
  by_cases h₂ : legendreSym d p = -1
  · -- `p` inert: `∑_{e odd} c p⁻ᵉ = c p / (p² - 1)`
    have hp := two_le_of_legendreSym_eq_neg_one h₂
    have hinj : Function.Injective (fun k : ℕ ↦ 2 * k + 1) := fun a b hab ↦ by
      simp only at hab; omega
    rw [positivePartnerExponents_of_legendreSym_eq_neg_one h₂,
      hinj.hasSum_range_iff (f := fun e ↦ c / (p : ℝ) ^ e)]
    have hg := (hasSum_geometric_of_lt_one (r := ((p : ℝ) ^ 2)⁻¹) (by positivity)
      (inv_lt_one_of_one_lt₀ (by nlinarith))).mul_left (c / p)
    convert hg using 1
    · ext k
      simp only [Function.comp_apply, pow_succ, pow_mul, inv_pow]
      field_simp
    · have h2 : (p : ℝ) ^ 2 - 1 ≠ 0 := by nlinarith
      rw [gammaPrime_of_legendreSym_eq_neg_one h₂, piPrimeValuation_of_ne h₁]
      field_simp
  · -- otherwise the sum is empty and `γ_p = 0`
    rw [gammaPrime_of_ne_of_legendreSym_ne_neg_one h₁ h₂, mul_zero, zero_div,
      positivePartnerExponents_of_ne_of_legendreSym_ne_neg_one h₁ h₂]
    exact hasSum_empty

/-- `γ_p = v(π_p) · ∑_{e ∈ I_p} p ^ (-e)`. -/
theorem hasSum_gammaPrime :
    HasSum (fun e : positivePartnerExponents d p ↦ piPrimeValuation d p / (p : ℝ) ^ (e : ℕ))
      (gammaPrime d p) := by
  convert hasSum_div_pow_positivePartnerExponents (d := d) (p := p) (piPrimeValuation d p) using 1
  rw [mul_div_cancel_left₀ _ piPrimeValuation_pos.ne']

end TauCeti.ComplexMultiplication
