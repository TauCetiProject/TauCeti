/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ArithmeticDirichletSeries.EulerProduct.BoundedCoefficients
public import TauCeti.NumberTheory.ArithmeticDirichletSeries.Prime.IdealZetaSum
public import TauCeti.NumberTheory.NumberField.ResidueDegree
import TauCeti.Analysis.SpecialFunctions.Complex.Exp.TendstoOfTendstoExp
import TauCeti.Analysis.SpecialFunctions.Log.NegLogOneSub
import TauCeti.Analysis.SpecialFunctions.Log.OneDivSub
import TauCeti.NumberTheory.ArithmeticDirichletSeries.Convergence
import TauCeti.NumberTheory.ArithmeticDirichletSeries.DirichletDensity.Negligible
import TauCeti.NumberTheory.ArithmeticDirichletSeries.ResidueDegree

/-!
# Densities of functions on the primes of degree one

Let `K` be a number field. For a complex function `a` on the height-one primes of `𝓞 K`, write
`∑_{N𝔭 prime} a(𝔭) N(𝔭) ^ (-s)` for its Dirichlet series over the primes of degree one, the primes
whose absolute norm is a prime number (`TauCeti.degreeOnePrimeSum`; the other primes form
`TauCeti.higherDegreePrimes K`). The function `a` has **prime density** `l ∈ ℂ`
(`TauCeti.HasPrimeDensity a l`) if this series converges for real `s > 1` near `1` and

`∑_{N𝔭 prime} a(𝔭) N(𝔭) ^ (-s) = l · log (1 / (s - 1)) + O(1)`  as `s → 1⁺`.

This is the density at primes of degree one up to a bounded term. For the indicator function of a
set `S` of primes it implies that `S` has Dirichlet density `l` in Mathlib's sense
(`TauCeti.HasPrimeDensity.hasDirichletDensity`); Mathlib's `NumberField.Set.HasDirichletDensity`
asks only for the ratio with the all-prime sum to converge, so it allows an error `o(log (1/(s-1)))`
where the prime density allows `O(1)`, and it says nothing about complex-valued functions.

The prime density is read off from the Euler product `TauCeti.primeEulerProduct a s`: if `‖a‖ ≤ 1`
and `(s - 1) ^ (-l) P(a, s)` tends to a nonzero limit as `s → 1⁺`, then `a` has prime density `-l`
(`TauCeti.hasPrimeDensity_of_tendsto`). Indeed `log P(a, s)` and the sum over the primes of degree
one differ by the terms of order at least two of the logarithms and by the terms at the primes of
higher degree, and these are at most `5 [K : ℚ]` uniformly in `s`
(`TauCeti.norm_tsum_neg_log_sub_degreeOnePrimeSum_le`); a factor `(s - 1) ^ l` contributes
`-l log (1 / (s - 1))`; and a continuous logarithm of a function with a nonzero limit stays bounded.

## Main definitions

* `TauCeti.degreeOnePrimeSum a s`: `∑_{N𝔭 prime} a(𝔭) N(𝔭) ^ (-s)`.
* `TauCeti.HasPrimeDensity a l`: `a` has prime density `l` at the primes of degree one.

## Main results

* `TauCeti.degreeOnePrimeSum_add`, `TauCeti.degreeOnePrimeSum_const_mul`: the series over the
  primes of degree one is linear in the coefficients.
* `TauCeti.hasPrimeDensity_of_tendsto`: the density from the order of the Euler product at `1`.
* `TauCeti.HasPrimeDensity.add`, `TauCeti.HasPrimeDensity.const_mul`,
  `TauCeti.HasPrimeDensity.sum`: densities are linear.
* `TauCeti.HasPrimeDensity.re_le_re`: densities are monotone in real parts, and
  `TauCeti.HasPrimeDensity.unique`: a function has at most one density.
* `TauCeti.HasPrimeDensity.congr_cofinite`: changing a function at finitely many primes of degree
  one does not change its density.
* `TauCeti.hasPrimeDensity_const`: the constant `c` has density `c`.
* `TauCeti.infinite_setOf_prime_absNorm`: infinitely many primes have prime norm.
* `TauCeti.hasPrimeDensity_mul_ncard_setOf_under_eq_and_absNorm_eq`: for a finite extension
  `L/K`, the number of primes of `L` of relative degree one above `𝔭`, times `c`, has density
  `c`.
* `TauCeti.HasPrimeDensity.hasDirichletDensity`: comparison with Mathlib's Dirichlet density.

## Provenance

Adapted from grh-lean (https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic
PBC), file `src/Lib/ClassField/HeckeL/EulerProduct.lean`: `New.HasPrimeDensity`,
`New.norm_log_one_add_neg_mul_cpow_sub_ite_le_of_norm_le_one`, `New.hasPrimeDensity_of_tendsto`,
`New.HasPrimeDensity.sum`, `New.HasPrimeDensity.re_le_re`, `New.hasPrimeDensity_const`,
`New.frequently_prime_q` and `New.hasPrimeDensity_card_degree_one`. The density of the constants
and the bounded contribution of the primes of higher degree are taken from the library
(`TauCeti.primeIdealZetaSum_univ_sub_log_one_div_sub_one_isBigO`,
`TauCeti.primeIdealZetaSum_higherDegreePrimes_le`) instead of being reproved from the Dedekind zeta
function.

## References

* J. Tate, *Fourier analysis in number fields and Hecke's zeta-functions*, in J. W. S. Cassels and
  A. Fröhlich (eds.), *Algebraic Number Theory*, Chapter XV.
* J. S. Milne, *Class Field Theory*, Chapter VI.
* J.-P. Serre, *A Course in Arithmetic*, Chapter VI, §4.
-/

public section

open NumberField IsDedekindDomain Complex Filter Topology Asymptotics
open scoped nonZeroDivisors

namespace TauCeti

variable {K : Type*} [Field K] [NumberField K]

/-! ### The Dirichlet series over the primes of degree one -/

/-- **The Dirichlet series of `a` over the primes of degree one**,
`∑_{N𝔭 prime} a(𝔭) N(𝔭) ^ (-s)`: the primes of degree one are those outside
`TauCeti.higherDegreePrimes K`, that is, of prime absolute norm
(`TauCeti.mem_higherDegreePrimes_iff_not_prime_absNorm`). -/
noncomputable def degreeOnePrimeSum (a : HeightOneSpectrum (𝓞 K) → ℂ) (s : ℂ) : ℂ :=
  ∑' 𝔭 : HeightOneSpectrum (𝓞 K),
    (higherDegreePrimes K)ᶜ.indicator a 𝔭 / (Ideal.absNorm 𝔭.asIdeal : ℂ) ^ s

/-- **Prime density at the primes of degree one, up to a bounded term.** The function `a` has
prime density `l` if for real `s → 1⁺` the series `∑_{N𝔭 prime} a(𝔭) N(𝔭) ^ (-s)` converges and
equals `l · log (1 / (s - 1)) + O(1)`. -/
def HasPrimeDensity (a : HeightOneSpectrum (𝓞 K) → ℂ) (l : ℂ) : Prop :=
  (∀ᶠ s : ℝ in 𝓝[>] 1, Summable fun 𝔭 : HeightOneSpectrum (𝓞 K) ↦
      (higherDegreePrimes K)ᶜ.indicator a 𝔭 / (Ideal.absNorm 𝔭.asIdeal : ℂ) ^ (s : ℂ)) ∧
    (fun s : ℝ ↦ degreeOnePrimeSum a s - l * Real.log (1 / (s - 1))) =O[𝓝[>] 1]
      fun _ ↦ (1 : ℝ)

variable {a b : HeightOneSpectrum (𝓞 K) → ℂ} {l l' : ℂ}

/-- The defining formula of `TauCeti.degreeOnePrimeSum`. -/
theorem degreeOnePrimeSum_def (a : HeightOneSpectrum (𝓞 K) → ℂ) (s : ℂ) :
    degreeOnePrimeSum a s = ∑' 𝔭 : HeightOneSpectrum (𝓞 K),
      (higherDegreePrimes K)ᶜ.indicator a 𝔭 / (Ideal.absNorm 𝔭.asIdeal : ℂ) ^ s := by
  rw [degreeOnePrimeSum]

/-- The definition of `TauCeti.HasPrimeDensity`, unfolded. -/
theorem hasPrimeDensity_iff :
    HasPrimeDensity a l ↔
      (∀ᶠ s : ℝ in 𝓝[>] 1, Summable fun 𝔭 : HeightOneSpectrum (𝓞 K) ↦
        (higherDegreePrimes K)ᶜ.indicator a 𝔭 / (Ideal.absNorm 𝔭.asIdeal : ℂ) ^ (s : ℂ)) ∧
      (fun s : ℝ ↦ degreeOnePrimeSum a s - l * Real.log (1 / (s - 1))) =O[𝓝[>] 1]
        fun _ ↦ (1 : ℝ) := by
  rw [HasPrimeDensity]

/-- The series of the zero function over the primes of degree one vanishes. -/
@[simp]
theorem degreeOnePrimeSum_zero (s : ℂ) :
    degreeOnePrimeSum (0 : HeightOneSpectrum (𝓞 K) → ℂ) s = 0 := by
  simp [degreeOnePrimeSum_def]

/-- The series over the primes of degree one is additive in the coefficients, when both series
converge. -/
theorem degreeOnePrimeSum_add {s : ℂ}
    (ha : Summable fun 𝔭 : HeightOneSpectrum (𝓞 K) ↦
      (higherDegreePrimes K)ᶜ.indicator a 𝔭 / (Ideal.absNorm 𝔭.asIdeal : ℂ) ^ s)
    (hb : Summable fun 𝔭 : HeightOneSpectrum (𝓞 K) ↦
      (higherDegreePrimes K)ᶜ.indicator b 𝔭 / (Ideal.absNorm 𝔭.asIdeal : ℂ) ^ s) :
    degreeOnePrimeSum (a + b) s = degreeOnePrimeSum a s + degreeOnePrimeSum b s := by
  simp only [degreeOnePrimeSum_def, Set.indicator_add', Pi.add_apply, add_div]
  exact ha.tsum_add hb

/-- Multiplying the coefficients by a constant multiplies the series over the primes of degree
one. -/
theorem degreeOnePrimeSum_const_mul (c : ℂ) (a : HeightOneSpectrum (𝓞 K) → ℂ) (s : ℂ) :
    degreeOnePrimeSum (fun 𝔭 ↦ c * a 𝔭) s = c * degreeOnePrimeSum a s := by
  simp only [degreeOnePrimeSum_def, Set.indicator_mul_right _ (fun _ ↦ c) a, mul_div_assoc,
    tsum_mul_left]

/-- For a bounded function and `Re s > 1` the Dirichlet series over any set of primes converges
absolutely. -/
theorem summable_indicator_div_absNorm_cpow {C : ℝ} (hC : ∀ 𝔭, ‖a 𝔭‖ ≤ C)
    (S : Set (HeightOneSpectrum (𝓞 K))) {s : ℂ} (hs : 1 < s.re) :
    Summable fun 𝔭 : HeightOneSpectrum (𝓞 K) ↦
      S.indicator a 𝔭 / (Ideal.absNorm 𝔭.asIdeal : ℂ) ^ s := by
  refine Summable.of_norm_bounded ((summable_absNorm_rpow_primes_of_one_lt hs).mul_left C)
    fun 𝔭 ↦ ?_
  rw [𝔭.norm_div_absNorm_cpow]
  exact mul_le_mul_of_nonneg_right ((norm_indicator_le_norm_self a 𝔭).trans (hC 𝔭))
    (by positivity)

/-- For a bounded function the summability condition of `TauCeti.HasPrimeDensity` holds. -/
theorem eventually_summable_indicator_div_absNorm_cpow {C : ℝ} (hC : ∀ 𝔭, ‖a 𝔭‖ ≤ C) :
    ∀ᶠ s : ℝ in 𝓝[>] 1, Summable fun 𝔭 : HeightOneSpectrum (𝓞 K) ↦
      (higherDegreePrimes K)ᶜ.indicator a 𝔭 / (Ideal.absNorm 𝔭.asIdeal : ℂ) ^ (s : ℂ) :=
  eventually_mem_nhdsWithin.mono fun _ hs ↦
    summable_indicator_div_absNorm_cpow hC _ (by simpa using hs)

/-! ### Linearity and monotonicity -/

/-- Densities add. -/
theorem HasPrimeDensity.add (ha : HasPrimeDensity a l) (hb : HasPrimeDensity b l') :
    HasPrimeDensity (a + b) (l + l') := by
  have hind (𝔭 : HeightOneSpectrum (𝓞 K)) (z : ℂ) :
      (higherDegreePrimes K)ᶜ.indicator (a + b) 𝔭 / z =
        (higherDegreePrimes K)ᶜ.indicator a 𝔭 / z + (higherDegreePrimes K)ᶜ.indicator b 𝔭 / z := by
    rw [Set.indicator_add', Pi.add_apply, add_div]
  refine ⟨(ha.1.and hb.1).mono fun s hs ↦ ?_, (ha.2.add hb.2).congr' ?_ .rfl⟩
  · simpa only [hind] using hs.1.add hs.2
  · filter_upwards [ha.1, hb.1] with s has hbs
    rw [degreeOnePrimeSum_add has hbs]
    ring

/-- Multiplying a function by a constant multiplies its density. -/
theorem HasPrimeDensity.const_mul (ha : HasPrimeDensity a l) (c : ℂ) :
    HasPrimeDensity (fun 𝔭 ↦ c * a 𝔭) (c * l) := by
  have hind (𝔭 : HeightOneSpectrum (𝓞 K)) :
      (higherDegreePrimes K)ᶜ.indicator (fun 𝔭 ↦ c * a 𝔭) 𝔭 =
        c * (higherDegreePrimes K)ᶜ.indicator a 𝔭 :=
    Set.indicator_mul_right _ (fun _ ↦ c) a
  refine ⟨ha.1.mono fun s hs ↦ ?_, (ha.2.const_mul_left c).congr' ?_ (.rfl)⟩
  · simpa only [hind, mul_div_assoc] using hs.mul_left c
  · refine .of_forall fun s ↦ ?_
    simp only [degreeOnePrimeSum_const_mul]
    ring

/-- The density of a finite sum of functions is the sum of their densities. -/
theorem HasPrimeDensity.sum {ι : Type*} (t : Finset ι) {a : ι → HeightOneSpectrum (𝓞 K) → ℂ}
    {l : ι → ℂ} (h : ∀ i ∈ t, HasPrimeDensity (a i) (l i)) :
    HasPrimeDensity (∑ i ∈ t, a i) (∑ i ∈ t, l i) := by
  classical
  induction t using Finset.induction_on with
  | empty =>
    refine ⟨.of_forall fun s ↦ by simp, ?_⟩
    exact (isBigO_zero (fun _ : ℝ ↦ (1 : ℝ)) (𝓝[>] (1 : ℝ))).congr'
      (.of_forall fun s ↦ by simp [degreeOnePrimeSum_def]) .rfl
  | insert i t hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    exact (h i (t.mem_insert_self i)).add (ih fun j hj ↦ h j (Finset.mem_insert_of_mem hj))

/-- The difference of two functions has the difference of their densities. -/
theorem HasPrimeDensity.sub (ha : HasPrimeDensity a l) (hb : HasPrimeDensity b l') :
    HasPrimeDensity (a - b) (l - l') := by
  simpa [sub_eq_add_neg, neg_mul, Pi.neg_def] using ha.add (hb.const_mul (-1))

/-- A property holding at all but finitely many points holds outside the finite set where it
fails. -/
private theorem eventually_cofinite_of_notMem_toFinset {α : Type*} {p : α → Prop}
    (h : ∀ᶠ x in cofinite, p x) {𝔭 : α} (h𝔭 : 𝔭 ∉ (eventually_cofinite.mp h).toFinset) :
    p 𝔭 := by
  by_contra hp
  exact h𝔭 ((eventually_cofinite.mp h).mem_toFinset.mpr hp)

/-- A lower bound for the real part of the series over the primes of degree one, when the real
part of the coefficients is nonnegative at the primes of degree one outside a finite set `E`. -/
private theorem neg_sum_le_re_degreeOnePrimeSum {E : Finset (HeightOneSpectrum (𝓞 K))}
    (hE : ∀ 𝔭 ∉ E, 𝔭 ∉ higherDegreePrimes K → 0 ≤ (a 𝔭).re) {s : ℝ} (hs : 1 ≤ s)
    (hsum : Summable fun 𝔭 : HeightOneSpectrum (𝓞 K) ↦
      (higherDegreePrimes K)ᶜ.indicator a 𝔭 / (Ideal.absNorm 𝔭.asIdeal : ℂ) ^ (s : ℂ)) :
    -∑ 𝔭 ∈ E, ‖a 𝔭‖ ≤ (degreeOnePrimeSum a s).re := by
  classical
  set f := fun 𝔭 : HeightOneSpectrum (𝓞 K) ↦
    (higherDegreePrimes K)ᶜ.indicator a 𝔭 / (Ideal.absNorm 𝔭.asIdeal : ℂ) ^ (s : ℂ)
  have hN (𝔭 : HeightOneSpectrum (𝓞 K)) :
      (Ideal.absNorm 𝔭.asIdeal : ℂ) ^ (s : ℂ) = ((Ideal.absNorm 𝔭.asIdeal : ℝ) ^ s : ℝ) := by
    rw [ofReal_cpow (Nat.cast_nonneg _), ofReal_natCast]
  have hNpos (𝔭 : HeightOneSpectrum (𝓞 K)) : 0 < (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ s :=
    Real.rpow_pos_of_pos (two_pos.trans_le (two_le_absNorm_asIdeal_real 𝔭)) s
  -- the real part of each term is at least `-‖a 𝔭‖` on `E` and `0` elsewhere
  have hterm (𝔭 : HeightOneSpectrum (𝓞 K)) :
      (if 𝔭 ∈ E then -‖a 𝔭‖ else 0) ≤ (f 𝔭).re := by
    have hre : (f 𝔭).re = ((higherDegreePrimes K)ᶜ.indicator a 𝔭).re /
        (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ s := by
      simp only [f, hN, div_ofReal_re]
    rw [hre]
    by_cases h𝔭 : 𝔭 ∈ higherDegreePrimes K
    · simp [h𝔭, apply_ite (fun x ↦ x ≤ (0 : ℝ))]
    rw [Set.indicator_of_mem (Set.mem_compl h𝔭)]
    split_ifs with hE𝔭
    · rw [le_div_iff₀ (hNpos 𝔭)]
      have h1 : (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ s ≥ 1 :=
        Real.one_le_rpow (one_le_two.trans (two_le_absNorm_asIdeal_real 𝔭)) (by linarith)
      nlinarith [neg_abs_le (a 𝔭).re, abs_re_le_norm (a 𝔭), norm_nonneg (a 𝔭)]
    · exact div_nonneg (hE 𝔭 hE𝔭 h𝔭) (hNpos 𝔭).le
  have hfin : HasSum (fun 𝔭 ↦ if 𝔭 ∈ E then -‖a 𝔭‖ else 0) (-∑ 𝔭 ∈ E, ‖a 𝔭‖) := by
    simpa [Finset.sum_neg_distrib] using
      hasSum_sum_of_ne_finset_zero (s := E) (f := fun 𝔭 ↦ if 𝔭 ∈ E then -‖a 𝔭‖ else 0)
        fun 𝔭 h𝔭 ↦ by simp [h𝔭]
  rw [degreeOnePrimeSum_def]
  exact hasSum_le hterm hfin (hasSum_re hsum.hasSum)

/-- **Densities are monotone in real parts.** If `a` has density `l`, `b` has density `l'`, and
`Re a(𝔭) ≤ Re b(𝔭)` at all but finitely many primes of degree one, then `Re l ≤ Re l'`. -/
theorem HasPrimeDensity.re_le_re (ha : HasPrimeDensity a l) (hb : HasPrimeDensity b l')
    (h : ∀ᶠ 𝔭 : HeightOneSpectrum (𝓞 K) in cofinite,
      (Ideal.absNorm 𝔭.asIdeal).Prime → (a 𝔭).re ≤ (b 𝔭).re) :
    l.re ≤ l'.re := by
  classical
  by_contra! hlt
  -- `b - a` has density `l' - l`, of negative real part
  obtain ⟨hsum, hO⟩ := hb.sub ha
  obtain ⟨C, hC⟩ := hO.bound
  set E := (eventually_cofinite.mp h).toFinset
  have hE (𝔭 : HeightOneSpectrum (𝓞 K)) (h𝔭E : 𝔭 ∉ E) (h𝔭 : 𝔭 ∉ higherDegreePrimes K) :
      0 ≤ ((b - a) 𝔭).re := by
    have := eventually_cofinite_of_notMem_toFinset h h𝔭E
    have hp := notMem_higherDegreePrimes_iff_prime_absNorm.mp h𝔭
    simpa using this hp
  -- `Re (l' - l) · log (1 / (s - 1)) → -∞`
  have hlim := (Real.tendsto_log_one_div_sub_atTop 1).const_mul_atTop_of_neg
    (sub_neg.mpr hlt : l'.re - l.re < 0)
  obtain ⟨s, hsC, hssum, hs1, hslt⟩ := (hC.and (hsum.and (eventually_mem_nhdsWithin.and
    (hlim.eventually_lt_atBot (-∑ 𝔭 ∈ E, ‖(b - a) 𝔭‖ - C))))).exists
  have hlow := neg_sum_le_re_degreeOnePrimeSum (a := b - a) hE (le_of_lt hs1) hssum
  have hre : (degreeOnePrimeSum (b - a) s - (l' - l) * Real.log (1 / (s - 1))).re ≤ C :=
    (re_le_norm _).trans (by simpa using hsC)
  simp only [sub_re, mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero] at hre
  linarith

/-- **Densities are unique.** Compare the real parts of the densities of `a` and of `I a` with
`TauCeti.HasPrimeDensity.re_le_re`. -/
theorem HasPrimeDensity.unique (ha : HasPrimeDensity a l) (ha' : HasPrimeDensity a l') :
    l = l' := by
  have hre {f : HeightOneSpectrum (𝓞 K) → ℂ} {l₁ l₂ : ℂ} (h₁ : HasPrimeDensity f l₁)
      (h₂ : HasPrimeDensity f l₂) : l₁.re ≤ l₂.re :=
    h₁.re_le_re h₂ (.of_forall fun _ _ ↦ le_rfl)
  have him {l₁ l₂ : ℂ} (h₁ : HasPrimeDensity a l₁) (h₂ : HasPrimeDensity a l₂) :
      l₂.im ≤ l₁.im := by
    simpa using hre (h₁.const_mul I) (h₂.const_mul I)
  exact Complex.ext (le_antisymm (hre ha ha') (hre ha' ha)) (le_antisymm (him ha' ha) (him ha ha'))

/-- A function vanishing at all but finitely many primes of degree one has prime density `0`: its
series over the primes of degree one is a finite sum, bounded for real `s ≥ 0`. -/
theorem hasPrimeDensity_zero_of_eventually_eq_zero
    (h : ∀ᶠ 𝔭 : HeightOneSpectrum (𝓞 K) in cofinite, (Ideal.absNorm 𝔭.asIdeal).Prime → a 𝔭 = 0) :
    HasPrimeDensity a 0 := by
  classical
  set E := (eventually_cofinite.mp h).toFinset
  have hzero (s : ℂ) (𝔭 : HeightOneSpectrum (𝓞 K)) (h𝔭E : 𝔭 ∉ E) :
      (higherDegreePrimes K)ᶜ.indicator a 𝔭 / (Ideal.absNorm 𝔭.asIdeal : ℂ) ^ s = 0 := by
    by_cases h𝔭 : 𝔭 ∈ higherDegreePrimes K
    · rw [Set.indicator_of_notMem (Set.notMem_compl_iff.mpr h𝔭), zero_div]
    have := eventually_cofinite_of_notMem_toFinset h h𝔭E
    have hp := notMem_higherDegreePrimes_iff_prime_absNorm.mp h𝔭
    rw [Set.indicator_of_mem (Set.mem_compl h𝔭), this hp, zero_div]
  refine ⟨.of_forall fun s ↦ summable_of_ne_finset_zero (s := E) (hzero _), ?_⟩
  refine IsBigO.of_bound (∑ 𝔭 ∈ E, ‖a 𝔭‖) ?_
  filter_upwards [self_mem_nhdsWithin] with s (hs : 1 < s)
  rw [zero_mul, sub_zero, norm_one, mul_one, degreeOnePrimeSum_def, tsum_eq_sum (hzero _)]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun 𝔭 _ ↦ ?_)
  rw [𝔭.norm_div_absNorm_cpow, ofReal_re]
  exact (mul_le_of_le_one_right (norm_nonneg _) (Real.rpow_le_one_of_one_le_of_nonpos
    (one_le_two.trans (two_le_absNorm_asIdeal_real 𝔭)) (by linarith))).trans
    (norm_indicator_le_norm_self a 𝔭)

/-- **Changing a function at finitely many primes of degree one keeps its density.** -/
theorem HasPrimeDensity.congr_cofinite (ha : HasPrimeDensity a l)
    (h : ∀ᶠ 𝔭 : HeightOneSpectrum (𝓞 K) in cofinite,
      (Ideal.absNorm 𝔭.asIdeal).Prime → a 𝔭 = b 𝔭) :
    HasPrimeDensity b l := by
  simpa using ha.add (hasPrimeDensity_zero_of_eventually_eq_zero (a := b - a)
    (h.mono fun 𝔭 h𝔭 hp ↦ by rw [Pi.sub_apply, h𝔭 hp, sub_self]))

/-! ### Constants, primes of degree one, and comparison with Dirichlet density -/

/-- For a set `S` of primes, the series of the indicator of `S` over the primes of degree one is
the prime zeta sum of `S` minus that of its primes of higher degree. -/
private theorem degreeOnePrimeSum_indicator_one_eq (S : Set (HeightOneSpectrum (𝓞 K))) {s : ℝ}
    (hs : 1 < s) :
    degreeOnePrimeSum (S.indicator 1) s =
      (S.primeIdealZetaSum s : ℂ) - (S ∩ higherDegreePrimes K).primeIdealZetaSum s := by
  rw [degreeOnePrimeSum_def,
    ((NumberField.Set.hasSum_indicator_one_div_absNorm_cpow S hs).sub
      (NumberField.Set.hasSum_indicator_one_div_absNorm_cpow (S ∩ higherDegreePrimes K)
        hs)).tsum_eq.symm]
  refine tsum_congr fun 𝔭 ↦ ?_
  by_cases h𝔭 : 𝔭 ∈ higherDegreePrimes K <;> by_cases hS : 𝔭 ∈ S <;> simp [h𝔭, hS]

/-- The prime zeta sum of a set of primes of higher degree is bounded near `1`. -/
private theorem isBigO_primeIdealZetaSum_of_subset {T : Set (HeightOneSpectrum (𝓞 K))}
    (hT : T ⊆ higherDegreePrimes K) :
    (fun s : ℝ ↦ (T.primeIdealZetaSum s : ℂ)) =O[𝓝[>] 1] fun _ ↦ (1 : ℝ) := by
  refine IsBigO.of_bound (2 * Module.finrank ℚ K) ?_
  filter_upwards [self_mem_nhdsWithin] with s (hs : 1 < s)
  rw [norm_real, Real.norm_of_nonneg (NumberField.Set.primeIdealZetaSum_nonneg _ _), norm_one,
    mul_one]
  exact (NumberField.Set.primeIdealZetaSum_mono_set_of_one_lt hT hs).trans
    (primeIdealZetaSum_higherDegreePrimes_le hs.le)

/-- **Constants have prime density equal to their value.** This is the asymptotic
`∑_𝔭 N(𝔭) ^ (-s) = log (1 / (s - 1)) + O(1)` of the library
(`TauCeti.primeIdealZetaSum_univ_sub_log_one_div_sub_one_isBigO`), with the primes of higher
degree contributing a bounded amount. -/
theorem hasPrimeDensity_const (c : ℂ) :
    HasPrimeDensity (fun _ : HeightOneSpectrum (𝓞 K) ↦ c) c := by
  suffices h1 : HasPrimeDensity (1 : HeightOneSpectrum (𝓞 K) → ℂ) 1 by
    simpa using h1.const_mul c
  refine ⟨eventually_summable_indicator_div_absNorm_cpow (C := 1) (fun _ ↦ by simp), ?_⟩
  refine ((isBigO_ofReal_left.mpr (primeIdealZetaSum_univ_sub_log_one_div_sub_one_isBigO
    (K := K))).sub (isBigO_primeIdealZetaSum_of_subset
      (T := Set.univ ∩ higherDegreePrimes K) Set.inter_subset_right)).congr' ?_ .rfl
  filter_upwards [self_mem_nhdsWithin] with s (hs : 1 < s)
  rw [← Set.indicator_univ (1 : HeightOneSpectrum (𝓞 K) → ℂ),
    degreeOnePrimeSum_indicator_one_eq _ hs]
  push_cast
  ring

/-- **Comparison with Mathlib's Dirichlet density.** If the indicator function of a set `S` of
primes has prime density `δ`, then `S` has Dirichlet density `δ` in the sense of
`NumberField.Set.HasDirichletDensity`. The prime density asks for more: the error is `O(1)`, not
merely `o(log (1 / (s - 1)))`. -/
theorem HasPrimeDensity.hasDirichletDensity {S : Set (HeightOneSpectrum (𝓞 K))} {δ : ℝ}
    (h : HasPrimeDensity (S.indicator 1) δ) : S.HasDirichletDensity δ := by
  rw [NumberField.Set.hasDirichletDensity_iff_tendsto_div_log_one_div_sub_one]
  have hO : (fun s : ℝ ↦ S.primeIdealZetaSum s - δ * Real.log (1 / (s - 1))) =O[𝓝[>] 1]
      fun _ ↦ (1 : ℝ) := by
    refine isBigO_ofReal_left.mp ((h.2.add (isBigO_primeIdealZetaSum_of_subset
      (T := S ∩ higherDegreePrimes K) Set.inter_subset_right)).congr' ?_ .rfl)
    filter_upwards [self_mem_nhdsWithin] with s (hs : 1 < s)
    rw [degreeOnePrimeSum_indicator_one_eq S hs]
    push_cast
    ring
  have hL := Real.tendsto_log_one_div_sub_atTop 1
  have ho := hO.trans_isLittleO
    ((isLittleO_one_left_iff ℝ).mpr (tendsto_norm_atTop_atTop.comp hL))
  have hlim := ho.tendsto_div_nhds_zero.add_const δ
  rw [zero_add] at hlim
  refine hlim.congr' ?_
  filter_upwards [hL.eventually_gt_atTop 0] with s hs
  field_simp
  ring

/-- **Infinitely many primes have prime norm**: the primes of degree one have Dirichlet
density one (`TauCeti.hasDirichletDensity_compl_higherDegreePrimes`). -/
theorem infinite_setOf_prime_absNorm :
    {𝔭 : HeightOneSpectrum (𝓞 K) | (Ideal.absNorm 𝔭.asIdeal).Prime}.Infinite := by
  exact compl_higherDegreePrimes (K := K) ▸
    hasDirichletDensity_compl_higherDegreePrimes.infinite one_ne_zero

/-! ### The density from the Euler product -/

/-- The bound for one term of `TauCeti.norm_tsum_neg_log_sub_degreeOnePrimeSum_le`: at a prime of
degree one `-log (1 - z) - z` has modulus at most `N(𝔭) ^ (-2)`, and at a prime of higher degree
`-log (1 - z)` has modulus at most `3/2 N(𝔭) ^ (-1)`. -/
private theorem norm_neg_log_sub_indicator_le (ha : ∀ 𝔭, ‖a 𝔭‖ ≤ 1) {s : ℂ} (hs : 1 ≤ s.re)
    (𝔭 : HeightOneSpectrum (𝓞 K)) :
    ‖-log (1 - a 𝔭 / (Ideal.absNorm 𝔭.asIdeal : ℂ) ^ s) -
        (higherDegreePrimes K)ᶜ.indicator a 𝔭 / (Ideal.absNorm 𝔭.asIdeal : ℂ) ^ s‖ ≤
      (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-(2 : ℝ)) + 3 / 2 *
        (higherDegreePrimes K).indicator
          (fun 𝔭 ↦ (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-(1 : ℝ))) 𝔭 := by
  by_cases h𝔭 : 𝔭 ∈ higherDegreePrimes K
  · rw [Set.indicator_of_notMem (Set.notMem_compl_iff.mpr h𝔭), Set.indicator_of_mem h𝔭,
      zero_div, sub_zero]
    have := norm_neg_log_one_sub_div_absNorm_cpow_le (ha 𝔭) hs hs
    have h2 : (0 : ℝ) ≤ (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-(2 : ℝ)) := by positivity
    linarith
  · have hz : ‖a 𝔭 / (Ideal.absNorm 𝔭.asIdeal : ℂ) ^ s‖ ≤
        (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-(1 : ℝ)) :=
      (norm_div_absNorm_cpow_le_rpow_neg (ha 𝔭)).trans (Real.rpow_le_rpow_of_exponent_le
        (one_le_two.trans (two_le_absNorm_asIdeal_real 𝔭)) (neg_le_neg hs))
    rw [Set.indicator_of_mem (Set.mem_compl h𝔭), Set.indicator_of_notMem h𝔭, mul_zero, add_zero]
    refine (Complex.norm_neg_log_one_sub_sub_le (norm_div_absNorm_cpow_le_half (ha 𝔭) hs)).trans ?_
    calc ‖a 𝔭 / (Ideal.absNorm 𝔭.asIdeal : ℂ) ^ s‖ ^ 2
        ≤ ((Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-(1 : ℝ))) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hz 2
      _ = (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-(2 : ℝ)) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
        norm_num

/-- **The logarithm of the Euler product differs from the sum over the primes of degree one by at
most `5 [K : ℚ]`.** For `‖a‖ ≤ 1` and `Re s > 1`, the difference consists of the terms of order at
least two of the logarithms, at most `∑_𝔭 N(𝔭) ^ (-2) ≤ 2 [K : ℚ]` in total, and of the
logarithms at the primes of higher degree, at most `3/2 ∑_{𝔭 of higher degree} N(𝔭) ^ (-1) ≤
3 [K : ℚ]` (`TauCeti.primeIdealZetaSum_higherDegreePrimes_le`). -/
theorem norm_tsum_neg_log_sub_degreeOnePrimeSum_le (ha : ∀ 𝔭, ‖a 𝔭‖ ≤ 1) {s : ℂ}
    (hs : 1 < s.re) :
    ‖(∑' 𝔭 : HeightOneSpectrum (𝓞 K), -log (1 - a 𝔭 / (Ideal.absNorm 𝔭.asIdeal : ℂ) ^ s)) -
        degreeOnePrimeSum a s‖ ≤ 5 * Module.finrank ℚ K := by
  have hg2 := summable_absNorm_rpow_primes_of_one_lt (K := K) one_lt_two
  have hg1 : Summable ((higherDegreePrimes K).indicator
      fun 𝔭 ↦ (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-(1 : ℝ))) :=
    summable_subtype_iff_indicator.mp (summable_absNorm_rpow_higherDegreePrimes (by norm_num))
  have hbound := tsum_of_norm_bounded (hg2.add (hg1.mul_left (3 / 2))).hasSum
    (norm_neg_log_sub_indicator_le ha hs.le)
  rw [degreeOnePrimeSum_def, ← (summable_neg_log_one_sub_div_absNorm_cpow ha hs).tsum_sub
    (summable_indicator_div_absNorm_cpow ha _ hs)]
  refine hbound.trans ?_
  rw [hg2.tsum_add (hg1.mul_left _), tsum_mul_left, ← tsum_subtype,
    ← NumberField.Set.primeIdealZetaSum_def]
  have h1 := tsum_absNorm_rpow_neg_two_le (K := K)
  have h2 := primeIdealZetaSum_higherDegreePrimes_le (K := K) le_rfl
  linarith

/-- **The prime density from the Euler product.** Let `‖a‖ ≤ 1`. If `P(a, s) (s - 1) ^ (-l)` tends
to a nonzero limit as real `s → 1⁺`, for some real `l`, then `a` has prime density `-l`. For example
`P(1, s) = ζ_K(s)` has a simple pole, `l = -1`, and the constant `1` has density `1`. -/
theorem hasPrimeDensity_of_tendsto (ha : ∀ 𝔭, ‖a 𝔭‖ ≤ 1) {l : ℝ} {c : ℂ} (hc : c ≠ 0)
    (h : Tendsto (fun s : ℝ ↦ primeEulerProduct a s * ((s - 1) ^ (-l) : ℝ)) (𝓝[>] 1) (𝓝 c)) :
    HasPrimeDensity a (-(l : ℂ)) := by
  set F : ℝ → ℂ := fun s ↦ ∑' 𝔭 : HeightOneSpectrum (𝓞 K),
    -log (1 - a 𝔭 / (Ideal.absNorm 𝔭.asIdeal : ℂ) ^ (s : ℂ))
  set G : ℝ → ℂ := fun s ↦ F s - l * Real.log (s - 1)
  have hlog : ContinuousOn (fun t : ℝ ↦ (l : ℂ) * (Real.log (t - 1) : ℂ)) (Set.Ioi 1) :=
    continuousOn_const.mul (continuous_ofReal.comp_continuousOn
      (Real.continuousOn_log.comp (continuousOn_id.sub continuousOn_const)
        fun t (ht : 1 < t) ↦ (sub_pos.mpr ht).ne'))
  have hGcont : ContinuousOn G (Set.Ioi 1) :=
    (continuousOn_tsum_neg_log_one_sub_div_absNorm_cpow ha).sub hlog
  -- `exp G` is the normalized Euler product
  have hexp : ∀ᶠ s : ℝ in 𝓝[>] (1 : ℝ),
      primeEulerProduct a s * (((s - 1) ^ (-l) : ℝ) : ℂ) = exp (G s) := by
    filter_upwards [self_mem_nhdsWithin] with s (hs : 1 < s)
    rw [primeEulerProduct_eq_exp ha (by rwa [ofReal_re]), Real.rpow_def_of_pos (sub_pos.mpr hs),
      ofReal_exp, ← exp_add]
    simp only [G, F]
    push_cast
    ring_nf
  obtain ⟨C, hC⟩ := Complex.exists_tendsto_of_tendsto_exp hGcont hc (h.congr' hexp)
  refine ⟨eventually_summable_indicator_div_absNorm_cpow ha, ?_⟩
  have hE : (fun s : ℝ ↦ F s - degreeOnePrimeSum a s) =O[𝓝[>] 1] fun _ ↦ (1 : ℝ) := by
    refine IsBigO.of_bound (5 * Module.finrank ℚ K) ?_
    filter_upwards [self_mem_nhdsWithin] with s (hs : 1 < s)
    rw [norm_one, mul_one]
    exact norm_tsum_neg_log_sub_degreeOnePrimeSum_le ha (by rwa [ofReal_re])
  refine ((hC.isBigO_one ℝ).sub hE).congr' (.of_forall fun s ↦ ?_) .rfl
  simp only [G, one_div, Real.log_inv]
  push_cast
  ring

/-! ### Primes of relative degree one in an extension -/

section Extension

variable (L : Type*) [Field L] [NumberField L] [Algebra K L]

/-- The terms of the series over the primes of degree one of `L` above a prime `𝔭` of `K` add up
to the term at `𝔭` of the series of the count of the primes of relative degree one. -/
private theorem tsum_fiber_under_eq (c : ℂ) (𝔭 : HeightOneSpectrum (𝓞 K)) (s : ℂ) :
    ∑' 𝔓 : (fun 𝔓 : HeightOneSpectrum (𝓞 L) ↦ 𝔓.under (𝓞 K)) ⁻¹' {𝔭},
        (higherDegreePrimes L)ᶜ.indicator (fun _ ↦ c) 𝔓 /
          (Ideal.absNorm (𝔓 : HeightOneSpectrum (𝓞 L)).asIdeal : ℂ) ^ s =
      (higherDegreePrimes K)ᶜ.indicator (fun 𝔭 ↦ c *
        ({𝔓 : HeightOneSpectrum (𝓞 L) | 𝔓.under (𝓞 K) = 𝔭 ∧
          Ideal.absNorm 𝔓.asIdeal = Ideal.absNorm 𝔭.asIdeal}.ncard : ℂ)) 𝔭 /
        (Ideal.absNorm 𝔭.asIdeal : ℂ) ^ s := by
  classical
  set A := {𝔓 : HeightOneSpectrum (𝓞 L) | 𝔓.under (𝓞 K) = 𝔭 ∧
    Ideal.absNorm 𝔓.asIdeal = Ideal.absNorm 𝔭.asIdeal}
  set x : ℂ := c / (Ideal.absNorm 𝔭.asIdeal : ℂ) ^ s
  -- on the fibre, the terms are `x` on `A` (if `𝔭` has degree one) and `0` elsewhere
  have hterm (𝔓 : (fun 𝔓 : HeightOneSpectrum (𝓞 L) ↦ 𝔓.under (𝓞 K)) ⁻¹' {𝔭}) :
      (higherDegreePrimes L)ᶜ.indicator (fun _ ↦ c) (𝔓 : HeightOneSpectrum (𝓞 L)) /
          (Ideal.absNorm (𝔓 : HeightOneSpectrum (𝓞 L)).asIdeal : ℂ) ^ s =
        if 𝔭 ∉ higherDegreePrimes K then A.indicator (fun _ ↦ x) 𝔓 else 0 := by
    obtain ⟨𝔓, h𝔓 : 𝔓.under (𝓞 K) = 𝔭⟩ := 𝔓
    have hiff := notMem_higherDegreePrimes_iff_of_under_eq h𝔓
    by_cases hP : 𝔓 ∈ higherDegreePrimes L
    · rw [Set.indicator_of_notMem (Set.notMem_compl_iff.mpr hP), zero_div]
      split_ifs with hp
      · rfl
      · exact (Set.indicator_of_notMem (fun (hA : 𝔓 ∈ A) ↦ hiff.mpr ⟨hp, hA.2⟩ hP) _).symm
    · obtain ⟨hp, heq⟩ := hiff.mp hP
      simp [hP, hp, A, h𝔓, heq, x]
  rw [tsum_congr hterm]
  by_cases hp : 𝔭 ∈ higherDegreePrimes K
  · simp [hp]
  have hAsub : A ⊆ (fun 𝔓 : HeightOneSpectrum (𝓞 L) ↦ 𝔓.under (𝓞 K)) ⁻¹' {𝔭} :=
    fun 𝔓 h𝔓 ↦ h𝔓.1
  simp only [hp, not_false_eq_true, ite_true, Set.indicator_of_mem (Set.mem_compl hp)]
  rw [tsum_subtype _ fun 𝔓 ↦ A.indicator (fun _ ↦ x) 𝔓, Set.indicator_indicator,
    Set.inter_eq_right.mpr hAsub, ← tsum_subtype, tsum_const, Nat.card_coe_set_eq, nsmul_eq_mul]
  ring

/-- **Primes of relative degree one in a finite extension.** For an extension `L/K` of number
fields and `c ∈ ℂ`, the function sending a prime `𝔭` of `K` to `c` times the number of primes `𝔓`
of `L` above `𝔭` with `N(𝔓) = N(𝔭)` (those of relative degree one) has prime density `c`. Its
series over the primes of degree one of `K` is, term by term, the series of the constant `c` over
the primes of degree one of `L`, grouped by the prime below. -/
theorem hasPrimeDensity_mul_ncard_setOf_under_eq_and_absNorm_eq (c : ℂ) :
    HasPrimeDensity (fun 𝔭 : HeightOneSpectrum (𝓞 K) ↦ c *
      ({𝔓 : HeightOneSpectrum (𝓞 L) | 𝔓.under (𝓞 K) = 𝔭 ∧
        Ideal.absNorm 𝔓.asIdeal = Ideal.absNorm 𝔭.asIdeal}.ncard : ℂ)) c := by
  obtain ⟨hsumL, hOL⟩ := hasPrimeDensity_const (K := L) c
  have hfib : ∀ᶠ s : ℝ in 𝓝[>] 1, HasSum (fun 𝔭 : HeightOneSpectrum (𝓞 K) ↦
      (higherDegreePrimes K)ᶜ.indicator (fun 𝔭 ↦ c *
        ({𝔓 : HeightOneSpectrum (𝓞 L) | 𝔓.under (𝓞 K) = 𝔭 ∧
          Ideal.absNorm 𝔓.asIdeal = Ideal.absNorm 𝔭.asIdeal}.ncard : ℂ)) 𝔭 /
        (Ideal.absNorm 𝔭.asIdeal : ℂ) ^ (s : ℂ))
      (degreeOnePrimeSum (fun _ : HeightOneSpectrum (𝓞 L) ↦ c) s) := by
    filter_upwards [hsumL] with s hs
    rw [degreeOnePrimeSum_def]
    simpa only [tsum_fiber_under_eq] using
      hs.hasSum.tsum_fiberwise fun 𝔓 : HeightOneSpectrum (𝓞 L) ↦ 𝔓.under (𝓞 K)
  refine ⟨hfib.mono fun s hs ↦ hs.summable, hOL.congr' ?_ .rfl⟩
  filter_upwards [hfib] with s hs
  rw [degreeOnePrimeSum_def (K := K), hs.tsum_eq]

end Extension

end TauCeti
