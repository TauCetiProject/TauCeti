/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.DedekindZeta
public import Mathlib.NumberTheory.NumberField.DirichletDensity
-- `NumberField.Set.HasDirichletDensity` is not exposed and Mathlib exports no lemma unfolding it;
-- its defining limit is needed to compare it with the logarithmic normalization.
import all Mathlib.NumberTheory.NumberField.DirichletDensity
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import TauCeti.Analysis.SpecialFunctions.Log.OneDivSub
import TauCeti.NumberTheory.ArithmeticDirichletSeries.Convergence
import TauCeti.NumberTheory.ArithmeticDirichletSeries.EulerProduct.Analytic
import TauCeti.Topology.Algebra.Order.Field

/-!
# The all-prime Dirichlet sum is `log (1 / (s - 1)) + O(1)`

For a number field `K`, write `P(s) = ∑_𝔭 N(𝔭) ^ (-s)` for the sum over all height-one primes of
`𝓞 K`, which is `NumberField.Set.primeIdealZetaSum Set.univ s`. This file proves that
`P(s) = log (1 / (s - 1)) + O(1)` as `s → 1⁺`, and hence that Mathlib's ratio-normalized
`NumberField.Set.HasDirichletDensity` agrees with the logarithmically normalized density.

The proof has two inputs, and neither suffices alone.

* **The Euler product.** For real `s > 1` the Dedekind zeta function is the product of the real
  local factors `(1 - N(𝔭) ^ (-s))⁻¹`, so `log ζ_K(s)` is the convergent sum
  `∑_𝔭 -log (1 - N(𝔭) ^ (-s))`. Since `N(𝔭) ≥ 2`, every local ratio `x = N(𝔭) ^ (-s)` lies in
  `(0, 1/2]`, where `x ≤ -log (1 - x) ≤ x + 2 x ^ 2`. Summing, `log ζ_K(s)` differs from `P(s)` by
  at most `2 P(2)`, uniformly in `s > 1`: the higher prime powers contribute a bounded amount.
* **The residue.** Mathlib's class number formula
  `NumberField.tendsto_sub_one_mul_dedekindZeta_nhdsGT` says that `(s - 1) ζ_K(s)` tends to the
  positive residue as `s → 1⁺`, so `log ζ_K(s) - log (1 / (s - 1))` tends to its logarithm.

## Main results

* `TauCeti.dedekindZeta_ofReal_eq_exp_tsum_neg_log_one_sub`: for real `s > 1`, `ζ_K(s)` is the
  exponential of the real sum `∑_𝔭 -log (1 - N(𝔭) ^ (-s))`.
* `TauCeti.primeIdealZetaSum_univ_le_log_dedekindZeta_re` and
  `TauCeti.log_dedekindZeta_re_le_primeIdealZetaSum_univ_add`: the two-sided comparison of
  `log ζ_K(s)` with `P(s)`, with error at most `2 P(2)`.
* `TauCeti.tendsto_log_dedekindZeta_re_sub_log_one_div_sub_one`: `log ζ_K(s) - log (1 / (s - 1))`
  tends to the logarithm of the residue.
* `TauCeti.primeIdealZetaSum_univ_sub_log_isBigO`: `P(s) - log (1 / (s - 1)) = O(1)` as `s → 1⁺`.
* `TauCeti.tendsto_primeIdealZetaSum_univ_atTop`: `P(s) → ∞` as `s → 1⁺`.
* `TauCeti.tendsto_primeIdealZetaSum_univ_div_log`: `P(s) / log (1 / (s - 1)) → 1` as `s → 1⁺`.
* `NumberField.Set.hasDirichletDensity_iff_tendsto_div_log`: a set of primes has Dirichlet density
  `δ` exactly when `P_S(s) / log (1 / (s - 1)) → δ`.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII, §13.
* J.-P. Serre, *A Course in Arithmetic*, Chapter VI, §4.1.
-/

public section

open Filter Asymptotics IsDedekindDomain NumberField
open scoped Topology

namespace TauCeti

variable {K : Type*} [Field K] [NumberField K]

/-! ### The local ratios -/

/-- For `1 ≤ s`, the local ratio `N(𝔭) ^ (-s)` of a height-one prime lies in `(0, 1/2]`, because
`N(𝔭) ≥ 2`. -/
private theorem absNorm_rpow_neg_le_half (P : HeightOneSpectrum (𝓞 K)) {s : ℝ} (hs : 1 ≤ s) :
    (Ideal.absNorm P.asIdeal : ℝ) ^ (-s) ≤ 1 / 2 := by
  have h2 : (2 : ℝ) ≤ Ideal.absNorm P.asIdeal := by
    exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm P
  calc (Ideal.absNorm P.asIdeal : ℝ) ^ (-s) ≤ (Ideal.absNorm P.asIdeal : ℝ) ^ (-1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
    _ ≤ 1 / 2 := by
        rw [Real.rpow_neg_one, one_div]
        exact inv_anti₀ (by norm_num) h2

/-- The local term `-log (1 - N(𝔭) ^ (-s))` of the logarithm of the Euler product lies between
the local ratio `x = N(𝔭) ^ (-s)` and `x + 2 x ^ 2`, for `1 ≤ s`. -/
private theorem neg_log_one_sub_absNorm_rpow_mem (P : HeightOneSpectrum (𝓞 K)) {s : ℝ}
    (hs : 1 ≤ s) :
    (Ideal.absNorm P.asIdeal : ℝ) ^ (-s) ≤ -Real.log (1 - (Ideal.absNorm P.asIdeal : ℝ) ^ (-s)) ∧
      -Real.log (1 - (Ideal.absNorm P.asIdeal : ℝ) ^ (-s)) ≤
        (Ideal.absNorm P.asIdeal : ℝ) ^ (-s) + 2 * ((Ideal.absNorm P.asIdeal : ℝ) ^ (-s)) ^ 2 := by
  set x := (Ideal.absNorm P.asIdeal : ℝ) ^ (-s)
  have hx0 : 0 ≤ x := by positivity
  have hx : x ≤ 1 / 2 := absNorm_rpow_neg_le_half P hs
  refine ⟨?_, ?_⟩
  · linarith [Real.log_le_sub_one_of_pos (show 0 < 1 - x by linarith)]
  · -- The first-order Taylor estimate `|x + log (1 - x)| ≤ x ^ 2 / (1 - x)`.
    have h := Real.abs_log_sub_add_sum_range_le (x := x) (by rw [abs_of_nonneg hx0]; linarith) 1
    simp only [Finset.range_one, Finset.sum_singleton, zero_add, pow_one, Nat.cast_zero, div_one,
      abs_of_nonneg hx0] at h
    have h' : x ^ 2 / (1 - x) ≤ 2 * x ^ 2 := by
      rw [div_le_iff₀ (by linarith)]
      nlinarith [sq_nonneg x]
    linarith [(abs_le.mp h).1]

private theorem summable_neg_log_one_sub_absNorm_rpow {s : ℝ} (hs : 1 < s) :
    Summable fun P : HeightOneSpectrum (𝓞 K) ↦
      -Real.log (1 - (Ideal.absNorm P.asIdeal : ℝ) ^ (-s)) := by
  refine ((summable_absNorm_rpow_primes_of_one_lt hs).mul_left 2).of_nonneg_of_le
    (fun P ↦ (Real.rpow_nonneg (Nat.cast_nonneg _) _).trans
      (neg_log_one_sub_absNorm_rpow_mem P hs.le).1) (fun P ↦ ?_)
  -- On `[0, 1/2]`, `x + 2 x ^ 2 ≤ 2 x`.
  have h := (neg_log_one_sub_absNorm_rpow_mem P hs.le).2
  have hx0 : 0 ≤ (Ideal.absNorm P.asIdeal : ℝ) ^ (-s) := by positivity
  have hx := absNorm_rpow_neg_le_half P hs.le
  nlinarith

/-! ### The Euler product in real logarithmic form -/

/-- **The real Euler product of the Dedekind zeta function in exponential form.** For real
`s > 1`, `ζ_K(s)` is the exponential of the convergent real sum
`∑_𝔭 -log (1 - N(𝔭) ^ (-s))` over the height-one primes of `𝓞 K`. In particular `ζ_K(s)` is a
positive real number, and that sum is its real logarithm. -/
theorem dedekindZeta_ofReal_eq_exp_tsum_neg_log_one_sub {s : ℝ} (hs : 1 < s) :
    dedekindZeta K s = (Real.exp (∑' P : HeightOneSpectrum (𝓞 K),
      -Real.log (1 - (Ideal.absNorm P.asIdeal : ℝ) ^ (-s))) : ℂ) := by
  have hprod := dedekindZeta_eulerProduct_hasProd (K := K) (s := (s : ℂ)) (by simpa using hs)
  have hexp := ((summable_neg_log_one_sub_absNorm_rpow (K := K) hs).hasSum.rexp).map
    Complex.ofRealHom Complex.continuous_ofReal
  refine hprod.unique (hexp.congr_fun fun P ↦ ?_)
  have hpos : 0 < 1 - (Ideal.absNorm P.asIdeal : ℝ) ^ (-s) := by
    linarith [absNorm_rpow_neg_le_half P hs.le]
  simp only [Function.comp_apply, Real.exp_neg, Real.exp_log hpos, Complex.ofRealHom_eq_coe,
    Complex.ofReal_inv, Complex.ofReal_sub, Complex.ofReal_one,
    Complex.ofReal_cpow (Nat.cast_nonneg _), Complex.ofReal_neg, Complex.ofReal_natCast]

/-- For real `s > 1`, the real part of `ζ_K(s)` is the exponential of `∑_𝔭 -log (1 - N(𝔭) ^ (-s))`.
-/
private theorem dedekindZeta_re_eq_exp {s : ℝ} (hs : 1 < s) :
    (dedekindZeta K s).re = Real.exp (∑' P : HeightOneSpectrum (𝓞 K),
      -Real.log (1 - (Ideal.absNorm P.asIdeal : ℝ) ^ (-s))) := by
  rw [dedekindZeta_ofReal_eq_exp_tsum_neg_log_one_sub hs, Complex.ofReal_re]

/-- For real `s > 1`, the real part of `ζ_K(s)` is positive. -/
private theorem dedekindZeta_re_pos {s : ℝ} (hs : 1 < s) : 0 < (dedekindZeta K s).re := by
  rw [dedekindZeta_re_eq_exp hs]
  exact Real.exp_pos _

/-- The all-prime Dirichlet sum, as the sum over the whole height-one spectrum. -/
private theorem primeIdealZetaSum_univ_eq_tsum (s : ℝ) :
    (Set.univ : Set (HeightOneSpectrum (𝓞 K))).primeIdealZetaSum s =
      ∑' P : HeightOneSpectrum (𝓞 K), (Ideal.absNorm P.asIdeal : ℝ) ^ (-s) := by
  rw [Set.primeIdealZetaSum_def,
    tsum_univ fun P : HeightOneSpectrum (𝓞 K) ↦ (Ideal.absNorm P.asIdeal : ℝ) ^ (-s)]

/-- **The prime sum is at most `log ζ_K(s)`.** For real `s > 1`, the sum of `N(𝔭) ^ (-s)` over all
height-one primes is at most the real logarithm of `ζ_K(s)`. -/
theorem primeIdealZetaSum_univ_le_log_dedekindZeta_re {s : ℝ} (hs : 1 < s) :
    (Set.univ : Set (HeightOneSpectrum (𝓞 K))).primeIdealZetaSum s ≤
      Real.log (dedekindZeta K s).re := by
  rw [dedekindZeta_re_eq_exp hs, Real.log_exp, primeIdealZetaSum_univ_eq_tsum]
  exact (summable_absNorm_rpow_primes_of_one_lt hs).tsum_le_tsum
    (fun P ↦ (neg_log_one_sub_absNorm_rpow_mem P hs.le).1)
    (summable_neg_log_one_sub_absNorm_rpow hs)

/-- **`log ζ_K(s)` exceeds the prime sum by at most `2 P(2)`.** For real `s > 1`, the real
logarithm of `ζ_K(s)` is at most the all-prime sum at `s` plus twice the all-prime sum at `2`, a
constant independent of `s` that bounds the contribution of the higher prime powers. -/
theorem log_dedekindZeta_re_le_primeIdealZetaSum_univ_add {s : ℝ} (hs : 1 < s) :
    Real.log (dedekindZeta K s).re ≤
      (Set.univ : Set (HeightOneSpectrum (𝓞 K))).primeIdealZetaSum s +
        2 * (Set.univ : Set (HeightOneSpectrum (𝓞 K))).primeIdealZetaSum 2 := by
  have hsum := summable_absNorm_rpow_primes_of_one_lt (K := K) hs
  have hsum2 := summable_absNorm_rpow_primes_of_one_lt (K := K) one_lt_two
  rw [dedekindZeta_re_eq_exp hs, Real.log_exp, primeIdealZetaSum_univ_eq_tsum,
    primeIdealZetaSum_univ_eq_tsum, ← tsum_mul_left, ← hsum.tsum_add (hsum2.mul_left 2)]
  -- Termwise, `-log (1 - x) ≤ x + 2 x ^ 2` and `x ^ 2 = N(𝔭) ^ (-2 s) ≤ N(𝔭) ^ (-2)`.
  refine (summable_neg_log_one_sub_absNorm_rpow hs).tsum_le_tsum (fun P ↦ ?_)
    (hsum.add (hsum2.mul_left 2))
  have hN : (1 : ℝ) ≤ Ideal.absNorm P.asIdeal := by
    exact_mod_cast (NumberField.HeightOneSpectrum.one_lt_absNorm P).le
  have hsq : ((Ideal.absNorm P.asIdeal : ℝ) ^ (-s)) ^ 2 ≤
      (Ideal.absNorm P.asIdeal : ℝ) ^ (-2 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    exact Real.rpow_le_rpow_of_exponent_le hN (by push_cast; linarith)
  have h := (neg_log_one_sub_absNorm_rpow_mem P hs.le).2
  linarith

/-! ### The residue and the logarithmic normalization -/

/-- **`log ζ_K(s) = log (1 / (s - 1)) + log κ_K + o(1)`.** As `s → 1⁺`, the difference between the
real logarithm of `ζ_K(s)` and `log (1 / (s - 1))` tends to the logarithm of the residue
`NumberField.dedekindZeta_residue K`. This is the logarithm of Mathlib's class number formula
`NumberField.tendsto_sub_one_mul_dedekindZeta_nhdsGT`. -/
theorem tendsto_log_dedekindZeta_re_sub_log_one_div_sub_one :
    Tendsto (fun s : ℝ ↦ Real.log (dedekindZeta K s).re - Real.log (1 / (s - 1))) (𝓝[>] 1)
      (𝓝 (Real.log (dedekindZeta_residue K))) := by
  have hre : Tendsto (fun s : ℝ ↦ (s - 1) * (dedekindZeta K s).re) (𝓝[>] 1)
      (𝓝 (dedekindZeta_residue K)) := by
    have h := (Complex.continuous_re.tendsto _).comp (tendsto_sub_one_mul_dedekindZeta_nhdsGT K)
    refine (Complex.ofReal_re (dedekindZeta_residue K) ▸ h).congr fun s ↦ ?_
    simp only [Function.comp_apply]
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.re_ofReal_mul]
  refine (hre.log (dedekindZeta_residue_ne_zero K)).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hs' : 0 < s - 1 := sub_pos.mpr hs
  rw [Real.log_mul hs'.ne' (dedekindZeta_re_pos hs).ne', one_div, Real.log_inv]
  ring

/-- The all-prime sum stays within a bounded distance of `log (1 / (s - 1))` near `1⁺`. -/
private theorem exists_abs_primeIdealZetaSum_univ_sub_log_le :
    ∃ C : ℝ, ∀ᶠ s in 𝓝[>] (1 : ℝ),
      |(Set.univ : Set (HeightOneSpectrum (𝓞 K))).primeIdealZetaSum s -
        Real.log (1 / (s - 1))| ≤ C := by
  refine ⟨|Real.log (dedekindZeta_residue K)| + 1 +
    2 * (Set.univ : Set (HeightOneSpectrum (𝓞 K))).primeIdealZetaSum 2, ?_⟩
  have hnear : ∀ᶠ s : ℝ in 𝓝[>] (1 : ℝ),
      |Real.log (dedekindZeta K s).re - Real.log (1 / (s - 1))| ≤
        |Real.log (dedekindZeta_residue K)| + 1 := by
    refine (tendsto_log_dedekindZeta_re_sub_log_one_div_sub_one (K := K)).abs.eventually
      (ge_mem_nhds ?_)
    linarith
  filter_upwards [hnear, self_mem_nhdsWithin] with s hnear hs
  have h1 := primeIdealZetaSum_univ_le_log_dedekindZeta_re (K := K) hs
  have h2 := log_dedekindZeta_re_le_primeIdealZetaSum_univ_add (K := K) hs
  have h3 := (Set.univ : Set (HeightOneSpectrum (𝓞 K))).primeIdealZetaSum_nonneg 2
  rw [abs_le] at hnear ⊢
  constructor <;> linarith [hnear.1, hnear.2]

/-- **The all-prime normalization.** As `s → 1⁺`, the sum of `N(𝔭) ^ (-s)` over all height-one
primes of `𝓞 K` is `log (1 / (s - 1)) + O(1)`. -/
theorem primeIdealZetaSum_univ_sub_log_isBigO :
    (fun s : ℝ ↦ (Set.univ : Set (HeightOneSpectrum (𝓞 K))).primeIdealZetaSum s -
      Real.log (1 / (s - 1))) =O[𝓝[>] 1] fun _ ↦ (1 : ℝ) := by
  obtain ⟨C, hC⟩ := exists_abs_primeIdealZetaSum_univ_sub_log_le (K := K)
  exact IsBigO.of_bound C (hC.mono fun s hs ↦ by simpa using hs)

/-- **The all-prime sum diverges at `1`.** The sum of `N(𝔭) ^ (-s)` over all height-one primes of
`𝓞 K` tends to `+∞` as `s → 1⁺`. -/
theorem tendsto_primeIdealZetaSum_univ_atTop :
    Tendsto (fun s : ℝ ↦ (Set.univ : Set (HeightOneSpectrum (𝓞 K))).primeIdealZetaSum s)
      (𝓝[>] 1) atTop := by
  obtain ⟨C, hC⟩ := exists_abs_primeIdealZetaSum_univ_sub_log_le (K := K)
  refine tendsto_atTop_mono' _ (hC.mono fun s hs ↦ ?_)
    (tendsto_atTop_add_const_right _ (-C) (Real.tendsto_log_one_div_sub_atTop 1))
  linarith [(abs_le.mp hs).1]

/-- **The all-prime sum is asymptotic to `log (1 / (s - 1))`.** The ratio of the sum of
`N(𝔭) ^ (-s)` over all height-one primes of `𝓞 K` to `log (1 / (s - 1))` tends to `1` as
`s → 1⁺`. -/
theorem tendsto_primeIdealZetaSum_univ_div_log :
    Tendsto (fun s : ℝ ↦ (Set.univ : Set (HeightOneSpectrum (𝓞 K))).primeIdealZetaSum s /
      Real.log (1 / (s - 1))) (𝓝[>] 1) (𝓝 1) := by
  obtain ⟨C, hC⟩ := exists_abs_primeIdealZetaSum_univ_sub_log_le (K := K)
  exact tendsto_div_nhds_one_of_le_add_const_of_sub_const_le
    (Real.tendsto_log_one_div_sub_atTop 1)
    ⟨C, hC.mono fun s hs ↦ by linarith [(abs_le.mp hs).2]⟩
    ⟨C, hC.mono fun s hs ↦ by linarith [(abs_le.mp hs).1]⟩

end TauCeti

namespace NumberField.Set

open TauCeti

variable {K : Type*} [Field K] [NumberField K]

/-- **Dirichlet density in logarithmic normalization.** A set `S` of height-one primes of `𝓞 K`
has Dirichlet density `δ`, defined as the limit of `P_S(s) / P(s)` with `P` the all-prime sum,
exactly when `P_S(s) / log (1 / (s - 1))` tends to `δ` as `s → 1⁺`. -/
theorem hasDirichletDensity_iff_tendsto_div_log (S : Set (HeightOneSpectrum (𝓞 K))) (δ : ℝ) :
    S.HasDirichletDensity δ ↔
      Tendsto (fun s : ℝ ↦ S.primeIdealZetaSum s / Real.log (1 / (s - 1))) (𝓝[>] 1) (𝓝 δ) := by
  have hratio := tendsto_primeIdealZetaSum_univ_div_log (K := K)
  have hP : ∀ᶠ s in 𝓝[>] (1 : ℝ),
      0 < (Set.univ : Set (HeightOneSpectrum (𝓞 K))).primeIdealZetaSum s :=
    tendsto_primeIdealZetaSum_univ_atTop.eventually_gt_atTop 0
  have hL : ∀ᶠ s in 𝓝[>] (1 : ℝ), 0 < Real.log (1 / (s - 1)) :=
    (Real.tendsto_log_one_div_sub_atTop 1).eventually_gt_atTop 0
  rw [HasDirichletDensity]
  constructor
  · intro h
    refine (mul_one δ ▸ h.mul hratio).congr' ?_
    filter_upwards [hP] with s hs
    rw [div_mul_div_cancel₀ hs.ne']
  · intro h
    refine (div_one δ ▸ h.div hratio one_ne_zero).congr' ?_
    filter_upwards [hL] with s hs
    rw [Pi.div_apply, div_div_div_cancel_right₀ hs.ne']

end NumberField.Set
