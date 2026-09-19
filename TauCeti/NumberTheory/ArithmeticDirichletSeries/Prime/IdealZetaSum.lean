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
import TauCeti.Analysis.SpecialFunctions.Log.NegLogOneSub
import TauCeti.Analysis.SpecialFunctions.Log.OneDivSub
import TauCeti.NumberTheory.ArithmeticDirichletSeries.Convergence
import TauCeti.NumberTheory.ArithmeticDirichletSeries.EulerProduct.Logarithm.DedekindZeta
import TauCeti.Topology.Algebra.Order.Field

/-!
# The all-prime Dirichlet sum is `log (1 / (s - 1)) + O(1)`

For a number field `K`, write `P(s) = ∑_𝔭 N(𝔭) ^ (-s)` for the sum over all height-one primes of
`𝓞 K`, which is `NumberField.Set.primeIdealZetaSum Set.univ s`. This file proves that
`P(s) = log (1 / (s - 1)) + O(1)` as `s → 1⁺`, and hence that Mathlib's ratio-normalized
`NumberField.Set.HasDirichletDensity` agrees with the logarithmically normalized density.

The proof has two inputs, and neither suffices alone.

* **The Euler product.** For real `s > 1`, `log ζ_K(s)` is the convergent sum
  `∑_𝔭 -log (1 - N(𝔭) ^ (-s))`, by `TauCeti.log_dedekindZeta_re_eq_tsum_neg_log_one_sub`. Since
  `N(𝔭) ≥ 2`, every local ratio `x = N(𝔭) ^ (-s)` lies in `(0, 1/2]`, where
  `x ≤ -log (1 - x) ≤ x + 2 x ^ 2`.
  Summing, `log ζ_K(s)` differs from `P(s)` by at most `2 P(2)`, uniformly in `s > 1`: the higher
  prime powers contribute a bounded amount.
* **The residue.** Mathlib's class number formula
  `NumberField.tendsto_sub_one_mul_dedekindZeta_nhdsGT` says that `(s - 1) ζ_K(s)` tends to the
  positive residue as `s → 1⁺`, so `log ζ_K(s) - log (1 / (s - 1))` tends to its logarithm.

## Main results

* `TauCeti.primeIdealZetaSum_univ_le_log_dedekindZeta_re` and
  `TauCeti.log_dedekindZeta_re_le_primeIdealZetaSum_univ_add`: the two-sided comparison of
  `log ζ_K(s)` with `P(s)`, with error at most `2 P(2)`.
* `TauCeti.tendsto_log_dedekindZeta_re_sub_log_one_div_sub_one`: `log ζ_K(s) - log (1 / (s - 1))`
  tends to the logarithm of the residue.
* `TauCeti.primeIdealZetaSum_univ_sub_log_one_div_sub_one_isBigO`:
  `P(s) - log (1 / (s - 1)) = O(1)` as `s → 1⁺`.
* `TauCeti.tendsto_primeIdealZetaSum_univ_atTop`: `P(s) → ∞` as `s → 1⁺`.
* `TauCeti.tendsto_primeIdealZetaSum_univ_div_log_one_div_sub_one`:
  `P(s) / log (1 / (s - 1)) → 1` as `s → 1⁺`.
* `NumberField.Set.hasDirichletDensity_iff_tendsto_div_log_one_div_sub_one`: a set of primes has
  Dirichlet density `δ` exactly when `P_S(s) / log (1 / (s - 1)) → δ`.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII, §13.
* J.-P. Serre, *A Course in Arithmetic*, Chapter VI, §4.1.
* The same argument (Sharifi, *Algebraic Number Theory*, 7.1.12) is formalized in the
  Birkbeck–Brasca Chebotarev density project, <https://github.com/CBirkbeck/chebotarev-density>
  (Apache-2.0), commit `8575c9df1ae0a61120ab5c964c7911414254bec7`, file
  `CebotarevDensity/Density.lean`: `primeIdealZetaSum_univ_tendsto_log` and
  `primeIdealZetaSum_univ_tendsto_atTop`, closed there by the helpers of
  `CebotarevDensity/ForMathlib/LogOneDivSubOne.lean` that `Real.tendsto_log_one_div_sub_atTop`
  and `TauCeti.tendsto_div_nhds_one_of_le_add_const_of_sub_const_le` adapt. This file follows
  its outline (Euler-product logarithm, bounded higher-prime-power contribution, simple pole),
  over `HeightOneSpectrum` rather than the nonzero prime ideals of `𝓞 K`. It differs in the
  higher-power bound, taken termwise as `-log (1 - x) ≤ x + 2 x ^ 2` rather than through the
  geometric tail `N(𝔭) ^ (-2 s) / (1 - N(𝔭) ^ (-s))`, and in deriving the logarithmic form of the
  Euler product from `TauCeti.MultiplicativeIdealWeight.exp_tsum_neg_log_one_sub_eq_LSeries`.
-/

public section

open Filter Asymptotics IsDedekindDomain NumberField
open scoped Topology

namespace TauCeti

variable {K : Type*} [Field K] [NumberField K]

/-- **The prime sum is at most `log ζ_K(s)`.** For real `s > 1`, the sum of `N(𝔭) ^ (-s)` over all
height-one primes is at most the real logarithm of `ζ_K(s)`. -/
theorem primeIdealZetaSum_univ_le_log_dedekindZeta_re {s : ℝ} (hs : 1 < s) :
    (Set.univ : Set (HeightOneSpectrum (𝓞 K))).primeIdealZetaSum s ≤
      Real.log (dedekindZeta K s).re := by
  rw [log_dedekindZeta_re_eq_tsum_neg_log_one_sub hs, Set.primeIdealZetaSum_univ]
  exact (summable_absNorm_rpow_primes_of_one_lt hs).tsum_le_tsum
    (fun P ↦ by
      have hpos : 0 < 1 - (Ideal.absNorm P.asIdeal : ℝ) ^ (-s) := by
        linarith [P.absNorm_rpow_neg_le_half hs.le]
      linarith [Real.log_le_sub_one_of_pos hpos])
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
  rw [log_dedekindZeta_re_eq_tsum_neg_log_one_sub hs, Set.primeIdealZetaSum_univ,
    Set.primeIdealZetaSum_univ, ← tsum_mul_left, ← hsum.tsum_add (hsum2.mul_left 2)]
  -- Termwise, `-log (1 - x) ≤ x + 2 x ^ 2` and `x ^ 2 = N(𝔭) ^ (-2 s) ≤ N(𝔭) ^ (-2)`.
  refine (summable_neg_log_one_sub_absNorm_rpow hs).tsum_le_tsum (fun P ↦ ?_)
    (hsum.add (hsum2.mul_left 2))
  have hN : (1 : ℝ) ≤ Ideal.absNorm P.asIdeal := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr ((Ideal.absNorm_ne_zero_iff _).mpr inferInstance)
  have hsq : ((Ideal.absNorm P.asIdeal : ℝ) ^ (-s)) ^ 2 ≤
      (Ideal.absNorm P.asIdeal : ℝ) ^ (-2 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    exact Real.rpow_le_rpow_of_exponent_le hN (by push_cast; linarith)
  have h :=
    Real.neg_log_one_sub_le_add_two_mul_sq (by positivity) (P.absNorm_rpow_neg_le_half hs.le)
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
private theorem exists_abs_primeIdealZetaSum_univ_sub_log_one_div_sub_one_le :
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
theorem primeIdealZetaSum_univ_sub_log_one_div_sub_one_isBigO :
    (fun s : ℝ ↦ (Set.univ : Set (HeightOneSpectrum (𝓞 K))).primeIdealZetaSum s -
      Real.log (1 / (s - 1))) =O[𝓝[>] 1] fun _ ↦ (1 : ℝ) := by
  obtain ⟨C, hC⟩ := exists_abs_primeIdealZetaSum_univ_sub_log_one_div_sub_one_le (K := K)
  exact IsBigO.of_bound C (hC.mono fun s hs ↦ by simpa using hs)

/-- **The all-prime sum diverges at `1`.** The sum of `N(𝔭) ^ (-s)` over all height-one primes of
`𝓞 K` tends to `+∞` as `s → 1⁺`. -/
theorem tendsto_primeIdealZetaSum_univ_atTop :
    Tendsto (fun s : ℝ ↦ (Set.univ : Set (HeightOneSpectrum (𝓞 K))).primeIdealZetaSum s)
      (𝓝[>] 1) atTop := by
  obtain ⟨C, hC⟩ := exists_abs_primeIdealZetaSum_univ_sub_log_one_div_sub_one_le (K := K)
  refine tendsto_atTop_mono' _ (hC.mono fun s hs ↦ ?_)
    (tendsto_atTop_add_const_right _ (-C) (Real.tendsto_log_one_div_sub_atTop 1))
  linarith [(abs_le.mp hs).1]

/-- **The all-prime sum is asymptotic to `log (1 / (s - 1))`.** The ratio of the sum of
`N(𝔭) ^ (-s)` over all height-one primes of `𝓞 K` to `log (1 / (s - 1))` tends to `1` as
`s → 1⁺`. -/
theorem tendsto_primeIdealZetaSum_univ_div_log_one_div_sub_one :
    Tendsto (fun s : ℝ ↦ (Set.univ : Set (HeightOneSpectrum (𝓞 K))).primeIdealZetaSum s /
      Real.log (1 / (s - 1))) (𝓝[>] 1) (𝓝 1) := by
  obtain ⟨C, hC⟩ := exists_abs_primeIdealZetaSum_univ_sub_log_one_div_sub_one_le (K := K)
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
theorem hasDirichletDensity_iff_tendsto_div_log_one_div_sub_one
    (S : Set (HeightOneSpectrum (𝓞 K))) (δ : ℝ) :
    S.HasDirichletDensity δ ↔
      Tendsto (fun s : ℝ ↦ S.primeIdealZetaSum s / Real.log (1 / (s - 1))) (𝓝[>] 1) (𝓝 δ) := by
  have hratio := tendsto_primeIdealZetaSum_univ_div_log_one_div_sub_one (K := K)
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
