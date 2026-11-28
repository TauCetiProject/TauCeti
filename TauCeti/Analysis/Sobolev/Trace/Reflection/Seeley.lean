/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Group.Tannery
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.LinearAlgebra.Lagrange
public import TauCeti.Analysis.Sobolev.Trace.Reflection.HalfSpace
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import TauCeti.Analysis.Calculus.ContDiff.Cutoff
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Seeley's extension of smooth functions across a half-space boundary

A function which is `C^∞` on the closed upper half-space `{(t, x) | 0 ≤ t}` of `ℝ × E` is the
restriction of a `C^∞` function on the whole space. Seeley's extension operator defines it at
negative times by an infinite reflection

`(seeleyExtension f) (t, x) = ∑ₖ aₖ ψ(-2ᵏ t) f(-2ᵏ t, x)`,  `t < 0`,

where `ψ` is a smooth cutoff equal to `1` on `(-∞, 1]` and to `0` on `[2, ∞)`, and the coefficients
`aₖ = seeleyCoeff k` solve the infinite moment problem

`∑ₖ aₖ (-2ᵏ) ^ j = 1` for every `j`, with `∑ₖ |aₖ| 2 ^ (k j) < ∞`

(`TauCeti.HalfSpaceExtension.tsum_seeleyCoeff_mul_neg_pow` and
`TauCeti.HalfSpaceExtension.summable_abs_seeleyCoeff_mul_pow`). The moment identities say that every
derivative of the reflected function matches the corresponding derivative of `f` at `t = 0`, and the
cutoff makes the series converge with all its derivatives. Unlike the finite reflections of
`TauCeti.HalfSpaceExtension.halfSpaceReflection`, which preserve `Cⁿ` regularity only for bounded
`n`, one operator works for every order at once: it sends `Cⁿ` inputs to `Cⁿ` functions for every
`n : ℕ∞` (`TauCeti.HalfSpaceExtension.contDiff_seeleyExtension`). The extension depends only on
the values of `f` on the closed half-space, and it is linear on the inputs continuous there.

The coefficients are Seeley's `aₖ = ∏_{j ≠ k} (1 + 2ʲ) / (2ʲ - 2ᵏ)`. For finitely many nodes
`2⁰, …, 2ᴺ` the products over `j ≤ N` are the Lagrange weights which evaluate an interpolating
polynomial at `-1`, so `∑_{k ≤ N} a_k^{(N)} 2^{k n} = (-1) ^ n` for `n ≤ N`. The factors with
`j < k` make `a_k^{(N)}` decay like `2^{-k² / 2}`, uniformly in `N`, while the factors with `j > k`
form a convergent product. Tannery's theorem passes the identities to the limit `N → ∞`.

## Main declarations

* `TauCeti.HalfSpaceExtension.seeleyCoeff`: Seeley's coefficients.
* `TauCeti.HalfSpaceExtension.tsum_seeleyCoeff_smul_compContinuousLinearMap_timeScale`: the
  coefficients reproduce every continuous multilinear map from its time dilations by `-2ᵏ`.
* `TauCeti.HalfSpaceExtension.seeleyExtension`: Seeley's extension operator.
* `TauCeti.HalfSpaceExtension.contDiff_seeleyExtension`: the extension of a function `Cⁿ` on the
  closed upper half-space is `Cⁿ`, for every `n : ℕ∞`.
* `TauCeti.HalfSpaceExtension.iteratedFDeriv_seeleyExtension_of_neg` and
  `TauCeti.HalfSpaceExtension.norm_iteratedFDeriv_seeleyExtension_le_of_neg`: the derivatives of
  the extension at negative times are the reflected derivatives of the cut-off input
  `TauCeti.HalfSpaceExtension.seeleyCutoff`, with the resulting estimates.
* `TauCeti.HalfSpaceExtension.iteratedFDeriv_seeleyExtension_of_nonneg`: at nonnegative times the
  derivatives of the extension are those of the input within the closed upper half-space.
* `TauCeti.HalfSpaceExtension.exists_contDiff_eqOn_upperHalfSpace`: a function `Cⁿ` on the
  half-space near a point agrees there, near the point, with a function `Cⁿ` on the whole space.
* `TauCeti.HalfSpaceExtension.exists_contDiff_eqOn_Ici_prod`,
  `TauCeti.HalfSpaceExtension.exists_contDiff_eqOn_Iic_prod`: a function `Cⁿ` on the closed
  half-space `[a, ∞) × E` or `(-∞, b] × E` is the restriction of a function `Cⁿ` on the whole
  space, for every `n : ℕ∞`; by translation and reflection in time.
* `TauCeti.HalfSpaceExtension.exists_contDiff_eqOn_Icc_prod`,
  `TauCeti.HalfSpaceExtension.exists_contDiff_eqOn_prod_Icc`: a function `Cⁿ` on a closed slab
  `[a, b] × E`, or `E × [a, b]`, is the restriction of a function `Cⁿ` on the whole space. A cutoff
  in the slab coordinate splits it into two parts, each extended across one of the two boundary
  hyperplanes.

## References

* R. T. Seeley, *Extension of `C^∞` functions defined in a half space*,
  Proc. Amer. Math. Soc. **15** (1964), 625–626.
-/

public section

open Set Filter
open scoped Topology ContDiff BigOperators

noncomputable section

namespace TauCeti.HalfSpaceExtension

/-! ### Seeley's coefficients -/

/-- The factor of node `j` in the Lagrange weight of node `k`, for the nodes `2 ^ j` and the
evaluation point `-1`. -/
private def seeleyFactor (k j : ℕ) : ℝ := (-1 - 2 ^ j) / (2 ^ k - 2 ^ j)

/-- The Lagrange weight of the node `2 ^ k` among the nodes `2 ^ 0, …, 2 ^ N`, at the point `-1`. -/
private def seeleyWeight (N k : ℕ) : ℝ :=
  (Lagrange.basis (Finset.range (N + 1)) (fun j : ℕ ↦ (2 : ℝ) ^ j) k).eval (-1)

/-- The factors of the nodes below `k`. -/
private def seeleyHead (k : ℕ) : ℝ := ∏ j ∈ Finset.range k, seeleyFactor k j

/-- The factors of the first `M` nodes above `k`. -/
private def seeleyTail (k M : ℕ) : ℝ := ∏ i ∈ Finset.range M, seeleyFactor k (k + 1 + i)

private theorem seeleyWeight_eq_prod (N k : ℕ) :
    seeleyWeight N k = ∏ j ∈ (Finset.range (N + 1)).erase k, seeleyFactor k j := by
  simp only [seeleyWeight, Lagrange.basis, Polynomial.eval_prod, Lagrange.basisDivisor,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_sub, Polynomial.eval_X, seeleyFactor,
    div_eq_inv_mul]

private theorem seeleyWeight_eq_head_mul_tail {N k : ℕ} (hk : k ≤ N) :
    seeleyWeight N k = seeleyHead k * seeleyTail k (N - k) := by
  have hsplit : (Finset.range (N + 1)).erase k = Finset.range k ∪ Finset.Ico (k + 1) (N + 1) := by
    ext j
    simp only [Finset.mem_erase, Finset.mem_range, Finset.mem_union, Finset.mem_Ico]
    omega
  have hdisj : Disjoint (Finset.range k) (Finset.Ico (k + 1) (N + 1)) := by
    rw [Finset.disjoint_left]
    intro j hj hj'
    simp only [Finset.mem_range, Finset.mem_Ico] at hj hj'
    omega
  rw [seeleyWeight_eq_prod, hsplit, Finset.prod_union hdisj, seeleyHead, seeleyTail,
    Finset.prod_Ico_eq_prod_range, show N + 1 - (k + 1) = N - k by omega]

/-- The Lagrange weights reproduce the monomials of degree at most `N` at `-1`. -/
private theorem sum_seeleyWeight_mul_pow {N n : ℕ} (hn : n ≤ N) :
    ∑ k ∈ Finset.range (N + 1), seeleyWeight N k * ((2 : ℝ) ^ k) ^ n = (-1) ^ n := by
  have hinj : InjOn (fun j : ℕ ↦ (2 : ℝ) ^ j) (↑(Finset.range (N + 1)) : Set ℕ) :=
    fun a _ b _ h ↦ pow_right_injective₀ two_pos (by norm_num) h
  have hdeg : (Polynomial.X ^ n : Polynomial ℝ).degree < (Finset.range (N + 1)).card := by
    rw [Polynomial.degree_X_pow, Finset.card_range]
    exact_mod_cast Nat.lt_succ_of_le hn
  have h := congrArg (Polynomial.eval (-1)) (Lagrange.eq_interpolate hinj hdeg)
  rw [Lagrange.interpolate_apply, Polynomial.eval_finsetSum] at h
  simp only [Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_mul, Polynomial.eval_C] at h
  rw [h]
  exact Finset.sum_congr rfl fun k _ ↦ mul_comm _ _

/-- A factor above `k` lies between `1` and `1 + 2 (1/2) ^ i`. -/
private theorem one_le_seeleyFactor_add (k i : ℕ) :
    1 ≤ seeleyFactor k (k + 1 + i) ∧ seeleyFactor k (k + 1 + i) ≤ 1 + 2 * (1 / 2) ^ i := by
  have hx : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
  have hy : (2 : ℝ) ^ (k + 1 + i) = 2 ^ k * (2 * 2 ^ i) := by ring
  have hi : (1 : ℝ) ≤ 2 ^ i := one_le_pow₀ (by norm_num)
  have hden : 2 ^ k * 2 ^ i ≤ (2 : ℝ) ^ (k + 1 + i) - 2 ^ k := by rw [hy]; nlinarith
  have hpos : 0 < (2 : ℝ) ^ (k + 1 + i) - 2 ^ k := by
    have : (0 : ℝ) < 2 ^ k * 2 ^ i := by positivity
    linarith
  have heq : seeleyFactor k (k + 1 + i) =
      1 + (1 + 2 ^ k) / ((2 : ℝ) ^ (k + 1 + i) - 2 ^ k) := by
    have hne : (2 : ℝ) ^ k - 2 ^ (k + 1 + i) ≠ 0 := by linarith
    rw [seeleyFactor]
    field_simp
    ring
  rw [heq]
  refine ⟨le_add_of_nonneg_right (by positivity), ?_⟩
  gcongr 1 + ?_
  rw [div_le_iff₀ hpos]
  calc 1 + (2 : ℝ) ^ k ≤ 2 * 2 ^ k := by linarith
    _ = 2 * (1 / 2) ^ i * (2 ^ k * 2 ^ i) := by
      rw [one_div, inv_pow]; field_simp
    _ ≤ 2 * (1 / 2) ^ i * ((2 : ℝ) ^ (k + 1 + i) - 2 ^ k) := by gcongr

private theorem seeleyFactor_add_nonneg (k i : ℕ) : 0 ≤ seeleyFactor k (k + 1 + i) :=
  zero_le_one.trans (one_le_seeleyFactor_add k i).1

private theorem seeleyTail_nonneg (k M : ℕ) : 0 ≤ seeleyTail k M :=
  Finset.prod_nonneg fun i _ ↦ seeleyFactor_add_nonneg k i

private theorem seeleyTail_mono (k : ℕ) : Monotone (seeleyTail k) := by
  refine monotone_nat_of_le_succ fun M ↦ ?_
  rw [seeleyTail, seeleyTail, Finset.prod_range_succ]
  exact le_mul_of_one_le_right (seeleyTail_nonneg k M) (one_le_seeleyFactor_add k M).1

private theorem seeleyTail_le (k M : ℕ) : seeleyTail k M ≤ Real.exp 4 := by
  calc seeleyTail k M ≤ ∏ i ∈ Finset.range M, (1 + 2 * (1 / 2 : ℝ) ^ i) :=
        Finset.prod_le_prod₀ (fun i _ ↦ seeleyFactor_add_nonneg k i)
          fun i _ ↦ (one_le_seeleyFactor_add k i).2
    _ ≤ Real.exp (∑ i ∈ Finset.range M, 2 * (1 / 2 : ℝ) ^ i) :=
        Real.prod_one_add_le_exp_sum _ fun i ↦ by positivity
    _ ≤ Real.exp 4 := by
        gcongr
        rw [← Finset.mul_sum]
        linarith [sum_geometric_two_le M]

/-- The factors below `k` gain a factor `2 (1/2) ^ k` from `k` to `k + 1`. -/
private theorem abs_seeleyHead_succ_le (k : ℕ) :
    |seeleyHead (k + 1)| ≤ 2 * (1 / 2) ^ k * |seeleyHead k| := by
  have hfac (j : ℕ) (hj : j < k) : |seeleyFactor (k + 1) j| ≤ 1 / 2 * |seeleyFactor k j| := by
    have hjk : (2 : ℝ) ^ j < 2 ^ k := pow_lt_pow_right₀ (by norm_num) hj
    have hd : 0 < (2 : ℝ) ^ k - 2 ^ j := by linarith
    have hd' : 2 * ((2 : ℝ) ^ k - 2 ^ j) ≤ 2 ^ (k + 1) - 2 ^ j := by
      rw [pow_succ]; linarith [pow_pos (two_pos : (0 : ℝ) < 2) j]
    -- The denominator at least doubles from `k` to `k + 1`, so the factor at least halves.
    have hd2 : 0 < (2 : ℝ) ^ (k + 1) - 2 ^ j := by linarith
    rw [seeleyFactor, seeleyFactor, abs_div, abs_div, abs_of_pos hd, abs_of_pos hd2]
    calc |-1 - (2 : ℝ) ^ j| / (2 ^ (k + 1) - 2 ^ j)
        ≤ |-1 - (2 : ℝ) ^ j| / (2 * (2 ^ k - 2 ^ j)) :=
          div_le_div_of_nonneg_left (abs_nonneg _) (by positivity) hd'
      _ = 1 / 2 * (|-1 - (2 : ℝ) ^ j| / (2 ^ k - 2 ^ j)) := by
          rw [div_mul_eq_div_div_swap]; ring
  have hlast : |seeleyFactor (k + 1) k| ≤ 2 := by
    have hk : (0 : ℝ) < 2 ^ k := by positivity
    rw [seeleyFactor, pow_succ, abs_div, abs_of_pos (by linarith : (0 : ℝ) < 2 ^ k * 2 - 2 ^ k),
      div_le_iff₀ (by linarith), abs_le]
    constructor <;> nlinarith [one_le_pow₀ (M₀ := ℝ) (a := 2) (n := k) (by norm_num)]
  rw [seeleyHead, Finset.prod_range_succ, abs_mul, Finset.abs_prod, seeleyHead, Finset.abs_prod]
  calc (∏ j ∈ Finset.range k, |seeleyFactor (k + 1) j|) * |seeleyFactor (k + 1) k|
      ≤ (∏ j ∈ Finset.range k, (1 / 2 * |seeleyFactor k j|)) * 2 := by
        gcongr with j hj
        exact hfac j (Finset.mem_range.mp hj)
    _ = 2 * (1 / 2) ^ k * ∏ j ∈ Finset.range k, |seeleyFactor k j| := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]
        ring

private theorem summable_abs_seeleyHead_mul_pow (n : ℕ) :
    Summable fun k ↦ |seeleyHead k| * ((2 : ℝ) ^ k) ^ n := by
  refine summable_of_ratio_norm_eventually_le (r := 1 / 2) (by norm_num) ?_
  have hlim : Tendsto (fun k : ℕ ↦ 2 * 2 ^ n * (1 / 2 : ℝ) ^ k) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num)).const_mul (2 * 2 ^ n)
  filter_upwards [hlim.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))] with k hk
  rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
  calc |seeleyHead (k + 1)| * ((2 : ℝ) ^ (k + 1)) ^ n
      ≤ 2 * (1 / 2) ^ k * |seeleyHead k| * ((2 : ℝ) ^ (k + 1)) ^ n := by
        gcongr
        exact abs_seeleyHead_succ_le k
    _ = (2 * 2 ^ n * (1 / 2 : ℝ) ^ k) * (|seeleyHead k| * ((2 : ℝ) ^ k) ^ n) := by ring
    _ ≤ 1 / 2 * (|seeleyHead k| * ((2 : ℝ) ^ k) ^ n) := by gcongr

/-- **Seeley's coefficients** `aₖ = ∏_{j ≠ k} (1 + 2ʲ) / (2ʲ - 2ᵏ)`: the factors of the nodes
`j < k` times the convergent product of the factors of the nodes `j > k`
(`tendsto_prod_seeleyCoeff`). They satisfy
`∑ₖ aₖ (-2ᵏ) ^ j = 1` for every `j` (`tsum_seeleyCoeff_mul_neg_pow`) with absolute convergence
against every power of `2ᵏ` (`summable_abs_seeleyCoeff_mul_pow`). -/
def seeleyCoeff (k : ℕ) : ℝ := seeleyHead k * ⨆ M, seeleyTail k M

private theorem bddAbove_range_seeleyTail (k : ℕ) : BddAbove (Set.range (seeleyTail k)) :=
  ⟨Real.exp 4, by rintro _ ⟨M, rfl⟩; exact seeleyTail_le k M⟩

private theorem abs_seeleyCoeff_le (k : ℕ) : |seeleyCoeff k| ≤ Real.exp 4 * |seeleyHead k| := by
  have h0 : 0 ≤ ⨆ M, seeleyTail k M :=
    (seeleyTail_nonneg k 0).trans (le_ciSup (bddAbove_range_seeleyTail k) 0)
  rw [seeleyCoeff, abs_mul, abs_of_nonneg h0, mul_comm]
  gcongr
  exact ciSup_le fun M ↦ seeleyTail_le k M

private theorem tendsto_seeleyWeight (k : ℕ) :
    Tendsto (fun N ↦ seeleyWeight N k) atTop (𝓝 (seeleyCoeff k)) := by
  have htail : Tendsto (fun N ↦ seeleyTail k (N - k)) atTop (𝓝 (⨆ M, seeleyTail k M)) :=
    (tendsto_atTop_ciSup (seeleyTail_mono k) (bddAbove_range_seeleyTail k)).comp
      (tendsto_sub_atTop_nat k)
  refine (htail.const_mul (seeleyHead k)).congr' ?_
  filter_upwards [eventually_ge_atTop k] with N hN
  exact (seeleyWeight_eq_head_mul_tail hN).symm

/-- **Seeley's product formula.** The coefficient `aₖ` is the limit of the finite products
`∏_{j ≤ N, j ≠ k} (1 + 2ʲ) / (2ʲ - 2ᵏ)`, the Lagrange weights of the node `2ᵏ` among the nodes
`2⁰, …, 2ᴺ` at the point `-1`. -/
theorem tendsto_prod_seeleyCoeff (k : ℕ) :
    Tendsto (fun N ↦ ∏ j ∈ (Finset.range (N + 1)).erase k, (1 + (2 : ℝ) ^ j) / (2 ^ j - 2 ^ k))
      atTop (𝓝 (seeleyCoeff k)) := by
  refine (tendsto_seeleyWeight k).congr fun N ↦ ?_
  rw [seeleyWeight_eq_prod]
  refine Finset.prod_congr rfl fun j _ ↦ ?_
  rw [seeleyFactor, ← neg_div_neg_eq]
  congr 1 <;> ring

/-- Seeley's coefficients are absolutely summable against every power of `2ᵏ`. -/
theorem summable_abs_seeleyCoeff_mul_pow (n : ℕ) :
    Summable fun k ↦ |seeleyCoeff k| * ((2 : ℝ) ^ k) ^ n := by
  refine ((summable_abs_seeleyHead_mul_pow n).mul_left (Real.exp 4)).of_nonneg_of_le
    (fun k ↦ by positivity) fun k ↦ ?_
  rw [← mul_assoc]
  gcongr
  exact abs_seeleyCoeff_le k

/-- Seeley's coefficients against the powers of the nodes `2ᵏ` give the powers of `-1`. -/
theorem tsum_seeleyCoeff_mul_pow (n : ℕ) :
    ∑' k, seeleyCoeff k * ((2 : ℝ) ^ k) ^ n = (-1) ^ n := by
  classical
  let g : ℕ → ℕ → ℝ := fun N k ↦ if k ≤ N then seeleyWeight N k * ((2 : ℝ) ^ k) ^ n else 0
  have hlim : Tendsto (fun N ↦ ∑' k, g N k) atTop
      (𝓝 (∑' k, seeleyCoeff k * ((2 : ℝ) ^ k) ^ n)) := by
    refine tendsto_tsum_of_dominated_convergence
      ((summable_abs_seeleyHead_mul_pow n).mul_left (Real.exp 4)) (fun k ↦ ?_) ?_
    · refine ((tendsto_seeleyWeight k).mul_const _).congr' ?_
      filter_upwards [eventually_ge_atTop k] with N hN
      simp [g, hN]
    · refine Eventually.of_forall fun N k ↦ ?_
      by_cases hk : k ≤ N
      · simp only [g, hk, ↓reduceIte, Real.norm_eq_abs, abs_mul, abs_pow,
          abs_of_pos (pow_pos two_pos k : (0 : ℝ) < 2 ^ k), seeleyWeight_eq_head_mul_tail hk,
          abs_of_nonneg (seeleyTail_nonneg _ _)]
        rw [← mul_assoc, mul_comm (Real.exp 4)]
        gcongr
        exact seeleyTail_le k (N - k)
      · simp only [g, hk, ↓reduceIte, norm_zero]
        positivity
  have hconst : ∀ᶠ N in atTop, ∑' k, g N k = (-1) ^ n := by
    filter_upwards [eventually_ge_atTop n] with N hN
    rw [tsum_eq_sum (s := Finset.range (N + 1)) fun k hk ↦ by
      simp only [Finset.mem_range, not_lt] at hk
      simp [g, show ¬ k ≤ N by omega]]
    rw [← sum_seeleyWeight_mul_pow hN]
    exact Finset.sum_congr rfl fun k hk ↦ by
      simp [g, show k ≤ N from Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)]
  exact tendsto_nhds_unique hlim (tendsto_const_nhds.congr' (hconst.mono fun _ h ↦ h.symm))

/-- **Seeley's moment identities**: against the powers of the nodes `-2ᵏ`, Seeley's coefficients
sum to `1`. -/
theorem tsum_seeleyCoeff_mul_neg_pow (n : ℕ) :
    ∑' k, seeleyCoeff k * (-(2 : ℝ) ^ k) ^ n = 1 := by
  have h (k : ℕ) : seeleyCoeff k * (-(2 : ℝ) ^ k) ^ n =
      (-1) ^ n * (seeleyCoeff k * ((2 : ℝ) ^ k) ^ n) := by
    rw [neg_pow]; ring
  simp_rw [h]
  rw [tsum_mul_left, tsum_seeleyCoeff_mul_pow, ← mul_pow]
  norm_num

/-- Seeley's coefficients are summable against every power of the nodes `-2ᵏ`. -/
theorem summable_seeleyCoeff_mul_neg_pow (n : ℕ) :
    Summable fun k ↦ seeleyCoeff k * (-(2 : ℝ) ^ k) ^ n :=
  .of_norm (by simpa [abs_mul, abs_pow] using summable_abs_seeleyCoeff_mul_pow n)

/-! ### Reproducing multilinear maps from their dilations -/

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The terms of Seeley's reproducing series for a multilinear map of order `m` are bounded by
`|aₖ| (2ᵏ) ^ m ‖A‖`. -/
private theorem norm_seeleyCoeff_smul_compContinuousLinearMap_le {m : ℕ}
    (A : (ℝ × E) [×m]→L[ℝ] F) (k : ℕ) :
    ‖seeleyCoeff k • A.compContinuousLinearMap (fun _ ↦ timeScale (-2 ^ k))‖ ≤
      |seeleyCoeff k| * ((2 : ℝ) ^ k) ^ m * ‖A‖ := by
  have hnorm : ‖(timeScale (-2 ^ k) : (ℝ × E) →L[ℝ] ℝ × E)‖ ≤ 2 ^ k := by
    refine (norm_timeScale_le _).trans_eq ?_
    rw [abs_neg, abs_of_pos (by positivity), max_eq_left (one_le_pow₀ (by norm_num))]
  rw [norm_smul, Real.norm_eq_abs, mul_assoc]
  gcongr
  calc ‖A.compContinuousLinearMap fun _ ↦ timeScale (-2 ^ k)‖
      ≤ ‖A‖ * ∏ _ : Fin m, ‖(timeScale (-2 ^ k) : (ℝ × E) →L[ℝ] ℝ × E)‖ :=
        A.norm_compContinuousLinearMap_le _
    _ ≤ ‖A‖ * ∏ _ : Fin m, (2 : ℝ) ^ k := by gcongr
    _ = ((2 : ℝ) ^ k) ^ m * ‖A‖ := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin,
        mul_comm]

/-- **Seeley's coefficients reproduce multilinear maps.** A continuous multilinear map is the
`aₖ`-weighted sum of its precompositions with the time dilations by the nodes `-2ᵏ`. This is the
identity behind the matching of all derivatives of the extension across the boundary. -/
theorem tsum_seeleyCoeff_smul_compContinuousLinearMap_timeScale [CompleteSpace F] {m : ℕ}
    (A : (ℝ × E) [×m]→L[ℝ] F) :
    ∑' k, seeleyCoeff k • A.compContinuousLinearMap (fun _ ↦ timeScale (-2 ^ k)) = A := by
  classical
  have hsum : Summable fun k ↦
      seeleyCoeff k • A.compContinuousLinearMap (fun _ ↦ timeScale (-(2 : ℝ) ^ k)) :=
    .of_norm_bounded ((summable_abs_seeleyCoeff_mul_pow m).mul_right ‖A‖)
      (norm_seeleyCoeff_smul_compContinuousLinearMap_le A)
  ext v
  rw [ContinuousMultilinearMap.tsum_eval hsum]
  simp only [smul_apply, ContinuousMultilinearMap.compContinuousLinearMap_apply]
  simp_rw [map_timeScale_eq_sum_pow_card_smul, Finset.smul_sum, smul_smul]
  rw [Summable.tsum_finsetSum fun s _ ↦ (summable_seeleyCoeff_mul_neg_pow s.card).smul_const _]
  simp_rw [Summable.tsum_smul_const (summable_seeleyCoeff_mul_neg_pow _),
    tsum_seeleyCoeff_mul_neg_pow, one_smul]
  rw [← A.map_add_univ]
  congr 1
  funext i
  ext <;> simp

/-! ### The extension operator -/

/-- **Seeley's extension operator.** At nonnegative times it is `f`; at a negative time `t` it is
the infinite reflection `∑ₖ aₖ ψ(-2ᵏ t) f(-2ᵏ t, x)`, where `aₖ = seeleyCoeff k` and the cutoff
`ψ = Real.smoothTransition (2 - ·)` is `1` on `(-∞, 1]` and `0` on `[2, ∞)`. -/
def seeleyExtension (f : ℝ × E → F) (x : ℝ × E) : F :=
  if 0 ≤ x.1 then f x else
    ∑' k, seeleyCoeff k • Real.smoothTransition (2 + 2 ^ k * x.1) • f (timeScale (-2 ^ k) x)

/-- The extension agrees with the input at nonnegative times. -/
@[simp] theorem seeleyExtension_of_nonneg (f : ℝ × E → F) {x : ℝ × E} (hx : 0 ≤ x.1) :
    seeleyExtension f x = f x := by
  simp [seeleyExtension, hx]

/-- At negative times the extension is Seeley's infinite reflection. -/
@[simp] theorem seeleyExtension_of_neg (f : ℝ × E → F) {x : ℝ × E} (hx : x.1 < 0) :
    seeleyExtension f x =
      ∑' k, seeleyCoeff k • Real.smoothTransition (2 + 2 ^ k * x.1) • f (timeScale (-2 ^ k) x) := by
  simp [seeleyExtension, hx.not_ge]

/-- The extension extends the input from the closed upper half-space. -/
theorem seeleyExtension_eqOn_upperHalfSpace (f : ℝ × E → F) :
    EqOn (seeleyExtension f) f (upperHalfSpace E) :=
  fun _ hx ↦ seeleyExtension_of_nonneg f (mem_upperHalfSpace.mp hx)

/-- Reflecting a nonpositive time at a node `-2ᵏ` lands in the upper half-space. -/
theorem timeScale_neg_two_pow_mem_upperHalfSpace (k : ℕ) {x : ℝ × E} (hx : x.1 ≤ 0) :
    timeScale (-2 ^ k) x ∈ upperHalfSpace E := by
  rw [mem_upperHalfSpace, timeScale_apply]
  exact mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.mpr (pow_nonneg zero_le_two k)) hx

/-- The extension depends only on the input on the closed upper half-space. -/
theorem seeleyExtension_congr {f g : ℝ × E → F} (hfg : EqOn f g (upperHalfSpace E)) :
    seeleyExtension f = seeleyExtension g := by
  funext x
  by_cases hx : 0 ≤ x.1
  · simp only [seeleyExtension_of_nonneg _ hx]
    exact hfg (mem_upperHalfSpace.mpr hx)
  · simp only [seeleyExtension_of_neg _ (lt_of_not_ge hx)]
    exact tsum_congr fun k ↦ by
      rw [hfg (timeScale_neg_two_pow_mem_upperHalfSpace k (lt_of_not_ge hx).le)]

/-- The extension commutes with real scalar multiplication. -/
theorem seeleyExtension_smul (c : ℝ) (f : ℝ × E → F) :
    seeleyExtension (c • f) = c • seeleyExtension f := by
  funext x
  by_cases hx : 0 ≤ x.1
  · simp only [seeleyExtension_of_nonneg _ hx, Pi.smul_apply]
  · simp only [seeleyExtension_of_neg _ (lt_of_not_ge hx), Pi.smul_apply]
    rw [← tsum_const_smul'']
    exact tsum_congr fun k ↦ by rw [smul_comm _ c, smul_comm _ c]

/-! ### Smoothness of the extension -/

/-- The input cut off at normal coordinates `t ≥ 2`, unchanged for `t ≤ 1`. The extension at a
negative time is the reflected series of this cut-off input. -/
def seeleyCutoff (f : ℝ × E → F) (y : ℝ × E) : F := Real.smoothTransition (2 - y.1) • f y

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- The cut-off input is the input scaled by the smooth transition at `2 - t`. -/
theorem seeleyCutoff_apply (f : ℝ × E → F) (y : ℝ × E) :
    seeleyCutoff f y = Real.smoothTransition (2 - y.1) • f y := by
  rw [seeleyCutoff]

/-- Cutting off preserves smoothness on the closed upper half-space. -/
theorem contDiffOn_seeleyCutoff {n : ℕ∞} {f : ℝ × E → F}
    (hf : ContDiffOn ℝ n f (upperHalfSpace E)) :
    ContDiffOn ℝ n (seeleyCutoff f) (upperHalfSpace E) :=
  ((Real.smoothTransition.contDiff.comp (contDiff_const.sub contDiff_fst)).contDiffOn).smul hf

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- The cut-off input vanishes at normal coordinates `t > 2`. -/
theorem seeleyCutoff_eq_zero (f : ℝ × E → F) {y : ℝ × E} (hy : 2 < y.1) :
    seeleyCutoff f y = 0 := by
  rw [seeleyCutoff, Real.smoothTransition.zero_of_nonpos (by linarith), zero_smul]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- The cut-off input agrees with the input at normal coordinates `t ≤ 1`. -/
theorem seeleyCutoff_eq_self (f : ℝ × E → F) {y : ℝ × E} (hy : y.1 ≤ 1) :
    seeleyCutoff f y = f y := by
  rw [seeleyCutoff, Real.smoothTransition.one_of_one_le (by linarith), one_smul]

private theorem seeleyCutoff_timeScale (f : ℝ × E → F) (k : ℕ) (x : ℝ × E) :
    seeleyCutoff f (timeScale (-2 ^ k) x) =
      Real.smoothTransition (2 + 2 ^ k * x.1) • f (timeScale (-2 ^ k) x) := by
  rw [seeleyCutoff, timeScale_apply, neg_mul, sub_neg_eq_add]

/-- Along the orbits of a point of the lower half-space under the dilations by `-2ᵏ`, a function
continuous on the upper half-space and vanishing at normal coordinates `t > 2` is bounded,
uniformly near the point. -/
private theorem exists_forall_norm_timeScale_le {G : Type*} [NormedAddCommGroup G]
    {φ : ℝ × E → G} (hφ : ContinuousOn φ (upperHalfSpace E))
    (h0 : ∀ y : ℝ × E, 2 < y.1 → φ y = 0) (z₀ : ℝ × E) :
    ∃ C, ∀ᶠ z in 𝓝 z₀, z.1 ≤ 0 → ∀ k : ℕ, ‖φ (timeScale (-2 ^ k) z)‖ ≤ C := by
  set K : Set (ℝ × E) := Icc 0 2 ×ˢ {z₀.2} with hKdef
  have hK : IsCompact K := isCompact_Icc.prod isCompact_singleton
  have hKs : K ⊆ upperHalfSpace E := fun y hy ↦ mem_upperHalfSpace.mpr hy.1.1
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (hφ.mono hKs)
  -- Near the compact segment `K` the bound `C + 1` persists on the upper half-space.
  have hev : ∀ᶠ y in 𝓝ˢ K, y ∈ upperHalfSpace E → ‖φ y‖ < C + 1 := by
    rw [eventually_nhdsSet_iff_forall]
    intro y hy
    exact eventually_nhdsWithin_iff.mp ((hφ y (hKs hy)).norm.eventually
      (gt_mem_nhds (by linarith [hC y hy])))
  have hprod : 𝓝ˢ K = 𝓝ˢ (Icc (0 : ℝ) 2) ×ˢ 𝓝 z₀.2 := by
    rw [hKdef, isCompact_Icc.nhdsSet_prod_eq isCompact_singleton,
      nhdsSet_singleton]
  rw [hprod, eventually_prod_iff] at hev
  obtain ⟨pa, hpa, pb, hpb, hab⟩ := hev
  refine ⟨max (C + 1) 0, ?_⟩
  filter_upwards [(continuous_snd.tendsto z₀).eventually hpb] with z hz hz₁ k
  have ht : 0 ≤ -2 ^ k * z.1 :=
    mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.mpr (by positivity)) hz₁
  by_cases h2 : -2 ^ k * z.1 ≤ 2
  · rw [timeScale_apply]
    exact (hab (hpa.self_of_nhdsSet _ ⟨ht, h2⟩) hz (mem_upperHalfSpace.mpr ht)).le.trans
      (le_max_left _ _)
  · rw [h0 _ (by rw [timeScale_apply]; exact lt_of_not_ge h2), norm_zero]
    exact le_max_right _ _

/-- For an input continuous on the closed upper half-space, the series defining the extension at a
point of the lower half-space converges absolutely. -/
private theorem summable_seeleyCoeff_smul_seeleyCutoff [CompleteSpace F] {f : ℝ × E → F}
    (hf : ContinuousOn f (upperHalfSpace E)) {z : ℝ × E} (hz : z.1 ≤ 0) :
    Summable fun k ↦
      seeleyCoeff k • Real.smoothTransition (2 + 2 ^ k * z.1) • f (timeScale (-2 ^ k) z) := by
  have hcont : ContinuousOn (seeleyCutoff f) (upperHalfSpace E) :=
    (Real.smoothTransition.continuous.comp
      (continuous_const.sub continuous_fst)).continuousOn.smul hf
  obtain ⟨C, hC⟩ := exists_forall_norm_timeScale_le hcont (fun y hy ↦ seeleyCutoff_eq_zero f hy) z
  refine .of_norm_bounded (((summable_abs_seeleyCoeff_mul_pow 0).mul_right C)) fun k ↦ ?_
  rw [← seeleyCutoff_timeScale, norm_smul, Real.norm_eq_abs, pow_zero, mul_one]
  gcongr
  exact hC.self_of_nhds hz k

/-- For inputs continuous on the closed upper half-space, the extension is additive. -/
theorem seeleyExtension_add [CompleteSpace F] {f g : ℝ × E → F}
    (hf : ContinuousOn f (upperHalfSpace E)) (hg : ContinuousOn g (upperHalfSpace E)) :
    seeleyExtension (f + g) = seeleyExtension f + seeleyExtension g := by
  funext x
  by_cases hx : 0 ≤ x.1
  · simp only [seeleyExtension_of_nonneg _ hx, Pi.add_apply]
  · have hneg : x.1 < 0 := lt_of_not_ge hx
    simp only [seeleyExtension_of_neg _ hneg, Pi.add_apply]
    rw [← (summable_seeleyCoeff_smul_seeleyCutoff hf hneg.le).tsum_add
      (summable_seeleyCoeff_smul_seeleyCutoff hg hneg.le)]
    exact tsum_congr fun k ↦ by simp only [smul_add]

/-- **Seeley's reflection of a Taylor series.** Let `g` have a Taylor series `p` up to order `n` on
the closed upper half-space whose coefficients vanish at normal coordinates `t > 2`. If the
reflected series `∑ₖ aₖ g(-2ᵏ t, x)` converges on the lower half-space, it has there the reflected
Taylor series `∑ₖ aₖ p(-2ᵏ t, x)` precomposed with the dilations by `-2ᵏ`. -/
private theorem hasFTaylorSeriesUpToOn_tsum_seeleyCoeff_smul [CompleteSpace F] {n : ℕ∞}
    {g : ℝ × E → F} {p : ℝ × E → FormalMultilinearSeries ℝ (ℝ × E) F}
    (hp : HasFTaylorSeriesUpToOn n g p (upperHalfSpace E))
    (hp0 : ∀ m (y : ℝ × E), 2 < y.1 → p y m = 0)
    (hsum : ∀ z ∈ lowerHalfSpace E, Summable fun k ↦ seeleyCoeff k • g (timeScale (-2 ^ k) z)) :
    HasFTaylorSeriesUpToOn n (fun z ↦ ∑' k, seeleyCoeff k • g (timeScale (-2 ^ k) z))
      (fun z m ↦ ∑' k, seeleyCoeff k •
        (p (timeScale (-2 ^ k) z) m).compContinuousLinearMap fun _ ↦ timeScale (-2 ^ k))
      (lowerHalfSpace E) := by
  -- The partial sums have the partial sums of the reflected Taylor series.
  have hT (k : ℕ) : HasFTaylorSeriesUpToOn n (fun z ↦ seeleyCoeff k • g (timeScale (-2 ^ k) z))
      (fun z m ↦ seeleyCoeff k •
        (p (timeScale (-2 ^ k) z) m).compContinuousLinearMap fun _ ↦ timeScale (-2 ^ k))
      (lowerHalfSpace E) :=
    ((hp.compContinuousLinearMap (timeScale (-2 ^ k))).const_smul (seeleyCoeff k)).mono
      fun z hz ↦ timeScale_neg_two_pow_mem_upperHalfSpace k (mem_lowerHalfSpace.mp hz)
  -- By the Weierstrass test with the orbit bounds, the coefficients converge locally uniformly.
  have hloc (m : ℕ) (hm : (m : WithTop ℕ∞) ≤ n) : TendstoLocallyUniformlyOn
      (fun N z ↦ ∑ k ∈ Finset.range N, seeleyCoeff k •
        (p (timeScale (-2 ^ k) z) m).compContinuousLinearMap fun _ ↦ timeScale (-2 ^ k))
      (fun z ↦ ∑' k, seeleyCoeff k •
        (p (timeScale (-2 ^ k) z) m).compContinuousLinearMap fun _ ↦ timeScale (-2 ^ k))
      atTop (lowerHalfSpace E) := by
    rw [tendstoLocallyUniformlyOn_iff_filter]
    intro z₀ _
    obtain ⟨C, hC⟩ := exists_forall_norm_timeScale_le (hp.cont m hm) (hp0 m) z₀
    obtain ⟨U, hU, hUC⟩ := hC.exists_mem
    have hunif := tendstoUniformlyOn_tsum_nat
      ((summable_abs_seeleyCoeff_mul_pow m).mul_right C) (s := lowerHalfSpace E ∩ U)
      fun k z hz ↦ (norm_seeleyCoeff_smul_compContinuousLinearMap_le _ k).trans
        (mul_le_mul_of_nonneg_left (hUC z hz.2 (mem_lowerHalfSpace.mp hz.1) k) (by positivity))
    exact (tendstoUniformlyOn_iff_tendstoUniformlyOnFilter.mp hunif).mono_right
      (le_principal_iff.mpr (inter_mem_nhdsWithin _ hU))
  exact .of_tendstoLocallyUniformlyOn_of_convex
    (fun _ _ ↦ ⟨_, subset_rfl, convex_lowerHalfSpace, self_mem_nhdsWithin⟩)
    (fun N ↦ HasFTaylorSeriesUpToOn.sum fun k _ ↦ hT k) hloc
    fun z hz ↦ (hsum z hz).hasSum.tendsto_sum_nat

/-- On the closed lower half-space, the reflected series of the cut-off input has the reflected
Taylor series of the cut-off input. -/
private theorem hasFTaylorSeriesUpToOn_tsum_seeleyCoeff_smul_seeleyCutoff [CompleteSpace F]
    {n : ℕ∞} {f : ℝ × E → F} (hf : ContDiffOn ℝ n f (upperHalfSpace E)) :
    HasFTaylorSeriesUpToOn n
      (fun z ↦ ∑' k, seeleyCoeff k • seeleyCutoff f (timeScale (-2 ^ k) z))
      (fun z m ↦ ∑' k, seeleyCoeff k •
        (iteratedFDerivWithin ℝ m (seeleyCutoff f) (upperHalfSpace E)
          (timeScale (-2 ^ k) z)).compContinuousLinearMap fun _ ↦ timeScale (-2 ^ k))
      (lowerHalfSpace E) := by
  have hg : ContDiffOn ℝ n (seeleyCutoff f) (upperHalfSpace E) := contDiffOn_seeleyCutoff hf
  -- The Taylor coefficients of the cut-off input vanish at normal coordinates `t > 2`.
  have hp0 (m : ℕ) (y : ℝ × E) (hy : 2 < y.1) :
      ftaylorSeriesWithin ℝ (seeleyCutoff f) (upperHalfSpace E) y m = 0 := by
    have hev : seeleyCutoff f =ᶠ[𝓝[upperHalfSpace E] y] 0 :=
      eventually_nhdsWithin_of_eventually_nhds <|
        ((isOpen_lt continuous_const continuous_fst).eventually_mem hy).mono
          fun w hw ↦ seeleyCutoff_eq_zero f hw
    simp only [ftaylorSeriesWithin, hev.iteratedFDerivWithin_eq (seeleyCutoff_eq_zero f hy) m,
      iteratedFDerivWithin_zero, Pi.zero_apply]
  exact hasFTaylorSeriesUpToOn_tsum_seeleyCoeff_smul
    (hg.ftaylorSeriesWithin uniqueDiffOn_upperHalfSpace) hp0 fun z hz ↦ by
      simpa only [seeleyCutoff_timeScale] using
        summable_seeleyCoeff_smul_seeleyCutoff hf.continuousOn (mem_lowerHalfSpace.mp hz)

/-- **Seeley's extension theorem.** If `f` is `Cⁿ` on the closed upper half-space, for any
`n : ℕ∞`, its Seeley extension is `Cⁿ` on the whole space. -/
theorem contDiff_seeleyExtension [CompleteSpace F] {n : ℕ∞} {f : ℝ × E → F}
    (hf : ContDiffOn ℝ n f (upperHalfSpace E)) : ContDiff ℝ n (seeleyExtension f) := by
  classical
  have hq := hasFTaylorSeriesUpToOn_tsum_seeleyCoeff_smul_seeleyCutoff hf
  -- On the boundary the reflected Taylor series reproduces that of `f`, since the cutoff is `1`
  -- there and the coefficients reproduce multilinear maps.
  have hmatch : ∀ x ∈ upperHalfSpace E ∩ lowerHalfSpace E, ∀ m : ℕ, m ≤ n →
      ftaylorSeriesWithin ℝ f (upperHalfSpace E) x m = ∑' k, seeleyCoeff k •
        (iteratedFDerivWithin ℝ m (seeleyCutoff f) (upperHalfSpace E)
          (timeScale (-2 ^ k) x)).compContinuousLinearMap fun _ ↦ timeScale (-2 ^ k) := by
    intro x hx m _
    have htime : x.1 = 0 :=
      le_antisymm (mem_lowerHalfSpace.mp hx.2) (mem_upperHalfSpace.mp hx.1)
    have hτ (k : ℕ) : timeScale (-2 ^ k) x = x := by ext <;> simp [htime]
    have hgf : seeleyCutoff f =ᶠ[𝓝[upperHalfSpace E] x] f :=
      eventually_nhdsWithin_of_eventually_nhds <|
        ((isOpen_lt continuous_fst continuous_const).eventually_mem (by linarith : x.1 < 1)).mono
          fun w hw ↦ seeleyCutoff_eq_self f (le_of_lt hw)
    simp only [hτ]
    rw [tsum_seeleyCoeff_smul_compContinuousLinearMap_timeScale]
    simp only [ftaylorSeriesWithin,
      hgf.iteratedFDerivWithin_eq (seeleyCutoff_eq_self f (by linarith)) m]
  have hglue := (hf.ftaylorSeriesWithin uniqueDiffOn_upperHalfSpace).contDiff_piecewise hq
    isClosed_upperHalfSpace isClosed_lowerHalfSpace upperHalfSpace_union_lowerHalfSpace hmatch
  convert hglue using 1
  funext x
  by_cases hx : 0 ≤ x.1
  · rw [seeleyExtension_of_nonneg _ hx, piecewise_eq_of_mem _ _ _ (mem_upperHalfSpace.mpr hx)]
  · rw [seeleyExtension_of_neg _ (lt_of_not_ge hx),
      piecewise_eq_of_notMem _ _ _ fun h ↦ hx (mem_upperHalfSpace.mp h)]
    exact tsum_congr fun k ↦ by simp only [seeleyCutoff_timeScale]

/-- At a nonnegative time, the `m`-th derivative of the extension of a function `Cⁿ` on the closed
upper half-space, with `m ≤ n`, is the `m`-th derivative of the input within the closed upper
half-space. -/
theorem iteratedFDeriv_seeleyExtension_of_nonneg [CompleteSpace F] {n : ℕ∞} {f : ℝ × E → F}
    (hf : ContDiffOn ℝ n f (upperHalfSpace E)) {x : ℝ × E} (hx : 0 ≤ x.1) {m : ℕ}
    (hm : (m : ℕ∞) ≤ n) :
    iteratedFDeriv ℝ m (seeleyExtension f) x = iteratedFDerivWithin ℝ m f (upperHalfSpace E) x := by
  have hxs : x ∈ upperHalfSpace E := mem_upperHalfSpace.mpr hx
  rw [← iteratedFDerivWithin_congr (seeleyExtension_eqOn_upperHalfSpace f) hxs,
    iteratedFDerivWithin_eq_iteratedFDeriv uniqueDiffOn_upperHalfSpace
      ((contDiff_seeleyExtension hf).contDiffAt.of_le (by exact_mod_cast hm)) hxs]

/-- **Derivatives of Seeley's extension.** At a negative time, the `m`-th derivative of the
extension of a function `Cⁿ` on the closed upper half-space, with `m ≤ n`, is the `aₖ`-weighted
sum of the `m`-th derivatives of the cut-off input at the reflected points, precomposed with the
dilations by `-2ᵏ`. -/
theorem iteratedFDeriv_seeleyExtension_of_neg [CompleteSpace F] {n : ℕ∞} {f : ℝ × E → F}
    (hf : ContDiffOn ℝ n f (upperHalfSpace E)) {x : ℝ × E} (hx : x.1 < 0) {m : ℕ}
    (hm : (m : ℕ∞) ≤ n) :
    iteratedFDeriv ℝ m (seeleyExtension f) x = ∑' k, seeleyCoeff k •
      (iteratedFDerivWithin ℝ m (seeleyCutoff f) (upperHalfSpace E)
        (timeScale (-2 ^ k) x)).compContinuousLinearMap fun _ ↦ timeScale (-2 ^ k) := by
  have hopen : IsOpen {z : ℝ × E | z.1 < 0} := isOpen_lt continuous_fst continuous_const
  have hev : seeleyExtension f =ᶠ[𝓝 x]
      fun z ↦ ∑' k, seeleyCoeff k • seeleyCutoff f (timeScale (-2 ^ k) z) :=
    (hopen.eventually_mem hx).mono fun z hz ↦ by
      simp only [seeleyExtension_of_neg f hz, seeleyCutoff_timeScale]
  have hlow : lowerHalfSpace E ∈ 𝓝 x :=
    mem_of_superset (hopen.mem_nhds hx) fun z hz ↦ mem_lowerHalfSpace.mpr (le_of_lt hz)
  have hq := hasFTaylorSeriesUpToOn_tsum_seeleyCoeff_smul_seeleyCutoff hf
  rw [(hev.iteratedFDeriv ℝ m).eq_of_nhds, ← iteratedFDerivWithin_univ,
    ← iteratedFDerivWithin_congr_set (eventuallyEqSet_univ.mpr hlow),
    ← hq.eq_iteratedFDerivWithin_of_uniqueDiffOn (by exact_mod_cast hm)
      uniqueDiffOn_lowerHalfSpace (mem_of_mem_nhds hlow)]

/-- **Derivative estimates for Seeley's extension.** At a negative time, the `m`-th derivative of
the extension of a function `Cⁿ` on the closed upper half-space, with `m ≤ n`, is bounded by
`∑ₖ |aₖ| (2ᵏ) ^ m` times any bound on the `m`-th derivatives of the cut-off input on the closed
upper half-space. -/
theorem norm_iteratedFDeriv_seeleyExtension_le_of_neg [CompleteSpace F] {n : ℕ∞} {f : ℝ × E → F}
    (hf : ContDiffOn ℝ n f (upperHalfSpace E)) {x : ℝ × E} (hx : x.1 < 0) {m : ℕ}
    (hm : (m : ℕ∞) ≤ n) {C : ℝ}
    (hC : ∀ y ∈ upperHalfSpace E,
      ‖iteratedFDerivWithin ℝ m (seeleyCutoff f) (upperHalfSpace E) y‖ ≤ C) :
    ‖iteratedFDeriv ℝ m (seeleyExtension f) x‖ ≤
      (∑' k, |seeleyCoeff k| * ((2 : ℝ) ^ k) ^ m) * C := by
  rw [iteratedFDeriv_seeleyExtension_of_neg hf hx hm, ← tsum_mul_right]
  refine tsum_of_norm_bounded ((summable_abs_seeleyCoeff_mul_pow m).mul_right C).hasSum
    fun k ↦ (norm_seeleyCoeff_smul_compContinuousLinearMap_le _ k).trans ?_
  gcongr
  exact hC _ (timeScale_neg_two_pow_mem_upperHalfSpace k hx.le)

open Metric in
/-- **Local Seeley extension.** A function `Cⁿ` on the part of a neighbourhood `s` of `a` in the
closed upper half-space agrees, on the half-space near `a`, with a function `Cⁿ` on the whole space:
cut it off by a bump function supported near `a`, which makes it `Cⁿ` on the whole closed
half-space, and apply Seeley's extension. -/
theorem exists_contDiff_eqOn_upperHalfSpace [FiniteDimensional ℝ E] [CompleteSpace F] {n : ℕ∞}
    {f : ℝ × E → F} {a : ℝ × E} {s : Set (ℝ × E)}
    (hf : ContDiffOn ℝ n f (s ∩ upperHalfSpace E)) (hs : s ∈ 𝓝 a) :
    ∃ g : ℝ × E → F, ∃ r > 0, ball a r ⊆ s ∧
      ContDiff ℝ n g ∧ EqOn g f (ball a r ∩ upperHalfSpace E) := by
  obtain ⟨R, hR, hRs⟩ := nhds_basis_ball.mem_iff.mp hs
  let χ : ContDiffBump a := ⟨R / 4, R / 2, by positivity, by linarith⟩
  have hg : ContDiffOn ℝ n (fun y ↦ χ y • f y) (upperHalfSpace E) := by
    refine contDiffOn_of_locally_contDiffOn fun y _ ↦ ?_
    by_cases hy : y ∈ ball a R
    · refine ⟨ball a R, isOpen_ball, hy, ?_⟩
      exact χ.contDiff.contDiffOn.smul (hf.mono fun z hz ↦ ⟨hRs hz.2, hz.1⟩)
    · -- Outside the ball of radius `R` the cut-off function vanishes near `y`.
      have hy' : y ∉ closedBall a (R / 2) := fun h ↦
        hy (closedBall_subset_ball (by linarith) h)
      refine ⟨(closedBall a (R / 2))ᶜ, isClosed_closedBall.isOpen_compl, hy', ?_⟩
      refine (contDiffOn_const (c := (0 : F))).congr fun z hz ↦ ?_
      have hz' : R / 2 < dist z a := by simpa [mem_closedBall] using hz.2
      rw [χ.zero_of_le_dist hz'.le, zero_smul]
  refine ⟨seeleyExtension fun y ↦ χ y • f y, R / 4, by positivity,
    (ball_subset_ball (by linarith)).trans hRs, contDiff_seeleyExtension hg, fun y hy ↦ ?_⟩
  rw [seeleyExtension_eqOn_upperHalfSpace _ hy.2,
    χ.one_of_mem_closedBall (ball_subset_closedBall hy.1), one_smul]

/-! ### Extension from closed half-spaces and slabs -/

/-- **Seeley extension from a translated half-space.** A function `Cⁿ` on the closed half-space
`[a, ∞) × E` is the restriction of a function `Cⁿ` on the whole space. -/
theorem exists_contDiff_eqOn_Ici_prod [CompleteSpace F] {n : ℕ∞} {f : ℝ × E → F} {a : ℝ}
    (hf : ContDiffOn ℝ n f (Ici a ×ˢ univ)) :
    ∃ g : ℝ × E → F, ContDiff ℝ n g ∧ EqOn g f (Ici a ×ˢ univ) := by
  -- Translate the upper half-space onto `[a, ∞) × E`, extend there, and translate back.
  have hτ : ContDiff ℝ n fun w : ℝ × E ↦ (w.1 + a, w.2) :=
    (contDiff_fst.add contDiff_const).prodMk contDiff_snd
  have hfτ : ContDiffOn ℝ n (fun w : ℝ × E ↦ f (w.1 + a, w.2)) (upperHalfSpace E) :=
    hf.comp hτ.contDiffOn fun w hw ↦ ⟨by simpa using mem_upperHalfSpace.mp hw, mem_univ _⟩
  refine ⟨fun z ↦ seeleyExtension (fun w ↦ f (w.1 + a, w.2)) (z.1 - a, z.2),
    (contDiff_seeleyExtension hfτ).comp
      ((contDiff_fst.sub contDiff_const).prodMk contDiff_snd), fun z hz ↦
    (seeleyExtension_eqOn_upperHalfSpace _ (mem_upperHalfSpace.mpr (sub_nonneg.mpr hz.1))).trans
      (by simp)⟩

/-- **Seeley extension from a reflected half-space.** A function `Cⁿ` on the closed half-space
`(-∞, b] × E` is the restriction of a function `Cⁿ` on the whole space. -/
theorem exists_contDiff_eqOn_Iic_prod [CompleteSpace F] {n : ℕ∞} {f : ℝ × E → F} {b : ℝ}
    (hf : ContDiffOn ℝ n f (Iic b ×ˢ univ)) :
    ∃ g : ℝ × E → F, ContDiff ℝ n g ∧ EqOn g f (Iic b ×ˢ univ) := by
  -- The reflection `(t, x) ↦ (b - t, x)` exchanges the upper half-space and `(-∞, b] × E`.
  have hσ : ContDiff ℝ n fun w : ℝ × E ↦ (b - w.1, w.2) :=
    (contDiff_const.sub contDiff_fst).prodMk contDiff_snd
  have hfσ : ContDiffOn ℝ n (fun w : ℝ × E ↦ f (b - w.1, w.2)) (upperHalfSpace E) :=
    hf.comp hσ.contDiffOn fun w hw ↦ ⟨by simpa using mem_upperHalfSpace.mp hw, mem_univ _⟩
  refine ⟨fun z ↦ seeleyExtension (fun w ↦ f (b - w.1, w.2)) (b - z.1, z.2),
    (contDiff_seeleyExtension hfσ).comp hσ, fun z hz ↦
    (seeleyExtension_eqOn_upperHalfSpace _ (mem_upperHalfSpace.mpr (sub_nonneg.mpr hz.1))).trans
      (by simp)⟩

/-- **Seeley extension from a slab.** A function `Cⁿ` on the closed slab `[a, b] × E` is the
restriction of a function `Cⁿ` on the whole space. -/
theorem exists_contDiff_eqOn_Icc_prod [CompleteSpace F] {n : ℕ∞} {f : ℝ × E → F} {a b : ℝ}
    (hf : ContDiffOn ℝ n f (Icc a b ×ˢ univ)) :
    ∃ g : ℝ × E → F, ContDiff ℝ n g ∧ EqOn g f (Icc a b ×ˢ univ) := by
  rcases lt_trichotomy a b with hab | rfl | hab
  · -- A cutoff `χ` in time, equal to `1` near `a` and to `0` near `b`, splits `f` into `χ f`,
    -- which is `Cⁿ` on `[a, ∞) × E`, and `(1 - χ) f`, which is `Cⁿ` on `(-∞, b] × E`.
    set δ := (b - a) / 3 with hδ
    have hδpos : 0 < δ := by linarith
    set χ : ℝ → ℝ := fun t ↦ Real.smoothTransition ((a + 2 * δ - t) / δ)
    have hχ : ContDiff ℝ n χ :=
      Real.smoothTransition.contDiff.comp ((contDiff_const.sub contDiff_id).div_const δ)
    have hχ0 {t : ℝ} (ht : a + 2 * δ ≤ t) : χ t = 0 :=
      Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith) hδpos.le)
    have hχ1 {t : ℝ} (ht : t ≤ a + δ) : χ t = 1 :=
      Real.smoothTransition.one_of_one_le (by rw [le_div_iff₀ hδpos]; linarith)
    have hf₁ : ContDiffOn ℝ n (fun z : ℝ × E ↦ χ z.1 • f z) (Ici a ×ˢ univ) :=
      contDiffOn_smul_of_eqOn_zero (hχ.comp contDiff_fst).contDiffOn hf
        (isOpen_Ioi.prod isOpen_univ) (isOpen_Iio.prod isOpen_univ) (fun w hw ↦ hχ0 (le_of_lt hw.1))
        (fun w hw ↦ ⟨⟨hw.1.1, le_of_lt hw.2.1⟩, mem_univ _⟩) fun z _ ↦ (lt_or_ge z.1 b).symm.imp
          (fun h ↦ ⟨show a + 2 * δ < z.1 by linarith, mem_univ _⟩) fun h ↦ ⟨h, mem_univ _⟩
    have hf₂ : ContDiffOn ℝ n (fun z : ℝ × E ↦ (1 - χ z.1) • f z) (Iic b ×ˢ univ) :=
      contDiffOn_smul_of_eqOn_zero (contDiff_const.sub (hχ.comp contDiff_fst)).contDiffOn hf
        (isOpen_Iio.prod isOpen_univ) (isOpen_Ioi.prod isOpen_univ)
        (fun w hw ↦ by simp [hχ1 (le_of_lt hw.1)])
        (fun w hw ↦ ⟨⟨le_of_lt hw.2.1, hw.1.1⟩, mem_univ _⟩) fun z _ ↦ (lt_or_ge a z.1).symm.imp
          (fun h ↦ ⟨show z.1 < a + δ by linarith, mem_univ _⟩) fun h ↦ ⟨h, mem_univ _⟩
    obtain ⟨g₁, hg₁, hg₁f⟩ := exists_contDiff_eqOn_Ici_prod hf₁
    obtain ⟨g₂, hg₂, hg₂f⟩ := exists_contDiff_eqOn_Iic_prod hf₂
    refine ⟨g₁ + g₂, hg₁.add hg₂, fun z hz ↦ ?_⟩
    rw [Pi.add_apply, hg₁f ⟨hz.1.1, mem_univ _⟩, hg₂f ⟨hz.1.2, mem_univ _⟩, ← add_smul,
      add_sub_cancel, one_smul]
  · -- On a degenerate slab `{a} × E` the function is extended constantly in time.
    refine ⟨fun z ↦ f (a, z.2), contDiffOn_univ.mp (hf.comp
      (contDiff_const.prodMk contDiff_snd).contDiffOn fun _ _ ↦ ⟨left_mem_Icc.mpr le_rfl,
        mem_univ _⟩), fun z hz ↦ ?_⟩
    obtain ⟨t, x⟩ := z
    obtain rfl : t = a := le_antisymm hz.1.2 hz.1.1
    rfl
  · exact ⟨0, contDiff_const, fun z hz ↦ absurd (hz.1.1.trans hz.1.2) (not_le.mpr hab)⟩

/-- **Seeley extension from a slab, slab coordinate last.** A function `Cⁿ` on the closed slab
`E × [a, b]` is the restriction of a function `Cⁿ` on the whole space. -/
theorem exists_contDiff_eqOn_prod_Icc [CompleteSpace F] {n : ℕ∞} {f : E × ℝ → F} {a b : ℝ}
    (hf : ContDiffOn ℝ n f (univ ×ˢ Icc a b)) :
    ∃ g : E × ℝ → F, ContDiff ℝ n g ∧ EqOn g f (univ ×ˢ Icc a b) := by
  obtain ⟨g, hg, hgf⟩ := exists_contDiff_eqOn_Icc_prod (f := f ∘ Prod.swap)
    (hf.comp (contDiff_snd.prodMk contDiff_fst).contDiffOn (mapsTo_swap_prod _ _))
  exact ⟨g ∘ Prod.swap, hg.comp (contDiff_snd.prodMk contDiff_fst), fun z hz ↦
    hgf ⟨hz.2, mem_univ _⟩⟩

end TauCeti.HalfSpaceExtension

end
