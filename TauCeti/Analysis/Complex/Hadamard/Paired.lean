/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.GrowthOrder.Centered
public import TauCeti.Analysis.Complex.Hadamard.OriginZero
import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.Topology.MetricSpace.Algebra
import TauCeti.Algebra.Polynomial.Coeff.Basic
import TauCeti.Analysis.Analytic.Reflection
import TauCeti.Analysis.Calculus.Deriv.Polynomial
import TauCeti.Analysis.Calculus.LogDeriv
import TauCeti.Analysis.Complex.Basic
import TauCeti.Analysis.Complex.ExtractZeros
import TauCeti.Analysis.Complex.GrowthOrder.Zero.Summability
import TauCeti.Analysis.Complex.IteratedDeriv
import TauCeti.Topology.Algebra.InfiniteSum.Real

/-!
# Paired Hadamard factorization and positivity of derivatives

Let `f : ℂ → ℂ` be an entire function of order at most one (`TauCeti.IsCenteredOrderOne f`)
satisfying `f (-z) = δ * f z`, having every zero on the imaginary axis, and taking strictly
positive real values at all sufficiently large real arguments. Following Yun and Zhang
(*Shtukas and the Taylor expansion of L-functions*, Appendix B.1, Proposition B.1), this file
proves:

1. **Paired Hadamard factorization (`TauCeti.pairedHadamard_factorization`).** Writing `m` for the
   analytic order of `f` at `0`, the functional equation and eventual positivity automatically force
   `δ = (-1) ^ m`, and there exist `c > 0` and a nonnegative sequence `γ : ℕ → ℝ` with
   `∑ (γ n)⁻¹ ^ 2 < ∞` (using `0` entries to pad unused indices when the zero multiset is finite)
   such that
   `f z = c * z ^ m * ∏' n, (if γ n = 0 then 1 else 1 + z ^ 2 / (γ n) ^ 2)`
   with uniform convergence of the finite partial products on every compact subset of `ℂ`.

2. **Nonnegative real derivatives (`TauCeti.pairedHadamard_derivatives_nonnegative`).** Because each
   partial product is a real polynomial with nonnegative coefficients, locally uniform convergence
   of all iterated derivatives implies that `iteratedDeriv k f x` is real and nonnegative for every
   `k : ℕ` and every real `x ≥ 0` (including the Taylor coefficients at `x = 0`; vanishing of
   opposite-parity Taylor coefficients at `0` holds generally by
   `AnalyticAt.iteratedDeriv_eq_zero_of_reflection`).

3. **Strict derivative positivity for nonpolynomials
   (`TauCeti.pairedHadamard_derivatives_positive`).** When `f` is not a polynomial, infinitely many
   entries `γ n` are positive; every Taylor coefficient of degree `m + 2 * j` (`j ≥ 0`) is strictly
   positive (`TauCeti.pairedHadamard_iteratedDeriv_zero_pos`), and expanding `iteratedDeriv k f` in
   its global Taylor series about `0` shows that `(iteratedDeriv k f x).re > 0` for every `k : ℕ`
   and every real `x > 0`.

## Main results

* `TauCeti.pairedHadamard_factorization`: paired Hadamard product with uniform convergence on
  compact sets.
* `TauCeti.pairedHadamard_derivatives_nonnegative`: reality and nonnegativity of all iterated
  derivatives on `[0, ∞)`.
* `TauCeti.pairedHadamard_iteratedDeriv_zero_pos` and `TauCeti.pairedHadamard_derivatives_positive`:
  strict positivity of same-parity Taylor coefficients from degree `m` upward and of every iterated
  derivative on `(0, ∞)` when `f` is not a polynomial.

## References

* Z. Yun and W. Zhang, *Shtukas and the Taylor expansion of L-functions*, Ann. of Math. (2) **186**
  (2017), no. 3, 767–911, Appendix B.1, (B.3) and Proposition B.1, pp. 902–903.
-/

public section

open Complex Filter Metric Polynomial Topology
open scoped BigOperators

namespace TauCeti

/-! ### Algebraic and convergence helpers for paired quadratic factors -/

/-- Under totalized real inversion `(0 : ℝ)⁻¹ = 0`, the conditional paired factor
`if y = 0 then 1 else 1 + z ^ 2 / y ^ 2` equals `1 + ((y⁻¹ ^ 2 : ℝ) : ℂ) * z ^ 2`
unconditionally. -/
private theorem pairedFactor_eq_one_add_inv_sq_mul (y : ℝ) (z : ℂ) :
    (if y = 0 then (1 : ℂ) else 1 + z ^ 2 / (y : ℂ) ^ 2) =
      1 + (((y⁻¹ ^ 2 : ℝ) : ℂ)) * z ^ 2 := by
  by_cases hy : y = 0
  · simp [hy]
  · rw [ite_eq_right hy]
    push_cast
    rw [div_eq_inv_mul, inv_pow, mul_comm]

/-- Pairing opposite purely imaginary roots `±ρ` in the genus-one Weierstrass product cancels the
exponential factors and yields `(1 + z ^ 2 / (Im ρ) ^ 2) ^ d`. -/
private theorem weierstrassFactorOne_imag_pair {ρ : ℂ} (hre : ρ.re = 0) (d : ℕ) (z : ℂ) :
    weierstrassFactorOne (ρ⁻¹ * z) ^ d * weierstrassFactorOne ((-ρ)⁻¹ * z) ^ d =
      (1 + z ^ 2 / (ρ.im : ℂ) ^ 2) ^ d := by
  have hneg : (-ρ)⁻¹ * z = -(ρ⁻¹ * z) := by rw [inv_neg, neg_mul]
  have hρ_sq : ρ ^ 2 = -(ρ.im : ℂ) ^ 2 := by
    conv_lhs => rw [Complex.eq_im_mul_I_of_re_eq_zero hre]
    rw [mul_pow, I_sq, mul_neg_one]
  rw [hneg, ← mul_pow, weierstrassFactorOne_mul_neg]
  congr 1
  rw [mul_pow, inv_pow, ← div_eq_inv_mul, hρ_sq, div_neg, sub_neg_eq_add]

/-- Square-summability of `(γ n)⁻¹` yields uniform convergence on every compact set `K ⊆ ℂ` of the
paired quadratic infinite product. -/
private theorem hasProdUniformlyOn_pairedFactor {γ : ℕ → ℝ}
    (hsum : Summable (fun n : ℕ ↦ (γ n)⁻¹ ^ 2)) {K : Set ℂ} (hK : IsCompact K) :
    HasProdUniformlyOn
      (fun (n : ℕ) (z : ℂ) ↦ if γ n = 0 then (1 : ℂ) else 1 + z ^ 2 / (γ n : ℂ) ^ 2)
      (fun z : ℂ ↦ ∏' n : ℕ, if γ n = 0 then (1 : ℂ) else 1 + z ^ 2 / (γ n : ℂ) ^ 2) K := by
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn continuous_id.continuousOn
  set B : ℝ := max M 0
  have hu : Summable (fun n : ℕ ↦ B ^ 2 * (γ n)⁻¹ ^ 2) := hsum.mul_left (B ^ 2)
  have hbound : ∀ᶠ n : ℕ in cofinite, ∀ z ∈ K,
      ‖((((γ n)⁻¹ ^ 2 : ℝ) : ℂ)) * z ^ 2‖ ≤ B ^ 2 * (γ n)⁻¹ ^ 2 := by
    refine Eventually.of_forall fun n z hz ↦ ?_
    have hzB : ‖z‖ ≤ B := (hM z hz).trans (le_max_left M 0)
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg (sq_nonneg _)]
    calc (γ n)⁻¹ ^ 2 * ‖z‖ ^ 2 ≤ (γ n)⁻¹ ^ 2 * B ^ 2 := by gcongr
      _ = B ^ 2 * (γ n)⁻¹ ^ 2 := mul_comm _ _
  have hcts : ∀ n : ℕ, ContinuousOn (fun z : ℂ ↦ ((((γ n)⁻¹ ^ 2 : ℝ) : ℂ)) * z ^ 2) K :=
    fun _ ↦ by fun_prop
  have hp := Summable.hasProdUniformlyOn_one_add hK hu hbound hcts
  have hcongr : ∀ n z, (if γ n = 0 then (1 : ℂ) else 1 + z ^ 2 / (γ n : ℂ) ^ 2) =
      1 + ((((γ n)⁻¹ ^ 2 : ℝ) : ℂ)) * z ^ 2 := fun n ↦ pairedFactor_eq_one_add_inv_sq_mul (γ n)
  simpa only [← hcongr] using hp

/-- Pointwise convergence of the paired quadratic infinite product at any `z : ℂ`. -/
private theorem hasProd_pairedFactor {γ : ℕ → ℝ}
    (hsum : Summable (fun n : ℕ ↦ (γ n)⁻¹ ^ 2)) (z : ℂ) :
    HasProd (fun n : ℕ ↦ if γ n = 0 then (1 : ℂ) else 1 + z ^ 2 / (γ n : ℂ) ^ 2)
      (∏' n : ℕ, if γ n = 0 then (1 : ℂ) else 1 + z ^ 2 / (γ n : ℂ) ^ 2) :=
  (hasProdUniformlyOn_pairedFactor hsum (isCompact_singleton (x := z))).hasProd
    (Set.mem_singleton z)

/-- At any real point `x : ℝ`, the paired infinite product has zero imaginary part and real part at
least `1`. -/
private theorem pairedProduct_ofReal_im_eq_zero_and_one_le_re {γ : ℕ → ℝ}
    (hsum : Summable (fun n : ℕ ↦ (γ n)⁻¹ ^ 2)) (x : ℝ) :
    (∏' n : ℕ, if γ n = 0 then (1 : ℂ) else 1 + (x : ℂ) ^ 2 / (γ n : ℂ) ^ 2).im = 0 ∧
      1 ≤ (∏' n : ℕ, if γ n = 0 then (1 : ℂ) else 1 + (x : ℂ) ^ 2 / (γ n : ℂ) ^ 2).re := by
  have hhp := hasProd_pairedFactor hsum (x : ℂ)
  have hreal (s : Finset ℕ) :
      (∏ n ∈ s, if γ n = 0 then (1 : ℂ) else 1 + (x : ℂ) ^ 2 / (γ n : ℂ) ^ 2) =
        (((∏ n ∈ s, (1 + (γ n)⁻¹ ^ 2 * x ^ 2) : ℝ) : ℂ)) := by
    rw [Complex.ofReal_prod]
    refine Finset.prod_congr rfl fun n _ ↦ ?_
    rw [pairedFactor_eq_one_add_inv_sq_mul]
    push_cast
    ring
  have him : Tendsto
      (fun s : Finset ℕ ↦
        (∏ n ∈ s, if γ n = 0 then (1 : ℂ) else 1 + (x : ℂ) ^ 2 / (γ n : ℂ) ^ 2).im)
      atTop (𝓝 0) := by
    refine tendsto_const_nhds.congr fun s ↦ ?_
    rw [hreal s, ofReal_im]
  have hre_ge : ∀ s : Finset ℕ,
      1 ≤ (∏ n ∈ s, if γ n = 0 then (1 : ℂ) else 1 + (x : ℂ) ^ 2 / (γ n : ℂ) ^ 2).re := by
    intro s
    rw [hreal s, ofReal_re]
    exact Finset.one_le_prod₀ fun n _ ↦ le_add_of_nonneg_right (by positivity)
  exact ⟨tendsto_nhds_unique (Complex.continuous_im.continuousAt.tendsto.comp hhp) him,
    ge_of_tendsto (Complex.continuous_re.continuousAt.tendsto.comp hhp)
      (Eventually.of_forall hre_ge)⟩

/-! ### Pairing the divisor product of an even entire function with imaginary zeros -/

private theorem re_eq_zero_of_mem_divisor_support {g : ℂ → ℂ} (hg : Differentiable ℂ g)
    (hzeros : ∀ z : ℂ, g z = 0 → z.re = 0) {ρ : ℂ}
    (hρ : ρ ∈ (MeromorphicOn.divisor g Set.univ).support) : ρ.re = 0 :=
  hzeros ρ ((hg.analyticAt ρ).eq_zero_of_mem_divisor_support hρ)

/-- Grouping each upper-half-plane zero `ρ` (`Im ρ > 0`) of an even entire function `g` with `-ρ`
rewrites `divisorProductOne g z` as a product over `{ρ ∈ d.support | 0 < ρ.im}`. -/
private theorem divisorProductOne_eq_tprod_im_pos {g : ℂ → ℂ} (hg : Differentiable ℂ g)
    (hg0 : g 0 ≠ 0) (heven : g.Even) (hzeros : ∀ z : ℂ, g z = 0 → z.re = 0)
    (hsum : Summable (fun ρ : (MeromorphicOn.divisor g Set.univ).support ↦
      ((MeromorphicOn.divisor g Set.univ ρ).toNat : ℝ) * ‖(ρ : ℂ)⁻¹‖ ^ 2))
    (z : ℂ) :
    divisorProductOne g z =
      ∏' ρ : {ρ : ℂ | ρ ∈ (MeromorphicOn.divisor g Set.univ).support ∧ 0 < ρ.im},
        (1 + z ^ 2 / (ρ.1.im : ℂ) ^ 2) ^ (MeromorphicOn.divisor g Set.univ ρ.1).toNat := by
  have h0_notMem : (0 : ℂ) ∉ (MeromorphicOn.divisor g Set.univ).support :=
    (hg.analyticAt 0).notMem_divisor_support_of_ne_zero hg0
  have hsupp_re {ρ : ℂ} (hρ : ρ ∈ (MeromorphicOn.divisor g Set.univ).support) : ρ.re = 0 :=
    re_eq_zero_of_mem_divisor_support hg hzeros hρ
  have hdiv_neg (ρ : ℂ) :
      MeromorphicOn.divisor g Set.univ (-ρ) = MeromorphicOn.divisor g Set.univ ρ :=
    (Complex.analyticOnNhd_univ_iff_differentiable.mpr hg).divisor_neg_eq_of_even heven ρ
  rw [divisorProductOne_def]
  generalize MeromorphicOn.divisor g Set.univ = d at h0_notMem hsupp_re hdiv_neg hsum ⊢
  have hsupp_im_ne {ρ : ℂ} (hρ : ρ ∈ d.support) : ρ.im ≠ 0 := fun him ↦ by
    have hρ0 : ρ = 0 := Complex.ext (by simp [hsupp_re hρ]) (by simp [him])
    exact h0_notMem (hρ0 ▸ hρ)
  have hsupp_neg {ρ : ℂ} (hρ : ρ ∈ d.support) : -ρ ∈ d.support := by
    rw [Function.mem_support, hdiv_neg]
    exact hρ
  let Spos : Set ℂ := {ρ : ℂ | ρ ∈ d.support ∧ 0 < ρ.im}
  let e : (Σ _ : Spos, Bool) ≃ d.support :=
    { toFun := fun ⟨ρ, b⟩ ↦ if b then ⟨ρ.1, ρ.2.1⟩ else ⟨-ρ.1, hsupp_neg ρ.2.1⟩
      invFun := fun σ ↦
        if h : 0 < (σ : ℂ).im then ⟨⟨σ.1, σ.2, h⟩, true⟩
        else ⟨⟨-σ.1, hsupp_neg σ.2, by
          rw [neg_im]; linarith [lt_of_le_of_ne (not_lt.mp h) (hsupp_im_ne σ.2)]⟩, false⟩
      left_inv := fun ⟨ρ, b⟩ ↦ by
        cases b
        · simpa using ρ.2.2.le
        · simp [ρ.2.2]
      right_inv := fun σ ↦ by by_cases h : 0 < (σ : ℂ).im <;> simp [h] }
  let F : d.support → ℂ := fun σ ↦ weierstrassFactorOne ((σ : ℂ)⁻¹ * z) ^ (d σ).toNat
  have hF_mult : Multipliable F :=
    ((hasProdLocallyUniformlyOn_weierstrassFactorOne_pow (fun σ : d.support ↦ (σ : ℂ)⁻¹)
      (fun σ ↦ (d σ).toNat) hsum).hasProd (Set.mem_univ z)).multipliable
  calc (∏' σ : d.support, F σ)
      = ∏' p : Σ _ : Spos, Bool, F (e p) := (e.tprod_eq F).symm
    _ = ∏' ρ : Spos, ∏' b : Bool, F (e ⟨ρ, b⟩) :=
        Multipliable.tprod_sigma' (fun _ ↦ Multipliable.of_finite) (e.multipliable_iff.mpr hF_mult)
    _ = ∏' ρ : Spos, (1 + z ^ 2 / (ρ.1.im : ℂ) ^ 2) ^ (d ρ.1).toNat := by
        refine tprod_congr fun ρ ↦ ?_
        rw [tprod_fintype, Fintype.prod_bool]
        simp only [F, e, Equiv.coe_fn_mk, ↓reduceIte, Bool.false_eq_true, hdiv_neg]
        exact weierstrassFactorOne_imag_pair (hsupp_re ρ.2.1) (d ρ.1).toNat z

/-- Any product `∏' i : α, (1 + z ^ 2 / (y i) ^ 2) ^ (m i)` with `0 < y i` and
`∑' i, m i * (y i)⁻¹ ^ 2 < ∞` can be flattened into an `ℕ`-indexed paired product padded by `0`. -/
private theorem exists_nat_seq_tprod_pairedFactor {α : Type*} {y : α → ℝ} {m : α → ℕ}
    (hy : ∀ i, 0 < y i) (hsum : Summable (fun i ↦ (m i : ℝ) * (y i)⁻¹ ^ 2)) :
    ∃ γ : ℕ → ℝ, (∀ n, 0 ≤ γ n) ∧ Summable (fun n ↦ (γ n)⁻¹ ^ 2) ∧
      ∀ z : ℂ, (∏' i : α, (1 + z ^ 2 / (y i : ℂ) ^ 2) ^ m i) =
        ∏' n : ℕ, if γ n = 0 then (1 : ℂ) else 1 + z ^ 2 / (γ n : ℂ) ^ 2 := by
  let ι := Σ i : α, Fin (m i)
  have hι_sum : Summable (fun p : ι ↦ (y p.1)⁻¹ ^ 2) :=
    (summable_sigma_fin_iff (fun i ↦ sq_nonneg (y i)⁻¹) m).mpr hsum
  have hcount_ι : Countable ι := by
    rw [← Set.countable_univ_iff]
    exact hι_sum.countable_support.mono fun p _ ↦ pow_ne_zero 2 (inv_ne_zero (hy p.1).ne')
  obtain ⟨emb, hemb⟩ := Countable.exists_injective_nat ι
  let γ : ℕ → ℝ := Function.extend emb (fun p : ι ↦ y p.1) 0
  have hγ_nonneg (n : ℕ) : 0 ≤ γ n := by
    by_cases hn : ∃ p : ι, emb p = n
    · obtain ⟨p, rfl⟩ := hn
      dsimp only [γ]
      rw [hemb.extend_apply]
      exact (hy p.1).le
    · dsimp only [γ]
      rw [Function.extend_apply' _ _ _ hn]
      exact le_rfl
  have hγ_inv_eq : (fun n : ℕ ↦ (γ n)⁻¹ ^ 2) =
      Function.extend emb (fun p : ι ↦ (y p.1)⁻¹ ^ 2) 0 := by
    ext n
    by_cases hn : ∃ p : ι, emb p = n
    · obtain ⟨p, rfl⟩ := hn; simp only [γ, hemb.extend_apply]
    · simp only [γ, Function.extend_apply' _ _ _ hn, Pi.zero_apply, inv_zero,
        zero_pow two_ne_zero]
  have hγ_sum : Summable (fun n : ℕ ↦ (γ n)⁻¹ ^ 2) := by
    rw [hγ_inv_eq]
    exact (summable_extend_zero hemb).mpr hι_sum
  refine ⟨γ, hγ_nonneg, hγ_sum, fun z ↦ ?_⟩
  have hfactor_ext :
      (fun n : ℕ ↦ if γ n = 0 then (1 : ℂ) else 1 + z ^ 2 / (γ n : ℂ) ^ 2) =
        Function.extend emb (fun p : ι ↦ 1 + z ^ 2 / (y p.1 : ℂ) ^ 2) 1 := by
    ext n
    by_cases hn : ∃ p : ι, emb p = n
    · obtain ⟨p, rfl⟩ := hn
      simp only [γ, hemb.extend_apply, ite_eq_right_iff]
      exact fun hy0 ↦ absurd hy0 (hy p.1).ne'
    · simp only [γ, Function.extend_apply' _ _ _ hn, Pi.zero_apply, ↓reduceIte, Pi.one_apply]
  have hmult_nat : Multipliable
      (fun n : ℕ ↦ if γ n = 0 then (1 : ℂ) else 1 + z ^ 2 / (γ n : ℂ) ^ 2) :=
    (hasProd_pairedFactor hγ_sum z).multipliable
  rw [hfactor_ext] at hmult_nat
  have hmult_ι : Multipliable (fun p : ι ↦ (1 : ℂ) + z ^ 2 / (y p.1 : ℂ) ^ 2) :=
    (multipliable_extend_one hemb).mp hmult_nat
  rw [hfactor_ext, tprod_extend_one hemb,
    Multipliable.tprod_sigma' (fun _ ↦ Multipliable.of_finite) hmult_ι]
  simp only [tprod_fintype, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- Every entire even function `g` with `g 0 ≠ 0`, zeros on the imaginary axis, and inverse-square
summable divisor has `divisorProductOne g` represented by a nonnegative sequence `γ : ℕ → ℝ` with
`Summable (fun n ↦ (γ n)⁻¹ ^ 2)`. -/
private theorem exists_paired_seq_divisorProductOne {g : ℂ → ℂ} (hg : Differentiable ℂ g)
    (hg0 : g 0 ≠ 0) (heven : g.Even) (hzeros : ∀ z : ℂ, g z = 0 → z.re = 0)
    (hsum : Summable (fun ρ : (MeromorphicOn.divisor g Set.univ).support ↦
      ((MeromorphicOn.divisor g Set.univ ρ).toNat : ℝ) * ‖(ρ : ℂ)⁻¹‖ ^ 2)) :
    ∃ γ : ℕ → ℝ, (∀ n, 0 ≤ γ n) ∧ Summable (fun n ↦ (γ n)⁻¹ ^ 2) ∧
      ∀ z : ℂ, divisorProductOne g z =
        ∏' n : ℕ, if γ n = 0 then (1 : ℂ) else 1 + z ^ 2 / (γ n : ℂ) ^ 2 := by
  have hprod_pos := divisorProductOne_eq_tprod_im_pos hg hg0 heven hzeros hsum
  have hsupp_re {ρ : ℂ} (hρ : ρ ∈ (MeromorphicOn.divisor g Set.univ).support) : ρ.re = 0 :=
    re_eq_zero_of_mem_divisor_support hg hzeros hρ
  generalize MeromorphicOn.divisor g Set.univ = d at hprod_pos hsupp_re hsum
  let Spos : Set ℂ := {ρ : ℂ | ρ ∈ d.support ∧ 0 < ρ.im}
  let incl : Spos → d.support := fun ρ ↦ ⟨ρ.1, ρ.2.1⟩
  have hincl : Function.Injective incl :=
    fun _ _ hrt ↦ Subtype.ext (congrArg (Subtype.val : d.support → ℂ) hrt)
  have hSpos_sum : Summable (fun ρ : Spos ↦ ((d ρ.1).toNat : ℝ) * (ρ.1.im)⁻¹ ^ 2) := by
    refine (hsum.comp_injective hincl).congr fun ρ ↦ ?_
    have hnorm : ‖(ρ.1)⁻¹‖ = (ρ.1.im)⁻¹ := by
      conv_lhs => rw [norm_inv, Complex.eq_im_mul_I_of_re_eq_zero (hsupp_re ρ.2.1)]
      rw [norm_mul, norm_I, mul_one, Complex.norm_real, Real.norm_of_nonneg ρ.2.2.le]
    dsimp only [Function.comp_apply, incl]
    rw [hnorm]
  obtain ⟨γ, hγ_nonneg, hγ_sum, hγ_prod⟩ :=
    exists_nat_seq_tprod_pairedFactor (fun ρ : Spos ↦ ρ.2.2) hSpos_sum
  exact ⟨γ, hγ_nonneg, hγ_sum, fun z ↦ (hprod_pos z).trans (hγ_prod z)⟩

/-! ### The paired Hadamard factorization theorem -/

variable {f : ℂ → ℂ} {δ : ℂ}

/-- Evaluating `f z = a * z ^ m * ∏' n, ...` at `x₀ = max R 1 > 0` shows that eventual real
positivity of `f` forces the leading constant `a` to be real and strictly positive. -/
private theorem im_eq_zero_and_re_pos_of_eq_mul_pow_pairedFactor {a : ℂ} {m : ℕ} {γ : ℕ → ℝ}
    (hsum : Summable (fun n ↦ (γ n)⁻¹ ^ 2))
    (hf_eq : ∀ z : ℂ, f z = a * z ^ m *
      ∏' n : ℕ, if γ n = 0 then (1 : ℂ) else 1 + z ^ 2 / (γ n : ℂ) ^ 2)
    (hpositive : ∃ R : ℝ, ∀ x : ℝ, R ≤ x → (f (x : ℂ)).im = 0 ∧ 0 < (f (x : ℂ)).re) :
    a.im = 0 ∧ 0 < a.re := by
  obtain ⟨R, hR⟩ := hpositive
  set x₀ : ℝ := max R 1
  obtain ⟨hfx_im, hfx_re⟩ := hR x₀ (le_max_left R 1)
  obtain ⟨hP_im, hP_re⟩ := pairedProduct_ofReal_im_eq_zero_and_one_le_re hsum x₀
  set P₀ : ℂ :=
    ∏' n : ℕ, if γ n = 0 then (1 : ℂ) else 1 + (x₀ : ℂ) ^ 2 / (γ n : ℂ) ^ 2 with hP₀_def
  have hK_pos : 0 < x₀ ^ m * P₀.re :=
    mul_pos (pow_pos (lt_of_lt_of_le zero_lt_one (le_max_right R 1)) m) (zero_lt_one.trans_le hP_re)
  have hP_coe : P₀ = (P₀.re : ℂ) := Complex.ext rfl hP_im
  have hfx_eval : f (x₀ : ℂ) = a * (((x₀ ^ m * P₀.re : ℝ) : ℂ)) := by
    conv_lhs => rw [hf_eq (x₀ : ℂ), ← hP₀_def, hP_coe]
    push_cast
    ring
  have ha_im : a.im = 0 := by
    have him := congrArg Complex.im hfx_eval
    rw [hfx_im, im_mul_ofReal] at him
    exact (mul_eq_zero.mp him.symm).resolve_right hK_pos.ne'
  have ha_re : 0 < a.re := by
    have hre := congrArg Complex.re hfx_eval
    rw [re_mul_ofReal] at hre
    exact pos_of_mul_pos_left (hre ▸ hfx_re) hK_pos.le
  exact ⟨ha_im, ha_re⟩

/-- Multiplying the compactly uniformly convergent paired partial products by `a * z ^ m` preserves
uniform convergence on any compact set `K ⊆ ℂ`. -/
private theorem tendstoUniformlyOn_mul_pow_pairedFactor (a : ℂ) (m : ℕ) {γ : ℕ → ℝ}
    (hsum : Summable (fun n ↦ (γ n)⁻¹ ^ 2)) {K : Set ℂ} (hK : IsCompact K) :
    TendstoUniformlyOn
      (fun (s : Finset ℕ) (z : ℂ) ↦ a * z ^ m *
        ∏ n ∈ s, if γ n = 0 then (1 : ℂ) else 1 + z ^ 2 / (γ n : ℂ) ^ 2)
      (fun z : ℂ ↦ a * z ^ m *
        ∏' n : ℕ, if γ n = 0 then (1 : ℂ) else 1 + z ^ 2 / (γ n : ℂ) ^ 2)
      atTop K := by
  have hp := (hasProdUniformlyOn_pairedFactor hsum hK).tendstoUniformlyOn
  have hp_cts : ContinuousOn
      (fun z : ℂ ↦ ∏' n : ℕ, if γ n = 0 then (1 : ℂ) else 1 + z ^ 2 / (γ n : ℂ) ^ 2) K :=
    hp.continuousOn ((Eventually.of_forall fun s : Finset ℕ ↦
      continuousOn_finsetProd (s := s) fun n _ ↦ by
        simp_rw [pairedFactor_eq_one_add_inv_sq_mul]; fun_prop).frequently)
  have hconst : TendstoLocallyUniformlyOn
      (fun (_ : Finset ℕ) (z : ℂ) ↦ a * z ^ m)
      (fun z : ℂ ↦ a * z ^ m) atTop K := by
    rw [tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hK,
      Metric.tendstoUniformlyOn_iff]
    exact fun ε hε ↦ Eventually.of_forall fun _ _ _ ↦ by simpa using hε
  exact (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hK).mp
    (hconst.fun_mul₀ hp.tendstoLocallyUniformlyOn (by fun_prop) hp_cts)

/-- Internal form of `pairedHadamard_factorization` pinning `m = (analyticOrderAt f 0).toNat`. -/
private theorem exists_analyticOrderAt_pairedHadamard_factorization
    (hf : IsCenteredOrderOne f)
    (hparity : ∀ z, f (-z) = δ * f z)
    (hzeros : ∀ z, f z = 0 → z.re = 0)
    (hpositive : ∃ R : ℝ, ∀ x : ℝ, R ≤ x → (f (x : ℂ)).im = 0 ∧ 0 < (f (x : ℂ)).re) :
    ∃ (c : ℝ) (γ : ℕ → ℝ), 0 < c ∧
      (∀ n, 0 ≤ γ n) ∧ Summable (fun n ↦ (γ n)⁻¹ ^ 2) ∧
      δ = (-1 : ℂ) ^ (analyticOrderAt f 0).toNat ∧
      (∀ z : ℂ, Multipliable (fun n ↦
        if γ n = 0 then (1 : ℂ) else 1 + z ^ 2 / (γ n : ℂ) ^ 2)) ∧
      (∀ z : ℂ, f z = (c : ℂ) * z ^ (analyticOrderAt f 0).toNat * ∏' n,
        if γ n = 0 then (1 : ℂ) else 1 + z ^ 2 / (γ n : ℂ) ^ 2) ∧
      (∀ K : Set ℂ, IsCompact K → TendstoUniformlyOn
        (fun (s : Finset ℕ) (z : ℂ) ↦ (c : ℂ) * z ^ (analyticOrderAt f 0).toNat *
          ∏ n ∈ s, if γ n = 0 then (1 : ℂ) else 1 + z ^ 2 / (γ n : ℂ) ^ 2)
        f Filter.atTop K) := by
  have hf_ne_zero : f ≠ 0 := by
    obtain ⟨R, hR⟩ := hpositive
    exact fun h0 ↦ lt_irrefl 0 (by simpa [h0] using (hR R le_rfl).2)
  set m : ℕ := (analyticOrderAt f 0).toNat
  obtain ⟨g, hg_diff, hg0, _, hfg⟩ := hf.differentiable.exists_eq_pow_mul hf_ne_zero
  obtain ⟨hδ_eq, hg_even⟩ :=
    eq_neg_one_pow_and_even_of_eq_pow_mul hfg hparity hg_diff.continuous.continuousAt hg0
  have hg_ord : OrderLE g 1 := hf.orderLE_one.of_eq_pow_mul hfg
  obtain ⟨a, ha_exp, hg_had⟩ := hg_ord.exists_eq_cexp_mul_divisorProductOne hg_diff hg0
  have hg_prod (z : ℂ) : g z = g 0 * divisorProductOne g z := by
    rw [hg_had z, hg_even.logDeriv_zero, zero_mul, add_zero, ha_exp]
  have hg_zeros (z : ℂ) (hgz : g z = 0) : z.re = 0 := hzeros z (by rw [hfg z, hgz, mul_zero])
  obtain ⟨γ, hγ_nonneg, hγ_sum, hdiv_eq⟩ := exists_paired_seq_divisorProductOne hg_diff hg0 hg_even
    hg_zeros (hg_ord.summable_divisor_toNat_mul_norm_inv_sq hg_diff (by norm_num))
  have hf_eq_g0 (z : ℂ) :
      f z = g 0 * z ^ m * ∏' n : ℕ, if γ n = 0 then (1 : ℂ) else 1 + z ^ 2 / (γ n : ℂ) ^ 2 := by
    rw [hfg z, hg_prod z, hdiv_eq z]; ring
  obtain ⟨hg0_im, hg0_re_pos⟩ :=
    im_eq_zero_and_re_pos_of_eq_mul_pow_pairedFactor hγ_sum hf_eq_g0 hpositive
  have hc_coe : (((g 0).re : ℝ) : ℂ) = g 0 := Complex.ext rfl hg0_im.symm
  have hf_eq_c (z : ℂ) : f z = (((g 0).re : ℝ) : ℂ) * z ^ m *
      ∏' n : ℕ, if γ n = 0 then (1 : ℂ) else 1 + z ^ 2 / (γ n : ℂ) ^ 2 :=
    hc_coe.symm ▸ hf_eq_g0 z
  exact ⟨(g 0).re, γ, hg0_re_pos, hγ_nonneg, hγ_sum, hδ_eq,
    fun z ↦ (hasProd_pairedFactor hγ_sum z).multipliable, hf_eq_c,
    fun K hK ↦ (tendstoUniformlyOn_mul_pow_pairedFactor _ m hγ_sum hK).congr_right
      fun z _ ↦ (hf_eq_c z).symm⟩

/-- **The paired Hadamard factorization theorem.** An entire function `f` satisfying
`IsCenteredOrderOne f`, `f (-z) = δ * f z`, with all zeros on the imaginary axis and strictly
positive real values for large positive reals, admits a locally uniformly convergent factorization
`f z = c * z ^ m * ∏' n, (1 + z ^ 2 / γ_n ^ 2)` (with `0` entries of `γ` encoding unused indices
when the zero multiset is finite), `c > 0`, and `δ = (-1) ^ m`. Note that `δ ∈ {1, -1}` does not
need to be assumed separately: eventual positivity implies `f ≠ 0`, so `f (-z) = δ * f z`
automatically forces `δ = (-1) ^ m` with `m = (analyticOrderAt f 0).toNat`. -/
theorem pairedHadamard_factorization
    (hf : IsCenteredOrderOne f)
    (hparity : ∀ z, f (-z) = δ * f z)
    (hzeros : ∀ z, f z = 0 → z.re = 0)
    (hpositive : ∃ R : ℝ, ∀ x : ℝ, R ≤ x → (f (x : ℂ)).im = 0 ∧ 0 < (f (x : ℂ)).re) :
    ∃ (m : ℕ) (c : ℝ) (γ : ℕ → ℝ), 0 < c ∧
      (∀ n, 0 ≤ γ n) ∧ Summable (fun n ↦ (γ n)⁻¹ ^ 2) ∧
      δ = (-1 : ℂ) ^ m ∧
      (∀ z : ℂ, Multipliable (fun n ↦
        if γ n = 0 then (1 : ℂ) else 1 + z ^ 2 / (γ n : ℂ) ^ 2)) ∧
      (∀ z : ℂ, f z = (c : ℂ) * z ^ m * ∏' n,
        if γ n = 0 then (1 : ℂ) else 1 + z ^ 2 / (γ n : ℂ) ^ 2) ∧
      (∀ K : Set ℂ, IsCompact K → TendstoUniformlyOn
        (fun (s : Finset ℕ) (z : ℂ) ↦ (c : ℂ) * z ^ m *
          ∏ n ∈ s, if γ n = 0 then (1 : ℂ) else 1 + z ^ 2 / (γ n : ℂ) ^ 2)
        f Filter.atTop K) := by
  obtain ⟨c, γ, hc⟩ :=
    exists_analyticOrderAt_pairedHadamard_factorization hf hparity hzeros hpositive
  exact ⟨(analyticOrderAt f 0).toNat, c, γ, hc⟩

/-! ### Polynomial partial products and derivative positivity -/

/-- The finite partial-product real polynomial
`P_s(X) = c * X ^ m * ∏_{n ∈ s} (1 + (γ n)⁻¹ ^ 2 * X ^ 2)`. -/
private noncomputable def pairedPartialPoly (c : ℝ) (m : ℕ) (γ : ℕ → ℝ) (s : Finset ℕ) : ℝ[X] :=
  C c * X ^ m * ∏ n ∈ s, (1 + C ((γ n)⁻¹ ^ 2) * X ^ 2)

private theorem eval_map_pairedPartialPoly (c : ℝ) (m : ℕ) (γ : ℕ → ℝ) (s : Finset ℕ) (z : ℂ) :
    ((pairedPartialPoly c m γ s).map (algebraMap ℝ ℂ)).eval z =
      (c : ℂ) * z ^ m * ∏ n ∈ s, if γ n = 0 then (1 : ℂ) else 1 + z ^ 2 / (γ n : ℂ) ^ 2 := by
  rw [eval_map, ← aeval_def]
  simp only [pairedPartialPoly, map_mul, map_pow, aeval_C, aeval_X, Complex.coe_algebraMap,
    map_prod, map_add, map_one]
  congr 1
  refine Finset.prod_congr rfl fun n _ ↦ ?_
  rw [pairedFactor_eq_one_add_inv_sq_mul]
  push_cast
  ring

/-- Every coefficient of `pairedPartialPoly c m γ s` is nonnegative when `0 ≤ c`. -/
private theorem coeff_pairedPartialPoly_nonneg {c : ℝ} (hc : 0 ≤ c) (m : ℕ) (γ : ℕ → ℝ)
    (s : Finset ℕ) : ∀ d, 0 ≤ (pairedPartialPoly c m γ s).coeff d := by
  classical
  unfold pairedPartialPoly
  set Q : ℝ[X] := ∏ n ∈ s, (1 + C ((γ n)⁻¹ ^ 2) * X ^ 2) with hQ
  suffices hprod : ∀ d, 0 ≤ Q.coeff d by
    intro d
    rw [mul_assoc, coeff_C_mul, mul_comm (X ^ m)]
    by_cases hmd : m ≤ d
    · have hshift : (Q * X ^ m).coeff d = Q.coeff (d - m) := by
        conv_lhs => rw [← Nat.sub_add_cancel hmd]
        exact coeff_mul_X_pow Q m (d - m)
      rw [hshift]
      exact mul_nonneg hc (hprod (d - m))
    · rw [coeff_mul_X_pow' Q m d, ite_eq_right hmd, mul_zero]
  rw [hQ]
  clear hQ Q
  induction s using Finset.induction_on with
  | empty =>
    intro d
    by_cases hd : d = 0 <;> simp [coeff_one, hd]
  | insert n s hns ih =>
    intro d
    rw [Finset.prod_insert hns, mul_comm]
    exact (ih d).trans (coeff_le_coeff_mul_one_add_C_mul_X_pow ih (sq_nonneg _) 2 d)

/-- The coefficients of `pairedPartialPoly c m γ s` are monotone with respect to `s : Finset ℕ`. -/
private theorem coeff_pairedPartialPoly_mono {c : ℝ} (hc : 0 ≤ c) (m : ℕ) (γ : ℕ → ℝ)
    {t s : Finset ℕ} (hts : t ⊆ s) (d : ℕ) :
    (pairedPartialPoly c m γ t).coeff d ≤ (pairedPartialPoly c m γ s).coeff d := by
  classical
  rw [(Finset.union_sdiff_of_subset hts).symm]
  have hdisj : Disjoint t (s \ t) := Finset.disjoint_sdiff
  generalize s \ t = u at hdisj ⊢
  induction u using Finset.induction_on with
  | empty => simp
  | insert n u hnu ih =>
    have hdisj_u : Disjoint t u := hdisj.mono_right (Finset.subset_insert n u)
    have hn_not_tu : n ∉ t ∪ u := by
      simp only [Finset.mem_union, not_or]
      exact ⟨fun hnt ↦ Finset.disjoint_right.mp hdisj (Finset.mem_insert_self n u) hnt, hnu⟩
    have htu : t ∪ insert n u = insert n (t ∪ u) := by ext; simp
    rw [htu]
    have hstep : pairedPartialPoly c m γ (insert n (t ∪ u)) =
        pairedPartialPoly c m γ (t ∪ u) * (1 + C ((γ n)⁻¹ ^ 2) * X ^ 2) := by
      simp only [pairedPartialPoly, Finset.prod_insert hn_not_tu]; ring
    rw [hstep]
    exact (ih hdisj_u).trans
      (coeff_le_coeff_mul_one_add_C_mul_X_pow (coeff_pairedPartialPoly_nonneg hc m γ (t ∪ u))
        (sq_nonneg _) 2 d)

/-- If every `n ∈ t` has `γ n ≠ 0`, the degree-`(m + 2 * t.card)` coefficient of
`pairedPartialPoly c m γ t` is `c * ∏ n ∈ t, (γ n)⁻¹ ^ 2 > 0`. -/
private theorem coeff_pairedPartialPoly_top_pos {c : ℝ} (hc : 0 < c) (m : ℕ) (γ : ℕ → ℝ)
    (t : Finset ℕ) (ht : ∀ n ∈ t, γ n ≠ 0) :
    0 < (pairedPartialPoly c m γ t).coeff (m + 2 * t.card) := by
  classical
  suffices hprod : (∏ n ∈ t, (1 + C ((γ n)⁻¹ ^ 2) * X ^ 2 : ℝ[X])).natDegree = 2 * t.card ∧
      (∏ n ∈ t, (1 + C ((γ n)⁻¹ ^ 2) * X ^ 2 : ℝ[X])).coeff (2 * t.card) =
        ∏ n ∈ t, (γ n)⁻¹ ^ 2 by
    unfold pairedPartialPoly
    rw [mul_assoc, coeff_C_mul, mul_comm (X ^ m), add_comm m, coeff_mul_X_pow, hprod.2]
    exact mul_pos hc (Finset.prod_pos fun n hn ↦ sq_pos_of_ne_zero (inv_ne_zero (ht n hn)))
  induction t using Finset.induction_on with
  | empty => simp
  | insert n t hnt ih =>
    have hγn : (γ n)⁻¹ ^ 2 ≠ 0 :=
      pow_ne_zero 2 (inv_ne_zero (ht n (Finset.mem_insert_self n t)))
    obtain ⟨hdeg_t, hcoeff_t⟩ := ih (fun r hr ↦ ht r (Finset.mem_insert_of_mem hr))
    have hq_deg : (1 + C ((γ n)⁻¹ ^ 2) * X ^ 2 : ℝ[X]).natDegree = 2 := by
      rw [add_comm, natDegree_add_eq_left_of_natDegree_lt]
      · exact natDegree_C_mul_X_pow 2 ((γ n)⁻¹ ^ 2) hγn
      · rw [natDegree_one, natDegree_C_mul_X_pow 2 ((γ n)⁻¹ ^ 2) hγn]; omega
    have hq_lc : (1 + C ((γ n)⁻¹ ^ 2) * X ^ 2 : ℝ[X]).leadingCoeff = (γ n)⁻¹ ^ 2 := by
      rw [leadingCoeff, hq_deg, coeff_add, coeff_one, ite_eq_right (by omega), zero_add,
        coeff_C_mul, coeff_X_pow_self, mul_one]
    have ht_lc : (∏ r ∈ t, (1 + C ((γ r)⁻¹ ^ 2) * X ^ 2 : ℝ[X])).leadingCoeff =
        ∏ r ∈ t, (γ r)⁻¹ ^ 2 := by rw [leadingCoeff, hdeg_t, hcoeff_t]
    have ht_ne : (∏ r ∈ t, (1 + C ((γ r)⁻¹ ^ 2) * X ^ 2 : ℝ[X])) ≠ 0 :=
      leadingCoeff_ne_zero.mp (ht_lc.symm ▸ Finset.prod_ne_zero_iff.mpr fun r hr ↦
        pow_ne_zero 2 (inv_ne_zero (ht r (Finset.mem_insert_of_mem hr))))
    rw [Finset.prod_insert hnt, Finset.card_insert_of_notMem hnt]
    have hdeg_ins :
        ((1 + C ((γ n)⁻¹ ^ 2) * X ^ 2) *
          ∏ r ∈ t, (1 + C ((γ r)⁻¹ ^ 2) * X ^ 2 : ℝ[X])).natDegree = 2 * (t.card + 1) := by
      rw [natDegree_mul (leadingCoeff_ne_zero.mp (hq_lc.symm ▸ hγn)) ht_ne, hq_deg, hdeg_t]; ring
    exact ⟨hdeg_ins, by
      rw [← hdeg_ins, ← leadingCoeff, leadingCoeff_mul, hq_lc, ht_lc, Finset.prod_insert hnt]⟩

/-- Locally uniform convergence of the paired partial polynomials implies convergence of every
iterated derivative at every point `z : ℂ`. -/
private theorem tendsto_iteratedDeriv_pairedPartialPoly {c : ℝ} {m : ℕ} {γ : ℕ → ℝ}
    (hunif : ∀ K : Set ℂ, IsCompact K → TendstoUniformlyOn
      (fun (s : Finset ℕ) (z : ℂ) ↦ (c : ℂ) * z ^ m *
        ∏ n ∈ s, if γ n = 0 then (1 : ℂ) else 1 + z ^ 2 / (γ n : ℂ) ^ 2)
      f atTop K)
    (k : ℕ) (z : ℂ) :
    Tendsto
      (fun s : Finset ℕ ↦
        iteratedDeriv k (fun w : ℂ ↦ ((pairedPartialPoly c m γ s).map (algebraMap ℝ ℂ)).eval w) z)
      atTop (𝓝 (iteratedDeriv k f z)) := by
  have hloc : TendstoLocallyUniformlyOn
      (fun (s : Finset ℕ) (w : ℂ) ↦ ((pairedPartialPoly c m γ s).map (algebraMap ℝ ℂ)).eval w)
      f atTop Set.univ := by
    rw [tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_univ]
    intro K _ hK
    exact (hunif K hK).congr (Eventually.of_forall fun s w _ ↦
      (eval_map_pairedPartialPoly c m γ s w).symm)
  have hdiff : ∀ᶠ s : Finset ℕ in atTop, DifferentiableOn ℂ
      (fun w : ℂ ↦ ((pairedPartialPoly c m γ s).map (algebraMap ℝ ℂ)).eval w) Set.univ :=
    Eventually.of_forall fun s ↦ ((pairedPartialPoly c m γ s).map (algebraMap ℝ ℂ)).differentiableOn
  exact (hloc.iteratedDeriv hdiff isOpen_univ k).tendsto_at (Set.mem_univ z)

/-- **Nonnegative derivatives of the paired product.** Under the hypotheses of
`TauCeti.pairedHadamard_factorization`, every iterated derivative `iteratedDeriv k f x` at a
nonnegative real point `x ≥ 0` is real and nonnegative. -/
theorem pairedHadamard_derivatives_nonnegative
    (hf : IsCenteredOrderOne f)
    (hparity : ∀ z, f (-z) = δ * f z)
    (hzeros : ∀ z, f z = 0 → z.re = 0)
    (hpositive : ∃ R : ℝ, ∀ x : ℝ, R ≤ x → (f (x : ℂ)).im = 0 ∧ 0 < (f (x : ℂ)).re)
    (k : ℕ) (x : ℝ) (hx : 0 ≤ x) :
    (iteratedDeriv k f (x : ℂ)).im = 0 ∧ 0 ≤ (iteratedDeriv k f (x : ℂ)).re := by
  obtain ⟨m, c, γ, hc, _, _, _, _, _, hunif⟩ :=
    pairedHadamard_factorization hf hparity hzeros hpositive
  have htend := tendsto_iteratedDeriv_pairedPartialPoly hunif k (x : ℂ)
  have hreal_val (s : Finset ℕ) :
      iteratedDeriv k
        (fun w : ℂ ↦ ((pairedPartialPoly c m γ s).map (algebraMap ℝ ℂ)).eval w) (x : ℂ) =
        ((((Polynomial.derivative^[k] (pairedPartialPoly c m γ s)).eval x : ℝ) : ℂ)) := by
    rw [Polynomial.iteratedDeriv]
    dsimp only
    have hmap : Polynomial.derivative^[k] ((pairedPartialPoly c m γ s).map (algebraMap ℝ ℂ)) =
        (Polynomial.derivative^[k] (pairedPartialPoly c m γ s)).map (algebraMap ℝ ℂ) := by
      ext d
      simp [coeff_iterate_derivative, Complex.coe_algebraMap]
    have hx_alg : (x : ℂ) = algebraMap ℝ ℂ x := by simp [Complex.coe_algebraMap]
    rw [hmap, hx_alg, eval_map, eval₂_hom]
    simp [Complex.coe_algebraMap]
  have hval_nonneg (s : Finset ℕ) :
      0 ≤ (Polynomial.derivative^[k] (pairedPartialPoly c m γ s)).eval x := by
    rw [eval_eq_sum]
    refine Finset.sum_nonneg fun d _ ↦ ?_
    rw [coeff_iterate_derivative]
    exact mul_nonneg (nsmul_nonneg (coeff_pairedPartialPoly_nonneg hc.le m γ s (d + k)) _)
      (pow_nonneg hx d)
  have him : Tendsto
      (fun s : Finset ℕ ↦ (iteratedDeriv k
        (fun w : ℂ ↦ ((pairedPartialPoly c m γ s).map (algebraMap ℝ ℂ)).eval w) (x : ℂ)).im)
      atTop (𝓝 0) :=
    tendsto_const_nhds.congr fun s ↦ by rw [hreal_val s, ofReal_im]
  exact ⟨tendsto_nhds_unique (Complex.continuous_im.continuousAt.tendsto.comp htend) him,
    ge_of_tendsto (Complex.continuous_re.continuousAt.tendsto.comp htend)
      (Eventually.of_forall fun s ↦ by
        dsimp only [Function.comp_apply]
        rw [hreal_val s, ofReal_re]
        exact hval_nonneg s)⟩

/-- **Strict positivity of same-parity Taylor coefficients for nonpolynomial paired products.** If
`f` is not a polynomial, then for every `j : ℕ` the derivative of order
`(analyticOrderAt f 0).toNat + 2 * j` at the origin has strictly positive real part. -/
theorem pairedHadamard_iteratedDeriv_zero_pos
    (hf : IsCenteredOrderOne f)
    (hparity : ∀ z, f (-z) = δ * f z)
    (hzeros : ∀ z, f z = 0 → z.re = 0)
    (hpositive : ∃ R : ℝ, ∀ x : ℝ, R ≤ x → (f (x : ℂ)).im = 0 ∧ 0 < (f (x : ℂ)).re)
    (hnonpoly : ¬ ∃ P : Polynomial ℂ, ∀ z, f z = P.eval z)
    (j : ℕ) :
    0 < (iteratedDeriv ((analyticOrderAt f 0).toNat + 2 * j) f 0).re := by
  classical
  set m : ℕ := (analyticOrderAt f 0).toNat
  obtain ⟨c, γ, hc, _, _, _, _, hprod_eq, hunif⟩ :=
    exists_analyticOrderAt_pairedHadamard_factorization hf hparity hzeros hpositive
  have hinf : {n : ℕ | γ n ≠ 0}.Infinite := fun hfin ↦ hnonpoly
    ⟨(pairedPartialPoly c m γ hfin.toFinset).map (algebraMap ℝ ℂ), fun z ↦ by
      rw [eval_map_pairedPartialPoly, hprod_eq z]
      congr 1
      refine tprod_eq_prod fun n hn ↦ ?_
      have hγ0 : γ n = 0 := by
        by_contra hne
        exact hn (hfin.mem_toFinset.mpr hne)
      simp [hγ0]⟩
  obtain ⟨t, ht_sub, ht_card⟩ := hinf.exists_subset_card_eq j
  set N : ℕ := m + 2 * j
  have ht_pos : 0 < (pairedPartialPoly c m γ t).coeff N := by
    simpa only [N, ht_card] using coeff_pairedPartialPoly_top_pos hc m γ t (fun n hn ↦ ht_sub hn)
  have htend := tendsto_iteratedDeriv_pairedPartialPoly hunif N 0
  have heval_zero (s : Finset ℕ) :
      (iteratedDeriv N
        (fun w : ℂ ↦ ((pairedPartialPoly c m γ s).map (algebraMap ℝ ℂ)).eval w) 0).re =
        (N.factorial : ℝ) * (pairedPartialPoly c m γ s).coeff N := by
    rw [Polynomial.iteratedDeriv_eval_zero, coeff_map, Complex.coe_algebraMap]
    have hcast : (N.factorial : ℂ) * (((pairedPartialPoly c m γ s).coeff N : ℝ) : ℂ) =
        (((N.factorial : ℝ) * (pairedPartialPoly c m γ s).coeff N : ℝ) : ℂ) := by
      push_cast
      ring
    rw [hcast, ofReal_re]
  have hlow : (N.factorial : ℝ) * (pairedPartialPoly c m γ t).coeff N ≤
      (iteratedDeriv N f 0).re := by
    refine ge_of_tendsto (Complex.continuous_re.continuousAt.tendsto.comp htend) ?_
    filter_upwards [Filter.eventually_ge_atTop t] with s hts
    dsimp only [Function.comp_apply]
    rw [heval_zero s]
    exact mul_le_mul_of_nonneg_left (coeff_pairedPartialPoly_mono hc.le m γ hts N)
      (Nat.cast_nonneg _)
  exact (mul_pos (Nat.cast_pos.mpr N.factorial_pos) ht_pos).trans_le hlow

/-- **Strict positivity of derivatives for nonpolynomial paired Hadamard products.** Under the
paired Hadamard hypotheses, if `f` is not a polynomial, then `(iteratedDeriv k f x).re > 0` for
every `k : ℕ` and every strictly positive real `x > 0`. -/
theorem pairedHadamard_derivatives_positive
    (hf : IsCenteredOrderOne f)
    (hparity : ∀ z, f (-z) = δ * f z)
    (hzeros : ∀ z, f z = 0 → z.re = 0)
    (hpositive : ∃ R : ℝ, ∀ x : ℝ, R ≤ x → (f (x : ℂ)).im = 0 ∧ 0 < (f (x : ℂ)).re)
    (hnonpoly : ¬ ∃ P : Polynomial ℂ, ∀ z, f z = P.eval z)
    (k : ℕ) (x : ℝ) (hx : 0 < x) :
    0 < (iteratedDeriv k f (x : ℂ)).re := by
  have hk_entire : Differentiable ℂ (iteratedDeriv k f) := hf.differentiable.iteratedDeriv k
  have hts := Complex.hasSum_taylorSeries_of_entire hk_entire 0 (x : ℂ)
  have hiter_add (n : ℕ) : iteratedDeriv n (iteratedDeriv k f) 0 = iteratedDeriv (n + k) f 0 := by
    rw [iteratedDeriv_eq_iterate, iteratedDeriv_eq_iterate, iteratedDeriv_eq_iterate,
      ← Function.iterate_add_apply]
  have hre_sum : HasSum
      (fun n : ℕ ↦ (n.factorial : ℝ)⁻¹ * x ^ n * (iteratedDeriv (n + k) f 0).re)
      (iteratedDeriv k f (x : ℂ)).re := by
    refine (Complex.reCLM.hasSum hts).congr_fun fun n ↦ ?_
    dsimp only [Complex.reCLM_apply]
    rw [sub_zero, hiter_add n, smul_eq_mul, smul_eq_mul]
    have hcast : ((n.factorial : ℂ)⁻¹ * ((x : ℂ) ^ n * iteratedDeriv (n + k) f 0)) =
        ((((n.factorial : ℝ)⁻¹ * x ^ n : ℝ) : ℂ)) * iteratedDeriv (n + k) f 0 := by
      push_cast; ring
    rw [hcast, re_ofReal_mul]
  have hterm_nonneg (n : ℕ) :
      0 ≤ (n.factorial : ℝ)⁻¹ * x ^ n * (iteratedDeriv (n + k) f 0).re :=
    mul_nonneg (mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) (pow_nonneg hx.le n))
      (pairedHadamard_derivatives_nonnegative hf hparity hzeros hpositive (n + k) 0 le_rfl).2
  set n₀ : ℕ := (analyticOrderAt f 0).toNat + k
  have hn₀_add : n₀ + k = (analyticOrderAt f 0).toNat + 2 * k := by omega
  have hpos_coeff : 0 < (iteratedDeriv (n₀ + k) f 0).re :=
    hn₀_add.symm ▸ pairedHadamard_iteratedDeriv_zero_pos hf hparity hzeros hpositive hnonpoly k
  have hterm_pos : 0 < (n₀.factorial : ℝ)⁻¹ * x ^ n₀ * (iteratedDeriv (n₀ + k) f 0).re :=
    mul_pos (mul_pos (inv_pos.mpr (Nat.cast_pos.mpr n₀.factorial_pos)) (pow_pos hx n₀)) hpos_coeff
  have hle : (n₀.factorial : ℝ)⁻¹ * x ^ n₀ * (iteratedDeriv (n₀ + k) f 0).re ≤
      (iteratedDeriv k f (x : ℂ)).re := by
    simpa only [Finset.sum_singleton] using
      sum_le_hasSum ({n₀} : Finset ℕ) (fun n _ ↦ hterm_nonneg n) hre_sum
  exact hterm_pos.trans_le hle

/-! ### Examples -/

/-- `1 + z ^ 2` satisfies the paired Hadamard hypotheses with `δ = 1`, so all of its derivatives on
`[0, ∞)` are real and nonnegative (though its fourth derivative vanishes since it is a
polynomial). -/
example (k : ℕ) (x : ℝ) (hx : 0 ≤ x) :
    (iteratedDeriv k (fun z : ℂ ↦ 1 + z ^ 2) (x : ℂ)).im = 0 ∧
      0 ≤ (iteratedDeriv k (fun z : ℂ ↦ 1 + z ^ 2) (x : ℂ)).re := by
  refine pairedHadamard_derivatives_nonnegative (δ := 1)
    ((isCenteredOrderOne_const 1).add (isCenteredOrderOne_id.pow 2))
    (fun z ↦ by ring) ?_ ⟨0, fun y _ ↦ ?_⟩ k x hx
  · intro z hz
    have hsq : z ^ 2 = -1 := eq_neg_of_add_eq_zero_right hz
    have hre_sq : (z ^ 2).re = -1 := by rw [hsq]; norm_num
    have him_sq : (z ^ 2).im = 0 := by rw [hsq]; norm_num
    rw [sq, mul_re] at hre_sq
    rw [sq, mul_im] at him_sq
    have hprod_zero : z.re * z.im = 0 := by linarith
    rcases mul_eq_zero.mp hprod_zero with hre0 | him0
    · exact hre0
    · exfalso; nlinarith [sq_nonneg z.re]
  · have hc : (1 : ℂ) + (y : ℂ) ^ 2 = (((1 + y ^ 2 : ℝ) : ℂ)) := by push_cast; ring
    rw [hc, ofReal_im, ofReal_re]
    exact ⟨rfl, by positivity⟩

/-- `Complex.cosh` satisfies the paired Hadamard hypotheses with `δ = 1` and is not a polynomial,
so every iterated derivative `iteratedDeriv k Complex.cosh (x : ℂ)` has strictly positive real part
for all `x > 0`. -/
example (k : ℕ) (x : ℝ) (hx : 0 < x) :
    0 < (iteratedDeriv k Complex.cosh (x : ℂ)).re := by
  have hcosh_eq : Complex.cosh = fun z : ℂ ↦ (2 : ℂ)⁻¹ * (exp z + exp (-z)) := by
    ext z; rw [Complex.cosh, div_eq_inv_mul, mul_comm]
  have hf : IsCenteredOrderOne Complex.cosh := by
    rw [hcosh_eq]
    exact (isCenteredOrderOne_cexp.add isCenteredOrderOne_cexp.comp_neg).const_mul (2 : ℂ)⁻¹
  have hzeros (z : ℂ) (hz : Complex.cosh z = 0) : z.re = 0 := by
    rw [Complex.cosh, div_eq_zero_iff] at hz
    have hnorm := congrArg norm (eq_neg_of_add_eq_zero_left (hz.resolve_right two_ne_zero))
    rw [norm_neg, norm_exp, norm_exp, neg_re, Real.exp_eq_exp] at hnorm
    linarith
  have hpos : ∃ R : ℝ, ∀ y : ℝ, R ≤ y → (Complex.cosh (y : ℂ)).im = 0 ∧
      0 < (Complex.cosh (y : ℂ)).re :=
    ⟨0, fun y _ ↦ by rw [← Complex.ofReal_cosh, ofReal_im, ofReal_re]; exact ⟨rfl, Real.cosh_pos y⟩⟩
  have hnonpoly : ¬ ∃ P : Polynomial ℂ, ∀ z, Complex.cosh z = P.eval z := by
    rintro ⟨P, hP⟩
    set m : ℕ := P.natDegree + 1
    have h1 : iteratedDeriv (2 * m) Complex.cosh 0 = 1 := by
      rw [hcosh_eq, iteratedDeriv_const_mul_field, iteratedDeriv_fun_add
        Complex.contDiff_exp.contDiffAt contDiff_neg.cexp.contDiffAt,
        iteratedDeriv_comp_neg, iteratedDeriv_eq_iterate,
        Complex.iter_deriv_exp, pow_mul, neg_one_sq, one_pow, one_smul, neg_zero, Complex.exp_zero]
      norm_num
    have h0 : iteratedDeriv (2 * m) Complex.cosh 0 = 0 := by
      rw [funext hP, P.iteratedDeriv, Polynomial.iterate_derivative_eq_zero (by omega)]
      simp
    exact one_ne_zero (h1.symm.trans h0)
  exact pairedHadamard_derivatives_positive (δ := 1) hf
    (fun z ↦ by simp [Complex.cosh_neg]) hzeros hpos hnonpoly k x hx

end TauCeti
