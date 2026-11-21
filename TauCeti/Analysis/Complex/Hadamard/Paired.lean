/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Analytic.Order
public import TauCeti.Analysis.Complex.GrowthOrder.Centered
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import TauCeti.Analysis.Analytic.Reflection
import TauCeti.Analysis.Calculus.Deriv.Polynomial
import TauCeti.Analysis.Calculus.LogDeriv.Symmetry
import TauCeti.Analysis.Complex.CanonicalProduct.Quadratic.Basic
import TauCeti.Analysis.Complex.CanonicalProduct.Quadratic.Positivity
import TauCeti.Analysis.Complex.GrowthOrder.Zero.Factorization
import TauCeti.Analysis.Complex.GrowthOrder.Zero.Summability
import TauCeti.Analysis.Complex.Hadamard.OrderOne

/-!
# Paired Hadamard factorization and positivity of derivatives

Let `f : ℂ → ℂ` be an entire function of order at most one (`TauCeti.IsCenteredOrderOne f`)
satisfying `f (-z) = δ * f z`, having every zero on the imaginary axis, and taking strictly
positive real values at all sufficiently large real arguments. Following Yun and Zhang
(*Shtukas and the Taylor expansion of L-functions*, Appendix B.1, Proposition B.1), this file
proves:

1. **Paired Hadamard factorization (`TauCeti.pairedHadamard_factorization`).** Writing
   `m = (analyticOrderAt f 0).toNat` for the analytic order of `f` at `0`, the functional equation
   and eventual positivity automatically force `δ = (-1) ^ m`, and there exist `c > 0` and a
   nonnegative sequence `γ : ℕ → ℝ` with `∑ (γ n)⁻¹ ^ 2 < ∞` (using `0` entries to pad unused
   indices when the zero multiset is finite; under totalized division `z ^ 2 / 0 = 0`, those
   factors equal `1` automatically) such that
   `f z = c * z ^ m * ∏' n, (1 + z ^ 2 / (γ n) ^ 2)`
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

/-! ### The paired Hadamard factorization theorem -/

variable {f : ℂ → ℂ} {δ : ℂ}

/-- Evaluating `f z = a * z ^ m * ∏' n, (1 + z ^ 2 / (γ n) ^ 2)` at `x₀ = max R 1 > 0` shows
that eventual real positivity of `f` forces the leading constant `a` to be real and strictly
positive. -/
private theorem im_eq_zero_and_re_pos_of_eq_mul_pow_one_add_div_sq {a : ℂ} {m : ℕ} {γ : ℕ → ℝ}
    (hsum : Summable (fun n ↦ (γ n)⁻¹ ^ 2))
    (hf_eq : ∀ z : ℂ, f z = a * z ^ m * ∏' n, (1 + z ^ 2 / (γ n : ℂ) ^ 2))
    (hpositive : ∃ R : ℝ, ∀ x : ℝ, R ≤ x → (f (x : ℂ)).im = 0 ∧ 0 < (f (x : ℂ)).re) :
    a.im = 0 ∧ 0 < a.re := by
  obtain ⟨R, hR⟩ := hpositive
  set x₀ : ℝ := max R 1
  obtain ⟨hfx_im, hfx_re⟩ := hR x₀ (le_max_left R 1)
  have hP_le : (1 : ℝ) ≤ (∏' n : ℕ, (1 + (x₀ : ℂ) ^ 2 / (γ n : ℂ) ^ 2)).re ∧
      (0 : ℝ) = (∏' n : ℕ, (1 + (x₀ : ℂ) ^ 2 / (γ n : ℂ) ^ 2)).im := by
    open scoped ComplexOrder in
    exact Complex.le_def.mp (one_le_tprod_one_add_div_sq hsum x₀)
  set P₀ : ℂ := ∏' n : ℕ, (1 + (x₀ : ℂ) ^ 2 / (γ n : ℂ) ^ 2) with hP₀_def
  have hK_pos : 0 < x₀ ^ m * P₀.re :=
    mul_pos (pow_pos (lt_of_lt_of_le zero_lt_one (le_max_right R 1)) m)
      (zero_lt_one.trans_le hP_le.1)
  have hP_coe : P₀ = (P₀.re : ℂ) := Complex.ext rfl hP_le.2.symm
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

/-- **The paired Hadamard factorization theorem.** An entire function `f` satisfying
`IsCenteredOrderOne f`, `f (-z) = δ * f z`, with all zeros on the imaginary axis and strictly
positive real values for large positive reals, admits a locally uniformly convergent factorization
`f z = c * z ^ m * ∏' n, (1 + z ^ 2 / γ_n ^ 2)` where `m = (analyticOrderAt f 0).toNat` (with `0`
entries of `γ` encoding unused indices when the zero multiset is finite), `c > 0`, and
`δ = (-1) ^ m`. Note that `δ ∈ {1, -1}` does not need to be assumed separately: eventual positivity
implies `f ≠ 0`, so `f (-z) = δ * f z` automatically forces `δ = (-1) ^ m`. -/
theorem pairedHadamard_factorization
    (hf : IsCenteredOrderOne f)
    (hparity : ∀ z, f (-z) = δ * f z)
    (hzeros : ∀ z, f z = 0 → z.re = 0)
    (hpositive : ∃ R : ℝ, ∀ x : ℝ, R ≤ x → (f (x : ℂ)).im = 0 ∧ 0 < (f (x : ℂ)).re) :
    ∃ (c : ℝ) (γ : ℕ → ℝ), 0 < c ∧
      (∀ n, 0 ≤ γ n) ∧ Summable (fun n ↦ (γ n)⁻¹ ^ 2) ∧
      δ = (-1 : ℂ) ^ (analyticOrderAt f 0).toNat ∧
      (∀ z : ℂ, Multipliable (fun n ↦ 1 + z ^ 2 / (γ n : ℂ) ^ 2)) ∧
      (∀ z : ℂ, f z = (c : ℂ) * z ^ (analyticOrderAt f 0).toNat *
        ∏' n, (1 + z ^ 2 / (γ n : ℂ) ^ 2)) ∧
      (∀ K : Set ℂ, IsCompact K → TendstoUniformlyOn
        (fun (s : Finset ℕ) (z : ℂ) ↦ (c : ℂ) * z ^ (analyticOrderAt f 0).toNat *
          ∏ n ∈ s, (1 + z ^ 2 / (γ n : ℂ) ^ 2))
        f Filter.atTop K) := by
  have hf_ne_zero : f ≠ 0 := by
    obtain ⟨R, hR⟩ := hpositive
    exact fun h0 ↦ lt_irrefl 0 (by simpa [h0] using (hR R le_rfl).2)
  set m : ℕ := (analyticOrderAt f 0).toNat
  obtain ⟨g, hg_diff, hg0, hg_ord, hfg0⟩ :=
    hf.orderLE_one.exists_eq_sub_pow_mul hf.differentiable (Function.ne_iff.mp hf_ne_zero) 0
  have hfg (z : ℂ) : f z = z ^ m * g z := by
    simpa only [sub_zero, analyticOrderNatAt] using hfg0 z
  obtain ⟨hδ_eq, hg_even⟩ :=
    eq_neg_one_pow_and_even_of_eq_pow_mul hfg hparity hg_diff.continuous.continuousAt hg0
  have hg_prod (z : ℂ) : g z = g 0 * divisorProductOne g z := by
    rw [hg_ord.eq_mul_cexp_logDeriv_mul_divisorProductOne hg_diff hg0 z,
      hg_even.logDeriv_zero, zero_mul, exp_zero, mul_one]
  have hg_zeros (z : ℂ) (hgz : g z = 0) : z.re = 0 := hzeros z (by rw [hfg z, hgz, mul_zero])
  obtain ⟨γ, hγ_nonneg, hγ_sum, hdiv_eq⟩ := exists_paired_seq_divisorProductOne hg_diff hg0 hg_even
    hg_zeros (hg_ord.summable_divisor_toNat_mul_norm_inv_sq hg_diff (by norm_num))
  have hf_eq_g0 (z : ℂ) :
      f z = g 0 * z ^ m * ∏' n : ℕ, (1 + z ^ 2 / (γ n : ℂ) ^ 2) := by
    rw [hfg z, hg_prod z, hdiv_eq z]; ring
  obtain ⟨hg0_im, hg0_re_pos⟩ :=
    im_eq_zero_and_re_pos_of_eq_mul_pow_one_add_div_sq hγ_sum hf_eq_g0 hpositive
  have hc_coe : g 0 = (((g 0).re : ℝ) : ℂ) := Complex.ext rfl hg0_im
  have hf_eq_c (z : ℂ) : f z = (((g 0).re : ℝ) : ℂ) * z ^ m *
      ∏' n : ℕ, (1 + z ^ 2 / (γ n : ℂ) ^ 2) := by
    rw [← hc_coe]
    exact hf_eq_g0 z
  refine ⟨(g 0).re, γ, hg0_re_pos, hγ_nonneg, hγ_sum, hδ_eq,
    fun z ↦ (hasProd_one_add_div_sq hγ_sum z).multipliable, hf_eq_c, fun K hK ↦
    (tendstoUniformlyOn_mul_pow_one_add_div_sq _ m hγ_sum hK).congr_right
      fun z _ ↦ (hf_eq_c z).symm⟩

/-! ### Derivative positivity for paired Hadamard products -/

private theorem infinite_ne_zero_of_not_poly {c : ℝ} {m : ℕ} {γ : ℕ → ℝ}
    (hprod_eq : ∀ z : ℂ, f z = (c : ℂ) * z ^ m * ∏' n : ℕ, (1 + z ^ 2 / (γ n : ℂ) ^ 2))
    (hnonpoly : ¬ ∃ P : Polynomial ℂ, ∀ z, f z = P.eval z) :
    {n : ℕ | γ n ≠ 0}.Infinite := by
  classical
  refine fun hfin ↦ hnonpoly
    ⟨Polynomial.C (c : ℂ) * Polynomial.X ^ m *
        ∏ n ∈ hfin.toFinset, (1 + Polynomial.C (((γ n : ℂ) ^ 2)⁻¹) * Polynomial.X ^ 2),
      fun z ↦ ?_⟩
  rw [hprod_eq z]
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X,
    Polynomial.eval_prod, Polynomial.eval_add, Polynomial.eval_one, div_eq_inv_mul]
  congr 1
  refine tprod_eq_prod fun n hn ↦ ?_
  have hγ0 : γ n = 0 := by
    by_contra hne
    exact hn (hfin.mem_toFinset.mpr hne)
  simp [hγ0]

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
  obtain ⟨c, γ, hc, _, hsum, _, _, hprod_eq, _⟩ :=
    pairedHadamard_factorization hf hparity hzeros hpositive
  exact iteratedDeriv_im_eq_zero_and_re_nonneg_of_eq_mul_pow_tprod_one_add_div_sq
    hc.le hsum hprod_eq k hx

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
  obtain ⟨c, γ, hc, _, hsum, _, _, hprod_eq, _⟩ :=
    pairedHadamard_factorization hf hparity hzeros hpositive
  exact re_iteratedDeriv_zero_pos_of_eq_mul_pow_tprod_one_add_div_sq
    hc hsum hprod_eq (infinite_ne_zero_of_not_poly hprod_eq hnonpoly) j

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
  obtain ⟨c, γ, hc, _, hsum, _, _, hprod_eq, _⟩ :=
    pairedHadamard_factorization hf hparity hzeros hpositive
  exact re_iteratedDeriv_pos_of_eq_mul_pow_tprod_one_add_div_sq
    hc hsum hprod_eq (infinite_ne_zero_of_not_poly hprod_eq hnonpoly) k hx

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
    open scoped ComplexOrder in
    exact Complex.sq_nonpos_iff.mp (by rw [eq_neg_of_add_eq_zero_right hz]; norm_num)
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
    rw [← Complex.cos_mul_I, Complex.cos_eq_zero_iff] at hz
    obtain ⟨n, hn⟩ := hz
    simpa using congrArg Complex.im hn
  have hpos : ∃ R : ℝ, ∀ y : ℝ, R ≤ y → (Complex.cosh (y : ℂ)).im = 0 ∧
      0 < (Complex.cosh (y : ℂ)).re :=
    ⟨0, fun y _ ↦ by rw [← Complex.ofReal_cosh, ofReal_im, ofReal_re]; exact ⟨rfl, Real.cosh_pos y⟩⟩
  have hnonpoly : ¬ ∃ P : Polynomial ℂ, ∀ z, Complex.cosh z = P.eval z := by
    rintro ⟨P, hP⟩
    set m : ℕ := P.natDegree + 1
    have h1 : iteratedDeriv (2 * m) Complex.cosh 0 = 1 := by
      rw [Complex.iteratedDeriv_even_cosh, Complex.cosh_zero]
    have h0 : iteratedDeriv (2 * m) Complex.cosh 0 = 0 := by
      rw [funext hP, P.iteratedDeriv, Polynomial.iterate_derivative_eq_zero (by omega)]
      simp
    exact one_ne_zero (h1.symm.trans h0)
  exact pairedHadamard_derivatives_positive (δ := 1) hf
    (fun z ↦ by simp [Complex.cosh_neg]) hzeros hpos hnonpoly k x hx

end TauCeti
