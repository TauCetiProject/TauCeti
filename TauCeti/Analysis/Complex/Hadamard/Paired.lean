/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Analytic.Order
public import TauCeti.Analysis.Complex.GrowthOrder.Centered
import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import TauCeti.Algebra.Polynomial.Coeff.Basic
import TauCeti.Algebra.Polynomial.Derivative
import TauCeti.Analysis.Analytic.Reflection
import TauCeti.Analysis.Calculus.Deriv.Polynomial
import TauCeti.Analysis.Calculus.LogDeriv.Symmetry
import TauCeti.Analysis.Complex.CanonicalProduct.Quadratic
import TauCeti.Analysis.Complex.GrowthOrder.Zero.Factorization
import TauCeti.Analysis.Complex.GrowthOrder.Zero.Summability
import TauCeti.Analysis.Complex.Hadamard.OrderOne
import TauCeti.Analysis.Complex.IteratedDeriv

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
   indices when the zero multiset is finite) such that
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
  refine ⟨(g 0).re, γ, hg0_re_pos, hγ_nonneg, hγ_sum, hδ_eq, ?_, ?_, ?_⟩
  · intro z
    simpa only [ite_eq_zero_one_add_div_sq] using (hasProd_one_add_div_sq hγ_sum z).multipliable
  · intro z
    simpa only [ite_eq_zero_one_add_div_sq] using hf_eq_c z
  · intro K hK
    simpa only [ite_eq_zero_one_add_div_sq] using
      (tendstoUniformlyOn_mul_pow_one_add_div_sq _ m hγ_sum hK).congr_right
        fun z _ ↦ (hf_eq_c z).symm

/-! ### Polynomial partial products and derivative positivity -/

/-- The finite partial-product real polynomial
`P_s(X) = c * X ^ m * ∏_{n ∈ s} (1 + (γ n)⁻¹ ^ 2 * X ^ 2)`. -/
private noncomputable def pairedPartialPoly (c : ℝ) (m : ℕ) (γ : ℕ → ℝ) (s : Finset ℕ) : ℝ[X] :=
  C c * X ^ m * ∏ n ∈ s, (1 + C ((γ n)⁻¹ ^ 2) * X ^ 2)

private theorem eval_map_pairedPartialPoly (c : ℝ) (m : ℕ) (γ : ℕ → ℝ) (s : Finset ℕ) (z : ℂ) :
    ((pairedPartialPoly c m γ s).map (algebraMap ℝ ℂ)).eval z =
      (c : ℂ) * z ^ m * ∏ n ∈ s, (1 + z ^ 2 / (γ n : ℂ) ^ 2) := by
  rw [eval_map, ← aeval_def]
  simp only [pairedPartialPoly, map_mul, map_pow, aeval_C, aeval_X, Complex.coe_algebraMap,
    map_prod, map_add, map_one]
  congr 1
  refine Finset.prod_congr rfl fun n _ ↦ ?_
  rw [one_add_div_sq_eq_one_add_inv_sq_mul]
  push_cast
  ring

/-- Every coefficient of `pairedPartialPoly c m γ s` is nonnegative when `0 ≤ c`. -/
private theorem coeff_pairedPartialPoly_nonneg {c : ℝ} (hc : 0 ≤ c) (m : ℕ) (γ : ℕ → ℝ)
    (s : Finset ℕ) : ∀ d, 0 ≤ (pairedPartialPoly c m γ s).coeff d := by
  classical
  have hC : ∀ d, 0 ≤ (C c).coeff d := fun d ↦ by rw [coeff_C]; split_ifs <;> positivity
  have hX : ∀ d, 0 ≤ (X ^ m : ℝ[X]).coeff d := fun d ↦ by
    rw [coeff_X_pow]; split_ifs <;> norm_num
  have hfactor (n : ℕ) : ∀ d, 0 ≤ (1 + C ((γ n)⁻¹ ^ 2) * X ^ 2).coeff d := fun d ↦ by
    rw [coeff_add, coeff_one, coeff_C_mul_X_pow]; split_ifs <;> positivity
  have hprod : ∀ d, 0 ≤ (∏ n ∈ s, (1 + C ((γ n)⁻¹ ^ 2) * X ^ 2)).coeff d := by
    refine Finset.prod_induction _ (fun p : ℝ[X] ↦ ∀ d, 0 ≤ p.coeff d)
      (fun _ _ hp hq d ↦ coeff_mul_nonneg hp hq d) (fun d ↦ ?_) (fun n _ ↦ hfactor n)
    rw [coeff_one]; split_ifs <;> norm_num
  exact coeff_mul_nonneg (coeff_mul_nonneg hC hX) hprod

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
  unfold pairedPartialPoly
  rw [mul_assoc, coeff_C_mul, mul_comm (X ^ m), add_comm m, coeff_mul_X_pow]
  have hdeg : ∀ n ∈ t, (1 + C ((γ n)⁻¹ ^ 2) * X ^ 2 : ℝ[X]).natDegree ≤ 2 := fun n _ ↦ by
    compute_degree!
  rw [mul_comm 2 t.card,
    coeff_prod_of_natDegree_le t (fun n ↦ 1 + C ((γ n)⁻¹ ^ 2) * X ^ 2) 2 hdeg]
  refine mul_pos hc (Finset.prod_pos fun n hn ↦ ?_)
  simp [coeff_one, sq_pos_of_ne_zero (ht n hn)]

/-- Locally uniform convergence of the paired partial polynomials implies convergence of every
iterated derivative at every point `z : ℂ`. -/
private theorem tendsto_iteratedDeriv_pairedPartialPoly {c : ℝ} {m : ℕ} {γ : ℕ → ℝ}
    (hunif : ∀ K : Set ℂ, IsCompact K → TendstoUniformlyOn
      (fun (s : Finset ℕ) (z : ℂ) ↦ (c : ℂ) * z ^ m *
        ∏ n ∈ s, (1 + z ^ 2 / (γ n : ℂ) ^ 2))
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
  set m : ℕ := (analyticOrderAt f 0).toNat
  obtain ⟨c, γ, hc, _, _, _, _, _, hunif⟩ :=
    pairedHadamard_factorization hf hparity hzeros hpositive
  simp_rw [ite_eq_zero_one_add_div_sq] at hunif
  have htend := tendsto_iteratedDeriv_pairedPartialPoly hunif k (x : ℂ)
  have hreal_val (s : Finset ℕ) :
      (((Polynomial.derivative^[k] (pairedPartialPoly c m γ s)).eval x : ℝ) : ℂ) =
        iteratedDeriv k
          (fun w : ℂ ↦ ((pairedPartialPoly c m γ s).map (algebraMap ℝ ℂ)).eval w) (x : ℂ) := by
    simpa only [Complex.coe_algebraMap] using
      ((pairedPartialPoly c m γ s).iteratedDeriv_eval_map (algebraMap ℝ ℂ) k x).symm
  open scoped ComplexOrder in
  have hle : (0 : ℂ) ≤ iteratedDeriv k f (x : ℂ) :=
    ge_of_tendsto' (htend.congr fun s ↦ (hreal_val s).symm) fun s ↦ by
      simpa only [Complex.ofReal_zero] using Complex.real_le_real.mpr
        (Polynomial.eval_iterate_derivative_nonneg
          (coeff_pairedPartialPoly_nonneg hc.le m γ s) k hx)
  open scoped ComplexOrder in
  exact ⟨(Complex.le_def.mp hle).2.symm, (Complex.le_def.mp hle).1⟩

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
    pairedHadamard_factorization hf hparity hzeros hpositive
  simp_rw [ite_eq_zero_one_add_div_sq] at hprod_eq hunif
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
      (((N.factorial : ℝ) * (pairedPartialPoly c m γ s).coeff N : ℝ) : ℂ) =
        iteratedDeriv N
          (fun w : ℂ ↦ ((pairedPartialPoly c m γ s).map (algebraMap ℝ ℂ)).eval w) 0 := by
    rw [Polynomial.iteratedDeriv_eval_zero, coeff_map, Complex.coe_algebraMap]
    push_cast
    ring
  open scoped ComplexOrder in
  have hle : (((N.factorial : ℝ) * (pairedPartialPoly c m γ t).coeff N : ℝ) : ℂ) ≤
      iteratedDeriv N f 0 :=
    ge_of_tendsto (htend.congr fun s ↦ (heval_zero s).symm)
      ((Filter.eventually_ge_atTop t).mono fun s hts ↦ Complex.real_le_real.mpr
        (mul_le_mul_of_nonneg_left (coeff_pairedPartialPoly_mono hc.le m γ hts N)
          (Nat.cast_nonneg _)))
  open scoped ComplexOrder in
  exact (mul_pos (Nat.cast_pos.mpr N.factorial_pos) ht_pos).trans_le (Complex.le_def.mp hle).1

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
  have hpos_coeff : 0 < (iteratedDeriv (n₀ + k) f 0).re := by
    rw [hn₀_add]
    exact pairedHadamard_iteratedDeriv_zero_pos hf hparity hzeros hpositive hnonpoly k
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
