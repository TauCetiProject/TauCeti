/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.Data.Finset.Interval
import TauCeti.Algebra.Polynomial.Coeff.Basic
import TauCeti.Algebra.Polynomial.Derivative
import TauCeti.Analysis.Calculus.Deriv.Polynomial
import TauCeti.Analysis.Calculus.IteratedDeriv.Basic
import TauCeti.Analysis.Complex.CanonicalProduct.Quadratic.Basic
import TauCeti.Analysis.Complex.IteratedDeriv

/-!
# Derivative positivity for paired quadratic canonical products

Let `f : ℂ → ℂ` be given by a convergent paired quadratic canonical product
`f z = c * z ^ m * ∏' n, (1 + z ^ 2 / (γ n) ^ 2)` with `c ≥ 0` and
`∑' n, (γ n)⁻¹ ^ 2 < ∞`. Each finite partial product is the complexification of a real polynomial
`P_s(X) = c * X ^ m * ∏_{n ∈ s} (1 + (γ n)⁻¹ ^ 2 * X ^ 2)` whose coefficients are nonnegative and
monotone in `s`.

By compact uniform convergence of the partial products
(`TauCeti.tendstoUniformlyOn_mul_pow_one_add_div_sq`)
and Weierstrass's theorem for iterated derivatives (`TendstoLocallyUniformlyOn.iteratedDeriv`),
this yields:

* `TauCeti.iteratedDeriv_im_eq_zero_and_re_nonneg_of_eq_mul_pow_tprod_one_add_div_sq`: for `c ≥ 0`,
  every iterated derivative `iteratedDeriv k f x` at `x ≥ 0` is real and nonnegative.
* `TauCeti.re_iteratedDeriv_zero_pos_of_eq_mul_pow_tprod_one_add_div_sq`: if `c > 0` and infinitely
  many `γ n` are nonzero, then every Taylor derivative of order `m + 2 * j` at `0` has strictly
  positive real part.
* `TauCeti.re_iteratedDeriv_pos_of_eq_mul_pow_tprod_one_add_div_sq`: under the same hypotheses,
  `(iteratedDeriv k f x).re > 0` for every `k : ℕ` and every `x > 0`.

## Main results

* `TauCeti.iteratedDeriv_im_eq_zero_and_re_nonneg_of_eq_mul_pow_tprod_one_add_div_sq`: reality and
  nonnegativity of all iterated derivatives on `[0, ∞)`.
* `TauCeti.re_iteratedDeriv_zero_pos_of_eq_mul_pow_tprod_one_add_div_sq`: strict positivity of
  same-parity Taylor derivatives from order `m` upward.
* `TauCeti.re_iteratedDeriv_pos_of_eq_mul_pow_tprod_one_add_div_sq`: strict positivity of all
  iterated derivatives on `(0, ∞)`.
-/

public section

open Complex Filter Metric Polynomial Topology
open scoped BigOperators

namespace TauCeti

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
  have hmono : Monotone (fun u ↦ (pairedPartialPoly c m γ u).coeff d) :=
    Finset.monotone_iff_forall_le_insert.mpr fun u n hn ↦ by
      have hstep : pairedPartialPoly c m γ (insert n u) =
          pairedPartialPoly c m γ u * (1 + C ((γ n)⁻¹ ^ 2) * X ^ 2) := by
        simp only [pairedPartialPoly, Finset.prod_insert hn]; ring
      rw [hstep]
      exact coeff_le_coeff_mul_one_add_C_mul_X_pow (coeff_pairedPartialPoly_nonneg hc m γ u)
        (sq_nonneg _) 2 d
  exact hmono hts

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

/-- The mapped partial polynomials converge locally uniformly on `ℂ` to `f`. -/
private theorem tendstoLocallyUniformlyOn_pairedPartialPoly {f : ℂ → ℂ} (c : ℝ) (m : ℕ)
    (γ : ℕ → ℝ) (hsum : Summable (fun n ↦ (γ n)⁻¹ ^ 2))
    (hf_eq : ∀ z : ℂ, f z = (c : ℂ) * z ^ m * ∏' n : ℕ, (1 + z ^ 2 / (γ n : ℂ) ^ 2)) :
    TendstoLocallyUniformlyOn
      (fun (s : Finset ℕ) (w : ℂ) ↦ ((pairedPartialPoly c m γ s).map (algebraMap ℝ ℂ)).eval w)
      f atTop Set.univ := by
  rw [tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_univ]
  intro K _ hK
  exact ((tendstoUniformlyOn_mul_pow_one_add_div_sq (c : ℂ) m hsum hK).congr_right
    fun z _ ↦ (hf_eq z).symm).congr (Eventually.of_forall fun s w _ ↦
      (eval_map_pairedPartialPoly c m γ s w).symm)

/-- Locally uniform convergence of the paired partial polynomials implies convergence of every
iterated derivative at every point `z : ℂ`. -/
private theorem tendsto_iteratedDeriv_pairedPartialPoly {f : ℂ → ℂ} (c : ℝ) (m : ℕ) (γ : ℕ → ℝ)
    (hsum : Summable (fun n ↦ (γ n)⁻¹ ^ 2))
    (hf_eq : ∀ z : ℂ, f z = (c : ℂ) * z ^ m * ∏' n : ℕ, (1 + z ^ 2 / (γ n : ℂ) ^ 2))
    (k : ℕ) (z : ℂ) :
    Tendsto
      (fun s : Finset ℕ ↦
        iteratedDeriv k (fun w : ℂ ↦ ((pairedPartialPoly c m γ s).map (algebraMap ℝ ℂ)).eval w) z)
      atTop (𝓝 (iteratedDeriv k f z)) := by
  have hloc := tendstoLocallyUniformlyOn_pairedPartialPoly c m γ hsum hf_eq
  have hdiff : ∀ᶠ s : Finset ℕ in atTop, DifferentiableOn ℂ
      (fun w : ℂ ↦ ((pairedPartialPoly c m γ s).map (algebraMap ℝ ℂ)).eval w) Set.univ :=
    Eventually.of_forall fun s ↦ ((pairedPartialPoly c m γ s).map (algebraMap ℝ ℂ)).differentiableOn
  exact (hloc.iteratedDeriv hdiff isOpen_univ k).tendsto_at (Set.mem_univ z)

/-- Every iterated derivative at `x ≥ 0` of a convergent paired quadratic canonical product with
nonnegative leading coefficient `c ≥ 0` is real and nonnegative. -/
theorem iteratedDeriv_im_eq_zero_and_re_nonneg_of_eq_mul_pow_tprod_one_add_div_sq
    {f : ℂ → ℂ} {c : ℝ} (hc : 0 ≤ c) {m : ℕ} {γ : ℕ → ℝ}
    (hsum : Summable (fun n ↦ (γ n)⁻¹ ^ 2))
    (hf_eq : ∀ z : ℂ, f z = (c : ℂ) * z ^ m * ∏' n : ℕ, (1 + z ^ 2 / (γ n : ℂ) ^ 2))
    (k : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    (iteratedDeriv k f (x : ℂ)).im = 0 ∧ 0 ≤ (iteratedDeriv k f (x : ℂ)).re := by
  have htend := tendsto_iteratedDeriv_pairedPartialPoly c m γ hsum hf_eq k (x : ℂ)
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
          (coeff_pairedPartialPoly_nonneg hc m γ s) k hx)
  open scoped ComplexOrder in
  exact ⟨(Complex.le_def.mp hle).2.symm, (Complex.le_def.mp hle).1⟩

/-- If `c > 0` and infinitely many `γ n` are nonzero, then for every `j : ℕ` the derivative of
order `m + 2 * j` at `0` of the paired quadratic canonical product has strictly positive real
part. -/
theorem re_iteratedDeriv_zero_pos_of_eq_mul_pow_tprod_one_add_div_sq
    {f : ℂ → ℂ} {c : ℝ} (hc : 0 < c) {m : ℕ} {γ : ℕ → ℝ}
    (hsum : Summable (fun n ↦ (γ n)⁻¹ ^ 2))
    (hf_eq : ∀ z : ℂ, f z = (c : ℂ) * z ^ m * ∏' n : ℕ, (1 + z ^ 2 / (γ n : ℂ) ^ 2))
    (hinf : {n : ℕ | γ n ≠ 0}.Infinite) (j : ℕ) :
    0 < (iteratedDeriv (m + 2 * j) f 0).re := by
  classical
  obtain ⟨t, ht_sub, ht_card⟩ := hinf.exists_subset_card_eq j
  set N : ℕ := m + 2 * j
  have ht_pos : 0 < (pairedPartialPoly c m γ t).coeff N := by
    simpa only [N, ht_card] using coeff_pairedPartialPoly_top_pos hc m γ t (fun n hn ↦ ht_sub hn)
  have htend := tendsto_iteratedDeriv_pairedPartialPoly c m γ hsum hf_eq N 0
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

/-- If `c > 0` and infinitely many `γ n` are nonzero, then every iterated derivative of the
paired quadratic canonical product has strictly positive real part on `(0, ∞)`. -/
theorem re_iteratedDeriv_pos_of_eq_mul_pow_tprod_one_add_div_sq
    {f : ℂ → ℂ} {c : ℝ} (hc : 0 < c) {m : ℕ} {γ : ℕ → ℝ}
    (hsum : Summable (fun n ↦ (γ n)⁻¹ ^ 2))
    (hf_eq : ∀ z : ℂ, f z = (c : ℂ) * z ^ m * ∏' n : ℕ, (1 + z ^ 2 / (γ n : ℂ) ^ 2))
    (hinf : {n : ℕ | γ n ≠ 0}.Infinite) (k : ℕ) {x : ℝ} (hx : 0 < x) :
    0 < (iteratedDeriv k f (x : ℂ)).re := by
  have hf_diff : Differentiable ℂ f := by
    rw [← differentiableOn_univ]
    exact (tendstoLocallyUniformlyOn_pairedPartialPoly c m γ hsum hf_eq).differentiableOn
      (Eventually.of_forall fun s ↦
        ((pairedPartialPoly c m γ s).map (algebraMap ℝ ℂ)).differentiableOn)
      isOpen_univ
  have hk_entire : Differentiable ℂ (iteratedDeriv k f) := hf_diff.iteratedDeriv k
  have hts := Complex.hasSum_taylorSeries_of_entire hk_entire 0 (x : ℂ)
  have hre_sum : HasSum
      (fun n : ℕ ↦ (n.factorial : ℝ)⁻¹ * x ^ n * (iteratedDeriv (n + k) f 0).re)
      (iteratedDeriv k f (x : ℂ)).re := by
    refine (Complex.reCLM.hasSum hts).congr_fun fun n ↦ ?_
    dsimp only [Complex.reCLM_apply]
    rw [sub_zero, iteratedDeriv_iteratedDeriv n k f, smul_eq_mul, smul_eq_mul]
    have hcast : ((n.factorial : ℂ)⁻¹ * ((x : ℂ) ^ n * iteratedDeriv (n + k) f 0)) =
        ((((n.factorial : ℝ)⁻¹ * x ^ n : ℝ) : ℂ)) * iteratedDeriv (n + k) f 0 := by
      push_cast; ring
    rw [hcast, re_ofReal_mul]
  have hterm_nonneg (n : ℕ) :
      0 ≤ (n.factorial : ℝ)⁻¹ * x ^ n * (iteratedDeriv (n + k) f 0).re :=
    mul_nonneg (mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) (pow_nonneg hx.le n))
      (iteratedDeriv_im_eq_zero_and_re_nonneg_of_eq_mul_pow_tprod_one_add_div_sq
        hc.le hsum hf_eq (n + k) le_rfl).2
  set n₀ : ℕ := m + k
  have hn₀_add : n₀ + k = m + 2 * k := by omega
  have hpos_coeff : 0 < (iteratedDeriv (n₀ + k) f 0).re := by
    rw [hn₀_add]
    exact re_iteratedDeriv_zero_pos_of_eq_mul_pow_tprod_one_add_div_sq hc hsum hf_eq hinf k
  have hterm_pos : 0 < (n₀.factorial : ℝ)⁻¹ * x ^ n₀ * (iteratedDeriv (n₀ + k) f 0).re :=
    mul_pos (mul_pos (inv_pos.mpr (Nat.cast_pos.mpr n₀.factorial_pos)) (pow_pos hx n₀)) hpos_coeff
  have hle : (n₀.factorial : ℝ)⁻¹ * x ^ n₀ * (iteratedDeriv (n₀ + k) f 0).re ≤
      (iteratedDeriv k f (x : ℂ)).re := by
    simpa only [Finset.sum_singleton] using
      sum_le_hasSum ({n₀} : Finset ℕ) (fun n _ ↦ hterm_nonneg n) hre_sum
  exact hterm_pos.trans_le hle

end TauCeti
