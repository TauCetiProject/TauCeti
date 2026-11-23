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
import Mathlib.Analysis.Complex.LocallyUniformLimit
import TauCeti.Algebra.Polynomial.Derivative
import TauCeti.Analysis.Calculus.Deriv.Polynomial
import TauCeti.Analysis.Calculus.IteratedDeriv.Basic
import TauCeti.Analysis.Complex.CanonicalProduct.Quadratic.Basic
import TauCeti.Analysis.Complex.CanonicalProduct.Quadratic.Polynomial
import TauCeti.Analysis.Complex.IteratedDeriv
import TauCeti.Analysis.Complex.Positivity

/-!
# Derivative positivity for paired quadratic canonical products

Let `f : ℂ → ℂ` be given by a convergent paired quadratic canonical product
`f z = c * z ^ m * ∏' n, (1 + z ^ 2 / (γ n) ^ 2)` with `c ≥ 0` and
`∑' n, (γ n)⁻¹ ^ 2 < ∞`. Each finite partial product is the complexification of a real polynomial
`TauCeti.pairedPartialPoly c m γ s` whose coefficients are nonnegative and monotone in `s`.

By compact uniform convergence of the partial products
(`TauCeti.tendstoUniformlyOn_mul_pow_one_add_div_sq`)
and Weierstrass's theorem for iterated derivatives (`TendstoLocallyUniformlyOn.iteratedDeriv`),
this yields:

* `TauCeti.iteratedDeriv_im_eq_zero_and_re_nonneg_of_eq_mul_pow_tprod_one_add_div_sq`: for `c ≥ 0`,
  every iterated derivative `iteratedDeriv k f x` at `x ≥ 0` is real and nonnegative.
* `TauCeti.re_iteratedDeriv_zero_pos_of_eq_mul_pow_tprod_one_add_div_sq`: if `c > 0` and `t` is a
  finite set of indices with `γ n ≠ 0`, then the Taylor derivative of order `m + 2 * t.card` at
  `0` has strictly positive real part.
* `TauCeti.re_iteratedDeriv_pos_of_eq_mul_pow_tprod_one_add_div_sq_of_le`: if `c > 0` and `t` is a
  finite set of nonzero entries with `k ≤ m + 2 * t.card`, then `(iteratedDeriv k f x).re > 0`
  for every `x > 0`.
* `TauCeti.re_iteratedDeriv_pos_of_eq_mul_pow_tprod_one_add_div_sq`: if `c > 0` and infinitely
  many `γ n` are nonzero, then `(iteratedDeriv k f x).re > 0` for every `k : ℕ` and every `x > 0`.

## Main results

* `TauCeti.iteratedDeriv_im_eq_zero_and_re_nonneg_of_eq_mul_pow_tprod_one_add_div_sq`: reality and
  nonnegativity of all iterated derivatives on `[0, ∞)`.
* `TauCeti.re_iteratedDeriv_zero_pos_of_eq_mul_pow_tprod_one_add_div_sq`: strict positivity of
  the Taylor derivative of order `m + 2 * t.card` at `0` given a finite nonzero index witness.
* `TauCeti.re_iteratedDeriv_pos_of_eq_mul_pow_tprod_one_add_div_sq_of_le`: strict positivity of
  iterated derivatives up to order `m + 2 * t.card` on `(0, ∞)` given a finite nonzero witness `t`.
* `TauCeti.re_iteratedDeriv_pos_of_eq_mul_pow_tprod_one_add_div_sq`: strict positivity of all
  iterated derivatives on `(0, ∞)` when infinitely many `γ n` are nonzero.

## References

* Z. Yun and W. Zhang, *Shtukas and the Taylor expansion of L-functions*, Ann. of Math. (2) **186**
  (2017), no. 3, 767–911, Appendix B.1, Proposition B.1, pp. 902–903.
-/

public section

open Complex Filter Metric Polynomial Topology
open scoped BigOperators

namespace TauCeti

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
    rw [Polynomial.iteratedDeriv, Polynomial.iterate_derivative_map]
    dsimp only
    rw [← Complex.coe_algebraMap, Polynomial.eval_map_apply]
  open scoped ComplexOrder in
  have hle : (0 : ℂ) ≤ iteratedDeriv k f (x : ℂ) :=
    ge_of_tendsto' (htend.congr fun s ↦ (hreal_val s).symm) fun s ↦ by
      simpa only [Complex.ofReal_zero] using Complex.real_le_real.mpr
        (Polynomial.eval_iterate_derivative_nonneg
          (coeff_pairedPartialPoly_nonneg hc m γ s) k hx)
  open scoped ComplexOrder in
  simpa only [Complex.nonneg_iff, eq_comm, and_comm] using hle

/-- If `c > 0` and `t : Finset ℕ` is a set of indices with `γ n ≠ 0`, then the derivative of order
`m + 2 * t.card` at `0` of the paired quadratic canonical product has strictly positive real
part. -/
theorem re_iteratedDeriv_zero_pos_of_eq_mul_pow_tprod_one_add_div_sq
    {f : ℂ → ℂ} {c : ℝ} (hc : 0 < c) {m : ℕ} {γ : ℕ → ℝ}
    (hsum : Summable (fun n ↦ (γ n)⁻¹ ^ 2))
    (hf_eq : ∀ z : ℂ, f z = (c : ℂ) * z ^ m * ∏' n : ℕ, (1 + z ^ 2 / (γ n : ℂ) ^ 2))
    {t : Finset ℕ} (ht : ∀ n ∈ t, γ n ≠ 0) :
    0 < (iteratedDeriv (m + 2 * t.card) f 0).re := by
  classical
  set N : ℕ := m + 2 * t.card
  have ht_pos : 0 < (pairedPartialPoly c m γ t).coeff N :=
    coeff_pairedPartialPoly_top_pos hc m γ t ht
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

/-- If `c > 0` and `t : Finset ℕ` is a finite set of indices with `γ n ≠ 0` such that
`k ≤ m + 2 * t.card`, then the `k`-th iterated derivative of the paired quadratic canonical
product has strictly positive real part on `(0, ∞)`. -/
theorem re_iteratedDeriv_pos_of_eq_mul_pow_tprod_one_add_div_sq_of_le
    {f : ℂ → ℂ} {c : ℝ} (hc : 0 < c) {m : ℕ} {γ : ℕ → ℝ}
    (hsum : Summable (fun n ↦ (γ n)⁻¹ ^ 2))
    (hf_eq : ∀ z : ℂ, f z = (c : ℂ) * z ^ m * ∏' n : ℕ, (1 + z ^ 2 / (γ n : ℂ) ^ 2))
    {t : Finset ℕ} (ht : ∀ n ∈ t, γ n ≠ 0) {k : ℕ} (hk : k ≤ m + 2 * t.card)
    {x : ℝ} (hx : 0 < x) :
    0 < (iteratedDeriv k f (x : ℂ)).re := by
  -- `f` is entire as a locally uniform limit of mapped partial polynomials.
  have hf_diff : Differentiable ℂ f := by
    rw [← differentiableOn_univ]
    exact (tendstoLocallyUniformlyOn_pairedPartialPoly c m γ hsum hf_eq).differentiableOn
      (Eventually.of_forall fun s ↦
        ((pairedPartialPoly c m γ s).map (algebraMap ℝ ℂ)).differentiableOn)
      isOpen_univ
  -- Choose the positive Taylor margin `a₀` of `iteratedDeriv k f` at `n₀ = m + 2 * t.card - k`.
  set n₀ : ℕ := m + 2 * t.card - k
  have hn₀_add : n₀ + k = m + 2 * t.card := by omega
  set a₀ : ℝ := (iteratedDeriv (n₀ + k) f 0).re / (n₀.factorial : ℝ)
  have ha₀_pos : 0 < a₀ := div_pos
    (hn₀_add ▸ re_iteratedDeriv_zero_pos_of_eq_mul_pow_tprod_one_add_div_sq hc hsum hf_eq ht)
    (Nat.cast_pos.mpr n₀.factorial_pos)
  -- Compare `iteratedDeriv k f` against `a₀ * x ^ n₀` on `[0, ∞)`.
  have hle : a₀ * x ^ n₀ ≤ (iteratedDeriv k f (x : ℂ)).re := by
    refine (hf_diff.iteratedDeriv k).mul_pow_le_re_of_iteratedDeriv_nonneg (fun n ↦ ?_) ?_ hx.le
    · rw [iteratedDeriv_iteratedDeriv]
      exact iteratedDeriv_im_eq_zero_and_re_nonneg_of_eq_mul_pow_tprod_one_add_div_sq
        hc.le hsum hf_eq (n + k) le_rfl
    · rw [iteratedDeriv_iteratedDeriv]
      exact (div_mul_cancel₀ _ (Nat.cast_ne_zero.mpr n₀.factorial_ne_zero)).le
  exact (mul_pos ha₀_pos (pow_pos hx n₀)).trans_le hle

/-- If `c > 0` and infinitely many `γ n` are nonzero, then every iterated derivative of the
paired quadratic canonical product has strictly positive real part on `(0, ∞)`. -/
theorem re_iteratedDeriv_pos_of_eq_mul_pow_tprod_one_add_div_sq
    {f : ℂ → ℂ} {c : ℝ} (hc : 0 < c) {m : ℕ} {γ : ℕ → ℝ}
    (hsum : Summable (fun n ↦ (γ n)⁻¹ ^ 2))
    (hf_eq : ∀ z : ℂ, f z = (c : ℂ) * z ^ m * ∏' n : ℕ, (1 + z ^ 2 / (γ n : ℂ) ^ 2))
    (hinf : {n : ℕ | γ n ≠ 0}.Infinite) (k : ℕ) {x : ℝ} (hx : 0 < x) :
    0 < (iteratedDeriv k f (x : ℂ)).re := by
  obtain ⟨t, ht_sub, ht_card⟩ := hinf.exists_subset_card_eq k
  exact re_iteratedDeriv_pos_of_eq_mul_pow_tprod_one_add_div_sq_of_le hc hsum hf_eq
    (fun _ hn ↦ ht_sub hn) (by omega) hx

end TauCeti
