/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.NumberTheory.LSeries.Convergence
import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.NumberTheory.LSeries.Positivity
import TauCeti.Analysis.Complex.CauchyEstimate
import TauCeti.NumberTheory.LSeries.Positivity

/-!
# Estermann's inequality for Dirichlet series with a simple pole

Let `F(s) = ∑ aₙ n⁻ˢ` be a Dirichlet series with nonnegative coefficients, `a₁ = 1`, converging
absolutely on `Re s > 1`, such that `H(s) = (s - 1) F(s)` extends to an entire function. Write
`λ = H(1)` for the residue of `F` at `1`, and let `B` bound `‖H‖` on the disc `|s - 2| ≤ 3/2`.
Nonnegativity of the coefficients says that the Taylor coefficients of `F` at `s = 2`, taken in
powers of `2 - s`, are nonnegative, and the first of them is at least `1`. The entire function
`F(s) - λ / (s - 1)` has the Taylor coefficients of `F` minus `λ`, and those are small by Cauchy's
estimate on `|s - 2| = 3/2`. Comparing the two expansions at a real point `σ` to the left of `1`
bounds `F(σ)` from below in terms of `λ`, with a loss polynomial in `B` of exponent `4 (1 - σ)`.

Conversely, a point `σ` with `F(σ) ≤ 0` forces the residue `λ` to be large. Applied to
`ζ(s) L(s, χ) L(s, ψ) L(s, χ ψ)` for quadratic characters, this is the step of Siegel's theorem
that turns a real zero of one `L`-function into a lower bound for the product
`L(1, χ) L(1, ψ) L(1, χ ψ)`, uniform in `ψ`. No contour integration is involved: the disc
`|s - 2| ≤ 3/2` lies in `Re s ≥ 1/2`, so bounds for `L`-functions in that half-plane suffice.

## Main results

* `TauCeti.LSeries.estermann_inequality`: **Estermann's inequality** with a free truncation point
  `N` of the Taylor expansion.
* `TauCeti.LSeries.estermann_inequality_rpow`: the inequality with `N` optimized,
  `F(σ) ≥ 1/2 - 2 λ (32 B)^{4 (1 - σ)} / (1 - σ)` for `7/8 ≤ σ < 1`.
* `TauCeti.LSeries.estermann_lower_bound`: if `F(σ) ≤ 0`, then
  `λ ≥ (1 - σ) / (4 (32 B)^{4 (1 - σ)})`.

## References

* T. Estermann, *On Dirichlet's L functions*, J. London Math. Soc. 23 (1948), 275–279.
* H. Davenport, *Multiplicative Number Theory*, chapter on Siegel's theorem.
-/

public section

open Complex Metric Nat
open scoped ComplexOrder Topology

namespace TauCeti.LSeries

variable {a : ℕ → ℂ} {H : ℂ → ℂ}

/-- The `n`-th derivative at `2` of `(H(s) - H(1)) / (s - 1)` is that of the Dirichlet series
minus `H(1)` times that of `1 / (s - 1)`. -/
private lemma iteratedDeriv_dslope_eq (hH : Differentiable ℂ H)
    (hHa : ∀ s : ℂ, 1 < s.re → H s = (s - 1) * LSeries a s) (n : ℕ) :
    iteratedDeriv n (dslope H 1) 2 =
      iteratedDeriv n (LSeries a) 2 - H 1 * ((-1) ^ n * n !) := by
  have hev : LSeries a =ᶠ[𝓝 2] dslope H 1 + fun s ↦ H 1 * (s - 1)⁻¹ := by
    have hopen : {s : ℂ | 1 < s.re} ∈ 𝓝 (2 : ℂ) :=
      (isOpen_lt continuous_const continuous_re).mem_nhds (by simp)
    filter_upwards [hopen] with s hs
    have hs1 : s ≠ 1 := fun h ↦ by simp [h] at hs
    have hs1' : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
    rw [Pi.add_apply, dslope_of_ne _ hs1, slope_def_field, hHa s hs]
    field_simp
    ring
  have hinv : iteratedDeriv n (fun s : ℂ ↦ (s - 1)⁻¹) 2 = (-1) ^ n * n ! := by
    have h := congrFun (iter_deriv_inv_linear_sub n (1 : ℂ) 1) 2
    simp only [one_mul] at h
    rw [iteratedDeriv_eq_iterate, h]
    norm_num
  have hinvd : ContDiffAt ℂ n (fun s : ℂ ↦ H 1 * (s - 1)⁻¹) 2 := by
    have : (2 : ℂ) - 1 ≠ 0 := by norm_num
    fun_prop (disch := assumption)
  rw [hev.iteratedDeriv_eq n,
    iteratedDeriv_add (hH.dslope 1).contDiff.contDiffAt hinvd,
    iteratedDeriv_const_mul_field, hinv, add_sub_cancel_right]

/-- The Taylor terms of `(H(s) - H(1)) / (s - 1)` at `2` decay geometrically at `σ ∈ [7/8, 1)`, by
Cauchy's estimate on the circle `|s - 2| = 3/2`, on which `|s - 1| ≥ 1/2`. -/
private lemma norm_taylor_term_dslope_le (hH : Differentiable ℂ H) {B : ℝ}
    (hB : ∀ s ∈ closedBall (2 : ℂ) (3 / 2), ‖H s‖ ≤ B) {σ : ℝ} (hσ : 7 / 8 ≤ σ) (hσ₁ : σ < 1)
    (n : ℕ) :
    ‖(n ! : ℂ)⁻¹ • ((σ : ℂ) - 2) ^ n • iteratedDeriv n (dslope H 1) 2‖ ≤
      4 * B * (3 / 4) ^ n := by
  have hB₀ : 0 ≤ B := (norm_nonneg _).trans (hB 2 (mem_closedBall_self (by norm_num)))
  have hnorm : ‖(1 : ℂ) - 2‖ = 1 := by norm_num
  have hC (z : ℂ) (hz : z ∈ sphere (2 : ℂ) (3 / 2)) : ‖dslope H 1 z‖ ≤ 4 * B := by
    have h := norm_dslope_le_of_mem_sphere (mem_ball_iff_norm.mpr (by rw [hnorm]; norm_num)) hB hz
    rwa [hnorm, show 2 * B / (3 / 2 - 1) = 4 * B by ring] at h
  have hnorm2 : ‖(σ : ℂ) - 2‖ = 2 - σ := by
    rw [← ofReal_ofNat, ← ofReal_sub, norm_real, Real.norm_eq_abs, abs_sub_comm,
      abs_of_pos (by linarith)]
  refine (norm_taylor_term_le_of_forall_mem_sphere_norm_le (by norm_num)
    (hH.dslope 1).diffContOnCl hC σ n).trans ?_
  rw [hnorm2]
  have hratio : (2 - σ) / (3 / 2) ≤ 3 / 4 := by linarith
  have hratio₀ : 0 ≤ (2 - σ) / (3 / 2) := by linarith
  gcongr

/-- The `n`-th Taylor coefficient at `2` of `LSeries a`, in powers of `2 - s`. -/
private noncomputable def taylorCoeff (a : ℕ → ℂ) (n : ℕ) : ℝ :=
  ((n ! : ℂ)⁻¹ * ((-1) ^ n * iteratedDeriv n (LSeries a) 2)).re

private lemma taylorCoeff_nonneg (ha : 0 ≤ a) (habs : LSeries.abscissaOfAbsConv a ≤ (1 : ℝ))
    (n : ℕ) : 0 ≤ taylorCoeff a n := by
  have h := LSeries.iteratedDeriv_alternating ha
    (habs.trans_lt (EReal.coe_lt_coe_iff.mpr (by norm_num : (1 : ℝ) < 2))) n
  rw [ofReal_ofNat] at h
  have hfac : (0 : ℂ) ≤ (n ! : ℂ)⁻¹ := by
    rw [← ofReal_natCast, ← ofReal_inv]
    exact zero_le_real.mpr (by positivity)
  exact (Complex.le_def.mp (mul_nonneg hfac h)).1

private lemma one_le_taylorCoeff_zero (ha : 0 ≤ a) (ha₁ : a 1 = 1)
    (habs : LSeries.abscissaOfAbsConv a ≤ (1 : ℝ)) : 1 ≤ taylorCoeff a 0 := by
  have h := apply_one_le_LSeries ha
    (habs.trans_lt (EReal.coe_lt_coe_iff.mpr (by norm_num : (1 : ℝ) < 2)))
  rw [ha₁, ofReal_ofNat] at h
  simpa [taylorCoeff] using (Complex.le_def.mp h).1

/-- The Taylor coefficients of `(H(s) - H(1)) / (s - 1)` at `2`, in powers of `2 - s`, are those of
`LSeries a` minus `H(1)`. -/
private lemma re_taylor_term_eq (hH : Differentiable ℂ H)
    (hHa : ∀ s : ℂ, 1 < s.re → H s = (s - 1) * LSeries a s) (σ : ℝ) (n : ℕ) :
    ((n ! : ℂ)⁻¹ • ((σ : ℂ) - 2) ^ n • iteratedDeriv n (dslope H 1) 2).re =
      (taylorCoeff a n - (H 1).re) * (2 - σ) ^ n := by
  have hc : (n ! : ℂ)⁻¹ * n ! = 1 := inv_mul_cancel₀ (Nat.cast_ne_zero.mpr n.factorial_ne_zero)
  have he : ((-1 : ℂ) ^ n) * (-1) ^ n = 1 := by rw [← mul_pow]; simp
  have hσ2 : ((σ : ℂ) - 2) ^ n = (-1) ^ n * (((2 - σ : ℝ) : ℂ)) ^ n := by
    rw [← mul_pow]
    congr 1
    push_cast
    ring
  have hf : (n ! : ℂ)⁻¹ • ((σ : ℂ) - 2) ^ n • iteratedDeriv n (dslope H 1) 2 =
      ((n ! : ℂ)⁻¹ * ((-1) ^ n * iteratedDeriv n (LSeries a) 2) - H 1) *
        ((2 - σ : ℝ) : ℂ) ^ n := by
    simp only [smul_eq_mul]
    rw [iteratedDeriv_dslope_eq hH hHa, hσ2]
    linear_combination (-(H 1) * ((2 - σ : ℝ) : ℂ) ^ n * (-1) ^ n * (-1) ^ n) * hc +
      (-(H 1) * ((2 - σ : ℝ) : ℂ) ^ n) * he
  rw [hf, ← ofReal_pow, re_mul_ofReal, sub_re, taylorCoeff]

/-- The first `N` Taylor terms: all coefficients of `LSeries a` are nonnegative, the first is at
least `1`, and the terms in `H(1)` form a geometric sum. -/
private lemma le_sum_re_taylor_term (ha : 0 ≤ a) (ha₁ : a 1 = 1)
    (habs : LSeries.abscissaOfAbsConv a ≤ (1 : ℝ)) (hH : Differentiable ℂ H)
    (hHa : ∀ s : ℂ, 1 < s.re → H s = (s - 1) * LSeries a s) {σ : ℝ} (hσ₁ : σ < 1) {N : ℕ}
    (hN : N ≠ 0) :
    1 - (H 1).re * (((2 - σ) ^ N - 1) / (1 - σ)) ≤
      ∑ n ∈ Finset.range N,
        ((n ! : ℂ)⁻¹ • ((σ : ℂ) - 2) ^ n • iteratedDeriv n (dslope H 1) 2).re := by
  have ht : 0 ≤ 2 - σ := by linarith
  have hgeom : ∑ n ∈ Finset.range N, (2 - σ) ^ n = ((2 - σ) ^ N - 1) / (1 - σ) := by
    rw [geom_sum_eq (by linarith)]
    congr 1
    ring
  have hsum : 1 ≤ ∑ n ∈ Finset.range N, taylorCoeff a n * (2 - σ) ^ n := by
    have h := Finset.single_le_sum (f := fun n ↦ taylorCoeff a n * (2 - σ) ^ n)
      (fun n _ ↦ mul_nonneg (taylorCoeff_nonneg ha habs n) (pow_nonneg ht n))
      (Finset.mem_range.mpr (Nat.pos_of_ne_zero hN))
    simp only [pow_zero, mul_one] at h
    exact (one_le_taylorCoeff_zero ha ha₁ habs).trans h
  simp only [re_taylor_term_eq hH hHa, sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum, hgeom]
  linarith

private lemma one_le_of_forall_closedBall_norm_le (ha : 0 ≤ a) (ha₁ : a 1 = 1)
    (habs : LSeries.abscissaOfAbsConv a ≤ (1 : ℝ))
    (hHa : ∀ s : ℂ, 1 < s.re → H s = (s - 1) * LSeries a s) {B : ℝ}
    (hB : ∀ s ∈ closedBall (2 : ℂ) (3 / 2), ‖H s‖ ≤ B) : 1 ≤ B := by
  have h2 : ‖H 2‖ ≤ B := hB 2 (mem_closedBall_self (by norm_num))
  rw [hHa 2 (by simp), show (2 : ℂ) - 1 = 1 by norm_num, one_mul] at h2
  have h1 := one_le_taylorCoeff_zero ha ha₁ habs
  simp only [taylorCoeff, iteratedDeriv_zero, pow_zero, Nat.factorial_zero, Nat.cast_one, inv_one,
    one_mul] at h1
  exact h1.trans ((re_le_norm _).trans h2)

/-- The value `H(1)` is the right-hand limit at `1` of the nonnegative quantities
`(x - 1) F(x)`. -/
private lemma re_apply_one_nonneg (ha : 0 ≤ a) (ha₁ : a 1 = 1)
    (habs : LSeries.abscissaOfAbsConv a ≤ (1 : ℝ)) (hH : Differentiable ℂ H)
    (hHa : ∀ s : ℂ, 1 < s.re → H s = (s - 1) * LSeries a s) : 0 ≤ (H 1).re := by
  have hc : ContinuousWithinAt (fun x : ℝ ↦ (H x).re) (Set.Ioi 1) 1 :=
    (continuous_re.comp (hH.continuous.comp continuous_ofReal)).continuousWithinAt
  rw [← ofReal_one]
  refine ge_of_tendsto hc.tendsto <| eventually_nhdsWithin_of_forall fun x hx ↦ ?_
  have hx' : (1 : ℝ) < x := hx
  have hpos : 0 < LSeries a x :=
    LSeries.positive ha (by simp [ha₁]) (habs.trans_lt (EReal.coe_lt_coe_iff.mpr hx'))
  rw [hHa x (by simpa using hx'), ← ofReal_one, ← ofReal_sub, re_ofReal_mul]
  exact mul_nonneg (by linarith) (Complex.le_def.mp hpos.le).1

/-- **Estermann's inequality.** Let `F = LSeries a` have nonnegative coefficients with `a 1 = 1`,
let `H(s) = (s - 1) F(s)` extend to an entire function, and let `B` bound `‖H‖` on the disc
`|s - 2| ≤ 3/2`. Then for `7/8 ≤ σ < 1` and every `N ≠ 0`, the value `H(σ) / (σ - 1)` of the
continued `F` is bounded below by `1 - 16 B (3/4)^N - H(1) (2 - σ)^N / (1 - σ)`.

Real parts are taken so that the statement needs no assumption that `H` is real on the real
axis. -/
theorem estermann_inequality (ha : 0 ≤ a) (ha₁ : a 1 = 1)
    (habs : LSeries.abscissaOfAbsConv a ≤ (1 : ℝ)) (hH : Differentiable ℂ H)
    (hHa : ∀ s : ℂ, 1 < s.re → H s = (s - 1) * LSeries a s) {B : ℝ}
    (hB : ∀ s ∈ closedBall (2 : ℂ) (3 / 2), ‖H s‖ ≤ B) {σ : ℝ} (hσ : 7 / 8 ≤ σ) (hσ₁ : σ < 1)
    {N : ℕ} (hN : N ≠ 0) :
    1 - 16 * B * (3 / 4) ^ N - (H 1).re * (2 - σ) ^ N / (1 - σ) ≤ (H σ).re / (σ - 1) := by
  have htail := norm_sub_le_of_geometric_bound_of_hasSum (r := 3 / 4) (by norm_num)
    (norm_taylor_term_dslope_le hH hB hσ hσ₁) (hasSum_taylorSeries_of_entire
      (hH.dslope 1) 2 (σ : ℂ)) N
  have hG : (∑ n ∈ Finset.range N,
      ((n ! : ℂ)⁻¹ • ((σ : ℂ) - 2) ^ n • iteratedDeriv n (dslope H 1) 2).re) -
      16 * B * (3 / 4) ^ N ≤ (dslope H 1 σ).re := by
    have h := (re_le_norm _).trans htail
    rw [sub_re, re_sum, show 4 * B * (3 / 4) ^ N / (1 - 3 / 4) = 16 * B * (3 / 4) ^ N by ring] at h
    linarith
  have hsum := le_sum_re_taylor_term ha ha₁ habs hH hHa hσ₁ hN
  have hHσ : H σ = H 1 + ((σ - 1 : ℝ) : ℂ) * dslope H 1 σ := by
    rw [ofReal_sub, ofReal_one, ← smul_eq_mul, sub_smul_dslope]
    ring
  have hd : σ - 1 ≠ 0 := by linarith
  have hd' : 1 - σ ≠ 0 := by linarith
  have heq : (H σ).re / (σ - 1) = (dslope H 1 σ).re - (H 1).re / (1 - σ) := by
    rw [hHσ, add_re, re_ofReal_mul]
    field_simp
    ring
  have hcancel : (H 1).re * (((2 - σ) ^ N - 1) / (1 - σ)) + (H 1).re / (1 - σ) =
      (H 1).re * (2 - σ) ^ N / (1 - σ) := by
    field_simp
    ring
  rw [heq]
  linarith

/-- A truncation point `N` of the Taylor expansion that makes the error of
`TauCeti.LSeries.estermann_inequality` at most `1/2`, at the cost of a power of `32 B`. -/
private lemma exists_truncation {B σ : ℝ} (hB₁ : 1 ≤ B) (hσ : 7 / 8 ≤ σ) (hσ₁ : σ < 1) :
    ∃ N : ℕ, N ≠ 0 ∧ 16 * B * (3 / 4) ^ N ≤ 1 / 2 ∧
      (2 - σ) ^ N ≤ 2 * (32 * B) ^ (4 * (1 - σ)) := by
  have hd : 0 < 1 - σ := by linarith
  set L := Real.log (32 * B)
  have hL : 0 < L := Real.log_pos (by linarith)
  set l := Real.log (4 / 3)
  have hl : 1 / 4 ≤ l := by
    have h := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 4 / 3 by norm_num)
    norm_num at h ⊢
    linarith
  have hl₀ : 0 < l := by linarith
  have hNl : L ≤ ⌈L / l⌉₊ * l := (div_le_iff₀ hl₀).mp (Nat.le_ceil _)
  have hNu : (⌈L / l⌉₊ : ℝ) ≤ 4 * L + 1 := by
    have h := Nat.ceil_lt_add_one (div_nonneg hL.le hl₀.le)
    have h' : L / l ≤ 4 * L := by
      rw [div_le_iff₀ hl₀]
      nlinarith
    linarith
  refine ⟨⌈L / l⌉₊, (Nat.ceil_pos.mpr (div_pos hL hl₀)).ne', ?_, ?_⟩
  · have hpow : 32 * B ≤ (4 / 3 : ℝ) ^ ⌈L / l⌉₊ := by
      refine (Real.log_le_log_iff (by positivity) (by positivity)).mp ?_
      rwa [Real.log_pow]
    have hmul : (3 / 4 : ℝ) ^ ⌈L / l⌉₊ * (4 / 3) ^ ⌈L / l⌉₊ = 1 := by
      rw [← mul_pow]
      norm_num
    have hpos : (0 : ℝ) < (3 / 4) ^ ⌈L / l⌉₊ := by positivity
    nlinarith
  · have hexp : Real.exp (1 - σ) ≤ 2 := by
      have h := Real.one_sub_inv_le_log_of_pos (two_pos (α := ℝ))
      exact (Real.le_log_iff_exp_le two_pos).mp (by norm_num at h; linarith)
    have hstep : 2 - σ ≤ Real.exp (1 - σ) := by linarith [Real.add_one_le_exp (1 - σ)]
    calc (2 - σ) ^ ⌈L / l⌉₊ ≤ Real.exp (1 - σ) ^ ⌈L / l⌉₊ :=
          pow_le_pow_left₀ (by linarith) hstep _
      _ = Real.exp (⌈L / l⌉₊ * (1 - σ)) := (Real.exp_nat_mul _ _).symm
      _ ≤ Real.exp ((4 * L + 1) * (1 - σ)) := Real.exp_le_exp.mpr (by gcongr)
      _ = Real.exp (1 - σ) * Real.exp (L * (4 * (1 - σ))) := by
        rw [← Real.exp_add]
        ring_nf
      _ ≤ 2 * (32 * B) ^ (4 * (1 - σ)) := by
        rw [Real.rpow_def_of_pos (by positivity)]
        gcongr

/-- **Estermann's inequality**, with the truncation point optimized: under the assumptions of
`TauCeti.LSeries.estermann_inequality`, the continued `F(σ) = H(σ) / (σ - 1)` is at least
`1/2 - 2 H(1) (32 B)^{4 (1 - σ)} / (1 - σ)`. -/
theorem estermann_inequality_rpow (ha : 0 ≤ a) (ha₁ : a 1 = 1)
    (habs : LSeries.abscissaOfAbsConv a ≤ (1 : ℝ)) (hH : Differentiable ℂ H)
    (hHa : ∀ s : ℂ, 1 < s.re → H s = (s - 1) * LSeries a s) {B : ℝ}
    (hB : ∀ s ∈ closedBall (2 : ℂ) (3 / 2), ‖H s‖ ≤ B) {σ : ℝ} (hσ : 7 / 8 ≤ σ) (hσ₁ : σ < 1) :
    1 / 2 - 2 * (H 1).re * (32 * B) ^ (4 * (1 - σ)) / (1 - σ) ≤ (H σ).re / (σ - 1) := by
  obtain ⟨N, hN, hsmall, hpow⟩ :=
    exists_truncation (one_le_of_forall_closedBall_norm_le ha ha₁ habs hHa hB) hσ hσ₁
  have hres := re_apply_one_nonneg ha ha₁ habs hH hHa
  have hd : 0 < 1 - σ := by linarith
  have hmain := estermann_inequality ha ha₁ habs hH hHa hB hσ hσ₁ hN
  have hle : (H 1).re * (2 - σ) ^ N / (1 - σ) ≤
      2 * (H 1).re * (32 * B) ^ (4 * (1 - σ)) / (1 - σ) := by
    rw [mul_comm 2, mul_assoc]
    gcongr
  linarith

/-- A point `σ ∈ [7/8, 1)` at which the continued `F(σ) = H(σ) / (σ - 1)` is nonpositive forces the
residue `H(1)` of `F` to be at least `(1 - σ) / (4 (32 B)^{4 (1 - σ)})`. -/
theorem estermann_lower_bound (ha : 0 ≤ a) (ha₁ : a 1 = 1)
    (habs : LSeries.abscissaOfAbsConv a ≤ (1 : ℝ)) (hH : Differentiable ℂ H)
    (hHa : ∀ s : ℂ, 1 < s.re → H s = (s - 1) * LSeries a s) {B : ℝ}
    (hB : ∀ s ∈ closedBall (2 : ℂ) (3 / 2), ‖H s‖ ≤ B) {σ : ℝ} (hσ : 7 / 8 ≤ σ) (hσ₁ : σ < 1)
    (hF : (H σ).re / (σ - 1) ≤ 0) :
    (1 - σ) / (4 * (32 * B) ^ (4 * (1 - σ))) ≤ (H 1).re := by
  have hB₁ : 1 ≤ B := one_le_of_forall_closedBall_norm_le ha ha₁ habs hHa hB
  have hd : 0 < 1 - σ := by linarith
  have hX : 0 < (32 * B) ^ (4 * (1 - σ)) := Real.rpow_pos_of_pos (by linarith) _
  have h := (estermann_inequality_rpow ha ha₁ habs hH hHa hB hσ hσ₁).trans hF
  rw [sub_nonpos, le_div_iff₀ hd] at h
  rw [div_le_iff₀ (by positivity)]
  linarith

end TauCeti.LSeries
