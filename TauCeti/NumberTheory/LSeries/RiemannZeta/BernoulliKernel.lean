/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.MellinTransform
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.NumberTheory.Bernoulli
public import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import TauCeti.Analysis.SpecialFunctions.Exp.DividedDifference

/-!
# The Bernoulli kernel `t / (exp t - 1)`

The Bernoulli kernel `β(t) = t / (exp t - 1)` is the exponential generating function of the
Bernoulli numbers `B_n` (with `B₁ = -1/2`). Its expression has a removable singularity at `t = 0`;
we define it as the inverse of the divided difference `(exp t - 1) / t` of the exponential at
`0`, which is positive on all of `ℝ` and equals `1` at `0`. This gives one real analytic function
with `β(0) = 1`, so no case split on `t = 0` enters its analytic theory.

The kernel is the basic test function for the Mellin-transform approach to special values of the
Riemann zeta function: its Mellin transform is `Γ(s + 1) ζ(s + 1)` on `Re s > 0`, its derivatives
at `0` are the Bernoulli numbers, and its derivatives decay exponentially at `+∞`. Dividing the
Mellin transform by `Γ(s)` gives `s ζ(s + 1)`, whose removable singularity at `s = 0` has value
`1`; this normalized Mellin transform is entire.

## Main definitions

* `TauCeti.bernoulliKernel`: the function `t ↦ t / (exp t - 1)`, with value `1` at `0`.

## Main results

* `TauCeti.bernoulliKernel_of_ne_zero`, `TauCeti.bernoulliKernel_zero`: its values.
* `TauCeti.exp_sub_one_mul_bernoulliKernel`: `(exp t - 1) β(t) = t` for every real `t`.
* `TauCeti.analyticOnNhd_bernoulliKernel`: the kernel is real analytic on `ℝ`.
* `TauCeti.eq_bernoulliKernel_of_continuousAt`: it is the only extension of `t / (exp t - 1)`
  continuous at `0`.
* `TauCeti.iteratedDeriv_bernoulliKernel_zero`: `β⁽ⁿ⁾(0) = B_n`.
* `TauCeti.isBigO_iteratedDeriv_bernoulliKernel`: `β⁽ⁿ⁾(t) = O(exp (-c t))` as `t → ∞`, for every
  `c < 1`.
* `TauCeti.mellin_bernoulliKernel`: `M(β, s) = Γ(s + 1) ζ(s + 1)` for `Re s > 0`.
* `TauCeti.bernoulliKernel_normalizedMellin`: `M(β, s) / Γ(s)` extends to an entire function
  equal to `s ζ(s + 1)` for `s ≠ 0` and to `1` at `s = 0`.

## References

* J. Rodrigues Jacinto and C. Williams, *An introduction to p-adic L-functions*, Essential Number
  Theory **4** (2025), 101–216, §2, Lemmas 2.6–2.7.
-/

public section

open Filter Asymptotics Polynomial
open scoped Topology

namespace TauCeti

/-- The Bernoulli kernel `t ↦ t / (exp t - 1)`, defined on all of `ℝ` as the inverse of the
divided difference `dslope exp 0` of the exponential at `0`, so that its value at `0` is `1`. -/
noncomputable def bernoulliKernel (t : ℝ) : ℝ :=
  (dslope Real.exp 0 t)⁻¹

theorem bernoulliKernel_def (t : ℝ) : bernoulliKernel t = (dslope Real.exp 0 t)⁻¹ := (rfl)

/-- The Bernoulli kernel has value `1` at its removable point. -/
@[simp]
theorem bernoulliKernel_zero : bernoulliKernel 0 = 1 := by
  simp [bernoulliKernel_def, dslope_same]

/-- Away from `0`, the Bernoulli kernel is `t / (exp t - 1)`. -/
theorem bernoulliKernel_of_ne_zero {t : ℝ} (ht : t ≠ 0) :
    bernoulliKernel t = t / (Real.exp t - 1) := by
  rw [bernoulliKernel_def, dslope_of_ne _ ht, slope_def_field, Real.exp_zero, sub_zero, inv_div]

/-- The Bernoulli kernel as a piecewise expression. -/
theorem bernoulliKernel_eq_ite (t : ℝ) :
    bernoulliKernel t = if t = 0 then 1 else t / (Real.exp t - 1) := by
  split_ifs with ht
  · rw [ht, bernoulliKernel_zero]
  · exact bernoulliKernel_of_ne_zero ht

/-- The Bernoulli kernel is positive on all of `ℝ`. -/
theorem bernoulliKernel_pos (t : ℝ) : 0 < bernoulliKernel t :=
  inv_pos.2 (Real.dslope_exp_pos 0 t)

/-- The defining identity of the Bernoulli kernel, valid for every real `t`, including `0`. -/
theorem exp_sub_one_mul_bernoulliKernel (t : ℝ) : (Real.exp t - 1) * bernoulliKernel t = t := by
  rcases eq_or_ne t 0 with rfl | ht
  · simp
  · rw [bernoulliKernel_of_ne_zero ht,
      mul_div_cancel₀ _ (sub_ne_zero.2 ((Real.exp_eq_one_iff t).not.2 ht))]

/-- The Bernoulli kernel is real analytic on `ℝ`, including at its removable point `0`. -/
theorem analyticOnNhd_bernoulliKernel : AnalyticOnNhd ℝ bernoulliKernel Set.univ := fun t _ ↦
  ((analyticOnNhd_rexp (u := Set.univ)).dslope 0 t trivial).inv (Real.dslope_exp_pos 0 t).ne'

/-- The Bernoulli kernel is smooth, indeed real analytic (`n = ω`). -/
theorem contDiff_bernoulliKernel {n : WithTop ℕ∞} : ContDiff ℝ n bernoulliKernel :=
  analyticOnNhd_bernoulliKernel.contDiff

/-- The Bernoulli kernel is continuous. -/
theorem continuous_bernoulliKernel : Continuous bernoulliKernel :=
  (contDiff_bernoulliKernel (n := 0)).continuous

/-- The Bernoulli kernel is the only extension of `t ↦ t / (exp t - 1)` from `t ≠ 0` to `ℝ` that
is continuous at `0`. -/
theorem eq_bernoulliKernel_of_continuousAt {g : ℝ → ℝ} (hg : ContinuousAt g 0)
    (h : ∀ t, t ≠ 0 → g t = t / (Real.exp t - 1)) : g = bernoulliKernel := by
  have hne : ∀ t, t ≠ 0 → g t = bernoulliKernel t := fun t ht ↦
    (h t ht).trans (bernoulliKernel_of_ne_zero ht).symm
  funext t
  rcases eq_or_ne t 0 with rfl | ht
  · have h₁ : Tendsto g (𝓝[≠] 0) (𝓝 (g 0)) := hg.tendsto.mono_left nhdsWithin_le_nhds
    refine tendsto_nhds_unique h₁ ?_
    refine (continuous_bernoulliKernel.tendsto 0).mono_left nhdsWithin_le_nhds |>.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t ht using (hne t ht).symm
  · exact hne t ht

/-- The derivatives of the Bernoulli kernel at `0` are the Bernoulli numbers (with
`B₁ = -1/2`): `t / (exp t - 1)` is their exponential generating function. -/
theorem iteratedDeriv_bernoulliKernel_zero (n : ℕ) :
    iteratedDeriv n bernoulliKernel 0 = bernoulli n := by
  -- Differentiating `β(t) exp t = t + β(t)` `m + 1` times at `0` gives the recursion
  -- `∑_{i ≤ m} (m+1 choose i) β⁽ⁱ⁾(0) = [m = 0]` satisfied by the Bernoulli numbers.
  have hrec (m : ℕ) : ∑ i ∈ Finset.range (m + 1),
      ((m + 1).choose i : ℝ) * iteratedDeriv i bernoulliKernel 0 = if m + 1 = 1 then 1 else 0 := by
    have hfun : (fun t ↦ bernoulliKernel t * Real.exp t) = fun t ↦ t + bernoulliKernel t := by
      funext t
      linear_combination exp_sub_one_mul_bernoulliKernel t
    have h := congrArg (fun f ↦ iteratedDeriv (m + 1) f 0) hfun
    rw [iteratedDeriv_fun_mul contDiff_bernoulliKernel.contDiffAt Real.contDiff_exp.contDiffAt,
      iteratedDeriv_fun_add (f := fun t ↦ t) (g := bernoulliKernel) (by fun_prop)
        contDiff_bernoulliKernel.contDiffAt,
      iteratedDeriv_fun_id_zero, Finset.sum_range_succ] at h
    have hexp (k : ℕ) : iteratedDeriv k Real.exp 0 = 1 := by
      rw [iteratedDeriv_eq_iterate, Real.iter_deriv_exp, Real.exp_zero]
    simp only [hexp, mul_one, Nat.choose_self, Nat.cast_one, one_mul] at h
    linarith
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    have h := hrec n
    have hB := congrArg (fun q : ℚ ↦ (q : ℝ)) (sum_bernoulli (n + 1))
    have hsum : ∑ i ∈ Finset.range n, ((n + 1).choose i : ℝ) * iteratedDeriv i bernoulliKernel 0 =
        ∑ i ∈ Finset.range n, ((n + 1).choose i : ℝ) * bernoulli i :=
      Finset.sum_congr rfl fun i hi ↦ by rw [ih i (Finset.mem_range.1 hi)]
    rw [Finset.sum_range_succ, hsum, Nat.choose_succ_self_right] at h
    rw [Finset.sum_range_succ, Nat.choose_succ_self_right] at hB
    apply mul_left_cancel₀ (by positivity : (n + 1 : ℝ) ≠ 0)
    push_cast at h hB
    split_ifs at h hB <;> push_cast at hB <;> linarith

/-! ### Exponential decay of the derivatives -/

/-- The derivative of `g = (exp t - 1)⁻¹` is `-(g + g²)`. -/
private theorem hasDerivAt_inv_exp_sub_one {t : ℝ} (ht : t ≠ 0) :
    HasDerivAt (fun s ↦ (Real.exp s - 1)⁻¹)
      (-((Real.exp t - 1)⁻¹ + (Real.exp t - 1)⁻¹ ^ 2)) t := by
  have hne : Real.exp t - 1 ≠ 0 := sub_ne_zero.2 ((Real.exp_eq_one_iff t).not.2 ht)
  convert ((Real.hasDerivAt_exp t).sub_const 1).inv hne using 1
  field_simp
  ring

/-- The polynomial `D A = -(1 + X) (A + X A')`, chosen so that the derivative of `g A(g)` is
`g (D A)(g)` for `g = (exp t - 1)⁻¹`. -/
private noncomputable def derivPoly (A : ℝ[X]) : ℝ[X] :=
  -((1 + X) * (A + X * derivative A))

private theorem hasDerivAt_mul_eval_inv_exp_sub_one {t : ℝ} (ht : t ≠ 0) (A : ℝ[X]) :
    HasDerivAt (fun s ↦ (Real.exp s - 1)⁻¹ * A.eval (Real.exp s - 1)⁻¹)
      ((Real.exp t - 1)⁻¹ * (derivPoly A).eval (Real.exp t - 1)⁻¹) t := by
  have hg := hasDerivAt_inv_exp_sub_one ht
  convert hg.fun_mul ((A.hasDerivAt _).comp t hg) using 1
  · rfl
  · simp only [derivPoly, eval_neg, eval_mul, eval_add, eval_one, eval_X, Function.comp_apply]
    ring

/-- Away from `0`, the `n`-th derivative of the Bernoulli kernel has the form
`t g A(g) + g B(g)` for polynomials `A`, `B` and `g = (exp t - 1)⁻¹`. -/
private theorem exists_iteratedDeriv_bernoulliKernel_eq (n : ℕ) :
    ∃ A B : ℝ[X], ∀ t, 0 < t → iteratedDeriv n bernoulliKernel t =
      t * ((Real.exp t - 1)⁻¹ * A.eval (Real.exp t - 1)⁻¹) +
        (Real.exp t - 1)⁻¹ * B.eval (Real.exp t - 1)⁻¹ := by
  induction n with
  | zero =>
    refine ⟨1, 0, fun t ht ↦ ?_⟩
    simp [bernoulliKernel_of_ne_zero ht.ne', div_eq_mul_inv]
  | succ n ih =>
    obtain ⟨A, B, h⟩ := ih
    refine ⟨derivPoly A, A + derivPoly B, fun t ht ↦ ?_⟩
    have heq : iteratedDeriv n bernoulliKernel =ᶠ[𝓝 t] fun s ↦
        s * ((Real.exp s - 1)⁻¹ * A.eval (Real.exp s - 1)⁻¹) +
          (Real.exp s - 1)⁻¹ * B.eval (Real.exp s - 1)⁻¹ := by
      filter_upwards [Ioi_mem_nhds ht] with s hs using h s hs
    rw [iteratedDeriv_succ, heq.deriv_eq]
    refine (((hasDerivAt_id t).mul (hasDerivAt_mul_eval_inv_exp_sub_one ht.ne' A)).add
      (hasDerivAt_mul_eval_inv_exp_sub_one ht.ne' B)).deriv.trans ?_
    simp only [id, eval_add]
    ring

/-- `(exp t - 1)⁻¹ = O(exp (-t))` as `t → ∞`. -/
private theorem isBigO_inv_exp_sub_one :
    (fun t ↦ (Real.exp t - 1)⁻¹) =O[atTop] fun t ↦ Real.exp (-t) := by
  refine IsBigO.of_bound 2 ?_
  filter_upwards [eventually_ge_atTop (Real.log 2)] with t ht
  have h2 : 2 ≤ Real.exp t := (Real.exp_log two_pos).symm.le.trans (Real.exp_le_exp.2 ht)
  have hpos : 0 < Real.exp t - 1 := by linarith
  rw [Real.norm_of_nonneg (inv_pos.2 hpos).le, Real.norm_of_nonneg (Real.exp_pos _).le,
    Real.exp_neg]
  calc (Real.exp t - 1)⁻¹ ≤ (Real.exp t / 2)⁻¹ := inv_anti₀ (by positivity) (by linarith)
    _ = 2 * (Real.exp t)⁻¹ := by rw [inv_div, div_eq_mul_inv]

/-- The functions `t g A(g) + g B(g)` decay like `exp (-c t)` for every `c < 1`. -/
private theorem isBigO_mul_eval_inv_exp_sub_one (A B : ℝ[X]) {c : ℝ} (hc : c < 1) :
    (fun t ↦ t * ((Real.exp t - 1)⁻¹ * A.eval (Real.exp t - 1)⁻¹) +
      (Real.exp t - 1)⁻¹ * B.eval (Real.exp t - 1)⁻¹) =O[atTop] fun t ↦ Real.exp (-(c * t)) := by
  have hg : Tendsto (fun t ↦ (Real.exp t - 1)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right _ (-1) Real.tendsto_exp_atTop)
  have hP (P : ℝ[X]) : (fun t ↦ (Real.exp t - 1)⁻¹ * P.eval (Real.exp t - 1)⁻¹) =O[atTop]
      fun t ↦ Real.exp (-t) := by
    have h1 : (fun t ↦ P.eval (Real.exp t - 1)⁻¹) =O[atTop] fun _ ↦ (1 : ℝ) :=
      ((P.continuous.tendsto 0).comp hg).isBigO_one ℝ
    simpa using isBigO_inv_exp_sub_one.mul h1
  -- `t exp (-t) = O(exp (-c t))` because `t = o(exp ((1 - c) t))`.
  have hlin : (fun t : ℝ ↦ t * Real.exp (-t)) =O[atTop] fun t ↦ Real.exp (-(c * t)) := by
    have h := (isLittleO_pow_exp_pos_mul_atTop 1 (sub_pos.2 hc)).isBigO.mul
      (isBigO_refl (fun t : ℝ ↦ Real.exp (-t)) atTop)
    refine h.congr (fun t ↦ by simp) fun t ↦ ?_
    rw [← Real.exp_add]
    ring_nf
  have hexp : (fun t : ℝ ↦ Real.exp (-t)) =O[atTop] fun t ↦ Real.exp (-(c * t)) := by
    refine IsBigO.of_bound 1 ?_
    filter_upwards [eventually_ge_atTop 0] with t ht
    simp only [Real.norm_eq_abs, Real.abs_exp, one_mul, Real.exp_le_exp]
    nlinarith
  exact (((isBigO_refl (fun t : ℝ ↦ t) atTop).mul (hP A)).trans hlin).add ((hP B).trans hexp)

/-- Every derivative of the Bernoulli kernel decays exponentially at `+∞`, with any rate
`c < 1`. The rate `1` itself is not attained, because of the polynomial factor `t`. -/
theorem isBigO_iteratedDeriv_bernoulliKernel (n : ℕ) {c : ℝ} (hc : c < 1) :
    iteratedDeriv n bernoulliKernel =O[atTop] fun t ↦ Real.exp (-(c * t)) := by
  obtain ⟨A, B, h⟩ := exists_iteratedDeriv_bernoulliKernel_eq n
  refine (isBigO_mul_eval_inv_exp_sub_one A B hc).congr' ?_ EventuallyEq.rfl
  filter_upwards [eventually_gt_atTop 0] with t ht using (h t ht).symm

/-! ### The Mellin transform -/

/-- For `t > 0`, the geometric expansion `(exp t - 1)⁻¹ = ∑_{k ≥ 0} exp (-((k + 1) t))`. -/
private theorem hasSum_exp_neg_mul {t : ℝ} (ht : 0 < t) :
    HasSum (fun k : ℕ ↦ Real.exp (-((k + 1) * t))) (Real.exp t - 1)⁻¹ := by
  have h1 : 1 < Real.exp t := Real.one_lt_exp_iff.2 ht
  convert (hasSum_geometric_of_lt_one (Real.exp_pos (-t)).le
    (Real.exp_lt_one_iff.2 (neg_neg_of_pos ht))).mul_left (Real.exp (-t)) using 1
  · funext k
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    ring_nf
  · have h2 : Real.exp t - 1 ≠ 0 := by linarith
    rw [Real.exp_neg]
    field_simp

/-- For `t > 0` and complex `s`, the Mellin integrand of the Bernoulli kernel is the sum of the
Gamma integrands `t ^ s exp (-((k + 1) t))`. -/
private theorem hasSum_mellin_integrand {t : ℝ} (ht : 0 < t) (s : ℂ) :
    HasSum (fun k : ℕ ↦ (t : ℂ) ^ (s + 1 - 1) * Complex.exp (-(((k : ℝ) + 1 : ℝ) * t)))
      ((t : ℂ) ^ (s - 1) • (bernoulliKernel t : ℂ)) := by
  have h := (Complex.ofRealCLM.hasSum ((hasSum_exp_neg_mul ht).mul_left t)).mul_left
    ((t : ℂ) ^ (s - 1))
  rw [bernoulliKernel_of_ne_zero ht.ne', div_eq_mul_inv, smul_eq_mul]
  convert h using 1
  · funext k
    have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 ht.ne'
    rw [add_sub_cancel_right, Complex.ofRealCLM_apply]
    push_cast
    nth_rw 1 [show s = s - 1 + 1 by ring]
    rw [Complex.cpow_add _ _ ht', Complex.cpow_one]
    ring
  · simp

/-- The Mellin transform of the Bernoulli kernel is `Γ(s + 1) ζ(s + 1)` on `Re s > 0`. -/
theorem mellin_bernoulliKernel {s : ℂ} (hs : 0 < s.re) :
    mellin (fun t ↦ (bernoulliKernel t : ℂ)) s = Complex.Gamma (s + 1) * riemannZeta (s + 1) := by
  set F : ℕ → ℝ → ℂ := fun k t ↦ (t : ℂ) ^ (s + 1 - 1) * Complex.exp (-(((k : ℝ) + 1 : ℝ) * t))
  have hs1 : 0 < (s + 1).re := by simp; linarith
  have hr (k : ℕ) : (0 : ℝ) < k + 1 := by positivity
  have hI (k : ℕ) : ∫ t in Set.Ioi 0, F k t =
      (1 / (((k : ℝ) + 1 : ℝ) : ℂ)) ^ (s + 1) * Complex.Gamma (s + 1) :=
    Complex.integral_cpow_mul_exp_neg_mul_Ioi hs1 (hr k)
  have hInt (k : ℕ) : MeasureTheory.IntegrableOn (F k) (Set.Ioi 0) := by
    refine MeasureTheory.Integrable.of_integral_ne_zero ?_
    rw [hI k]
    refine mul_ne_zero ?_ (Complex.Gamma_ne_zero_of_re_pos hs1)
    rw [Ne, Complex.cpow_eq_zero_iff]
    simp only [one_div, inv_eq_zero, Complex.ofReal_eq_zero, not_and]
    intro h
    linarith [hr k]
  have hnorm (k : ℕ) : ∫ t in Set.Ioi 0, ‖F k t‖ =
      (1 / ((k : ℝ) + 1)) ^ (s.re + 1) * Real.Gamma (s.re + 1) := by
    rw [← Real.integral_rpow_mul_exp_neg_mul_Ioi (by linarith) (hr k)]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun t ht ↦ ?_
    simp only [F, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht, Complex.norm_exp]
    simp
  have hsum : Summable fun k : ℕ ↦ ∫ t in Set.Ioi 0, ‖F k t‖ := by
    simp_rw [hnorm]
    refine Summable.mul_right _ ?_
    have h := (summable_nat_add_iff 1).2 (Real.summable_nat_rpow_inv.2 (by linarith :
      1 < s.re + 1))
    refine h.congr fun k ↦ ?_
    rw [one_div, Real.inv_rpow (by positivity)]
    push_cast
    rfl
  rw [mellin, ← MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
      fun t ht ↦ (hasSum_mellin_integrand ht s).tsum_eq,
    ← MeasureTheory.integral_tsum_of_summable_integral_norm hInt hsum]
  simp_rw [hI]
  rw [tsum_mul_right, zeta_eq_tsum_one_div_nat_add_one_cpow (by simp; linarith), mul_comm]
  congr 1
  refine tsum_congr fun k ↦ ?_
  have harg : ((k : ℂ) + 1).arg ≠ Real.pi := by
    rw [show (k : ℂ) + 1 = (((k : ℝ) + 1 : ℝ) : ℂ) by push_cast; rfl,
      Complex.arg_ofReal_of_nonneg (hr k).le]
    exact Real.pi_pos.ne
  push_cast
  rw [one_div, one_div, Complex.inv_cpow _ _ harg]

/-- The normalized Mellin transform `M(β, s) / Γ(s)` of the Bernoulli kernel extends to an
entire function, equal to `s ζ(s + 1)` for `s ≠ 0` and to `1` at the removable point `s = 0`
(the residue of `ζ` at `1`). The extension is `riemannZeta₁ (s + 1)`, where Mathlib's
`riemannZeta₁` is the entire completion of `(s - 1) ζ(s)`. -/
theorem bernoulliKernel_normalizedMellin :
    ∃ F : ℂ → ℂ, Differentiable ℂ F ∧
      (∀ s : ℂ, 0 < s.re →
        F s = mellin (fun t ↦ (bernoulliKernel t : ℂ)) s / Complex.Gamma s) ∧
      (∀ s : ℂ, s ≠ 0 → F s = s * riemannZeta (s + 1)) ∧ F 0 = 1 := by
  have hF_ne (s : ℂ) (hs : s ≠ 0) : riemannZeta₁ (s + 1) = s * riemannZeta (s + 1) := by
    rw [riemannZeta_eq_inv_sub_mul (by simpa using hs), add_sub_cancel_right,
      mul_inv_cancel_left₀ hs]
  refine ⟨fun s ↦ riemannZeta₁ (s + 1),
    differentiable_riemannZeta₁.comp (differentiable_id.add_const 1), fun s hs ↦ ?_, hF_ne,
    by simp [riemannZeta₁_one]⟩
  have hs0 : s ≠ 0 := fun h ↦ by simp [h] at hs
  beta_reduce
  rw [hF_ne s hs0, mellin_bernoulliKernel hs, Complex.Gamma_add_one s hs0, mul_assoc,
    mul_div_assoc, mul_div_cancel_left₀ _ (Complex.Gamma_ne_zero_of_re_pos hs)]

end TauCeti
