/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
module

public import TauCeti.Analysis.Complex.GrowthOrder
import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import TauCeti.Analysis.Complex.Liouville
public import TauCeti.Analysis.Complex.BorelCaratheodory
public import TauCeti.Analysis.Complex.BranchLogRoot
public import TauCeti.Analysis.Convex.SimplyConnected

/-!
# Polynomial exponents of finite-order exponentials

An entire function whose exponential has order at most any real `ρ` is a polynomial of
natural degree at most `⌊ρ⌋₊`, and the exponential of every such polynomial has that order
bound. Consequently, every zero-free entire function of order at most `ρ` is the exponential
of such a polynomial. This is the zero-free case of Hadamard factorization. At order at most
one the exponent is affine; its linear coefficient is the logarithmic derivative at zero.
For negative `ρ`, the natural floor is zero, so the exponent is constant. For functions with
zeros, comparison with a canonical product additionally requires a growth bound on the quotient.

## Main results

* `TauCeti.OrderLE.exists_eq_polynomial_eval_of_cexp` gives the polynomial exponent and its
  floor degree bound at every real order.
* `TauCeti.OrderLE.eq_affine_of_cexp` identifies the exponent by its value and derivative
  at zero.
* `TauCeti.OrderLE.exists_eq_cexp_add_logDeriv_mul` writes a zero-free entire function of
  order at most one as `exp (a + b z)`, with `b` its logarithmic derivative at zero.
* `TauCeti.OrderLE.exists_eq_cexp_affine_of_forall_ne_zero` classifies zero-free entire
  functions of order at most one.
* `TauCeti.orderLE_cexp_polynomial_eval_iff` gives the exact natural-degree criterion for a
  polynomial exponential at every real order.
* `TauCeti.orderLE_cexp_comp_iff` characterizes the entire exponents whose exponential has
  order at most `ρ`; `TauCeti.orderLE_cexp_comp_one_iff` is the affine characterization.
* `TauCeti.OrderLE.exists_eq_cexp_polynomial_eval_of_forall_ne_zero` classifies zero-free entire
  functions at every real order.

## References

* H. Davenport, *Multiplicative Number Theory*, 3rd ed., Chapter 11.
-/

public section

open Complex Filter Bornology Topology Asymptotics

namespace TauCeti

/-- An entire exponent whose exponential has order at most `ρ : ℝ` is a polynomial of
natural degree at most `⌊ρ⌋₊`. -/
theorem OrderLE.exists_eq_polynomial_eval_of_cexp {H : ℂ → ℂ} {ρ : ℝ}
    (h : OrderLE (fun z ↦ exp (H z)) ρ) (hH : Differentiable ℂ H) :
    ∃ P : Polynomial ℂ, P.natDegree ≤ ⌊ρ⌋₊ ∧ H = P.eval := by
  have htop : max ρ 0 < (⌊ρ⌋₊ : ℝ) + 1 :=
    max_lt (Nat.lt_floor_add_one ρ) (by positivity)
  obtain ⟨p, hp, hpn⟩ := exists_between htop
  have hG := hH.isBigO_of_cexp_isBigO ((le_max_right ρ 0).trans hp.le)
    (h.isBigO ((le_max_left ρ 0).trans_lt hp))
  have hr : (fun r : ℝ ↦ r ^ p) =o[atTop] (fun r : ℝ ↦ r ^ (⌊ρ⌋₊ + 1)) := by
    have he := (isLittleO_exp_mul_rpow_of_lt 0 hpn).comp_tendsto Real.tendsto_log_atTop
    apply he.congr'
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
      simp only [Function.comp_apply, Real.rpow_zero, mul_one, Real.rpow_def_of_pos hr,
        mul_comm p]
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
      rw [Function.comp_apply, ← Real.rpow_natCast, Real.rpow_def_of_pos hr]
      congr 1
      push_cast
      ring
  have hlo : H =o[cobounded ℂ] (fun z : ℂ ↦ z ^ (⌊ρ⌋₊ + 1)) := by
    apply hG.trans_isLittleO
    rw [← isLittleO_norm_right]
    simpa only [Function.comp_def, norm_pow] using hr.comp_tendsto
      (tendsto_norm_cobounded_atTop : Tendsto (fun z : ℂ ↦ ‖z‖) (cobounded ℂ) atTop)
  exact hH.exists_eq_polynomial_eval_of_isLittleO_pow hlo

/-- The exponential of a polynomial has order at most `ρ` exactly when its natural degree
is at most `⌊ρ⌋₊`. This includes all negative `ρ`: every constant has every such order. -/
@[simp]
theorem orderLE_cexp_polynomial_eval_iff {P : Polynomial ℂ} {ρ : ℝ} :
    OrderLE (fun z : ℂ ↦ exp (P.eval z)) ρ ↔ P.natDegree ≤ ⌊ρ⌋₊ := by
  constructor
  · intro h
    obtain ⟨Q, hQ, hPQ⟩ := h.exists_eq_polynomial_eval_of_cexp P.differentiable
    have heq : P = Q := Polynomial.funext fun z ↦ congrFun hPQ z
    simpa only [heq] using hQ
  · intro hP
    by_cases hdeg : P.natDegree = 0
    · rw [Polynomial.eq_C_of_natDegree_eq_zero hdeg]
      simpa only [Polynomial.eval_C] using orderLE_const (exp (P.coeff 0)) ρ
    · exact P.orderLE_cexp_eval.mono ((Nat.le_floor_iff' hdeg).mp hP)

/-- An entire exponent whose exponential has order at most one is affine. -/
theorem OrderLE.eq_affine_of_cexp {H : ℂ → ℂ}
    (h : OrderLE (fun z ↦ exp (H z)) 1) (hH : Differentiable ℂ H) :
    ∀ z, H z = H 0 + deriv H 0 * z := by
  obtain ⟨P, hP, hHP⟩ := h.exists_eq_polynomial_eval_of_cexp hH
  apply hH.eq_affine_of_isLittleO_sq
  rw [hHP]
  exact P.isBigO_cobounded_pow_natDegree.trans_isLittleO
    (isLittleO_pow_pow_cobounded_of_lt (by simpa using Nat.lt_succ_of_le hP))

/-- Every zero-free entire function of order at most `ρ` is the exponential of a polynomial
of natural degree at most `⌊ρ⌋₊`. Constants and negative orders are included. -/
theorem OrderLE.exists_eq_cexp_polynomial_eval_of_forall_ne_zero {f : ℂ → ℂ} {ρ : ℝ}
    (h : OrderLE f ρ) (hf : Differentiable ℂ f) (hf0 : ∀ z, f z ≠ 0) :
    ∃ P : Polynomial ℂ, P.natDegree ≤ ⌊ρ⌋₊ ∧ ∀ z, f z = exp (P.eval z) := by
  obtain ⟨H, hH, heq⟩ := exists_differentiableOn_eqOn_exp_comp
    (convex_univ.isSimplyConnected Set.univ_nonempty) isOpen_univ hf.differentiableOn
    (by simpa only [Set.mem_image, Set.mem_univ, true_and, not_exists] using hf0)
  have he : (fun z ↦ exp (H z)) = f := funext fun z ↦ heq (Set.mem_univ z)
  obtain ⟨P, hP, hHP⟩ :=
    (he.symm ▸ h : OrderLE (fun z ↦ exp (H z)) ρ).exists_eq_polynomial_eval_of_cexp
      (differentiableOn_univ.mp hH)
  exact ⟨P, hP, fun z ↦ (heq (Set.mem_univ z)).symm.trans (congrArg exp (congrFun hHP z))⟩


/-- A zero-free entire function of order at most one has affine exponential form with
linear coefficient given by its logarithmic derivative at zero. -/
theorem OrderLE.exists_eq_cexp_add_logDeriv_mul {f : ℂ → ℂ}
    (h : OrderLE f 1) (hf : Differentiable ℂ f) (hf0 : ∀ z, f z ≠ 0) :
    ∃ a : ℂ, exp a = f 0 ∧ ∀ z, f z = exp (a + logDeriv f 0 * z) := by
  obtain ⟨P, _, hP⟩ := h.exists_eq_cexp_polynomial_eval_of_forall_ne_zero hf hf0
  have heq : Set.EqOn (fun z ↦ exp (P.eval z)) f Set.univ := fun z _ ↦ (hP z).symm
  have he : (fun z ↦ exp (P.eval z)) = f := funext fun z ↦ (hP z).symm
  have hPa := (he.symm ▸ h : OrderLE (fun z ↦ exp (P.eval z)) 1).eq_affine_of_cexp
    P.differentiable
  rw [deriv_eq_logDeriv_of_eqOn_exp_comp isOpen_univ P.differentiable.differentiableOn heq
    (Set.mem_univ 0)] at hPa
  exact ⟨P.eval 0, (hP 0).symm,
    fun z ↦ (hP z).trans (congrArg exp (hPa z))⟩

/-- A zero-free entire function of order at most one is the exponential
of an affine function. -/
theorem OrderLE.exists_eq_cexp_affine_of_forall_ne_zero {f : ℂ → ℂ}
    (h : OrderLE f 1) (hf : Differentiable ℂ f) (hf0 : ∀ z, f z ≠ 0) :
    ∃ a b : ℂ, ∀ z, f z = exp (a + b * z) :=
  let ⟨a, _, ha⟩ := h.exists_eq_cexp_add_logDeriv_mul hf hf0
  ⟨a, logDeriv f 0, ha⟩

/-- The exponential of an entire function has order at most one exactly when its exponent
is affine. -/
theorem orderLE_cexp_comp_one_iff {H : ℂ → ℂ} (hH : Differentiable ℂ H) :
    OrderLE (fun z ↦ exp (H z)) 1 ↔ ∃ a b : ℂ, ∀ z, H z = a + b * z := by
  constructor
  · intro h
    exact ⟨H 0, deriv H 0, h.eq_affine_of_cexp hH⟩
  · rintro ⟨a, b, h⟩
    have he : (fun z ↦ exp (H z)) = fun z ↦ exp (b * z + a) := by
      funext z
      rw [h z, add_comm]
    rw [he]
    exact (orderLE_cexp_iff.mpr le_rfl).comp_mul_add b a

/-- The exponential of an entire function has order at most any real `ρ` exactly when the
exponent is a polynomial of natural degree at most `⌊ρ⌋₊`. -/
theorem orderLE_cexp_comp_iff {H : ℂ → ℂ} {ρ : ℝ} (hH : Differentiable ℂ H) :
    OrderLE (fun z ↦ exp (H z)) ρ ↔
      ∃ P : Polynomial ℂ, P.natDegree ≤ ⌊ρ⌋₊ ∧ H = P.eval := by
  constructor
  · exact fun h ↦ h.exists_eq_polynomial_eval_of_cexp hH
  · rintro ⟨P, hP, rfl⟩
    exact orderLE_cexp_polynomial_eval_iff.mpr hP


end TauCeti
