/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
module

public import TauCeti.Analysis.Complex.GrowthOrder
public import TauCeti.Analysis.Complex.Liouville
public import TauCeti.Analysis.Complex.BorelCaratheodory
public import TauCeti.Analysis.Complex.BranchLogRoot
public import Mathlib.Analysis.Convex.Contractible

/-!
# Exponential rigidity at order at most one

An entire function whose exponential has order at most one is affine. Consequently, every
zero-free entire function of order at most one has the form `exp(a + b z)`. The latter is the
zero-free case of Hadamard factorization. For functions with zeros, comparison with a canonical
product additionally requires a growth bound on the quotient.

## Main results

* `TauCeti.OrderLE.eq_affine_of_cexp` identifies the exponent by its value and derivative
  at zero.
* `TauCeti.OrderLE.exists_eq_cexp_affine_of_forall_ne_zero` classifies zero-free entire
  functions of order at most one.
* `TauCeti.orderLE_cexp_comp_iff` characterizes the entire exponents with order-one exponential.
* `TauCeti.OrderLE.exists_eq_cexp_add_logDeriv_mul` identifies the linear coefficient
  with the logarithmic derivative at zero.

## References

* H. Davenport, *Multiplicative Number Theory*, 3rd ed., Chapter 11.
-/

public section

open Complex Filter Bornology Topology Asymptotics

namespace TauCeti

/-- An entire exponent whose exponential has order at most one is affine. -/
theorem OrderLE.eq_affine_of_cexp {H : ℂ → ℂ}
    (h : OrderLE (fun z ↦ exp (H z)) 1) (hH : Differentiable ℂ H) :
    ∀ z, H z = H 0 + deriv H 0 * z := by
  have hg := hH.isBigO_of_cexp_isBigO (by norm_num : (0 : ℝ) ≤ 3 / 2)
    (h.isBigO (by norm_num : (1 : ℝ) < 3 / 2))
  have hr_real : (fun r : ℝ ↦ r ^ (3 / 2 : ℝ)) =o[atTop] (fun r ↦ r ^ 2) := by
    have hgf : ∀ᶠ r : ℝ in atTop, r ^ 2 = 0 → r ^ (3 / 2 : ℝ) = 0 := by
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
      exact fun hz ↦ False.elim ((pow_ne_zero 2 hr.ne') hz)
    apply (isLittleO_iff_tendsto' hgf).mpr
    apply (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 2)).congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
    rw [← Real.rpow_two, ← Real.rpow_sub hr]
    norm_num
  have hr : (fun z : ℂ ↦ ‖z‖ ^ (3 / 2 : ℝ)) =o[cobounded ℂ] (fun z ↦ ‖z‖ ^ 2) := by
    exact (hr_real.comp_tendsto
      (tendsto_norm_cobounded_atTop : Tendsto (fun z : ℂ ↦ ‖z‖) (cobounded ℂ) atTop)).congr
        (fun z ↦ rfl) (fun z ↦ rfl)
  have hnorm : (fun z : ℂ ↦ ‖z‖ ^ 2) =O[cobounded ℂ] (fun z ↦ z ^ 2) :=
    isBigO_of_le _ (fun z ↦ by simp [norm_pow])
  exact hH.eq_affine_of_isLittleO_sq (hg.trans_isLittleO (hr.trans_isBigO hnorm))

/-- A zero-free entire function of order at most one is the exponential
of an affine function. -/
theorem OrderLE.exists_eq_cexp_affine_of_forall_ne_zero {f : ℂ → ℂ}
    (h : OrderLE f 1) (hf : Differentiable ℂ f) (hf0 : ∀ z, f z ≠ 0) :
    ∃ a b : ℂ, ∀ z, f z = exp (a + b * z) := by
  have hU : IsSimplyConnected (Set.univ : Set ℂ) := by
    have : ContractibleSpace (Set.univ : Set ℂ) :=
      Convex.contractibleSpace convex_univ Set.univ_nonempty
    exact SimplyConnectedSpace.ofContractible _
  obtain ⟨H, hH, heq⟩ := exists_differentiableOn_eqOn_exp_comp hU isOpen_univ
    hf.differentiableOn
    (by simpa only [Set.mem_image, Set.mem_univ, true_and, not_exists] using hf0)
  have hHd : Differentiable ℂ H := differentiableOn_univ.mp hH
  have he : (fun z ↦ exp (H z)) = f := funext fun z ↦ heq (Set.mem_univ z)
  have hcomp : OrderLE (fun z ↦ exp (H z)) 1 := he.symm ▸ h
  have hHa := hcomp.eq_affine_of_cexp hHd
  exact ⟨H 0, deriv H 0, fun z ↦ (heq (Set.mem_univ z)).symm.trans (congrArg exp (hHa z))⟩

/-- A zero-free entire function of order at most one has affine exponential form with
linear coefficient given by its logarithmic derivative at zero. -/
theorem OrderLE.exists_eq_cexp_add_logDeriv_mul {f : ℂ → ℂ}
    (h : OrderLE f 1) (hf : Differentiable ℂ f) (hf0 : ∀ z, f z ≠ 0) :
    ∃ a : ℂ, exp a = f 0 ∧ ∀ z, f z = exp (a + logDeriv f 0 * z) := by
  obtain ⟨a, b, h⟩ := h.exists_eq_cexp_affine_of_forall_ne_zero hf hf0
  have he : f = fun z ↦ exp (a + b * z) := funext h
  have h0 : f 0 = exp a := by simpa using h 0
  have hd : HasDerivAt f (b * exp a) 0 := by
    rw [he]
    convert ((hasDerivAt_const (0 : ℂ) a).add ((hasDerivAt_id 0).const_mul b)).cexp using 1 <;>
      simp [mul_comm]
  have hb : logDeriv f 0 = b := by
    rw [logDeriv_apply, hd.deriv, h0]
    exact mul_div_cancel_right₀ b (exp_ne_zero a)
  exact ⟨a, h0.symm, fun z ↦ by rw [hb]; exact h z⟩

/-- The exponential of an entire function has order at most one exactly when its exponent
is affine. -/
theorem orderLE_cexp_comp_iff {H : ℂ → ℂ} (hH : Differentiable ℂ H) :
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

end TauCeti
