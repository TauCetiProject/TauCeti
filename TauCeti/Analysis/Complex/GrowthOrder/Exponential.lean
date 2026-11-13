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
public import TauCeti.Analysis.Convex.SimplyConnected

/-!
# Exponential rigidity at order at most one

An entire function whose exponential has order at most one is affine. Consequently, every
zero-free entire function of order at most one has the form `exp(a + b z)`. The latter is the
zero-free case of Hadamard factorization. For functions with zeros, comparison with a canonical
product additionally requires a growth bound on the quotient.

## Main results

* `TauCeti.OrderLE.eq_affine_of_cexp` identifies the exponent by its value and derivative
  at zero.
* `TauCeti.OrderLE.exists_eq_cexp_add_logDeriv_mul` writes a zero-free entire function of
  order at most one as `exp (a + b z)`, with `b` its logarithmic derivative at zero.
* `TauCeti.OrderLE.exists_eq_cexp_affine_of_forall_ne_zero` classifies zero-free entire
  functions of order at most one.
* `TauCeti.orderLE_cexp_comp_iff` characterizes the entire exponents whose exponential has
  order at most one (exactly the affine ones).

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

/-- A zero-free entire function of order at most one has affine exponential form with
linear coefficient given by its logarithmic derivative at zero. -/
theorem OrderLE.exists_eq_cexp_add_logDeriv_mul {f : ℂ → ℂ}
    (h : OrderLE f 1) (hf : Differentiable ℂ f) (hf0 : ∀ z, f z ≠ 0) :
    ∃ a : ℂ, exp a = f 0 ∧ ∀ z, f z = exp (a + logDeriv f 0 * z) := by
  obtain ⟨H, hH, heq⟩ := exists_differentiableOn_eqOn_exp_comp
    (convex_univ.isSimplyConnected Set.univ_nonempty) isOpen_univ hf.differentiableOn
    (by simpa only [Set.mem_image, Set.mem_univ, true_and, not_exists] using hf0)
  have he : (fun z ↦ exp (H z)) = f := funext fun z ↦ heq (Set.mem_univ z)
  have hHa := (he.symm ▸ h : OrderLE (fun z ↦ exp (H z)) 1).eq_affine_of_cexp
    (differentiableOn_univ.mp hH)
  rw [deriv_eq_logDeriv_of_eqOn_exp_comp isOpen_univ hH heq (Set.mem_univ 0)] at hHa
  exact ⟨H 0, heq (Set.mem_univ 0),
    fun z ↦ (heq (Set.mem_univ z)).symm.trans (congrArg exp (hHa z))⟩

/-- A zero-free entire function of order at most one is the exponential
of an affine function. -/
theorem OrderLE.exists_eq_cexp_affine_of_forall_ne_zero {f : ℂ → ℂ}
    (h : OrderLE f 1) (hf : Differentiable ℂ f) (hf0 : ∀ z, f z ≠ 0) :
    ∃ a b : ℂ, ∀ z, f z = exp (a + b * z) :=
  let ⟨a, _, ha⟩ := h.exists_eq_cexp_add_logDeriv_mul hf hf0
  ⟨a, logDeriv f 0, ha⟩

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
