/-
Copyright (c) 2026 Matteo Cipollina and The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina, The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.CanonicalProduct.ElementaryFactor
public import TauCeti.Analysis.Complex.GrowthOrder
import TauCeti.Analysis.Complex.BorelCaratheodory
import TauCeti.Analysis.Complex.CanonicalProduct.GoodCircle
import TauCeti.Analysis.Complex.CanonicalProduct.PrimaryProduct
import TauCeti.Analysis.Complex.GrowthOrder.Zero.Summability
import TauCeti.Analysis.Normed.Group.SummableNormInvRpow

/-!
# Hadamard factorization of entire functions of finite order

Let `f` be an entire function, not identically zero, with `‖f z‖ ≤ C_b * exp (‖z‖ ^ b)` for every
`b > ρ`, and let `n = ⌊ρ⌋₊`. Its nonzero zeros `α`, counted with their analytic orders `m_α`,
satisfy `∑ m_α * ‖α‖ ^ (-(n + 1)) < ∞`, and
`f z = z ^ m₀ * exp (P z) * ∏ α, E_n(z / α) ^ m_α`,
where `m₀` is the order of `f` at `0`, `E_n` is Weierstrass's primary factor of genus `n`, the
product over finite sets of nonzero complex numbers converges locally uniformly, and `P` is a
polynomial of degree at most `n` (`TauCeti.finite_order_hadamard`).

The product is indexed by all nonzero complex numbers; only the zeros of `f` have nonzero
multiplicity. Every genus `p > ρ - 1` gives such a factorization with an entire exponent
(`Differentiable.exists_eq_pow_mul_exp_mul_tprod_nonzero_weierstrassFactor_div_pow`, in
`TauCeti.Analysis.Complex.CanonicalProduct.PrimaryProduct`), and the exponent is then a
polynomial of degree at most `p`
(`TauCeti.OrderLE.exists_eq_polynomial_eval_of_eq_pow_mul_exp_mul_tprod`).

## Main results

* `TauCeti.OrderLE.exists_eq_polynomial_eval_of_eq_pow_mul_exp_mul_tprod`: for an entire function
  of order at most `ρ < p + 1`, the exponent in its genus-`p` factorization is a polynomial of
  degree at most `p`.
* `TauCeti.finite_order_hadamard`: Hadamard's factorization theorem.

## Provenance

Adapted from Matteo Cipollina's `HadamardFactorization.lean`, `HadamardFactorization/Growth.lean`
and `HadamardFactorization/Order.lean` in
[PrimeNumberTheoremAnd, revision df0ccba](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/tree/df0ccba486bb86e273ecab565b6ab222c37f8320/PrimeNumberTheoremAnd/Mathlib/Analysis/Complex),
which build the product over an enumeration of the divisor and bound the quotient `f / (z ^ m₀ * P)`
on Cartan's circles. Here the product is over all nonzero complex numbers with analytic orders as
exponents, and the exponent is bounded through its real part on those circles.

## References

* Z. Yun, W. Zhang, *Shtukas and the Taylor expansion of L-functions*, *Ann. of Math.* (2) **186**
  (2017), no. 3, 767–911, Appendix B.1.
* A. Kupers, *Complex analysis* lecture notes, Theorem 14.1.1 and Corollary 14.1.6.
-/

public section

open Complex Filter Set Topology

namespace TauCeti

variable {f : ℂ → ℂ} {ρ : ℝ}

/-- If `w = z ^ m * exp u * q` with `1 ≤ ‖z‖`, `‖w‖ ≤ B * exp t` and `exp (-c) ≤ ‖q‖`, then
`u.re ≤ log B + t + c`. -/
private theorem re_le_log_add_add_of_eq_pow_mul_exp_mul {w z u q : ℂ} {m : ℕ} {B t c : ℝ}
    (hw : w = z ^ m * cexp u * q) (hz : 1 ≤ ‖z‖) (hwB : ‖w‖ ≤ B * Real.exp t)
    (hq : Real.exp (-c) ≤ ‖q‖) : u.re ≤ Real.log B + t + c := by
  have hzm : 1 ≤ ‖z‖ ^ m := one_le_pow₀ hz
  have hB : 0 < B := by
    have hw0 : 0 < ‖w‖ := by
      rw [hw, norm_mul, norm_mul, Complex.norm_exp]
      exact mul_pos (mul_pos (by rw [norm_pow]; linarith) (Real.exp_pos _))
        ((Real.exp_pos _).trans_le hq)
    by_contra! hB
    nlinarith [Real.exp_pos t]
  have h : Real.exp (u.re + -c) ≤ Real.exp (Real.log B + t) := by
    rw [Real.exp_add, Real.exp_add, Real.exp_log hB]
    calc Real.exp u.re * Real.exp (-c) ≤ ‖z‖ ^ m * (Real.exp u.re * ‖q‖) := by
          rw [← one_mul (Real.exp u.re * Real.exp (-c))]
          gcongr
      _ = ‖w‖ := by rw [hw, norm_mul, norm_mul, norm_pow, Complex.norm_exp, mul_assoc]
      _ ≤ B * Real.exp t := hwB
  linarith [Real.exp_le_exp.mp h]

/-- **Hadamard's degree bound.** Let `f` be entire of order at most `ρ < p + 1`, factored as
`f z = z ^ m₀ * exp (g z) * ∏' α, E_p(z / α) ^ m_α` with `g` entire, the product running over all
nonzero complex numbers with the analytic orders `m_α` of `f` as exponents. Then `g` is a
polynomial of degree at most `p`.

The bound `ρ < p + 1` is needed: `exp (z ^ 2)` has order `2`, an empty product, and exponent
`z ^ 2` of degree `2 > 1`. -/
theorem OrderLE.exists_eq_polynomial_eval_of_eq_pow_mul_exp_mul_tprod (h : OrderLE f ρ)
    (hf : Differentiable ℂ f) {p : ℕ} (hρp : ρ < p + 1) {g : ℂ → ℂ} (hg : Differentiable ℂ g)
    (hfg : ∀ z, f z = z ^ analyticOrderNatAt f 0 * cexp (g z) *
      ∏' α : {a : ℂ // a ≠ 0}, weierstrassFactor p (z / α) ^ analyticOrderNatAt f α) :
    ∃ P : Polynomial ℂ, P.natDegree ≤ p ∧ g = P.eval := by
  -- An exponent `s` with `max ρ p < s < p + 1`.
  obtain ⟨s, hρs, hps, hsp⟩ : ∃ s, ρ < s ∧ (p : ℝ) ≤ s ∧ s < p + 1 := by
    have := max_lt hρp (by linarith : (p : ℝ) < p + 1)
    refine ⟨(max ρ p + p + 1) / 2, ?_, ?_, by linarith⟩ <;>
      linarith [le_max_left ρ (p : ℝ), le_max_right ρ (p : ℝ)]
  have hs : 0 ≤ s := (Nat.cast_nonneg p).trans hps
  have hsum := h.summable_analyticOrderNatAt_mul_norm_inv_rpow hf hρs
  set K := ((Real.log 2 + 12 * Real.sqrt 6 + p) * 4 ^ s + p + 2) *
    ∑' α : {a : ℂ // a ≠ 0}, (analyticOrderNatAt f α : ℝ) * ‖(α : ℂ)‖⁻¹ ^ s
  obtain ⟨B, -, hfB⟩ := h.exists_norm_le_mul_exp_rpow hf.continuous hρs
  -- On Cartan's circles of radius at least `1`, `Re g ≤ (|log B| + 1 + K) * R ^ s`.
  have hre : ∃ᶠ R in atTop, ∀ z ∈ Metric.sphere (0 : ℂ) R,
      (g z).re ≤ (|Real.log B| + 1 + K) * R ^ s := by
    refine frequently_atTop.mpr fun A ↦ ?_
    obtain ⟨r, hr, hcircle⟩ :=
      Complex.exists_mem_Ioc_forall_norm_eq_exp_neg_le_norm_tprod_weierstrassFactor_div_pow p
        hps hsp.le hsum (R := max A 1) (by positivity)
    have hr1 : 1 ≤ r := (le_max_right A 1).trans hr.1.le
    refine ⟨r, (le_max_left A 1).trans hr.1.le, fun z hz ↦ ?_⟩
    rw [mem_sphere_zero_iff_norm] at hz
    have hbound := re_le_log_add_add_of_eq_pow_mul_exp_mul (hfg z) (hz ▸ hr1) (hfB z)
      (hcircle z hz)
    have hrs : 1 ≤ r ^ s := Real.one_le_rpow hr1 hs
    rw [hz] at hbound
    -- `K` abbreviates the constant of the good-circle estimate.
    replace hbound : (g z).re ≤ Real.log B + r ^ s + K * r ^ s := hbound
    nlinarith [mul_le_mul_of_nonneg_left hrs (abs_nonneg (Real.log B)), le_abs_self (Real.log B)]
  obtain ⟨P, hP, rfl⟩ := hg.exists_eq_polynomial_eval_of_frequently_re_le_rpow hre
  exact ⟨P, hP.trans (Nat.lt_succ_iff.mp ((Nat.floor_lt' (Nat.succ_ne_zero p)).mpr
    (by exact_mod_cast hsp))), rfl⟩

/-- **Hadamard's factorization theorem.** Let `f` be an entire function, not identically zero,
with `‖f z‖ ≤ C_b * exp (‖z‖ ^ b)` for every `b > ρ`, and let `n = ⌊ρ⌋₊`. Then its nonzero zeros
`α`, with their analytic orders `m_α`, satisfy `∑ m_α * ‖α‖ ^ (-(n + 1)) < ∞`, and
`f z = z ^ m₀ * exp (P z) * g z`, where `m₀` is the order of `f` at `0`, `P` is a polynomial of
degree at most `n`, and `g` is the locally uniform limit of the finite products
`∏ α ∈ S, E_n(z / α) ^ m_α`.

Each hypothesis is needed: `f = 0` has no such factorization, `conj` is not entire, and
`exp (exp z)` with `ρ = 0` would be the exponential of a constant. -/
theorem finite_order_hadamard (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (hne : ∃ z, f z ≠ 0) {ρ : ℝ}
    (hgrowth : ∀ b : ℝ, ρ < b → ∃ C > 0, ∀ z : ℂ, ‖f z‖ ≤ C * Real.exp (‖z‖ ^ b)) :
    let E := fun (α : {a : ℂ // a ≠ 0}) (z : ℂ) ↦
      weierstrassFactor ⌊ρ⌋₊ (z / α.val) ^ (analyticOrderAt f α.val).toNat
    Summable (fun α : {a : ℂ // a ≠ 0} ↦
      (analyticOrderAt f α.val).toNat * ‖α.val‖ ^ (-(⌊ρ⌋₊ + 1 : ℝ))) ∧
    ∃ (P : Polynomial ℂ) (g : ℂ → ℂ), P.natDegree ≤ ⌊ρ⌋₊ ∧
      TendstoLocallyUniformly
        (fun S : Finset {a : ℂ // a ≠ 0} ↦ fun z ↦ ∏ α ∈ S, E α z) g atTop ∧
      ∀ z : ℂ, f z = z ^ (analyticOrderAt f 0).toNat * Complex.exp (P.eval z) * g z := by
  intro E
  have h : OrderLE f ρ := orderLE_of_forall_exists_norm_le_mul_exp_rpow fun b hb ↦
    (hgrowth b hb).imp fun _ hC ↦ hC.2
  have hρn : ρ < ⌊ρ⌋₊ + 1 := Nat.lt_floor_add_one ρ
  have hsum := h.summable_analyticOrderNatAt_mul_norm_inv_rpow hf hρn
  have hm (R : ℝ) (_ : 0 < R) :=
    hsum.natCast_mul_div_pow_succ (by positivity) (p := ⌊ρ⌋₊) le_rfl R
  obtain ⟨g, hg, hfg⟩ :=
    hf.exists_eq_pow_mul_exp_mul_tprod_nonzero_weierstrassFactor_div_pow hne hm
  obtain ⟨P, hP, rfl⟩ := h.exists_eq_polynomial_eval_of_eq_pow_mul_exp_mul_tprod hf hρn hg hfg
  refine ⟨hsum.congr fun α ↦ ?_, P, _, hP, tendstoLocallyUniformlyOn_univ.mp
    (hasProdLocallyUniformlyOn_weierstrassFactor_div_pow hm), hfg⟩
  rw [Real.rpow_neg (norm_nonneg _), ← Real.inv_rpow (norm_nonneg _)]
  -- `analyticOrderNatAt f z` is by definition `(analyticOrderAt f z).toNat`.
  rfl

end TauCeti
