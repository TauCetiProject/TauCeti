/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
module

public import Mathlib.NumberTheory.LSeries.DirichletContinuation
public import TauCeti.Analysis.Complex.GrowthOrder
public import TauCeti.Analysis.Complex.VerticalStrip.Growth
public import TauCeti.NumberTheory.LFunctions.Zeros.Completion.RiemannZeta.Basic
import TauCeti.Analysis.SpecialFunctions.Gamma.Archimedean
import TauCeti.Analysis.SpecialFunctions.Gamma.Reciprocal.Order
import TauCeti.NumberTheory.DirichletCharacter.LFunction.Basic
import TauCeti.NumberTheory.LFunctions.Data.RiemannZeta
import TauCeti.NumberTheory.LFunctions.GammaFactor.Vertical
import TauCeti.NumberTheory.LFunctions.Zeros.Completion.RiemannZeta.Growth
import TauCeti.NumberTheory.LSeries.RiemannZeta.Bounds
import TauCeti.NumberTheory.LSeries.RiemannZeta.FunctionalEquation

/-!
# Growth of the pole-removed Riemann zeta function

Mathlib's entire function `DirichletCharacter.LFunctionTrivChar₁ 1` extends `(s - 1) ζ(s)`
through the pole at one. It is the product of the entire completion of zeta and a shifted
reciprocal Gamma factor, divided by `2π`. Both factors have order at most one, so the
pole-removed uncompleted function does too. The identity holds at the cancelled poles,
including zero and one.

On every closed vertical strip `a ≤ Re s ≤ b` the same function has polynomial growth
`C (|Im s| + 2) ^ B`. To the right of `Re s = 1/2` this follows from the right-half-plane bound
`TauCeti.norm_riemannZeta_le_one_half_add_inv_add_div`. To the left, the functional equation
`ζ(s) = ζ(1 - s) Γℝ(1 - s) / Γℝ(s)` reflects the linear bound
`TauCeti.norm_riemannZeta_le_three_halves_add_norm`, and the Stirling estimate for the
gamma quotient, `AnalyticLFunctionData.exists_norm_dual_gammaFactor_div_bounds` for the zeta
record, is a power of `|Im s|`. This gives `HasVerticalStripGrowth`, and continuity extends the
bound to bounded heights. No Phragmén–Lindelöf interpolation is used, so the exponent is not
the convexity exponent.

## Main results

* `TauCeti.LFunctions.LFunctionTrivChar₁_one_eq_zetaEntireCompletion_mul_inv_Gammaℝ` and
  `TauCeti.orderLE_LFunctionTrivChar₁_one`: the factorization and order at most one.
* `TauCeti.LFunctions.logDeriv_zetaEntireCompletion_eq_add_logDeriv_Gammaℝ`: the factorization
  in logarithmic-derivative form.
* `TauCeti.hasVerticalStripGrowth_LFunctionTrivChar₁_one`: vertical-strip growth at large height.
* `TauCeti.exists_norm_LFunctionTrivChar₁_one_le_rpow`: polynomial growth on vertical strips at
  every height.
* `TauCeti.exists_norm_LFunctionTrivChar₁_one_le_rpow_of_norm_sub_le`: the same polynomial growth
  on closed discs of a fixed radius centred on a vertical line.

## References

* H. Davenport, *Multiplicative Number Theory*, 3rd ed., Chapter 12.
* H. Iwaniec and E. Kowalski, *Analytic Number Theory*, Chapter 5.
* E. C. Titchmarsh, *The Theory of the Riemann Zeta-Function*, 2nd ed., §5.1.
-/

public section

open Complex DirichletCharacter Filter Real Topology Set

namespace TauCeti.LFunctions

/-- The entire pole-removed zeta function is the entire completion times the shifted reciprocal
Gamma factor. The equality includes the removed pole and the trivial zeros. -/
theorem LFunctionTrivChar₁_one_eq_zetaEntireCompletion_mul_inv_Gammaℝ (s : ℂ) :
    LFunctionTrivChar₁ 1 s =
      zetaEntireCompletion s * (Gammaℝ (s + 2))⁻¹ / (2 * π : ℂ) := by
  have hg : Differentiable ℂ (fun z : ℂ ↦
      zetaEntireCompletion z * (Gammaℝ (z + 2))⁻¹ / (2 * π : ℂ)) :=
    (differentiable_zetaEntireCompletion.mul
      (differentiable_Gammaℝ_inv.comp (differentiable_id.add_const 2))).div_const _
  suffices heq : LFunctionTrivChar₁ 1 = (fun z : ℂ ↦
      zetaEntireCompletion z * (Gammaℝ (z + 2))⁻¹ / (2 * π : ℂ)) by
    exact congrFun heq s
  apply AnalyticOnNhd.eq_of_eventuallyEq
    (fun z _ ↦ (differentiable_LFunctionTrivChar₁ 1).analyticAt z)
    (fun z _ ↦ hg.analyticAt z) (z₀ := (2 : ℂ))
  filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds
    (by norm_num : 1 < (2 : ℂ).re)] with z hz
  have hz0 : z ≠ 0 := by intro h; subst z; norm_num at hz
  have hz1 : z ≠ 1 := by intro h; subst z; norm_num at hz
  have hΓ : Gammaℝ z ≠ 0 := Gammaℝ_ne_zero_of_re_pos (lt_trans zero_lt_one hz)
  rw [LFunctionTrivChar₁_one_apply_of_ne_one hz1, zetaEntireCompletion_eq_mul hz0 hz1,
    riemannZeta_def_of_ne_zero hz0, Gammaℝ_add_two hz0]
  field_simp [hz0, hΓ, ofReal_ne_zero.mpr pi_ne_zero]

/-- The shifted real gamma factor gives the difference between the logarithmic derivatives of
zeta's entire completion and its pole-removed continuation. This applies at `0` and `1` too. -/
theorem logDeriv_zetaEntireCompletion_eq_add_logDeriv_Gammaℝ {s : ℂ}
    (hξ : zetaEntireCompletion s ≠ 0) (hΓ : Gammaℝ (s + 2) ≠ 0) :
    logDeriv zetaEntireCompletion s = logDeriv (LFunctionTrivChar₁ 1) s +
      logDeriv Gammaℝ (s + 2) := by
  have hc : (2 * Real.pi : ℂ) ≠ 0 := mul_ne_zero two_ne_zero (ofReal_ne_zero.mpr Real.pi_ne_zero)
  have hfactor := funext LFunctionTrivChar₁_one_eq_zetaEntireCompletion_mul_inv_Gammaℝ
  have hinv : DifferentiableAt ℂ (Gammaℝ⁻¹) (s + 2) := differentiable_Gammaℝ_inv _
  have hg : DifferentiableAt ℂ Gammaℝ (s + 2) := by
    simpa only [inv_inv] using hinv.inv (inv_ne_zero hΓ)
  have hshift : DifferentiableAt ℂ (fun z : ℂ ↦ z + 2) s := by fun_prop
  have hfun := hg.comp s hshift
  have hl : logDeriv (fun z : ℂ ↦ (Gammaℝ (z + 2))⁻¹) s = -logDeriv Gammaℝ (s + 2) := by
    have hz := logDeriv_fun_zpow hfun (-1 : ℤ)
    rw [logDeriv_comp (x := s) (g := fun z : ℂ ↦ z + 2) hg hshift] at hz
    simpa [Function.comp_def, deriv_add_const] using hz
  have hlog : logDeriv (LFunctionTrivChar₁ 1) s =
      logDeriv zetaEntireCompletion s + -logDeriv Gammaℝ (s + 2) := by
    rw [hfactor]
    simp only [div_eq_mul_inv, logDeriv_mul_const _ _ (inv_ne_zero hc)]
    rw [logDeriv_fun_mul (g := fun z : ℂ ↦ (Gammaℝ (z + 2))⁻¹) s hξ (inv_ne_zero hΓ)
      (differentiable_zetaEntireCompletion s) (hfun.inv hΓ), hl]
  linear_combination -hlog

end TauCeti.LFunctions

namespace TauCeti

/-- The entire extension of `(s - 1) ζ(s)` has order at most one on the whole complex plane. -/
theorem orderLE_LFunctionTrivChar₁_one : OrderLE (LFunctionTrivChar₁ 1) 1 := by
  rw [funext LFunctions.LFunctionTrivChar₁_one_eq_zetaEntireCompletion_mul_inv_Gammaℝ]
  simpa only [one_mul, div_eq_mul_inv] using
    (LFunctions.orderLE_zetaEntireCompletion.mul (orderLE_inv_Gammaℝ.comp_mul_add 1 2)).mul
      (orderLE_const ((2 * π : ℂ)⁻¹) 1)

/-- On `1/2 ≤ Re s`, `‖(s - 1) ζ(s)‖ ≤ (‖s‖ + 3) ^ 2`. -/
private theorem norm_sub_one_mul_riemannZeta_le_of_half_le_re {s : ℂ} (hre : 1 / 2 ≤ s.re) :
    ‖(s - 1) * riemannZeta s‖ ≤ (‖s‖ + 3) ^ 2 := by
  rcases eq_or_ne s 1 with rfl | hs1
  · simp only [sub_self, zero_mul, norm_zero]
    positivity
  have hs : ‖s - 1‖ ≠ 0 := norm_ne_zero_iff.2 (sub_ne_zero.2 hs1)
  have hζ := norm_riemannZeta_le_one_half_add_inv_add_div (by linarith) hs1
  have hdiv : ‖s‖ / (2 * s.re) ≤ ‖s‖ := div_le_self (norm_nonneg s) (by linarith)
  have h1 : ‖s - 1‖ ≤ ‖s‖ + 1 := by linarith [norm_sub_le s 1, norm_one (α := ℂ)]
  rw [norm_mul]
  calc ‖s - 1‖ * ‖riemannZeta s‖ ≤ ‖s - 1‖ * (1 / 2 + 1 / ‖s - 1‖ + ‖s‖) := by
        gcongr
        linarith
    _ = ‖s - 1‖ * (1 / 2 + ‖s‖) + 1 := by field_simp; ring
    _ ≤ (‖s‖ + 1) * (1 / 2 + ‖s‖) + 1 := by gcongr
    _ ≤ (‖s‖ + 3) ^ 2 := by nlinarith [norm_nonneg s]

/-- Away from the real axis by at least `1`, on `Re s ≤ 1/2`,
`‖(s - 1) ζ(s)‖ ≤ (‖s‖ + 3) ^ 2 ‖Γℝ(1 - s) / Γℝ(s)‖`. -/
private theorem norm_sub_one_mul_riemannZeta_le_of_re_le_half {s : ℂ} (hre : s.re ≤ 1 / 2)
    (him : 1 ≤ |s.im|) :
    ‖(s - 1) * riemannZeta s‖ ≤ (‖s‖ + 3) ^ 2 * ‖Gammaℝ (1 - s) / Gammaℝ s‖ := by
  have h1 : ‖s - 1‖ ≤ ‖s‖ + 3 := by linarith [norm_sub_le s 1, norm_one (α := ℂ)]
  have h1' : ‖1 - s‖ ≤ ‖s‖ + 1 := by
    rw [norm_sub_rev]; linarith [norm_sub_le s 1, norm_one (α := ℂ)]
  have hpole : 1 ≤ ‖1 - s - 1‖ := him.trans (by simpa using abs_im_le_norm s)
  have hζ := norm_riemannZeta_le_three_halves_add_norm
    (by rw [sub_re, one_re]; linarith) hpole
  have him0 : s.im ≠ 0 := abs_pos.1 (by linarith)
  rw [riemannZeta_eq_riemannZeta_one_sub_mul_Gammaℝ_div (fun h ↦ him0 (by simp [h]))
    (Gammaℝ_ne_zero_of_im_ne_zero (by simpa using him0)), norm_mul, norm_mul, sq, mul_assoc]
  exact mul_le_mul h1 (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _))
    (by positivity) (by positivity)

/-- **`(s - 1) ζ(s)` has vertical-strip growth.** On every vertical strip, the entire function
`LFunctionTrivChar₁ 1` is bounded by a power of `1 + |Im s|` at large height. -/
theorem hasVerticalStripGrowth_LFunctionTrivChar₁_one :
    HasVerticalStripGrowth (LFunctionTrivChar₁ 1) := by
  refine hasVerticalStripGrowth_iff.2 fun a b _ ↦ ?_
  obtain ⟨_, _, C₂, _, T, _, hΓ⟩ :=
    LFunctions.riemannZetaData.exists_norm_dual_gammaFactor_div_bounds a b
  set E := max ((1 - 2 * a) / 2) 0
  set K := max |a| |b| + 3
  have hK0 : 0 < K := three_pos.trans_le (le_add_of_nonneg_left (le_max_of_le_left (abs_nonneg a)))
  refine ⟨K ^ 2 * max C₂ 1, by positivity, 2 + E, by positivity, max T 1,
    zero_le_one.trans (le_max_right _ _), fun s ⟨ha, hb⟩ ht ↦ ?_⟩
  have ht1 : 1 ≤ |s.im| := (le_max_right _ _).trans ht
  have hs1 : s ≠ 1 := fun h ↦ by norm_num [h] at ht1
  rw [LFunctionTrivChar₁_one_apply_of_ne_one hs1]
  have hx : 1 ≤ 1 + |s.im| := by linarith [abs_nonneg s.im]
  have hX : (‖s‖ + 3) ^ 2 ≤ K ^ 2 * (1 + |s.im|) ^ (2 : ℝ) := by
    have hn := norm_le_abs_re_add_abs_im s
    have hr := abs_le_max_abs_abs ha hb
    have hK : ‖s‖ + 3 ≤ K * (1 + |s.im|) := by
      nlinarith [abs_nonneg s.im, abs_nonneg a, le_max_left |a| |b|]
    rw [Real.rpow_two, ← mul_pow]
    exact pow_le_pow_left₀ (by positivity) hK 2
  have hsplit : (1 + |s.im|) ^ (2 + E) = (1 + |s.im|) ^ (2 : ℝ) * (1 + |s.im|) ^ E :=
    Real.rpow_add (by linarith) _ _
  have hE1 : 1 ≤ (1 + |s.im|) ^ E := Real.one_le_rpow hx (le_max_right _ _)
  rcases le_or_gt (1 / 2) s.re with hre | hre
  · refine (norm_sub_one_mul_riemannZeta_le_of_half_le_re hre).trans (hX.trans ?_)
    rw [hsplit, mul_assoc]
    gcongr
    calc (1 + |s.im|) ^ (2 : ℝ) = 1 * ((1 + |s.im|) ^ (2 : ℝ) * 1) := by ring
      _ ≤ max C₂ 1 * ((1 + |s.im|) ^ (2 : ℝ) * (1 + |s.im|) ^ E) := by
        gcongr
        exact le_max_right _ _
  obtain ⟨-, hQ⟩ := hΓ s ⟨ha, hb⟩ ((le_max_left _ _).trans ht)
  simp only [LFunctions.riemannZetaData_dual, LFunctions.riemannZetaData_gammaFactor,
    LFunctions.riemannZetaData_degree, Nat.cast_one] at hQ
  have hpow : |s.im| ^ (1 / 2 * (1 - 2 * s.re)) ≤ (1 + |s.im|) ^ E :=
    (Real.rpow_le_rpow (abs_nonneg _) (by linarith) (by nlinarith)).trans
      (Real.rpow_le_rpow_of_exponent_le hx (le_max_of_le_left (by linarith)))
  refine (norm_sub_one_mul_riemannZeta_le_of_re_le_half hre.le ht1).trans ?_
  rw [hsplit]
  calc (‖s‖ + 3) ^ 2 * ‖Gammaℝ (1 - s) / Gammaℝ s‖
      ≤ (K ^ 2 * (1 + |s.im|) ^ (2 : ℝ)) * (max C₂ 1 * (1 + |s.im|) ^ E) := by
        gcongr
        exact hQ.trans (by gcongr; exact le_max_left _ _)
    _ = _ := by ring

/-- **Polynomial growth of `(s - 1) ζ(s)` on vertical strips.** On every closed vertical strip
`a ≤ Re s ≤ b`, the entire function `LFunctionTrivChar₁ 1`, which is `(s - 1) ζ(s)` away from
`s = 1` and the residue `1` at `s = 1`, satisfies `‖LFunctionTrivChar₁ 1 s‖ ≤ C (|Im s| + 2) ^ B`
at every height. The strip may reach into `Re s < 0`. -/
theorem exists_norm_LFunctionTrivChar₁_one_le_rpow (a b : ℝ) :
    ∃ C B : ℝ, ∀ s : ℂ, a ≤ s.re → s.re ≤ b →
      ‖LFunctionTrivChar₁ 1 s‖ ≤ C * (|s.im| + 2) ^ B := by
  obtain ⟨C, hC, B, hB, h⟩ :=
    hasVerticalStripGrowth_LFunctionTrivChar₁_one.exists_bound_of_continuousOn
      (differentiable_LFunctionTrivChar₁ 1).continuous.continuousOn (a := a) (b := b)
  exact ⟨C, B, fun s ha hb ↦ (h s ⟨ha, hb⟩).trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow (by positivity) (by linarith) hB) hC.le)⟩

/-- On the closed discs of a fixed radius `R` centred on a vertical line `Re s₀ = σ₀`,
`‖(s - 1) ζ(s)‖ ≤ K (|Im s₀| + 2) ^ B` with `K > 0` and `B` independent of `s₀`. -/
theorem exists_norm_LFunctionTrivChar₁_one_le_rpow_of_norm_sub_le (σ₀ R : ℝ) :
    ∃ K B : ℝ, 0 < K ∧ ∀ s₀ w : ℂ, s₀.re = σ₀ → ‖w - s₀‖ ≤ R →
      ‖LFunctionTrivChar₁ 1 w‖ ≤ K * (|s₀.im| + 2) ^ B := by
  obtain ⟨C, B, hC⟩ := exists_norm_LFunctionTrivChar₁_one_le_rpow (σ₀ - R) (σ₀ + R)
  refine ⟨max C 1 * (|R| + 1) ^ max B 0, max B 0,
    mul_pos (lt_max_of_lt_right one_pos) (Real.rpow_pos_of_pos (by positivity) _),
    fun s₀ w hs₀ hw ↦ ?_⟩
  have hre := abs_re_le_norm (w - s₀)
  rw [sub_re, hs₀, abs_le] at hre
  have him := (abs_sub_abs_le_abs_sub w.im s₀.im).trans ((sub_im w s₀ ▸ abs_im_le_norm _).trans hw)
  calc ‖LFunctionTrivChar₁ 1 w‖ ≤ C * (|w.im| + 2) ^ B := hC w (by linarith) (by linarith)
    _ ≤ max C 1 * (|w.im| + 2) ^ max B 0 := by
        gcongr
        · exact le_max_left _ _
        · linarith [abs_nonneg w.im]
        · exact le_max_left _ _
    _ ≤ max C 1 * ((|R| + 1) * (|s₀.im| + 2)) ^ max B 0 := by
        gcongr
        nlinarith [abs_nonneg s₀.im, le_abs_self R, abs_nonneg R]
    _ = _ := by rw [Real.mul_rpow (by positivity) (by positivity), mul_assoc]

end TauCeti
