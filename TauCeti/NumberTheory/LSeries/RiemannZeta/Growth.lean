/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
module

public import Mathlib.NumberTheory.LSeries.DirichletContinuation
public import TauCeti.Analysis.Complex.GrowthOrder
public import TauCeti.NumberTheory.LFunctions.Zeros.Completion.RiemannZeta.Basic
import TauCeti.Analysis.SpecialFunctions.Gamma.Archimedean
import TauCeti.Analysis.SpecialFunctions.Gamma.Reciprocal.Order
import TauCeti.NumberTheory.LFunctions.Data.RiemannZeta
import TauCeti.NumberTheory.LFunctions.GammaFactor.Vertical
import TauCeti.NumberTheory.LFunctions.Zeros.Completion.RiemannZeta.Growth
import TauCeti.NumberTheory.LSeries.RiemannZeta.Bounds

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
record, is a power of `|Im s|`. Bounded heights are handled by compactness. No
Phragmén–Lindelöf interpolation is used, so the exponent is not the convexity exponent.

## Main results

* `TauCeti.LFunctions.LFunctionTrivChar₁_one_eq_zetaEntireCompletion_mul_inv_Gammaℝ` and
  `TauCeti.orderLE_LFunctionTrivChar₁_one`: the factorization and order at most one.
* `TauCeti.exists_norm_LFunctionTrivChar₁_one_le_rpow`: polynomial growth on vertical strips.

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
  rw [LFunctionTrivChar₁, Function.update_of_ne hz1,
    LFunctionTrivChar_eq_mul_riemannZeta hz1]
  simp only [Nat.primeFactors_one, Finset.prod_empty, one_mul]
  rw [zetaEntireCompletion_eq_mul hz0 hz1, riemannZeta_def_of_ne_zero hz0, Gammaℝ_add_two hz0]
  field_simp [hz0, hΓ, ofReal_ne_zero.mpr pi_ne_zero]

end TauCeti.LFunctions

namespace TauCeti

/-- The entire extension of `(s - 1) ζ(s)` has order at most one on the whole complex plane. -/
theorem orderLE_LFunctionTrivChar₁_one : OrderLE (LFunctionTrivChar₁ 1) 1 := by
  rw [funext LFunctions.LFunctionTrivChar₁_one_eq_zetaEntireCompletion_mul_inv_Gammaℝ]
  simpa only [one_mul, div_eq_mul_inv] using
    (LFunctions.orderLE_zetaEntireCompletion.mul (orderLE_inv_Gammaℝ.comp_mul_add 1 2)).mul
      (orderLE_const ((2 * π : ℂ)⁻¹) 1)

/-- Off the real axis, the functional equation in the form `ζ(s) = ζ(1 - s) Γℝ(1 - s) / Γℝ(s)`. -/
private theorem riemannZeta_eq_riemannZeta_one_sub_mul_Gammaℝ_div {s : ℂ} (hs : s.im ≠ 0) :
    riemannZeta s = riemannZeta (1 - s) * (Gammaℝ (1 - s) / Gammaℝ s) := by
  have hs0 : s ≠ 0 := fun h ↦ hs (by simp [h])
  have hs1 : (1 - s).im ≠ 0 := by simpa using hs
  have hs1' : 1 - s ≠ 0 := fun h ↦ hs1 (by simp [h])
  have hΓ := Gammaℝ_ne_zero_of_im_ne_zero hs
  have hΓ' := Gammaℝ_ne_zero_of_im_ne_zero hs1
  rw [riemannZeta_def_of_ne_zero hs0, riemannZeta_def_of_ne_zero hs1',
    completedRiemannZeta_one_sub]
  field_simp

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
  have hζ := norm_riemannZeta_le_three_halves_add_norm (by simp; linarith) hpole
  rw [riemannZeta_eq_riemannZeta_one_sub_mul_Gammaℝ_div (abs_pos.1 (by linarith)), norm_mul,
    norm_mul, sq, mul_assoc]
  exact mul_le_mul h1 (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _))
    (by positivity) (by positivity)

/-- Polynomial growth of `(s - 1) ζ(s)` on a vertical strip at sufficiently large height. -/
private theorem exists_norm_sub_one_mul_riemannZeta_le_of_le_abs_im (a b : ℝ) :
    ∃ T C B : ℝ, 1 ≤ T ∧ 0 ≤ C ∧ 0 ≤ B ∧ ∀ s : ℂ, a ≤ s.re → s.re ≤ b → T ≤ |s.im| →
      ‖(s - 1) * riemannZeta s‖ ≤ C * (|s.im| + 2) ^ B := by
  obtain ⟨_, _, C₂, _, T, _, hΓ⟩ :=
    LFunctions.riemannZetaData.exists_norm_dual_gammaFactor_div_bounds a b
  set E := max ((1 - 2 * a) / 2) 0
  set K := max |a| |b| + 3
  refine ⟨max T 1, K ^ 2 * max C₂ 1, 2 + E, le_max_right _ _, by positivity, by positivity,
    fun s ha hb ht ↦ ?_⟩
  have ht1 : 1 ≤ |s.im| := (le_max_right _ _).trans ht
  have hx : 1 ≤ |s.im| + 2 := by linarith [abs_nonneg s.im]
  have hX : (‖s‖ + 3) ^ 2 ≤ K ^ 2 * (|s.im| + 2) ^ (2 : ℝ) := by
    have hn := norm_le_abs_re_add_abs_im s
    have hr := abs_le_max_abs_abs ha hb
    have hK : ‖s‖ + 3 ≤ K * (|s.im| + 2) := by
      nlinarith [abs_nonneg s.im, abs_nonneg a, le_max_left |a| |b|]
    rw [Real.rpow_two, ← mul_pow]
    exact pow_le_pow_left₀ (by positivity) hK 2
  have hsplit : (|s.im| + 2) ^ (2 + E) = (|s.im| + 2) ^ (2 : ℝ) * (|s.im| + 2) ^ E :=
    Real.rpow_add (by linarith) _ _
  have hE1 : 1 ≤ (|s.im| + 2) ^ E := Real.one_le_rpow hx (le_max_right _ _)
  rcases le_or_gt (1 / 2) s.re with hre | hre
  · refine (norm_sub_one_mul_riemannZeta_le_of_half_le_re hre).trans (hX.trans ?_)
    rw [hsplit, mul_assoc]
    gcongr
    calc (|s.im| + 2) ^ (2 : ℝ) = 1 * ((|s.im| + 2) ^ (2 : ℝ) * 1) := by ring
      _ ≤ max C₂ 1 * ((|s.im| + 2) ^ (2 : ℝ) * (|s.im| + 2) ^ E) := by gcongr; simp
  obtain ⟨-, hQ⟩ := hΓ s ⟨ha, hb⟩ ((le_max_left _ _).trans ht)
  simp only [LFunctions.riemannZetaData_dual, LFunctions.riemannZetaData_gammaFactor,
    LFunctions.riemannZetaData_degree, Nat.cast_one] at hQ
  have hpow : |s.im| ^ (1 / 2 * (1 - 2 * s.re)) ≤ (|s.im| + 2) ^ E :=
    (Real.rpow_le_rpow (abs_nonneg _) (by linarith) (by nlinarith)).trans
      (Real.rpow_le_rpow_of_exponent_le hx (le_max_of_le_left (by linarith)))
  refine (norm_sub_one_mul_riemannZeta_le_of_re_le_half hre.le ht1).trans ?_
  rw [hsplit]
  calc (‖s‖ + 3) ^ 2 * ‖Gammaℝ (1 - s) / Gammaℝ s‖
      ≤ (K ^ 2 * (|s.im| + 2) ^ (2 : ℝ)) * (max C₂ 1 * (|s.im| + 2) ^ E) := by
        gcongr
        exact hQ.trans (by gcongr; exact le_max_left _ _)
    _ = _ := by ring

/-- **Polynomial growth of `(s - 1) ζ(s)` on vertical strips.** On every closed vertical strip
`a ≤ Re s ≤ b`, the entire function `LFunctionTrivChar₁ 1`, which is `(s - 1) ζ(s)` away from
`s = 1` and the residue `1` at `s = 1`, satisfies `‖LFunctionTrivChar₁ 1 s‖ ≤ C (|Im s| + 2) ^ B`.
The strip may reach into `Re s < 0`. -/
theorem exists_norm_LFunctionTrivChar₁_one_le_rpow (a b : ℝ) :
    ∃ C B : ℝ, ∀ s : ℂ, a ≤ s.re → s.re ≤ b →
      ‖LFunctionTrivChar₁ 1 s‖ ≤ C * (|s.im| + 2) ^ B := by
  obtain ⟨T, C₁, B, hT, hC₁, hB, hbig⟩ := exists_norm_sub_one_mul_riemannZeta_le_of_le_abs_im a b
  obtain ⟨C₀, hC₀⟩ := (isCompact_Icc.reProdIm isCompact_Icc : IsCompact (Icc a b ×ℂ Icc (-T) T))
    |>.exists_bound_of_continuousOn (differentiable_LFunctionTrivChar₁ 1).continuous.continuousOn
  refine ⟨max C₀ 0 + C₁, B, fun s ha hb ↦ ?_⟩
  have hx : 1 ≤ (|s.im| + 2) ^ B := Real.one_le_rpow (by linarith [abs_nonneg s.im]) hB
  have hx0 : 0 ≤ (|s.im| + 2) ^ B := zero_le_one.trans hx
  rcases le_or_gt |s.im| T with ht | ht
  · have := hC₀ s (mem_reProdIm.2 ⟨⟨ha, hb⟩, abs_le.1 ht⟩)
    nlinarith [le_max_left C₀ 0, le_max_right C₀ 0, mul_nonneg hC₁ hx0]
  · have hs1 : s ≠ 1 := fun h ↦ by subst h; simp at ht; linarith
    rw [LFunctionTrivChar₁, Function.update_of_ne hs1, LFunctionTrivChar, LFunction_modOne_eq]
    nlinarith [hbig s ha hb ht.le, le_max_right C₀ 0, mul_nonneg (le_max_right C₀ 0) hx0]

end TauCeti
