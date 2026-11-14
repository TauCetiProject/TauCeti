/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.MellinInversion
public import TauCeti.Analysis.Contour.Residue.Basic
public import TauCeti.NumberTheory.LSeries.Quadratic.Pair.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import TauCeti.Analysis.Contour.Residue.ChangeOfVariables
import TauCeti.Analysis.MellinInversion
import TauCeti.Analysis.SpecialFunctions.Gamma.Order
import TauCeti.Analysis.SpecialFunctions.Gamma.Residue
import TauCeti.Analysis.SpecialFunctions.Gamma.Vertical
import TauCeti.NumberTheory.DirichletCharacter.LFunction.Bounds
import TauCeti.NumberTheory.DirichletCharacter.LFunction.Completed.Basic
import TauCeti.NumberTheory.DirichletCharacter.Quadratic
import TauCeti.NumberTheory.LSeries.CompletedRiemannZeta
import TauCeti.NumberTheory.LSeries.Quadratic.Pair.Residue
import TauCeti.NumberTheory.LSeries.RiemannZeta.Bounds
import TauCeti.NumberTheory.LSeries.SmoothedSum
import TauCeti.NumberTheory.LSeries.Twist

/-!
# Smoothed Mellin contour shift and error bound for the four-factor L-function product

In Goldfeld's proof of Siegel's theorem, the Dirichlet coefficients `a(n)` of the four-factor
product `F(s) = ζ(s) L(s, χ) L(s, ψ) L(s, χ.mul ψ)` (`DirichletCharacter.zetaMulPairCoeffs`) are
twisted by `n^{-β}` (`1 / 2 < β < 3 / 2`, `β ≠ 1`) and exponentially smoothed by `e^{-n x}`
(`x > 0`). On any vertical line `Re w = σ > 0` with `σ + β > 1`, Mellin inversion of `Γ` identifies
this smoothed sum with the vertical integral `mellinInv σ (fun w ↦ Γ(w) F(w + β)) x`.

Shifting the line of integration left from `σ₁ = 2 - β` to `σ₀ = 1 / 2 - β` (`Re(w + β) = 1 / 2`)
crosses two distinct poles in the open strip `1 / 2 - β < Re w < 2 - β`:

* `w = 0`, where `Γ` has a simple pole of residue `1` while `w ↦ x^{-w} F(w + β)` is analytic
  (since `β ≠ 1`), contributing `F(β)`;
* `w = 1 - β`, where `s = w + β` crosses `1`, contributing
  `Res_{s = 1} (F(s) Γ(s - β) x^{β - s})`.

Evaluating the `s = 1` residue with `DirichletCharacter.residue_pair_mul_of_mul_ne_one` and
`DirichletCharacter.residue_pair_mul_of_mul_eq_one` produces both the simple-pole (`χ.mul ψ ≠ 1`)
and double-pole (`χ.mul ψ = 1`) shifted formulas. On the shifted line `Re w = 1 / 2 - β`,
combining `‖F(1 / 2 + i t)‖ ≤ 625 (M N)² (1 + t²)²` with
`‖Γ((1 / 2 - β) + i t)‖ ≤ 120 / ((β - 1 / 2) (3 / 2 - β) (1 + t²)³)` yields an integrable
`(1 + t²)⁻¹` majorant and the explicit error estimate
`‖mellinInv (1 / 2 - β) (fun w ↦ Γ(w) F(w + β)) x‖ ≤
  37500 (M N)² / ((β - 1 / 2) (3 / 2 - β)) · x^{β - 1 / 2}`.
For quadratic characters, `a(n) ≥ 0` and `a(1) = 1` bound the smoothed sum below by `e^{-x}`,
producing Goldfeld's real-part inequalities in both the simple-pole and double-pole regimes.

## Main results

* `DirichletCharacter.norm_pair_le_of_one_half_le_norm_sub_one`,
  `DirichletCharacter.norm_pair_le_of_one_half_le_re`,
  `DirichletCharacter.norm_pair_one_half_add_mul_I_le`: explicit vertical growth bounds on `F(s)`
  for arbitrary characters (principal or nonprincipal).
* `DirichletCharacter.hasSum_zetaMulPairCoeffs_div_cpow_mul_exp`: Mellin integral representation of
  `∑ a(n) n^{-β} e^{-n x}` on `Re w = σ > 0` with `σ + β > 1`.
* `DirichletCharacter.tsum_zetaMulPairCoeffs_div_cpow_mul_exp_eq`,
  `DirichletCharacter.tsum_zetaMulPairCoeffs_div_cpow_mul_exp_eq_of_mul_ne_one`,
  `DirichletCharacter.tsum_zetaMulPairCoeffs_div_cpow_mul_exp_eq_of_mul_eq_one`: Goldfeld's shifted
  contour formula in general and specialized to the simple-pole and double-pole cases.
* `DirichletCharacter.norm_mellinInv_Gamma_mul_pair_le`: explicit `O((M N)² x^{β - 1 / 2})` bound
  on the shifted vertical integral across `1 / 2 < β < 3 / 2`.
* `DirichletCharacter.exp_neg_le_tsum_zetaMulPairCoeffs`,
  `DirichletCharacter.exp_neg_le_re_pair_add_of_mul_ne_one`,
  `DirichletCharacter.exp_neg_le_re_pair_add_of_mul_eq_one`: quadratic positivity lower bound
  `e^{-x}` and Goldfeld's resulting real-part inequalities.

## References

* D. Goldfeld, *A simple proof of Siegel's theorem*, Proc. Nat. Acad. Sci. USA 71 (1974), 1055.
* H. Iwaniec, E. Kowalski, *Analytic Number Theory*, §5.9.
* H. Davenport, *Multiplicative Number Theory*, Ch. 21.
-/

public section

open Set MeasureTheory Filter
open scoped Real Topology ComplexOrder
open Complex hiding exp continuous_exp

namespace DirichletCharacter

variable {M N : ℕ} [NeZero M] [NeZero N]
variable (χ : DirichletCharacter ℂ M) (ψ : DirichletCharacter ℂ N)

private noncomputable abbrev pairLFunction (s : ℂ) : ℂ :=
  riemannZeta s * χ.LFunction s * ψ.LFunction s * (χ.mul ψ).LFunction s

private theorem analyticAt_pair {s : ℂ} (hs : s ≠ 1) : AnalyticAt ℂ (pairLFunction χ ψ) s :=
  (((analyticOn_riemannZeta s hs).mul (χ.analyticAt_LFunction (.inl hs))).mul
    (ψ.analyticAt_LFunction (.inl hs))).mul ((χ.mul ψ).analyticAt_LFunction (.inl hs))

private theorem meromorphic_pair : Meromorphic (pairLFunction χ ψ) := fun s ↦
  (((TauCeti.meromorphic_riemannZeta s).mul (χ.meromorphic_LFunction s)).mul
    (ψ.meromorphic_LFunction s)).mul ((χ.mul ψ).meromorphic_LFunction s)

/-- On `Re s > 0` outside the open disk `‖s - 1‖ < 1 / 2`, the four-factor product
`ζ(s) L(s, χ) L(s, ψ) L(s, χ.mul ψ)` of arbitrary characters of levels `M` and `N` satisfies
`‖F(s)‖ ≤ (M N)² (3 + ‖s‖ / Re s)⁴`. Neither quadraticity nor nonprincipality is required. -/
theorem norm_pair_le_of_one_half_le_norm_sub_one {s : ℂ} (hs : 0 < s.re) (hs1 : 1 / 2 ≤ ‖s - 1‖) :
    ‖riemannZeta s * χ.LFunction s * ψ.LFunction s * (χ.mul ψ).LFunction s‖ ≤
      ((M : ℝ) * N) ^ 2 * (3 + ‖s‖ / s.re) ^ 4 := by
  have hinv : ‖s - 1‖⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ (by linarith) two_pos]
    simpa using hs1
  have hζ : ‖riemannZeta s‖ ≤ 3 + ‖s‖ / s.re :=
    (TauCeti.norm_riemannZeta_le hs).trans (by linarith)
  have hlcm : (Nat.lcm M N : ℝ) ≤ (M : ℝ) * N := by
    exact_mod_cast Nat.le_of_dvd (Nat.mul_pos (NeZero.pos M) (NeZero.pos N)) (Nat.lcm_dvd_mul M N)
  have hpos : 0 ≤ 3 + ‖s‖ / s.re := by positivity
  rw [norm_mul, norm_mul, norm_mul]
  calc ‖riemannZeta s‖ * ‖χ.LFunction s‖ * ‖ψ.LFunction s‖ * ‖(χ.mul ψ).LFunction s‖
      ≤ (3 + ‖s‖ / s.re) * ((M : ℝ) * (3 + ‖s‖ / s.re)) *
          ((N : ℝ) * (3 + ‖s‖ / s.re)) * ((Nat.lcm M N : ℝ) * (3 + ‖s‖ / s.re)) :=
        mul_le_mul
          (mul_le_mul
            (mul_le_mul hζ (χ.norm_LFunction_le_of_one_half_le_norm_sub_one hs hs1)
              (norm_nonneg _) hpos)
            (ψ.norm_LFunction_le_of_one_half_le_norm_sub_one hs hs1) (norm_nonneg _)
            (by positivity))
          ((χ.mul ψ).norm_LFunction_le_of_one_half_le_norm_sub_one hs hs1) (norm_nonneg _)
          (by positivity)
    _ = (M : ℝ) * N * (Nat.lcm M N : ℝ) * (3 + ‖s‖ / s.re) ^ 4 := by ring
    _ ≤ (M : ℝ) * N * ((M : ℝ) * N) * (3 + ‖s‖ / s.re) ^ 4 := by gcongr
    _ = ((M : ℝ) * N) ^ 2 * (3 + ‖s‖ / s.re) ^ 4 := by ring

/-- On the half-plane `Re s ≥ 1 / 2` outside `‖s - 1‖ < 1 / 2`, the four-factor product satisfies
the uniform polynomial vertical bound `‖F(s)‖ ≤ 625 (M N)² (1 + (Im s)²)²`. -/
theorem norm_pair_le_of_one_half_le_re {s : ℂ} (hre : 1 / 2 ≤ s.re) (hs1 : 1 / 2 ≤ ‖s - 1‖) :
    ‖riemannZeta s * χ.LFunction s * ψ.LFunction s * (χ.mul ψ).LFunction s‖ ≤
      625 * ((M : ℝ) * N) ^ 2 * (1 + s.im ^ 2) ^ 2 := by
  have hs_pos : 0 < s.re := by linarith
  have hsq : ‖s‖ ^ 2 ≤ (2 * s.re * √(1 + s.im ^ 2)) ^ 2 := by
    rw [Complex.sq_norm, normSq_apply, mul_pow, mul_pow, Real.sq_sqrt (by positivity)]
    have hre_sq : 1 ≤ 4 * s.re ^ 2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_right hre_sq (sq_nonneg s.im), sq_nonneg s.re]
  have hnorm : ‖s‖ ≤ 2 * s.re * √(1 + s.im ^ 2) :=
    le_of_pow_le_pow_left₀ two_ne_zero (by positivity) hsq
  have hdiv : ‖s‖ / s.re ≤ 2 * √(1 + s.im ^ 2) :=
    (div_le_iff₀ hs_pos).mpr (by linarith)
  have hone : 1 ≤ √(1 + s.im ^ 2) := Real.le_sqrt_of_sq_le (by nlinarith [sq_nonneg s.im])
  have hbase : 3 + ‖s‖ / s.re ≤ 5 * √(1 + s.im ^ 2) := by linarith
  have hpow : (3 + ‖s‖ / s.re) ^ 4 ≤ 625 * (1 + s.im ^ 2) ^ 2 :=
    calc (3 + ‖s‖ / s.re) ^ 4 ≤ (5 * √(1 + s.im ^ 2)) ^ 4 :=
          pow_le_pow_left₀ (by positivity) hbase 4
      _ = 625 * (√(1 + s.im ^ 2) ^ 2) ^ 2 := by ring
      _ = 625 * (1 + s.im ^ 2) ^ 2 := by rw [Real.sq_sqrt (by positivity)]
  calc ‖riemannZeta s * χ.LFunction s * ψ.LFunction s * (χ.mul ψ).LFunction s‖
      ≤ ((M : ℝ) * N) ^ 2 * (3 + ‖s‖ / s.re) ^ 4 :=
        norm_pair_le_of_one_half_le_norm_sub_one χ ψ hs_pos hs1
    _ ≤ ((M : ℝ) * N) ^ 2 * (625 * (1 + s.im ^ 2) ^ 2) :=
        mul_le_mul_of_nonneg_left hpow (by positivity)
    _ = 625 * ((M : ℝ) * N) ^ 2 * (1 + s.im ^ 2) ^ 2 := by ring

/-- On the critical line `s = 1 / 2 + i t`, the four-factor product satisfies
`‖F(1 / 2 + i t)‖ ≤ 625 (M N)² (1 + t²)²` for all `t : ℝ`. -/
theorem norm_pair_one_half_add_mul_I_le (t : ℝ) :
    ‖riemannZeta (1 / 2 + t * I) * χ.LFunction (1 / 2 + t * I) *
        ψ.LFunction (1 / 2 + t * I) * (χ.mul ψ).LFunction (1 / 2 + t * I)‖ ≤
      625 * ((M : ℝ) * N) ^ 2 * (1 + t ^ 2) ^ 2 := by
  have hs1 : 1 / 2 ≤ ‖(1 / 2 : ℂ) + t * I - 1‖ := by
    have h := abs_re_le_norm ((1 / 2 : ℂ) + t * I - 1)
    norm_num at h
    exact h
  simpa using norm_pair_le_of_one_half_le_re χ ψ (s := 1 / 2 + t * I) (by simp) hs1

/-- **Mellin integral representation of the twisted smoothed four-factor sum.** On any vertical line
`Re w = σ > 0` with `σ + β > 1` and `x > 0`, the exponentially smoothed twisted Dirichlet series
`∑ n, a(n) n^{-β} e^{-n x}` sums to `mellinInv σ (fun w ↦ Γ(w) F(w + β)) x`. -/
theorem hasSum_zetaMulPairCoeffs_div_cpow_mul_exp {σ β x : ℝ} (hσ : 0 < σ) (hσβ : 1 < σ + β)
    (hx : 0 < x) :
    HasSum (fun n : ℕ ↦ χ.zetaMulPairCoeffs ψ n / (n : ℂ) ^ (β : ℂ) * Real.exp (-n * x))
      (mellinInv σ (fun w ↦ Gamma w * (riemannZeta (w + β) * χ.LFunction (w + β) *
        ψ.LFunction (w + β) * (χ.mul ψ).LFunction (w + β))) x) := by
  set g : ℕ → ℂ := fun n ↦ χ.zetaMulPairCoeffs ψ n * (n : ℂ) ^ (-(β : ℂ))
  have hg0 : g 0 = 0 := by simp [g]
  have hsumm : LSeriesSummable g σ := by
    rw [LSeriesSummable,
      funext (TauCeti.LSeries.term_mul_natCast_cpow_neg (χ.zetaMulPairCoeffs ψ) β σ)]
    exact (LSeriesHasSum_zetaMulPairCoeffs χ ψ (s := (σ : ℂ) + β)
      (by simp [hσβ])).LSeriesSummable
  have hsum := TauCeti.LSeries.hasSum_mellinInv_Gamma_mul_LSeries hg0 hσ hsumm hx
  have hterm : (fun n : ℕ ↦ χ.zetaMulPairCoeffs ψ n / (n : ℂ) ^ (β : ℂ) * Real.exp (-n * x)) =
      fun n : ℕ ↦ g n * Real.exp (-n * x) := by
    funext n
    simp [g, div_eq_mul_inv, cpow_neg]
  have hline (t : ℝ) : LSeries g (σ + t * I) = pairLFunction χ ψ ((σ + t * I) + β) := by
    rw [TauCeti.LSeries.LSeries_mul_natCast_cpow_neg]
    exact (LSeriesHasSum_zetaMulPairCoeffs χ ψ (by simp; linarith)).LSeries_eq
  rw [hterm]
  convert hsum using 1
  simp_rw [mellinInv, hline]

/-- On `1 / 2 - β ≤ u ≤ 2 - β` at height `±T` with `T ≥ 1`, the shifted integrand
`w ↦ Γ(w) F(w + β)` decays uniformly as `O(1 / T)`. -/
private theorem exists_norm_Gamma_mul_pair_horiz_le (β : ℝ) :
    ∃ B : ℝ → ℝ, Tendsto B atTop (𝓝 0) ∧
      ∀ᶠ (T : ℝ) in atTop, ∀ u ∈ Icc (1 / 2 - β) (2 - β),
        ‖Gamma ((u : ℂ) + T * I) * pairLFunction χ ψ ((u : ℂ) + T * I + β)‖ ≤ B T ∧
        ‖Gamma ((u : ℂ) - T * I) * pairLFunction χ ψ ((u : ℂ) - T * I + β)‖ ≤ B T := by
  obtain ⟨C, _, hC⟩ := exists_norm_Gamma_le_div_pow_of_re_mem_Icc (1 / 2 - β) (2 - β) 5
  set K : ℝ := C * (2500 * ((M : ℝ) * N) ^ 2)
  refine ⟨fun T ↦ K / T, tendsto_const_nhds.div_atTop tendsto_id, ?_⟩
  have hstep {z : ℂ} {T : ℝ} (hT : 1 ≤ T) (hz_re : z.re ∈ Icc (1 / 2 - β) (2 - β))
      (hz_im : |z.im| = T) : ‖Gamma z * pairLFunction χ ψ (z + β)‖ ≤ K / T := by
    have hΓ : ‖Gamma z‖ ≤ C / T ^ 5 := by simpa [hz_im] using hC z hz_re (hz_im ▸ hT)
    have hs1 : 1 / 2 ≤ ‖z + β - 1‖ := by
      have him := abs_im_le_norm (z + β - 1)
      have him_eq : |(z + β - 1).im| = T := by simpa using hz_im
      linarith
    have hF : ‖pairLFunction χ ψ (z + β)‖ ≤ 2500 * ((M : ℝ) * N) ^ 2 * T ^ 4 := by
      have h1 := norm_pair_le_of_one_half_le_re χ ψ (s := z + β) (by simp; linarith [hz_re.1]) hs1
      have h2 : (1 + (z + β).im ^ 2) ^ 2 ≤ 4 * T ^ 4 := by
        have hsq : (z + β).im ^ 2 = T ^ 2 := by
          have := congrArg (· ^ 2) hz_im; simpa [sq_abs] using this
        have hT2 : 1 ≤ T ^ 2 := by nlinarith
        calc (1 + (z + β).im ^ 2) ^ 2 = (1 + T ^ 2) ^ 2 := by rw [hsq]
          _ ≤ (T ^ 2 + T ^ 2) ^ 2 := pow_le_pow_left₀ (by positivity) (by linarith) 2
          _ = 4 * T ^ 4 := by ring
      exact h1.trans (by nlinarith [sq_nonneg ((M : ℝ) * N)])
    rw [norm_mul]
    calc ‖Gamma z‖ * ‖pairLFunction χ ψ (z + β)‖
        ≤ (C / T ^ 5) * (2500 * ((M : ℝ) * N) ^ 2 * T ^ 4) :=
          mul_le_mul hΓ hF (norm_nonneg _) (by positivity)
      _ = K / T := by dsimp [K]; field_simp
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT u hu
  have hT_abs : |T| = T := abs_of_nonneg (zero_le_one.trans hT)
  exact ⟨hstep hT (by simpa using hu) (by simpa using hT_abs),
    hstep hT (by simpa using hu) (by simpa using hT_abs)⟩

private theorem residue_cpow_mul_Gamma_mul_pair_zero {β x : ℝ} (hβ : β ≠ 1) (hx : x ≠ 0) :
    TauCeti.Contour.residue (fun z ↦ (x : ℂ) ^ (-z) * (Gamma z * pairLFunction χ ψ (z + β))) 0 =
      pairLFunction χ ψ β := by
  have hcomm : (fun z ↦ (x : ℂ) ^ (-z) * (Gamma z * pairLFunction χ ψ (z + β))) =
      fun z ↦ Gamma z * ((x : ℂ) ^ (-z) * pairLFunction χ ψ (z + β)) :=
    funext fun _ ↦ by ring
  have hcpow : AnalyticAt ℂ (fun z : ℂ ↦ (x : ℂ) ^ (-z)) 0 :=
    (differentiable_id.neg.const_cpow (.inl (ofReal_ne_zero.mpr hx))).analyticAt 0
  have hp : AnalyticAt ℂ (fun z : ℂ ↦ pairLFunction χ ψ (z + β)) 0 :=
    AnalyticAt.comp (g := pairLFunction χ ψ) (f := fun z : ℂ ↦ z + β)
      (analyticAt_pair χ ψ (by simpa using ofReal_ne_one.mpr hβ)) (by fun_prop)
  have hw : AnalyticAt ℂ (fun z : ℂ ↦ (x : ℂ) ^ (-z) * pairLFunction χ ψ (z + β)) 0 :=
    hcpow.mul hp
  rw [hcomm, residue_Gamma_mul_zero hw]
  simp

private theorem residue_cpow_mul_Gamma_mul_pair_one_sub (β x : ℝ) :
    TauCeti.Contour.residue
        (fun z ↦ (x : ℂ) ^ (-z) * (Gamma z * pairLFunction χ ψ (z + β))) (1 - β) =
      TauCeti.Contour.residue
        (fun s ↦ pairLFunction χ ψ s * (Gamma (s - β) * (x : ℂ) ^ ((β : ℂ) - s))) 1 := by
  have htr := TauCeti.Contour.residue_comp_add_const
    (fun s ↦ pairLFunction χ ψ s * (Gamma (s - β) * (x : ℂ) ^ ((β : ℂ) - s))) β (1 - β)
  rw [show (1 - (β : ℂ)) + β = 1 by ring] at htr
  rw [← htr]
  refine congrArg (TauCeti.Contour.residue · _) (funext fun z ↦ ?_)
  rw [show z + (β : ℂ) - β = z by ring, show (β : ℂ) - (z + β) = -z by ring]
  ring

private theorem analyticAt_Gamma_mul_pair {β : ℝ} {z : ℂ}
    (hz_Γ : ∀ n : ℕ, z ≠ -n) (hz_1 : z + β ≠ 1) :
    AnalyticAt ℂ (fun w ↦ Gamma w * pairLFunction χ ψ (w + β)) z :=
  (analyticAt_Gamma hz_Γ).mul
    (AnalyticAt.comp (g := pairLFunction χ ψ) (f := fun w : ℂ ↦ w + β)
      (analyticAt_pair χ ψ hz_1) (by fun_prop))

private theorem meromorphicAt_Gamma_mul_pair (β : ℝ) (s : ℂ) :
    MeromorphicAt (fun w ↦ Gamma w * pairLFunction χ ψ (w + β)) s := by
  have hΓm : MeromorphicAt Gamma s := by
    simpa only [Pi.inv_def, inv_inv] using
      (differentiable_one_div_Gamma.analyticAt s).meromorphicAt.inv
  have hpm : MeromorphicAt (fun w ↦ pairLFunction χ ψ (w + β)) s :=
    MeromorphicAt.comp_analyticAt (x := s) (g := fun w : ℂ ↦ w + β)
      (meromorphic_pair χ ψ (s + β)) (by fun_prop)
  exact hΓm.mul hpm

/-- **Goldfeld's shifted contour formula (general residue form).** For `1 / 2 < β < 3 / 2` with
`β ≠ 1` and `x > 0`, shifting the Mellin inversion contour of `w ↦ Γ(w) F(w + β)` from `2 - β` to
`1 / 2 - β` crosses the distinct poles `w = 0` and `w = 1 - β`, yielding
`∑ n, a(n) n^{-β} e^{-n x} = F(β) + Res_{s = 1} (F(s) Γ(s - β) x^{β - s}) +
  mellinInv (1 / 2 - β) (fun w ↦ Γ(w) F(w + β)) x`. -/
theorem tsum_zetaMulPairCoeffs_div_cpow_mul_exp_eq {β x : ℝ} (hβ₀ : 1 / 2 < β) (hβ₁ : β < 3 / 2)
    (hβ : β ≠ 1) (hx : 0 < x) :
    ∑' n : ℕ, χ.zetaMulPairCoeffs ψ n / (n : ℂ) ^ (β : ℂ) * Real.exp (-n * x) =
      riemannZeta β * χ.LFunction β * ψ.LFunction β * (χ.mul ψ).LFunction β +
        TauCeti.Contour.residue
          (fun s ↦ riemannZeta s * χ.LFunction s * ψ.LFunction s * (χ.mul ψ).LFunction s *
            (Gamma (s - β) * (x : ℂ) ^ ((β : ℂ) - s))) 1 +
        mellinInv (1 / 2 - β)
          (fun w ↦ Gamma w * (riemannZeta (w + β) * χ.LFunction (w + β) *
            ψ.LFunction (w + β) * (χ.mul ψ).LFunction (w + β))) x := by
  classical
  set f : ℂ → ℂ := fun w ↦ Gamma w * pairLFunction χ ψ (w + β)
  obtain ⟨B, hB, hbound⟩ := exists_norm_Gamma_mul_pair_horiz_le χ ψ β
  have hne01 : (0 : ℂ) ≠ 1 - β := fun h ↦ hβ (by have := congrArg re h; simp at this; linarith)
  have hanal (z : ℂ) (hz : z.re ∈ Icc (1 / 2 - β) (2 - β))
      (hzS : z ∉ ({0, 1 - (β : ℂ)} : Finset ℂ)) : AnalyticAt ℂ f z := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hzS
    refine analyticAt_Gamma_mul_pair χ ψ (fun n hn ↦ ?_) fun h1 ↦ hzS.2 (by linear_combination h1)
    rcases n with _ | k
    · exact hzS.1 (by simpa using hn)
    · have hre := congrArg re hn; simp at hre; linarith [hz.1, (Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  have hv {σ : ℝ} (h1 : 1 / 2 ≤ σ + β) (h2 : 1 / 2 ≤ |σ + β - 1|) (hσ : ∀ n : ℕ, σ ≠ -n) :
      VerticalIntegrable f σ := by
    have hc : Continuous fun t : ℝ ↦ pairLFunction χ ψ (σ + t * I + β) :=
      continuous_iff_continuousAt.mpr fun t ↦ ContinuousAt.comp (g := pairLFunction χ ψ)
        (f := fun u : ℝ ↦ (σ : ℂ) + u * I + β)
        (analyticAt_pair χ ψ fun h ↦ by
          have := congrArg re h; simp at this
          linarith [abs_eq_zero.mpr (show σ + β - 1 = 0 by linarith)]).continuousAt (by fun_prop)
    simpa only [VerticalIntegrable, smul_eq_mul, f] using
      verticalIntegrable_Gamma_smul_of_norm_le (E := ℂ) (g := fun w ↦ pairLFunction χ ψ (w + β))
        (C := 625 * ((M : ℝ) * N) ^ 2) (m := 2) hσ hc.aestronglyMeasurable fun t ↦ by
          have hs1 : 1 / 2 ≤ ‖(σ : ℂ) + t * I + β - 1‖ :=
            h2.trans (by simpa [add_right_comm] using abs_re_le_norm ((σ : ℂ) + t * I + β - 1))
          simpa [pairLFunction] using
            norm_pair_le_of_one_half_le_re χ ψ (s := σ + t * I + β) (by simp; linarith) hs1
  have hshift := mellinInv_eq_mellinInv_add_sum_residue_of_norm_le
    (f := f) (S := {0, 1 - (β : ℂ)}) (σ₀ := 1 / 2 - β) (σ₁ := 2 - β) (by linarith) hx.le
    hanal (fun s _ ↦ meromorphicAt_Gamma_mul_pair χ ψ β s)
    (fun s hs ↦ by
      rcases Finset.mem_insert.mp hs with rfl | hs'
      · simp; constructor <;> linarith
      · rw [Finset.mem_singleton.mp hs']; simp; linarith)
    (hv (by linarith) (by norm_num) fun n hn ↦ by
      rcases n with _ | k
      · simp at hn; linarith
      · push_cast at hn; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)])
    (hv (by linarith) (by norm_num) fun n hn ↦ by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
    hB hbound
  rw [(hasSum_zetaMulPairCoeffs_div_cpow_mul_exp χ ψ (σ := 2 - β) (by linarith) (by linarith)
    hx).tsum_eq]
  change mellinInv (2 - β) f x = _
  rw [hshift, Finset.sum_pair hne01, residue_cpow_mul_Gamma_mul_pair_zero χ ψ hβ hx.ne',
    residue_cpow_mul_Gamma_mul_pair_one_sub χ ψ β x]
  ring

omit [NeZero M] [NeZero N] in
private theorem analyticAt_Gamma_sub_mul_cpow {β : ℝ} (x : ℝ) (hβ : ∀ n : ℕ, β ≠ n + 1) :
    AnalyticAt ℂ (fun s ↦ Gamma (s - β) * (x : ℂ) ^ ((β : ℂ) - s)) 1 := by
  rcases eq_or_ne x 0 with rfl | hx
  · have hne : (β : ℂ) - 1 ≠ 0 := sub_ne_zero.mpr (ofReal_ne_one.mpr (by simpa using hβ 0))
    refine (analyticAt_const (v := (0 : ℂ))).congr ?_
    filter_upwards [((continuous_const.sub continuous_id).continuousAt.eventually_ne hne)]
      with s (hs : (β : ℂ) - s ≠ 0)
    simp [zero_cpow hs]
  · have hcpow : AnalyticAt ℂ (fun s : ℂ ↦ (x : ℂ) ^ ((β : ℂ) - s)) 1 :=
      (((differentiable_const (β : ℂ)).sub differentiable_id).const_cpow
        (.inl (ofReal_ne_zero.mpr hx))).analyticAt 1
    refine ((analyticAt_Gamma fun n hn ↦ ?_).comp (by fun_prop)).mul hcpow
    exact hβ n (by have := congrArg re hn; simp at this; linarith)

/-- **Goldfeld's shifted contour formula (simple-pole case).** When `χ ≠ 1`, `ψ ≠ 1`, and
`χ.mul ψ ≠ 1`, the `s = 1` pole is simple with residue
`L(1, χ) L(1, ψ) L(1, χ.mul ψ) Γ(1 - β) x^{β - 1}`. -/
theorem tsum_zetaMulPairCoeffs_div_cpow_mul_exp_eq_of_mul_ne_one
    (hχ : χ ≠ 1) (hψ : ψ ≠ 1) (hχψ : χ.mul ψ ≠ 1) {β x : ℝ}
    (hβ₀ : 1 / 2 < β) (hβ₁ : β < 3 / 2) (hβ : β ≠ 1) (hx : 0 < x) :
    ∑' n : ℕ, χ.zetaMulPairCoeffs ψ n / (n : ℂ) ^ (β : ℂ) * Real.exp (-n * x) =
      riemannZeta β * χ.LFunction β * ψ.LFunction β * (χ.mul ψ).LFunction β +
        χ.LFunction 1 * ψ.LFunction 1 * (χ.mul ψ).LFunction 1 *
          (Gamma (1 - β) * (x : ℂ) ^ ((β : ℂ) - 1)) +
        mellinInv (1 / 2 - β)
          (fun w ↦ Gamma w * (riemannZeta (w + β) * χ.LFunction (w + β) *
            ψ.LFunction (w + β) * (χ.mul ψ).LFunction (w + β))) x := by
  have hanal := analyticAt_Gamma_sub_mul_cpow x fun n hn ↦ by
    rcases n with _ | k
    · exact hβ (by simpa using hn)
    · push_cast at hn; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  rw [tsum_zetaMulPairCoeffs_div_cpow_mul_exp_eq χ ψ hβ₀ hβ₁ hβ hx,
    residue_pair_mul_of_mul_ne_one χ ψ hχ hψ hχψ hanal]

/-- **Goldfeld's shifted contour formula (double-pole case).** When `χ ≠ 1` and `χ.mul ψ = 1`
(which implies `ψ ≠ 1`), the `s = 1` pole is double and its residue is the derivative at `1` of the
analytic regularization multiplied by `Γ(s - β) x^{β - s}`. -/
theorem tsum_zetaMulPairCoeffs_div_cpow_mul_exp_eq_of_mul_eq_one
    (hχ : χ ≠ 1) (hχψ : χ.mul ψ = 1) {β x : ℝ}
    (hβ₀ : 1 / 2 < β) (hβ₁ : β < 3 / 2) (hβ : β ≠ 1) (hx : 0 < x) :
    ∑' n : ℕ, χ.zetaMulPairCoeffs ψ n / (n : ℂ) ^ (β : ℂ) * Real.exp (-n * x) =
      riemannZeta β * χ.LFunction β * ψ.LFunction β * (χ.mul ψ).LFunction β +
        deriv (fun s ↦ LFunctionTrivChar₁ 1 s * χ.LFunction s * ψ.LFunction s *
          LFunctionTrivChar₁ (Nat.lcm M N) s *
          (Gamma (s - β) * (x : ℂ) ^ ((β : ℂ) - s))) 1 +
        mellinInv (1 / 2 - β)
          (fun w ↦ Gamma w * (riemannZeta (w + β) * χ.LFunction (w + β) *
            ψ.LFunction (w + β) * (χ.mul ψ).LFunction (w + β))) x := by
  have hψ : ψ ≠ 1 := by
    rintro rfl
    rw [DirichletCharacter.mul, map_one, mul_one, changeLevel_eq_one_iff] at hχψ
    exact hχ hχψ
  have hanal := analyticAt_Gamma_sub_mul_cpow x fun n hn ↦ by
    rcases n with _ | k
    · exact hβ (by simpa using hn)
    · push_cast at hn; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  rw [tsum_zetaMulPairCoeffs_div_cpow_mul_exp_eq χ ψ hβ₀ hβ₁ hβ hx,
    residue_pair_mul_of_mul_eq_one χ ψ hχ hψ hχψ hanal]

/-- **Goldfeld's vertical-line error estimate.** Across the pole-free strip `1 / 2 < β < 3 / 2` and
for all `x ≥ 0`, the shifted Mellin integral on `Re w = 1 / 2 - β` satisfies
`‖mellinInv (1 / 2 - β) (fun w ↦ Γ(w) F(w + β)) x‖ ≤
  37500 (M N)² / ((β - 1 / 2) (3 / 2 - β)) · x^{β - 1 / 2}`. -/
theorem norm_mellinInv_Gamma_mul_pair_le {β x : ℝ} (hβ₀ : 1 / 2 < β) (hβ₁ : β < 3 / 2)
    (hx : 0 ≤ x) :
    ‖mellinInv (1 / 2 - β)
        (fun w ↦ Gamma w * (riemannZeta (w + β) * χ.LFunction (w + β) *
          ψ.LFunction (w + β) * (χ.mul ψ).LFunction (w + β))) x‖ ≤
      37500 * ((M : ℝ) * N) ^ 2 / ((β - 1 / 2) * (3 / 2 - β)) * x ^ (β - 1 / 2) := by
  set σ : ℝ := 1 / 2 - β
  set D : ℝ := (β - 1 / 2) * (3 / 2 - β)
  have hD : 0 < D := mul_pos (by linarith) (by linarith)
  have hint_le : ∫ t : ℝ, ‖Gamma (σ + t * I) * pairLFunction χ ψ (σ + t * I + β)‖ ≤
      (75000 * ((M : ℝ) * N) ^ 2 / D) * π := by
    rw [← integral_univ_inv_one_add_sq, ← integral_const_mul]
    refine integral_mono_of_nonneg (Eventually.of_forall fun _ ↦ norm_nonneg _)
      (integrable_inv_one_add_sq.const_mul _) (Eventually.of_forall fun t ↦ ?_)
    have hΓ := norm_Gamma_add_mul_I_le_of_mem_Ioo (σ := σ) (by dsimp [σ]; linarith)
      (by dsimp [σ]; linarith) t
    have hadd : (σ : ℂ) + t * I + β = 1 / 2 + t * I := by dsimp [σ]; push_cast; ring
    have hF : ‖pairLFunction χ ψ (σ + t * I + β)‖ ≤
        625 * ((M : ℝ) * N) ^ 2 * (1 + t ^ 2) ^ 2 := by
      rw [hadd]; exact norm_pair_one_half_add_mul_I_le χ ψ t
    have hσD : -σ * (σ + 1) = D := by dsimp [σ, D]; ring
    rw [hσD] at hΓ
    dsimp only
    rw [norm_mul]
    calc ‖Gamma (σ + t * I)‖ * ‖pairLFunction χ ψ (σ + t * I + β)‖
        ≤ (120 / (D * (1 + t ^ 2) ^ 3)) * (625 * ((M : ℝ) * N) ^ 2 * (1 + t ^ 2) ^ 2) :=
          mul_le_mul hΓ hF (norm_nonneg _) (by positivity)
      _ = 75000 * ((M : ℝ) * N) ^ 2 / D * (1 + t ^ 2)⁻¹ := by field_simp; ring
  have hm := norm_mellinInv_le σ (fun w ↦ Gamma w * pairLFunction χ ψ (w + β)) hx
  have hrpow : x ^ (-σ) = x ^ (β - 1 / 2) := by congr 1; dsimp [σ]; ring
  calc ‖mellinInv σ (fun w ↦ Gamma w * pairLFunction χ ψ (w + β)) x‖
      ≤ x ^ (-σ) / (2 * π) *
          ∫ t : ℝ, ‖Gamma (σ + t * I) * pairLFunction χ ψ (σ + t * I + β)‖ := hm
    _ ≤ x ^ (-σ) / (2 * π) * ((75000 * ((M : ℝ) * N) ^ 2 / D) * π) :=
        mul_le_mul_of_nonneg_left hint_le (div_nonneg (Real.rpow_nonneg hx _) (by positivity))
    _ = 37500 * ((M : ℝ) * N) ^ 2 / D * x ^ (β - 1 / 2) := by
        rw [hrpow]; field_simp [Real.pi_ne_zero]; ring

omit [NeZero M] [NeZero N] in
/-- For quadratic characters `χ` and `ψ`, all terms of `∑ a(n) n^{-β} e^{-n x}` are nonnegative real
numbers and the `n = 1` term is `e^{-x}`, so whenever the series converges its sum is at least
`e^{-x}` in `ComplexOrder`. -/
theorem exp_neg_le_tsum_zetaMulPairCoeffs {χ : DirichletCharacter ℂ M}
    {ψ : DirichletCharacter ℂ N} (hχ : χ.IsQuadratic) (hψ : ψ.IsQuadratic) {β x : ℝ}
    (hsum : Summable fun n : ℕ ↦
      χ.zetaMulPairCoeffs ψ n / (n : ℂ) ^ (β : ℂ) * Real.exp (-n * x)) :
    (Real.exp (-x) : ℂ) ≤
      ∑' n : ℕ, χ.zetaMulPairCoeffs ψ n / (n : ℂ) ^ (β : ℂ) * Real.exp (-n * x) := by
  set u : ℕ → ℂ := fun n ↦ χ.zetaMulPairCoeffs ψ n / (n : ℂ) ^ (β : ℂ) * Real.exp (-n * x)
  have hu_nonneg (n : ℕ) : 0 ≤ u n := by
    rcases eq_or_ne n 0 with rfl | hn
    · simp [u]
    · have hc : (n : ℂ) ^ (β : ℂ) = ((n : ℝ) ^ β : ℝ) := by
        rw [ofReal_cpow n.cast_nonneg, ofReal_natCast]
      have hd : 0 ≤ ((n : ℂ) ^ (β : ℂ))⁻¹ := by
        rw [hc, ← ofReal_inv]
        exact zero_le_real.mpr (by positivity)
      have he : 0 ≤ (Real.exp (-n * x) : ℂ) := zero_le_real.mpr (Real.exp_pos _).le
      dsimp [u]
      rw [div_eq_mul_inv]
      exact mul_nonneg (mul_nonneg (zetaMulPairCoeffs_nonneg hχ hψ n) hd) he
  have h1 : u 1 = Real.exp (-x) := by simp [u]
  rw [← h1, Complex.le_def]
  refine ⟨?_, ?_⟩
  · rw [Complex.re_tsum hsum]
    exact Summable.le_tsum (Complex.reCLM.summable hsum) 1 fun n _ ↦
      (Complex.le_def.mp (hu_nonneg n)).1
  · rw [Complex.im_tsum hsum, ← (Complex.le_def.mp (hu_nonneg 1)).2, zero_im]
    symm
    exact (tsum_congr fun n ↦ ((Complex.le_def.mp (hu_nonneg n)).2).symm).trans tsum_zero

/-- **Goldfeld's real-part lower bound (simple-pole case).** For nonprincipal quadratic characters
`χ` and `ψ` with `χ.mul ψ ≠ 1`, `1 / 2 < β < 3 / 2` with `β ≠ 1`, and `x > 0`,
`e^{-x} ≤ Re F(β) + Re(L(1, χ) L(1, ψ) L(1, χ.mul ψ)) Γ(1 - β) x^{β - 1} +
  37500 (M N)² / ((β - 1 / 2) (3 / 2 - β)) · x^{β - 1 / 2}`. -/
theorem exp_neg_le_re_pair_add_of_mul_ne_one
    {χ : DirichletCharacter ℂ M} {ψ : DirichletCharacter ℂ N}
    (hχ : χ.IsQuadratic) (hψ : ψ.IsQuadratic) (hχ1 : χ ≠ 1) (hψ1 : ψ ≠ 1)
    (hχψ : χ.mul ψ ≠ 1) {β x : ℝ} (hβ₀ : 1 / 2 < β) (hβ₁ : β < 3 / 2) (hβ : β ≠ 1)
    (hx : 0 < x) :
    Real.exp (-x) ≤
      (riemannZeta β * χ.LFunction β * ψ.LFunction β * (χ.mul ψ).LFunction β).re +
        (χ.LFunction 1 * ψ.LFunction 1 * (χ.mul ψ).LFunction 1).re *
          Real.Gamma (1 - β) * x ^ (β - 1) +
        37500 * ((M : ℝ) * N) ^ 2 / ((β - 1 / 2) * (3 / 2 - β)) * x ^ (β - 1 / 2) := by
  have hsum := (hasSum_zetaMulPairCoeffs_div_cpow_mul_exp χ ψ (σ := 2 - β) (β := β) (by linarith)
    (by linarith) hx).summable
  have hlo := (Complex.le_def.mp (exp_neg_le_tsum_zetaMulPairCoeffs hχ hψ hsum)).1
  rw [ofReal_re, tsum_zetaMulPairCoeffs_div_cpow_mul_exp_eq_of_mul_ne_one χ ψ hχ1 hψ1 hχψ
    hβ₀ hβ₁ hβ hx] at hlo
  have hΓx : Gamma ((1 : ℂ) - β) * (x : ℂ) ^ ((β : ℂ) - 1) =
      ((Real.Gamma (1 - β) * x ^ (β - 1) : ℝ) : ℂ) := by
    rw [show (1 : ℂ) - β = ((1 - β : ℝ) : ℂ) by push_cast; ring,
      show (β : ℂ) - 1 = ((β - 1 : ℝ) : ℂ) by push_cast; ring,
      Gamma_ofReal, ← ofReal_cpow hx.le, ofReal_mul]
  have hmid : (χ.LFunction 1 * ψ.LFunction 1 * (χ.mul ψ).LFunction 1 *
      (Gamma (1 - β) * (x : ℂ) ^ ((β : ℂ) - 1))).re =
      (χ.LFunction 1 * ψ.LFunction 1 * (χ.mul ψ).LFunction 1).re *
        Real.Gamma (1 - β) * x ^ (β - 1) := by
    rw [hΓx, mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero, ← mul_assoc]
  have herr := (re_le_norm _).trans (norm_mellinInv_Gamma_mul_pair_le χ ψ hβ₀ hβ₁ hx.le)
  rw [add_re, add_re, hmid] at hlo
  linarith

/-- **Goldfeld's real-part lower bound (double-pole case).** For a nonprincipal quadratic character
`χ` and a character `ψ` with `χ.mul ψ = 1` (which implies `ψ` is quadratic and nonprincipal),
`1 / 2 < β < 3 / 2` with `β ≠ 1`, and `x > 0`, the same lower bound holds with the double-pole
derivative residue at `s = 1`. -/
theorem exp_neg_le_re_pair_add_of_mul_eq_one
    {χ : DirichletCharacter ℂ M} {ψ : DirichletCharacter ℂ N}
    (hχ : χ.IsQuadratic) (hχ1 : χ ≠ 1) (hχψ : χ.mul ψ = 1)
    {β x : ℝ} (hβ₀ : 1 / 2 < β) (hβ₁ : β < 3 / 2) (hβ : β ≠ 1) (hx : 0 < x) :
    Real.exp (-x) ≤
      (riemannZeta β * χ.LFunction β * ψ.LFunction β * (χ.mul ψ).LFunction β).re +
        (deriv (fun s ↦ LFunctionTrivChar₁ 1 s * χ.LFunction s * ψ.LFunction s *
          LFunctionTrivChar₁ (Nat.lcm M N) s *
          (Gamma (s - β) * (x : ℂ) ^ ((β : ℂ) - s))) 1).re +
        37500 * ((M : ℝ) * N) ^ 2 / ((β - 1 / 2) * (3 / 2 - β)) * x ^ (β - 1 / 2) := by
  have hψ : ψ.IsQuadratic := by
    rw [← isQuadratic_changeLevel_iff (Nat.dvd_lcm_right M N)]
    have hsq : (changeLevel (Nat.dvd_lcm_left M N) χ) ^ 2 = 1 :=
      (hχ.changeLevel (Nat.dvd_lcm_left M N)).sq_eq_one
    have heq : changeLevel (Nat.dvd_lcm_right M N) ψ = changeLevel (Nat.dvd_lcm_left M N) χ := by
      calc changeLevel (Nat.dvd_lcm_right M N) ψ
          = changeLevel (Nat.dvd_lcm_left M N) χ ^ 2 *
              changeLevel (Nat.dvd_lcm_right M N) ψ := by rw [hsq, one_mul]
        _ = changeLevel (Nat.dvd_lcm_left M N) χ * (χ.mul ψ) := by
            rw [sq, DirichletCharacter.mul, mul_assoc]
        _ = changeLevel (Nat.dvd_lcm_left M N) χ := by rw [hχψ, mul_one]
    rw [heq]
    exact hχ.changeLevel _
  have hsum := (hasSum_zetaMulPairCoeffs_div_cpow_mul_exp χ ψ (σ := 2 - β) (β := β) (by linarith)
    (by linarith) hx).summable
  have hlo := (Complex.le_def.mp (exp_neg_le_tsum_zetaMulPairCoeffs hχ hψ hsum)).1
  rw [ofReal_re, tsum_zetaMulPairCoeffs_div_cpow_mul_exp_eq_of_mul_eq_one χ ψ hχ1 hχψ
    hβ₀ hβ₁ hβ hx] at hlo
  have herr := (re_le_norm _).trans (norm_mellinInv_Gamma_mul_pair_le χ ψ hβ₀ hβ₁ hx.le)
  simp only [add_re] at hlo
  linarith

end DirichletCharacter
