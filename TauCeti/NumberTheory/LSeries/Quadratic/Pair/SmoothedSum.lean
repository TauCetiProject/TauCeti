/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.DirichletCharacter.Quadratic
public import TauCeti.NumberTheory.LSeries.Quadratic.Pair.Residue
public import TauCeti.NumberTheory.LSeries.SmoothedSum
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import TauCeti.Analysis.Contour.Residue.ChangeOfVariables
import TauCeti.Analysis.MellinInversion.Shift
import TauCeti.Analysis.SpecialFunctions.Gamma.Growth
import TauCeti.Analysis.SpecialFunctions.Gamma.Order
import TauCeti.Analysis.SpecialFunctions.Gamma.Residue
import TauCeti.NumberTheory.DirichletCharacter.LFunction.Bounds
import TauCeti.NumberTheory.DirichletCharacter.LFunction.Meromorphic
import TauCeti.NumberTheory.LSeries.Quadratic.Character
import TauCeti.NumberTheory.LSeries.RiemannZeta
import TauCeti.NumberTheory.LSeries.Twist

/-!
# Smoothed sums and Goldfeld's inequality for the four-factor L-function product

For Dirichlet characters `χ` mod `M` and `ψ` mod `N`, the four-factor product
`F(s) = ζ(s) L(s, χ) L(s, ψ) L(s, χ.mul ψ)` is the Dirichlet series of
`DirichletCharacter.zetaMulPairCoeffs χ ψ` on `Re s > 1`. Twisting by `n ↦ n⁻ᵝ` for `1 / 2 < β < 1`
and smoothing with `e^{-n x}` (`x > 0`) expresses `∑_{n ≥ 1} a_n n⁻ᵝ e^{-n x}` as the Mellin
inverse on `Re w = 2 - β` of `w ↦ Γ(w) F(w + β)`.

Shifting the line of integration left from `Re w = 2 - β` to `Re w = 1 / 2 - β` crosses two poles
in the strip: the simple pole of `Γ(w)` at `w = 0`, with residue `F(β)`, and the pole of `F(w + β)`
at `w = 1 - β`. When `χ`, `ψ`, and `χ.mul ψ` are nonprincipal, the pole at `w = 1 - β` is simple
with residue `x ^ (β - 1) Γ(1 - β) L(1, χ) L(1, ψ) L(1, χ.mul ψ)`, while for all characters and
`β ∈ [3 / 4, 5 / 4]` the shifted integral on `Re w = 1 / 2 - β` is bounded explicitly by
`O((M N)² x ^ (β - 1 / 2))`.

When `χ` and `ψ` are nonprincipal quadratic with `χ.mul ψ ≠ 1` and `Re F(β) ≤ 0` for some
`3 / 4 ≤ β`, positivity of the coefficients `a_n` (`a_1 = 1`) and an optimal choice of `x`
yield Goldfeld's fundamental lower bound
`(1 / 3360000000) (1 - β) (M N) ^ (-8 (1 - β)) ≤ Re (L(1, χ) L(1, ψ) L(1, χ.mul ψ))`.

## Main results

* `DirichletCharacter.hasSum_zetaMulPairCoeffs_mul_rpow_mul_exp`: the contour-shifted smoothed sum
  identity for `1 / 2 < β < 1`, valid for arbitrary characters `χ` and `ψ`.
* `DirichletCharacter.hasSum_zetaMulPairCoeffs_mul_rpow_mul_exp_of_mul_ne_one`: specialization to
  the simple-pole case `χ ≠ 1`, `ψ ≠ 1`, `χ.mul ψ ≠ 1`.
* `DirichletCharacter.norm_mellinInv_Gamma_mul_pair_le`: explicit `(M N)² x ^ (β - 1 / 2)` bound on
  the shifted integral at `Re w = 1 / 2 - β` for `β ∈ [3 / 4, 5 / 4]` and `x ≥ 0`.
* `DirichletCharacter.le_LFunction_one_mul_mul_re_of_pair_re_nonpos`: Goldfeld's lower bound on
  `Re (L(1, χ) L(1, ψ) L(1, χ.mul ψ))` when `Re F(β) ≤ 0`.

## References

* D. Goldfeld, *A simple proof of Siegel's theorem*, Proc. Nat. Acad. Sci. USA 71 (1974), 1055.
* H. Iwaniec and E. Kowalski, *Analytic Number Theory*, §5.9.
-/

public section

open Set MeasureTheory Filter
open Complex hiding exp continuous_exp
open scoped Real Topology ComplexOrder

namespace DirichletCharacter

variable {M N : ℕ} [NeZero M] [NeZero N]

private noncomputable abbrev pairProd (χ : DirichletCharacter ℂ M) (ψ : DirichletCharacter ℂ N)
    (s : ℂ) : ℂ :=
  riemannZeta s * χ.LFunction s * ψ.LFunction s * (χ.mul ψ).LFunction s

private theorem hasSum_mellinInv_two_sub_pairProd (χ : DirichletCharacter ℂ M)
    (ψ : DirichletCharacter ℂ N) {β x : ℝ} (hβ : β < 2) (hx : 0 < x) :
    HasSum (fun n : ℕ ↦ χ.zetaMulPairCoeffs ψ n * ((n : ℝ) ^ (-β) : ℝ) * Real.exp (-n * x))
      (mellinInv (2 - β) (fun w ↦ Gamma w * pairProd χ ψ (w + β)) x) := by
  set f : ℕ → ℂ := fun n ↦ χ.zetaMulPairCoeffs ψ n * (n : ℂ) ^ (-(β : ℂ))
  have hf0 : f 0 = 0 := by simp [f]
  have hsum : LSeriesSummable f ((2 - β : ℝ) : ℂ) := by
    have h2 := (LSeriesHasSum_zetaMulPairCoeffs χ ψ (s := 2) (by norm_num)).LSeriesSummable
    refine h2.congr fun n ↦ ?_
    dsimp only [f]
    rw [TauCeti.LSeries.term_mul_natCast_cpow_neg]
    congr 1; push_cast; ring
  have hm := TauCeti.LSeries.hasSum_mellinInv_Gamma_mul_LSeries hf0 (sub_pos.mpr hβ) hsum hx
  have hterm : (fun n : ℕ ↦ f n * Real.exp (-n * x)) =
      fun n : ℕ ↦ χ.zetaMulPairCoeffs ψ n * ((n : ℝ) ^ (-β) : ℝ) * Real.exp (-n * x) := by
    ext n
    simp only [f, ofReal_cpow n.cast_nonneg, ofReal_neg, ofReal_natCast]
  have heq : mellinInv (2 - β) (fun w ↦ Gamma w * LSeries f w) x =
      mellinInv (2 - β) (fun w ↦ Gamma w * pairProd χ ψ (w + β)) x := by
    simp only [mellinInv]
    congr 2
    ext t
    have hre : 1 < (((2 - β : ℝ) : ℂ) + t * I + β).re := by simp
    dsimp only [f]
    rw [TauCeti.LSeries.LSeries_mul_natCast_cpow_neg,
      (LSeriesHasSum_zetaMulPairCoeffs χ ψ hre).LSeries_eq]
  rwa [hterm, heq] at hm

private theorem norm_riemannZeta_le_three_mul {s : ℂ} (hs : 1 / 2 ≤ s.re)
    (hs1 : 1 / 2 ≤ ‖s - 1‖) : ‖riemannZeta s‖ ≤ 3 * (1 + ‖s‖) := by
  have hz := TauCeti.norm_riemannZeta_le (by linarith : 0 < s.re)
  have hinv : ‖s - 1‖⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ (by linarith) two_pos]; norm_num; exact hs1
  have hdiv : ‖s‖ / s.re ≤ 2 * ‖s‖ := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith [norm_nonneg s]
  linarith [norm_nonneg s]

private theorem norm_LFunction_le_three_mul {L : ℕ} [NeZero L] (ρ : DirichletCharacter ℂ L)
    {s : ℂ} (hs : 1 / 2 ≤ s.re) (hs1 : 1 / 2 ≤ ‖s - 1‖) :
    ‖ρ.LFunction s‖ ≤ 3 * L * (1 + ‖s‖) := by
  have hne : s ≠ 1 := fun h ↦ by simp [h] at hs1; linarith
  have hb := ρ.norm_LFunction_le (by linarith : 0 < s.re) (.inr hne)
  have hinv : ‖s - 1‖⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ (by linarith) two_pos]; norm_num; exact hs1
  have hdiv : ‖s‖ / s.re ≤ 2 * ‖s‖ := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith [norm_nonneg s]
  nlinarith [Nat.cast_nonneg (α := ℝ) L, norm_nonneg s]

private theorem norm_pairProd_le (χ : DirichletCharacter ℂ M) (ψ : DirichletCharacter ℂ N)
    {s : ℂ} (hs : 1 / 2 ≤ s.re) (hs1 : 1 / 2 ≤ ‖s - 1‖) :
    ‖pairProd χ ψ s‖ ≤ 81 * ((M : ℝ) * N) ^ 2 * (1 + ‖s‖) ^ 4 := by
  have hlcm : (Nat.lcm M N : ℝ) ≤ (M : ℝ) * N := by
    exact_mod_cast Nat.le_of_dvd (Nat.mul_pos (NeZero.pos M) (NeZero.pos N)) (Nat.lcm_dvd_mul M N)
  simp only [pairProd, norm_mul]
  calc
    ‖riemannZeta s‖ * ‖χ.LFunction s‖ * ‖ψ.LFunction s‖ * ‖(χ.mul ψ).LFunction s‖
      ≤ (3 * (1 + ‖s‖)) * (3 * M * (1 + ‖s‖)) * (3 * N * (1 + ‖s‖)) *
          (3 * Nat.lcm M N * (1 + ‖s‖)) :=
        mul_le_mul (mul_le_mul (mul_le_mul (norm_riemannZeta_le_three_mul hs hs1)
          (norm_LFunction_le_three_mul χ hs hs1) (norm_nonneg _) (by positivity))
          (norm_LFunction_le_three_mul ψ hs hs1) (norm_nonneg _) (by positivity))
          (norm_LFunction_le_three_mul (χ.mul ψ) hs hs1) (norm_nonneg _) (by positivity)
    _ ≤ (3 * (1 + ‖s‖)) * (3 * M * (1 + ‖s‖)) * (3 * N * (1 + ‖s‖)) *
          (3 * ((M : ℝ) * N) * (1 + ‖s‖)) := by gcongr
    _ = 81 * ((M : ℝ) * N) ^ 2 * (1 + ‖s‖) ^ 4 := by ring

private theorem norm_pairProd_add_mul_I_le (χ : DirichletCharacter ℂ M)
    (ψ : DirichletCharacter ℂ N) {σ : ℝ} (hre : 1 / 2 ≤ σ) (h1 : 1 / 2 ≤ |σ - 1|) (t : ℝ) :
    ‖pairProd χ ψ ((σ : ℂ) + t * I)‖ ≤
      324 * ((M : ℝ) * N) ^ 2 * (1 + |σ|) ^ 4 * (1 + t ^ 2) ^ 2 := by
  set s : ℂ := (σ : ℂ) + t * I
  have hs_re : 1 / 2 ≤ s.re := by simpa [s] using hre
  have hs_1 : 1 / 2 ≤ ‖s - 1‖ :=
    h1.trans (by simpa [s] using abs_re_le_norm (s - 1))
  have hnorm_s : 1 + ‖s‖ ≤ (1 + |σ|) * (1 + |t|) := by
    have hle : ‖s‖ ≤ |σ| + |t| := by simpa [s] using Complex.norm_le_abs_re_add_abs_im s
    nlinarith [abs_nonneg σ, abs_nonneg t]
  have ht4 : (1 + |t|) ^ 4 ≤ 4 * (1 + t ^ 2) ^ 2 := by
    have h2 : (1 + |t|) ^ 2 ≤ 2 * (1 + t ^ 2) := by nlinarith [sq_nonneg (|t| - 1), sq_abs t]
    calc (1 + |t|) ^ 4 = ((1 + |t|) ^ 2) ^ 2 := by ring
      _ ≤ (2 * (1 + t ^ 2)) ^ 2 := pow_le_pow_left₀ (by positivity) h2 2
      _ = 4 * (1 + t ^ 2) ^ 2 := by ring
  calc ‖pairProd χ ψ s‖ ≤ 81 * ((M : ℝ) * N) ^ 2 * (1 + ‖s‖) ^ 4 :=
        norm_pairProd_le χ ψ hs_re hs_1
    _ ≤ 81 * ((M : ℝ) * N) ^ 2 * ((1 + |σ|) * (1 + |t|)) ^ 4 := by gcongr
    _ = 81 * ((M : ℝ) * N) ^ 2 * (1 + |σ|) ^ 4 * (1 + |t|) ^ 4 := by ring
    _ ≤ 81 * ((M : ℝ) * N) ^ 2 * (1 + |σ|) ^ 4 * (4 * (1 + t ^ 2) ^ 2) := by gcongr
    _ = 324 * ((M : ℝ) * N) ^ 2 * (1 + |σ|) ^ 4 * (1 + t ^ 2) ^ 2 := by ring

private theorem analyticAt_pairProd (χ : DirichletCharacter ℂ M) (ψ : DirichletCharacter ℂ N)
    {s : ℂ} (hs1 : s ≠ 1) : AnalyticAt ℂ (pairProd χ ψ) s := by
  have hdiff : DifferentiableOn ℂ (pairProd χ ψ) {z : ℂ | z ≠ 1} := fun z hz ↦
    ((((differentiableAt_riemannZeta hz).mul (χ.differentiableAt_LFunction z (.inl hz))).mul
      (ψ.differentiableAt_LFunction z (.inl hz))).mul
        ((χ.mul ψ).differentiableAt_LFunction z (.inl hz))).differentiableWithinAt
  exact hdiff.analyticAt (isOpen_ne.mem_nhds hs1)

private theorem verticalIntegrable_Gamma_mul_pairProd (χ : DirichletCharacter ℂ M)
    (ψ : DirichletCharacter ℂ N) {σ₀ β : ℝ} (hΓ : ∀ n : ℕ, σ₀ ≠ -n)
    (hre : 1 / 2 ≤ σ₀ + β) (h1 : 1 / 2 ≤ |σ₀ + β - 1|) :
    VerticalIntegrable (fun w ↦ Gamma w * pairProd χ ψ (w + β)) σ₀ := by
  obtain ⟨CΓ, hCΓ⟩ := exists_norm_Gamma_le_mul_inv_one_add_sq_pow hΓ 3
  set C : ℝ := 324 * ((M : ℝ) * N) ^ 2 * (1 + |σ₀ + β|) ^ 4
  have hcont : Continuous fun t : ℝ ↦ Gamma (σ₀ + t * I) * pairProd χ ψ (σ₀ + t * I + β) := by
    refine Continuous.mul (continuous_iff_continuousAt.mpr fun t ↦ ?_)
      (continuous_iff_continuousAt.mpr fun t ↦ ?_)
    · refine (differentiableAt_Gamma _ fun m hm ↦ hΓ m ?_).continuousAt.comp (by fun_prop)
      simpa using congrArg re hm
    · refine (analyticAt_pairProd χ ψ fun h ↦ ?_).continuousAt.comp (by fun_prop)
      have hre_eq : σ₀ + β = 1 := by
        have := congrArg re h; simp at this; linarith
      rw [hre_eq] at h1; norm_num at h1
  refine (integrable_inv_one_add_sq.const_mul (max CΓ 0 * C)).mono'
    hcont.aestronglyMeasurable (Eventually.of_forall fun t ↦ ?_)
  have hs : (σ₀ : ℂ) + t * I + β = ((σ₀ + β : ℝ) : ℂ) + t * I := by push_cast; ring
  have hP : ‖pairProd χ ψ ((σ₀ : ℂ) + t * I + β)‖ ≤ C * (1 + t ^ 2) ^ 2 := by
    rw [hs]; exact norm_pairProd_add_mul_I_le χ ψ hre h1 t
  have hG : ‖Gamma ((σ₀ : ℂ) + t * I)‖ ≤ max CΓ 0 * ((1 + t ^ 2) ^ 3)⁻¹ :=
    (hCΓ t).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
  rw [norm_mul]
  calc ‖Gamma ((σ₀ : ℂ) + t * I)‖ * ‖pairProd χ ψ ((σ₀ : ℂ) + t * I + β)‖
      ≤ max CΓ 0 * ((1 + t ^ 2) ^ 3)⁻¹ * (C * (1 + t ^ 2) ^ 2) :=
        mul_le_mul hG hP (norm_nonneg _) (by positivity)
    _ = max CΓ 0 * C * (1 + t ^ 2)⁻¹ := by
        have : 0 < 1 + t ^ 2 := by positivity
        field_simp

private theorem norm_Gamma_mul_pairProd_le_of_one_le_abs (χ : DirichletCharacter ℂ M)
    (ψ : DirichletCharacter ℂ N) {β σ y : ℝ} (hβ : β ∈ Ioo (1 / 2) 1)
    (hσ : σ ∈ Icc (1 / 2 - β) (2 - β)) (hy : 1 ≤ |y|) :
    ‖Gamma (σ + y * I) * pairProd χ ψ (σ + y * I + β)‖ ≤
      20736 * Real.Gamma 8 * ((M : ℝ) * N) ^ 2 * (|y| ^ 2)⁻¹ := by
  set w : ℂ := (σ : ℂ) + y * I
  have hw_re : w.re = σ := by simp [w]
  have hpos6 : 0 < w.re + 6 := by rw [hw_re]; linarith [hσ.1, hβ.2]
  have hΓle : Real.Gamma (w.re + 6) ≤ Real.Gamma 8 :=
    Real.Gamma_strictMonoOn_Ici.monotoneOn (a := w.re + 6) (b := 8)
      (by rw [mem_Ici, hw_re]; linarith [hσ.1, hβ.2]) (by norm_num)
      (by rw [hw_re]; linarith [hσ.2, hβ.1])
  have hprod : |y| ^ 6 ≤ ∏ k ∈ Finset.range 6, ‖w + k‖ := by
    calc |y| ^ 6 = ∏ _k ∈ Finset.range 6, |y| := by simp
      _ ≤ ∏ k ∈ Finset.range 6, ‖w + k‖ :=
        Finset.prod_le_prod₀ (fun _ _ ↦ abs_nonneg y) fun k _ ↦ by
          simpa [w] using abs_im_le_norm (w + k)
  have hΓw : ‖Gamma w‖ ≤ Real.Gamma 8 / |y| ^ 6 := by
    rw [le_div_iff₀ (by positivity)]
    exact (mul_le_mul_of_nonneg_left hprod (norm_nonneg _)).trans
      ((norm_Gamma_mul_prod_norm_le (s := w) (n := 6) hpos6).trans hΓle)
  set s : ℂ := w + β
  have hs_re : 1 / 2 ≤ s.re := by simp [s, w]; linarith [hσ.1]
  have hs_1 : 1 / 2 ≤ ‖s - 1‖ :=
    (by norm_num : (1 / 2 : ℝ) ≤ 1).trans
      (hy.trans (by simpa [s, w] using abs_im_le_norm (s - 1)))
  have hs_norm : 1 + ‖s‖ ≤ 4 * |y| := by
    have hle : ‖s‖ ≤ |σ + β| + |y| := by simpa [s, w] using Complex.norm_le_abs_re_add_abs_im s
    have habs : |σ + β| ≤ 2 := abs_le.mpr ⟨by linarith [hσ.1], by linarith [hσ.2]⟩
    linarith
  have hPs : ‖pairProd χ ψ s‖ ≤ 20736 * ((M : ℝ) * N) ^ 2 * |y| ^ 4 := by
    calc ‖pairProd χ ψ s‖ ≤ 81 * ((M : ℝ) * N) ^ 2 * (1 + ‖s‖) ^ 4 :=
          norm_pairProd_le χ ψ hs_re hs_1
      _ ≤ 81 * ((M : ℝ) * N) ^ 2 * (4 * |y|) ^ 4 := by gcongr
      _ = 20736 * ((M : ℝ) * N) ^ 2 * |y| ^ 4 := by ring
  rw [norm_mul]
  calc ‖Gamma w‖ * ‖pairProd χ ψ s‖
      ≤ Real.Gamma 8 / |y| ^ 6 * (20736 * ((M : ℝ) * N) ^ 2 * |y| ^ 4) :=
        mul_le_mul hΓw hPs (norm_nonneg _)
          (div_nonneg (Real.Gamma_pos_of_pos (by norm_num)).le (by positivity))
    _ = 20736 * Real.Gamma 8 * ((M : ℝ) * N) ^ 2 * (|y| ^ 2)⁻¹ := by
        have : 0 < |y| := by linarith
        field_simp

private theorem tendsto_integral_norm_Gamma_mul_pairProd (χ : DirichletCharacter ℂ M)
    (ψ : DirichletCharacter ℂ N) {β : ℝ} (hβ : β ∈ Ioo (1 / 2) 1) (sgn : ℝ) (hsgn : |sgn| = 1) :
    Tendsto (fun T : ℝ ↦ ∫ σ : ℝ in (1 / 2 - β)..(2 - β),
        ‖Gamma (σ + ((sgn * T : ℝ) : ℂ) * I) *
          pairProd χ ψ (σ + ((sgn * T : ℝ) : ℂ) * I + β)‖)
      atTop (𝓝 0) := by
  set K : ℝ := 20736 * Real.Gamma 8 * ((M : ℝ) * N) ^ 2
  have hlim : Tendsto (fun T : ℝ ↦ (3 / 2 : ℝ) * (K * (T ^ 2)⁻¹)) atTop (𝓝 0) := by
    simpa using
      (((tendsto_pow_atTop (by norm_num : 2 ≠ 0)).inv_tendsto_atTop).const_mul K).const_mul
        (3 / 2 : ℝ)
  refine squeeze_zero_norm' (a := fun T ↦ (3 / 2 : ℝ) * (K * (T ^ 2)⁻¹)) ?_ hlim
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
  have hTabs : |sgn * T| = T := by rw [abs_mul, hsgn, one_mul, abs_of_nonneg (by linarith)]
  have hlen : |(2 - β) - (1 / 2 - β)| = 3 / 2 := by norm_num
  refine (intervalIntegral.norm_integral_le_of_norm_le_const (C := K * (T ^ 2)⁻¹)
    fun σ hσ ↦ ?_).trans_eq (by rw [hlen, mul_comm])
  have hσ' : σ ∈ Icc (1 / 2 - β) (2 - β) := by
    rw [uIoc_of_le (by linarith)] at hσ; exact ⟨hσ.1.le, hσ.2⟩
  simpa only [K, hTabs, norm_norm] using
    norm_Gamma_mul_pairProd_le_of_one_le_abs χ ψ hβ hσ' (y := sgn * T) (by linarith)

private theorem meromorphicAt_pairProd (χ : DirichletCharacter ℂ M) (ψ : DirichletCharacter ℂ N)
    (z : ℂ) : MeromorphicAt (pairProd χ ψ) z :=
  (((LFunction_modOne_eq ▸ (1 : DirichletCharacter ℂ 1).meromorphic_LFunction z).mul
    (χ.meromorphic_LFunction z)).mul (ψ.meromorphic_LFunction z)).mul
      ((χ.mul ψ).meromorphic_LFunction z)

private theorem sum_residue_pairProd (χ : DirichletCharacter ℂ M) (ψ : DirichletCharacter ℂ N)
    {β x : ℝ} (hβ : β ∈ Ioo (1 / 2) 1) (hx : 0 < x) :
    TauCeti.Contour.residue
        (fun z ↦ (x : ℂ) ^ (-z) * (Gamma z * pairProd χ ψ (z + β))) 0 +
      TauCeti.Contour.residue
        (fun z ↦ (x : ℂ) ^ (-z) * (Gamma z * pairProd χ ψ (z + β))) ((1 - β : ℝ) : ℂ) =
      pairProd χ ψ β +
        TauCeti.Contour.residue
          (fun s ↦ pairProd χ ψ s * ((x : ℂ) ^ (-(s - β)) * Gamma (s - β))) 1 := by
  have hβ1 : (β : ℂ) ≠ 1 := by
    intro h; have := congrArg re h; simp at this; linarith [hβ.2]
  have hg0 : AnalyticAt ℂ (fun z ↦ (x : ℂ) ^ (-z) * pairProd χ ψ (z + β)) 0 :=
    (analyticAt_const.cpow analyticAt_id.neg (ofReal_mem_slitPlane.mpr hx)).mul
      ((analyticAt_pairProd χ ψ hβ1).comp_of_eq (by fun_prop) (zero_add _))
  have hres0 : TauCeti.Contour.residue
      (fun z ↦ (x : ℂ) ^ (-z) * (Gamma z * pairProd χ ψ (z + β))) 0 = pairProd χ ψ β := by
    have hcongr : (fun z ↦ (x : ℂ) ^ (-z) * (Gamma z * pairProd χ ψ (z + β))) =
        fun z ↦ ((x : ℂ) ^ (-z) * pairProd χ ψ (z + β)) * Gamma z := by
      ext z; ring
    simpa [hcongr] using TauCeti.Contour.residue_mul_Gamma_zero hg0
  set F₁ : ℂ → ℂ := fun s ↦ pairProd χ ψ s * ((x : ℂ) ^ (-(s - β)) * Gamma (s - β))
  have hcomp : (fun z ↦ (x : ℂ) ^ (-z) * (Gamma z * pairProd χ ψ (z + β))) =
      fun z ↦ F₁ (z + β) := by
    ext z; simp only [F₁, add_sub_cancel_right]; ring
  rw [hres0, hcomp, TauCeti.Contour.residue_comp_add_const,
    show (((1 - β : ℝ) : ℂ) + (β : ℂ)) = 1 by push_cast; ring]

private theorem differentiableOn_Gamma_mul_pairProd (χ : DirichletCharacter ℂ M)
    (ψ : DirichletCharacter ℂ N) {β : ℝ} (hβ : β < 1) :
    DifferentiableOn ℂ (fun w ↦ Gamma w * pairProd χ ψ (w + β))
      ((Icc (1 / 2 - β) (2 - β) ×ℂ univ) \ ({0, ((1 - β : ℝ) : ℂ)} : Set ℂ)) := fun w hw ↦ by
  have hw_re : 1 / 2 - β ≤ w.re := hw.1.1.1
  have hw0 : w ≠ 0 := fun h ↦ hw.2 (by simp [h])
  have hw1 : w + β ≠ 1 := fun h ↦ hw.2 (by
    have : w = ((1 - β : ℝ) : ℂ) := by push_cast; linear_combination h
    simp [this])
  have hwΓ : ∀ m : ℕ, w ≠ -m := fun m hm ↦ by
    rcases eq_or_ne m 0 with rfl | hm0
    · exact hw0 (by simpa using hm)
    · have hre : w.re = -(m : ℝ) := by simp [hm]
      have hm1 : (1 : ℝ) ≤ m := Nat.one_le_cast.mpr (Nat.pos_of_ne_zero hm0)
      linarith [hw_re, hβ]
  exact ((differentiableAt_Gamma w hwΓ).mul
    (((analyticAt_pairProd χ ψ hw1).comp_of_eq (f := fun z : ℂ ↦ z + β)
      (by fun_prop) rfl).differentiableAt)).differentiableWithinAt

/-- **Smoothed sum identity for the four-factor L-function product.** For any Dirichlet characters
`χ` and `ψ`, real `1 / 2 < β < 1`, and `x > 0`, the series `∑_{n ≥ 1} a_n n⁻ᵝ e^{-n x}` sums to
`F(β)` plus the residue of `F(s) x^{-(s - β)} Γ(s - β)` at `s = 1` plus
`mellinInv (1 / 2 - β) (w ↦ Γ(w) F(w + β)) x`. -/
theorem hasSum_zetaMulPairCoeffs_mul_rpow_mul_exp (χ : DirichletCharacter ℂ M)
    (ψ : DirichletCharacter ℂ N) {β x : ℝ}
    (hβ : β ∈ Ioo (1 / 2) 1) (hx : 0 < x) :
    HasSum (fun n : ℕ ↦ χ.zetaMulPairCoeffs ψ n * ((n : ℝ) ^ (-β) : ℝ) * Real.exp (-n * x))
      (riemannZeta β * χ.LFunction β * ψ.LFunction β * (χ.mul ψ).LFunction β +
        TauCeti.Contour.residue (fun s ↦
          riemannZeta s * χ.LFunction s * ψ.LFunction s * (χ.mul ψ).LFunction s *
            ((x : ℂ) ^ (-(s - β)) * Gamma (s - β))) 1 +
        mellinInv (1 / 2 - β) (fun w ↦ Gamma w *
          (riemannZeta (w + β) * χ.LFunction (w + β) * ψ.LFunction (w + β) *
            (χ.mul ψ).LFunction (w + β))) x) := by
  classical
  set f : ℂ → ℂ := fun w ↦ Gamma w * pairProd χ ψ (w + β)
  set S : Finset ℂ := {0, ((1 - β : ℝ) : ℂ)}
  have hf_diff : DifferentiableOn ℂ f ((Icc (1 / 2 - β) (2 - β) ×ℂ univ) \ (↑S : Set ℂ)) := by
    simpa [f, S] using differentiableOn_Gamma_mul_pairProd χ ψ hβ.2
  have hmero : ∀ s ∈ S, MeromorphicAt f s := fun s _ ↦
    (Meromorphic.Gamma s).mul
      (MeromorphicAt.comp_analyticAt (g := fun w : ℂ ↦ w + β)
        (meromorphicAt_pairProd χ ψ (s + β)) (by fun_prop))
  have ha_int : VerticalIntegrable f (1 / 2 - β) :=
    verticalIntegrable_Gamma_mul_pairProd χ ψ
      (fun n hn ↦ by
        rcases eq_or_ne n 0 with rfl | hn0
        · simp at hn; linarith [hβ.1]
        · have : (1 : ℝ) ≤ n := Nat.one_le_cast.mpr (Nat.pos_of_ne_zero hn0)
          linarith [hβ.2])
      (by linarith) (by norm_num)
  have hb_int : VerticalIntegrable f (2 - β) :=
    verticalIntegrable_Gamma_mul_pairProd χ ψ
      (fun n hn ↦ by linarith [hβ.2, (n.cast_nonneg : (0 : ℝ) ≤ n)])
      (by linarith) (by norm_num)
  have hshift := TauCeti.Contour.mellinInv_sub_mellinInv_eq_sum_residue
    (a := 1 / 2 - β) (b := 2 - β) (f := f) (S := S) (by linarith) hx hf_diff hmero
    (fun s hs ↦ by
      simp only [S, Finset.mem_insert, Finset.mem_singleton] at hs
      rcases hs with rfl | rfl
      · simp only [zero_re, mem_Ioo]; constructor <;> linarith [hβ.1, hβ.2]
      · simp only [ofReal_re, mem_Ioo]; constructor <;> linarith [hβ.1, hβ.2])
    ha_int hb_int
    (by simpa [f, one_mul] using tendsto_integral_norm_Gamma_mul_pairProd χ ψ hβ 1 (by norm_num))
    (by simpa [f, sub_eq_add_neg, neg_mul] using
      tendsto_integral_norm_Gamma_mul_pairProd χ ψ hβ (-1) (by norm_num))
  have hneS : (0 : ℂ) ≠ ((1 - β : ℝ) : ℂ) := by
    intro h; have := congrArg re h; simp at this; linarith [hβ.2]
  rw [Finset.sum_pair hneS, sum_residue_pairProd χ ψ hβ hx, sub_eq_iff_eq_add] at hshift
  have hmain := hasSum_mellinInv_two_sub_pairProd χ ψ (β := β) (by linarith [hβ.2]) hx
  rw [hshift] at hmain
  simpa only [f, pairProd, add_assoc] using hmain

/-- **Simple-pole smoothed sum of the four-factor L-function product.** When `χ`, `ψ`, and
`χ.mul ψ` are nonprincipal, the pole at `s = 1` is simple and its residue evaluates to
`x ^ (β - 1) Γ(1 - β) L(1, χ) L(1, ψ) L(1, χ.mul ψ)`. -/
theorem hasSum_zetaMulPairCoeffs_mul_rpow_mul_exp_of_mul_ne_one {χ : DirichletCharacter ℂ M}
    {ψ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) (hψ : ψ ≠ 1) (hχψ : χ.mul ψ ≠ 1) {β x : ℝ}
    (hβ : β ∈ Ioo (1 / 2) 1) (hx : 0 < x) :
    HasSum (fun n : ℕ ↦ χ.zetaMulPairCoeffs ψ n * ((n : ℝ) ^ (-β) : ℝ) * Real.exp (-n * x))
      (riemannZeta β * χ.LFunction β * ψ.LFunction β * (χ.mul ψ).LFunction β +
        ((x ^ (β - 1) * Real.Gamma (1 - β) : ℝ) : ℂ) *
          (χ.LFunction 1 * ψ.LFunction 1 * (χ.mul ψ).LFunction 1) +
        mellinInv (1 / 2 - β) (fun w ↦ Gamma w *
          (riemannZeta (w + β) * χ.LFunction (w + β) * ψ.LFunction (w + β) *
            (χ.mul ψ).LFunction (w + β))) x) := by
  have hw_an : AnalyticAt ℂ (fun s : ℂ ↦ (x : ℂ) ^ (-(s - β)) * Gamma (s - β)) 1 := by
    refine ((analyticAt_const (v := (x : ℂ))).cpow
      (analyticAt_id.sub (analyticAt_const (v := (β : ℂ)))).neg
      (ofReal_mem_slitPlane.mpr hx)).mul ?_
    refine (analyticAt_Gamma (s := 1 - (β : ℂ)) fun m hm ↦ ?_).comp_of_eq
      (f := fun s : ℂ ↦ s - β) (by fun_prop) rfl
    have := congrArg re hm
    simp at this
    linarith [hβ.2, (m.cast_nonneg : (0 : ℝ) ≤ m)]
  have hres := residue_pair_mul_of_mul_ne_one χ ψ hχ hψ hχψ hw_an
  have h1 : (x : ℂ) ^ (-((1 : ℂ) - (β : ℂ))) = ((x ^ (β - 1) : ℝ) : ℂ) := by
    rw [ofReal_cpow hx.le]
    congr 1; push_cast; ring
  have h2 : Gamma ((1 : ℂ) - (β : ℂ)) = (Real.Gamma (1 - β) : ℂ) := by
    rw [← Gamma_ofReal]
    congr 1; push_cast; ring
  have hval : (x : ℂ) ^ (-((1 : ℂ) - β)) * Gamma ((1 : ℂ) - β) =
      ((x ^ (β - 1) * Real.Gamma (1 - β) : ℝ) : ℂ) := by
    rw [h1, h2, ofReal_mul]
  rw [hval, mul_comm _ (((x ^ (β - 1) * Real.Gamma (1 - β) : ℝ) : ℂ))] at hres
  simpa only [hres] using hasSum_zetaMulPairCoeffs_mul_rpow_mul_exp χ ψ hβ hx

private theorem norm_Gamma_half_sub_le {β : ℝ} (hβ : β ∈ Icc (3 / 4) (5 / 4)) (t : ℝ) :
    ‖Gamma (((1 / 2 - β : ℝ) : ℂ) + t * I)‖ ≤ 80640 * ((1 + t ^ 2) ^ 3)⁻¹ := by
  set w : ℂ := ((1 / 2 - β : ℝ) : ℂ) + t * I
  have hw_re : w.re = 1 / 2 - β := by simp [w]
  have hΓ8 : Real.Gamma (w.re + 8) ≤ 5040 := by
    have hmono := Real.Gamma_strictMonoOn_Ici.monotoneOn (a := w.re + 8) (b := 8)
      (by rw [mem_Ici, hw_re]; linarith [hβ.2]) (by norm_num) (by rw [hw_re]; linarith [hβ.1])
    have hfac : Real.Gamma 8 = 5040 := by
      rw [show (8 : ℝ) = (7 : ℕ) + 1 by norm_num, Real.Gamma_nat_eq_factorial]
      norm_num [Nat.factorial]
    linarith
  have hP6 : (1 + t ^ 2) ^ 3 ≤ ∏ j ∈ Finset.range 6, ‖w + ((j + 1 + 1 : ℕ) : ℂ)‖ := by
    have hsq : ((1 + t ^ 2) ^ 3) ^ 2 ≤
        (∏ j ∈ Finset.range 6, ‖w + ((j + 1 + 1 : ℕ) : ℂ)‖) ^ 2 := by
      rw [← Finset.prod_pow]
      calc ((1 + t ^ 2) ^ 3) ^ 2 = ∏ _j ∈ Finset.range 6, (1 + t ^ 2) := by simp; ring
        _ ≤ ∏ j ∈ Finset.range 6, ‖w + ((j + 1 + 1 : ℕ) : ℂ)‖ ^ 2 :=
          Finset.prod_le_prod₀ (fun _ _ ↦ by positivity) fun j _ ↦ by
            rw [← normSq_eq_norm_sq, normSq_apply]
            have hre_j : 1 ≤ (w + ((j + 1 + 1 : ℕ) : ℂ)).re := by
              simp [w]; linarith [hβ.2, (j.cast_nonneg : (0 : ℝ) ≤ j)]
            have him_j : (w + ((j + 1 + 1 : ℕ) : ℂ)).im = t := by simp [w]
            rw [him_j]; nlinarith
    exact le_of_pow_le_pow_left₀ two_ne_zero (Finset.prod_nonneg fun _ _ ↦ norm_nonneg _) hsq
  have hw0 : 1 / 4 ≤ ‖w‖ :=
    (by rw [abs_of_neg (by linarith [hβ.1])]; linarith [hβ.1] : 1 / 4 ≤ |1 / 2 - β|).trans
      (hw_re ▸ abs_re_le_norm w)
  have hw1 : 1 / 4 ≤ ‖w + 1‖ :=
    (by rw [abs_of_pos (by linarith [hβ.2])]; linarith [hβ.2] : 1 / 4 ≤ |1 / 2 - β + 1|).trans
      (by simpa [w] using abs_re_le_norm (w + 1))
  have hprod8 : (1 / 16 : ℝ) * (1 + t ^ 2) ^ 3 ≤ ∏ k ∈ Finset.range 8, ‖w + k‖ := by
    rw [Finset.prod_range_succ', Finset.prod_range_succ']
    simp only [Nat.cast_zero, add_zero, zero_add, Nat.cast_one]
    calc (1 / 16 : ℝ) * (1 + t ^ 2) ^ 3 = (1 + t ^ 2) ^ 3 * (1 / 4) * (1 / 4) := by ring
      _ ≤ (∏ k ∈ Finset.range 6, ‖w + ((k + 1 + 1 : ℕ) : ℂ)‖) * ‖w + 1‖ * ‖w‖ :=
        mul_le_mul (mul_le_mul hP6 hw1 (by positivity) (Finset.prod_nonneg fun _ _ ↦ norm_nonneg _))
          hw0 (by positivity) (by positivity)
  have hb := (norm_Gamma_mul_prod_norm_le (s := w) (n := 8)
    (by rw [hw_re]; linarith [hβ.2])).trans hΓ8
  rw [show 80640 * ((1 + t ^ 2) ^ 3)⁻¹ = 5040 / ((1 / 16 : ℝ) * (1 + t ^ 2) ^ 3) by
    field_simp; ring, le_div_iff₀ (by positivity)]
  exact (mul_le_mul_of_nonneg_left hprod8 (norm_nonneg _)).trans hb

private theorem norm_pairProd_half_le (χ : DirichletCharacter ℂ M) (ψ : DirichletCharacter ℂ N)
    (t : ℝ) :
    ‖pairProd χ ψ ((1 / 2 : ℂ) + t * I)‖ ≤ 5184 * ((M : ℝ) * N) ^ 2 * (1 + t ^ 2) ^ 2 := by
  have h := norm_pairProd_add_mul_I_le χ ψ (σ := 1 / 2) le_rfl (by norm_num) t
  have hcast : ((1 / 2 : ℝ) : ℂ) + t * I = (1 / 2 : ℂ) + t * I := by push_cast; rfl
  rw [hcast] at h
  refine h.trans ?_
  have hnum : (324 : ℝ) * (1 + |(1 / 2 : ℝ)|) ^ 4 ≤ 5184 := by norm_num
  have hfac : 0 ≤ ((M : ℝ) * N) ^ 2 * (1 + t ^ 2) ^ 2 := by positivity
  calc 324 * ((M : ℝ) * N) ^ 2 * (1 + |(1 / 2 : ℝ)|) ^ 4 * (1 + t ^ 2) ^ 2
      = (324 * (1 + |(1 / 2 : ℝ)|) ^ 4) * (((M : ℝ) * N) ^ 2 * (1 + t ^ 2) ^ 2) := by ring
    _ ≤ 5184 * (((M : ℝ) * N) ^ 2 * (1 + t ^ 2) ^ 2) := mul_le_mul_of_nonneg_right hnum hfac
    _ = 5184 * ((M : ℝ) * N) ^ 2 * (1 + t ^ 2) ^ 2 := by ring

private theorem norm_Gamma_mul_pairProd_half_sub_le (χ : DirichletCharacter ℂ M)
    (ψ : DirichletCharacter ℂ N) {β : ℝ} (hβ : β ∈ Icc (3 / 4) (5 / 4)) (t : ℝ) :
    ‖Gamma ((1 / 2 - β : ℝ) + t * I) * pairProd χ ψ (((1 / 2 - β : ℝ) + t * I) + β)‖ ≤
      418037760 * ((M : ℝ) * N) ^ 2 * (1 + t ^ 2)⁻¹ := by
  have hs_eq : (((1 / 2 - β : ℝ) : ℂ) + t * I) + β = (1 / 2 : ℂ) + t * I := by push_cast; ring
  rw [norm_mul, hs_eq]
  calc ‖Gamma (((1 / 2 - β : ℝ) : ℂ) + t * I)‖ * ‖pairProd χ ψ ((1 / 2 : ℂ) + t * I)‖
      ≤ 80640 * ((1 + t ^ 2) ^ 3)⁻¹ * (5184 * ((M : ℝ) * N) ^ 2 * (1 + t ^ 2) ^ 2) :=
        mul_le_mul (norm_Gamma_half_sub_le hβ t) (norm_pairProd_half_le χ ψ t)
          (norm_nonneg _) (by positivity)
    _ = 418037760 * ((M : ℝ) * N) ^ 2 * (1 + t ^ 2)⁻¹ := by
        have : 0 < 1 + t ^ 2 := by positivity
        field_simp; ring

/-- **Explicit level bound for the shifted Mellin integral on `Re w = 1 / 2 - β`.** For any
Dirichlet characters `χ` mod `M` and `ψ` mod `N`, `β ∈ [3 / 4, 5 / 4]`, and `x ≥ 0`, the shifted
contour integral on `Re w = 1 / 2 - β` has norm at most `209018880 (M N)² x ^ (β - 1 / 2)`. -/
theorem norm_mellinInv_Gamma_mul_pair_le (χ : DirichletCharacter ℂ M)
    (ψ : DirichletCharacter ℂ N) {β x : ℝ} (hβ : β ∈ Icc (3 / 4) (5 / 4)) (hx : 0 ≤ x) :
    ‖mellinInv (1 / 2 - β) (fun w ↦ Gamma w *
      (riemannZeta (w + β) * χ.LFunction (w + β) * ψ.LFunction (w + β) *
        (χ.mul ψ).LFunction (w + β))) x‖ ≤
      209018880 * ((M : ℝ) * N) ^ 2 * x ^ (β - 1 / 2) := by
  rcases eq_or_lt_of_le hx with rfl | hx
  · have hpow (t : ℝ) : (0 : ℂ) ^ (-(((1 / 2 - β : ℝ) : ℂ) + t * I)) = 0 :=
      zero_cpow fun h ↦ by
        have := congrArg re h; simp at this; linarith [hβ.1]
    simp only [mellinInv, ofReal_zero, hpow, zero_smul, integral_zero, smul_zero, norm_zero,
      Real.zero_rpow (by linarith [hβ.1] : β - 1 / 2 ≠ 0), mul_zero, le_rfl]
  set C : ℝ := 418037760 * ((M : ℝ) * N) ^ 2 * x ^ (β - 1 / 2)
  have hint :
      ‖∫ t : ℝ, (x : ℂ) ^ (-(((1 / 2 - β : ℝ) : ℂ) + t * I)) •
        (Gamma (((1 / 2 - β : ℝ) : ℂ) + t * I) *
          pairProd χ ψ ((((1 / 2 - β : ℝ) : ℂ) + t * I) + β))‖ ≤ C * π := by
    calc
      _ ≤ ∫ t : ℝ, C * (1 + t ^ 2)⁻¹ := by
        refine norm_integral_le_of_norm_le (integrable_inv_one_add_sq.const_mul C)
          (Eventually.of_forall fun t ↦ ?_)
        rw [norm_smul, norm_cpow_eq_rpow_re_of_pos hx,
          show (-(((1 / 2 - β : ℝ) : ℂ) + t * I)).re = β - 1 / 2 by simp]
        calc x ^ (β - 1 / 2) *
              ‖Gamma (((1 / 2 - β : ℝ) : ℂ) + t * I) *
                pairProd χ ψ ((((1 / 2 - β : ℝ) : ℂ) + t * I) + β)‖
            ≤ x ^ (β - 1 / 2) * (418037760 * ((M : ℝ) * N) ^ 2 * (1 + t ^ 2)⁻¹) :=
              mul_le_mul_of_nonneg_left
                (norm_Gamma_mul_pairProd_half_sub_le χ ψ hβ t) (by positivity)
          _ = C * (1 + t ^ 2)⁻¹ := by simp only [C]; ring
      _ = C * π := by rw [integral_const_mul, integral_univ_inv_one_add_sq]
  rw [mellinInv, norm_smul, Real.norm_of_nonneg (by positivity)]
  calc 1 / (2 * π) *
        ‖∫ t : ℝ, (x : ℂ) ^ (-(((1 / 2 - β : ℝ) : ℂ) + t * I)) •
          (Gamma (((1 / 2 - β : ℝ) : ℂ) + t * I) *
            pairProd χ ψ ((((1 / 2 - β : ℝ) : ℂ) + t * I) + β))‖
      ≤ 1 / (2 * π) * (C * π) :=
        mul_le_mul_of_nonneg_left hint (by positivity)
    _ = 209018880 * ((M : ℝ) * N) ^ 2 * x ^ (β - 1 / 2) := by
        simp only [C]; field_simp [Real.pi_ne_zero]; ring

omit [NeZero M] [NeZero N] in
private theorem exp_neg_le_tsum_zetaMulPairCoeffs_re {χ : DirichletCharacter ℂ M}
    {ψ : DirichletCharacter ℂ N} (hχ : χ.IsQuadratic) (hψ : ψ.IsQuadratic)
    {β x : ℝ} (hs : Summable fun n : ℕ ↦
      (χ.zetaMulPairCoeffs ψ n * ((n : ℝ) ^ (-β) : ℝ) * Real.exp (-n * x)).re) :
    Real.exp (-x) ≤
      ∑' n : ℕ, (χ.zetaMulPairCoeffs ψ n * ((n : ℝ) ^ (-β) : ℝ) * Real.exp (-n * x)).re := by
  have hterm (n : ℕ) :
      0 ≤ (χ.zetaMulPairCoeffs ψ n * ((n : ℝ) ^ (-β) : ℝ) * Real.exp (-n * x)).re := by
    have hc := Complex.le_def.mp (zetaMulPairCoeffs_nonneg hχ hψ n)
    have hre : (χ.zetaMulPairCoeffs ψ n * ((n : ℝ) ^ (-β) : ℝ) * Real.exp (-n * x)).re =
        (χ.zetaMulPairCoeffs ψ n).re * ((n : ℝ) ^ (-β) * Real.exp (-n * x)) := by
      rw [mul_assoc, ← ofReal_mul, mul_comm, re_ofReal_mul, mul_comm]
    rw [hre]
    exact mul_nonneg hc.1 (mul_nonneg (Real.rpow_nonneg n.cast_nonneg _) (Real.exp_pos _).le)
  have hle := hs.le_tsum 1 fun n _ ↦ hterm n
  have h1 : (χ.zetaMulPairCoeffs ψ 1 * (((1 : ℕ) : ℝ) ^ (-β) : ℝ) *
      Real.exp (-(1 : ℕ) * x)).re = Real.exp (-x) := by
    rw [zetaMulPairCoeffs_one]
    simp only [Nat.cast_one, Real.one_rpow, ofReal_one, mul_one, one_mul, neg_mul, ofReal_re]
  rwa [h1] at hle

private theorem quarter_mul_sub_mul_rpow_le_LFunction_one_re {χ : DirichletCharacter ℂ M}
    {ψ : DirichletCharacter ℂ N} (hχ : χ.IsQuadratic) (hψ : ψ.IsQuadratic) (hχ₁ : χ ≠ 1)
    (hψ₁ : ψ ≠ 1) (hχψ : χ.mul ψ ≠ 1) {β x : ℝ} (hβ : β ∈ Ioo (1 / 2) 1)
    (hx : x ∈ Ioc 0 (1 / 4))
    (hsign : (riemannZeta β * χ.LFunction β * ψ.LFunction β * (χ.mul ψ).LFunction β).re ≤ 0)
    (herr : ‖mellinInv (1 / 2 - β) (fun w ↦ Gamma w * pairProd χ ψ (w + β)) x‖ ≤ 1 / 4) :
    (1 / 4 : ℝ) * (1 - β) * x ^ (1 - β) ≤
      (χ.LFunction 1 * ψ.LFunction 1 * (χ.mul ψ).LFunction 1).re := by
  have hsum_re := Complex.reCLM.hasSum
    (hasSum_zetaMulPairCoeffs_mul_rpow_mul_exp_of_mul_ne_one hχ₁ hψ₁ hχψ hβ hx.1)
  have hexp_le : 1 / 2 ≤ ∑' n : ℕ,
      (χ.zetaMulPairCoeffs ψ n * ((n : ℝ) ^ (-β) : ℝ) * Real.exp (-n * x)).re :=
    (by linarith [Real.add_one_le_exp (-x), hx.2] : 1 / 2 ≤ Real.exp (-x)).trans
      (exp_neg_le_tsum_zetaMulPairCoeffs_re hχ hψ (by simpa using hsum_re.summable))
  set R : ℝ := (χ.LFunction 1 * ψ.LFunction 1 * (χ.mul ψ).LFunction 1).re
  have hR_pos : 0 < R := (Complex.pos_iff.mp (mul_pos (mul_pos (LFunction_apply_one_pos hχ hχ₁)
    (LFunction_apply_one_pos hψ hψ₁)) (LFunction_apply_one_pos (isQuadratic_mul hχ hψ) hχψ))).1
  have hmain_ub : 1 / 4 ≤ x ^ (β - 1) * (1 - β)⁻¹ * R := by
    have heq := hsum_re.tsum_eq
    simp only [Complex.reCLM_apply, add_re, re_ofReal_mul] at heq
    have hm_re : (mellinInv (1 / 2 - β) (fun w ↦ Gamma w * pairProd χ ψ (w + β)) x).re ≤ 1 / 4 :=
      (le_abs_self _).trans ((abs_re_le_norm _).trans herr)
    have hmain_ge : 1 / 4 ≤ x ^ (β - 1) * Real.Gamma (1 - β) * R := by
      dsimp only [pairProd] at hm_re; linarith
    exact hmain_ge.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
      (Real.Gamma_le_inv (sub_pos.mpr hβ.2) (by linarith [hβ.1]))
      (Real.rpow_pos_of_pos hx.1 _).le) hR_pos.le)
  have h1β : 0 < 1 - β := sub_pos.mpr hβ.2
  have hmul := mul_le_mul_of_nonneg_right hmain_ub
    (mul_nonneg h1β.le (Real.rpow_nonneg hx.1.le (1 - β)))
  calc (1 / 4 : ℝ) * (1 - β) * x ^ (1 - β)
      = 1 / 4 * ((1 - β) * x ^ (1 - β)) := by ring
    _ ≤ x ^ (β - 1) * (1 - β)⁻¹ * R * ((1 - β) * x ^ (1 - β)) := hmul
    _ = R * ((1 - β)⁻¹ * (1 - β)) * (x ^ (β - 1) * x ^ (1 - β)) := by ring
    _ = R := by rw [inv_mul_cancel₀ h1β.ne', ← Real.rpow_add hx.1]; norm_num

/-- **Goldfeld's fundamental inequality.** Let `χ` mod `M` and `ψ` mod `N` be nonprincipal
quadratic Dirichlet characters whose product `χ.mul ψ` is also nonprincipal. If `3 / 4 ≤ β` and
`Re (ζ(β) L(β, χ) L(β, ψ) L(β, χ.mul ψ)) ≤ 0`, then
`(1 / 3360000000) (1 - β) (M N) ^ (-8 (1 - β)) ≤ Re (L(1, χ) L(1, ψ) L(1, χ.mul ψ))`. -/
theorem le_LFunction_one_mul_mul_re_of_pair_re_nonpos {χ : DirichletCharacter ℂ M}
    {ψ : DirichletCharacter ℂ N} (hχ : χ.IsQuadratic) (hψ : ψ.IsQuadratic) (hχ₁ : χ ≠ 1)
    (hψ₁ : ψ ≠ 1) (hχψ : χ.mul ψ ≠ 1) {β : ℝ} (hβ : 3 / 4 ≤ β)
    (hsign : (riemannZeta β * χ.LFunction β * ψ.LFunction β * (χ.mul ψ).LFunction β).re ≤ 0) :
    (1 / 3360000000 : ℝ) * (1 - β) * ((M : ℝ) * N) ^ (-8 * (1 - β)) ≤
      (χ.LFunction 1 * ψ.LFunction 1 * (χ.mul ψ).LFunction 1).re := by
  set P : ℝ := (M : ℝ) * N
  have hP1 : 1 ≤ P := by
    have hM : (1 : ℝ) ≤ M := Nat.one_le_cast.mpr NeZero.one_le
    have hN : (1 : ℝ) ≤ N := Nat.one_le_cast.mpr NeZero.one_le
    nlinarith
  rcases le_or_gt 1 β with h1β | hβ1
  · have hR_pos := (Complex.pos_iff.mp (mul_pos (mul_pos (LFunction_apply_one_pos hχ hχ₁)
      (LFunction_apply_one_pos hψ hψ₁)) (LFunction_apply_one_pos (isQuadratic_mul hχ hψ) hχψ))).1
    exact (mul_nonpos_of_nonpos_of_nonneg (by linarith) (Real.rpow_nonneg (by positivity) _)).trans
      hR_pos.le
  set A : ℝ := 840000000 * P ^ 2
  have hA1 : 840000000 ≤ A := by nlinarith
  set x : ℝ := A ^ (-4 : ℝ) with hx_def
  have hx : 0 < x := Real.rpow_pos_of_pos (by linarith) _
  have hx_half : x ≤ 1 / 4 :=
    (Real.rpow_le_rpow_of_nonpos (by norm_num) hA1 (by norm_num)).trans (by norm_num)
  have herr : ‖mellinInv (1 / 2 - β) (fun w ↦ Gamma w * pairProd χ ψ (w + β)) x‖ ≤ 1 / 4 := by
    have hb := norm_mellinInv_Gamma_mul_pair_le χ ψ ⟨hβ, by linarith⟩ hx.le
    have hxpow : x ^ (β - 1 / 2) ≤ A⁻¹ :=
      (Real.rpow_le_rpow_of_exponent_ge (z := 1 / 4) hx (by linarith)
        (by linarith)).trans_eq (by
          rw [hx_def, ← Real.rpow_mul (by linarith)]
          norm_num [Real.rpow_neg_one])
    calc ‖mellinInv (1 / 2 - β) (fun w ↦ Gamma w * pairProd χ ψ (w + β)) x‖
        ≤ 209018880 * P ^ 2 * A⁻¹ := hb.trans (by gcongr)
      _ = 209018880 / 840000000 := by simp only [A]; field_simp
      _ ≤ 1 / 4 := by norm_num
  have hx1β : (1 / 840000000 : ℝ) * P ^ (-8 * (1 - β)) ≤ x ^ (1 - β) := by
    have hA_pow : x ^ (1 - β) = (840000000 : ℝ) ^ (-4 * (1 - β)) * P ^ (-8 * (1 - β)) := by
      simp only [x, A]
      rw [← Real.rpow_mul (by positivity), Real.mul_rpow (by norm_num) (by positivity),
        ← Real.rpow_two, ← Real.rpow_mul (by positivity)]
      ring_nf
    have h84 : (1 / 840000000 : ℝ) ≤ (840000000 : ℝ) ^ (-4 * (1 - β)) :=
      (by norm_num [Real.rpow_neg_one] : (1 / 840000000 : ℝ) = (840000000 : ℝ) ^ (-1 : ℝ)).trans_le
        (Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith))
    exact hA_pow ▸ mul_le_mul_of_nonneg_right h84 (by positivity)
  calc (1 / 3360000000 : ℝ) * (1 - β) * P ^ (-8 * (1 - β))
      = (1 / 4 : ℝ) * (1 - β) * ((1 / 840000000 : ℝ) * P ^ (-8 * (1 - β))) := by ring
    _ ≤ (1 / 4 : ℝ) * (1 - β) * x ^ (1 - β) := mul_le_mul_of_nonneg_left hx1β (by linarith)
    _ ≤ (χ.LFunction 1 * ψ.LFunction 1 * (χ.mul ψ).LFunction 1).re :=
      quarter_mul_sub_mul_rpow_le_LFunction_one_re hχ hψ hχ₁ hψ₁ hχψ
        ⟨by linarith, hβ1⟩ ⟨hx, hx_half⟩ hsign herr

end DirichletCharacter
