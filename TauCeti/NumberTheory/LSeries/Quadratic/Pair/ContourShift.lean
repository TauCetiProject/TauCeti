/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LSeries.Quadratic.Pair.Residue
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Topology.Algebra.InfiniteSum.Order
import TauCeti.Analysis.Contour.Residue.Cycle
import TauCeti.Analysis.Contour.Winding.Number.Rectangle
import TauCeti.Analysis.SpecialFunctions.Gamma.Order
import TauCeti.NumberTheory.DirichletCharacter.LFunction.Bounds
import TauCeti.NumberTheory.DirichletCharacter.Quadratic
import TauCeti.NumberTheory.LSeries.Quadratic.Character
import TauCeti.NumberTheory.LSeries.RiemannZeta
import TauCeti.NumberTheory.LSeries.SmoothedSum
import TauCeti.NumberTheory.LSeries.Twist

/-!
# Smoothed Mellin contour shift and residue lower bound for two-character products

Let `χ` and `ψ` be nonprincipal Dirichlet characters of positive levels `M` and `N`, and write
`F(s) = ζ(s) L(s, χ) L(s, ψ) L(s, χ.mul ψ)` with `χ.mul ψ` at `Nat.lcm M N`. Twisting
`DirichletCharacter.zetaMulPairCoeffs` by `n ^ (-β)` (`β < 2`) and applying exponential Mellin
smoothing on `Re(s - β) = 2 - β` expresses `∑ₙ aₙ n^{-β} e^{-n x}` (`x > 0`) as the vertical
integral of `F(s) x^{-(s - β)} Γ(s - β)` along `Re s = 2`. When `χ` and `ψ` are quadratic, the
coefficients `aₙ` are nonnegative real numbers with `a₁ = 1`, so `e^{-x}` bounds the real part of
that vertical integral from below.

For `1 / 2 < β < 1`, shifting the contour from `Re s = 2` to `Re s = 1 / 2` crosses only the pole
of `F` at `s = 1` (simple when `χ.mul ψ ≠ 1`, double when `χ.mul ψ = 1`) and the simple pole of
`Γ(s - β)` at `s = β` with residue `F(β)`. Rapid vertical decay of `Γ` (`n = 6` in
`Complex.norm_Gamma_mul_prod_norm_le`) kills the horizontal segments against the fourth-power
polynomial growth of `F` from `TauCeti.norm_riemannZeta_le_div_add_div` and
`DirichletCharacter.norm_LFunction_le_level_mul_norm_div_re`.

On `Re s = 1 / 2` with `3 / 4 ≤ β < 1` and `χ.mul ψ ≠ 1`, `s - β` stays uniformly away from the
poles `0` and `-1` of `Γ`, yielding a single absolute constant `C` with shifted-integral norm at
most `C (M N)² x^{β - 1/2}`. Specializing `x` to a fixed negative power of `M N` when `F(β) ≤ 0`
gives Goldfeld's uniform lower bound `c (1 - β) (M N)^{-8 (1 - β)} ≤ L(1, χ) L(1, ψ) L(1, χ.mul ψ)`.

## Main results

* `DirichletCharacter.hasSum_zetaMulPairCoeffs_cpow_neg_mul_exp`: Mellin-smoothed sum of
  `aₙ n^{-β} e^{-n x}` as the `Re s = 2` integral.
* `DirichletCharacter.exp_neg_le_re_integral_pair_mul_Gamma`: `e^{-x}` bounds the real part of the
  `Re s = 2` integral from below for quadratic `χ, ψ`.
* `DirichletCharacter.integral_pair_mul_Gamma_two_eq`,
  `DirichletCharacter.integral_pair_mul_Gamma_two_eq_of_mul_ne_one`,
  `DirichletCharacter.integral_pair_mul_Gamma_two_eq_of_mul_eq_one`: the contour shift from
  `Re s = 2` to `Re s = 1 / 2`, in general and in both pole regimes.
* `DirichletCharacter.exists_norm_integral_pair_mul_Gamma_half_le`: uniform `C (M N)² x^{β - 1/2}`
  error bound on `Re s = 1 / 2` for `β ∈ [3 / 4, 1)` and `χ.mul ψ ≠ 1`.
* `DirichletCharacter.exists_pos_mul_rpow_le_LFunction_one_re_mul`: Goldfeld's residue lower bound
  under `F(β) ≤ 0`.

## References

* D. Goldfeld, *A simple proof of Siegel's theorem*, Proc. Nat. Acad. Sci. USA 71 (1974), 1055.
* H. Davenport, *Multiplicative Number Theory*, Chapter 21.
-/

public section

open Filter Set MeasureTheory
open Complex hiding exp continuous_exp
open scoped Topology ComplexOrder Interval

namespace DirichletCharacter

section SmoothedSum

variable {M N : ℕ} [NeZero M] [NeZero N]
variable (χ : DirichletCharacter ℂ M) (ψ : DirichletCharacter ℂ N)

/-- **Mellin-smoothed sum of the shifted four-factor coefficients.** For `β < 2` and `x > 0`, the
exponentially smoothed series `∑ₙ aₙ n^{-β} e^{-n x}` equals `(2π)⁻¹` times the vertical integral
of `ζ(s) L(s, χ) L(s, ψ) L(s, χ.mul ψ) x^{-(s - β)} Γ(s - β)` along `Re s = 2`. -/
theorem hasSum_zetaMulPairCoeffs_cpow_neg_mul_exp {β : ℝ} (hβ : β < 2) {x : ℝ} (hx : 0 < x) :
    HasSum (fun n : ℕ ↦ χ.zetaMulPairCoeffs ψ n * (n : ℂ) ^ (-(β : ℂ)) * Real.exp (-n * x))
      (((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ t : ℝ,
        riemannZeta (2 + t * I) * χ.LFunction (2 + t * I) * ψ.LFunction (2 + t * I) *
          (χ.mul ψ).LFunction (2 + t * I) *
          ((x : ℂ) ^ (-((2 + t * I) - β)) * Gamma ((2 + t * I) - β))) := by
  set f : ℕ → ℂ := fun n ↦ χ.zetaMulPairCoeffs ψ n * (n : ℂ) ^ (-(β : ℂ))
  have hf0 : f 0 = 0 := by simp [f]
  have hσ : 0 < 2 - β := by linarith
  have hsumm : LSeriesSummable f (2 - β : ℝ) := by
    rw [ofReal_sub, ofReal_ofNat,
      TauCeti.LSeries.LSeriesSummable_mul_natCast_cpow_neg_iff, sub_add_cancel]
    exact (χ.LSeriesHasSum_zetaMulPairCoeffs ψ (by norm_num : 1 < (2 : ℂ).re)).LSeriesSummable
  have h := TauCeti.LSeries.hasSum_mellinInv_Gamma_mul_LSeries hf0 hσ hsumm hx
  rw [mellinInv, real_smul] at h
  have hint_eq : (∫ y : ℝ, (x : ℂ) ^ (-(((2 - β : ℝ) : ℂ) + y * I)) •
      (Gamma (((2 - β : ℝ) : ℂ) + y * I) * LSeries f (((2 - β : ℝ) : ℂ) + y * I))) =
      ∫ t : ℝ, riemannZeta (2 + t * I) * χ.LFunction (2 + t * I) * ψ.LFunction (2 + t * I) *
        (χ.mul ψ).LFunction (2 + t * I) *
        ((x : ℂ) ^ (-((2 + t * I) - β)) * Gamma ((2 + t * I) - β)) := by
    refine integral_congr_ae (Eventually.of_forall fun t ↦ ?_)
    have hw : ((2 - β : ℝ) : ℂ) + t * I = (2 + t * I) - (β : ℂ) := by push_cast; ring
    have hwβ : (2 + t * I) - (β : ℂ) + (β : ℂ) = 2 + t * I := sub_add_cancel _ _
    have hre : 1 < (2 + (t : ℂ) * I).re := by simp
    have hLf : LSeries f ((2 + t * I) - (β : ℂ)) =
        LSeries (χ.zetaMulPairCoeffs ψ) (2 + t * I) := by
      rw [TauCeti.LSeries.LSeries_mul_natCast_cpow_neg, hwβ]
    dsimp only
    rw [smul_eq_mul, hw, hLf, (χ.LSeriesHasSum_zetaMulPairCoeffs ψ hre).LSeries_eq]
    ring
  rw [hint_eq] at h
  exact h

/-- **Positivity lower bound for the smoothed four-factor integral.** For quadratic `χ` and `ψ`,
`β < 2`, and `x > 0`, `e^{-x}` bounds the real part of `(2π)⁻¹` times the `Re s = 2` smoothed
four-factor integral from below. -/
theorem exp_neg_le_re_integral_pair_mul_Gamma (hχq : χ.IsQuadratic) (hψq : ψ.IsQuadratic)
    {β : ℝ} (hβ : β < 2) {x : ℝ} (hx : 0 < x) :
    Real.exp (-x) ≤
      ((((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ t : ℝ,
        riemannZeta (2 + t * I) * χ.LFunction (2 + t * I) * ψ.LFunction (2 + t * I) *
          (χ.mul ψ).LFunction (2 + t * I) *
          ((x : ℂ) ^ (-((2 + t * I) - β)) * Gamma ((2 + t * I) - β))).re) := by
  have hsum := hasSum_re (χ.hasSum_zetaMulPairCoeffs_cpow_neg_mul_exp ψ hβ hx)
  have hnonneg (n : ℕ) :
      0 ≤ (χ.zetaMulPairCoeffs ψ n * (n : ℂ) ^ (-(β : ℂ)) * Real.exp (-n * x)).re := by
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    obtain ⟨hre, him⟩ := Complex.nonneg_iff.mp (zetaMulPairCoeffs_nonneg hχq hψq n)
    have hc : χ.zetaMulPairCoeffs ψ n = ((χ.zetaMulPairCoeffs ψ n).re : ℂ) :=
      Complex.ext rfl him.symm
    have hpow : (n : ℂ) ^ (-(β : ℂ)) = (((n : ℝ) ^ (-β) : ℝ) : ℂ) := by
      rw [← ofReal_natCast, ofReal_cpow n.cast_nonneg, ofReal_neg]
    rw [hc, hpow, ← ofReal_mul, ← ofReal_mul, ofReal_re]
    positivity
  have hle := le_hasSum hsum 1 fun n _ ↦ hnonneg n
  have hone : (χ.zetaMulPairCoeffs ψ 1 * ((1 : ℕ) : ℂ) ^ (-(β : ℂ)) *
      Real.exp (-((1 : ℕ) : ℝ) * x)).re = Real.exp (-x) := by
    simp only [zetaMulPairCoeffs_one, Nat.cast_one, one_cpow, one_mul, neg_mul, ofReal_re]
  rwa [hone] at hle

end SmoothedSum

/-! ### Analyticity, polynomial growth, and contour shift from `Re s = 2` to `Re s = 1 / 2` -/

section ContourShift

variable {M N : ℕ} [NeZero M] [NeZero N]
variable (χ : DirichletCharacter ℂ M) (ψ : DirichletCharacter ℂ N)

/-- Analyticity of the smoothing weight `x^{-(s - β)} Γ(s - β)` at `s = 1` for `β < 1` and
`x > 0`. -/
theorem analyticAt_cpow_neg_sub_mul_Gamma_one {β : ℝ} (hβ : β < 1) {x : ℝ} (hx : 0 < x) :
    AnalyticAt ℂ (fun s : ℂ ↦ (x : ℂ) ^ (-(s - (β : ℂ))) * Gamma (s - (β : ℂ))) 1 := by
  have hcpow : AnalyticAt ℂ (fun s : ℂ ↦ (x : ℂ) ^ (-(s - (β : ℂ)))) 1 :=
    (Differentiable.const_cpow (by fun_prop) (.inl (ofReal_ne_zero.mpr hx.ne'))).analyticAt 1
  have hΓ : AnalyticAt ℂ (fun s : ℂ ↦ Gamma (s - (β : ℂ))) 1 := by
    refine (Complex.analyticAt_Gamma fun m hm ↦ ?_).comp (by fun_prop)
    have hre := congrArg re hm
    simp only [sub_re, one_re, ofReal_re, neg_re, natCast_re] at hre
    linarith [m.cast_nonneg (α := ℝ)]
  exact hcpow.mul hΓ

private theorem meromorphicAt_and_residue_pair_mul_Gamma_beta (hχ : χ ≠ 1) (hψ : ψ ≠ 1)
    {β : ℝ} (hβ : β < 1) {x : ℝ} (hx : 0 < x) :
    MeromorphicAt (fun s : ℂ ↦
      riemannZeta s * χ.LFunction s * ψ.LFunction s * (χ.mul ψ).LFunction s *
        ((x : ℂ) ^ (-(s - β)) * Gamma (s - β))) β ∧
    TauCeti.Contour.residue (fun s : ℂ ↦
      riemannZeta s * χ.LFunction s * ψ.LFunction s * (χ.mul ψ).LFunction s *
        ((x : ℂ) ^ (-(s - β)) * Gamma (s - β))) β =
      riemannZeta β * χ.LFunction β * ψ.LFunction β * (χ.mul ψ).LFunction β := by
  have hβ1 : (β : ℂ) ≠ 1 := by exact_mod_cast hβ.ne
  have hζ : AnalyticAt ℂ riemannZeta β :=
    (differentiableOn_riemannZeta.analyticOnNhd isOpen_compl_singleton) β hβ1
  have hmul : AnalyticAt ℂ (χ.mul ψ).LFunction β :=
    ((DifferentiableOn.analyticOnNhd
      (fun z (hz : z ∈ ({1}ᶜ : Set ℂ)) ↦
        (differentiableAt_LFunction _ z (.inl hz)).differentiableWithinAt)
      isOpen_compl_singleton)) β hβ1
  have hcpow : AnalyticAt ℂ (fun s : ℂ ↦ (x : ℂ) ^ (-(s - (β : ℂ)))) β :=
    (Differentiable.const_cpow (by fun_prop) (.inl (ofReal_ne_zero.mpr hx.ne'))).analyticAt β
  have hΓ1 : AnalyticAt ℂ (fun s : ℂ ↦ Gamma (s - (β : ℂ) + 1)) β := by
    refine (Complex.analyticAt_Gamma fun m hm ↦ ?_).comp (by fun_prop)
    have hre := congrArg re hm
    simp only [sub_self, zero_add, one_re, neg_re, natCast_re] at hre
    linarith [m.cast_nonneg (α := ℝ)]
  have hreg : AnalyticAt ℂ (fun s : ℂ ↦
      riemannZeta s * χ.LFunction s * ψ.LFunction s * (χ.mul ψ).LFunction s *
        ((x : ℂ) ^ (-(s - β)) * Gamma (s - β + 1))) β :=
    ((((hζ.mul ((differentiable_LFunction hχ).analyticAt β)).mul
      ((differentiable_LFunction hψ).analyticAt β)).mul hmul).mul
      (hcpow.mul hΓ1))
  have hev : (fun s : ℂ ↦
      riemannZeta s * χ.LFunction s * ψ.LFunction s * (χ.mul ψ).LFunction s *
        ((x : ℂ) ^ (-(s - β)) * Gamma (s - β))) =ᶠ[𝓝[≠] (β : ℂ)]
      fun s : ℂ ↦ (s - β) ^ (-1 : ℤ) •
        (riemannZeta s * χ.LFunction s * ψ.LFunction s * (χ.mul ψ).LFunction s *
          ((x : ℂ) ^ (-(s - β)) * Gamma (s - β + 1))) := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hne : s - (β : ℂ) ≠ 0 := sub_ne_zero.mpr hs
    rw [Gamma_add_one _ hne, smul_eq_mul, zpow_neg_one]
    field_simp [hne]
  refine ⟨MeromorphicAt.iff_eventuallyEq_zpow_smul_analyticAt.mpr ⟨-1, _, hreg, hev⟩, ?_⟩
  simpa [iteratedDeriv_zero, Complex.Gamma_one] using
    TauCeti.Contour.residue_eq_of_eventuallyEq_zpow_smul (by norm_num : (-1 : ℤ) ≤ -1) hreg hev

private theorem meromorphicAt_pair_mul_Gamma_one (hχ : χ ≠ 1) (hψ : ψ ≠ 1)
    {β : ℝ} (hβ : β < 1) {x : ℝ} (hx : 0 < x) :
    MeromorphicAt (fun s : ℂ ↦
      riemannZeta s * χ.LFunction s * ψ.LFunction s * (χ.mul ψ).LFunction s *
        ((x : ℂ) ^ (-(s - β)) * Gamma (s - β))) 1 := by
  have hp : MeromorphicAt
      (fun s : ℂ ↦ riemannZeta s * χ.LFunction s * ψ.LFunction s * (χ.mul ψ).LFunction s) 1 := by
    by_cases hχψ : χ.mul ψ = 1
    · exact meromorphicAt_of_meromorphicOrderAt_ne_zero
        (by rw [meromorphicOrderAt_pair_eq_neg_two χ ψ hχ hψ hχψ]; decide)
    · exact meromorphicAt_of_meromorphicOrderAt_ne_zero
        (by rw [meromorphicOrderAt_pair_eq_neg_one χ ψ hχ hψ hχψ]; decide)
  exact hp.mul (analyticAt_cpow_neg_sub_mul_Gamma_one hβ hx).meromorphicAt

/-- Uniform fourth-power polynomial growth of the four-factor product on
`{s | 1 / 2 ≤ s.re ∧ 1 / 2 ≤ ‖s - 1‖}`, covering both principal and nonprincipal `χ.mul ψ`. -/
private theorem exists_norm_pair_le_mul_norm_pow_four (hχ : χ ≠ 1) (hψ : ψ ≠ 1) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ s : ℂ, 1 / 2 ≤ s.re → 1 / 2 ≤ ‖s - 1‖ →
      ‖riemannZeta s * χ.LFunction s * ψ.LFunction s * (χ.mul ψ).LFunction s‖ ≤
        B * ‖s‖ ^ 4 := by
  have hζ (s : ℂ) (hre : 1 / 2 ≤ s.re) (h1 : 1 / 2 ≤ ‖s - 1‖) : ‖riemannZeta s‖ ≤ 4 * ‖s‖ := by
    have hs1 : s ≠ 1 := fun h ↦ by rw [h, sub_self, norm_zero] at h1; linarith
    calc ‖riemannZeta s‖ ≤ ‖s‖ / ‖s - 1‖ + ‖s‖ / s.re :=
          TauCeti.norm_riemannZeta_le_div_add_div (by linarith) hs1
      _ ≤ ‖s‖ / (1 / 2) + ‖s‖ / (1 / 2) := by gcongr
      _ = 4 * ‖s‖ := by ring
  have hL {L : ℕ} [NeZero L] (ρ : DirichletCharacter ℂ L) (hρ : ρ ≠ 1)
      (s : ℂ) (hre : 1 / 2 ≤ s.re) : ‖ρ.LFunction s‖ ≤ (2 * L) * ‖s‖ := by
    calc ‖ρ.LFunction s‖ ≤ (L : ℝ) * ‖s‖ / s.re :=
          ρ.norm_LFunction_le_level_mul_norm_div_re hρ (by linarith)
      _ ≤ (L : ℝ) * ‖s‖ / (1 / 2) := by gcongr
      _ = (2 * L) * ‖s‖ := by ring
  obtain ⟨C₄, hC₄0, hC₄⟩ : ∃ C₄ : ℝ, 0 ≤ C₄ ∧
      ∀ s : ℂ, 1 / 2 ≤ s.re → 1 / 2 ≤ ‖s - 1‖ → ‖(χ.mul ψ).LFunction s‖ ≤ C₄ * ‖s‖ := by
    by_cases hχψ : χ.mul ψ = 1
    · refine ⟨4 * (2 : ℝ) ^ (Nat.lcm M N).primeFactors.card, by positivity, fun s hre h1 ↦ ?_⟩
      have hs1 : s ≠ 1 := fun h ↦ by rw [h, sub_self, norm_zero] at h1; linarith
      rw [hχψ, ← LFunctionTrivChar, LFunctionTrivChar_eq_mul_riemannZeta hs1, norm_mul, norm_prod]
      have hprod : ∏ p ∈ (Nat.lcm M N).primeFactors, ‖(1 : ℂ) - (p : ℂ) ^ (-s)‖ ≤
          (2 : ℝ) ^ (Nat.lcm M N).primeFactors.card := by
        refine (Finset.prod_le_prod₀ (g := fun _ ↦ (2 : ℝ)) (fun _ _ ↦ norm_nonneg _)
          fun p hp ↦ ?_).trans_eq (by simp)
        have hp0 : 0 < p := (Nat.prime_of_mem_primeFactors hp).pos
        have hcp : ‖(p : ℂ) ^ (-s)‖ ≤ 1 := by
          rw [norm_natCast_cpow_of_pos hp0, neg_re]
          exact Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hp0) (by linarith)
        exact (norm_sub_le _ _).trans (by rw [norm_one]; linarith)
      exact (mul_le_mul hprod (hζ s hre h1) (norm_nonneg _) (by positivity)).trans_eq (by ring)
    · exact ⟨2 * Nat.lcm M N, by positivity, fun s hre _ ↦ hL (χ.mul ψ) hχψ s hre⟩
  refine ⟨4 * (2 * M) * (2 * N) * C₄, by positivity, fun s hre h1 ↦ ?_⟩
  rw [norm_mul, norm_mul, norm_mul]
  exact (mul_le_mul (mul_le_mul (mul_le_mul (hζ s hre h1) (hL χ hχ s hre)
    (norm_nonneg _) (by positivity)) (hL ψ hψ s hre) (norm_nonneg _) (by positivity))
    (hC₄ s hre h1) (norm_nonneg _) (by positivity)).trans_eq (by ring)

/-- Integrability of the smoothed four-factor integrand on a vertical line `Re s = σ` with
`1 / 2 ≤ σ`, `1 / 2 ≤ |σ - 1|`, and `σ - β` avoiding the poles of `Γ`. -/
private theorem integrable_pair_mul_Gamma_vertical (hχ : χ ≠ 1) (hψ : ψ ≠ 1)
    {β σ x : ℝ} (hx : 0 < x) (hσ : 1 / 2 ≤ σ) (hσ1 : 1 / 2 ≤ |σ - 1|)
    (hpoles : ∀ m : ℕ, σ - β ≠ -m) :
    Integrable (fun t : ℝ ↦
      riemannZeta (σ + t * I) * χ.LFunction (σ + t * I) * ψ.LFunction (σ + t * I) *
        (χ.mul ψ).LFunction (σ + t * I) *
        ((x : ℂ) ^ (-((σ + t * I) - β)) * Gamma ((σ + t * I) - β))) := by
  obtain ⟨B, hB0, hB⟩ := χ.exists_norm_pair_le_mul_norm_pow_four ψ hχ hψ
  obtain ⟨CΓ, hCΓ⟩ := exists_norm_Gamma_le_mul_inv_one_add_sq_pow hpoles 3
  have hCΓ' (t : ℝ) : ‖Gamma ((σ + t * I) - β)‖ ≤ max CΓ 0 * ((1 + t ^ 2) ^ 3)⁻¹ := by
    have heq : (σ + (t : ℂ) * I) - β = ((σ - β : ℝ) : ℂ) + t * I := by push_cast; ring
    exact heq ▸ (hCΓ t).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
  set K : ℝ := B * (1 + σ ^ 2) ^ 2 * x ^ (β - σ) * max CΓ 0
  refine (integrable_inv_one_add_sq.const_mul K).mono' ?_ (Eventually.of_forall fun t ↦ ?_)
  · refine Continuous.aestronglyMeasurable (continuous_iff_continuousAt.mpr fun t ↦ ?_)
    have hs1 : (σ : ℂ) + t * I ≠ 1 := fun h ↦ by
      have hre := congrArg re h
      simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
        sub_self, add_zero, one_re] at hre
      subst hre; norm_num at hσ1
    have hdiff : DifferentiableAt ℂ (fun s : ℂ ↦
        riemannZeta s * χ.LFunction s * ψ.LFunction s * (χ.mul ψ).LFunction s *
          ((x : ℂ) ^ (-(s - β)) * Gamma (s - β))) (σ + t * I) := by
      refine ((((differentiableAt_riemannZeta hs1).mul
        (differentiable_LFunction hχ _)).mul (differentiable_LFunction hψ _)).mul
        (differentiableAt_LFunction _ _ (.inl hs1))).mul
        (((Differentiable.const_cpow (by fun_prop) (.inl (ofReal_ne_zero.mpr hx.ne'))) _).mul ?_)
      refine (differentiableAt_Gamma _ fun m hm ↦ hpoles m ?_).comp _ (by fun_prop)
      have hre := congrArg re hm
      simp only [sub_re, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im,
        mul_one, sub_self, add_zero, neg_re, natCast_re] at hre
      exact hre
    exact ContinuousAt.comp (f := fun u : ℝ ↦ (σ : ℂ) + u * I) hdiff.continuousAt (by fun_prop)
  · set s : ℂ := σ + t * I
    have hsre : s.re = σ := by simp [s]
    have hs1 : 1 / 2 ≤ ‖s - 1‖ := hσ1.trans (by simpa [s] using abs_re_le_norm (s - 1))
    have hns : ‖s‖ ^ 4 ≤ (1 + σ ^ 2) ^ 2 * (1 + t ^ 2) ^ 2 := by
      have hsq : ‖s‖ ^ 2 = σ ^ 2 + t ^ 2 := by
        rw [← normSq_eq_norm_sq, normSq_apply]
        simp only [s, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
          sub_self, add_zero, add_im, mul_im, zero_add]
        ring
      calc ‖s‖ ^ 4 = (‖s‖ ^ 2) ^ 2 := by ring
        _ ≤ ((1 + σ ^ 2) * (1 + t ^ 2)) ^ 2 :=
            pow_le_pow_left₀ (by positivity) (by rw [hsq]; nlinarith [sq_nonneg (σ * t)]) 2
        _ = (1 + σ ^ 2) ^ 2 * (1 + t ^ 2) ^ 2 := by ring
    have hxpow : ‖(x : ℂ) ^ (-(s - β))‖ = x ^ (β - σ) := by
      rw [norm_cpow_eq_rpow_re_of_pos hx]; congr 1; simp [s]
    have h1t : 0 < 1 + t ^ 2 := by positivity
    rw [norm_mul, norm_mul ((x : ℂ) ^ _), hxpow]
    calc _ ≤ (B * ‖s‖ ^ 4) * (x ^ (β - σ) * (max CΓ 0 * ((1 + t ^ 2) ^ 3)⁻¹)) :=
          mul_le_mul (hB s (hsre ▸ hσ) hs1)
            (mul_le_mul_of_nonneg_left (hCΓ' t) (by positivity)) (by positivity) (by positivity)
      _ ≤ (B * ((1 + σ ^ 2) ^ 2 * (1 + t ^ 2) ^ 2)) *
          (x ^ (β - σ) * (max CΓ 0 * ((1 + t ^ 2) ^ 3)⁻¹)) := by gcongr
      _ = K * (1 + t ^ 2)⁻¹ := by simp only [K]; field_simp [h1t.ne']

private theorem exists_norm_Gamma_horizontal_le {β c : ℝ} (hβ : β ∈ Set.Ioo (1 / 2) 1)
    (hc : |c| = 1) :
    ∃ CΓ : ℝ, 0 ≤ CΓ ∧ ∀ {T : ℝ}, 1 ≤ T → ∀ {σ : ℝ}, σ ∈ Set.Ioc (1 / 2) 2 →
      ‖Gamma ((σ + (c * T : ℝ) * I) - β)‖ ≤ CΓ / T ^ 6 := by
  obtain ⟨CΓ, hCΓ⟩ := (isCompact_Icc (a := (5 : ℝ)) (b := 8)).exists_bound_of_continuousOn
    (Real.differentiableOn_Gamma_Ioi.continuousOn.mono
      fun y hy ↦ Set.mem_Ioi.mpr (by linarith [hy.1]))
  refine ⟨CΓ, (norm_nonneg _).trans (hCΓ 5 ⟨le_rfl, by norm_num⟩), fun {T} hT {σ} hσ ↦ ?_⟩
  have hT0 : 0 < T := zero_lt_one.trans_le hT
  set s : ℂ := σ + (c * T : ℝ) * I
  have h6 : 0 < (s - (β : ℂ)).re + (6 : ℕ) := by
    simp only [s, sub_re, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im,
      mul_one, sub_self, add_zero]
    push_cast; linarith [hσ.1, hβ.2]
  have hprod : T ^ 6 ≤ ∏ k ∈ Finset.range 6, ‖s - (β : ℂ) + k‖ := by
    refine (by simp : T ^ 6 = ∏ _k ∈ Finset.range 6, T).trans_le
      (Finset.prod_le_prod₀ (fun _ _ ↦ hT0.le) fun k _ ↦ ?_)
    have him := abs_im_le_norm (s - (β : ℂ) + k)
    simpa [s, hc, abs_of_pos hT0] using him
  have hGmem : (s - (β : ℂ)).re + (6 : ℕ) ∈ Set.Icc (5 : ℝ) 8 := by
    simp only [s, sub_re, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im,
      mul_one, sub_self, add_zero, Set.mem_Icc]
    constructor <;> push_cast <;> linarith [hσ.1, hσ.2, hβ.1, hβ.2]
  have hGC : Real.Gamma ((s - (β : ℂ)).re + (6 : ℕ)) ≤ CΓ :=
    (le_abs_self _).trans (Real.norm_eq_abs _ ▸ hCΓ _ hGmem)
  rw [le_div_iff₀ (pow_pos hT0 6)]
  exact (mul_le_mul_of_nonneg_left hprod (norm_nonneg _)).trans
    ((norm_Gamma_mul_prod_norm_le h6).trans hGC)

/-- Horizontal segment decay: for `c = ±1` and `β ∈ (1 / 2, 1)`, the horizontal integral of the
smoothed four-factor integrand over `[1 / 2, 2] + c T i` tends to `0` as `T → ∞`. -/
private theorem tendsto_horizontal_pair_mul_Gamma (hχ : χ ≠ 1) (hψ : ψ ≠ 1)
    {β x c : ℝ} (hβ : β ∈ Set.Ioo (1 / 2) 1) (hx : 0 < x) (hc : |c| = 1) :
    Tendsto (fun T : ℝ ↦ ∫ σ : ℝ in (1 / 2 : ℝ)..2,
      riemannZeta (σ + (c * T : ℝ) * I) * χ.LFunction (σ + (c * T : ℝ) * I) *
        ψ.LFunction (σ + (c * T : ℝ) * I) * (χ.mul ψ).LFunction (σ + (c * T : ℝ) * I) *
        ((x : ℂ) ^ (-((σ + (c * T : ℝ) * I) - β)) * Gamma ((σ + (c * T : ℝ) * I) - β)))
      atTop (𝓝 0) := by
  obtain ⟨B, hB0, hB⟩ := χ.exists_norm_pair_le_mul_norm_pow_four ψ hχ hψ
  obtain ⟨CΓ, _, hΓb⟩ := exists_norm_Gamma_horizontal_le hβ hc
  set X : ℝ := max (x ^ (β - 1 / 2)) (x ^ (β - 2))
  have hX0 : 0 ≤ X := le_trans (by positivity) (le_max_left _ _)
  refine squeeze_zero_norm' ?_
    (((tendsto_inv_atTop_zero.pow 2).const_mul (3 / 2 * (B * 81 * X * CΓ))).trans_eq (by simp))
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
  have hT0 : 0 < T := zero_lt_one.trans_le hT
  refine (intervalIntegral.norm_integral_le_of_norm_le_const (C := B * 81 * X * CΓ * (T⁻¹) ^ 2)
    fun σ hσ ↦ ?_).trans_eq (by norm_num; ring)
  rw [uIoc_of_le (by norm_num)] at hσ
  set s : ℂ := σ + (c * T : ℝ) * I
  have hsre : s.re = σ := by simp [s]
  have hs1 : 1 / 2 ≤ ‖s - 1‖ := by
    have him := abs_im_le_norm (s - 1)
    simp only [s, sub_im, one_im, sub_zero, add_im, ofReal_im, mul_im, I_re, mul_zero,
      ofReal_re, I_im, mul_one, add_zero, zero_add, abs_mul, hc, one_mul, abs_of_pos hT0] at him
    linarith
  have hns : ‖s‖ ^ 4 ≤ 81 * T ^ 4 := by
    have hn : ‖s‖ ≤ 3 * T := by
      calc ‖s‖ ≤ ‖(σ : ℂ)‖ + ‖((c * T : ℝ) : ℂ) * I‖ := norm_add_le _ _
        _ = |σ| + T := by simp [hc, abs_of_pos hT0]
        _ ≤ 3 * T := by rw [abs_of_pos (by linarith [hσ.1])]; linarith [hσ.2]
    exact (pow_le_pow_left₀ (norm_nonneg _) hn 4).trans_eq (by ring)
  have hxpow : ‖(x : ℂ) ^ (-(s - β))‖ ≤ X := by
    have hre' : (-(s - (β : ℂ))).re = β - σ := by simp [hsre]
    rw [norm_cpow_eq_rpow_re_of_pos hx, hre']
    rcases le_or_gt 1 x with hx1 | hx1
    · exact (Real.rpow_le_rpow_of_exponent_le hx1 (by linarith [hσ.1])).trans (le_max_left _ _)
    · exact (Real.rpow_le_rpow_of_exponent_ge hx hx1.le (by linarith [hσ.2])).trans
        (le_max_right _ _)
  rw [norm_mul, norm_mul ((x : ℂ) ^ _)]
  calc _ ≤ (B * (81 * T ^ 4)) * (X * (CΓ / T ^ 6)) :=
        mul_le_mul ((hB s (hsre ▸ hσ.1.le) hs1).trans (by gcongr))
          (mul_le_mul hxpow (hΓb hT hσ) (norm_nonneg _) hX0) (by positivity) (by positivity)
    _ = B * 81 * X * CΓ * (T⁻¹) ^ 2 := by field_simp [hT0.ne']

private theorem differentiableOn_pair_mul_Gamma (hχ : χ ≠ 1) (hψ : ψ ≠ 1)
    {β x : ℝ} (hβ : β < 1) (hx : 0 < x) :
    DifferentiableOn ℂ (fun s : ℂ ↦
      riemannZeta s * χ.LFunction s * ψ.LFunction s * (χ.mul ψ).LFunction s *
        ((x : ℂ) ^ (-(s - β)) * Gamma (s - β)))
      ({s : ℂ | 1 / 4 < s.re} \ ({1, (β : ℂ)} : Set ℂ)) := by
  intro s ⟨(hsU : 1 / 4 < s.re), hsS⟩
  have hs1 : s ≠ 1 := fun h ↦ hsS (by simp [h])
  have hsβ : s ≠ (β : ℂ) := fun h ↦ hsS (by simp [h])
  refine (((((differentiableAt_riemannZeta hs1).mul
    (differentiable_LFunction hχ s)).mul (differentiable_LFunction hψ s)).mul
    (differentiableAt_LFunction _ s (.inl hs1))).mul
    (((Differentiable.const_cpow (by fun_prop) (.inl (ofReal_ne_zero.mpr hx.ne'))) s).mul ?_)
      ).differentiableWithinAt
  refine (differentiableAt_Gamma _ fun m hm ↦ ?_).comp s (by fun_prop)
  rcases eq_or_ne m 0 with rfl | hm0
  · exact sub_ne_zero.mpr hsβ (by simpa using hm)
  · have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast Nat.pos_of_ne_zero hm0
    have hre := congrArg re hm
    simp only [sub_re, ofReal_re, neg_re, natCast_re] at hre
    linarith

/-- Rectangle residue identity on `[1 / 2, 2] × [-T, T]` (`T > 0`) for `β ∈ (1 / 2, 1)`. -/
private theorem rect_residue_pair_mul_Gamma (hχ : χ ≠ 1) (hψ : ψ ≠ 1)
    {β x T : ℝ} (hβ : β ∈ Set.Ioo (1 / 2) 1) (hx : 0 < x) (hT : 0 < T) :
    let g : ℂ → ℂ := fun s ↦
      riemannZeta s * χ.LFunction s * ψ.LFunction s * (χ.mul ψ).LFunction s *
        ((x : ℂ) ^ (-(s - β)) * Gamma (s - β))
    (∫ σ : ℝ in (1 / 2 : ℝ)..2, g (σ + (-T : ℝ) * I)) -
      (∫ σ : ℝ in (1 / 2 : ℝ)..2, g (σ + (T : ℝ) * I)) +
      I * (∫ t : ℝ in (-T)..T, g (2 + t * I)) -
      I * (∫ t : ℝ in (-T)..T, g (1 / 2 + t * I)) =
      2 * Real.pi * I *
        (TauCeti.Contour.residue g 1 +
          riemannZeta β * χ.LFunction β * ψ.LFunction β * (χ.mul ψ).LFunction β) := by
  intro g
  set U : Set ℂ := {s | 1 / 4 < s.re}
  set S : Finset ℂ := {1, (β : ℂ)}
  set z : ℂ := (1 / 2 : ℝ) + (-T : ℝ) * I
  set w : ℂ := (2 : ℝ) + (T : ℝ) * I
  have hzre : z.re = 1 / 2 := by simp [z]
  have hwre : w.re = 2 := by simp [w]
  have hzim : z.im = -T := by simp [z]
  have hwim : w.im = T := by simp [w]
  have hU : IsOpen U := isOpen_lt continuous_const continuous_re
  have h1neβ : (1 : ℂ) ≠ (β : ℂ) := by exact_mod_cast hβ.2.ne'
  have hgdiff : DifferentiableOn ℂ g (U \ (↑S : Set ℂ)) := by
    simpa [g, U, S] using χ.differentiableOn_pair_mul_Gamma ψ hχ hψ hβ.2 hx
  have hmero : ∀ s ∈ S, s ∈ U → MeromorphicAt g s := by
    intro s hs _
    rcases Finset.mem_insert.mp hs with rfl | hs'
    · exact χ.meromorphicAt_pair_mul_Gamma_one ψ hχ hψ hβ.2 hx
    · rw [Finset.mem_singleton.mp hs']
      exact (χ.meromorphicAt_and_residue_pair_mul_Gamma_beta ψ hχ hψ hβ.2 hx).1
  have hrectU : Rectangle z w ⊆ U := by
    intro p hp
    rw [mem_rectangle_iff (by linarith) (by linarith)] at hp
    exact Set.mem_ofPred.mpr (by linarith [hp.1.1])
  have hfrS : ∀ p ∈ frontier (Rectangle z w), p ∉ (↑S : Set ℂ) := by
    intro p hp hpS
    rw [frontier_rectangle, uIcc_of_le (by linarith), uIcc_of_le (by linarith)] at hp
    have hpim : p.im = 0 ∧ (1 / 2 < p.re ∧ p.re < 2) := by
      rcases Finset.mem_insert.mp (Finset.mem_coe.mp hpS) with rfl | h'
      · norm_num
      · rw [Finset.mem_singleton.mp h']; exact ⟨by simp, hβ.1, by rw [ofReal_re]; linarith [hβ.2]⟩
    rcases hp with ⟨_, him⟩ | ⟨hre, _⟩
    · simp [hzim, hwim, hpim.1, hT.ne, hT.ne'] at him
    · rw [Set.mem_preimage, hzre, hwre, mem_insert_iff, mem_singleton_iff] at hre
      rcases hre with hre | hre <;> linarith [hpim.2.1, hpim.2.2]
  have hcont : ContinuousOn g (frontier (Rectangle z w)) :=
    hgdiff.continuousOn.mono fun p hp ↦ ⟨hrectU ((isClosed_rectangle z w).frontier_subset hp),
      hfrS p hp⟩
  have hres := TauCeti.Contour.classicalResidueTheorem_nullHomologous hU hgdiff hmero
    (isPiecewiseC1On_rectBoundary z w) (fun t _ ↦ hrectU (rectBoundary_mem_rectangle t))
    (by simp) (fun t _ ↦ hfrS _ (rectBoundary_mem_frontier t))
    (TauCeti.Contour.isNullHomologous_rectBoundary hrectU)
  have hw1 : TauCeti.Contour.windingNumber (rectBoundary z w) 0 4 1 = 1 :=
    TauCeti.Contour.windingNumber_rectBoundary_eq_one (by
      rw [mem_reProdIm, hzre, hwre, hzim, hwim]
      exact ⟨by norm_num, by rw [one_im]; exact ⟨by linarith, hT⟩⟩)
  have hwβ : TauCeti.Contour.windingNumber (rectBoundary z w) 0 4 (β : ℂ) = 1 :=
    TauCeti.Contour.windingNumber_rectBoundary_eq_one (by
      rw [mem_reProdIm, hzre, hwre, hzim, hwim, ofReal_re, ofReal_im]
      exact ⟨⟨hβ.1, by linarith [hβ.2]⟩, by linarith, hT⟩)
  rw [integral_rectBoundary hcont, Finset.sum_pair h1neβ, hw1, hwβ, one_mul, one_mul,
    (χ.meromorphicAt_and_residue_pair_mul_Gamma_beta ψ hχ hψ hβ.2 hx).2] at hres
  simpa [z, w, smul_eq_mul] using hres

/-- **Contour shift for the smoothed four-factor integral.** For nonprincipal `χ` and `ψ`,
`β ∈ (1 / 2, 1)`, and `x > 0`, shifting `Re s = 2` to `Re s = 1 / 2` picks up the residue at `1`
(simple or double) together with `F(β)` at the simple pole `s = β` of `Γ(s - β)`. -/
theorem integral_pair_mul_Gamma_two_eq (hχ : χ ≠ 1) (hψ : ψ ≠ 1)
    {β : ℝ} (hβ : β ∈ Set.Ioo (1 / 2) 1) {x : ℝ} (hx : 0 < x) :
    (((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ t : ℝ,
      riemannZeta (2 + t * I) * χ.LFunction (2 + t * I) * ψ.LFunction (2 + t * I) *
        (χ.mul ψ).LFunction (2 + t * I) *
        ((x : ℂ) ^ (-((2 + t * I) - β)) * Gamma ((2 + t * I) - β))) =
      TauCeti.Contour.residue (fun s ↦
        riemannZeta s * χ.LFunction s * ψ.LFunction s * (χ.mul ψ).LFunction s *
          ((x : ℂ) ^ (-(s - β)) * Gamma (s - β))) 1 +
        riemannZeta β * χ.LFunction β * ψ.LFunction β * (χ.mul ψ).LFunction β +
        (((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ t : ℝ,
          riemannZeta (1 / 2 + t * I) * χ.LFunction (1 / 2 + t * I) *
            ψ.LFunction (1 / 2 + t * I) * (χ.mul ψ).LFunction (1 / 2 + t * I) *
            ((x : ℂ) ^ (-((1 / 2 + t * I) - β)) * Gamma ((1 / 2 + t * I) - β))) := by
  set g : ℂ → ℂ := fun s ↦
    riemannZeta s * χ.LFunction s * ψ.LFunction s * (χ.mul ψ).LFunction s *
      ((x : ℂ) ^ (-(s - β)) * Gamma (s - β))
  have hint2 : Integrable (fun t : ℝ ↦ g (2 + t * I)) := by
    simpa [g] using χ.integrable_pair_mul_Gamma_vertical ψ hχ hψ (σ := 2) hx (by norm_num)
      (by norm_num) fun m hm ↦ by linarith [hβ.2, m.cast_nonneg (α := ℝ)]
  have hint12 : Integrable (fun t : ℝ ↦ g (1 / 2 + t * I)) := by
    simpa [g] using χ.integrable_pair_mul_Gamma_vertical ψ hχ hψ (σ := 1 / 2) hx le_rfl
      (by norm_num) fun m hm ↦ by
        rcases eq_or_ne m 0 with rfl | hm0
        · rw [Nat.cast_zero, neg_zero] at hm; linarith [hβ.1]
        · have : (1 : ℝ) ≤ m := by exact_mod_cast Nat.pos_of_ne_zero hm0
          linarith [hβ.2]
  have hbot : Tendsto (fun T : ℝ ↦ ∫ σ : ℝ in (1 / 2 : ℝ)..2, g (σ + (-T : ℝ) * I))
      atTop (𝓝 0) := by
    simpa [g] using χ.tendsto_horizontal_pair_mul_Gamma ψ hχ hψ hβ hx (c := -1) (by norm_num)
  have htop : Tendsto (fun T : ℝ ↦ ∫ σ : ℝ in (1 / 2 : ℝ)..2, g (σ + (T : ℝ) * I))
      atTop (𝓝 0) := by
    simpa [g] using χ.tendsto_horizontal_pair_mul_Gamma ψ hχ hψ hβ hx (c := 1) (by norm_num)
  have hv2 := intervalIntegral_tendsto_integral hint2 tendsto_neg_atTop_atBot tendsto_id
  have hv12 := intervalIntegral_tendsto_integral hint12 tendsto_neg_atTop_atBot tendsto_id
  have hlhs : Tendsto (fun T : ℝ ↦
      (∫ σ : ℝ in (1 / 2 : ℝ)..2, g (σ + (-T : ℝ) * I)) -
        (∫ σ : ℝ in (1 / 2 : ℝ)..2, g (σ + (T : ℝ) * I)) +
        I * (∫ t : ℝ in (-T)..T, g (2 + t * I)) -
        I * (∫ t : ℝ in (-T)..T, g (1 / 2 + t * I)))
      atTop (𝓝 (0 - 0 + I * (∫ t : ℝ, g (2 + t * I)) - I * (∫ t : ℝ, g (1 / 2 + t * I)))) :=
    ((hbot.sub htop).add (hv2.const_mul I)).sub (hv12.const_mul I)
  have hconst : Tendsto (fun T : ℝ ↦
      (∫ σ : ℝ in (1 / 2 : ℝ)..2, g (σ + (-T : ℝ) * I)) -
        (∫ σ : ℝ in (1 / 2 : ℝ)..2, g (σ + (T : ℝ) * I)) +
        I * (∫ t : ℝ in (-T)..T, g (2 + t * I)) -
        I * (∫ t : ℝ in (-T)..T, g (1 / 2 + t * I)))
      atTop (𝓝 (2 * Real.pi * I *
        (TauCeti.Contour.residue g 1 +
          riemannZeta β * χ.LFunction β * ψ.LFunction β * (χ.mul ψ).LFunction β))) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
    exact (χ.rect_residue_pair_mul_Gamma ψ hχ hψ hβ hx hT).symm
  have heq := tendsto_nhds_unique hlhs hconst
  have h2 : (∫ t : ℝ, g (2 + t * I)) =
      2 * Real.pi * (TauCeti.Contour.residue g 1 +
        riemannZeta β * χ.LFunction β * ψ.LFunction β * (χ.mul ψ).LFunction β) +
      (∫ t : ℝ, g (1 / 2 + t * I)) := by
    have heq' : (∫ t : ℝ, g (2 + t * I)) - (∫ t : ℝ, g (1 / 2 + t * I)) =
        2 * Real.pi * (TauCeti.Contour.residue g 1 +
          riemannZeta β * χ.LFunction β * ψ.LFunction β * (χ.mul ψ).LFunction β) :=
      mul_left_cancel₀ I_ne_zero (by linear_combination heq)
    linear_combination heq'
  have hpi : (((1 / (2 * Real.pi) : ℝ) : ℂ) * (2 * Real.pi)) = 1 := by
    have : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
    push_cast; field_simp
  rw [h2, mul_add, ← mul_assoc, hpi, one_mul]

/-- **Simple-pole contour shift (`χ.mul ψ ≠ 1`).** For nonprincipal `χ` and `ψ` with
`χ.mul ψ ≠ 1`, `β ∈ (1 / 2, 1)`, and `x > 0`, shifting `Re s = 2` to `Re s = 1 / 2` yields the
simple-pole residue `L(1, χ) L(1, ψ) L(1, χ.mul ψ) x^{-(1 - β)} Γ(1 - β)` at `1` plus `F(β)` at
`β`. -/
theorem integral_pair_mul_Gamma_two_eq_of_mul_ne_one (hχ : χ ≠ 1) (hψ : ψ ≠ 1)
    (hχψ : χ.mul ψ ≠ 1) {β : ℝ} (hβ : β ∈ Set.Ioo (1 / 2) 1) {x : ℝ} (hx : 0 < x) :
    (((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ t : ℝ,
      riemannZeta (2 + t * I) * χ.LFunction (2 + t * I) * ψ.LFunction (2 + t * I) *
        (χ.mul ψ).LFunction (2 + t * I) *
        ((x : ℂ) ^ (-((2 + t * I) - β)) * Gamma ((2 + t * I) - β))) =
      χ.LFunction 1 * ψ.LFunction 1 * (χ.mul ψ).LFunction 1 *
        ((x : ℂ) ^ (-((1 : ℂ) - β)) * Gamma ((1 : ℂ) - β)) +
      riemannZeta β * χ.LFunction β * ψ.LFunction β * (χ.mul ψ).LFunction β +
      (((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ t : ℝ,
        riemannZeta (1 / 2 + t * I) * χ.LFunction (1 / 2 + t * I) *
          ψ.LFunction (1 / 2 + t * I) * (χ.mul ψ).LFunction (1 / 2 + t * I) *
          ((x : ℂ) ^ (-((1 / 2 + t * I) - β)) * Gamma ((1 / 2 + t * I) - β))) := by
  rw [χ.integral_pair_mul_Gamma_two_eq ψ hχ hψ hβ hx,
    χ.residue_pair_mul_of_mul_ne_one ψ hχ hψ hχψ (analyticAt_cpow_neg_sub_mul_Gamma_one hβ.2 hx)]

/-- **Double-pole contour shift (`χ.mul ψ = 1`).** For nonprincipal `χ` and `ψ` with
`χ.mul ψ = 1`, `β ∈ (1 / 2, 1)`, and `x > 0`, shifting `Re s = 2` to `Re s = 1 / 2` yields the
double-pole derivative residue at `1` plus `F(β)` at `β`. -/
theorem integral_pair_mul_Gamma_two_eq_of_mul_eq_one (hχ : χ ≠ 1) (hψ : ψ ≠ 1)
    (hχψ : χ.mul ψ = 1) {β : ℝ} (hβ : β ∈ Set.Ioo (1 / 2) 1) {x : ℝ} (hx : 0 < x) :
    (((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ t : ℝ,
      riemannZeta (2 + t * I) * χ.LFunction (2 + t * I) * ψ.LFunction (2 + t * I) *
        (χ.mul ψ).LFunction (2 + t * I) *
        ((x : ℂ) ^ (-((2 + t * I) - β)) * Gamma ((2 + t * I) - β))) =
      deriv (fun s ↦ LFunctionTrivChar₁ 1 s * χ.LFunction s * ψ.LFunction s *
        LFunctionTrivChar₁ (Nat.lcm M N) s * ((x : ℂ) ^ (-(s - β)) * Gamma (s - β))) 1 +
      riemannZeta β * χ.LFunction β * ψ.LFunction β * (χ.mul ψ).LFunction β +
      (((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ t : ℝ,
        riemannZeta (1 / 2 + t * I) * χ.LFunction (1 / 2 + t * I) *
          ψ.LFunction (1 / 2 + t * I) * (χ.mul ψ).LFunction (1 / 2 + t * I) *
          ((x : ℂ) ^ (-((1 / 2 + t * I) - β)) * Gamma ((1 / 2 + t * I) - β))) := by
  rw [χ.integral_pair_mul_Gamma_two_eq ψ hχ hψ hβ hx,
    χ.residue_pair_mul_of_mul_eq_one ψ hχ hψ hχψ (analyticAt_cpow_neg_sub_mul_Gamma_one hβ.2 hx)]

end ContourShift

/-! ### Uniform shifted-integral bound and Goldfeld's residue lower bound -/

section ResidueLowerBound

private theorem norm_pair_half_le {M N : ℕ} [NeZero M] [NeZero N]
    (χ : DirichletCharacter ℂ M) (ψ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (hψ : ψ ≠ 1) (hχψ : χ.mul ψ ≠ 1) (t : ℝ) :
    ‖riemannZeta (1 / 2 + t * I) * χ.LFunction (1 / 2 + t * I) *
      ψ.LFunction (1 / 2 + t * I) * (χ.mul ψ).LFunction (1 / 2 + t * I)‖ ≤
      32 * ((M : ℝ) * N) ^ 2 * (1 + t ^ 2) ^ 2 := by
  have hlcm : (Nat.lcm M N : ℝ) ≤ (M : ℝ) * N := by
    exact_mod_cast Nat.le_of_dvd (Nat.mul_pos (NeZero.pos M) (NeZero.pos N)) (Nat.lcm_dvd_mul M N)
  set s : ℂ := 1 / 2 + t * I
  have hsre : s.re = 1 / 2 := by simp [s]
  have hs0 : 0 < s.re := by linarith
  have hs1 : 1 / 2 ≤ ‖s - 1‖ := by
    have hre : (s - 1).re = -1 / 2 := by rw [sub_re, hsre, one_re]; norm_num
    have := abs_re_le_norm (s - 1); rw [hre] at this; norm_num at this; exact this
  have hsne1 : s ≠ 1 := fun h ↦ by rw [h, sub_self, norm_zero] at hs1; linarith
  have hζ : ‖riemannZeta s‖ ≤ 4 * ‖s‖ := by
    calc ‖riemannZeta s‖ ≤ ‖s‖ / ‖s - 1‖ + ‖s‖ / s.re :=
          TauCeti.norm_riemannZeta_le_div_add_div hs0 hsne1
      _ ≤ ‖s‖ / (1 / 2) + ‖s‖ / (1 / 2) := by rw [hsre]; gcongr
      _ = 4 * ‖s‖ := by ring
  have hL {L : ℕ} [NeZero L] (ρ : DirichletCharacter ℂ L) (hρ : ρ ≠ 1) :
      ‖ρ.LFunction s‖ ≤ 2 * L * ‖s‖ := by
    have hb := ρ.norm_LFunction_le_level_mul_norm_div_re hρ hs0; rw [hsre] at hb; linarith
  have hns : ‖s‖ ^ 4 ≤ (1 + t ^ 2) ^ 2 := by
    have hsim : s.im = t := by simp [s]
    have hsq : ‖s‖ ^ 2 ≤ 1 + t ^ 2 := by
      rw [← normSq_eq_norm_sq, normSq_apply, hsre, hsim]; linarith
    exact (by ring : ‖s‖ ^ 4 = (‖s‖ ^ 2) ^ 2).trans_le (pow_le_pow_left₀ (by positivity) hsq 2)
  rw [norm_mul, norm_mul, norm_mul]
  calc _ ≤ (4 * ‖s‖) * (2 * M * ‖s‖) * (2 * N * ‖s‖) * (2 * ((M : ℝ) * N) * ‖s‖) :=
        mul_le_mul (mul_le_mul (mul_le_mul hζ (hL χ hχ) (norm_nonneg _)
          (by positivity)) (hL ψ hψ) (norm_nonneg _) (by positivity))
          ((hL (χ.mul ψ) hχψ).trans (by gcongr)) (norm_nonneg _) (by positivity)
    _ = 32 * ((M : ℝ) * N) ^ 2 * ‖s‖ ^ 4 := by ring
    _ ≤ 32 * ((M : ℝ) * N) ^ 2 * (1 + t ^ 2) ^ 2 := by gcongr

private theorem exists_norm_Gamma_half_sub_le :
    ∃ KΓ : ℝ, 0 < KΓ ∧ ∀ {β : ℝ}, β ∈ Set.Ico (3 / 4) 1 → ∀ t : ℝ,
      ‖Gamma ((1 / 2 + t * I) - β)‖ ≤ KΓ * ((1 + t ^ 2) ^ 3)⁻¹ := by
  obtain ⟨CΓ, hCΓ⟩ := (isCompact_Icc (a := (5 : ℝ)) (b := 6)).exists_bound_of_continuousOn
    (Real.differentiableOn_Gamma_Ioi.continuousOn.mono
      fun y hy ↦ Set.mem_Ioi.mpr (by linarith [hy.1]))
  refine ⟨16 * max CΓ 1, by positivity, fun {β} hβ t ↦ ?_⟩
  set s : ℂ := 1 / 2 + t * I
  have hsre : s.re = 1 / 2 := by simp [s]
  have hsim : s.im = t := by simp [s]
  have h6 : 0 < (s - (β : ℂ)).re + (6 : ℕ) := by
    rw [sub_re, hsre, ofReal_re]; push_cast; linarith [hβ.2]
  have hGmem : (s - (β : ℂ)).re + (6 : ℕ) ∈ Set.Icc (5 : ℝ) 6 := by
    rw [sub_re, hsre, ofReal_re, Set.mem_Icc]
    constructor <;> push_cast <;> linarith [hβ.1, hβ.2]
  have hGC : Real.Gamma ((s - (β : ℂ)).re + (6 : ℕ)) ≤ max CΓ 1 :=
    ((le_abs_self _).trans (Real.norm_eq_abs _ ▸ hCΓ _ hGmem)).trans (le_max_left _ _)
  have hfac (k : ℕ) : (if k < 2 then (1 / 4 : ℝ) else 1) ^ 2 * (1 + t ^ 2) ≤
      ‖s - (β : ℂ) + k‖ ^ 2 := by
    rw [← normSq_eq_norm_sq, normSq_apply]
    have hre' : (s - (β : ℂ) + k).re = 1 / 2 - β + k := by simp [hsre]
    have him' : (s - (β : ℂ) + k).im = t := by simp [hsim]
    rw [hre', him', ← sq, ← sq]
    split_ifs with hk
    · interval_cases k
      · have : 1 / 4 ≤ β - 1 / 2 := by linarith [hβ.1]
        nlinarith [sq_nonneg t]
      · have : 1 / 2 ≤ 3 / 2 - β := by linarith [hβ.2]
        nlinarith [sq_nonneg t]
    · have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast Nat.le_of_not_lt hk
      have : 1 ≤ 1 / 2 - β + k := by linarith [hβ.2]
      nlinarith [sq_nonneg t]
  have hp2 : ((1 / 16 : ℝ) * (1 + t ^ 2) ^ 3) ^ 2 ≤
      (∏ k ∈ Finset.range 6, ‖s - (β : ℂ) + k‖) ^ 2 := by
    rw [← Finset.prod_pow]
    have hp_eq : ((1 / 16 : ℝ) * (1 + t ^ 2) ^ 3) ^ 2 =
        ∏ k ∈ Finset.range 6, (if k < 2 then (1 / 4 : ℝ) else 1) ^ 2 * (1 + t ^ 2) := by
      norm_num [Finset.prod_range_succ]
      ring
    exact hp_eq.trans_le (Finset.prod_le_prod₀ (fun _ _ ↦ by positivity) fun k _ ↦ hfac k)
  have hp1 : (1 / 16 : ℝ) * (1 + t ^ 2) ^ 3 ≤ ∏ k ∈ Finset.range 6, ‖s - (β : ℂ) + k‖ :=
    le_of_pow_le_pow_left₀ two_ne_zero (Finset.prod_nonneg fun _ _ ↦ norm_nonneg _) hp2
  have hdiv : 16 * max CΓ 1 * ((1 + t ^ 2) ^ 3)⁻¹ =
      max CΓ 1 / ((1 / 16 : ℝ) * (1 + t ^ 2) ^ 3) := by field_simp
  rw [hdiv, le_div_iff₀ (by positivity)]
  exact (mul_le_mul_of_nonneg_left hp1 (norm_nonneg _)).trans
    ((norm_Gamma_mul_prod_norm_le h6).trans hGC)

/-- **Uniform shifted-integral bound on `Re s = 1 / 2`.** There is one absolute constant `C > 0`
such that for all nonprincipal `χ, ψ` of positive levels `M, N` with `χ.mul ψ ≠ 1`, all
`β ∈ [3 / 4, 1)`, and all `x > 0`, the shifted `Re s = 1 / 2` integral has norm at most
`C (M N)² x^{β - 1/2}`. -/
theorem exists_norm_integral_pair_mul_Gamma_half_le :
    ∃ C : ℝ, 0 < C ∧ ∀ {M N : ℕ} [NeZero M] [NeZero N]
      (χ : DirichletCharacter ℂ M) (ψ : DirichletCharacter ℂ N),
      χ ≠ 1 → ψ ≠ 1 → χ.mul ψ ≠ 1 →
      ∀ {β : ℝ}, β ∈ Set.Ico (3 / 4) 1 → ∀ {x : ℝ}, 0 < x →
      ‖((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ t : ℝ,
        riemannZeta (1 / 2 + t * I) * χ.LFunction (1 / 2 + t * I) *
          ψ.LFunction (1 / 2 + t * I) * (χ.mul ψ).LFunction (1 / 2 + t * I) *
          ((x : ℂ) ^ (-((1 / 2 + t * I) - β)) * Gamma ((1 / 2 + t * I) - β))‖ ≤
        C * ((M : ℝ) * N) ^ 2 * x ^ (β - 1 / 2) := by
  obtain ⟨KΓ, hKΓ, hΓ⟩ := exists_norm_Gamma_half_sub_le
  set J : ℝ := ∫ t : ℝ, (1 + t ^ 2)⁻¹
  have hJ : 0 ≤ J := integral_nonneg fun t ↦ by positivity
  refine ⟨16 * KΓ * (J + 1) / Real.pi, by positivity,
    fun {M N} _ _ χ ψ hχ hψ hχψ {β} hβ {x} hx ↦ ?_⟩
  have hpoint (t : ℝ) :
      ‖riemannZeta (1 / 2 + t * I) * χ.LFunction (1 / 2 + t * I) *
        ψ.LFunction (1 / 2 + t * I) * (χ.mul ψ).LFunction (1 / 2 + t * I) *
        ((x : ℂ) ^ (-((1 / 2 + t * I) - β)) * Gamma ((1 / 2 + t * I) - β))‖ ≤
        (32 * KΓ * ((M : ℝ) * N) ^ 2 * x ^ (β - 1 / 2)) * (1 + t ^ 2)⁻¹ := by
    have hxpow : ‖(x : ℂ) ^ (-((1 / 2 + t * I) - β))‖ = x ^ (β - 1 / 2) := by
      rw [norm_cpow_eq_rpow_re_of_pos hx]; congr 1; simp
    have h1t : 0 < 1 + t ^ 2 := by positivity
    rw [norm_mul, norm_mul ((x : ℂ) ^ _), hxpow]
    calc _ ≤ (32 * ((M : ℝ) * N) ^ 2 * (1 + t ^ 2) ^ 2) *
          (x ^ (β - 1 / 2) * (KΓ * ((1 + t ^ 2) ^ 3)⁻¹)) :=
          mul_le_mul (norm_pair_half_le χ ψ hχ hψ hχψ t)
            (mul_le_mul_of_nonneg_left (hΓ hβ t) (by positivity))
            (by positivity) (by positivity)
      _ = (32 * KΓ * ((M : ℝ) * N) ^ 2 * x ^ (β - 1 / 2)) * (1 + t ^ 2)⁻¹ := by
        field_simp [h1t.ne']
  have hint := norm_integral_le_of_norm_le
    (integrable_inv_one_add_sq.const_mul (32 * KΓ * ((M : ℝ) * N) ^ 2 * x ^ (β - 1 / 2)))
    (Eventually.of_forall hpoint)
  rw [integral_const_mul] at hint
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  calc (1 / (2 * Real.pi)) * ‖∫ t : ℝ, _‖ ≤
        (1 / (2 * Real.pi)) * ((32 * KΓ * ((M : ℝ) * N) ^ 2 * x ^ (β - 1 / 2)) * J) := by gcongr
    _ ≤ (1 / (2 * Real.pi)) * ((32 * KΓ * ((M : ℝ) * N) ^ 2 * x ^ (β - 1 / 2)) * (J + 1)) := by
        gcongr; linarith
    _ = (16 * KΓ * (J + 1) / Real.pi) * ((M : ℝ) * N) ^ 2 * x ^ (β - 1 / 2) := by
        field_simp [Real.pi_ne_zero]; ring

private theorem re_LFunction_one_mul_cpow_Gamma_eq {M N : ℕ} [NeZero M] [NeZero N]
    (χ : DirichletCharacter ℂ M) (ψ : DirichletCharacter ℂ N)
    (hχq : χ.IsQuadratic) (hψq : ψ.IsQuadratic) (hχ : χ ≠ 1) (hψ : ψ ≠ 1) (hχψ : χ.mul ψ ≠ 1)
    {β x : ℝ} (hx : 0 < x) :
    (χ.LFunction 1 * ψ.LFunction 1 * (χ.mul ψ).LFunction 1 *
      ((x : ℂ) ^ (-((1 : ℂ) - β)) * Gamma ((1 : ℂ) - β))).re =
      ((χ.LFunction 1).re * (ψ.LFunction 1).re * ((χ.mul ψ).LFunction 1).re) *
        (x ^ (β - 1) * Real.Gamma (1 - β)) ∧
    0 < (χ.LFunction 1).re * (ψ.LFunction 1).re * ((χ.mul ψ).LFunction 1).re := by
  have hrc {L : ℕ} [NeZero L] (ρ : DirichletCharacter ℂ L) (hρq : ρ.IsQuadratic) (hρ : ρ ≠ 1) :
      ρ.LFunction 1 = ((ρ.LFunction 1).re : ℂ) :=
    Complex.ext rfl (by simpa using (Complex.pos_iff.mp (LFunction_apply_one_pos hρq hρ)).2.symm)
  have hsub1 : -((1 : ℂ) - (β : ℂ)) = ((β - 1 : ℝ) : ℂ) := by push_cast; ring
  have hsub2 : (1 : ℂ) - (β : ℂ) = ((1 - β : ℝ) : ℂ) := by push_cast; ring
  have hw : (x : ℂ) ^ (-((1 : ℂ) - β)) * Gamma ((1 : ℂ) - β) =
      ((x ^ (β - 1) * Real.Gamma (1 - β) : ℝ) : ℂ) := by
    rw [hsub1, hsub2, ← ofReal_cpow hx.le, Complex.Gamma_ofReal, ← ofReal_mul]
  refine ⟨?_, mul_pos (mul_pos (Complex.pos_iff.mp (LFunction_apply_one_pos hχq hχ)).1
    (Complex.pos_iff.mp (LFunction_apply_one_pos hψq hψ)).1)
    (Complex.pos_iff.mp (LFunction_apply_one_pos (isQuadratic_mul hχq hψq) hχψ)).1⟩
  rw [hrc χ hχq hχ, hrc ψ hψq hψ, hrc (χ.mul ψ) (isQuadratic_mul hχq hψq) hχψ, hw]
  push_cast; simp

private theorem inv_mul_pow_eight_estimates {C₀ : ℝ} (hC₀ : 0 < C₀) {P β : ℝ} (hP : 1 ≤ P)
    (hβ : β ∈ Set.Ico (3 / 4) 1) :
    let B : ℝ := max 1 ((2 * C₀ / Real.exp (-1)) ^ (4 : ℕ))
    let x : ℝ := (B * P ^ (8 : ℕ))⁻¹
    x ≤ 1 ∧ C₀ * P ^ 2 * x ^ (β - 1 / 2) ≤ Real.exp (-1) / 2 ∧
      B⁻¹ * P ^ (-8 * (1 - β)) ≤ x ^ (1 - β) := by
  intro B x
  have hB1 : 1 ≤ B := le_max_left _ _
  have hB0 : 0 < B := zero_lt_one.trans_le hB1
  have hP0 : 0 < P := zero_lt_one.trans_le hP
  have hx0 : 0 < x := by positivity
  have hx1 : x ≤ 1 := inv_le_one_of_one_le₀ (by
    calc (1 : ℝ) = 1 * 1 ^ (8 : ℕ) := by norm_num
      _ ≤ B * P ^ (8 : ℕ) :=
        mul_le_mul hB1 (pow_le_pow_left₀ zero_le_one hP 8) (by positivity) hB0.le)
  refine ⟨hx1, ?_, ?_⟩
  · have hpow : x ^ (β - 1 / 2) ≤ x ^ (1 / 4 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_ge hx0 hx1 (by linarith [hβ.1])
    have hq : (2 * C₀ / Real.exp (-1)) * P ^ 2 ≤ (B * P ^ (8 : ℕ)) ^ (1 / 4 : ℝ) := by
      refine le_of_pow_le_pow_left₀ (n := 4) (by norm_num) (by positivity) ?_
      rw [mul_pow, ← pow_mul, ← Real.rpow_natCast ((B * P ^ (8 : ℕ)) ^ (1 / 4 : ℝ)),
        ← Real.rpow_mul (by positivity)]
      norm_num
      exact mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
    have hx4 : x ^ (1 / 4 : ℝ) ≤ (2 * C₀ / Real.exp (-1))⁻¹ * (P ^ 2)⁻¹ := by
      dsimp only [x]
      rw [Real.inv_rpow (by positivity), ← mul_inv]
      exact inv_anti₀ (by positivity) hq
    calc C₀ * P ^ 2 * x ^ (β - 1 / 2) ≤ C₀ * P ^ 2 * x ^ (1 / 4 : ℝ) :=
          mul_le_mul_of_nonneg_left hpow (by positivity)
      _ ≤ C₀ * P ^ 2 * ((2 * C₀ / Real.exp (-1))⁻¹ * (P ^ 2)⁻¹) :=
          mul_le_mul_of_nonneg_left hx4 (by positivity)
      _ = Real.exp (-1) / 2 := by field_simp [hC₀.ne', hP0.ne']
  · have hBp : B⁻¹ ≤ B ^ (-(1 - β)) := by
      rw [← Real.rpow_neg_one]
      exact Real.rpow_le_rpow_of_exponent_le hB1 (by linarith [hβ.1])
    have hPp : (P ^ (8 : ℕ)) ^ (-(1 - β)) = P ^ (-8 * (1 - β)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hP0.le]; congr 1; push_cast; ring
    calc B⁻¹ * P ^ (-8 * (1 - β)) ≤ B ^ (-(1 - β)) * (P ^ (8 : ℕ)) ^ (-(1 - β)) := by
          rw [← hPp]; exact mul_le_mul_of_nonneg_right hBp (by positivity)
      _ = (B * P ^ (8 : ℕ)) ^ (-(1 - β)) := (Real.mul_rpow hB0.le (by positivity)).symm
      _ = x ^ (1 - β) := by rw [Real.rpow_neg (by positivity), ← Real.inv_rpow (by positivity)]

/-- **Goldfeld's residue lower bound.** There is one absolute constant `c > 0` such that for all
nonprincipal quadratic characters `χ, ψ` of positive levels `M, N` with `χ.mul ψ ≠ 1` and every
`β ∈ [3 / 4, 1)` at which `ζ(β) L(β, χ) L(β, ψ) L(β, χ.mul ψ) ≤ 0`,
`c (1 - β) (M N)^{-8 (1 - β)} ≤ Re L(1, χ) · Re L(1, ψ) · Re L(1, χ.mul ψ)`. -/
theorem exists_pos_mul_rpow_le_LFunction_one_re_mul :
    ∃ c : ℝ, 0 < c ∧ ∀ {M N : ℕ} [NeZero M] [NeZero N]
      (χ : DirichletCharacter ℂ M) (ψ : DirichletCharacter ℂ N),
      χ.IsQuadratic → ψ.IsQuadratic → χ ≠ 1 → ψ ≠ 1 → χ.mul ψ ≠ 1 →
      ∀ {β : ℝ}, β ∈ Set.Ico (3 / 4) 1 →
      riemannZeta β * χ.LFunction β * ψ.LFunction β * (χ.mul ψ).LFunction β ≤ 0 →
      c * (1 - β) * ((M : ℝ) * N) ^ (-8 * (1 - β)) ≤
        (χ.LFunction 1).re * (ψ.LFunction 1).re * ((χ.mul ψ).LFunction 1).re := by
  obtain ⟨C₀, hC₀, hhalf⟩ := exists_norm_integral_pair_mul_Gamma_half_le
  obtain ⟨C₁, hC₁⟩ := (isCompact_Icc (a := (1 : ℝ)) (b := 2)).exists_bound_of_continuousOn
    (Real.differentiableOn_Gamma_Ioi.continuousOn.mono
      fun y hy ↦ Set.mem_Ioi.mpr (by linarith [hy.1]))
  set K₁ : ℝ := max C₁ 1
  have : 0 < K₁ := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  set B : ℝ := max 1 ((2 * C₀ / Real.exp (-1)) ^ (4 : ℕ))
  have hB0 : 0 < B := zero_lt_one.trans_le (le_max_left _ _)
  refine ⟨Real.exp (-1) / (2 * B * K₁), by positivity,
    fun {M N} _ _ χ ψ hχq hψq hχ hψ hχψ {β} hβ hFβ ↦ ?_⟩
  have hMN1 : (1 : ℝ) ≤ (M : ℝ) * N := by
    have hM : (1 : ℝ) ≤ M := Nat.one_le_cast.mpr NeZero.one_le
    have hN : (1 : ℝ) ≤ N := Nat.one_le_cast.mpr NeZero.one_le
    nlinarith
  set x : ℝ := (B * ((M : ℝ) * N) ^ (8 : ℕ))⁻¹
  have hx0 : 0 < x := by positivity
  obtain ⟨hx1, herr_bound, hx_lb⟩ := inv_mul_pow_eight_estimates hC₀ hMN1 hβ
  have hexp : Real.exp (-1) ≤ Real.exp (-x) := Real.exp_le_exp.mpr (by linarith)
  have hsm := χ.exp_neg_le_re_integral_pair_mul_Gamma ψ hχq hψq (by linarith [hβ.2] : β < 2) hx0
  rw [χ.integral_pair_mul_Gamma_two_eq_of_mul_ne_one ψ hχ hψ hχψ ⟨by linarith [hβ.1], hβ.2⟩ hx0,
    add_re, add_re] at hsm
  have herr := ((re_le_norm _).trans (hhalf χ ψ hχ hψ hχψ hβ hx0)).trans herr_bound
  obtain ⟨hR_eq, hRpos⟩ := re_LFunction_one_mul_cpow_Gamma_eq χ ψ hχq hψq hχ hψ hχψ hx0 (β := β)
  set R : ℝ := (χ.LFunction 1).re * (ψ.LFunction 1).re * ((χ.mul ψ).LFunction 1).re
  have h1β : 0 < 1 - β := by linarith [hβ.2]
  have hΓ1 : Real.Gamma (1 - β) ≤ K₁ / (1 - β) := by
    have hmem : 1 - β + 1 ∈ Set.Icc (1 : ℝ) 2 := ⟨by linarith [hβ.2], by linarith [hβ.1]⟩
    rw [le_div_iff₀ h1β, mul_comm, ← Real.Gamma_add_one h1β.ne']
    exact ((le_abs_self _).trans (Real.norm_eq_abs _ ▸ hC₁ _ hmem)).trans (le_max_left _ _)
  have hres_lb : Real.exp (-1) / 2 ≤ R * (x ^ (β - 1) * (K₁ / (1 - β))) := by
    have hstep : Real.exp (-1) / 2 ≤ R * (x ^ (β - 1) * Real.Gamma (1 - β)) := by
      linarith [hexp, hsm, (Complex.nonpos_iff.mp hFβ).1, herr, hR_eq]
    exact hstep.trans (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hΓ1 (by positivity)) hRpos.le)
  have hmul := mul_le_mul_of_nonneg_right hres_lb (by positivity : 0 ≤ (1 - β) * x ^ (1 - β))
  have hrhs : R * (x ^ (β - 1) * (K₁ / (1 - β))) * ((1 - β) * x ^ (1 - β)) = K₁ * R := by
    have hcancel : x ^ (β - 1) * x ^ (1 - β) = 1 := by rw [← Real.rpow_add hx0]; norm_num
    calc R * (x ^ (β - 1) * (K₁ / (1 - β))) * ((1 - β) * x ^ (1 - β)) =
          K₁ * R * (x ^ (β - 1) * x ^ (1 - β)) * ((1 - β) / (1 - β)) := by ring
      _ = K₁ * R := by rw [hcancel, div_self h1β.ne', mul_one, mul_one]
  rw [hrhs] at hmul
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  calc Real.exp (-1) * (1 - β) * ((M : ℝ) * N) ^ (-8 * (1 - β)) =
        2 * B * ((Real.exp (-1) / 2) * (1 - β) * (B⁻¹ * ((M : ℝ) * N) ^ (-8 * (1 - β)))) := by
        field_simp [hB0.ne']
    _ ≤ 2 * B * ((Real.exp (-1) / 2) * ((1 - β) * x ^ (1 - β))) := by
        have hx_lb' : B⁻¹ * ((M : ℝ) * N) ^ (-8 * (1 - β)) ≤ x ^ (1 - β) := hx_lb
        have := mul_le_mul_of_nonneg_left hx_lb' (by positivity : 0 ≤ (Real.exp (-1) / 2) * (1 - β))
        nlinarith
    _ ≤ 2 * B * (K₁ * R) := mul_le_mul_of_nonneg_left hmul (by positivity)
    _ = R * (2 * B * K₁) := by ring

end ResidueLowerBound

end DirichletCharacter
