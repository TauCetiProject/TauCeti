/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Meromorphic.Order
public import TauCeti.NumberTheory.ArithmeticDirichletSeries.Cancellation
public import TauCeti.NumberTheory.ArithmeticDirichletSeries.Convolution.Quadratic
public import TauCeti.NumberTheory.LSeries.EntireExtension
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Meromorphic.NormalForm
import TauCeti.Analysis.Complex.HalfPlaneIdentity
import TauCeti.NumberTheory.ArithmeticDirichletSeries.EulerProduct.Analytic
import TauCeti.NumberTheory.ArithmeticDirichletSeries.EulerProduct.Restrict
import TauCeti.NumberTheory.ArithmeticDirichletSeries.EulerProduct.ThreeFourOne
import TauCeti.NumberTheory.LSeries.Landau
import TauCeti.NumberTheory.LSeries.Twist
import TauCeti.NumberTheory.NumberField.DedekindZeta

/-!
# Landau's nonvanishing theorem for quadratic ideal weights

Let `K` be a number field and `χ : TauCeti.MultiplicativeIdealWeight K` a completely multiplicative
ideal weight whose pointwise square `χ ^ 2` is trivial on its good ideals, or more generally is a
purely imaginary norm twist `I ↦ N(I) ^ (u * I)` on its good ideals. While the `3-4-1` inequality
rules out zeros of `L(χ, s)` on `Re s = 1` away from the exceptional point `s = 1 + (u / 2) * I`,
it cannot reach that point because `L(χ ^ 2, 2s - 1)` has a pole there.

This file proves Landau's nonvanishing argument for ideal weights, closing the exceptional point
and hence the entire closed half-plane `Re s ≥ 1` without assuming cancellation of partial sums:

1. For `(χ ^ 2).IsTrivialOnGood`, the Dirichlet convolution `1 * χ` has nonnegative norm
   coefficients (`TauCeti.normCoeff_convolution_one_nonneg`) and abscissa of absolute convergence
   in `[1 / 2, 1]`. By Landau's theorem on nonnegative Dirichlet series
   (`TauCeti.LSeries.abscissaOfAbsConv_le_of_differentiableOn`), any holomorphic continuation `F`
   of `ζ_K(s) L(χ, s)` to `Re s > σ₁` forces `abscissaOfAbsConv (1 * χ) ≤ σ₁`, and hence
   `1 / 2 ≤ σ₁`. On the sharp half-plane `Re s > 1 / 2`, the square lower bound
   `ζ_K(2σ) ≤ L(1 * χ, σ)` forces `(F σ).re → +∞` as `σ → (1 / 2)⁺`.
2. If `Z` continues `ζ_K` holomorphically to `{s | 1 / 2 < s.re} \ {1}` and `L` continues
   `L(χ, ·)` holomorphically to `{s | 1 / 2 < s.re}` with `L 1 = 0`, the simple pole of `Z` at `1`
   cancels the zero of `L`, producing a holomorphic continuation of `ζ_K(s) L(χ, s)` to
   `Re s > 1 / 2` and forcing `(Z σ * L σ).re → +∞` as `σ → (1 / 2)⁺`. Thus `L 1 ≠ 0` whenever
   `(Z σ * L σ).re` does not tend to `+∞` as `σ → (1 / 2)⁺` — in particular whenever `Z` and `L`
   are continuous at `1 / 2`, or holomorphic past `1 / 2`.
3. Twisting by `N(I) ^ (-(u / 2) * I)` reduces `(χ ^ 2).IsNormTwistOnGood u` to the untwisted
   case and establishes `L (1 + (u / 2) * I) ≠ 0`. Combining this with the Euler product on
   `Re s > 1` and the `3-4-1` criterion (`TauCeti.UnitaryIdealWeight.ne_zero_of_eqOn_LSeries`) on
   `Re s = 1 \ {1 + (u / 2) * I}` yields `L s ≠ 0` and `meromorphicOrderAt L s = 0` throughout
   `Re s ≥ 1`.
4. Over fields with `[K : ℚ] = 1`, the Dedekind zeta continuation
   `TauCeti.exists_differentiableOn_eq_dedekindZeta_sub` already reaches `Re s > 0`, discharging
   the `Z` hypothesis unconditionally; for any cancelling weight `χ`, `continuedLFunctionOfWeight χ`
   also reaches `Re s > 0`, yielding unconditional nonvanishing on `Re s ≥ 1`.
5. Finally, the ideal Liouville weight `TauCeti.MultiplicativeIdealWeight.liouville K` satisfies
   `λ_K ^ 2 = 1`, and its `L`-series `ζ_K(2s) / ζ_K(s)` continues holomorphically across `s = 1`
   with a zero at `s = 1`. Thus continuation across `s = 1` alone cannot rule out `L 1 = 0`:
   reaching `Re s = 1 / 2` is genuinely necessary.

## Main results

* `abscissaOfAbsConv_normCoeff_convolution_one_le_of_differentiableOn`,
  `not_hasEntireExtension_normCoeff_convolution_one`,
  `not_differentiableOn_eqOn_dedekindZeta_mul_of_lt_half`, and
  `tendsto_re_atTop_of_differentiableOn_eqOn_dedekindZeta_mul` (in
  `TauCeti.MultiplicativeIdealWeight`): Landau obstructions for holomorphic continuations of
  `ζ_K(s) L(χ, s)`.
* `ne_zero_one_of_eqOn_LSeries`, `ne_zero_one_of_continuousAt_half`,
  `ne_zero_one_of_differentiableOn_re_gt`, `ne_zero_one_of_differentiable`, and
  `meromorphicOrderAt_one_eq_zero_of_eqOn_LSeries`: Landau nonvanishing at `s = 1` when
  `(χ ^ 2).IsTrivialOnGood`.
* `ne_zero_of_isNormTwistOnGood_sq` and `ne_zero_of_isNormTwistOnGood_sq_of_continuousAt`: Landau
  nonvanishing at `s = 1 + (u / 2) * I` when `(χ ^ 2).IsNormTwistOnGood u`.
* `ne_zero_of_one_le_re_of_isNormTwistOnGood_sq`, `ne_zero_of_one_le_re_of_isTrivialOnGood_sq`,
  `ne_zero_of_one_le_re_of_isNormTwistOnGood_sq_of_continuousAt`, and
  `meromorphicOrderAt_eq_zero_of_one_le_re_of_isNormTwistOnGood_sq`: full closed half-plane
  `Re s ≥ 1` nonvanishing.
* `ne_zero_of_one_le_re_of_finrank_eq_one`, `ne_zero_one_of_finrank_eq_one`,
  `TauCeti.continuedLFunctionOfWeight_ne_zero_of_isNormTwistOnGood_sq_of_finrank_eq_one`, and
  `TauCeti.continuedLFunctionOfWeight_ne_zero_of_isTrivialOnGood_sq_of_finrank_eq_one`:
  unconditional specializations for `[K : ℚ] = 1`.
* `exists_differentiableOn_eqOn_LSeries_liouville_apply_one_eq_zero`: sharpness test showing that
  continuation across `s = 1` alone does not rule out `L 1 = 0`.

## References

* E. Landau, *Über die zu einem algebraischen Zahlkörper gehörige Zetafunction und die Ausdehnung
  der Tschebyschefschen Primzahlentheorie auf das Problem der Vertheilung der Primideale*,
  J. Reine Angew. Math. 125 (1903), 64–188.
* H. Davenport, *Multiplicative Number Theory*, Chapter 4.
* J. Neukirch, *Algebraic Number Theory*, Chapter VII, §5–§6.
* The Dirichlet-character prototype is `DirichletCharacter.LFunction_ne_zero_of_one_le_re` in
  `Mathlib/NumberTheory/LSeries/Nonvanishing.lean` (Michael Stoll and David Loeffler).
-/

public section

namespace TauCeti.MultiplicativeIdealWeight

open Complex Filter IsDedekindDomain NumberField Set
open scoped ComplexOrder NumberField Topology

variable {K : Type*} [Field K] [NumberField K]

/-- Norm-regrouped `L`-series summability on `Re s > 1` for a weight with
`(χ ^ 2).IsTrivialOnGood`. -/
private theorem LSeriesSummable_normCoeff_of_isTrivialOnGood_sq {χ : MultiplicativeIdealWeight K}
    (hχ : (χ ^ 2).IsTrivialOnGood) {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (normCoeff K χ.toIdealArithmeticFunction) s :=
  LSeriesSummable_normCoeff K <|
    summable_idealTerm_of_bounded_of_one_lt_re (C := 1)
      (fun I ↦ by simpa using norm_apply_le_one_of_isTrivialOnGood_sq hχ I) hs

/-! ### Landau obstructions for `ζ_K(s) L(χ, s)` -/

/-- **Abscissa pushdown for `1 * χ`.** If `(χ ^ 2).IsTrivialOnGood` and `F` is holomorphic on
`Re s > σ₁` agreeing with `ζ_K(s) L(χ, s)` on `Re s > 1`, then the abscissa of absolute
convergence of `L(1 * χ, ·)` is at most `σ₁`. -/
theorem abscissaOfAbsConv_normCoeff_convolution_one_le_of_differentiableOn
    {χ : MultiplicativeIdealWeight K} (hχ : (χ ^ 2).IsTrivialOnGood) {σ₁ : ℝ} {F : ℂ → ℂ}
    (hF : DifferentiableOn ℂ F {s | σ₁ < s.re})
    (hFeq : EqOn F
      (fun s ↦ dedekindZeta K s * LSeries (normCoeff K χ.toIdealArithmeticFunction) s)
      {s | 1 < s.re}) :
    LSeries.abscissaOfAbsConv
      (normCoeff K (IdealArithmeticFunction.convolution 1 χ.toIdealArithmeticFunction)) ≤ σ₁ := by
  set a : ℕ → ℂ :=
    ⇑(normCoeff K (IdealArithmeticFunction.convolution 1 χ.toIdealArithmeticFunction))
  by_cases hle : LSeries.abscissaOfAbsConv a ≤ (σ₁ : EReal)
  · exact hle
  have hlt : (σ₁ : EReal) < LSeries.abscissaOfAbsConv a := not_le.mp hle
  have htop : LSeries.abscissaOfAbsConv a ≠ ⊤ :=
    ((abscissaOfAbsConv_normCoeff_convolution_one_le_one hχ).trans_lt (EReal.coe_lt_top 1)).ne
  have hbot : LSeries.abscissaOfAbsConv a ≠ ⊥ := fun h ↦ by simp [h] at hlt
  set τ : ℝ := (LSeries.abscissaOfAbsConv a).toReal
  have habs : LSeries.abscissaOfAbsConv a = (τ : EReal) := (EReal.coe_toReal htop hbot).symm
  have hσ₁τ : σ₁ < τ := by rw [habs] at hlt; exact_mod_cast hlt
  have hLdiff : DifferentiableOn ℂ (LSeries a) {s | τ < s.re} :=
    (LSeries_differentiableOn a).mono fun s hs ↦ by
      rw [habs]
      exact_mod_cast hs
  have hFeq1 : EqOn F (LSeries a) {s | 1 < s.re} := fun s hs ↦ by
    rw [hFeq hs, LSeries_normCoeff_convolution_one_eq_dedekindZeta_mul hs
      (LSeriesSummable_normCoeff_of_isTrivialOnGood_sq hχ hs)]
  have hFeqτ : EqOn F (LSeries a) {s | τ < s.re} :=
    (hF.mono fun _ hs ↦ hσ₁τ.trans hs).eqOn_of_eqOn_re_gt hLdiff hFeq1
  exact TauCeti.LSeries.abscissaOfAbsConv_le_of_differentiableOn
    (normCoeff_convolution_one_nonneg hχ) htop hF fun s _ hs ↦
      hFeqτ (by rw [habs] at hs; exact_mod_cast hs)

/-- **No entire extension for `1 * χ`.** When `χ ^ 2` is trivial on its good ideals, the Dirichlet
series of `1 * χ` has no entire extension. -/
theorem not_hasEntireExtension_normCoeff_convolution_one {χ : MultiplicativeIdealWeight K}
    (hχ : (χ ^ 2).IsTrivialOnGood) :
    ¬ LSeries.HasEntireExtension
      (normCoeff K (IdealArithmeticFunction.convolution 1 χ.toIdealArithmeticFunction)) := by
  intro h
  have hbot := TauCeti.LSeries.abscissaOfAbsConv_eq_bot_of_hasEntireExtension
    (normCoeff_convolution_one_nonneg hχ) h
  have hhalf := half_le_abscissaOfAbsConv_normCoeff_convolution_one hχ
  rw [hbot] at hhalf
  exact not_lt_of_ge hhalf (EReal.bot_lt_coe _)

/-- **No holomorphic continuation of `ζ_K(s) L(χ, s)` past `Re s = 1 / 2`.** If `χ ^ 2` is trivial
on its good ideals and `σ₁ < 1 / 2`, no function holomorphic on `Re s > σ₁` can agree with
`ζ_K(s) L(χ, s)` on `Re s > 1`. -/
theorem not_differentiableOn_eqOn_dedekindZeta_mul_of_lt_half {χ : MultiplicativeIdealWeight K}
    (hχ : (χ ^ 2).IsTrivialOnGood) {σ₁ : ℝ} (hσ₁ : σ₁ < 1 / 2) {F : ℂ → ℂ}
    (hF : DifferentiableOn ℂ F {s | σ₁ < s.re})
    (hFeq : EqOn F
      (fun s ↦ dedekindZeta K s * LSeries (normCoeff K χ.toIdealArithmeticFunction) s)
      {s | 1 < s.re}) : False := by
  have hle := abscissaOfAbsConv_normCoeff_convolution_one_le_of_differentiableOn hχ hF hFeq
  have hge := half_le_abscissaOfAbsConv_normCoeff_convolution_one hχ
  have : ((1 / 2 : ℝ) : EReal) ≤ (σ₁ : EReal) := hge.trans hle
  exact not_lt_of_ge (by exact_mod_cast this : (1 / 2 : ℝ) ≤ σ₁) hσ₁

/-- **Sharp boundary blowup at `Re s = 1 / 2`.** If `χ ^ 2` is trivial on its good ideals and `F`
continues `ζ_K(s) L(χ, s)` holomorphically to the sharp half-plane `Re s > 1 / 2`, then
`(F σ).re → +∞` as real `σ → (1 / 2)⁺`. -/
theorem tendsto_re_atTop_of_differentiableOn_eqOn_dedekindZeta_mul
    {χ : MultiplicativeIdealWeight K} (hχ : (χ ^ 2).IsTrivialOnGood) {F : ℂ → ℂ}
    (hF : DifferentiableOn ℂ F {s | (1 / 2 : ℝ) < s.re})
    (hFeq : EqOn F
      (fun s ↦ dedekindZeta K s * LSeries (normCoeff K χ.toIdealArithmeticFunction) s)
      {s | 1 < s.re}) :
    Tendsto (fun σ : ℝ ↦ (F σ).re) (𝓝[>] (1 / 2 : ℝ)) atTop := by
  set a : ℕ → ℂ :=
    ⇑(normCoeff K (IdealArithmeticFunction.convolution 1 χ.toIdealArithmeticFunction))
  have habs_le : LSeries.abscissaOfAbsConv a ≤ ((1 / 2 : ℝ) : EReal) :=
    abscissaOfAbsConv_normCoeff_convolution_one_le_of_differentiableOn hχ hF hFeq
  have hLdiff : DifferentiableOn ℂ (LSeries a) {s | (1 / 2 : ℝ) < s.re} :=
    (LSeries_differentiableOn a).mono fun s hs ↦ habs_le.trans_lt (by exact_mod_cast hs)
  have hFeq1 : EqOn F (LSeries a) {s | 1 < s.re} := fun s hs ↦ by
    rw [hFeq hs, LSeries_normCoeff_convolution_one_eq_dedekindZeta_mul hs
      (LSeriesSummable_normCoeff_of_isTrivialOnGood_sq hχ hs)]
  have hFeqhalf : EqOn F (LSeries a) {s | (1 / 2 : ℝ) < s.re} :=
    hF.eqOn_of_eqOn_re_gt hLdiff hFeq1
  have h2 : Tendsto (fun σ : ℝ ↦ 2 * σ) (𝓝[>] (1 / 2 : ℝ)) (𝓝[>] 1) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_
      (eventually_nhdsWithin_of_forall fun σ (hσ : (1 / 2 : ℝ) < σ) ↦ by
        change 1 < 2 * σ; linarith)
    have h0 : Tendsto (fun σ : ℝ ↦ 2 * σ) (𝓝 (1 / 2 : ℝ)) (𝓝 1) := by
      simpa using (continuous_const_mul (2 : ℝ)).tendsto (1 / 2 : ℝ)
    exact h0.mono_left nhdsWithin_le_nhds
  refine Filter.tendsto_atTop_mono' _ ?_ ((tendsto_re_dedekindZeta_nhdsGT_one K).comp h2)
  filter_upwards [self_mem_nhdsWithin] with σ (hσ : (1 / 2 : ℝ) < σ)
  have hsum : LSeriesSummable a σ :=
    LSeriesSummable_of_abscissaOfAbsConv_lt_re
      (habs_le.trans_lt (by simpa using (EReal.coe_lt_coe_iff.mpr hσ)))
  have hle := dedekindZeta_two_mul_le_LSeries_convolution_one hχ hsum
  have hFσ : F σ = LSeries a σ := hFeqhalf (by simpa using hσ)
  rw [hFσ]
  exact (Complex.le_def.mp hle).1

/-! ### Pole cancellation and Landau nonvanishing at `s = 1` -/

/-- If `Z` continues `ζ_K` holomorphically to `{s | 1 / 2 < s.re} \ {1}` and `L` is holomorphic on
`{s | 1 / 2 < s.re}` with `L 1 = 0`, then `Z * L` has a removable singularity at `1`, with
limiting value `dedekindZeta_residue K * deriv L 1`. -/
private theorem differentiableOn_update_mul_of_apply_one_eq_zero {Z L : ℂ → ℂ}
    (hZ : DifferentiableOn ℂ Z ({s | (1 / 2 : ℝ) < s.re} \ {1}))
    (hZζ : EqOn Z (dedekindZeta K) {s | 1 < s.re})
    (hL : DifferentiableOn ℂ L {s | (1 / 2 : ℝ) < s.re}) (hL1 : L 1 = 0) :
    DifferentiableOn ℂ
      (Function.update (fun s ↦ Z s * L s) 1 ((dedekindZeta_residue K : ℂ) * deriv L 1))
      {s | (1 / 2 : ℝ) < s.re} := by
  classical
  set U : Set ℂ := {s | (1 / 2 : ℝ) < s.re}
  have hU : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have h1U : (1 : ℂ) ∈ U := by norm_num [U]
  set F : ℂ → ℂ :=
    Function.update (fun s ↦ Z s * L s) 1 ((dedekindZeta_residue K : ℂ) * deriv L 1)
  rw [← Complex.differentiableOn_compl_singleton_and_continuousAt_iff (hU.mem_nhds h1U)]
  refine ⟨(hZ.mul (hL.mono sdiff_subset)).congr fun s hs ↦ Function.update_of_ne hs.2 _ _, ?_⟩
  rw [continuousAt_update_same]
  have hZdiff : ∀ᶠ s in 𝓝[≠] (1 : ℂ), DifferentiableAt ℂ Z s := by
    filter_upwards [inter_mem_nhdsWithin _ (hU.mem_nhds h1U)] with s hs
    exact hZ.differentiableAt ((hU.sdiff isClosed_singleton).mem_nhds ⟨hs.2, hs.1⟩)
  have hZlim : Tendsto (fun s : ℂ ↦ (s - 1) * Z s) (𝓝[≠] 1) (𝓝 (dedekindZeta_residue K : ℂ)) :=
    tendsto_sub_one_mul_of_eqOn_dedekindZeta hZdiff hZζ
  have hLlim : Tendsto (fun s : ℂ ↦ L s / (s - 1)) (𝓝[≠] 1) (𝓝 (deriv L 1)) := by
    have hslope :=
      hasDerivAt_iff_tendsto_slope.mp (hL.differentiableAt (hU.mem_nhds h1U)).hasDerivAt
    refine hslope.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s _
    rw [slope_def_field, hL1, sub_zero]
  refine (hZlim.mul hLlim).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hne
  have hs1 : s - 1 ≠ 0 := sub_ne_zero.mpr hne
  field_simp [hs1]

omit [Field K] [NumberField K] in
/-- If two complex functions are continuous at a real point `c`, then `(f σ * g σ).re` cannot tend
to `+∞` as real `σ → c⁺`. -/
private theorem not_tendsto_re_mul_atTop_of_continuousAt {f g : ℂ → ℂ} {c : ℝ}
    (hf : ContinuousAt f (c : ℂ)) (hg : ContinuousAt g (c : ℂ)) :
    ¬ Tendsto (fun σ : ℝ ↦ (f σ * g σ).re) (𝓝[>] c) atTop := by
  have hcont : ContinuousAt (fun σ : ℝ ↦ (f σ * g σ).re) c :=
    Complex.continuous_re.continuousAt.comp
      ((hf.comp Complex.continuous_ofReal.continuousAt).mul
        (hg.comp Complex.continuous_ofReal.continuousAt))
  have hlim : Tendsto (fun σ : ℝ ↦ (f σ * g σ).re) (𝓝[>] c) (𝓝 ((f c * g c).re)) :=
    hcont.tendsto.mono_left nhdsWithin_le_nhds
  intro hat
  set y : ℝ := (f c * g c).re
  have hlt : ∀ᶠ σ : ℝ in 𝓝[>] c, (f σ * g σ).re < y + 1 :=
    hlim (Iio_mem_nhds (lt_add_one y))
  have hge : ∀ᶠ σ : ℝ in 𝓝[>] c, y + 1 ≤ (f σ * g σ).re :=
    hat (Ici_mem_atTop (y + 1))
  obtain ⟨σ, h1, h2⟩ := (hlt.and hge).exists
  linarith

/-- **Landau's nonvanishing theorem at `s = 1`, sharp boundary form.** Let `χ` be a completely
multiplicative ideal weight with `(χ ^ 2).IsTrivialOnGood`. Suppose `Z` continues `ζ_K`
holomorphically to `{s | 1 / 2 < s.re} \ {1}` and `L` continues `L(χ, ·)` holomorphically to
`{s | 1 / 2 < s.re}`. If `(Z σ * L σ).re` does not tend to `+∞` as real `σ → (1 / 2)⁺`, then
`L 1 ≠ 0`. -/
theorem ne_zero_one_of_eqOn_LSeries {χ : MultiplicativeIdealWeight K}
    (hχ : (χ ^ 2).IsTrivialOnGood) {Z L : ℂ → ℂ}
    (hZ : DifferentiableOn ℂ Z ({s | (1 / 2 : ℝ) < s.re} \ {1}))
    (hZζ : EqOn Z (dedekindZeta K) {s | 1 < s.re})
    (hL : DifferentiableOn ℂ L {s | (1 / 2 : ℝ) < s.re})
    (hLL : EqOn L (LSeries (normCoeff K χ.toIdealArithmeticFunction)) {s | 1 < s.re})
    (hnot : ¬ Tendsto (fun σ : ℝ ↦ (Z σ * L σ).re) (𝓝[>] (1 / 2 : ℝ)) atTop) :
    L 1 ≠ 0 := by
  classical
  intro hL1
  set F : ℂ → ℂ :=
    Function.update (fun s ↦ Z s * L s) 1 ((dedekindZeta_residue K : ℂ) * deriv L 1)
  have hF : DifferentiableOn ℂ F {s | (1 / 2 : ℝ) < s.re} :=
    differentiableOn_update_mul_of_apply_one_eq_zero hZ hZζ hL hL1
  have hFeq : EqOn F
      (fun s ↦ dedekindZeta K s * LSeries (normCoeff K χ.toIdealArithmeticFunction) s)
      {s | 1 < s.re} := fun s hs ↦ by
    have hne : s ≠ 1 := fun h ↦ by simp [h] at hs
    simp only [F, Function.update_of_ne hne, hZζ hs, hLL hs]
  have hblow := tendsto_re_atTop_of_differentiableOn_eqOn_dedekindZeta_mul hχ hF hFeq
  apply hnot
  refine hblow.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT (by norm_num : (1 / 2 : ℝ) < 1)] with σ hσ
  have hne : (σ : ℂ) ≠ 1 := fun h ↦ hσ.2.ne (by exact_mod_cast h)
  simp [F, Function.update_of_ne hne]

/-- **Landau's nonvanishing theorem at `s = 1`, continuous-at-`1 / 2` form.** If `Z` and `L`
continue `ζ_K` and `L(χ, ·)` holomorphically to `{s | 1 / 2 < s.re}` (with `1` punctured from `Z`)
and both are continuous at `1 / 2`, then `L 1 ≠ 0`. -/
theorem ne_zero_one_of_continuousAt_half {χ : MultiplicativeIdealWeight K}
    (hχ : (χ ^ 2).IsTrivialOnGood) {Z L : ℂ → ℂ}
    (hZ : DifferentiableOn ℂ Z ({s | (1 / 2 : ℝ) < s.re} \ {1}))
    (hZζ : EqOn Z (dedekindZeta K) {s | 1 < s.re})
    (hL : DifferentiableOn ℂ L {s | (1 / 2 : ℝ) < s.re})
    (hLL : EqOn L (LSeries (normCoeff K χ.toIdealArithmeticFunction)) {s | 1 < s.re})
    (hZhalf : ContinuousAt Z (1 / 2 : ℂ)) (hLhalf : ContinuousAt L (1 / 2 : ℂ)) :
    L 1 ≠ 0 :=
  ne_zero_one_of_eqOn_LSeries hχ hZ hZζ hL hLL
    (not_tendsto_re_mul_atTop_of_continuousAt (c := 1 / 2)
      (by simpa using hZhalf) (by simpa using hLhalf))

/-- **Landau's nonvanishing theorem at `s = 1`, open half-plane past `1 / 2`.** If `σ₁ < 1 / 2`
and `Z`, `L` continue `ζ_K` and `L(χ, ·)` holomorphically to `{s | σ₁ < s.re}` (with `1` punctured
from `Z`), then `L 1 ≠ 0`. -/
theorem ne_zero_one_of_differentiableOn_re_gt {χ : MultiplicativeIdealWeight K}
    (hχ : (χ ^ 2).IsTrivialOnGood) {σ₁ : ℝ} (hσ₁ : σ₁ < 1 / 2) {Z L : ℂ → ℂ}
    (hZ : DifferentiableOn ℂ Z ({s | σ₁ < s.re} \ {1}))
    (hZζ : EqOn Z (dedekindZeta K) {s | 1 < s.re})
    (hL : DifferentiableOn ℂ L {s | σ₁ < s.re})
    (hLL : EqOn L (LSeries (normCoeff K χ.toIdealArithmeticFunction)) {s | 1 < s.re}) :
    L 1 ≠ 0 := by
  have hopen : IsOpen {s : ℂ | σ₁ < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hhalf_mem : (1 / 2 : ℂ) ∈ {s : ℂ | σ₁ < s.re} := by simpa using hσ₁
  have hhalf_ne : (1 / 2 : ℂ) ≠ 1 := by norm_num
  have hsub : {s : ℂ | (1 / 2 : ℝ) < s.re} ⊆ {s : ℂ | σ₁ < s.re} := fun _ hs ↦ hσ₁.trans hs
  exact ne_zero_one_of_continuousAt_half hχ
    (hZ.mono (sdiff_subset_sdiff_left hsub)) hZζ (hL.mono hsub) hLL
    (hZ.differentiableAt
      ((hopen.sdiff isClosed_singleton).mem_nhds ⟨hhalf_mem, hhalf_ne⟩)).continuousAt
    (hL.differentiableAt (hopen.mem_nhds hhalf_mem)).continuousAt

/-- **Landau's nonvanishing theorem at `s = 1`, whole-plane form.** If `Z` is holomorphic away from
`1` continuing `ζ_K` and `L` is entire continuing `L(χ, ·)`, then `L 1 ≠ 0`. -/
theorem ne_zero_one_of_differentiable {χ : MultiplicativeIdealWeight K}
    (hχ : (χ ^ 2).IsTrivialOnGood) {Z L : ℂ → ℂ}
    (hZ : DifferentiableOn ℂ Z {1}ᶜ) (hZζ : EqOn Z (dedekindZeta K) {s | 1 < s.re})
    (hL : Differentiable ℂ L)
    (hLL : EqOn L (LSeries (normCoeff K χ.toIdealArithmeticFunction)) {s | 1 < s.re}) :
    L 1 ≠ 0 :=
  ne_zero_one_of_differentiableOn_re_gt hχ (σ₁ := 0) (by norm_num)
    (hZ.mono fun _ hs ↦ hs.2) hZζ hL.differentiableOn hLL

/-- **Meromorphic order at `s = 1`.** Under the hypotheses of `ne_zero_one_of_eqOn_LSeries`, the
continuation `L` has meromorphic order `0` at `s = 1`. -/
theorem meromorphicOrderAt_one_eq_zero_of_eqOn_LSeries {χ : MultiplicativeIdealWeight K}
    (hχ : (χ ^ 2).IsTrivialOnGood) {Z L : ℂ → ℂ}
    (hZ : DifferentiableOn ℂ Z ({s | (1 / 2 : ℝ) < s.re} \ {1}))
    (hZζ : EqOn Z (dedekindZeta K) {s | 1 < s.re})
    (hL : DifferentiableOn ℂ L {s | (1 / 2 : ℝ) < s.re})
    (hLL : EqOn L (LSeries (normCoeff K χ.toIdealArithmeticFunction)) {s | 1 < s.re})
    (hnot : ¬ Tendsto (fun σ : ℝ ↦ (Z σ * L σ).re) (𝓝[>] (1 / 2 : ℝ)) atTop) :
    meromorphicOrderAt L 1 = 0 := by
  have hopen : IsOpen {s : ℂ | (1 / 2 : ℝ) < s.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  have hana : AnalyticAt ℂ L 1 := hL.analyticAt (hopen.mem_nhds (by norm_num))
  exact hana.meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mpr
    (ne_zero_one_of_eqOn_LSeries hχ hZ hZζ hL hLL hnot)

/-! ### Norm-twisted Landau nonvanishing at `s = 1 + (u / 2) * I` -/

/-- **Landau's nonvanishing theorem at `s = 1 + (u / 2) * I`, sharp boundary form.** If
`(χ ^ 2).IsNormTwistOnGood u`, `Z` continues `ζ_K` holomorphically to `{s | 1 / 2 < s.re} \ {1}`,
`L` continues `L(χ, ·)` holomorphically to `{s | 1 / 2 < s.re}`, and
`(Z σ * L (σ + (u / 2) * I)).re` does not tend to `+∞` as `σ → (1 / 2)⁺`, then
`L (1 + (u / 2) * I) ≠ 0`. -/
theorem ne_zero_of_isNormTwistOnGood_sq {χ : MultiplicativeIdealWeight K} {u : ℝ}
    (hχ : (χ ^ 2).IsNormTwistOnGood u) {Z L : ℂ → ℂ}
    (hZ : DifferentiableOn ℂ Z ({s | (1 / 2 : ℝ) < s.re} \ {1}))
    (hZζ : EqOn Z (dedekindZeta K) {s | 1 < s.re})
    (hL : DifferentiableOn ℂ L {s | (1 / 2 : ℝ) < s.re})
    (hLL : EqOn L (LSeries (normCoeff K χ.toIdealArithmeticFunction)) {s | 1 < s.re})
    (hnot : ¬ Tendsto (fun σ : ℝ ↦ (Z σ * L ((σ : ℂ) + (u : ℂ) / 2 * I)).re)
      (𝓝[>] (1 / 2 : ℝ)) atTop) :
    L (1 + (u : ℂ) / 2 * I) ≠ 0 := by
  set v : ℂ := ((u / 2 : ℝ) : ℂ) * I
  have hv_eq : v = (u : ℂ) / 2 * I := by simp [v]
  have hv_re : v.re = 0 := by simp [v]
  set χ' : MultiplicativeIdealWeight K := normTwist v χ
  have hχ' : (χ' ^ 2).IsTrivialOnGood := isTrivialOnGood_sq_normTwist_of_isNormTwistOnGood_sq hχ
  set L' : ℂ → ℂ := fun s ↦ L (s + v)
  have hL' : DifferentiableOn ℂ L' {s | (1 / 2 : ℝ) < s.re} :=
    hL.comp (differentiableOn_id.add_const v) fun s hs ↦ by
      change (1 / 2 : ℝ) < (s + v).re
      simpa [hv_re] using hs
  have hL'L : EqOn L' (LSeries (normCoeff K χ'.toIdealArithmeticFunction)) {s | 1 < s.re} := by
    intro s hs
    have hcoeff : ⇑(normCoeff K χ'.toIdealArithmeticFunction) =
        fun n : ℕ ↦ normCoeff K χ.toIdealArithmeticFunction n * (n : ℂ) ^ (-v) :=
      funext (normCoeff_normTwist v χ)
    rw [hcoeff, TauCeti.LSeries.LSeries_mul_natCast_cpow_neg]
    exact hLL (by simpa [hv_re] using hs)
  have h1 : L' 1 ≠ 0 :=
    ne_zero_one_of_eqOn_LSeries hχ' hZ hZζ hL' hL'L (by simpa [L', hv_eq] using hnot)
  simpa [L', hv_eq] using h1

/-- **Landau's nonvanishing theorem at `s = 1 + (u / 2) * I`, continuous-at-`1 / 2` form.** -/
theorem ne_zero_of_isNormTwistOnGood_sq_of_continuousAt {χ : MultiplicativeIdealWeight K} {u : ℝ}
    (hχ : (χ ^ 2).IsNormTwistOnGood u) {Z L : ℂ → ℂ}
    (hZ : DifferentiableOn ℂ Z ({s | (1 / 2 : ℝ) < s.re} \ {1}))
    (hZζ : EqOn Z (dedekindZeta K) {s | 1 < s.re})
    (hL : DifferentiableOn ℂ L {s | (1 / 2 : ℝ) < s.re})
    (hLL : EqOn L (LSeries (normCoeff K χ.toIdealArithmeticFunction)) {s | 1 < s.re})
    (hZhalf : ContinuousAt Z (1 / 2 : ℂ))
    (hLhalf : ContinuousAt L (1 / 2 + (u : ℂ) / 2 * I)) :
    L (1 + (u : ℂ) / 2 * I) ≠ 0 := by
  have hLshift : ContinuousAt (fun z : ℂ ↦ L (z + (u : ℂ) / 2 * I)) (((1 / 2 : ℝ) : ℂ)) :=
    hLhalf.comp_of_eq (continuousAt_id.add continuousAt_const) (by push_cast; rfl)
  exact ne_zero_of_isNormTwistOnGood_sq hχ hZ hZζ hL hLL
    (not_tendsto_re_mul_atTop_of_continuousAt (c := 1 / 2)
      (by simpa using hZhalf) hLshift)

/-! ### Full closed half-plane `Re s ≥ 1` nonvanishing -/

/-- The `3-4-1` nonvanishing step on `Re s = 1` away from `1 + (u / 2) * I` for a weight whose
square is a purely imaginary norm twist on its good ideals. -/
private theorem ne_zero_of_re_eq_one_ne_of_isNormTwistOnGood_sq {χ : MultiplicativeIdealWeight K}
    {u : ℝ} (hχ : (χ ^ 2).IsNormTwistOnGood u) {L : ℂ → ℂ} {s : ℂ} (hs : s.re = 1)
    (hsu : s ≠ 1 + (u : ℂ) / 2 * I) (hLs : DifferentiableAt ℂ L s)
    (hLL : EqOn L (LSeries (normCoeff K χ.toIdealArithmeticFunction)) {z | 1 < z.re}) :
    L s ≠ 0 := by
  let χu : UnitaryIdealWeight K :=
    ⟨χ, fun P hP ↦
      norm_apply_eq_one_of_isNormTwistOnGood_sq hχ (Ideal.isPrimeTo_asIdeal_iff.mpr hP)⟩
  have hχu2 : (χu ^ 2).1 = χ ^ 2 := by rw [UnitaryIdealWeight.val_pow]
  obtain ⟨S, hS⟩ : ∃ S : Finset (HeightOneSpectrum (𝓞 K)),
      (χ ^ 2).badPrimes = (S : Set (HeightOneSpectrum (𝓞 K))) :=
    ⟨(χ ^ 2).finite_badPrimes.toFinset, (χ ^ 2).finite_badPrimes.coe_toFinset.symm⟩
  obtain ⟨G, hG, hGL⟩ := exists_differentiableOn_eq_LSeries_ofBadPrimes_sub K S
  set ρ : ℂ := dedekindZeta_residue K * ∏ P ∈ S, (1 - (Ideal.absNorm P.asIdeal : ℂ) ^ (-1 : ℂ))
  set w₀ : ℂ := 2 * s - 1 - (u : ℂ) * I
  have hw₀ : w₀ - 1 ≠ 0 := fun h ↦ hsu (by linear_combination h / 2)
  have hcont : ContinuousAt (fun z : ℂ ↦ G (z - (u : ℂ) * I) + ρ / (z - (u : ℂ) * I - 1))
      (2 * s - 1) := by
    have hG₀ : ContinuousAt G w₀ :=
      (hG.differentiableAt ((isOpen_lt continuous_const continuous_re).mem_nhds
        (setOf_one_le_re_subset_setOf_one_sub_one_div_finrank_lt_re K
          (show 1 ≤ w₀.re by norm_num [w₀, hs])))).continuousAt
    have hsub : ContinuousAt (fun z : ℂ ↦ z - (u : ℂ) * I) (2 * s - 1) :=
      continuousAt_id.sub continuousAt_const
    exact (hG₀.comp_of_eq hsub rfl).add
      (continuousAt_const.div (hsub.sub continuousAt_const) hw₀)
  refine χu.ne_zero_of_eqOn_LSeries hs hLs
    (by simpa only [UnitaryIdealWeight.toIdealArithmeticFunction_eq_val] using hLL) hcont
    fun z hz ↦ ?_
  have hz' : 1 < (z - (u : ℂ) * I).re := by simpa using hz
  rw [UnitaryIdealWeight.toIdealArithmeticFunction_eq_val, hχu2, hχ.LSeries_normCoeff hS,
    hGL _ hz', sub_add_cancel]

/-- **Full closed half-plane `Re s ≥ 1` nonvanishing for norm-twisted-square ideal weights.**
Combining the Euler product on `Re s > 1`, the `3-4-1` inequality on
`Re s = 1 \ {1 + (u / 2) * I}`, and Landau's theorem at `s = 1 + (u / 2) * I`, any holomorphic
continuation `L` of `L(χ, ·)` to `Re s > 1 / 2` has no zeros anywhere on `Re s ≥ 1`. -/
theorem ne_zero_of_one_le_re_of_isNormTwistOnGood_sq {χ : MultiplicativeIdealWeight K} {u : ℝ}
    (hχ : (χ ^ 2).IsNormTwistOnGood u) {Z L : ℂ → ℂ}
    (hZ : DifferentiableOn ℂ Z ({s | (1 / 2 : ℝ) < s.re} \ {1}))
    (hZζ : EqOn Z (dedekindZeta K) {s | 1 < s.re})
    (hL : DifferentiableOn ℂ L {s | (1 / 2 : ℝ) < s.re})
    (hLL : EqOn L (LSeries (normCoeff K χ.toIdealArithmeticFunction)) {s | 1 < s.re})
    (hnot : ¬ Tendsto (fun σ : ℝ ↦ (Z σ * L ((σ : ℂ) + (u : ℂ) / 2 * I)).re)
      (𝓝[>] (1 / 2 : ℝ)) atTop)
    {s : ℂ} (hs : 1 ≤ s.re) : L s ≠ 0 := by
  rcases hs.lt_or_eq with hsgt | hseq
  · rw [hLL hsgt]
    exact χ.LSeries_ne_zero_of_summable_idealTerm
      (summable_idealTerm_of_bounded_of_one_lt_re (C := 1)
        (fun I ↦ by simpa using norm_apply_le_one_of_isNormTwistOnGood_sq hχ I) hsgt)
  · by_cases hsu : s = 1 + (u : ℂ) / 2 * I
    · rw [hsu]
      exact ne_zero_of_isNormTwistOnGood_sq hχ hZ hZζ hL hLL hnot
    · have hopen : IsOpen {z : ℂ | (1 / 2 : ℝ) < z.re} :=
        isOpen_lt continuous_const Complex.continuous_re
      exact ne_zero_of_re_eq_one_ne_of_isNormTwistOnGood_sq hχ hseq.symm hsu
        (hL.differentiableAt (hopen.mem_nhds (by change (1 / 2 : ℝ) < s.re; linarith))) hLL

/-- **Full closed half-plane `Re s ≥ 1` nonvanishing for quadratic ideal weights** (`u = 0`). -/
theorem ne_zero_of_one_le_re_of_isTrivialOnGood_sq {χ : MultiplicativeIdealWeight K}
    (hχ : (χ ^ 2).IsTrivialOnGood) {Z L : ℂ → ℂ}
    (hZ : DifferentiableOn ℂ Z ({s | (1 / 2 : ℝ) < s.re} \ {1}))
    (hZζ : EqOn Z (dedekindZeta K) {s | 1 < s.re})
    (hL : DifferentiableOn ℂ L {s | (1 / 2 : ℝ) < s.re})
    (hLL : EqOn L (LSeries (normCoeff K χ.toIdealArithmeticFunction)) {s | 1 < s.re})
    (hnot : ¬ Tendsto (fun σ : ℝ ↦ (Z σ * L σ).re) (𝓝[>] (1 / 2 : ℝ)) atTop)
    {s : ℂ} (hs : 1 ≤ s.re) : L s ≠ 0 :=
  ne_zero_of_one_le_re_of_isNormTwistOnGood_sq ((isNormTwistOnGood_zero_iff _).mpr hχ)
    hZ hZζ hL hLL (by simpa using hnot) hs

/-- **Full closed half-plane `Re s ≥ 1` nonvanishing**, continuous-at-`1 / 2` form. -/
theorem ne_zero_of_one_le_re_of_isNormTwistOnGood_sq_of_continuousAt
    {χ : MultiplicativeIdealWeight K} {u : ℝ} (hχ : (χ ^ 2).IsNormTwistOnGood u) {Z L : ℂ → ℂ}
    (hZ : DifferentiableOn ℂ Z ({s | (1 / 2 : ℝ) < s.re} \ {1}))
    (hZζ : EqOn Z (dedekindZeta K) {s | 1 < s.re})
    (hL : DifferentiableOn ℂ L {s | (1 / 2 : ℝ) < s.re})
    (hLL : EqOn L (LSeries (normCoeff K χ.toIdealArithmeticFunction)) {s | 1 < s.re})
    (hZhalf : ContinuousAt Z (1 / 2 : ℂ))
    (hLhalf : ContinuousAt L (1 / 2 + (u : ℂ) / 2 * I))
    {s : ℂ} (hs : 1 ≤ s.re) : L s ≠ 0 := by
  have hLshift : ContinuousAt (fun z : ℂ ↦ L (z + (u : ℂ) / 2 * I)) (((1 / 2 : ℝ) : ℂ)) :=
    hLhalf.comp_of_eq (continuousAt_id.add continuousAt_const) (by push_cast; rfl)
  exact ne_zero_of_one_le_re_of_isNormTwistOnGood_sq hχ hZ hZζ hL hLL
    (not_tendsto_re_mul_atTop_of_continuousAt (c := 1 / 2)
      (by simpa using hZhalf) hLshift) hs

/-- **Meromorphic order zero throughout `Re s ≥ 1`.** Under the hypotheses of
`ne_zero_of_one_le_re_of_isNormTwistOnGood_sq`, `meromorphicOrderAt L s = 0` for every `s` with
`1 ≤ s.re`. -/
theorem meromorphicOrderAt_eq_zero_of_one_le_re_of_isNormTwistOnGood_sq
    {χ : MultiplicativeIdealWeight K} {u : ℝ} (hχ : (χ ^ 2).IsNormTwistOnGood u) {Z L : ℂ → ℂ}
    (hZ : DifferentiableOn ℂ Z ({s | (1 / 2 : ℝ) < s.re} \ {1}))
    (hZζ : EqOn Z (dedekindZeta K) {s | 1 < s.re})
    (hL : DifferentiableOn ℂ L {s | (1 / 2 : ℝ) < s.re})
    (hLL : EqOn L (LSeries (normCoeff K χ.toIdealArithmeticFunction)) {s | 1 < s.re})
    (hnot : ¬ Tendsto (fun σ : ℝ ↦ (Z σ * L ((σ : ℂ) + (u : ℂ) / 2 * I)).re)
      (𝓝[>] (1 / 2 : ℝ)) atTop)
    {s : ℂ} (hs : 1 ≤ s.re) : meromorphicOrderAt L s = 0 := by
  have hopen : IsOpen {z : ℂ | (1 / 2 : ℝ) < z.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  have hana : AnalyticAt ℂ L s :=
    hL.analyticAt (hopen.mem_nhds (by change (1 / 2 : ℝ) < s.re; linarith))
  exact hana.meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mpr
    (ne_zero_of_one_le_re_of_isNormTwistOnGood_sq hχ hZ hZζ hL hLL hnot hs)

/-! ### Unconditional specialization for `[K : ℚ] = 1` -/

/-- **Unconditional nonvanishing on `Re s ≥ 1` when `[K : ℚ] = 1`.** For a field of degree `1`
over `ℚ`, `TauCeti.exists_differentiableOn_eq_dedekindZeta_sub` already continues `ζ_K`
meromorphically to `Re s > 0`, discharging the `Z` hypothesis completely. -/
theorem ne_zero_of_one_le_re_of_finrank_eq_one (hK : Module.finrank ℚ K = 1)
    {χ : MultiplicativeIdealWeight K} {u : ℝ} (hχ : (χ ^ 2).IsNormTwistOnGood u) {L : ℂ → ℂ}
    (hL : DifferentiableOn ℂ L {s | (1 / 2 : ℝ) < s.re})
    (hLL : EqOn L (LSeries (normCoeff K χ.toIdealArithmeticFunction)) {s | 1 < s.re})
    (hLhalf : ContinuousAt L (1 / 2 + (u : ℂ) / 2 * I))
    {s : ℂ} (hs : 1 ≤ s.re) : L s ≠ 0 := by
  obtain ⟨G, hG, hGζ⟩ := exists_differentiableOn_eq_dedekindZeta_sub K
  have hG0 : DifferentiableOn ℂ G {z | (0 : ℝ) < z.re} := by
    simpa [hK] using hG
  set Z : ℂ → ℂ := fun z ↦ G z + (dedekindZeta_residue K : ℂ) / (z - 1)
  have hZ0 : DifferentiableOn ℂ Z ({z | (0 : ℝ) < z.re} \ {1}) :=
    (hG0.mono sdiff_subset).add
      ((differentiableOn_const _).div (differentiableOn_id.sub_const 1) fun _ hz ↦
        sub_ne_zero.mpr hz.2)
  have hopen : IsOpen ({z : ℂ | (0 : ℝ) < z.re} \ {1}) :=
    (isOpen_lt continuous_const Complex.continuous_re).sdiff isClosed_singleton
  have hZhalf : ContinuousAt Z (1 / 2 : ℂ) :=
    (hZ0.differentiableAt (hopen.mem_nhds ⟨by norm_num, by norm_num⟩)).continuousAt
  have hZ : DifferentiableOn ℂ Z ({z | (1 / 2 : ℝ) < z.re} \ {1}) :=
    hZ0.mono fun _ hz ↦ ⟨lt_trans (by norm_num : (0 : ℝ) < 1 / 2) hz.1, hz.2⟩
  have hZζ : EqOn Z (dedekindZeta K) {z | 1 < z.re} := fun z hz ↦ by
    simp only [Z, hGζ z hz, sub_add_cancel]
  exact ne_zero_of_one_le_re_of_isNormTwistOnGood_sq_of_continuousAt hχ hZ hZζ hL hLL hZhalf
    hLhalf hs

/-- **Unconditional nonvanishing at `s = 1` when `[K : ℚ] = 1` and `(χ ^ 2).IsTrivialOnGood`.** -/
theorem ne_zero_one_of_finrank_eq_one (hK : Module.finrank ℚ K = 1)
    {χ : MultiplicativeIdealWeight K} (hχ : (χ ^ 2).IsTrivialOnGood) {L : ℂ → ℂ}
    (hL : DifferentiableOn ℂ L {s | (1 / 2 : ℝ) < s.re})
    (hLL : EqOn L (LSeries (normCoeff K χ.toIdealArithmeticFunction)) {s | 1 < s.re})
    (hLhalf : ContinuousAt L (1 / 2 : ℂ)) : L 1 ≠ 0 := by
  simpa using ne_zero_of_one_le_re_of_finrank_eq_one hK
    ((isNormTwistOnGood_zero_iff _).mpr hχ) hL hLL (by simpa using hLhalf) (s := 1) (by simp)

/-- **Unconditional nonvanishing of `continuedLFunctionOfWeight` on `Re s ≥ 1` when
`[K : ℚ] = 1`.** For a degree-`1` field, cancellation continues `L(χ, ·)` holomorphically to
`Re s > 0`, discharging both continuation hypotheses unconditionally. -/
theorem _root_.TauCeti.continuedLFunctionOfWeight_ne_zero_of_isNormTwistOnGood_sq_of_finrank_eq_one
    (hK : Module.finrank ℚ K = 1) {χ : UnitaryIdealWeight K} (hχ : HasCancellation χ)
    {u : ℝ} (hχ₂ : (χ ^ 2).1.IsNormTwistOnGood u) {s : ℂ} (hs : 1 ≤ s.re) :
    continuedLFunctionOfWeight χ s ≠ 0 := by
  have hdiff : DifferentiableOn ℂ (continuedLFunctionOfWeight χ) {z | (0 : ℝ) < z.re} := by
    simpa [hK] using differentiableOn_continuedLFunctionOfWeight hχ
  have hopen : IsOpen {z : ℂ | (0 : ℝ) < z.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  exact ne_zero_of_one_le_re_of_finrank_eq_one hK hχ₂
    (hdiff.mono fun _ hz ↦ lt_trans (by norm_num : (0 : ℝ) < 1 / 2) hz)
    (fun z hz ↦ by
      rw [continuedLFunctionOfWeight_eq_LSeries χ hz,
        UnitaryIdealWeight.toIdealArithmeticFunction_eq_val])
    (hdiff.differentiableAt (hopen.mem_nhds (by norm_num))).continuousAt hs

/-- **Unconditional nonvanishing of `continuedLFunctionOfWeight` on `Re s ≥ 1` when
`[K : ℚ] = 1` and `(χ ^ 2).1.IsTrivialOnGood`.** -/
theorem _root_.TauCeti.continuedLFunctionOfWeight_ne_zero_of_isTrivialOnGood_sq_of_finrank_eq_one
    (hK : Module.finrank ℚ K = 1) {χ : UnitaryIdealWeight K} (hχ : HasCancellation χ)
    (hχ₂ : (χ ^ 2).1.IsTrivialOnGood) {s : ℂ} (hs : 1 ≤ s.re) :
    continuedLFunctionOfWeight χ s ≠ 0 :=
  continuedLFunctionOfWeight_ne_zero_of_isNormTwistOnGood_sq_of_finrank_eq_one hK hχ
    ((isNormTwistOnGood_zero_iff _).mpr hχ₂) hs

/-! ### Sharpness test: analytic continuation across `s = 1` alone does not prevent `L 1 = 0` -/

/-- **Necessity of continuation down to `Re s = 1 / 2`.** For the ideal Liouville weight
`λ_K = MultiplicativeIdealWeight.liouville K`, which satisfies `(λ_K ^ 2).IsTrivialOnGood`, the
Dirichlet series `L(λ_K, s) = ζ_K(2s) / ζ_K(s)` continues holomorphically across `s = 1` to
`Metric.ball 1 r ∪ {s | 1 < s.re}` and vanishes at `s = 1`. Thus analytic continuation across
`s = 1` alone cannot rule out `L 1 = 0`. -/
theorem exists_differentiableOn_eqOn_LSeries_liouville_apply_one_eq_zero :
    ∃ r > 0, ∃ L : ℂ → ℂ,
      DifferentiableOn ℂ L (Metric.ball (1 : ℂ) r ∪ {s | 1 < s.re}) ∧
      EqOn L (LSeries (normCoeff K (liouville K).toIdealArithmeticFunction)) {s | 1 < s.re} ∧
      L 1 = 0 := by
  obtain ⟨G, hG, hGζ⟩ := exists_differentiableOn_eq_dedekindZeta_sub K
  set U : Set ℂ := {s | 1 - 1 / (Module.finrank ℚ K : ℝ) < s.re}
  have hUopen : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have h1U : (1 : ℂ) ∈ U :=
    setOf_one_le_re_subset_setOf_one_sub_one_div_finrank_lt_re K (by simp)
  set H : ℂ → ℂ := fun s ↦ (s - 1) * G s + (dedekindZeta_residue K : ℂ)
  have hHdiff : DifferentiableOn ℂ H U :=
    ((differentiableOn_id.sub_const 1).mul hG).add (differentiableOn_const _)
  have hHeq : ∀ {s : ℂ}, 1 < s.re → H s = (s - 1) * dedekindZeta K s := fun {s} hs ↦ by
    have hne : s - 1 ≠ 0 := sub_ne_zero.mpr fun h ↦ by simp [h] at hs
    simp only [H, hGζ s hs]; field_simp [hne]; ring
  have hH1 : H 1 ≠ 0 := by
    simp only [H, sub_self, zero_mul, zero_add]
    exact_mod_cast (dedekindZeta_residue_pos K).ne'
  have hmem : U ∩ {s : ℂ | (1 / 2 : ℝ) < s.re} ∩ {s : ℂ | H s ≠ 0} ∈ 𝓝 (1 : ℂ) :=
    Filter.inter_mem (Filter.inter_mem (hUopen.mem_nhds h1U)
      ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)))
      ((hHdiff.differentiableAt (hUopen.mem_nhds h1U)).continuousAt.eventually_ne hH1)
  obtain ⟨r, hr, hball⟩ := Metric.nhds_basis_ball.mem_iff.mp hmem
  set L : ℂ → ℂ := fun s ↦ (s - 1) * dedekindZeta K (2 * s) / H s
  refine ⟨r, hr, L, ?_, ?_, by simp [L]⟩
  · intro s hs
    have hsU : s ∈ U := hs.elim (fun h ↦ (hball h).1.1) fun h ↦
      setOf_one_le_re_subset_setOf_one_sub_one_div_finrank_lt_re K (show (1 : ℝ) ≤ s.re from h.le)
    have hs2 : 1 < (2 * s).re := by
      have hhalf : (1 / 2 : ℝ) < s.re :=
        hs.elim (fun h ↦ (hball h).1.2) fun h ↦ by linarith [show (1 : ℝ) < s.re from h]
      simp only [Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, zero_mul, sub_zero]; linarith
    have hHs : H s ≠ 0 := hs.elim (fun h ↦ (hball h).2) fun h ↦ by
      rw [hHeq h]
      exact mul_ne_zero (sub_ne_zero.mpr fun hc ↦ by simp [hc] at h)
        (dedekindZeta_ne_zero_of_one_lt_re h)
    have hζ2 : DifferentiableAt ℂ (fun z : ℂ ↦ dedekindZeta K (2 * z)) s :=
      (analyticOnNhd_dedekindZeta K (2 * s) hs2).differentiableAt.comp s
        (differentiableAt_id.const_mul 2)
    exact (((differentiableAt_id.sub_const 1).mul hζ2).div
      (hHdiff.differentiableAt (hUopen.mem_nhds hsU)) hHs).differentiableWithinAt
  · intro s hs
    have hne : s - 1 ≠ 0 := sub_ne_zero.mpr fun h ↦ by simp [h] at hs
    have hζne : dedekindZeta K s ≠ 0 := dedekindZeta_ne_zero_of_one_lt_re hs
    have hconv : dedekindZeta K (2 * s) = dedekindZeta K s *
        LSeries (normCoeff K (liouville K).toIdealArithmeticFunction) s := by
      rw [← LSeries_normCoeff_convolution_one_liouville,
        LSeries_normCoeff_convolution_one_eq_dedekindZeta_mul hs
          (LSeriesSummable_normCoeff_of_isTrivialOnGood_sq (isTrivialOnGood_liouville_sq K) hs)]
    simp only [L, hHeq hs, hconv]
    field_simp [hne, hζne]

end TauCeti.MultiplicativeIdealWeight
