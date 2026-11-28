/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Meromorphic.NormalForm
public import TauCeti.NumberTheory.ArithmeticDirichletSeries.Convolution.Quadratic
public import TauCeti.NumberTheory.LSeries.EntireExtension
import Mathlib.Analysis.Complex.RemovableSingularity
import TauCeti.Analysis.Complex.HalfPlaneIdentity
import TauCeti.NumberTheory.ArithmeticDirichletSeries.Convolution.Analytic
import TauCeti.NumberTheory.ArithmeticDirichletSeries.EulerProduct.Analytic
import TauCeti.NumberTheory.ArithmeticDirichletSeries.EulerProduct.Nonvanishing
import TauCeti.NumberTheory.LSeries.Landau
import TauCeti.NumberTheory.LSeries.Twist
import TauCeti.NumberTheory.NumberField.DedekindZeta.Basic
import TauCeti.NumberTheory.NumberField.DedekindZeta.Limits

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
   case and establishes `L (1 + (u / 2) * I) ≠ 0`, provided `Z` continues `ζ_K` holomorphically to
   `{s | 1 / 2 < s.re} \ {1}`, `L` continues `L(χ, ·)` holomorphically to `{s | 1 / 2 < s.re}`,
   and `(Z σ * L (σ + (u / 2) * I)).re` does not tend to `+∞` as `σ → (1 / 2)⁺` (in particular
   when `Z` is continuous at `1 / 2` and `L` is continuous at `1 / 2 + (u / 2) * I`). Combining
   this with the Euler product on `Re s > 1` and the `3-4-1` criterion
   (`TauCeti.MultiplicativeIdealWeight.ne_zero_of_eqOn_LSeries_of_isNormTwistOnGood_sq`) on
   `Re s = 1 \ {1 + (u / 2) * I}` yields branch-minimal `L s ≠ 0` and `meromorphicOrderAt L s = 0`
   criteria throughout `Re s ≥ 1` (requiring half-plane continuation and boundary data only at
   `s = 1 + (u / 2) * I`, and local differentiability — or meromorphy and continuity — on the rest
   of `Re s = 1`).
4. Over fields where `[K : ℚ] = 1`, `TauCeti.exists_differentiableOn_eq_dedekindZeta` already
   continues `ζ_K` to `{s | 0 < s.re} \ {1}`, discharging the `Z` continuation hypothesis at
   `s = 1 + (u / 2) * I`.
   `TauCeti.NumberTheory.ArithmeticDirichletSeries.Cancellation.Nonvanishing.DegreeOne`
   instantiates `L` with `continuedLFunctionOfWeight` for weights with cancellation.

For sharpness, see `TauCeti.MultiplicativeIdealWeight.`
`exists_differentiableOn_eqOn_LSeries_liouville_and_apply_one_eq_zero`
in `TauCeti.NumberTheory.ArithmeticDirichletSeries.Convolution.Liouville.Continuation`, which
shows that local analytic continuation across `s = 1` alone does not rule out `L 1 = 0`.

## Main results

* `abscissaOfAbsConv_normCoeff_convolution_one_le_of_differentiableOn`,
  `not_hasEntireExtension_normCoeff_convolution_one`,
  `not_differentiableOn_eqOn_dedekindZeta_mul_of_lt_half`, and
  `tendsto_re_atTop_of_differentiableOn_eqOn_dedekindZeta_mul` (in
  `TauCeti.MultiplicativeIdealWeight`): Landau obstructions for holomorphic continuations of
  `ζ_K(s) L(χ, s)`.
* `apply_one_ne_zero_of_eqOn_LSeries`, `apply_one_ne_zero_of_continuousAt_half`, and
  `apply_one_ne_zero_of_differentiableOn_re_gt`: Landau nonvanishing at `s = 1` when
  `(χ ^ 2).IsTrivialOnGood`.
* `apply_one_add_div_two_mul_I_ne_zero_of_isNormTwistOnGood_sq` and
  `apply_one_add_div_two_mul_I_ne_zero_of_isNormTwistOnGood_sq_of_continuousAt`: Landau
  nonvanishing at `s = 1 + (u / 2) * I` when `(χ ^ 2).IsNormTwistOnGood u`.
* `ne_zero_of_one_le_re_of_isNormTwistOnGood_sq`, `ne_zero_of_one_le_re_of_isTrivialOnGood_sq`,
  `ne_zero_of_one_le_re_of_isNormTwistOnGood_sq_of_continuousAt`, and
  `meromorphicOrderAt_eq_zero_of_one_le_re_of_isNormTwistOnGood_sq`: branch-minimal closed
  half-plane `Re s ≥ 1` nonvanishing and order-zero criteria.
* `ne_zero_of_one_le_re_of_finrank_eq_one`: degree-`1` specialization discharging the `ζ_K`
  continuation hypothesis `Z` at `s = 1 + (u / 2) * I`.

## References

* E. Landau, *Über die zu einem algebraischen Zahlkörper gehörige Zetafunction und die Ausdehnung
  der Tschebyschefschen Primzahlentheorie auf das Problem der Vertheilung der Primideale*,
  J. Reine Angew. Math. 125 (1903), 64–188.
* H. Davenport, *Multiplicative Number Theory*, Chapter 4.
* J. Neukirch, *Algebraic Number Theory*, Chapter VII, §5–§6.
* The Dirichlet-character prototype is `DirichletCharacter.LFunction_ne_zero_of_one_le_re` in
  `Mathlib/NumberTheory/LSeries/Nonvanishing.lean` (Michael Stoll, David Loeffler, and
  Terence Tao).
-/

public section

namespace TauCeti.MultiplicativeIdealWeight

open Complex Filter IsDedekindDomain NumberField Set
open scoped ComplexOrder NumberField Topology

variable {K : Type*} [Field K] [NumberField K]

/-! ### Landau obstructions for `ζ_K(s) L(χ, s)` -/

/-- Any continuation `F` of `ζ_K(s) L(χ, s)` holomorphic on `Re s > τ` with `abscissaOfAbsConv ≤ τ`
agrees with `L(1 * χ, s)` throughout `Re s > τ`. -/
private theorem eqOn_LSeries_convolution_one_of_eqOn_dedekindZeta_mul
    {χ : MultiplicativeIdealWeight K} (hχ : (χ ^ 2).IsTrivialOnGood) {τ : ℝ} {F : ℂ → ℂ}
    (hF : DifferentiableOn ℂ F {s | τ < s.re})
    (hFeq : EqOn F
      (fun s ↦ dedekindZeta K s * LSeries (normCoeff K χ.toIdealArithmeticFunction) s)
      {s | 1 < s.re})
    (habs : LSeries.abscissaOfAbsConv
      (normCoeff K (IdealArithmeticFunction.convolution 1 χ.toIdealArithmeticFunction)) ≤
        (τ : EReal)) :
    EqOn F
      (LSeries (normCoeff K (IdealArithmeticFunction.convolution 1 χ.toIdealArithmeticFunction)))
      {s | τ < s.re} := by
  set a : ℕ → ℂ :=
    ⇑(normCoeff K (IdealArithmeticFunction.convolution 1 χ.toIdealArithmeticFunction))
  have hLdiff : DifferentiableOn ℂ (LSeries a) {s | τ < s.re} :=
    (LSeries_differentiableOn a).mono fun _ hs ↦
      habs.trans_lt (by simpa only [mem_ofPred_eq] using EReal.coe_lt_coe_iff.mpr hs)
  have hFeq1 : EqOn F (LSeries a) {s | 1 < s.re} := fun s hs ↦ by
    rw [hFeq hs, LSeries_normCoeff_convolution_one_eq_dedekindZeta_mul hs
      (LSeriesSummable_normCoeff_of_isTrivialOnGood_sq hχ hs)]
  exact hF.eqOn_of_eqOn_re_gt hLdiff hFeq1

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
  have hFeqτ := eqOn_LSeries_convolution_one_of_eqOn_dedekindZeta_mul hχ
    (hF.mono fun _ hs ↦ hσ₁τ.trans hs) hFeq habs.le
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
  have hFeqhalf := eqOn_LSeries_convolution_one_of_eqOn_dedekindZeta_mul hχ hF hFeq habs_le
  have h2 : Tendsto (fun σ : ℝ ↦ 2 * σ) (𝓝[>] (1 / 2 : ℝ)) (𝓝[>] 1) := by
    simpa [mul_one_div_cancel (two_ne_zero : (2 : ℝ) ≠ 0)] using
      Filter.TendstoNhdsWithinIoi.const_mul (by norm_num : (0 : ℝ) < 2)
        (tendsto_id : Tendsto id (𝓝[>] (1 / 2 : ℝ)) (𝓝[>] (1 / 2 : ℝ)))
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

/-- Points with `1 ≤ s.re` lie in the open half-plane `1 / 2 < s.re`. -/
private theorem mem_half_lt_re_of_one_le_re {s : ℂ} (hs : 1 ≤ s.re) :
    s ∈ {z : ℂ | (1 / 2 : ℝ) < z.re} := by
  simp only [mem_ofPred_eq]
  linarith

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
  rw [← Complex.differentiableOn_compl_singleton_and_continuousAt_iff (hU.mem_nhds h1U)]
  refine ⟨(hZ.mul (hL.mono sdiff_subset)).congr fun s hs ↦ Function.update_of_ne hs.2 _ _, ?_⟩
  rw [continuousAt_update_same]
  have hZdiff : ∀ᶠ s in 𝓝[≠] (1 : ℂ), DifferentiableAt ℂ Z s := by
    filter_upwards [inter_mem_nhdsWithin _ (hU.mem_nhds h1U)] with s hs
    exact hZ.differentiableAt ((hU.sdiff isClosed_singleton).mem_nhds ⟨hs.2, hs.1⟩)
  have hZlim : Tendsto (fun s : ℂ ↦ (s - 1) * Z s) (𝓝[≠] 1) (𝓝 (dedekindZeta_residue K : ℂ)) :=
    tendsto_sub_one_mul_of_eventuallyEq_dedekindZeta hZdiff hZζ.eventuallyEq_nhdsWithin
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

/-- **Landau's nonvanishing theorem at `s = 1`, sharp boundary form.** Let `χ` be a completely
multiplicative ideal weight with `(χ ^ 2).IsTrivialOnGood`. Suppose `Z` continues `ζ_K`
holomorphically to `{s | 1 / 2 < s.re} \ {1}` and `L` continues `L(χ, ·)` holomorphically to
`{s | 1 / 2 < s.re}`. If `(Z σ * L σ).re` does not tend to `+∞` as real `σ → (1 / 2)⁺`, then
`L 1 ≠ 0`. -/
theorem apply_one_ne_zero_of_eqOn_LSeries {χ : MultiplicativeIdealWeight K}
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

/-- If `Z` is continuous at `1 / 2` and `L` is continuous at `1 / 2 + v`, then
`(Z σ * L (σ + v)).re` does not tend to `+∞` as real `σ → (1 / 2)⁺`. -/
private theorem not_tendsto_re_mul_add_atTop_of_continuousAt {Z L : ℂ → ℂ} {v : ℂ}
    (hZhalf : ContinuousAt Z (1 / 2 : ℂ)) (hLhalf : ContinuousAt L (1 / 2 + v)) :
    ¬ Tendsto (fun σ : ℝ ↦ (Z σ * L ((σ : ℂ) + v)).re) (𝓝[>] (1 / 2 : ℝ)) atTop :=
  not_tendsto_atTop_of_tendsto_nhds <|
    (continuous_re.continuousAt.comp
      ((hZhalf.comp_of_eq continuous_ofReal.continuousAt (by norm_num)).mul
        (hLhalf.comp_of_eq (continuous_ofReal.continuousAt.add_const v) (by norm_num)))
      ).tendsto.mono_left nhdsWithin_le_nhds

/-- **Landau's nonvanishing theorem at `s = 1`, continuous-at-`1 / 2` form.** When
`(χ ^ 2).IsTrivialOnGood`, if `Z` and `L` continue `ζ_K` and `L(χ, ·)` holomorphically to
`{s | 1 / 2 < s.re}` (with `1` punctured from `Z`) and both are continuous at `1 / 2`, then
`L 1 ≠ 0`. -/
theorem apply_one_ne_zero_of_continuousAt_half {χ : MultiplicativeIdealWeight K}
    (hχ : (χ ^ 2).IsTrivialOnGood) {Z L : ℂ → ℂ}
    (hZ : DifferentiableOn ℂ Z ({s | (1 / 2 : ℝ) < s.re} \ {1}))
    (hZζ : EqOn Z (dedekindZeta K) {s | 1 < s.re})
    (hL : DifferentiableOn ℂ L {s | (1 / 2 : ℝ) < s.re})
    (hLL : EqOn L (LSeries (normCoeff K χ.toIdealArithmeticFunction)) {s | 1 < s.re})
    (hZhalf : ContinuousAt Z (1 / 2 : ℂ)) (hLhalf : ContinuousAt L (1 / 2 : ℂ)) :
    L 1 ≠ 0 :=
  apply_one_ne_zero_of_eqOn_LSeries hχ hZ hZζ hL hLL <| by
    simpa using not_tendsto_re_mul_add_atTop_of_continuousAt (v := 0) hZhalf (by simpa using hLhalf)

/-- **Landau's nonvanishing theorem at `s = 1`, open half-plane past `1 / 2`.** When
`(χ ^ 2).IsTrivialOnGood`, if `σ₁ < 1 / 2` and `Z`, `L` continue `ζ_K` and `L(χ, ·)`
holomorphically to `{s | σ₁ < s.re}` (with `1` punctured from `Z`), then `L 1 ≠ 0`. -/
theorem apply_one_ne_zero_of_differentiableOn_re_gt {χ : MultiplicativeIdealWeight K}
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
  exact apply_one_ne_zero_of_continuousAt_half hχ
    (hZ.mono (sdiff_subset_sdiff_left hsub)) hZζ (hL.mono hsub) hLL
    (hZ.differentiableAt
      ((hopen.sdiff isClosed_singleton).mem_nhds ⟨hhalf_mem, hhalf_ne⟩)).continuousAt
    (hL.differentiableAt (hopen.mem_nhds hhalf_mem)).continuousAt

/-! ### Norm-twisted Landau nonvanishing at `s = 1 + (u / 2) * I` -/

/-- **Landau's nonvanishing theorem at `s = 1 + (u / 2) * I`, sharp boundary form.** If
`(χ ^ 2).IsNormTwistOnGood u`, `Z` continues `ζ_K` holomorphically to `{s | 1 / 2 < s.re} \ {1}`,
`L` continues `L(χ, ·)` holomorphically to `{s | 1 / 2 < s.re}`, and
`(Z σ * L (σ + (u / 2) * I)).re` does not tend to `+∞` as `σ → (1 / 2)⁺`, then
`L (1 + (u / 2) * I) ≠ 0`. -/
theorem apply_one_add_div_two_mul_I_ne_zero_of_isNormTwistOnGood_sq
    {χ : MultiplicativeIdealWeight K} {u : ℝ} (hχ : (χ ^ 2).IsNormTwistOnGood u) {Z L : ℂ → ℂ}
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
      simp only [mem_ofPred_eq, add_re, hv_re, add_zero]
      exact hs
  have hL'L : EqOn L' (LSeries (normCoeff K χ'.toIdealArithmeticFunction)) {s | 1 < s.re} := by
    intro s hs
    have hcoeff : ⇑(normCoeff K χ'.toIdealArithmeticFunction) =
        fun n : ℕ ↦ normCoeff K χ.toIdealArithmeticFunction n * (n : ℂ) ^ (-v) :=
      funext (normCoeff_normTwist v χ)
    rw [hcoeff, TauCeti.LSeries.LSeries_mul_natCast_cpow_neg]
    exact hLL (by simpa [hv_re] using hs)
  have h1 : L' 1 ≠ 0 :=
    apply_one_ne_zero_of_eqOn_LSeries hχ' hZ hZζ hL' hL'L (by simpa [L', hv_eq] using hnot)
  simpa [L', hv_eq] using h1

/-- **Landau's nonvanishing theorem at `s = 1 + (u / 2) * I`, continuous-at-`1 / 2` form.** -/
theorem apply_one_add_div_two_mul_I_ne_zero_of_isNormTwistOnGood_sq_of_continuousAt
    {χ : MultiplicativeIdealWeight K} {u : ℝ} (hχ : (χ ^ 2).IsNormTwistOnGood u) {Z L : ℂ → ℂ}
    (hZ : DifferentiableOn ℂ Z ({s | (1 / 2 : ℝ) < s.re} \ {1}))
    (hZζ : EqOn Z (dedekindZeta K) {s | 1 < s.re})
    (hL : DifferentiableOn ℂ L {s | (1 / 2 : ℝ) < s.re})
    (hLL : EqOn L (LSeries (normCoeff K χ.toIdealArithmeticFunction)) {s | 1 < s.re})
    (hZhalf : ContinuousAt Z (1 / 2 : ℂ))
    (hLhalf : ContinuousAt L (1 / 2 + (u : ℂ) / 2 * I)) :
    L (1 + (u : ℂ) / 2 * I) ≠ 0 :=
  apply_one_add_div_two_mul_I_ne_zero_of_isNormTwistOnGood_sq hχ hZ hZζ hL hLL
    (not_tendsto_re_mul_add_atTop_of_continuousAt hZhalf hLhalf)

/-! ### Full closed half-plane `Re s ≥ 1` nonvanishing -/

/-- **Full closed half-plane `Re s ≥ 1` nonvanishing for norm-twisted-square ideal weights.**
Combining the Euler product on `Re s > 1`, the `3-4-1` inequality on
`Re s = 1 \ {1 + (u / 2) * I}`, and Landau's theorem at `s = 1 + (u / 2) * I` with branch-minimal
hypotheses: series agreement on `Re z > 1` suffices on `Re s > 1`, differentiability of `L` at `s`
suffices on `Re s = 1 \ {1 + (u / 2) * I}`, and half-plane continuations of `ζ_K` and `L` together
with the boundary condition are required only at `s = 1 + (u / 2) * I`. See
`ne_zero_of_one_le_re_of_isNormTwistOnGood_sq_of_continuousAt` for the special case where `Z` and
`L` are continuous at `1 / 2` and `1 / 2 + (u / 2) * I`. -/
theorem ne_zero_of_one_le_re_of_isNormTwistOnGood_sq {χ : MultiplicativeIdealWeight K} {u : ℝ}
    (hχ : (χ ^ 2).IsNormTwistOnGood u) {L : ℂ → ℂ}
    (hLL : EqOn L (LSeries (normCoeff K χ.toIdealArithmeticFunction)) {z | 1 < z.re})
    {s : ℂ} (hs : 1 ≤ s.re)
    (hLs : s.re = 1 → s ≠ 1 + (u : ℂ) / 2 * I → DifferentiableAt ℂ L s)
    (hlandau : s = 1 + (u : ℂ) / 2 * I → ∃ Z : ℂ → ℂ,
      DifferentiableOn ℂ Z ({z | (1 / 2 : ℝ) < z.re} \ {1}) ∧
      EqOn Z (dedekindZeta K) {z | 1 < z.re} ∧
      DifferentiableOn ℂ L {z | (1 / 2 : ℝ) < z.re} ∧
      ¬ Tendsto (fun σ : ℝ ↦ (Z σ * L ((σ : ℂ) + (u : ℂ) / 2 * I)).re)
        (𝓝[>] (1 / 2 : ℝ)) atTop) :
    L s ≠ 0 := by
  rcases hs.lt_or_eq with hsgt | hseq
  · rw [hLL hsgt]
    exact χ.LSeries_ne_zero_of_summable_idealTerm <| by
      simpa [UnitaryIdealWeight.toIdealArithmeticFunction_eq_val] using
        summable_idealTerm_of_unitary_of_one_lt_re (unitaryOfIsNormTwistOnGoodSq hχ) hsgt
  · by_cases hsu : s = 1 + (u : ℂ) / 2 * I
    · obtain ⟨Z, hZ, hZζ, hL, hnot⟩ := hlandau hsu
      rw [hsu]
      exact apply_one_add_div_two_mul_I_ne_zero_of_isNormTwistOnGood_sq
        hχ hZ hZζ hL hLL hnot
    · exact χ.ne_zero_of_eqOn_LSeries_of_isNormTwistOnGood_sq hχ hseq.symm hsu
        (hLs hseq.symm hsu) hLL

/-- **Full closed half-plane `Re s ≥ 1` nonvanishing for quadratic ideal weights** (`u = 0`), with
branch-minimal hypotheses matching `ne_zero_of_one_le_re_of_isNormTwistOnGood_sq`. See
`ne_zero_of_one_le_re_of_isNormTwistOnGood_sq_of_continuousAt` at `u = 0` for the continuity
sufficient condition. -/
theorem ne_zero_of_one_le_re_of_isTrivialOnGood_sq {χ : MultiplicativeIdealWeight K}
    (hχ : (χ ^ 2).IsTrivialOnGood) {L : ℂ → ℂ}
    (hLL : EqOn L (LSeries (normCoeff K χ.toIdealArithmeticFunction)) {z | 1 < z.re})
    {s : ℂ} (hs : 1 ≤ s.re)
    (hLs : s.re = 1 → s ≠ 1 → DifferentiableAt ℂ L s)
    (hlandau : s = 1 → ∃ Z : ℂ → ℂ,
      DifferentiableOn ℂ Z ({z | (1 / 2 : ℝ) < z.re} \ {1}) ∧
      EqOn Z (dedekindZeta K) {z | 1 < z.re} ∧
      DifferentiableOn ℂ L {z | (1 / 2 : ℝ) < z.re} ∧
      ¬ Tendsto (fun σ : ℝ ↦ (Z σ * L σ).re) (𝓝[>] (1 / 2 : ℝ)) atTop) :
    L s ≠ 0 :=
  ne_zero_of_one_le_re_of_isNormTwistOnGood_sq ((isNormTwistOnGood_zero_iff _).mpr hχ)
    hLL hs (by simpa using hLs) (by simpa using hlandau)

/-- **Full closed half-plane `Re s ≥ 1` nonvanishing**, continuous-at-`1 / 2` form. -/
theorem ne_zero_of_one_le_re_of_isNormTwistOnGood_sq_of_continuousAt
    {χ : MultiplicativeIdealWeight K} {u : ℝ} (hχ : (χ ^ 2).IsNormTwistOnGood u) {L : ℂ → ℂ}
    (hLL : EqOn L (LSeries (normCoeff K χ.toIdealArithmeticFunction)) {z | 1 < z.re})
    {s : ℂ} (hs : 1 ≤ s.re)
    (hLs : s.re = 1 → s ≠ 1 + (u : ℂ) / 2 * I → DifferentiableAt ℂ L s)
    (hlandau : s = 1 + (u : ℂ) / 2 * I → ∃ Z : ℂ → ℂ,
      DifferentiableOn ℂ Z ({z | (1 / 2 : ℝ) < z.re} \ {1}) ∧
      EqOn Z (dedekindZeta K) {z | 1 < z.re} ∧
      ContinuousAt Z (1 / 2 : ℂ) ∧
      DifferentiableOn ℂ L {z | (1 / 2 : ℝ) < z.re} ∧
      ContinuousAt L (1 / 2 + (u : ℂ) / 2 * I)) :
    L s ≠ 0 :=
  ne_zero_of_one_le_re_of_isNormTwistOnGood_sq hχ hLL hs hLs fun hsu ↦ by
    obtain ⟨Z, hZ, hZζ, hZhalf, hL, hLhalf⟩ := hlandau hsu
    exact ⟨Z, hZ, hZζ, hL, not_tendsto_re_mul_add_atTop_of_continuousAt hZhalf hLhalf⟩

/-- **Meromorphic order zero throughout `Re s ≥ 1`.** Under the branch-minimal hypotheses of
`ne_zero_of_one_le_re_of_isNormTwistOnGood_sq`, requiring meromorphy and continuity at the
nonexceptional boundary point `s` (`s.re = 1` with `s ≠ 1 + (u / 2) * I`),
`meromorphicOrderAt L s = 0` for every `s` with `1 ≤ s.re`. -/
theorem meromorphicOrderAt_eq_zero_of_one_le_re_of_isNormTwistOnGood_sq
    {χ : MultiplicativeIdealWeight K} {u : ℝ} (hχ : (χ ^ 2).IsNormTwistOnGood u) {L : ℂ → ℂ}
    (hLL : EqOn L (LSeries (normCoeff K χ.toIdealArithmeticFunction)) {z | 1 < z.re})
    {s : ℂ} (hs : 1 ≤ s.re)
    (hLM : s.re = 1 → s ≠ 1 + (u : ℂ) / 2 * I → MeromorphicAt L s)
    (hLs : s.re = 1 → s ≠ 1 + (u : ℂ) / 2 * I → ContinuousAt L s)
    (hlandau : s = 1 + (u : ℂ) / 2 * I → ∃ Z : ℂ → ℂ,
      DifferentiableOn ℂ Z ({z | (1 / 2 : ℝ) < z.re} \ {1}) ∧
      EqOn Z (dedekindZeta K) {z | 1 < z.re} ∧
      DifferentiableOn ℂ L {z | (1 / 2 : ℝ) < z.re} ∧
      ¬ Tendsto (fun σ : ℝ ↦ (Z σ * L ((σ : ℂ) + (u : ℂ) / 2 * I)).re)
        (𝓝[>] (1 / 2 : ℝ)) atTop) :
    meromorphicOrderAt L s = 0 := by
  have hne : L s ≠ 0 :=
    ne_zero_of_one_le_re_of_isNormTwistOnGood_sq hχ hLL hs
      (fun hseq hsu ↦ ((hLM hseq hsu).analyticAt (hLs hseq hsu)).differentiableAt) hlandau
  have hnf : MeromorphicNFAt L s := by
    rcases hs.lt_or_eq with hsgt | hseq
    · exact ((unitaryOfIsNormTwistOnGoodSq hχ).analyticAt_of_eqOn_LSeries (by
        simpa [UnitaryIdealWeight.toIdealArithmeticFunction_eq_val] using hLL) hsgt).meromorphicNFAt
    · by_cases hsu : s = 1 + (u : ℂ) / 2 * I
      · obtain ⟨_, _, _, hL, _⟩ := hlandau hsu
        have hopen : IsOpen {z : ℂ | (1 / 2 : ℝ) < z.re} :=
          isOpen_lt continuous_const Complex.continuous_re
        exact (hL.analyticAt
          (hopen.mem_nhds (mem_half_lt_re_of_one_le_re hs))).meromorphicNFAt
      · exact ((hLM hseq.symm hsu).analyticAt (hLs hseq.symm hsu)).meromorphicNFAt
  exact hnf.meromorphicOrderAt_eq_zero_iff.mpr hne

/-! ### Degree-`1` specialization discharging the Dedekind zeta continuation -/

/-- **Nonvanishing on `Re s ≥ 1` when `[K : ℚ] = 1` at the exceptional point.** When
`s = 1 + (u / 2) * I` and `[K : ℚ] = 1`, `TauCeti.exists_differentiableOn_eq_dedekindZeta` already
continues `ζ_K` holomorphically to `{s | 0 < s.re} \ {1}`, discharging the `Z` hypothesis of
`ne_zero_of_one_le_re_of_isNormTwistOnGood_sq_of_continuousAt`; the pointwise differentiability on
`Re s = 1 \ {1 + (u / 2) * I}` and half-plane continuation/continuity hypotheses on `L` at
`s = 1 + (u / 2) * I` remain explicit. -/
theorem ne_zero_of_one_le_re_of_finrank_eq_one
    {χ : MultiplicativeIdealWeight K} {u : ℝ} (hχ : (χ ^ 2).IsNormTwistOnGood u) {L : ℂ → ℂ}
    (hLL : EqOn L (LSeries (normCoeff K χ.toIdealArithmeticFunction)) {z | 1 < z.re})
    {s : ℂ} (hs : 1 ≤ s.re)
    (hLs : s.re = 1 → s ≠ 1 + (u : ℂ) / 2 * I → DifferentiableAt ℂ L s)
    (hlandau : s = 1 + (u : ℂ) / 2 * I →
      DifferentiableOn ℂ L {z | (1 / 2 : ℝ) < z.re} ∧
      ContinuousAt L (1 / 2 + (u : ℂ) / 2 * I))
    (hK : s = 1 + (u : ℂ) / 2 * I → Module.finrank ℚ K = 1) :
    L s ≠ 0 := by
  refine ne_zero_of_one_le_re_of_isNormTwistOnGood_sq_of_continuousAt hχ hLL hs hLs fun hsu ↦ ?_
  obtain ⟨hL, hLhalf⟩ := hlandau hsu
  obtain ⟨Z, hZ0, hZζ⟩ := exists_differentiableOn_eq_dedekindZeta K
  have hZ0' : DifferentiableOn ℂ Z ({z | (0 : ℝ) < z.re} \ {1}) := by
    simpa [hK hsu] using hZ0
  have hopen : IsOpen ({z : ℂ | (0 : ℝ) < z.re} \ {1}) :=
    (isOpen_lt continuous_const Complex.continuous_re).sdiff isClosed_singleton
  have hZhalf : ContinuousAt Z (1 / 2 : ℂ) :=
    (hZ0'.differentiableAt (hopen.mem_nhds ⟨by norm_num, by norm_num⟩)).continuousAt
  have hZ : DifferentiableOn ℂ Z ({z | (1 / 2 : ℝ) < z.re} \ {1}) :=
    hZ0'.mono fun _ hz ↦ ⟨lt_trans (by norm_num : (0 : ℝ) < 1 / 2) hz.1, hz.2⟩
  exact ⟨Z, hZ, hZζ, hZhalf, hL, hLhalf⟩

end TauCeti.MultiplicativeIdealWeight
