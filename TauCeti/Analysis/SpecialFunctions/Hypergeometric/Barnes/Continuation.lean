/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.RegularizedHypergeometric
public import TauCeti.Analysis.SpecialFunctions.Hypergeometric.EulerIntegral.Basic
public import TauCeti.Analysis.SpecialFunctions.Hypergeometric.Barnes.Analyticity
import Mathlib.Analysis.Analytic.Uniqueness
import TauCeti.Analysis.Complex.RealIdentity
import TauCeti.Analysis.SpecialFunctions.Gamma.Order
import TauCeti.Analysis.SpecialFunctions.RegularizedHypergeometric.Basic

/-!
# Mellin–Barnes continuation of Euler's integral and the Gauss hypergeometric function

This module defines the normalized Mellin–Barnes analytic continuations on the cut plane
`-z ∈ Complex.slitPlane`:
* `Complex.mellinBarnesRegularizedGaussHGFun a b c z =
  (Γ(a) Γ(b))⁻¹ * mellinBarnesIntegral a b c z`, extending `Complex.regularizedGaussHGFun`
  (`𝐅(a, b; c; z)`) to all `a, b ∉ -ℕ`, arbitrary `c : ℂ`, and `-z ∈ Complex.slitPlane`;
* `Complex.mellinBarnesOrdinaryHypergeometric a b c z =
  (Γ(c) / (Γ(a) Γ(b))) * mellinBarnesIntegral a b c z`, extending `ordinaryHypergeometric`
  (`₂F₁(a, b; c; z)`) to all `a, b, c ∉ -ℕ` and `-z ∈ Complex.slitPlane`.

It proves joint four-variable holomorphy on their respective parameter domains and establishes the
overlap identities with Euler's normalized integral `Complex.eulerIntegral` (for `0 < Re b < Re c`)
and with the hypergeometric power series on `‖z‖ < 1` (DLMF 15.6.6), including negative real
parameters and integer differences `a - b ∈ ℤ`.

For `0 < Re a` and `0 < Re b < Re c`, `Complex.eulerIntegral_eq_hypergeometricMellinBarnes` already
identifies `eulerIntegral a b c z` with `(Γ(a) Γ(b))⁻¹ * hypergeometricMellinBarnes a b c z σ`
at any admissible negative abscissa `σ < 0` on `-z ∈ Complex.slitPlane`. Combining this with joint
holomorphy of `mellinBarnesIntegral` (`Complex.analyticOnNhd_mellinBarnesIntegral`),
`eulerIntegral` (`Complex.analyticOnNhd_eulerIntegral`), and `regularizedGaussHGFun`
(`AnalyticAt.regularizedGaussHGFun`), together with `Complex.regularizedGaussHGFun_eq_eulerIntegral`
and identity continuation on `{w : ℂ | ∀ k : ℕ, w ≠ -k}` from `0 < Re w`, extends the
representation to general parameters.

## Main results

* `Complex.mellinBarnesRegularizedGaussHGFun`, `Complex.mellinBarnesRegularizedGaussHGFun_def`,
  `Complex.mellinBarnesRegularizedGaussHGFun_neg_natCast_left`,
  `Complex.mellinBarnesRegularizedGaussHGFun_neg_natCast_right`,
  `Complex.mellinBarnesRegularizedGaussHGFun_symm`,
  `Complex.mellinBarnesRegularizedGaussHGFun_eq_hypergeometricMellinBarnes`,
  `Complex.analyticOnNhd_mellinBarnesRegularizedGaussHGFun`,
  `AnalyticAt.mellinBarnesRegularizedGaussHGFun`: normalized regularized Mellin–Barnes continuation,
  totalized values at excluded upper parameters, and joint cut-plane holomorphy for `a, b ∉ -ℕ`,
  arbitrary `c : ℂ`, `-z ∈ Complex.slitPlane`.
* `Complex.mellinBarnesOrdinaryHypergeometric`, `Complex.mellinBarnesOrdinaryHypergeometric_def`,
  `Complex.mellinBarnesOrdinaryHypergeometric_neg_natCast_left`,
  `Complex.mellinBarnesOrdinaryHypergeometric_neg_natCast_right`,
  `Complex.mellinBarnesOrdinaryHypergeometric_neg_natCast_lower`,
  `Complex.mellinBarnesOrdinaryHypergeometric_eq_Gamma_mul`,
  `Complex.mellinBarnesOrdinaryHypergeometric_symm`,
  `Complex.mellinBarnesOrdinaryHypergeometric_eq_hypergeometricMellinBarnes`,
  `Complex.analyticOnNhd_mellinBarnesOrdinaryHypergeometric`,
  `AnalyticAt.mellinBarnesOrdinaryHypergeometric`: ordinary Mellin–Barnes continuation, totalized
  values at excluded parameters, and joint cut-plane holomorphy for `a, b, c ∉ -ℕ`,
  `-z ∈ Complex.slitPlane`.
* `Complex.eulerIntegral_eq_mellinBarnesRegularizedGaussHGFun`,
  `Complex.eulerIntegral_eq_hypergeometricMellinBarnes_of_ne_neg_natCast`: overlap with Euler's
  integral for `0 < Re b < Re c`, `a ∉ -ℕ`, and `-z ∈ Complex.slitPlane`.
* `Complex.regularizedGaussHGFun_eq_mellinBarnesRegularizedGaussHGFun`,
  `Complex.regularizedGaussHGFun_eq_hypergeometricMellinBarnes`,
  `Complex.eqOn_mellinBarnesRegularizedGaussHGFun_of_analyticOnNhd`: DLMF 15.6.6 overlap and
  cut-plane uniqueness for `regularizedGaussHGFun` across `a, b ∉ -ℕ`, arbitrary `c : ℂ`, and
  `-z ∈ slitPlane`.
* `Complex.ordinaryHypergeometric_eq_mellinBarnesOrdinaryHypergeometric`,
  `Complex.ordinaryHypergeometric_eq_hypergeometricMellinBarnes`,
  `Complex.eqOn_mellinBarnesOrdinaryHypergeometric_of_analyticOnNhd`: DLMF 15.6.6 overlap and
  cut-plane uniqueness for `ordinaryHypergeometric` (`₂F₁`) across `a, b, c ∉ -ℕ` and
  `-z ∈ slitPlane`.

## References

* NIST Digital Library of Mathematical Functions, §15.6(ii), equation 15.6.6.
* E. T. Whittaker and G. N. Watson, *A Course of Modern Analysis*, §14.5.
* F. W. J. Olver, *Asymptotics and Special Functions*, Chapter 5.
-/

public section

noncomputable section

open Complex Filter MeasureTheory Metric Set
open scoped Real Topology

namespace Complex

private theorem eulerIntegral_mul_Gamma_eq_mellinBarnesIntegral {a b c z : ℂ}
    (ha : ∀ k : ℕ, a ≠ -k) (hb : 0 < b.re) (hbc : b.re < c.re) (hz : -z ∈ slitPlane) :
    Gamma a * Gamma b * eulerIntegral a b c z = mellinBarnesIntegral a b c z := by
  have hb_ne := ne_neg_natCast_of_re_pos hb
  have hstep1 {a' : ℂ} (ha' : 0 < a'.re) :
      Gamma a' * Gamma b * eulerIntegral a' b c z = mellinBarnesIntegral a' b c z := by
    obtain ⟨σ, hσ, haσ, hbσ, hm⟩ :=
      exists_mellinBarnesIntegral_eq_hypergeometricMellinBarnes a' b c z
    rw [hm, eulerIntegral_eq_hypergeometricMellinBarnes ha' hb hbc hz hσ haσ hbσ,
      mul_inv_cancel_left₀ (mul_ne_zero (Gamma_ne_zero_of_re_pos ha') (Gamma_ne_zero_of_re_pos hb))]
  refine AnalyticOnNhd.eqOn_forall_ne_neg_natCast_of_re_pos ?_ ?_ (fun hw => hstep1 hw) ha
  · exact fun w hw => ((analyticAt_Gamma hw).mul analyticAt_const).mul
      ((analyticOnNhd_eulerIntegral hb hbc (w, z)
        (by simpa [sub_eq_add_neg] using
          TauCeti.ofReal_add_mem_slitPlane hz zero_le_one)).comp_of_eq
        ((by fun_prop : Differentiable ℂ fun x : ℂ => (x, z)).analyticAt w) rfl)
  · exact fun w hw => analyticAt_id.mellinBarnesIntegral analyticAt_const analyticAt_const
      analyticAt_const hw hb_ne hz

/-! ### Section 1: Normalized cut-plane continuations and holomorphy -/

/-- **Mellin–Barnes analytic continuation of the regularized Gauss hypergeometric function
`𝐅(a, b; c; z)`** to the cut plane `-z ∈ Complex.slitPlane`, defined as
`(Γ(a) Γ(b))⁻¹ * mellinBarnesIntegral a b c z`. On the domain `a, b ∉ -ℕ`, arbitrary `c : ℂ`,
`-z ∈ slitPlane`, this function is jointly analytic in `(a, b, c, z)`, agrees with
`regularizedGaussHGFun a b c z` on `‖z‖ < 1`, and agrees with `eulerIntegral a b c z` for
`0 < Re b < Re c`. -/
def mellinBarnesRegularizedGaussHGFun (a b c z : ℂ) : ℂ :=
  (Gamma a * Gamma b)⁻¹ * mellinBarnesIntegral a b c z

/-- Defining formula for `mellinBarnesRegularizedGaussHGFun`. -/
theorem mellinBarnesRegularizedGaussHGFun_def (a b c z : ℂ) :
    mellinBarnesRegularizedGaussHGFun a b c z =
      (Gamma a * Gamma b)⁻¹ * mellinBarnesIntegral a b c z := (rfl)

/-- Totalized value of `mellinBarnesRegularizedGaussHGFun` when the first upper parameter is a
nonpositive integer `-n` (so `(Γ(-n))⁻¹ = 0`). -/
@[simp]
theorem mellinBarnesRegularizedGaussHGFun_neg_natCast_left (n : ℕ) (b c z : ℂ) :
    mellinBarnesRegularizedGaussHGFun (-n) b c z = 0 := by
  simp [mellinBarnesRegularizedGaussHGFun_def, Gamma_neg_nat_eq_zero]

/-- Totalized value of `mellinBarnesRegularizedGaussHGFun` when the first upper parameter is `0`
(so `(Γ(0))⁻¹ = 0`). -/
@[simp]
theorem mellinBarnesRegularizedGaussHGFun_zero_left (b c z : ℂ) :
    mellinBarnesRegularizedGaussHGFun 0 b c z = 0 := by
  simp [mellinBarnesRegularizedGaussHGFun_def]

/-- Totalized value of `mellinBarnesRegularizedGaussHGFun` when the second upper parameter is a
nonpositive integer `-n` (so `(Γ(-n))⁻¹ = 0`). -/
@[simp]
theorem mellinBarnesRegularizedGaussHGFun_neg_natCast_right (a : ℂ) (n : ℕ) (c z : ℂ) :
    mellinBarnesRegularizedGaussHGFun a (-n) c z = 0 := by
  simp [mellinBarnesRegularizedGaussHGFun_def, Gamma_neg_nat_eq_zero]

/-- Totalized value of `mellinBarnesRegularizedGaussHGFun` when the second upper parameter is `0`
(so `(Γ(0))⁻¹ = 0`). -/
@[simp]
theorem mellinBarnesRegularizedGaussHGFun_zero_right (a c z : ℂ) :
    mellinBarnesRegularizedGaussHGFun a 0 c z = 0 := by
  simp [mellinBarnesRegularizedGaussHGFun_def]

/-- Symmetry of `mellinBarnesRegularizedGaussHGFun` in the upper parameters `a` and `b`. -/
theorem mellinBarnesRegularizedGaussHGFun_symm (a b c z : ℂ) :
    mellinBarnesRegularizedGaussHGFun a b c z = mellinBarnesRegularizedGaussHGFun b a c z := by
  simp only [mellinBarnesRegularizedGaussHGFun_def, mul_comm (Gamma a), mellinBarnesIntegral_symm]

/-- Separating-contour formula for `mellinBarnesRegularizedGaussHGFun` at any admissible
negative abscissa `σ < 0`. -/
theorem mellinBarnesRegularizedGaussHGFun_eq_hypergeometricMellinBarnes (a b c z : ℂ)
    {σ : ℝ} (hσ : σ < 0) (haσ : ∀ k : ℕ, a.re + σ ≠ -k) (hbσ : ∀ k : ℕ, b.re + σ ≠ -k)
    (hz : -z ∈ slitPlane) :
    mellinBarnesRegularizedGaussHGFun a b c z =
      (Gamma a * Gamma b)⁻¹ * hypergeometricMellinBarnes a b c z σ := by
  rw [mellinBarnesRegularizedGaussHGFun_def,
    mellinBarnesIntegral_eq_hypergeometricMellinBarnes c hσ haσ hbσ hz]

/-- **Joint four-variable holomorphy of `mellinBarnesRegularizedGaussHGFun`** on the cut plane
`-z ∈ slitPlane` for `a, b ∉ -ℕ` and arbitrary `c : ℂ`, including resonant integer differences
`a - b ∈ ℤ`. -/
theorem analyticOnNhd_mellinBarnesRegularizedGaussHGFun :
    AnalyticOnNhd ℂ
      (fun p : ℂ × ℂ × ℂ × ℂ => mellinBarnesRegularizedGaussHGFun p.1 p.2.1 p.2.2.1 p.2.2.2)
      {p | (∀ k : ℕ, p.1 ≠ -k) ∧ (∀ k : ℕ, p.2.1 ≠ -k) ∧ -p.2.2.2 ∈ slitPlane} := by
  intro p hp
  have hdef :
      (fun q : ℂ × ℂ × ℂ × ℂ =>
        mellinBarnesRegularizedGaussHGFun q.1 q.2.1 q.2.2.1 q.2.2.2) =
      fun q => (Gamma q.1)⁻¹ * (Gamma q.2.1)⁻¹ *
        mellinBarnesIntegral q.1 q.2.1 q.2.2.1 q.2.2.2 := by
    ext q
    rw [mellinBarnesRegularizedGaussHGFun_def, mul_inv]
  rw [hdef]
  have hp1 : AnalyticAt ℂ (fun q : ℂ × ℂ × ℂ × ℂ => q.1) p := analyticAt_fst
  have hp2 : AnalyticAt ℂ (fun q : ℂ × ℂ × ℂ × ℂ => q.2.1) p := analyticAt_fst.comp analyticAt_snd
  have hinv1 : AnalyticAt ℂ (fun s : ℂ => (Gamma s)⁻¹) p.1 := by
    simpa only [one_div] using differentiable_one_div_Gamma.analyticAt p.1
  have hinv2 : AnalyticAt ℂ (fun s : ℂ => (Gamma s)⁻¹) p.2.1 := by
    simpa only [one_div] using differentiable_one_div_Gamma.analyticAt p.2.1
  have ha_an : AnalyticAt ℂ (fun q : ℂ × ℂ × ℂ × ℂ => (Gamma q.1)⁻¹) p :=
    hinv1.comp_of_eq hp1 rfl
  have hb_an : AnalyticAt ℂ (fun q : ℂ × ℂ × ℂ × ℂ => (Gamma q.2.1)⁻¹) p :=
    hinv2.comp_of_eq hp2 rfl
  exact (ha_an.mul hb_an).mul (analyticOnNhd_mellinBarnesIntegral p hp)

/-- `Complex.mellinBarnesRegularizedGaussHGFun` composed with four analytic functions is analytic
wherever `fa x, fb x ∉ -ℕ` and `-fz x ∈ slitPlane`. -/
theorem _root_.AnalyticAt.mellinBarnesRegularizedGaussHGFun {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {fa fb fc fz : E → ℂ} {x : E}
    (hfa : AnalyticAt ℂ fa x) (hfb : AnalyticAt ℂ fb x) (hfc : AnalyticAt ℂ fc x)
    (hfz : AnalyticAt ℂ fz x) (ha : ∀ k : ℕ, fa x ≠ -k) (hb : ∀ k : ℕ, fb x ≠ -k)
    (hz : -fz x ∈ Complex.slitPlane) :
    AnalyticAt ℂ
      (fun w => Complex.mellinBarnesRegularizedGaussHGFun (fa w) (fb w) (fc w) (fz w)) x :=
  (Complex.analyticOnNhd_mellinBarnesRegularizedGaussHGFun (fa x, fb x, fc x, fz x)
    ⟨ha, hb, hz⟩).comp_of_eq (hfa.prod (hfb.prod (hfc.prod hfz))) rfl

/-- **Mellin–Barnes analytic continuation of the ordinary Gauss hypergeometric function
`₂F₁(a, b; c; z)`** to the cut plane `-z ∈ Complex.slitPlane`, defined as
`Γ(c) / (Γ(a) Γ(b)) * mellinBarnesIntegral a b c z`. On the domain `a, b, c ∉ -ℕ`,
`-z ∈ slitPlane`, this function is jointly analytic in `(a, b, c, z)` and agrees with
`ordinaryHypergeometric a b c z` on `‖z‖ < 1`. -/
def mellinBarnesOrdinaryHypergeometric (a b c z : ℂ) : ℂ :=
  Gamma c / (Gamma a * Gamma b) * mellinBarnesIntegral a b c z

/-- Defining formula for `mellinBarnesOrdinaryHypergeometric`. -/
theorem mellinBarnesOrdinaryHypergeometric_def (a b c z : ℂ) :
    mellinBarnesOrdinaryHypergeometric a b c z =
      Gamma c / (Gamma a * Gamma b) * mellinBarnesIntegral a b c z := (rfl)

/-- Totalized value of `mellinBarnesOrdinaryHypergeometric` when the first upper parameter is a
nonpositive integer `-n` (so `(Γ(-n))⁻¹ = 0`). -/
@[simp]
theorem mellinBarnesOrdinaryHypergeometric_neg_natCast_left (n : ℕ) (b c z : ℂ) :
    mellinBarnesOrdinaryHypergeometric (-n) b c z = 0 := by
  simp [mellinBarnesOrdinaryHypergeometric_def, Gamma_neg_nat_eq_zero]

/-- Totalized value of `mellinBarnesOrdinaryHypergeometric` when the first upper parameter is `0`
(so `(Γ(0))⁻¹ = 0`). -/
@[simp]
theorem mellinBarnesOrdinaryHypergeometric_zero_left (b c z : ℂ) :
    mellinBarnesOrdinaryHypergeometric 0 b c z = 0 := by
  simp [mellinBarnesOrdinaryHypergeometric_def]

/-- Totalized value of `mellinBarnesOrdinaryHypergeometric` when the second upper parameter is a
nonpositive integer `-n` (so `(Γ(-n))⁻¹ = 0`). -/
@[simp]
theorem mellinBarnesOrdinaryHypergeometric_neg_natCast_right (a : ℂ) (n : ℕ) (c z : ℂ) :
    mellinBarnesOrdinaryHypergeometric a (-n) c z = 0 := by
  simp [mellinBarnesOrdinaryHypergeometric_def, Gamma_neg_nat_eq_zero]

/-- Totalized value of `mellinBarnesOrdinaryHypergeometric` when the second upper parameter is `0`
(so `(Γ(0))⁻¹ = 0`). -/
@[simp]
theorem mellinBarnesOrdinaryHypergeometric_zero_right (a c z : ℂ) :
    mellinBarnesOrdinaryHypergeometric a 0 c z = 0 := by
  simp [mellinBarnesOrdinaryHypergeometric_def]

/-- Totalized value of `mellinBarnesOrdinaryHypergeometric` when the lower parameter is a
nonpositive integer `-n` (so `Γ(-n) = 0`). -/
@[simp]
theorem mellinBarnesOrdinaryHypergeometric_neg_natCast_lower (a b : ℂ) (n : ℕ) (z : ℂ) :
    mellinBarnesOrdinaryHypergeometric a b (-n) z = 0 := by
  simp [mellinBarnesOrdinaryHypergeometric_def, Gamma_neg_nat_eq_zero]

/-- Totalized value of `mellinBarnesOrdinaryHypergeometric` when the lower parameter is `0`
(so `Γ(0) = 0`). -/
@[simp]
theorem mellinBarnesOrdinaryHypergeometric_zero_lower (a b z : ℂ) :
    mellinBarnesOrdinaryHypergeometric a b 0 z = 0 := by
  simp [mellinBarnesOrdinaryHypergeometric_def]

/-- Relation between `mellinBarnesOrdinaryHypergeometric` and
`mellinBarnesRegularizedGaussHGFun`. -/
theorem mellinBarnesOrdinaryHypergeometric_eq_Gamma_mul (a b c z : ℂ) :
    mellinBarnesOrdinaryHypergeometric a b c z =
      Gamma c * mellinBarnesRegularizedGaussHGFun a b c z := by
  rw [mellinBarnesOrdinaryHypergeometric_def, mellinBarnesRegularizedGaussHGFun_def,
    div_eq_mul_inv]
  ring

/-- Symmetry of `mellinBarnesOrdinaryHypergeometric` in the upper parameters `a` and `b`. -/
theorem mellinBarnesOrdinaryHypergeometric_symm (a b c z : ℂ) :
    mellinBarnesOrdinaryHypergeometric a b c z =
      mellinBarnesOrdinaryHypergeometric b a c z := by
  simp only [mellinBarnesOrdinaryHypergeometric_eq_Gamma_mul,
    mellinBarnesRegularizedGaussHGFun_symm]

/-- Separating-contour formula for `mellinBarnesOrdinaryHypergeometric` at any admissible
negative abscissa `σ < 0`. -/
theorem mellinBarnesOrdinaryHypergeometric_eq_hypergeometricMellinBarnes (a b c z : ℂ)
    {σ : ℝ} (hσ : σ < 0) (haσ : ∀ k : ℕ, a.re + σ ≠ -k) (hbσ : ∀ k : ℕ, b.re + σ ≠ -k)
    (hz : -z ∈ slitPlane) :
    mellinBarnesOrdinaryHypergeometric a b c z =
      Gamma c / (Gamma a * Gamma b) * hypergeometricMellinBarnes a b c z σ := by
  rw [mellinBarnesOrdinaryHypergeometric_def,
    mellinBarnesIntegral_eq_hypergeometricMellinBarnes c hσ haσ hbσ hz]

/-- **Joint four-variable holomorphy of `mellinBarnesOrdinaryHypergeometric`** on the cut plane
`-z ∈ slitPlane` for `a, b, c ∉ -ℕ`, including resonant integer differences `a - b ∈ ℤ`. -/
theorem analyticOnNhd_mellinBarnesOrdinaryHypergeometric :
    AnalyticOnNhd ℂ
      (fun p : ℂ × ℂ × ℂ × ℂ => mellinBarnesOrdinaryHypergeometric p.1 p.2.1 p.2.2.1 p.2.2.2)
      {p | (∀ k : ℕ, p.1 ≠ -k) ∧ (∀ k : ℕ, p.2.1 ≠ -k) ∧ (∀ k : ℕ, p.2.2.1 ≠ -k) ∧
        -p.2.2.2 ∈ slitPlane} := by
  rintro p ⟨ha, hb, hc, hz⟩
  have hdef :
      (fun q : ℂ × ℂ × ℂ × ℂ =>
        mellinBarnesOrdinaryHypergeometric q.1 q.2.1 q.2.2.1 q.2.2.2) =
      fun q => Gamma q.2.2.1 * mellinBarnesRegularizedGaussHGFun q.1 q.2.1 q.2.2.1 q.2.2.2 := by
    ext q
    exact mellinBarnesOrdinaryHypergeometric_eq_Gamma_mul q.1 q.2.1 q.2.2.1 q.2.2.2
  rw [hdef]
  have hp3 : AnalyticAt ℂ (fun q : ℂ × ℂ × ℂ × ℂ => q.2.2.1) p :=
    analyticAt_fst.comp (analyticAt_snd.comp analyticAt_snd)
  have hc_an : AnalyticAt ℂ (fun q : ℂ × ℂ × ℂ × ℂ => Gamma q.2.2.1) p :=
    (analyticAt_Gamma hc).comp_of_eq hp3 rfl
  exact hc_an.mul (analyticOnNhd_mellinBarnesRegularizedGaussHGFun p ⟨ha, hb, hz⟩)

/-- `Complex.mellinBarnesOrdinaryHypergeometric` composed with four analytic functions is analytic
wherever `fa x, fb x, fc x ∉ -ℕ` and `-fz x ∈ slitPlane`. -/
theorem _root_.AnalyticAt.mellinBarnesOrdinaryHypergeometric {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {fa fb fc fz : E → ℂ} {x : E}
    (hfa : AnalyticAt ℂ fa x) (hfb : AnalyticAt ℂ fb x) (hfc : AnalyticAt ℂ fc x)
    (hfz : AnalyticAt ℂ fz x) (ha : ∀ k : ℕ, fa x ≠ -k) (hb : ∀ k : ℕ, fb x ≠ -k)
    (hc : ∀ k : ℕ, fc x ≠ -k) (hz : -fz x ∈ Complex.slitPlane) :
    AnalyticAt ℂ
      (fun w => Complex.mellinBarnesOrdinaryHypergeometric (fa w) (fb w) (fc w) (fz w)) x :=
  (Complex.analyticOnNhd_mellinBarnesOrdinaryHypergeometric (fa x, fb x, fc x, fz x)
    ⟨ha, hb, hc, hz⟩).comp_of_eq (hfa.prod (hfb.prod (hfc.prod hfz))) rfl

/-! ### Section 2: Overlap lemmas with Euler's integral and hypergeometric series -/

/-- **Overlap with Euler's integral.** For `0 < Re b < Re c`, `a ∉ -ℕ`, and `-z ∈ slitPlane`,
Euler's normalized integral equals `mellinBarnesRegularizedGaussHGFun a b c z`. -/
theorem eulerIntegral_eq_mellinBarnesRegularizedGaussHGFun {a b c z : ℂ} (ha : ∀ k : ℕ, a ≠ -k)
    (hb : 0 < b.re) (hbc : b.re < c.re) (hz : -z ∈ slitPlane) :
    eulerIntegral a b c z = mellinBarnesRegularizedGaussHGFun a b c z := by
  rw [mellinBarnesRegularizedGaussHGFun_def,
    ← eulerIntegral_mul_Gamma_eq_mellinBarnesIntegral ha hb hbc hz,
    inv_mul_cancel_left₀ (mul_ne_zero (Gamma_ne_zero ha) (Gamma_ne_zero_of_re_pos hb))]

/-- **Separating-contour Mellin–Barnes representation of Euler's integral.** For `0 < Re b < Re c`,
`a ∉ -ℕ`, `-z ∈ slitPlane`, and any admissible abscissa `σ < 0` avoiding `-Re a - ℕ` and
`-Re b - ℕ`, Euler's normalized integral equals `(Γ(a) Γ(b))⁻¹` times
`hypergeometricMellinBarnes a b c z σ`. -/
theorem eulerIntegral_eq_hypergeometricMellinBarnes_of_ne_neg_natCast {a b c z : ℂ} {σ : ℝ}
    (ha : ∀ k : ℕ, a ≠ -k) (hb : 0 < b.re) (hbc : b.re < c.re) (hσ : σ < 0)
    (haσ : ∀ k : ℕ, a.re + σ ≠ -k) (hbσ : ∀ k : ℕ, b.re + σ ≠ -k) (hz : -z ∈ slitPlane) :
    eulerIntegral a b c z = (Gamma a * Gamma b)⁻¹ * hypergeometricMellinBarnes a b c z σ := by
  rw [eulerIntegral_eq_mellinBarnesRegularizedGaussHGFun ha hb hbc hz,
    mellinBarnesRegularizedGaussHGFun_eq_hypergeometricMellinBarnes a b c z hσ haσ hbσ hz]

private theorem regularizedGaussHGFun_mul_Gamma_eq_mellinBarnesIntegral {a b : ℂ} (c : ℂ) {z : ℂ}
    (ha : ∀ k : ℕ, a ≠ -k) (hb : ∀ k : ℕ, b ≠ -k) (hz_norm : ‖z‖ < 1)
    (hz_slit : -z ∈ slitPlane) :
    Gamma a * Gamma b * regularizedGaussHGFun a b c z = mellinBarnesIntegral a b c z := by
  have hstep_c {b' : ℂ} (hb' : 0 < b'.re) :
      Gamma a * Gamma b' * regularizedGaussHGFun a b' c z = mellinBarnesIntegral a b' c z := by
    have hfc : AnalyticOnNhd ℂ (fun w => Gamma a * Gamma b' * regularizedGaussHGFun a b' w z)
        univ := fun _ _ => analyticAt_const.mul
      (analyticAt_const.regularizedGaussHGFun analyticAt_const analyticAt_id analyticAt_const
        hz_norm)
    have hgc : AnalyticOnNhd ℂ (fun w => mellinBarnesIntegral a b' w z) univ := fun _ _ =>
      analyticAt_const.mellinBarnesIntegral analyticAt_const analyticAt_id analyticAt_const
        ha (ne_neg_natCast_of_re_pos hb') hz_slit
    have hevc : (fun w => Gamma a * Gamma b' * regularizedGaussHGFun a b' w z) =ᶠ[𝓝 (b' + 1)]
        (fun w => mellinBarnesIntegral a b' w z) := by
      filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds
        (by simp : b'.re < (b' + 1).re)] with w hw
      rw [regularizedGaussHGFun_eq_eulerIntegral a hb' hw hz_norm]
      exact eulerIntegral_mul_Gamma_eq_mellinBarnesIntegral ha hb' hw hz_slit
    exact congrFun (hfc.eq_of_eventuallyEq hgc hevc) c
  refine AnalyticOnNhd.eqOn_forall_ne_neg_natCast_of_re_pos ?_ ?_ hstep_c hb
  · exact fun w hw => (analyticAt_const.mul (analyticAt_Gamma hw)).mul
      (analyticAt_const.regularizedGaussHGFun analyticAt_id analyticAt_const analyticAt_const
        hz_norm)
  · exact fun w hw => analyticAt_const.mellinBarnesIntegral analyticAt_id analyticAt_const
      analyticAt_const ha hw hz_slit

/-- **Overlap with the regularized Gauss hypergeometric series (DLMF 15.6.6).** For all
`a, b ∉ -ℕ`, arbitrary `c : ℂ`, `‖z‖ < 1`, and `-z ∈ slitPlane`, `regularizedGaussHGFun a b c z`
agrees with `mellinBarnesRegularizedGaussHGFun a b c z`. -/
theorem regularizedGaussHGFun_eq_mellinBarnesRegularizedGaussHGFun {a b : ℂ} (c : ℂ) {z : ℂ}
    (ha : ∀ k : ℕ, a ≠ -k) (hb : ∀ k : ℕ, b ≠ -k) (hz_norm : ‖z‖ < 1)
    (hz_slit : -z ∈ slitPlane) :
    regularizedGaussHGFun a b c z = mellinBarnesRegularizedGaussHGFun a b c z := by
  rw [mellinBarnesRegularizedGaussHGFun_def,
    ← regularizedGaussHGFun_mul_Gamma_eq_mellinBarnesIntegral c ha hb hz_norm hz_slit,
    inv_mul_cancel_left₀ (mul_ne_zero (Gamma_ne_zero ha) (Gamma_ne_zero hb))]

/-- **Separating-contour Mellin–Barnes representation of `regularizedGaussHGFun` (DLMF 15.6.6)**
at any admissible abscissa `σ < 0` avoiding `-Re a - ℕ` and `-Re b - ℕ`, giving
`𝐅(a, b; c; z) = (Γ(a) Γ(b))⁻¹ * hypergeometricMellinBarnes a b c z σ` for all `a, b ∉ -ℕ`,
arbitrary `c : ℂ`, `‖z‖ < 1`, and `-z ∈ slitPlane`. -/
theorem regularizedGaussHGFun_eq_hypergeometricMellinBarnes {a b : ℂ} (c : ℂ) {z : ℂ} {σ : ℝ}
    (ha : ∀ k : ℕ, a ≠ -k) (hb : ∀ k : ℕ, b ≠ -k) (hσ : σ < 0)
    (haσ : ∀ k : ℕ, a.re + σ ≠ -k) (hbσ : ∀ k : ℕ, b.re + σ ≠ -k)
    (hz_norm : ‖z‖ < 1) (hz_slit : -z ∈ slitPlane) :
    regularizedGaussHGFun a b c z =
      (Gamma a * Gamma b)⁻¹ * hypergeometricMellinBarnes a b c z σ := by
  rw [regularizedGaussHGFun_eq_mellinBarnesRegularizedGaussHGFun c ha hb hz_norm hz_slit,
    mellinBarnesRegularizedGaussHGFun_eq_hypergeometricMellinBarnes a b c z hσ haσ hbσ hz_slit]

/-- **Uniqueness of the Mellin–Barnes continuation for `regularizedGaussHGFun` on the cut
plane.** Any function holomorphic on `{z : ℂ | -z ∈ slitPlane}` that agrees with
`regularizedGaussHGFun a b c` on `{z : ℂ | ‖z‖ < 1 ∧ -z ∈ slitPlane}` agrees with
`mellinBarnesRegularizedGaussHGFun a b c` throughout `{z : ℂ | -z ∈ slitPlane}`. -/
theorem eqOn_mellinBarnesRegularizedGaussHGFun_of_analyticOnNhd {a b c : ℂ} {f : ℂ → ℂ}
    (ha : ∀ k : ℕ, a ≠ -k) (hb : ∀ k : ℕ, b ≠ -k)
    (hf : AnalyticOnNhd ℂ f {z : ℂ | -z ∈ slitPlane})
    (hEq : Set.EqOn f (regularizedGaussHGFun a b c) {z : ℂ | ‖z‖ < 1 ∧ -z ∈ slitPlane}) :
    Set.EqOn f (mellinBarnesRegularizedGaussHGFun a b c) {z : ℂ | -z ∈ slitPlane} := by
  refine hf.eqOn_neg_slitPlane_of_eqOn_cut_ball
    (fun z hz => analyticAt_const.mellinBarnesRegularizedGaussHGFun
      analyticAt_const analyticAt_const analyticAt_id ha hb hz) fun z hz => ?_
  rw [hEq hz, regularizedGaussHGFun_eq_mellinBarnesRegularizedGaussHGFun c ha hb hz.1 hz.2]

/-- **Overlap with the ordinary Gauss hypergeometric series `₂F₁` (DLMF 15.6.6).** For all
`a, b, c ∉ -ℕ`, `‖z‖ < 1`, and `-z ∈ slitPlane`, `ordinaryHypergeometric a b c z` agrees with
`mellinBarnesOrdinaryHypergeometric a b c z`. -/
theorem ordinaryHypergeometric_eq_mellinBarnesOrdinaryHypergeometric {a b c z : ℂ}
    (ha : ∀ k : ℕ, a ≠ -k) (hb : ∀ k : ℕ, b ≠ -k) (hc : ∀ k : ℕ, c ≠ -k)
    (hz_norm : ‖z‖ < 1) (hz_slit : -z ∈ slitPlane) :
    ordinaryHypergeometric a b c z = mellinBarnesOrdinaryHypergeometric a b c z := by
  have h := ordinaryHypergeometric_div_Gamma_eq (a := a) (b := b) (z := z) hc
  rw [div_eq_iff (Gamma_ne_zero hc),
    regularizedGaussHGFun_eq_mellinBarnesRegularizedGaussHGFun c ha hb hz_norm hz_slit,
    mul_comm] at h
  rw [h, mellinBarnesOrdinaryHypergeometric_eq_Gamma_mul]

/-- **Separating-contour Mellin–Barnes representation of `ordinaryHypergeometric` (`₂F₁`)**
(DLMF 15.6.6) at any admissible abscissa `σ < 0` avoiding `-Re a - ℕ` and `-Re b - ℕ`, giving
`₂F₁(a, b; c; z) = (Γ(c) / (Γ(a) Γ(b))) * hypergeometricMellinBarnes a b c z σ` for all
`a, b, c ∉ -ℕ`, `‖z‖ < 1`, and `-z ∈ slitPlane`. -/
theorem ordinaryHypergeometric_eq_hypergeometricMellinBarnes {a b c z : ℂ} {σ : ℝ}
    (ha : ∀ k : ℕ, a ≠ -k) (hb : ∀ k : ℕ, b ≠ -k) (hc : ∀ k : ℕ, c ≠ -k) (hσ : σ < 0)
    (haσ : ∀ k : ℕ, a.re + σ ≠ -k) (hbσ : ∀ k : ℕ, b.re + σ ≠ -k)
    (hz_norm : ‖z‖ < 1) (hz_slit : -z ∈ slitPlane) :
    ordinaryHypergeometric a b c z =
      Gamma c / (Gamma a * Gamma b) * hypergeometricMellinBarnes a b c z σ := by
  rw [ordinaryHypergeometric_eq_mellinBarnesOrdinaryHypergeometric ha hb hc hz_norm hz_slit,
    mellinBarnesOrdinaryHypergeometric_eq_hypergeometricMellinBarnes a b c z hσ haσ hbσ hz_slit]

/-- **Uniqueness of the Mellin–Barnes continuation for `ordinaryHypergeometric` (`₂F₁`) on the
cut plane.** Any function holomorphic on `{z : ℂ | -z ∈ slitPlane}` that agrees with
`ordinaryHypergeometric a b c` on `{z : ℂ | ‖z‖ < 1 ∧ -z ∈ slitPlane}` agrees with
`mellinBarnesOrdinaryHypergeometric a b c` throughout `{z : ℂ | -z ∈ slitPlane}`. -/
theorem eqOn_mellinBarnesOrdinaryHypergeometric_of_analyticOnNhd {a b c : ℂ} {f : ℂ → ℂ}
    (ha : ∀ k : ℕ, a ≠ -k) (hb : ∀ k : ℕ, b ≠ -k) (hc : ∀ k : ℕ, c ≠ -k)
    (hf : AnalyticOnNhd ℂ f {z : ℂ | -z ∈ slitPlane})
    (hEq : Set.EqOn f (ordinaryHypergeometric a b c) {z : ℂ | ‖z‖ < 1 ∧ -z ∈ slitPlane}) :
    Set.EqOn f (mellinBarnesOrdinaryHypergeometric a b c) {z : ℂ | -z ∈ slitPlane} := by
  refine hf.eqOn_neg_slitPlane_of_eqOn_cut_ball
    (fun z hz => analyticAt_const.mellinBarnesOrdinaryHypergeometric
      analyticAt_const analyticAt_const analyticAt_id ha hb hc hz) fun z hz => ?_
  rw [hEq hz, ordinaryHypergeometric_eq_mellinBarnesOrdinaryHypergeometric ha hb hc hz.1 hz.2]

end Complex
