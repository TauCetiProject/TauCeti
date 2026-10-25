/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Wirtinger.Basic
public import TauCeti.Analysis.Fourier.MihlinHormander
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import TauCeti.Analysis.InnerProductSpace.Orthonormal.Multilinear

/-!
# The Calderón–Zygmund inequality for the Cauchy–Riemann operator

For `1 < p < ∞` there is a constant `C` with

`‖Du‖_{Lᵖ} ≤ C ‖\bar∂u‖_{Lᵖ}`

for every Schwartz function `u : ℂ → F` with values in a complex Hilbert space
(`TauCeti.exists_eLpNorm_fderiv_le_eLpNorm_conjWirtingerDeriv`), and hence for every smooth
compactly supported `u`
(`TauCeti.exists_eLpNorm_fderiv_le_eLpNorm_conjWirtingerDeriv_of_hasCompactSupport`). Here `Du` is
the real derivative of `u` and `\bar∂u = (∂ₓu + I ∂ᵧu) / 2` is its conjugate Wirtinger derivative
`TauCeti.conjWirtingerDeriv u z 1`. For `F = ℂⁿ` this is the inequality
`‖∇u‖_{Lᵖ} ≤ C ‖∂ₛu + J₀ ∂ₜu‖_{Lᵖ}` behind the elliptic estimates for `J`-holomorphic curves. It
fails at the endpoints `p = 1` and `p = ∞`.

## The argument

With Mathlib's normalization of the Fourier transform, `𝓕 (∂_v u) ξ = 2πi ⟪ξ, v⟫ 𝓕 u ξ` and
hence `𝓕 (\bar∂u) ξ = πi ξ 𝓕 u ξ`, the real inner product on `ℂ` being `⟪ξ, v⟫ = re (conj ξ v)`.
So on Schwartz functions `∂_v = T_{m_v} ∘ \bar∂`, where `T_{m_v}` is the Fourier multiplier with
symbol

`m_v(ξ) = 2 ⟪ξ, v⟫ / ξ = conj v + v (conj ξ / ξ)`.

Up to the constant term, this is `v` times the symbol `conj ξ / ξ` of the Beurling transform.
The symbol is smooth away from the origin and homogeneous of degree `0`, so it satisfies Mihlin's
condition (`TauCeti.exists_norm_iteratedFDeriv_le_div_pow_of_smul_eq`), and the Mihlin–Hörmander
multiplier theorem (`TauCeti.exists_eLpNorm_fourierMultiplierCLM_le_of_norm_iteratedFDeriv_le`)
bounds `T_{m_v}` on `Lᵖ`. Applying this to the directions `v = 1` and `v = I` bounds the whole
derivative.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS
  Colloquium Publications **52**, 2012, Appendix B.2 (the Calderón–Zygmund inequality).
* E. M. Stein, *Singular Integrals and Differentiability Properties of Functions*, Chapter IV, §3.
-/

public section

noncomputable section

open scoped ENNReal NNReal FourierTransform SchwartzMap LineDeriv Real ContDiff
open FourierTransform MeasureTheory Complex

namespace TauCeti

/-! ### The symbol of `∂_v ∘ \bar∂⁻¹` -/

/-- The symbol `ξ ↦ 2 ⟪ξ, v⟫ / ξ` of the operator `∂_v ∘ \bar∂⁻¹` on `ℂ`. At the origin it takes
the value `0`. -/
private def dbarSymbol (v ξ : ℂ) : ℂ := 2 * ((inner ℝ ξ v : ℝ) : ℂ) * ξ⁻¹

private theorem dbarSymbol_mul (v ξ : ℂ) : dbarSymbol v ξ * ξ = 2 * ((inner ℝ ξ v : ℝ) : ℂ) := by
  rcases eq_or_ne ξ 0 with rfl | hξ
  · simp [dbarSymbol]
  · exact inv_mul_cancel_right₀ hξ _

private theorem norm_dbarSymbol_le (v ξ : ℂ) : ‖dbarSymbol v ξ‖ ≤ 2 * ‖v‖ := by
  rcases eq_or_ne ξ 0 with rfl | hξ
  · simp [dbarSymbol]
  rw [dbarSymbol, norm_mul, norm_inv, norm_mul, ← div_eq_mul_inv, Complex.norm_real,
    div_le_iff₀ (norm_pos_iff.2 hξ)]
  have := abs_real_inner_le_norm ξ v
  simp only [Real.norm_eq_abs, Complex.norm_ofNat]
  nlinarith [norm_nonneg ξ, norm_nonneg v]

private theorem dbarSymbol_smul (v : ℂ) {t : ℝ} (ht : 0 < t) (ξ : ℂ) :
    dbarSymbol v (t • ξ) = dbarSymbol v ξ := by
  rcases eq_or_ne ξ 0 with rfl | hξ
  · simp [dbarSymbol]
  have ht' : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  rw [dbarSymbol, dbarSymbol, real_inner_smul_left, Complex.real_smul, Complex.ofReal_mul]
  field_simp

private theorem contDiffOn_dbarSymbol (v : ℂ) : ContDiffOn ℝ ∞ (dbarSymbol v) {0}ᶜ :=
  fun _ hξ ↦ ContDiffAt.contDiffWithinAt <|
    (contDiff_const.mul (ofRealCLM.contDiff.comp
      (contDiff_id.inner ℝ contDiff_const))).contDiffAt.mul
      ((contDiffAt_inv ℂ hξ).restrict_scalars ℝ)

private theorem memLp_dbarSymbol (v : ℂ) (μ : Measure ℂ) : MemLp (dbarSymbol v) (∞ : ℝ≥0∞) μ :=
  memLp_top_of_bound (by unfold dbarSymbol; fun_prop) _ (.of_forall (norm_dbarSymbol_le v))

/-! ### The Cauchy–Riemann operator on the Fourier side -/

variable {F : Type*} [NormedAddCommGroup F]

/-- The Cauchy–Riemann operator `\bar∂ = (∂ₓ + I ∂ᵧ) / 2` on Schwartz functions on `ℂ`. -/
private def schwartzDbar [NormedSpace ℂ F] (u : 𝓢(ℂ, F)) : 𝓢(ℂ, F) :=
  (2 : ℂ)⁻¹ • (∂_{(1 : ℂ)} u + I • ∂_{I} u)

private theorem schwartzDbar_apply [NormedSpace ℂ F] (u : 𝓢(ℂ, F)) (z : ℂ) :
    schwartzDbar u z = conjWirtingerDeriv (⇑u) z 1 := by
  simp [schwartzDbar, conjWirtingerDeriv_apply, SchwartzMap.lineDerivOp_apply_eq_fderiv]

/-- On the Fourier side, `∂_v u` is the symbol `2 ⟪ξ, v⟫ / ξ` times `\bar∂u`. -/
private theorem fourier_lineDerivOp_apply_eq_dbarSymbol_smul [NormedSpace ℂ F] (u : 𝓢(ℂ, F))
    (v ξ : ℂ) : 𝓕 (∂_{v} u) ξ = dbarSymbol v ξ • 𝓕 (schwartzDbar u) ξ := by
  have h : ∀ w : ℂ, 𝓕 (∂_{w} u) ξ = ((2 * π * I) * (inner ℝ ξ w : ℝ)) • 𝓕 u ξ := fun w ↦ by
    have hw : (inner ℝ · w : ℂ → ℝ).HasTemperateGrowth := by fun_prop
    rw [SchwartzMap.fourier_lineDerivOp_eq, smul_apply,
      SchwartzMap.smulLeftCLM_apply_apply hw, ← Complex.coe_smul, smul_smul]
  rw [schwartzDbar, FourierTransform.fourier_smul, smul_apply,
    FourierTransform.fourier_add, add_apply, FourierTransform.fourier_smul,
    smul_apply, h, h, h, smul_smul I, ← add_smul, smul_smul, smul_smul]
  congr 1
  -- With `ξ = re ξ + im ξ I`, both sides are `2πi ⟪ξ, v⟫`.
  have hm := dbarSymbol_mul v ξ
  have hξ := re_add_im ξ
  simp only [Complex.inner, one_mul, mul_re, I_re, I_im, conj_re, conj_im] at hm ⊢
  push_cast at hm ⊢
  linear_combination (-(π : ℂ) * I) * hm - ((π : ℂ) * I * dbarSymbol v ξ) * hξ

variable [InnerProductSpace ℂ F] [CompleteSpace F]

/-- In `L²`, `∂_v u = T_{m_v} (\bar∂u)` for the Fourier multiplier with symbol
`m_v(ξ) = 2 ⟪ξ, v⟫ / ξ`. -/
private theorem toLp_lineDerivOp_eq_fourierMultiplierCLM (u : 𝓢(ℂ, F)) (v : ℂ) :
    (∂_{v} u).toLp 2 = Lp.fourierMultiplierCLM F ((memLp_dbarSymbol v volume).toLp _)
      ((schwartzDbar u).toLp 2) := by
  refine (fourierInv_fourier_eq (F := Lp F 2 (volume : Measure ℂ)) _).symm.trans ?_
  rw [Lp.fourierMultiplierCLM_apply, SchwartzMap.toLp_fourier_eq, SchwartzMap.toLp_fourier_eq]
  congr 1
  apply Lp.ext
  filter_upwards [SchwartzMap.coeFn_toLp (𝓕 (∂_{v} u)) 2,
    Lp.coeFn_lpSMul (r := 2) ((memLp_dbarSymbol v volume).toLp _) ((𝓕 (schwartzDbar u)).toLp 2),
    (memLp_dbarSymbol v volume).coeFn_toLp, SchwartzMap.coeFn_toLp (𝓕 (schwartzDbar u)) 2]
    with ξ h₁ h₂ h₃ h₄
  rw [h₁, h₂, Pi.smul_apply', h₃, h₄, fourier_lineDerivOp_apply_eq_dbarSymbol_smul]

/-- The estimate `‖∂_v u‖_{Lᵖ} ≤ C ‖\bar∂u‖_{Lᵖ}` for one direction `v`, from the Mihlin–Hörmander
multiplier theorem. -/
private theorem exists_eLpNorm_lineDerivOp_le (v : ℂ) {p : ℝ≥0∞} (hp : 1 < p)
    (hp_top : p ≠ (∞ : ℝ≥0∞)) :
    ∃ C : ℝ≥0, ∀ u : 𝓢(ℂ, F),
      eLpNorm (⇑(∂_{v} u : 𝓢(ℂ, F))) p volume ≤ C * eLpNorm (⇑(schwartzDbar u)) p volume := by
  obtain ⟨A, hA⟩ := exists_norm_iteratedFDeriv_le_div_pow_of_smul_eq (N := 2)
    ((contDiffOn_dbarSymbol v).of_le (by simp)) fun t ht ξ ↦ dbarSymbol_smul v ht ξ
  obtain ⟨C, hC⟩ := exists_eLpNorm_fourierMultiplierCLM_le_of_norm_iteratedFDeriv_le (V := ℂ)
    (F := F) (N := 2) (by simp [Complex.finrank_real_complex]) hp hp_top
  refine ⟨C * A, fun u ↦ ?_⟩
  have h := hC (contDiffOn_dbarSymbol v) hA _ (memLp_dbarSymbol v volume).coeFn_toLp
    ((schwartzDbar u).toLp 2)
  rwa [← toLp_lineDerivOp_eq_fourierMultiplierCLM,
    eLpNorm_congr_ae (SchwartzMap.coeFn_toLp _ 2 volume),
    eLpNorm_congr_ae (SchwartzMap.coeFn_toLp _ 2 volume), ← ENNReal.coe_mul] at h

/-! ### The Calderón–Zygmund inequality -/

/-- **The Calderón–Zygmund inequality for the Cauchy–Riemann operator.** Let `1 < p < ∞`. There
is a constant `C` with

`‖Du‖_{Lᵖ} ≤ C ‖\bar∂u‖_{Lᵖ}`

for every Schwartz function `u` on `ℂ` with values in a complex Hilbert space, where `Du` is the
real derivative of `u` and `\bar∂u = (∂ₓu + I ∂ᵧu) / 2` its conjugate Wirtinger derivative. -/
theorem exists_eLpNorm_fderiv_le_eLpNorm_conjWirtingerDeriv {p : ℝ≥0∞} (hp : 1 < p)
    (hp_top : p ≠ (∞ : ℝ≥0∞)) :
    ∃ C : ℝ≥0, ∀ u : 𝓢(ℂ, F), eLpNorm (fderiv ℝ ⇑u) p volume ≤
      C * eLpNorm (fun z ↦ conjWirtingerDeriv (⇑u) z 1) p volume := by
  obtain ⟨C₁, hC₁⟩ := exists_eLpNorm_lineDerivOp_le (F := F) 1 hp hp_top
  obtain ⟨C₂, hC₂⟩ := exists_eLpNorm_lineDerivOp_le (F := F) I hp hp_top
  refine ⟨C₁ + C₂, fun u ↦ ?_⟩
  set u₁ : 𝓢(ℂ, F) := ∂_{(1 : ℂ)} u
  set u₂ : 𝓢(ℂ, F) := ∂_{I} u
  -- The derivative is bounded pointwise by its values on the basis `1, I` of `ℂ` over `ℝ`.
  have hpt : ∀ z, ‖fderiv ℝ (⇑u) z‖ ≤ ‖u₁ z‖ + ‖u₂ z‖ := fun z ↦ by
    simpa [u₁, u₂, Fin.sum_univ_two, SchwartzMap.lineDerivOp_apply_eq_fderiv] using
      (fderiv ℝ (⇑u) z).opNorm_le_sum_norm_apply_orthonormalBasis Complex.orthonormalBasisOneI
  calc eLpNorm (fderiv ℝ ⇑u) p volume
      ≤ eLpNorm (fun z ↦ ‖u₁ z‖ + ‖u₂ z‖) p volume :=
        eLpNorm_mono_real ((u.smooth ⊤).continuous_fderiv (by simp)).aestronglyMeasurable hpt
    _ ≤ eLpNorm (⇑u₁) p volume + eLpNorm (⇑u₂) p volume := by
        refine (eLpNorm_add_le (f := fun z ↦ ‖u₁ z‖) (g := fun z ↦ ‖u₂ z‖) hp.le).trans_eq ?_
        rw [eLpNorm_norm _ u₁.continuous.aestronglyMeasurable,
          eLpNorm_norm _ u₂.continuous.aestronglyMeasurable]
    _ ≤ C₁ * eLpNorm (⇑(schwartzDbar u)) p volume + C₂ * eLpNorm (⇑(schwartzDbar u)) p volume :=
        add_le_add (hC₁ u) (hC₂ u)
    _ = (C₁ + C₂ : ℝ≥0) * eLpNorm (fun z ↦ conjWirtingerDeriv (⇑u) z 1) p volume := by
        rw [← funext (schwartzDbar_apply u), ENNReal.coe_add, add_mul]

/-- **The Calderón–Zygmund inequality for smooth compactly supported maps.** Let `1 < p < ∞`.
There is a constant `C` with `‖Du‖_{Lᵖ} ≤ C ‖\bar∂u‖_{Lᵖ}` for every smooth compactly supported map
`u` from `ℂ` to a complex Hilbert space. -/
theorem exists_eLpNorm_fderiv_le_eLpNorm_conjWirtingerDeriv_of_hasCompactSupport {p : ℝ≥0∞}
    (hp : 1 < p) (hp_top : p ≠ (∞ : ℝ≥0∞)) :
    ∃ C : ℝ≥0, ∀ u : ℂ → F, ContDiff ℝ ∞ u → HasCompactSupport u →
      eLpNorm (fderiv ℝ u) p volume ≤
        C * eLpNorm (fun z ↦ conjWirtingerDeriv u z 1) p volume := by
  obtain ⟨C, hC⟩ := exists_eLpNorm_fderiv_le_eLpNorm_conjWirtingerDeriv (F := F) hp hp_top
  refine ⟨C, fun u hu hc ↦ ?_⟩
  have hcoe : ⇑(hc.toSchwartzMap hu) = u := funext (HasCompactSupport.toSchwartzMap_toFun _ _)
  simpa only [hcoe] using hC (hc.toSchwartzMap hu)

end TauCeti
