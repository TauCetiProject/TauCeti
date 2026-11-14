/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Prod
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# Parametrized surfaces of revolution

Rotating a plane profile `(f(v), g(v))` about the vertical axis gives the parametrization
`(u, v) ↦ (f(v) cos u, f(v) sin u, g(v))`. Its first fundamental form is diagonal, with
coefficients `f(v)²` and `f'(v)² + g'(v)²`. The differential is injective wherever the radius
is nonzero and the profile velocity is nonzero. All differential statements are local in
the profile parameter; neither completeness nor an invertible height function is assumed.
-/

public noncomputable section

open scoped InnerProductSpace ContDiff

namespace TauCeti.SurfaceOfRevolution

local notation "E₃" => EuclideanSpace ℝ (Fin 3)

/-- The surface obtained by revolving the profile `(f, g)` about the third coordinate axis. -/
def parametrization (f g : ℝ → ℝ) (p : ℝ × ℝ) : E₃ :=
  (f p.2 * Real.cos p.1) • EuclideanSpace.basisFun (Fin 3) ℝ 0 +
    (f p.2 * Real.sin p.1) • EuclideanSpace.basisFun (Fin 3) ℝ 1 +
    g p.2 • EuclideanSpace.basisFun (Fin 3) ℝ 2

/-- The three Euclidean coordinates of the revolution parametrization. -/
theorem parametrization_def (f g : ℝ → ℝ) (p : ℝ × ℝ) :
    parametrization f g p =
      (f p.2 * Real.cos p.1) • EuclideanSpace.basisFun (Fin 3) ℝ 0 +
      (f p.2 * Real.sin p.1) • EuclideanSpace.basisFun (Fin 3) ℝ 1 +
      g p.2 • EuclideanSpace.basisFun (Fin 3) ℝ 2 :=
  (rfl)

/-- The squared speed of the generating profile in its given parameter. -/
def profileSpeedSq (f g : ℝ → ℝ) (v : ℝ) : ℝ :=
  deriv f v ^ 2 + deriv g v ^ 2

/-- The profile-speed coefficient is the sum of the squares of its two derivatives. -/
theorem profileSpeedSq_def (f g : ℝ → ℝ) (v : ℝ) :
    profileSpeedSq f g v = deriv f v ^ 2 + deriv g v ^ 2 :=
  (rfl)

/-- Differentiability of the profile at a point gives differentiability of its revolution
parametrization at the corresponding coordinate point. -/
theorem differentiableAt_parametrization {f g : ℝ → ℝ} {p : ℝ × ℝ}
    (hf : DifferentiableAt ℝ f p.2) (hg : DifferentiableAt ℝ g p.2) :
    DifferentiableAt ℝ (parametrization f g) p := by
  unfold parametrization
  fun_prop

/-- The coordinate formula for the differential of a surface of revolution. -/
theorem fderiv_parametrization {f g : ℝ → ℝ} {p : ℝ × ℝ}
    (hf : DifferentiableAt ℝ f p.2) (hg : DifferentiableAt ℝ g p.2) (w : ℝ × ℝ) :
    fderiv ℝ (parametrization f g) p w =
      (deriv f p.2 * w.2 * Real.cos p.1 - f p.2 * Real.sin p.1 * w.1) •
        EuclideanSpace.basisFun (Fin 3) ℝ 0 +
      (deriv f p.2 * w.2 * Real.sin p.1 + f p.2 * Real.cos p.1 * w.1) •
        EuclideanSpace.basisFun (Fin 3) ℝ 1 +
      (deriv g p.2 * w.2) • EuclideanSpace.basisFun (Fin 3) ℝ 2 := by
  have hf' := hf.hasDerivAt.hasFDerivAt.comp p hasFDerivAt_snd
  have hg' := hg.hasDerivAt.hasFDerivAt.comp p hasFDerivAt_snd
  have hc := (Real.hasDerivAt_cos p.1).hasFDerivAt.comp p hasFDerivAt_fst
  have hs := (Real.hasDerivAt_sin p.1).hasFDerivAt.comp p hasFDerivAt_fst
  have h := (((hf'.mul hc).smul_const (EuclideanSpace.basisFun (Fin 3) ℝ 0)).add
    ((hf'.mul hs).smul_const (EuclideanSpace.basisFun (Fin 3) ℝ 1))).add
      (hg'.smul_const (EuclideanSpace.basisFun (Fin 3) ℝ 2))
  have h' : HasFDerivAt (parametrization f g) _ p := h
  rw [h'.fderiv]
  simp only [add_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.comp_apply, smul_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
    ContinuousLinearMap.toSpanSingleton_apply, Function.comp_apply, smul_eq_mul]
  congr 2 <;> ring_nf

/-- The first fundamental form in arbitrary profile coordinates. -/
theorem inner_fderiv_parametrization {f g : ℝ → ℝ} {p : ℝ × ℝ}
    (hf : DifferentiableAt ℝ f p.2) (hg : DifferentiableAt ℝ g p.2)
    (w z : ℝ × ℝ) :
    inner ℝ (fderiv ℝ (parametrization f g) p w)
        (fderiv ℝ (parametrization f g) p z) =
      f p.2 ^ 2 * w.1 * z.1 + profileSpeedSq f g p.2 * w.2 * z.2 := by
  rw [fderiv_parametrization hf hg, fderiv_parametrization hf hg]
  unfold profileSpeedSq
  simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
    EuclideanSpace.basisFun_apply, EuclideanSpace.inner_single_left]
  norm_num
  linear_combination
    (f p.2 ^ 2 * w.1 * z.1 + deriv f p.2 ^ 2 * w.2 * z.2) *
      Real.sin_sq_add_cos_sq p.1

/-- A surface of revolution is smooth wherever both generating functions are smooth. -/
theorem contDiff_parametrization {f g : ℝ → ℝ} {n : ℕ∞ω}
    (hf : ContDiff ℝ n f) (hg : ContDiff ℝ n g) :
    ContDiff ℝ n (parametrization f g) := by
  unfold parametrization
  fun_prop

/-- Local smoothness of the parametrization only requires local smoothness of its profile. -/
theorem contDiffAt_parametrization {f g : ℝ → ℝ} {n : ℕ∞ω} {p : ℝ × ℝ}
    (hf : ContDiffAt ℝ n f p.2) (hg : ContDiffAt ℝ n g p.2) :
    ContDiffAt ℝ n (parametrization f g) p := by
  unfold parametrization
  fun_prop

/-- The first fundamental form is positive on every nonzero coordinate vector at a regular
profile point of nonzero radius. -/
theorem firstFundamentalForm_pos {f g : ℝ → ℝ} {v : ℝ}
    (hf : f v ≠ 0) (hfg : 0 < profileSpeedSq f g v) {w : ℝ × ℝ} (hw : w ≠ 0) :
    0 < f v ^ 2 * w.1 ^ 2 + profileSpeedSq f g v * w.2 ^ 2 := by
  have hr : 0 < f v ^ 2 := sq_pos_of_ne_zero hf
  have h₁ : 0 ≤ f v ^ 2 * w.1 ^ 2 := mul_nonneg hr.le (sq_nonneg _)
  have h₂ : 0 ≤ profileSpeedSq f g v * w.2 ^ 2 := mul_nonneg hfg.le (sq_nonneg _)
  by_cases hw₁ : w.1 = 0
  · have hw₂ : w.2 ≠ 0 := by
      intro h
      exact hw (Prod.ext hw₁ h)
    exact add_pos_of_nonneg_of_pos h₁ (mul_pos hfg (sq_pos_of_ne_zero hw₂))
  · exact add_pos_of_pos_of_nonneg (mul_pos hr (sq_pos_of_ne_zero hw₁)) h₂

/-- The differential is injective at every regular profile point of nonzero radius. -/
theorem injective_fderiv_parametrization {f g : ℝ → ℝ} {p : ℝ × ℝ}
    (hf : DifferentiableAt ℝ f p.2) (hg : DifferentiableAt ℝ g p.2)
    (hr : f p.2 ≠ 0) (hfg : 0 < profileSpeedSq f g p.2) :
    Function.Injective (fderiv ℝ (parametrization f g) p) := by
  intro w z hwz
  apply sub_eq_zero.mp
  by_contra hne
  have hpos := firstFundamentalForm_pos hr hfg hne
  have hinner := inner_fderiv_parametrization hf hg (w - z) (w - z)
  rw [map_sub, hwz, sub_self] at hinner
  simp only [inner_zero_left] at hinner
  nlinarith [hinner]

end TauCeti.SurfaceOfRevolution
