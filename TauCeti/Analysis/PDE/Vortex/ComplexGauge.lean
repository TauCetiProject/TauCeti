/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.GaugeFixed
public import TauCeti.Analysis.Complex.Wirtinger.Basic
public import Mathlib.MeasureTheory.Function.L2Space
import TauCeti.Analysis.InnerProductSpace.Laplacian.Liouville
import TauCeti.Analysis.PDE.Vortex.Zeros

/-!
# Complexified gauge directions and the kernel of the gauge-fixed vortex operator

In the coordinates of `TauCeti.Vortex.equation`, a field `x = (b₁, b₂, p, q)` has connection
`a = i (b₁ ds + b₂ dt)` and section `α = 2 (p + i q)`, and a variation `y` has section variation
`δα = 2 (y₂ + i y₃)`. For a complex function `h = u + i v`, the complexified gauge direction
`complexGaugeDirection x h` is the variation with

`δα = h α`,    `δa = i (y₀ ds + y₁ dt)`,    `y₀ + i y₁ = 2 i ∂bar h`.

Its imaginary part `v` is the infinitesimal unitary gauge action `gaugeDirection x v`, and its real
part `u` is the infinitesimal action of the complex gauge `exp u`, which rescales the section and
changes the connection by `i (-∂₂ u ds + ∂₁ u dt)`, preserving the holomorphicity equation
`∂bar_a α = 0`. At any field, the gauge-fixed operator `L_x = d₀* ⊕ d₁` sends it to

`L_x (complexGaugeDirection x h) = ((-Δ h + P h).im, (-Δ h + P h).re, h E)`,    `P = |α|² / 4`,

where `E` is the complex defect `∂bar_a α` of `x` (`gaugeFixedOperator_complexGaugeDirection`).

Conversely, at a vortex, the two holomorphicity rows of `d₁ y = 0` determine the connection part
of `y` from its section part wherever `α ≠ 0`. Hence a variation with `d₁ y = 0` whose section
variation is divisible by `α`, `δα = h α` with `h` of class `C¹`, is the complexified gauge
direction of `h` (`eq_complexGaugeDirection_of_forall_sectionValue_eq_mul`). If moreover
`L_x y = 0`, then `-Δ h + P h = 0`, so `|h|²` is subharmonic. When `y` is square integrable and
`|α| → 1` at infinity, `h` is square integrable too, and the sub-mean-value inequality forces
`h = 0`. Therefore:

* `eq_zero_of_memLp_of_gaugeFixedOperator_eq_zero_of_sectionValue_eq_mul`: at a plane vortex with
  `|α| → 1`, a continuous `L²` solution of `L_x y = 0` whose section variation is a `C²` multiple
  of `α` vanishes.
* `eq_zero_of_memLp_of_gaugeFixedOperator_eq_zero_of_sectionValue_ne_zero`: at a plane vortex
  with `|α| → 1` and no zeros, the `C²` kernel of `L_x` in `L²` is zero.

At a vortex with zeros of total multiplicity `m`, the quotient `δα / α` of a kernel element is
defined away from the zeros of `α`, and the first theorem says that it cannot extend to a `C²`
function on the whole plane unless the kernel element is zero. This is the injectivity behind
the identification of the kernel of `L_x` with the tangent space of the symmetric product
`Sym^m ℂ` of vortex divisors, in which the singular part of `δα / α` at a zero of multiplicity
`n` is a principal part of order at most `n`. The construction of that principal-part map and
its surjectivity, which needs the existence theory of vortices, are not treated here.

## References

* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2,
  Birkhäuser, 1980, Chapter III.
* C. H. Taubes, *Arbitrary N-vortex solutions to the first order Ginzburg–Landau equations*,
  Comm. Math. Phys. 72 (1980), 277–292.
-/

public section

noncomputable section

namespace TauCeti.Vortex

open Complex Filter MeasureTheory Topology
open scoped Laplacian RealInnerProductSpace

/-- The infinitesimal complexified gauge action of a complex function `h = u + i v` at the field
`x`: the variation with section variation `δα = h α` and connection variation
`δa = i (y₀ ds + y₁ dt)`, `y₀ + i y₁ = 2 i ∂bar h`. Its imaginary part is the unitary gauge action
`gaugeDirection x v`; its real part is the action of the complex gauge `exp u`. -/
def complexGaugeDirection (x : ℂ → EuclideanSpace ℝ (Fin 4)) (h : ℂ → ℂ) (z : ℂ) :
    EuclideanSpace ℝ (Fin 4) :=
  !₂[-(fderiv ℝ h z 1).im - (fderiv ℝ h z I).re, (fderiv ℝ h z 1).re - (fderiv ℝ h z I).im,
    (h z).re * x z 2 - (h z).im * x z 3, (h z).re * x z 3 + (h z).im * x z 2]

/-- The first connection component of the complexified gauge action. -/
@[simp]
theorem complexGaugeDirection_apply_zero (x : ℂ → EuclideanSpace ℝ (Fin 4)) (h : ℂ → ℂ)
    (z : ℂ) :
    complexGaugeDirection x h z 0 = -(fderiv ℝ h z 1).im - (fderiv ℝ h z I).re := by
  rfl

/-- The second connection component of the complexified gauge action. -/
@[simp]
theorem complexGaugeDirection_apply_one (x : ℂ → EuclideanSpace ℝ (Fin 4)) (h : ℂ → ℂ)
    (z : ℂ) :
    complexGaugeDirection x h z 1 = (fderiv ℝ h z 1).re - (fderiv ℝ h z I).im := by
  rfl

/-- The real section component of the complexified gauge action. -/
@[simp]
theorem complexGaugeDirection_apply_two (x : ℂ → EuclideanSpace ℝ (Fin 4)) (h : ℂ → ℂ)
    (z : ℂ) :
    complexGaugeDirection x h z 2 = (h z).re * x z 2 - (h z).im * x z 3 := by
  rfl

/-- The imaginary section component of the complexified gauge action. -/
@[simp]
theorem complexGaugeDirection_apply_three (x : ℂ → EuclideanSpace ℝ (Fin 4)) (h : ℂ → ℂ)
    (z : ℂ) :
    complexGaugeDirection x h z 3 = (h z).re * x z 3 + (h z).im * x z 2 := by
  rfl

/-- The section variation of the complexified gauge action of `h` is `h α`. -/
@[simp]
theorem sectionValue_complexGaugeDirection (x : ℂ → EuclideanSpace ℝ (Fin 4)) (h : ℂ → ℂ)
    (z : ℂ) : sectionValue (complexGaugeDirection x h) z = h z * sectionValue x z := by
  apply Complex.ext <;> simp [sectionValue_apply] <;> ring

/-- The connection variation of the complexified gauge action of `h` is `2 i ∂bar h`, as the
complex coefficient `y₀ + i y₁`. -/
theorem complexGaugeDirection_apply_zero_add_apply_one_mul_I
    (x : ℂ → EuclideanSpace ℝ (Fin 4)) (h : ℂ → ℂ) (z : ℂ) :
    (complexGaugeDirection x h z 0 : ℂ) + complexGaugeDirection x h z 1 * I =
      2 * I * conjWirtingerDeriv h z 1 := by
  rw [conjWirtingerDeriv_apply]
  apply Complex.ext <;> simp <;> ring

/-- The complexified gauge action of the zero function is zero. -/
@[simp]
theorem complexGaugeDirection_zero (x : ℂ → EuclideanSpace ℝ (Fin 4)) :
    complexGaugeDirection x 0 = 0 := by
  funext z
  ext i
  fin_cases i <;> simp [complexGaugeDirection]

/-- On imaginary functions `i f` the complexified gauge action is the unitary gauge action
`gaugeDirection x f`. -/
theorem complexGaugeDirection_ofReal_mul_I (x : ℂ → EuclideanSpace ℝ (Fin 4)) {f : ℂ → ℝ}
    {z : ℂ} (hf : DifferentiableAt ℝ f z) :
    complexGaugeDirection x (fun w ↦ (f w : ℂ) * I) z = gaugeDirection x f z := by
  have hd : HasFDerivAt (fun w ↦ (f w : ℂ) * I) (I • ofRealCLM.comp (fderiv ℝ f z)) z := by
    simpa [Function.comp_def] using (ofRealCLM.hasFDerivAt.comp z hf.hasFDerivAt).mul_const I
  ext i
  fin_cases i <;> simp [hd.fderiv]

/-! ### The gauge-fixed operator on complexified gauge directions -/

section Operator

variable {x : ℂ → EuclideanSpace ℝ (Fin 4)} {h : ℂ → ℂ} {z : ℂ}

/-- A directional derivative of `h` is differentiable where `fderiv ℝ h` is. -/
private theorem hasFDerivAt_fderiv_apply (hh : DifferentiableAt ℝ (fderiv ℝ h) z) (c : ℂ) :
    HasFDerivAt (fun w ↦ fderiv ℝ h w c) (fderiv ℝ (fun w ↦ fderiv ℝ h w c) z) z :=
  (hh.clm_apply (differentiableAt_const c)).hasFDerivAt

private theorem fderiv_complexGaugeDirection_apply_zero
    (hh : DifferentiableAt ℝ (fderiv ℝ h) z) (v : ℂ) :
    fderiv ℝ (fun w ↦ complexGaugeDirection x h w 0) z v =
      -(fderiv ℝ (fun w ↦ fderiv ℝ h w 1) z v).im -
        (fderiv ℝ (fun w ↦ fderiv ℝ h w I) z v).re := by
  have h₁ := (imCLM.hasFDerivAt.comp z (hasFDerivAt_fderiv_apply hh 1)).fun_neg.fun_sub
    (reCLM.hasFDerivAt.comp z (hasFDerivAt_fderiv_apply hh I))
  simp only [Function.comp_def, imCLM_apply, reCLM_apply] at h₁
  simp only [complexGaugeDirection_apply_zero, h₁.fderiv]
  simp

private theorem fderiv_complexGaugeDirection_apply_one
    (hh : DifferentiableAt ℝ (fderiv ℝ h) z) (v : ℂ) :
    fderiv ℝ (fun w ↦ complexGaugeDirection x h w 1) z v =
      (fderiv ℝ (fun w ↦ fderiv ℝ h w 1) z v).re -
        (fderiv ℝ (fun w ↦ fderiv ℝ h w I) z v).im := by
  have h₁ := (reCLM.hasFDerivAt.comp z (hasFDerivAt_fderiv_apply hh 1)).fun_sub
    (imCLM.hasFDerivAt.comp z (hasFDerivAt_fderiv_apply hh I))
  simp only [Function.comp_def, imCLM_apply, reCLM_apply] at h₁
  simp only [complexGaugeDirection_apply_one, h₁.fderiv]
  simp

private theorem fderiv_complexGaugeDirection_apply_two
    (hp : DifferentiableAt ℝ (fun w ↦ x w 2) z) (hq : DifferentiableAt ℝ (fun w ↦ x w 3) z)
    (hh : DifferentiableAt ℝ h z) (v : ℂ) :
    fderiv ℝ (fun w ↦ complexGaugeDirection x h w 2) z v =
      (fderiv ℝ h z v).re * x z 2 + (h z).re * fderiv ℝ (fun w ↦ x w 2) z v -
        ((fderiv ℝ h z v).im * x z 3 + (h z).im * fderiv ℝ (fun w ↦ x w 3) z v) := by
  have hu := reCLM.hasFDerivAt.comp z hh.hasFDerivAt
  have hv := imCLM.hasFDerivAt.comp z hh.hasFDerivAt
  have h₁ := (hu.fun_mul hp.hasFDerivAt).fun_sub (hv.fun_mul hq.hasFDerivAt)
  simp only [Function.comp_def, imCLM_apply, reCLM_apply] at h₁
  simp only [complexGaugeDirection_apply_two, h₁.fderiv]
  simp
  ring

private theorem fderiv_complexGaugeDirection_apply_three
    (hp : DifferentiableAt ℝ (fun w ↦ x w 2) z) (hq : DifferentiableAt ℝ (fun w ↦ x w 3) z)
    (hh : DifferentiableAt ℝ h z) (v : ℂ) :
    fderiv ℝ (fun w ↦ complexGaugeDirection x h w 3) z v =
      (fderiv ℝ h z v).re * x z 3 + (h z).re * fderiv ℝ (fun w ↦ x w 3) z v +
        ((fderiv ℝ h z v).im * x z 2 + (h z).im * fderiv ℝ (fun w ↦ x w 2) z v) := by
  have hu := reCLM.hasFDerivAt.comp z hh.hasFDerivAt
  have hv := imCLM.hasFDerivAt.comp z hh.hasFDerivAt
  have h₁ := (hu.fun_mul hq.hasFDerivAt).fun_add (hv.fun_mul hp.hasFDerivAt)
  simp only [Function.comp_def, imCLM_apply, reCLM_apply] at h₁
  simp only [complexGaugeDirection_apply_three, h₁.fderiv]
  simp
  ring

/-- The Laplacian and the symmetry of the second derivatives of `h`, in the coordinate
frame `(1, i)`. -/
private theorem laplacian_eq_and_symm (hh : ContDiffAt ℝ 2 h z) :
    Δ h z = fderiv ℝ (fun w ↦ fderiv ℝ h w 1) z 1 + fderiv ℝ (fun w ↦ fderiv ℝ h w I) z I ∧
      fderiv ℝ (fun w ↦ fderiv ℝ h w 1) z I = fderiv ℝ (fun w ↦ fderiv ℝ h w I) z 1 := by
  have hdf := (hh.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  refine ⟨?_, ?_⟩
  · rw [laplacian_eq_sum_fderiv_fderiv_apply orthonormalBasisOneI hdf]
    simp [Fin.sum_univ_two]
  · have hs := (hh.isSymmSndFDerivAt (by simp)).eq I 1
    rw [fderiv_clm_apply hdf (differentiableAt_const _),
      fderiv_clm_apply hdf (differentiableAt_const _)]
    simpa using hs

/-- **The gauge-fixing row on complexified gauge directions**: at every field,
`d₀* (complexGaugeDirection x h) = (-Δ h + P h).im`, where `P = p² + q² = |α|² / 4`. -/
theorem gaugeAdjoint_complexGaugeDirection (hh : ContDiffAt ℝ 2 h z) :
    gaugeAdjoint x (complexGaugeDirection x h) z =
      (-Δ h z + (x z 2 ^ 2 + x z 3 ^ 2) • h z).im := by
  have hdf := (hh.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  obtain ⟨hΔ, hs⟩ := laplacian_eq_and_symm hh
  rw [gaugeAdjoint_def, fderiv_complexGaugeDirection_apply_zero hdf,
    fderiv_complexGaugeDirection_apply_one hdf, hΔ, hs]
  simp [-ofReal_pow]
  ring

/-- The curvature row of `d₁` on complexified gauge directions: at every field it is
`(-Δ h + P h).re`, where `P = p² + q² = |α|² / 4`. -/
theorem linearizedEquation_complexGaugeDirection_apply_zero (hh : ContDiffAt ℝ 2 h z) :
    linearizedEquation x (complexGaugeDirection x h) z 0 =
      (-Δ h z + (x z 2 ^ 2 + x z 3 ^ 2) • h z).re := by
  have hdf := (hh.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  obtain ⟨hΔ, hs⟩ := laplacian_eq_and_symm hh
  rw [linearizedEquation_apply_zero, fderiv_complexGaugeDirection_apply_zero hdf,
    fderiv_complexGaugeDirection_apply_one hdf, hΔ, hs]
  simp [-ofReal_pow]
  ring

/-- The first holomorphicity row of `d₁` on complexified gauge directions is the corresponding
row of `h E`, where `E` is the complex defect `∂bar_a α` of `x`. -/
theorem linearizedEquation_complexGaugeDirection_apply_one
    (hp : DifferentiableAt ℝ (fun w ↦ x w 2) z) (hq : DifferentiableAt ℝ (fun w ↦ x w 3) z)
    (hh : DifferentiableAt ℝ h z) :
    linearizedEquation x (complexGaugeDirection x h) z 1 =
      (h z).re * equation x z 1 - (h z).im * equation x z 2 := by
  rw [linearizedEquation_apply_one, fderiv_complexGaugeDirection_apply_two hp hq hh,
    fderiv_complexGaugeDirection_apply_three hp hq hh]
  simp
  ring

/-- The second holomorphicity row of `d₁` on complexified gauge directions is the corresponding
row of `h E`, where `E` is the complex defect `∂bar_a α` of `x`. -/
theorem linearizedEquation_complexGaugeDirection_apply_two
    (hp : DifferentiableAt ℝ (fun w ↦ x w 2) z) (hq : DifferentiableAt ℝ (fun w ↦ x w 3) z)
    (hh : DifferentiableAt ℝ h z) :
    linearizedEquation x (complexGaugeDirection x h) z 2 =
      (h z).re * equation x z 2 + (h z).im * equation x z 1 := by
  rw [linearizedEquation_apply_two, fderiv_complexGaugeDirection_apply_two hp hq hh,
    fderiv_complexGaugeDirection_apply_three hp hq hh]
  simp
  ring

/-- **The gauge-fixed operator on complexified gauge directions.** At every field,
`L_x (complexGaugeDirection x h) = ((-Δ h + P h).im, (-Δ h + P h).re, h E)`, where
`P = p² + q² = |α|² / 4` and `E` is the complex defect `∂bar_a α` of `x`, written in its two real
rows. -/
theorem gaugeFixedOperator_complexGaugeDirection
    (hp : DifferentiableAt ℝ (fun w ↦ x w 2) z) (hq : DifferentiableAt ℝ (fun w ↦ x w 3) z)
    (hh : ContDiffAt ℝ 2 h z) :
    gaugeFixedOperator x (complexGaugeDirection x h) z =
      !₂[(-Δ h z + (x z 2 ^ 2 + x z 3 ^ 2) • h z).im,
        (-Δ h z + (x z 2 ^ 2 + x z 3 ^ 2) • h z).re,
        (h z).re * equation x z 1 - (h z).im * equation x z 2,
        (h z).re * equation x z 2 + (h z).im * equation x z 1] := by
  have hh₁ := hh.differentiableAt (by norm_num)
  ext i
  fin_cases i
  · simpa using gaugeAdjoint_complexGaugeDirection hh
  · simpa using linearizedEquation_complexGaugeDirection_apply_zero hh
  · simpa using linearizedEquation_complexGaugeDirection_apply_one hp hq hh₁
  · simpa using linearizedEquation_complexGaugeDirection_apply_two hp hq hh₁

/-- The complexified gauge action of a `C¹` function on a field with continuous section
coordinates is continuous. -/
theorem continuous_complexGaugeDirection (hp : Continuous fun w ↦ x w 2)
    (hq : Continuous fun w ↦ x w 3) (hh : ContDiff ℝ 1 h) :
    Continuous (complexGaugeDirection x h) := by
  have hd (v : ℂ) : Continuous fun w ↦ fderiv ℝ h w v :=
    (hh.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hre : Continuous fun w ↦ (h w).re := continuous_re.comp hh.continuous
  have him : Continuous fun w ↦ (h w).im := continuous_im.comp hh.continuous
  have h₀ : Continuous fun w ↦ complexGaugeDirection x h w 0 := by
    simp only [complexGaugeDirection_apply_zero]
    exact ((continuous_im.comp (hd 1)).neg).sub (continuous_re.comp (hd I))
  have h₁ : Continuous fun w ↦ complexGaugeDirection x h w 1 := by
    simp only [complexGaugeDirection_apply_one]
    exact (continuous_re.comp (hd 1)).sub (continuous_im.comp (hd I))
  have h₂ : Continuous fun w ↦ complexGaugeDirection x h w 2 := by
    simp only [complexGaugeDirection_apply_two]
    exact (hre.mul hp).sub (him.mul hq)
  have h₃ : Continuous fun w ↦ complexGaugeDirection x h w 3 := by
    simp only [complexGaugeDirection_apply_three]
    exact (hre.mul hq).add (him.mul hp)
  refine contDiff_zero.mp (contDiff_euclidean.mpr fun i ↦ contDiff_zero.mpr ?_)
  fin_cases i
  exacts [h₀, h₁, h₂, h₃]

end Operator

/-! ### Variations divisible by the section -/

section Divisible

variable {x y : ℂ → EuclideanSpace ℝ (Fin 4)} {h : ℂ → ℂ}

/-- **Recovering a variation from its section part.** At a point where the two holomorphicity rows
of the vortex equation hold and `α ≠ 0`, a variation `y` satisfying the two holomorphicity rows of
`d₁ y = 0`, whose section variation is `δα = h α` near the point, agrees there with the
complexified gauge direction of `h`. -/
theorem apply_eq_complexGaugeDirection_of_sectionValue_eq_mul {z : ℂ}
    (hp : DifferentiableAt ℝ (fun w ↦ x w 2) z) (hq : DifferentiableAt ℝ (fun w ↦ x w 3) z)
    (hh : DifferentiableAt ℝ h z) (hsol₁ : equation x z 1 = 0) (hsol₂ : equation x z 2 = 0)
    (hy₁ : linearizedEquation x y z 1 = 0) (hy₂ : linearizedEquation x y z 2 = 0)
    (hα : ∀ᶠ w in 𝓝 z, sectionValue y w = h w * sectionValue x w)
    (hz : sectionValue x z ≠ 0) :
    y z = complexGaugeDirection x h z := by
  -- The section coordinates of `y` and of the complexified gauge direction agree near `z`.
  have h₂ : (fun w ↦ y w 2) =ᶠ[𝓝 z] fun w ↦ complexGaugeDirection x h w 2 := by
    filter_upwards [hα] with w hw
    have := congrArg Complex.re hw
    simp [sectionValue_apply] at this
    simp only [complexGaugeDirection_apply_two]
    linarith
  have h₃ : (fun w ↦ y w 3) =ᶠ[𝓝 z] fun w ↦ complexGaugeDirection x h w 3 := by
    filter_upwards [hα] with w hw
    have := congrArg Complex.im hw
    simp [sectionValue_apply] at this
    simp only [complexGaugeDirection_apply_three]
    linarith
  have e₁ := linearizedEquation_complexGaugeDirection_apply_one hp hq hh
  have e₂ := linearizedEquation_complexGaugeDirection_apply_two hp hq hh
  rw [hsol₁, hsol₂] at e₁ e₂
  have hv₂ : y z 2 = complexGaugeDirection x h z 2 := h₂.self_of_nhds
  have hv₃ : y z 3 = complexGaugeDirection x h z 3 := h₃.self_of_nhds
  rw [linearizedEquation_apply_one, ← h₂.fderiv_eq, ← h₃.fderiv_eq] at e₁
  rw [linearizedEquation_apply_two, ← h₂.fderiv_eq, ← h₃.fderiv_eq] at e₂
  rw [linearizedEquation_apply_one, hv₂, hv₃] at hy₁
  rw [linearizedEquation_apply_two, hv₂, hv₃] at hy₂
  -- The differences `a, b` of the connection coordinates solve a system of determinant `p² + q²`.
  have hP : x z 2 ^ 2 + x z 3 ^ 2 ≠ 0 := (sectionValue_eq_zero_iff x z).not.mp hz
  set a := y z 0 - complexGaugeDirection x h z 0
  set b := y z 1 - complexGaugeDirection x h z 1
  have ha : a * (x z 2 ^ 2 + x z 3 ^ 2) = 0 := by
    simp only [mul_zero, sub_zero] at e₁ e₂
    linear_combination (-x z 3) * (hy₁ - e₁) + x z 2 * (hy₂ - e₂)
  have hb : b * (x z 2 ^ 2 + x z 3 ^ 2) = 0 := by
    simp only [mul_zero, sub_zero] at e₁ e₂
    linear_combination (-x z 2) * (hy₁ - e₁) - x z 3 * (hy₂ - e₂)
  have ha₀ : a = 0 := (mul_eq_zero.mp ha).resolve_right hP
  have hb₀ : b = 0 := (mul_eq_zero.mp hb).resolve_right hP
  ext i
  fin_cases i
  · exact sub_eq_zero.mp ha₀
  · exact sub_eq_zero.mp hb₀
  · exact hv₂
  · exact hv₃

/-- **Variations with section variation divisible by `α`.** Let `x` satisfy the holomorphicity rows
of the vortex equation, with zeros of `α` of empty interior. A continuous variation `y` satisfying
the holomorphicity rows of `d₁ y = 0`, whose section variation is `δα = h α` for a `C¹` function
`h`, is the complexified gauge direction of `h`. -/
theorem eq_complexGaugeDirection_of_forall_sectionValue_eq_mul
    (hp : Differentiable ℝ (fun w ↦ x w 2)) (hq : Differentiable ℝ (fun w ↦ x w 3))
    (hhol : ∀ z, equation x z 1 = 0 ∧ equation x z 2 = 0)
    (hdense : Dense {z | sectionValue x z ≠ 0}) (hy : Continuous y) (hh : ContDiff ℝ 1 h)
    (hker : ∀ z, linearizedEquation x y z 1 = 0 ∧ linearizedEquation x y z 2 = 0)
    (hα : ∀ z, sectionValue y z = h z * sectionValue x z) :
    y = complexGaugeDirection x h :=
  hy.ext_on hdense
    (continuous_complexGaugeDirection hp.continuous hq.continuous hh) fun z hz ↦
    apply_eq_complexGaugeDirection_of_sectionValue_eq_mul (hp z) (hq z)
      (hh.differentiable one_ne_zero z) (hhol z).1 (hhol z).2 (hker z).1 (hker z).2
      (Eventually.of_forall hα) hz

/-- A function whose product with the section of a field with unit-modulus end is square
integrable is itself square integrable, when it is continuous. -/
private theorem integrable_norm_sq_of_memLp_sectionValue_mul {μ : Measure ℂ}
    [μ.IsAddHaarMeasure]
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    (hy₂ : MemLp y 2 μ) (hh : Continuous h)
    (hα : ∀ z, sectionValue y z = h z * sectionValue x z) :
    Integrable (fun z ↦ ‖h z‖ ^ 2) μ := by
  obtain ⟨K, hK, hKs⟩ := mem_cocompact.mp
    (hlim.eventually (lt_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1)))
  have hy : Integrable (fun z ↦ ‖y z‖ ^ 2) μ :=
    (memLp_two_iff_integrable_sq_norm hy₂.aestronglyMeasurable).mp hy₂
  have hK' : Integrable (K.indicator fun z ↦ ‖h z‖ ^ 2) μ :=
    ((hh.norm.pow 2).continuousOn.integrableOn_compact hK).integrable_indicator
      hK.measurableSet
  refine ((hy.const_mul 8).add hK').mono' (hh.norm.pow 2).aestronglyMeasurable
    (ae_of_all _ fun z ↦ ?_)
  rw [Real.norm_of_nonneg (by positivity), Pi.add_apply]
  by_cases hz : z ∈ K
  · rw [Set.indicator_of_mem hz]
    nlinarith [sq_nonneg ‖y z‖]
  · rw [Set.indicator_of_notMem hz]
    have hz' : 1 / 2 < 4 * (x z 2 ^ 2 + x z 3 ^ 2) := hKs hz
    -- `|h|² |α|² = |δα|² ≤ 4 |y|²` and `|α|² > 1 / 2`.
    have he : ‖h z‖ ^ 2 * (4 * (x z 2 ^ 2 + x z 3 ^ 2)) = ‖sectionValue y z‖ ^ 2 := by
      rw [hα, norm_mul, mul_pow, sq_norm_sectionValue]
    have hs : ‖sectionValue y z‖ ^ 2 ≤ 4 * ‖y z‖ ^ 2 := by
      rw [sq_norm_sectionValue, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_four]
      nlinarith [sq_nonneg (y z 0), sq_nonneg (y z 1)]
    nlinarith [sq_nonneg ‖h z‖]

/-- **Kernel elements divisible by the section vanish.** At a `C¹` plane vortex with
`|α| → 1` at infinity, a continuous square-integrable solution `y` of `L_x y = 0` whose section
variation is `δα = h α` for a `C²` function `h` is zero. No decay rate is assumed. -/
theorem eq_zero_of_memLp_of_gaugeFixedOperator_eq_zero_of_sectionValue_eq_mul
    {μ : Measure ℂ} [μ.IsAddHaarMeasure]
    (hx : ContDiff ℝ 1 x) (hsol : ∀ z, equation x z = 0)
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    (hy : Continuous y) (hy₂ : MemLp y 2 μ) (hh : ContDiff ℝ 2 h)
    (hker : ∀ z, gaugeFixedOperator x y z = 0)
    (hα : ∀ z, sectionValue y z = h z * sectionValue x z) : y = 0 := by
  have hxi (i : Fin 4) : ContDiff ℝ 1 fun z ↦ x z i := contDiff_euclidean.mp hx i
  have hp : Differentiable ℝ fun z ↦ x z 2 := (hxi 2).differentiable one_ne_zero
  have hq : Differentiable ℝ fun z ↦ x z 3 := (hxi 3).differentiable one_ne_zero
  have hhol (z : ℂ) : equation x z 1 = 0 ∧ equation x z 2 = 0 := by simp [hsol z]
  -- The zeros of `α` are finite, so their complement is dense.
  have hdense : Dense {z | sectionValue x z ≠ 0} :=
    (dense_univ.sdiff_finite (finite_setOfPred_sectionValue_eq_zero (k := 1) le_rfl (hxi 0)
      (hxi 1) hp hq hhol hlim)).mono fun z hz ↦ by simpa using hz
  have hker' (z : ℂ) : linearizedEquation x y z 1 = 0 ∧ linearizedEquation x y z 2 = 0 := by
    have h₂ := congrArg (fun v ↦ v 2) (hker z)
    have h₃ := congrArg (fun v ↦ v 3) (hker z)
    simp only [gaugeFixedOperator_apply_two, gaugeFixedOperator_apply_three,
      PiLp.zero_apply] at h₂ h₃
    exact ⟨h₂, h₃⟩
  have hyh := eq_complexGaugeDirection_of_forall_sectionValue_eq_mul hp hq hhol hdense hy
    (hh.of_le (by norm_num)) hker' hα
  -- The two gauge-type rows of `L_x y = 0` say `Δ h = P h`, so `|h|²` is subharmonic.
  have hΔ (z : ℂ) : Δ h z = (x z 2 ^ 2 + x z 3 ^ 2) • h z := by
    have hL := gaugeFixedOperator_complexGaugeDirection (hp z) (hq z) hh.contDiffAt
    rw [← hyh, hker z] at hL
    have h₀ := congrArg (fun v ↦ v 0) hL
    have h₁ := congrArg (fun v ↦ v 1) hL
    simp only [PiLp.zero_apply] at h₀ h₁
    simp at h₀ h₁
    rw [← sub_eq_zero]
    apply Complex.ext <;> simp <;> linarith
  have hsub (z : ℂ) : 0 ≤ Δ (fun w ↦ ‖h w‖ ^ 2) z := by
    rw [hh.contDiffAt.laplacian_norm_sq orthonormalBasisOneI, hΔ, real_inner_smul_right,
      real_inner_self_eq_norm_sq]
    positivity
  have hnorm := eq_zero_of_integrable_of_nonneg_of_laplacian_nonneg (μ := μ) (hh.norm_sq ℝ)
    (integrable_norm_sq_of_memLp_sectionValue_mul hlim hy₂ hh.continuous hα)
    (fun z ↦ sq_nonneg ‖h z‖) hsub
  have h₀ : h = 0 := funext fun z ↦
    norm_eq_zero.mp (sq_eq_zero_iff.mp (by simpa using congrFun hnorm z))
  rw [hyh, h₀, complexGaugeDirection_zero]

/-- **The kernel of `L_x` at a vortex without zeros.** At a `C²` plane vortex whose section has no
zeros and tends to unit modulus at infinity, every `C²` square-integrable solution of `L_x y = 0`
vanishes. -/
theorem eq_zero_of_memLp_of_gaugeFixedOperator_eq_zero_of_sectionValue_ne_zero
    {μ : Measure ℂ} [μ.IsAddHaarMeasure]
    (hx : ContDiff ℝ 2 x) (hsol : ∀ z, equation x z = 0)
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    (hne : ∀ z, sectionValue x z ≠ 0) (hy : ContDiff ℝ 2 y) (hy₂ : MemLp y 2 μ)
    (hker : ∀ z, gaugeFixedOperator x y z = 0) : y = 0 := by
  have hxi (i : Fin 4) : ContDiff ℝ 2 fun z ↦ x z i := contDiff_euclidean.mp hx i
  have hyi (i : Fin 4) : ContDiff ℝ 2 fun z ↦ y z i := contDiff_euclidean.mp hy i
  refine eq_zero_of_memLp_of_gaugeFixedOperator_eq_zero_of_sectionValue_eq_mul
    (h := fun z ↦ sectionValue y z * (sectionValue x z)⁻¹) (hx.of_le (by norm_num)) hsol hlim
    hy.continuous hy₂ ((contDiff_sectionValue (hyi 2) (hyi 3)).mul
      ((contDiff_sectionValue (hxi 2) (hxi 3)).inv hne)) hker fun z ↦ ?_
  rw [inv_mul_cancel_right₀ (hne z)]

end Divisible

end TauCeti.Vortex
