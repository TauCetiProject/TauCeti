/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.Gauge.Fixed
public import TauCeti.Analysis.Complex.Wirtinger.Basic
public import Mathlib.MeasureTheory.Function.L2Space
public import TauCeti.Analysis.Distribution.Sobolev
import Mathlib.MeasureTheory.SpecificCodomains.WithLp
import Mathlib.Topology.Algebra.Module.Cardinality
import TauCeti.Analysis.Sobolev.BesselPotential.Basic
import TauCeti.Analysis.InnerProductSpace.Laplacian.Liouville
import TauCeti.Analysis.PDE.Vortex.Zeros

/-!
# The logarithmic variations of a plane vortex

A field `x = (b₁, b₂, p, q)` represents `a = i (b₁ ds + b₂ dt)` and `α = 2 (p + i q)`; write
`φ = α / 2` and `P = |φ|² = p² + q²`. For a complex function `η`, the **logarithmic variation**
`logVariation x η` is the variation `(δa, δα)` with

`δα = α η`,  `δb₁ + i δb₂ = 2 i ∂bar η`,

so that `η = δα / α` wherever `α ≠ 0`. Following Samols and Taubes, these variations reduce the
kernel of the gauge-fixed operator `L_x = d₀* ⊕ d₁` of a vortex to the scalar Schrödinger
equation `Δη = P η`.

* `logVariation_add`, `logVariation_smul`, `logVariation_sub`: the logarithmic variation is
  real-linear in differentiable `η` (pointwise: `logVariation_add_apply`).
* `logVariation_congr_nhds`, `contDiff_logVariation`: it is local in `η`, and `Cⁿ` along a `Cⁿ`
  field when `η` is `Cⁿ⁺¹`.
* `logVariation_apply_zero_eq_zero_of_differentiableAt`,
  `logVariation_apply_one_eq_zero_of_differentiableAt`: the connection part vanishes where `η` is
  holomorphic.
* `memLp_logVariation`: it is square integrable when `η` and `Dη` are, along a field with bounded
  section components.
* `memLp_logVariation_of_mem_realSobolevFunctions`: square integrability for a `C¹` function
  `η ∈ H²(ℂ; ℂ)` along a field with bounded section.
* `logVariation_eq_of_differentiableAt`: where `η` is holomorphic, the logarithmic variation is
  the variation of the section alone by `α η`.
* `gaugeFixedOperator_logVariation`: at every field, writing `E = ∂bar_a α` for the complex
  holomorphicity defect (the rows `1` and `2` of `equation x`),
  `L_x (logVariation x η) = (Im (P η - Δη), Re (P η - Δη), Re (η E), Im (η E))`.
  Only the holomorphicity rows of the vortex equation enter; the curvature row does not.
* `gaugeFixedOperator_logVariation_eq_zero_iff`: hence where `∂bar_a α = 0`, the logarithmic
  variation of `η` lies in the kernel of `L_x` exactly when `Δη = P η`.
* `apply_eq_logVariation_div_apply`: conversely, where `∂bar_a α = 0` and `α ≠ 0`, the two
  `∂bar` rows of `L_x y = 0` force `y` to be the logarithmic variation of `η = δα / α`.
* `laplacian_div_sectionValue_eq_smul`: hence on the open set where `α ≠ 0`, every `C²` kernel
  element of `L_x` at a `C²` field with `∂bar_a α = 0` is given by a solution `η = δα / α` of
  `Δη = P η`.
* `eq_zero_of_gaugeFixedOperator_eq_zero_of_sectionValue_eq_mul`: a kernel element whose section
  variation is `δα = α η` for a global `C²` function `η` in `L²` is zero, provided the zeros of
  `α` have dense complement. Indeed `Δ |η|² = 2 |∇η|² + 2 P |η|² ≥ 0`.
* `eq_zero_of_gaugeFixedOperator_eq_zero_of_sectionValue_eq_mul_of_tendsto`: the same for an
  `L²` kernel element of a vortex with `|α| → 1` at infinity, where the integrability of `η` and
  the density follow.

Since `η = δα / α`, the function `η` of a kernel element is in general singular at the zeros of
`α`: the covariant translations of `TauCeti.Analysis.PDE.Vortex.TranslationKernel`, which move
the zeros, have `η = ∇_v α / α` with poles there. The last two theorems say that, at a field
`x` whose holomorphicity rows vanish everywhere, a continuous kernel element `y` vanishes if
`δα / α` extends to a `C²` function `η` with `η ∈ L²`; for a framed vortex (`x` of class `C¹`
with `|α|² → 1` at infinity) it suffices that `y ∈ L²`, which gives `η ∈ L²`. By linearity of
`L_x`, two continuous `L²` kernel elements of such a framed vortex agree once their quotients
`δα / α` differ by a `C²` function, so such a kernel element is determined by the singular part
of `δα / α` at the zeros of `α`. This is the vanishing step behind the injectivity half of the
identification of the kernel of `L_x` with the tangent space of the divisor space `Sym^m ℂ`
through the principal parts of `δα / α`. The principal-part map itself, which needs the local
structure of `δα / α` at a zero of `α`, is in `TauCeti.Analysis.PDE.Vortex.PrincipalPart`.
Kernel elements with prescribed principal parts are constructed in
`TauCeti.Analysis.PDE.Vortex.KernelExistence`, `TauCeti.Analysis.PDE.Vortex.ZeroMode` and
`TauCeti.Analysis.PDE.Vortex.TangentKernel`.

## References

* T. M. Samols, *Vortex scattering*, Comm. Math. Phys. 145 (1992), 149–179.
* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III.
-/

public section

noncomputable section

namespace TauCeti.Vortex

open Complex Filter MeasureTheory Set TemperedDistribution
open scoped Laplacian Topology

/-- The **logarithmic variation** of a field `x` along a complex function `η`: the variation
`(δa, δα)` with section variation `δα = α η` and connection variation
`δb₁ + i δb₂ = 2 i ∂bar η`, in the real coordinates of `TauCeti.Vortex.equation`. Where `α ≠ 0`,
`η = δα / α`. See `sectionValue_logVariation` and `logVariation_zero_add_one_mul_I`. -/
def logVariation (x : ℂ → EuclideanSpace ℝ (Fin 4)) (η : ℂ → ℂ) (z : ℂ) :
    EuclideanSpace ℝ (Fin 4) :=
  !₂[-fderiv ℝ (fun w ↦ (η w).im) z 1 - fderiv ℝ (fun w ↦ (η w).re) z I,
    fderiv ℝ (fun w ↦ (η w).re) z 1 - fderiv ℝ (fun w ↦ (η w).im) z I,
    x z 2 * (η z).re - x z 3 * (η z).im, x z 2 * (η z).im + x z 3 * (η z).re]

/-- The first connection component of the logarithmic variation. -/
@[simp]
theorem logVariation_apply_zero (x : ℂ → EuclideanSpace ℝ (Fin 4)) (η : ℂ → ℂ) (z : ℂ) :
    logVariation x η z 0 =
      -fderiv ℝ (fun w ↦ (η w).im) z 1 - fderiv ℝ (fun w ↦ (η w).re) z I :=
  (rfl)

/-- The second connection component of the logarithmic variation. -/
@[simp]
theorem logVariation_apply_one (x : ℂ → EuclideanSpace ℝ (Fin 4)) (η : ℂ → ℂ) (z : ℂ) :
    logVariation x η z 1 =
      fderiv ℝ (fun w ↦ (η w).re) z 1 - fderiv ℝ (fun w ↦ (η w).im) z I :=
  (rfl)

/-- The real section component of the logarithmic variation. -/
@[simp]
theorem logVariation_apply_two (x : ℂ → EuclideanSpace ℝ (Fin 4)) (η : ℂ → ℂ) (z : ℂ) :
    logVariation x η z 2 = x z 2 * (η z).re - x z 3 * (η z).im :=
  (rfl)

/-- The imaginary section component of the logarithmic variation. -/
@[simp]
theorem logVariation_apply_three (x : ℂ → EuclideanSpace ℝ (Fin 4)) (η : ℂ → ℂ) (z : ℂ) :
    logVariation x η z 3 = x z 2 * (η z).im + x z 3 * (η z).re :=
  (rfl)

/-- The section variation of the logarithmic variation of `η` is `α η`. -/
@[simp]
theorem sectionValue_logVariation (x : ℂ → EuclideanSpace ℝ (Fin 4)) (η : ℂ → ℂ) (z : ℂ) :
    sectionValue (logVariation x η) z = sectionValue x z * η z := by
  apply Complex.ext <;> simp [sectionValue_apply] <;> ring

/-- The connection variation of the logarithmic variation of a differentiable `η` is
`δb₁ + i δb₂ = 2 i ∂bar η`. -/
theorem logVariation_zero_add_one_mul_I (x : ℂ → EuclideanSpace ℝ (Fin 4)) {η : ℂ → ℂ} {z : ℂ}
    (hη : DifferentiableAt ℝ η z) :
    (logVariation x η z 0 : ℂ) + logVariation x η z 1 * I =
      2 * I * conjWirtingerDeriv η z 1 := by
  have hre (v : ℂ) : fderiv ℝ (fun w ↦ (η w).re) z v = (fderiv ℝ η z v).re :=
    congrArg (fun L : ℂ →L[ℝ] ℝ ↦ L v) (reCLM.hasFDerivAt.comp z hη.hasFDerivAt).fderiv
  have him (v : ℂ) : fderiv ℝ (fun w ↦ (η w).im) z v = (fderiv ℝ η z v).im :=
    congrArg (fun L : ℂ →L[ℝ] ℝ ↦ L v) (imCLM.hasFDerivAt.comp z hη.hasFDerivAt).fderiv
  rw [conjWirtingerDeriv_apply]
  apply Complex.ext <;> simp [hre, him] <;> ring

/-- Where `η` is holomorphic, the connection variation `2 i ∂bar η` of its logarithmic variation
vanishes. -/
private theorem logVariation_zero_add_one_mul_I_eq_zero (x : ℂ → EuclideanSpace ℝ (Fin 4))
    {η : ℂ → ℂ} {z : ℂ} (hη : DifferentiableAt ℂ η z) :
    (logVariation x η z 0 : ℂ) + logVariation x η z 1 * I = 0 := by
  rw [logVariation_zero_add_one_mul_I x (hη.restrictScalars ℝ), hη.conjWirtingerDeriv_eq_zero,
    _root_.zero_apply, mul_zero]

/-- The first connection component of the logarithmic variation vanishes where `η` is
holomorphic. -/
theorem logVariation_apply_zero_eq_zero_of_differentiableAt (x : ℂ → EuclideanSpace ℝ (Fin 4))
    {η : ℂ → ℂ} {z : ℂ} (hη : DifferentiableAt ℂ η z) : logVariation x η z 0 = 0 := by
  simpa using congrArg re (logVariation_zero_add_one_mul_I_eq_zero x hη)

/-- The second connection component of the logarithmic variation vanishes where `η` is
holomorphic. -/
theorem logVariation_apply_one_eq_zero_of_differentiableAt (x : ℂ → EuclideanSpace ℝ (Fin 4))
    {η : ℂ → ℂ} {z : ℂ} (hη : DifferentiableAt ℂ η z) : logVariation x η z 1 = 0 := by
  simpa using congrArg im (logVariation_zero_add_one_mul_I_eq_zero x hη)

/-- Where `η` is holomorphic, its logarithmic variation is the variation of the section alone
by `α η`, with no connection part. -/
theorem logVariation_eq_of_differentiableAt (x : ℂ → EuclideanSpace ℝ (Fin 4)) {η : ℂ → ℂ}
    {z : ℂ} (hη : DifferentiableAt ℂ η z) :
    logVariation x η z = sectionVariation (fun w ↦ sectionValue x w * η w) z := by
  refine apply_eq_of_sectionValue_eq ?_ ?_ ?_
  · simpa using logVariation_apply_zero_eq_zero_of_differentiableAt x hη
  · simpa using logVariation_apply_one_eq_zero_of_differentiableAt x hη
  · rw [sectionValue_logVariation, sectionValue_sectionVariation]

/-- The logarithmic variation of a `C¹` function `η ∈ H²(ℂ; ℂ)` along a field with bounded section
is square integrable: its connection part consists of first derivatives of `η`, and its section
part `α η` has a bounded factor `α`. -/
theorem memLp_logVariation_of_mem_realSobolevFunctions {x : ℂ → EuclideanSpace ℝ (Fin 4)}
    (hx₂ : MemLp (fun z ↦ x z 2) ⊤ volume) (hx₃ : MemLp (fun z ↦ x z 3) ⊤ volume) {η : ℂ → ℂ}
    (hη : ContDiff ℝ 1 η) (hre : (fun z ↦ (η z).re) ∈ realSobolevFunctions ℂ 2 2)
    (him : (fun z ↦ (η z).im) ∈ realSobolevFunctions ℂ 2 2) :
    MemLp (logVariation x η) 2 volume := by
  have hd (f : ℂ → ℝ) (hf : ContDiff ℝ 1 f) (hf2 : f ∈ realSobolevFunctions ℂ 2 2) (v : ℂ) :
      MemLp (fun z ↦ fderiv ℝ f z v) 2 volume := by
    refine memLp_of_mem_realSobolevFunctions (s := 1)
      (fderiv_apply_mem_realSobolevFunctions (by norm_num) (by simp) zero_le_one hf ?_ v)
    norm_num
    exact hf2
  have hu : ContDiff ℝ 1 (fun z ↦ (η z).re) := reCLM.contDiff.comp hη
  have hv : ContDiff ℝ 1 (fun z ↦ (η z).im) := imCLM.contDiff.comp hη
  have hu2 := memLp_of_mem_realSobolevFunctions hre
  have hv2 := memLp_of_mem_realSobolevFunctions him
  refine MemLp.of_eval_piLp fun i ↦ ?_
  fin_cases i
  · exact ((hd _ hv him 1).neg.sub (hd _ hu hre I)).ae_eq (ae_of_all _ fun z ↦ by simp)
  · exact ((hd _ hu hre 1).sub (hd _ hv him I)).ae_eq (ae_of_all _ fun z ↦ by simp)
  · exact ((hx₂.mul hu2 : MemLp (fun z ↦ x z 2 * (η z).re) 2 volume).sub
      (hx₃.mul hv2 : MemLp (fun z ↦ x z 3 * (η z).im) 2 volume)).ae_eq
      (ae_of_all _ fun z ↦ by simp)
  · exact ((hx₂.mul hv2 : MemLp (fun z ↦ x z 2 * (η z).im) 2 volume).add
      (hx₃.mul hu2 : MemLp (fun z ↦ x z 3 * (η z).re) 2 volume)).ae_eq
      (ae_of_all _ fun z ↦ by simp)

/-- The two `∂bar` rows of `L_x` on a logarithmic variation: they are the real and imaginary
parts of `η E`, where `E` is the complex holomorphicity defect of `x` (rows `1` and `2` of
`equation x`). This only needs first derivatives of `x` and `η`. -/
theorem gaugeFixedOperator_logVariation_two_three {x : ℂ → EuclideanSpace ℝ (Fin 4)}
    {η : ℂ → ℂ} {z : ℂ} (hx : DifferentiableAt ℝ x z) (hη : DifferentiableAt ℝ η z) :
    gaugeFixedOperator x (logVariation x η) z 2 =
        equation x z 1 * (η z).re - equation x z 2 * (η z).im ∧
      gaugeFixedOperator x (logVariation x η) z 3 =
        equation x z 2 * (η z).re + equation x z 1 * (η z).im := by
  have hxi (i : Fin 4) : DifferentiableAt ℝ (fun w ↦ x w i) z :=
    ((EuclideanSpace.proj (𝕜 := ℝ) i).differentiableAt.comp z hx :)
  have hu : DifferentiableAt ℝ (fun w ↦ (η w).re) z := reCLM.differentiableAt.comp z hη
  have hv : DifferentiableAt ℝ (fun w ↦ (η w).im) z := imCLM.differentiableAt.comp z hη
  have hd₂ (v : ℂ) : fderiv ℝ (fun w ↦ x w 2 * (η w).re - x w 3 * (η w).im) z v =
      fderiv ℝ (fun w ↦ x w 2) z v * (η z).re + x z 2 * fderiv ℝ (fun w ↦ (η w).re) z v -
        (fderiv ℝ (fun w ↦ x w 3) z v * (η z).im +
          x z 3 * fderiv ℝ (fun w ↦ (η w).im) z v) := by
    rw [(((hxi 2).hasFDerivAt.fun_mul hu.hasFDerivAt).fun_sub
      ((hxi 3).hasFDerivAt.fun_mul hv.hasFDerivAt)).fderiv]
    simp only [sub_apply, add_apply, smul_apply, smul_eq_mul]
    ring
  have hd₃ (v : ℂ) : fderiv ℝ (fun w ↦ x w 2 * (η w).im + x w 3 * (η w).re) z v =
      fderiv ℝ (fun w ↦ x w 2) z v * (η z).im + x z 2 * fderiv ℝ (fun w ↦ (η w).im) z v +
        (fderiv ℝ (fun w ↦ x w 3) z v * (η z).re +
          x z 3 * fderiv ℝ (fun w ↦ (η w).re) z v) := by
    rw [(((hxi 2).hasFDerivAt.fun_mul hv.hasFDerivAt).fun_add
      ((hxi 3).hasFDerivAt.fun_mul hu.hasFDerivAt)).fderiv]
    simp only [add_apply, smul_apply, smul_eq_mul]
    ring
  simp only [gaugeFixedOperator_apply_two, gaugeFixedOperator_apply_three,
    linearizedEquation_apply_one, linearizedEquation_apply_two, equation_apply_one,
    equation_apply_two, hd₂, hd₃, logVariation_apply_zero, logVariation_apply_one,
    logVariation_apply_two, logVariation_apply_three]
  constructor <;> ring

/-- **The gauge-fixed operator on logarithmic variations.** At every field `x`, with
`P = p² + q² = |α|² / 4` and `E` the complex holomorphicity defect of `x` (rows `1` and `2` of
`equation x`),

`L_x (logVariation x η) = (Im (P η - Δη), Re (P η - Δη), Re (η E), Im (η E))`.

The curvature row of `equation x` does not enter. -/
theorem gaugeFixedOperator_logVariation {x : ℂ → EuclideanSpace ℝ (Fin 4)} {η : ℂ → ℂ} {z : ℂ}
    (hx : DifferentiableAt ℝ x z) (hη : ContDiffAt ℝ 2 η z) :
    gaugeFixedOperator x (logVariation x η) z =
      !₂[(x z 2 ^ 2 + x z 3 ^ 2) * (η z).im - (Δ η z).im,
        (x z 2 ^ 2 + x z 3 ^ 2) * (η z).re - (Δ η z).re,
        equation x z 1 * (η z).re - equation x z 2 * (η z).im,
        equation x z 2 * (η z).re + equation x z 1 * (η z).im] := by
  obtain ⟨h₂, h₃⟩ := gaugeFixedOperator_logVariation_two_three hx
    (hη.differentiableAt (by norm_num))
  have hu : ContDiffAt ℝ 2 (fun w ↦ (η w).re) z := reCLM.contDiff.contDiffAt.comp z hη
  have hv : ContDiffAt ℝ 2 (fun w ↦ (η w).im) z := imCLM.contDiff.contDiffAt.comp z hη
  have hdu : DifferentiableAt ℝ (fderiv ℝ (fun w ↦ (η w).re)) z :=
    (hu.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hdv : DifferentiableAt ℝ (fderiv ℝ (fun w ↦ (η w).im)) z :=
    (hv.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  -- Second partial derivatives of the real and imaginary parts, and their symmetry.
  have hd (f : ℂ → ℝ) (hf : DifferentiableAt ℝ (fderiv ℝ f) z) (a b : ℂ) :
      fderiv ℝ (fun w ↦ fderiv ℝ f w a) z b = fderiv ℝ (fderiv ℝ f) z b a := by
    rw [fderiv_clm_apply hf (differentiableAt_const a)]
    simp
  have hsu := (hu.isSymmSndFDerivAt (by simp)).eq 1 I
  have hsv := (hv.isSymmSndFDerivAt (by simp)).eq 1 I
  have hΔre : (Δ η z).re = Δ (fun w ↦ (η w).re) z :=
    (hη.laplacian_CLM_comp_left (l := reCLM)).symm
  have hΔim : (Δ η z).im = Δ (fun w ↦ (η w).im) z :=
    (hη.laplacian_CLM_comp_left (l := imCLM)).symm
  have hdiff (f g : ℂ → ℝ) (hf : DifferentiableAt ℝ (fderiv ℝ f) z)
      (hg : DifferentiableAt ℝ (fderiv ℝ g) z) (a b c : ℂ) (s t : ℝ) :
      fderiv ℝ (fun w ↦ s * fderiv ℝ f w a + t * fderiv ℝ g w b) z c =
        s * fderiv ℝ (fderiv ℝ f) z c a + t * fderiv ℝ (fderiv ℝ g) z c b := by
    have hfa : DifferentiableAt ℝ (fun w ↦ fderiv ℝ f w a) z :=
      hf.clm_apply (differentiableAt_const a)
    have hgb : DifferentiableAt ℝ (fun w ↦ fderiv ℝ g w b) z :=
      hg.clm_apply (differentiableAt_const b)
    rw [fderiv_fun_add (hfa.const_mul s) (hgb.const_mul t), fderiv_const_mul hfa,
      fderiv_const_mul hgb]
    simp [hd f hf, hd g hg]
  have h₀ : (fun w ↦ logVariation x η w 0) = fun w ↦
      (-1) * fderiv ℝ (fun w ↦ (η w).im) w 1 + (-1) * fderiv ℝ (fun w ↦ (η w).re) w I := by
    funext w
    simp only [logVariation_apply_zero]
    ring
  have h₁ : (fun w ↦ logVariation x η w 1) = fun w ↦
      1 * fderiv ℝ (fun w ↦ (η w).re) w 1 + (-1) * fderiv ℝ (fun w ↦ (η w).im) w I := by
    funext w
    simp only [logVariation_apply_one]
    ring
  -- In rows `0` and `1` the mixed partials of `η` cancel, leaving `P η - Δη`.
  ext i
  fin_cases i
  · simp only [Fin.zero_eta, Fin.isValue, gaugeFixedOperator_apply_zero, gaugeAdjoint_def, h₀,
      h₁, hdiff _ _ hdv hdu, hdiff _ _ hdu hdv, logVariation_apply_two, logVariation_apply_three,
      hΔim, laplacian_eq_sum_fderiv_fderiv_apply orthonormalBasisOneI hdv, Fin.sum_univ_two,
      coe_orthonormalBasisOneI, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, hd _ hdv]
    linear_combination -hsu
  · simp only [Fin.mk_one, Fin.isValue, gaugeFixedOperator_apply_one,
      linearizedEquation_apply_zero, h₀, h₁, hdiff _ _ hdv hdu, hdiff _ _ hdu hdv,
      logVariation_apply_two, logVariation_apply_three, hΔre,
      laplacian_eq_sum_fderiv_fderiv_apply orthonormalBasisOneI hdu, Fin.sum_univ_two,
      coe_orthonormalBasisOneI, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, hd _ hdu]
    linear_combination hsv
  · simpa using h₂
  · simpa using h₃

/-- **Logarithmic variations in the kernel.** Where the holomorphicity rows of the vortex
equation hold, the logarithmic variation of a `C²` function `η` lies in the kernel of `L_x`
exactly when `η` solves the Schrödinger equation `Δη = P η`, `P = p² + q² = |α|² / 4`. -/
theorem gaugeFixedOperator_logVariation_eq_zero_iff {x : ℂ → EuclideanSpace ℝ (Fin 4)}
    {η : ℂ → ℂ} {z : ℂ} (hx : DifferentiableAt ℝ x z) (hη : ContDiffAt ℝ 2 η z)
    (h₁ : equation x z 1 = 0) (h₂ : equation x z 2 = 0) :
    gaugeFixedOperator x (logVariation x η) z = 0 ↔ Δ η z = (x z 2 ^ 2 + x z 3 ^ 2) • η z := by
  rw [gaugeFixedOperator_logVariation hx hη, h₁, h₂, Complex.ext_iff, Complex.smul_re,
    Complex.smul_im, smul_eq_mul, smul_eq_mul]
  constructor
  · intro h
    have h₀ := congrArg (fun v ↦ v 0) h
    have h₁ := congrArg (fun v ↦ v 1) h
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, PiLp.zero_apply] at h₀ h₁
    constructor <;> linarith
  · rintro ⟨hre, him⟩
    ext i
    fin_cases i <;> simp [hre, him]

/-- **Kernel elements off the zeros are logarithmic variations.** At a point where the
holomorphicity rows of the vortex equation hold and `α ≠ 0`, let `y` satisfy the two `∂bar` rows
of `L_x y = 0`, and let `η` be differentiable with `δα = α η` near the point. Then `y` is the
logarithmic variation of `η` there. -/
theorem apply_eq_logVariation_apply {x y : ℂ → EuclideanSpace ℝ (Fin 4)} {η : ℂ → ℂ} {z : ℂ}
    (hx : DifferentiableAt ℝ x z) (hη : DifferentiableAt ℝ η z) (hα : sectionValue x z ≠ 0)
    (hyη : ∀ᶠ w in 𝓝 z, sectionValue y w = sectionValue x w * η w)
    (h₁ : equation x z 1 = 0) (h₂ : equation x z 2 = 0)
    (hy₂ : gaugeFixedOperator x y z 2 = 0) (hy₃ : gaugeFixedOperator x y z 3 = 0) :
    y z = logVariation x η z := by
  have hs : ∀ᶠ w in 𝓝 z, sectionValue y w = sectionValue (logVariation x η) w := by
    filter_upwards [hyη] with w hw
    rw [sectionValue_logVariation, hw]
  -- Near `z` the section components of `y` and of the logarithmic variation agree.
  have hcomp (i : Fin 4) (hi : i = 2 ∨ i = 3) :
      (fun w ↦ y w i) =ᶠ[𝓝 z] fun w ↦ logVariation x η w i := by
    filter_upwards [hs] with w hw
    have hre := congrArg re hw
    have him := congrArg im hw
    simp only [sectionValue_apply, mul_re, mul_im, add_re, add_im, ofReal_re, ofReal_im, I_re,
      I_im, re_ofNat, im_ofNat] at hre him
    rcases hi with rfl | rfl <;> linarith
  obtain ⟨hl₂, hl₃⟩ := gaugeFixedOperator_logVariation_two_three hx hη
  rw [h₁, h₂] at hl₂ hl₃
  have hv₂ := (hcomp 2 (by simp)).self_of_nhds
  have hv₃ := (hcomp 3 (by simp)).self_of_nhds
  have hd₂ := (hcomp 2 (by simp)).fderiv_eq (𝕜 := ℝ)
  have hd₃ := (hcomp 3 (by simp)).fderiv_eq (𝕜 := ℝ)
  simp only [gaugeFixedOperator_apply_two, gaugeFixedOperator_apply_three,
    linearizedEquation_apply_one, linearizedEquation_apply_two] at hy₂ hy₃ hl₂ hl₃
  simp only at hv₂ hv₃
  rw [hd₂, hd₃, hv₂, hv₃] at hy₂ hy₃
  -- The connection components are then forced by the two `∂bar` rows, since `p² + q² ≠ 0`.
  have hP : x z 2 ^ 2 + x z 3 ^ 2 ≠ 0 := by rwa [ne_eq, ← sectionValue_eq_zero_iff]
  have ha : (y z 0 - logVariation x η z 0) * (x z 2 ^ 2 + x z 3 ^ 2) = 0 := by
    linear_combination x z 2 * (hy₃ - hl₃) - x z 3 * (hy₂ - hl₂)
  have hb : (y z 1 - logVariation x η z 1) * (x z 2 ^ 2 + x z 3 ^ 2) = 0 := by
    linear_combination (-x z 3) * (hy₃ - hl₃) - x z 2 * (hy₂ - hl₂)
  refine apply_eq_of_sectionValue_eq ?_ ?_ hs.self_of_nhds
  · linarith [(mul_eq_zero.mp ha).resolve_right hP]
  · linarith [(mul_eq_zero.mp hb).resolve_right hP]

/-- At a point where the holomorphicity rows of the vortex equation hold and `α ≠ 0`, a variation
`y` satisfying the two `∂bar` rows of `L_x y = 0` is the logarithmic variation of
`η = δα / α` there. -/
theorem apply_eq_logVariation_div_apply {x y : ℂ → EuclideanSpace ℝ (Fin 4)} {z : ℂ}
    (hx : DifferentiableAt ℝ x z) (hy : DifferentiableAt ℝ y z) (hα : sectionValue x z ≠ 0)
    (h₁ : equation x z 1 = 0) (h₂ : equation x z 2 = 0)
    (hy₂ : gaugeFixedOperator x y z 2 = 0) (hy₃ : gaugeFixedOperator x y z 3 = 0) :
    y z = logVariation x (fun w ↦ sectionValue y w / sectionValue x w) z := by
  have hdα := differentiableAt_sectionValue_of_differentiableAt hx
  refine apply_eq_logVariation_apply hx
    ((differentiableAt_sectionValue_of_differentiableAt hy).mul (hdα.inv hα)) hα ?_ h₁ h₂ hy₂ hy₃
  filter_upwards [hdα.continuousAt.eventually_ne hα] with w hw
  rw [mul_div_cancel₀ _ hw]

/-- **The scalar equation of a kernel element off the zeros.** Let `x` be a `C²` field whose
holomorphicity rows vanish near `z`, with `α(z) ≠ 0`, and let `y` be a `C²` variation with
`L_x y = 0` near `z`. Then `η = δα / α` solves `Δη = P η` at `z`, `P = p² + q² = |α|² / 4`. -/
theorem laplacian_div_sectionValue_eq_smul {x y : ℂ → EuclideanSpace ℝ (Fin 4)} {z : ℂ}
    (hx : ContDiffAt ℝ 2 x z) (hy : ContDiffAt ℝ 2 y z) (hα : sectionValue x z ≠ 0)
    (hhol : ∀ᶠ w in 𝓝 z, equation x w 1 = 0 ∧ equation x w 2 = 0)
    (hker : ∀ᶠ w in 𝓝 z, gaugeFixedOperator x y w = 0) :
    Δ (fun w ↦ sectionValue y w / sectionValue x w) z =
      (x z 2 ^ 2 + x z 3 ^ 2) • (sectionValue y z / sectionValue x z) := by
  have hdα := contDiffAt_sectionValue_of_contDiffAt hx
  have hη : ContDiffAt ℝ 2 (fun w ↦ sectionValue y w / sectionValue x w) z := by
    simp_rw [div_eq_mul_inv]
    exact (contDiffAt_sectionValue_of_contDiffAt hy).mul (hdα.inv hα)
  have hrep : y =ᶠ[𝓝 z] logVariation x (fun w ↦ sectionValue y w / sectionValue x w) := by
    filter_upwards [hx.eventually (by simp), hy.eventually (by simp),
      (hdα.continuousAt.eventually_ne hα), hhol, hker] with w hxw hyw hαw hholw hkerw
    exact apply_eq_logVariation_div_apply (hxw.differentiableAt (by simp))
      (hyw.differentiableAt (by simp)) hαw hholw.1 hholw.2 (by simp [hkerw]) (by simp [hkerw])
  have hL := hker.self_of_nhds
  rw [gaugeFixedOperator_congr_nhds x hrep] at hL
  exact (gaugeFixedOperator_logVariation_eq_zero_iff (hx.differentiableAt (by simp)) hη
    hhol.self_of_nhds.1 hhol.self_of_nhds.2).mp hL

/-- The logarithmic variation of `0` is `0`. -/
@[simp]
theorem logVariation_zero (x : ℂ → EuclideanSpace ℝ (Fin 4)) : logVariation x 0 = 0 := by
  funext z
  ext i
  fin_cases i <;> simp

/-- The logarithmic variation is additive in `η` at a point where both summands are
differentiable. -/
theorem logVariation_add_apply (x : ℂ → EuclideanSpace ℝ (Fin 4)) {η ζ : ℂ → ℂ} {z : ℂ}
    (hη : DifferentiableAt ℝ η z) (hζ : DifferentiableAt ℝ ζ z) :
    logVariation x (η + ζ) z = logVariation x η z + logVariation x ζ z := by
  have hre : fderiv ℝ (fun w ↦ (η w).re + (ζ w).re) z =
      fderiv ℝ (fun w ↦ (η w).re) z + fderiv ℝ (fun w ↦ (ζ w).re) z :=
    fderiv_fun_add (reCLM.differentiableAt.comp z hη) (reCLM.differentiableAt.comp z hζ)
  have him : fderiv ℝ (fun w ↦ (η w).im + (ζ w).im) z =
      fderiv ℝ (fun w ↦ (η w).im) z + fderiv ℝ (fun w ↦ (ζ w).im) z :=
    fderiv_fun_add (imCLM.differentiableAt.comp z hη) (imCLM.differentiableAt.comp z hζ)
  ext i
  fin_cases i <;> simp [hre, him] <;> ring

/-- The logarithmic variation is additive in differentiable functions `η`. -/
theorem logVariation_add (x : ℂ → EuclideanSpace ℝ (Fin 4)) {η ζ : ℂ → ℂ}
    (hη : Differentiable ℝ η) (hζ : Differentiable ℝ ζ) :
    logVariation x (η + ζ) = logVariation x η + logVariation x ζ :=
  funext fun z ↦ logVariation_add_apply x (hη z) (hζ z)

/-- The logarithmic variation commutes with real scalar multiplication of `η`. -/
theorem logVariation_smul (x : ℂ → EuclideanSpace ℝ (Fin 4)) (c : ℝ) (η : ℂ → ℂ) :
    logVariation x (c • η) = c • logVariation x η := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  have := invertibleOfNonzero hc
  have hre (z : ℂ) : fderiv ℝ (fun w ↦ c * (η w).re) z = c • fderiv ℝ (fun w ↦ (η w).re) z :=
    fderiv_const_smul_of_invertible (f := fun w ↦ (η w).re) c
  have him (z : ℂ) : fderiv ℝ (fun w ↦ c * (η w).im) z = c • fderiv ℝ (fun w ↦ (η w).im) z :=
    fderiv_const_smul_of_invertible (f := fun w ↦ (η w).im) c
  funext z
  ext i
  fin_cases i <;> simp [hre, him] <;> ring

/-- The logarithmic variation of a difference of differentiable functions is the difference. -/
theorem logVariation_sub (x : ℂ → EuclideanSpace ℝ (Fin 4)) {η ζ : ℂ → ℂ}
    (hη : Differentiable ℝ η) (hζ : Differentiable ℝ ζ) :
    logVariation x (η - ζ) = logVariation x η - logVariation x ζ := by
  have hneg : -ζ = (-1 : ℝ) • ζ := by simp
  rw [sub_eq_add_neg, sub_eq_add_neg, hneg, logVariation_add x hη (hζ.const_smul _),
    logVariation_smul, neg_one_smul]

/-- The logarithmic variation at a point depends only on the germ of `η` there. -/
theorem logVariation_congr_nhds (x : ℂ → EuclideanSpace ℝ (Fin 4)) {η ζ : ℂ → ℂ} {z : ℂ}
    (h : η =ᶠ[𝓝 z] ζ) : logVariation x η z = logVariation x ζ z := by
  have hre : (fun w ↦ (η w).re) =ᶠ[𝓝 z] fun w ↦ (ζ w).re := h.mono fun w hw ↦ by simp only [hw]
  have him : (fun w ↦ (η w).im) =ᶠ[𝓝 z] fun w ↦ (ζ w).im := h.mono fun w hw ↦ by simp only [hw]
  refine apply_eq_of_sectionValue_eq ?_ ?_ ?_
  · simp only [logVariation_apply_zero, hre.fderiv_eq, him.fderiv_eq]
  · simp only [logVariation_apply_one, hre.fderiv_eq, him.fderiv_eq]
  · rw [sectionValue_logVariation, sectionValue_logVariation, h.eq_of_nhds]

/-- The logarithmic variation of a `Cⁿ⁺¹` function along a `Cⁿ` field is `Cⁿ`, at a point. -/
theorem contDiffAt_logVariation {x : ℂ → EuclideanSpace ℝ (Fin 4)} {η : ℂ → ℂ} {z : ℂ}
    {n : WithTop ℕ∞} (hx : ContDiffAt ℝ n x z) (hη : ContDiffAt ℝ (n + 1) η z) :
    ContDiffAt ℝ n (logVariation x η) z := by
  have hu : ContDiffAt ℝ (n + 1) (fun w ↦ (η w).re) z := reCLM.contDiff.contDiffAt.comp z hη
  have hv : ContDiffAt ℝ (n + 1) (fun w ↦ (η w).im) z := imCLM.contDiff.contDiffAt.comp z hη
  have hdu (a : ℂ) : ContDiffAt ℝ n (fun w ↦ fderiv ℝ (fun w ↦ (η w).re) w a) z :=
    (hu.fderiv_right le_rfl).clm_apply contDiffAt_const
  have hdv (a : ℂ) : ContDiffAt ℝ n (fun w ↦ fderiv ℝ (fun w ↦ (η w).im) w a) z :=
    (hv.fderiv_right le_rfl).clm_apply contDiffAt_const
  have hxi (i : Fin 4) : ContDiffAt ℝ n (fun w ↦ x w i) z := contDiffAt_euclidean.1 hx i
  have hu' := hu.of_le le_self_add
  have hv' := hv.of_le le_self_add
  have h₀ : ContDiffAt ℝ n (fun w ↦ logVariation x η w 0) z := by
    simpa only [logVariation_apply_zero] using (hdv 1).neg.sub (hdu I)
  have h₁ : ContDiffAt ℝ n (fun w ↦ logVariation x η w 1) z := by
    simpa only [logVariation_apply_one] using (hdu 1).sub (hdv I)
  have h₂ : ContDiffAt ℝ n (fun w ↦ logVariation x η w 2) z := by
    simpa only [logVariation_apply_two] using ((hxi 2).mul hu').sub ((hxi 3).mul hv')
  have h₃ : ContDiffAt ℝ n (fun w ↦ logVariation x η w 3) z := by
    simpa only [logVariation_apply_three] using ((hxi 2).mul hv').add ((hxi 3).mul hu')
  refine contDiffAt_euclidean.2 fun i ↦ ?_
  fin_cases i
  exacts [h₀, h₁, h₂, h₃]

/-- The logarithmic variation of a `Cⁿ⁺¹` function along a `Cⁿ` field is `Cⁿ`. -/
theorem contDiff_logVariation {x : ℂ → EuclideanSpace ℝ (Fin 4)} {η : ℂ → ℂ}
    {n : WithTop ℕ∞} (hx : ContDiff ℝ n x) (hη : ContDiff ℝ (n + 1) η) :
    ContDiff ℝ n (logVariation x η) :=
  contDiff_iff_contDiffAt.2 fun _ ↦ contDiffAt_logVariation hx.contDiffAt hη.contDiffAt

/-- The logarithmic variation of `η` is in `Lᵖ` when the real and imaginary parts of `η` and their
derivatives are, along a continuous field whose section components are bounded. -/
theorem memLp_logVariation {x : ℂ → EuclideanSpace ℝ (Fin 4)} (hx : Continuous x) {B : ℝ}
    (hB : ∀ w, |x w 2| ≤ B ∧ |x w 3| ≤ B) {η : ℂ → ℂ} {p : ENNReal} {μ : Measure ℂ}
    (hu : MemLp (fun w ↦ (η w).re) p μ) (hv : MemLp (fun w ↦ (η w).im) p μ)
    (hdu : MemLp (fderiv ℝ fun w ↦ (η w).re) p μ) (hdv : MemLp (fderiv ℝ fun w ↦ (η w).im) p μ) :
    MemLp (logVariation x η) p μ := by
  have happ {f : ℂ → ℝ} (hf : MemLp (fderiv ℝ f) p μ) (a : ℂ) :
      MemLp (fun w ↦ fderiv ℝ f w a) p μ :=
    (ContinuousLinearMap.apply ℝ ℝ a).comp_memLp' hf
  have hxi (i : Fin 4) : Continuous fun w ↦ x w i := by fun_prop
  have hmul {f : ℂ → ℝ} (hf : MemLp f p μ) (i : Fin 4) (hi : ∀ w, |x w i| ≤ B) :
      MemLp (fun w ↦ x w i * f w) p μ :=
    hf.of_le_mul (c := B) ((hxi i).aestronglyMeasurable.mul hf.aestronglyMeasurable)
      (ae_of_all _ fun w ↦ by rw [norm_mul, Real.norm_eq_abs]; gcongr; exact hi w)
  have h₀ : MemLp (fun w ↦ logVariation x η w 0) p μ := by
    simp only [logVariation_apply_zero]
    exact (happ hdv 1).neg.sub (happ hdu I)
  have h₁ : MemLp (fun w ↦ logVariation x η w 1) p μ := by
    simp only [logVariation_apply_one]
    exact (happ hdu 1).sub (happ hdv I)
  have h₂ : MemLp (fun w ↦ logVariation x η w 2) p μ := by
    simp only [logVariation_apply_two]
    exact (hmul hu 2 fun w ↦ (hB w).1).sub (hmul hv 3 fun w ↦ (hB w).2)
  have h₃ : MemLp (fun w ↦ logVariation x η w 3) p μ := by
    simp only [logVariation_apply_three]
    exact (hmul hv 2 fun w ↦ (hB w).1).add (hmul hu 3 fun w ↦ (hB w).2)
  refine memLp_piLp_iff.2 fun i ↦ ?_
  fin_cases i
  exacts [h₀, h₁, h₂, h₃]

/-- **A kernel element with regular `δα / α` vanishes.** Let `x` be a differentiable field whose
holomorphicity rows vanish everywhere and whose zeros have dense complement, and let `y` be a
continuous variation with `L_x y = 0`. If `δα = α η` for a `C²` function `η` in `L²`, then `y = 0`:
`η` solves `Δη = P η` with `P ≥ 0`, so `|η|²` is subharmonic. -/
theorem eq_zero_of_gaugeFixedOperator_eq_zero_of_sectionValue_eq_mul
    {μ : Measure ℂ} [μ.IsAddHaarMeasure] {x y : ℂ → EuclideanSpace ℝ (Fin 4)} {η : ℂ → ℂ}
    (hx : Differentiable ℝ x) (hhol : ∀ w, equation x w 1 = 0 ∧ equation x w 2 = 0)
    (hy : Continuous y) (hker : ∀ w, gaugeFixedOperator x y w = 0)
    (hη : ContDiff ℝ 2 η) (hyη : ∀ w, sectionValue y w = sectionValue x w * η w)
    (hdense : Dense {w | sectionValue x w ≠ 0}) (hη₂ : MemLp η 2 μ) : y = 0 := by
  have hdη (w : ℂ) : DifferentiableAt ℝ η w := hη.differentiable (by simp) w
  -- `y` is the logarithmic variation of `η` off the zeros of `α`, hence everywhere.
  have hoff : EqOn y (logVariation x η) {w | sectionValue x w ≠ 0} := fun w hw ↦
    apply_eq_logVariation_apply (hx w) (hdη w) hw (Eventually.of_forall hyη) (hhol w).1
      (hhol w).2 (by simp [hker w]) (by simp [hker w])
  have hcont (i : Fin 4) : Continuous fun w ↦ logVariation x η w i := by
    have hf (f : ℂ → ℝ) (hf : ContDiff ℝ 2 f) (v : ℂ) : Continuous fun w ↦ fderiv ℝ f w v :=
      (hf.continuous_fderiv (by simp)).clm_apply continuous_const
    have hu : ContDiff ℝ 2 fun w ↦ (η w).re := reCLM.contDiff.comp hη
    have hv : ContDiff ℝ 2 fun w ↦ (η w).im := imCLM.contDiff.comp hη
    have hxi (j : Fin 4) : Continuous fun w ↦ x w j :=
      (EuclideanSpace.proj (𝕜 := ℝ) j).continuous.comp hx.continuous
    fin_cases i
    · exact ((hf _ hv 1).neg).sub (hf _ hu I)
    · exact (hf _ hu 1).sub (hf _ hv I)
    · exact ((hxi 2).mul hu.continuous).sub ((hxi 3).mul hv.continuous)
    · exact ((hxi 2).mul hv.continuous).add ((hxi 3).mul hu.continuous)
  have hyl : y = logVariation x η := by
    funext w
    ext i
    exact congrFun (Continuous.ext_on hdense
      ((EuclideanSpace.proj (𝕜 := ℝ) i).continuous.comp hy) (hcont i)
      fun w hw ↦ by simp [hoff hw]) w
  -- Hence `Δη = P η` everywhere, and `η = 0` by subharmonicity of `|η|²`.
  have hΔ (w : ℂ) : Δ η w = (x w 2 ^ 2 + x w 3 ^ 2) • η w :=
    (gaugeFixedOperator_logVariation_eq_zero_iff (hx w) hη.contDiffAt (hhol w).1
      (hhol w).2).mp (hyl ▸ hker w)
  have hη0 : η = 0 := eq_zero_of_memLp_of_laplacian_eq_smul hη hη₂ (fun w ↦ by positivity) hΔ
  rw [hyl, hη0, logVariation_zero]

/-- **A kernel element of a framed vortex with regular `δα / α` vanishes.** Let `x` be a `C¹`
field whose holomorphicity rows vanish everywhere, with `|α|² → 1` at infinity, and let `y` be a
continuous variation in `L²` with `L_x y = 0`. If `δα = α η` for a `C²` function `η`, then `y = 0`.
Here the zeros of `α` are finite and `η` is in `L²`, since `|η| ≤ 4 |y|` where `|α| ≥ 1 / 2`. -/
theorem eq_zero_of_gaugeFixedOperator_eq_zero_of_sectionValue_eq_mul_of_tendsto
    {μ : Measure ℂ} [μ.IsAddHaarMeasure] {x y : ℂ → EuclideanSpace ℝ (Fin 4)} {η : ℂ → ℂ}
    (hx : ContDiff ℝ 1 x) (hhol : ∀ w, equation x w 1 = 0 ∧ equation x w 2 = 0)
    (hlim : Tendsto (fun w ↦ 4 * (x w 2 ^ 2 + x w 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    (hy : Continuous y) (hy₂ : MemLp y 2 μ) (hker : ∀ w, gaugeFixedOperator x y w = 0)
    (hη : ContDiff ℝ 2 η) (hyη : ∀ w, sectionValue y w = sectionValue x w * η w) : y = 0 := by
  have hxi (i : Fin 4) : ContDiff ℝ 1 fun w ↦ x w i :=
    (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.comp hx
  have hfin := finite_setOfPred_sectionValue_eq_zero (k := 1) le_rfl (hxi 0) (hxi 1)
    ((hxi 2).differentiable (by simp)) ((hxi 3).differentiable (by simp)) hhol hlim
  have hdense : Dense {w | sectionValue x w ≠ 0} := by
    simpa only [compl_ofPred] using Set.Countable.dense_compl ℝ hfin.countable
  -- Outside a compact set `|α| ≥ 1 / 2`, so `|η| ≤ 4 |y|` there; `η` is bounded on the compact.
  obtain ⟨K, hK, hKc⟩ := mem_cocompact.mp
    (hlim.eventually (lt_mem_nhds (by norm_num : (1 / 4 : ℝ) < 1)))
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hη.continuous.continuousOn
  have hbound (w : ℂ) : ‖η w‖ ≤ K.indicator (fun _ ↦ M) w + 4 * ‖y w‖ := by
    by_cases hw : w ∈ K
    · rw [indicator_of_mem hw]
      linarith [hM w hw, norm_nonneg (y w)]
    · rw [indicator_of_notMem hw, zero_add]
      have hα : 1 / 4 < ‖sectionValue x w‖ ^ 2 := by
        rw [sq_norm_sectionValue]
        exact hKc hw
      have hαη : ‖sectionValue x w‖ * ‖η w‖ ≤ 2 * ‖y w‖ := by
        rw [← norm_mul, ← hyη]
        exact norm_sectionValue_le y w
      nlinarith [norm_nonneg (η w), norm_nonneg (sectionValue x w)]
  have hg : MemLp (fun w ↦ K.indicator (fun _ ↦ M) w + 4 * ‖y w‖) 2 μ :=
    (memLp_indicator_const 2 hK.measurableSet.nullMeasurableSet M
      (Or.inr hK.measure_lt_top.ne)).add (hy₂.norm.const_mul 4)
  have hη₂ : MemLp η 2 μ := hg.of_le hη.continuous.aestronglyMeasurable
    (Eventually.of_forall fun w ↦ (hbound w).trans (le_abs_self _))
  exact eq_zero_of_gaugeFixedOperator_eq_zero_of_sectionValue_eq_mul
    (hx.differentiable (by simp)) hhol hy hker hη hyη hdense hη₂

end TauCeti.Vortex
