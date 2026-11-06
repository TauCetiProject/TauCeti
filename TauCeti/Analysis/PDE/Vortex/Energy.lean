/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.Decay
import TauCeti.Analysis.InnerProductSpace.Laplacian.Integral

/-!
# Finite energy of plane vortex solutions

A classical plane vortex whose section has unit modulus at infinity has finite physical energy.
No decay of its connection coefficients, phase, or derivatives is assumed. This allows solutions
constructed by the scalar equation to enter the finite-energy framed moduli problem before a
Sobolev gauge normalization is chosen.

The covariant Bochner identity, valid also at section zeros, is
`Δ |α|² = 2 |d_a α|² - (1 - |α|²) |α|² / 4`.
The integrable modulus defect controls the negative part of this Laplacian. A cutoff argument
therefore gives integrability of the covariant kinetic energy; the curvature and potential
terms are controlled directly by the modulus defect. The energy is the existing
`energyDensity`, with no change of its coefficients and no assertion of a quantized value.

## References

* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Birkhäuser, 1980, Chapter III.
-/

public section

noncomputable section

namespace TauCeti.Vortex

open Complex Filter MeasureTheory Topology InnerProductSpace Laplacian

variable {x : ℂ → EuclideanSpace ℝ (Fin 4)}

/-- The covariant Bochner identity at a plane vortex, including the zeros of its section.
Only the connection coefficients need be differentiable at the point. -/
theorem laplacian_normSq_of_equation_eq_zero {z : ℂ}
    (hb₁ : DifferentiableAt ℝ (fun w ↦ x w 0) z)
    (hb₂ : DifferentiableAt ℝ (fun w ↦ x w 1) z)
    (hp : ContDiffAt ℝ 2 (fun w ↦ x w 2) z)
    (hq : ContDiffAt ℝ 2 (fun w ↦ x w 3) z)
    (hsol : ∀ᶠ w in 𝓝 z, equation x w = 0) :
    Δ (fun w : ℂ ↦ (4 : ℝ) * (x w 2 ^ 2 + x w 3 ^ 2)) z =
      2 * (‖covariantDerivative x z 1‖ ^ 2 + ‖covariantDerivative x z I‖ ^ 2) -
        (1 - 4 * (x z 2 ^ 2 + x z 3 ^ 2)) * (4 * (x z 2 ^ 2 + x z 3 ^ 2)) / 4 := by
  have hp' := hp.differentiableAt (by norm_num)
  have hq' := hq.differentiableAt (by norm_num)
  have hdp := (hp.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hdq := (hq.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hcomm (i : Fin 4) (hi : ContDiffAt ℝ 2 (fun w ↦ x w i) z) :=
    (hi.isSymmSndFDerivAt (by norm_num)).eq (1 : ℂ) I
  -- Differentiate the two holomorphicity rows, retaining the connection derivatives.
  have hrow (i : Fin 3) (v : ℂ) : fderiv ℝ (fun w ↦ equation x w i) z v = 0 := by
    have he : (fun w ↦ equation x w i) =ᶠ[𝓝 z] fun _ ↦ 0 :=
      hsol.mono fun w hw ↦ by simp [hw]
    rw [he.fderiv_eq]
    simp
  have h11 := hrow 1 1
  have h1I := hrow 1 I
  have h21 := hrow 2 1
  have h2I := hrow 2 I
  simp (disch := fun_prop) only [equation_apply_one, equation_apply_two,
    fderiv_fun_sub, fderiv_fun_add, fderiv_fun_mul,
    fderiv_clm_apply hdp (differentiableAt_const _),
    fderiv_clm_apply hdq (differentiableAt_const _),
    add_apply, sub_apply, smul_apply, smul_eq_mul]
    at h11 h1I h21 h2I
  have hcurv := curvature_eq_of_equation_eq_zero hsol.self_of_nhds
  have hΔp := hp.laplacian_norm_sq orthonormalBasisOneI
  have hΔq := hq.laplacian_norm_sq orthonormalBasisOneI
  simp only [Fin.isValue, Real.norm_eq_abs, sq_abs, coe_orthonormalBasisOneI,
    Nat.succ_eq_add_one, Nat.reduceAdd, Fin.sum_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, RCLike.inner_apply, conj_trivial] at hΔp hΔq
  have hΔ := laplacian_smul (𝕜 := ℝ) (f := fun w ↦ x w 2 ^ 2 + x w 3 ^ 2) 4
    ((hp.pow 2).add (hq.pow 2))
  simp only [Pi.smul_def, smul_eq_mul] at hΔ
  have hsum := (hp.pow 2).laplacian_add (hq.pow 2)
  simp only [Pi.add_def] at hsum
  rw [hΔ, hsum, hΔp, hΔq]
  -- Expand the ordinary Laplacians and the covariant squares in the same unitary frame.
  have hsfun := funext (sectionValue_apply x)
  have hcastp := (ofRealCLM.hasFDerivAt.comp z hp'.hasFDerivAt).fderiv
  have hcastq := (ofRealCLM.hasFDerivAt.comp z hq'.hasFDerivAt).fderiv
  simp only [Function.comp_def, ofRealCLM_apply] at hcastp hcastq
  have he1 := congrArg (fun v : EuclideanSpace ℝ (Fin 3) ↦ v 1) hsol.self_of_nhds
  have he2 := congrArg (fun v : EuclideanSpace ℝ (Fin 3) ↦ v 2) hsol.self_of_nhds
  simp only [equation_apply_one, equation_apply_two, PiLp.zero_apply] at he1 he2
  simp (disch := fun_prop) [laplacian_eq_sum_fderiv_fderiv_apply orthonormalBasisOneI hdp,
    laplacian_eq_sum_fderiv_fderiv_apply orthonormalBasisOneI hdq, Fin.sum_univ_two,
    covariantDerivative_apply, hsfun, Complex.sq_norm, Complex.normSq_apply,
    fderiv_fun_add, fderiv_fun_mul, hcastp, hcastq,
    fderiv_clm_apply hdp (differentiableAt_const _),
    fderiv_clm_apply hdq (differentiableAt_const _), hcomm 2 hp, hcomm 3 hq]
    at h11 h1I h21 h2I ⊢
  linear_combination 8 * x z 2 * (h11 + h2I) + 8 * x z 3 * (h21 - h1I) +
    8 * (x z 2 ^ 2 + x z 3 ^ 2) * hcurv +
    8 * (x z 2 * x z 1 + x z 3 * x z 0) * he1 +
    8 * (x z 3 * x z 1 - x z 2 * x z 0) * he2

variable (μ : Measure ℂ) [μ.IsAddHaarMeasure]

/-- The covariant kinetic energy of a classical vortex with unit-modulus end is integrable.
This conclusion is gauge invariant and does not require a Sobolev tail for the connection. -/
theorem integrable_covariantDerivative_norm_sq
    (hb₁ : Differentiable ℝ (fun w ↦ x w 0))
    (hb₂ : Differentiable ℝ (fun w ↦ x w 1))
    (hp : ContDiff ℝ 2 (fun w ↦ x w 2)) (hq : ContDiff ℝ 2 (fun w ↦ x w 3))
    (hsol : ∀ z, equation x z = 0)
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1)) :
    Integrable (fun z ↦ ‖covariantDerivative x z 1‖ ^ 2 +
      ‖covariantDerivative x z I‖ ^ 2) μ := by
  let s := fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)
  have hs : ContDiff ℝ 2 s := contDiff_const.mul ((hp.pow 2).add (hq.pow 2))
  have hsi : Integrable (fun z ↦ 1 - s z) μ :=
    integrable_one_sub_normSq μ hb₁ hb₂ hp hq hsol hlim
  have hs1 : ∀ z, s z ≤ 1 := normSq_le_one_of_tendsto hb₁ hb₂ hp hq hsol hlim
  have hid (z : ℂ) := laplacian_normSq_of_equation_eq_zero (hb₁ z) (hb₂ z)
    hp.contDiffAt hq.contDiffAt (Eventually.of_forall hsol)
  have hΔ : Integrable (Δ (fun z ↦ s z - 1)) μ :=
    integrable_laplacian_of_integrable_of_le (hs.sub contDiff_const)
      (by simpa only [Pi.neg_def, neg_sub] using hsi.neg)
      (hsi.div_const 4) (fun z ↦ by
        simp only [← Pi.sub_def, hs.contDiffAt.laplacian_sub contDiffAt_const,
          laplacian_const, Pi.zero_apply, sub_zero]
        dsimp only [s] at hid ⊢
        nlinarith [hid z, sq_nonneg (1 - 4 * (x z 2 ^ 2 + x z 3 ^ 2)),
          sq_nonneg ‖covariantDerivative x z 1‖, sq_nonneg ‖covariantDerivative x z I‖])
  have hΔs : Integrable (Δ s) μ := hΔ.congr (ae_of_all μ fun z ↦ by
    simp only [← Pi.sub_def, hs.contDiffAt.laplacian_sub contDiffAt_const,
      laplacian_const, Pi.zero_apply, sub_zero])
  have hprod : Integrable (fun z ↦ (1 - s z) * s z / 4) μ := by
    apply (hsi.div_const 4).mono' ((continuous_const.sub hs.continuous).mul
      hs.continuous |>.div_const 4 |>.aestronglyMeasurable)
    apply ae_of_all
    intro z
    have : 0 ≤ s z := by dsimp [s]; positivity
    have hdef : 0 ≤ 1 - s z := sub_nonneg.mpr (hs1 z)
    dsimp only [Pi.div_apply, Pi.mul_apply, Pi.sub_apply]
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    nlinarith [hs1 z]
  exact ((hΔs.add hprod).div_const 2).congr (ae_of_all μ fun z ↦ by
    dsimp only [s, Pi.add_apply, Pi.div_apply] at hid ⊢
    linarith [hid z])

/-- Every classical plane vortex with unit-modulus section at infinity has finite physical
energy `∫ (|F_a|² + |d_a α|² + (1 - |α|²)²)`, without assumed derivative decay. -/
theorem integrable_energyDensity
    (hb₁ : Differentiable ℝ (fun w ↦ x w 0))
    (hb₂ : Differentiable ℝ (fun w ↦ x w 1))
    (hp : ContDiff ℝ 2 (fun w ↦ x w 2)) (hq : ContDiff ℝ 2 (fun w ↦ x w 3))
    (hsol : ∀ z, equation x z = 0)
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1)) :
    Integrable (energyDensity x) μ := by
  have hs1 := normSq_le_one_of_tendsto hb₁ hb₂ hp hq hsol hlim
  have hpot : Integrable (fun z ↦ (1 - 4 * (x z 2 ^ 2 + x z 3 ^ 2)) ^ 2) μ := by
    apply (integrable_one_sub_normSq μ hb₁ hb₂ hp hq hsol hlim).mono'
      ((continuous_const.sub (continuous_const.mul
        ((hp.continuous.pow 2).add (hq.continuous.pow 2)))).pow 2).aestronglyMeasurable
    apply ae_of_all
    intro z
    dsimp only [Pi.pow_apply, Pi.sub_apply, Pi.mul_apply, Pi.add_apply]
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have : 0 ≤ 4 * (x z 2 ^ 2 + x z 3 ^ 2) := by positivity
    nlinarith [hs1 z]
  have hcurv : Integrable (fun z ↦ curvature x z ^ 2) μ := by
    exact (hpot.div_const 64).congr (ae_of_all μ fun z ↦ by
      dsimp only
      rw [curvature_apply, curvature_eq_of_equation_eq_zero (hsol z)]
      ring)
  have hkin := integrable_covariantDerivative_norm_sq μ hb₁ hb₂ hp hq hsol hlim
  convert (hcurv.add hkin).add hpot using 1
  ext z
  have hn : ‖sectionValue x z‖ ^ 2 = 4 * (x z 2 ^ 2 + x z 3 ^ 2) := by
    rw [sectionValue_apply, Complex.sq_norm]
    norm_num [Complex.normSq_apply]
    ring
  rw [energyDensity_apply, hn]
  dsimp only [Pi.add_apply]
  ring

end TauCeti.Vortex
