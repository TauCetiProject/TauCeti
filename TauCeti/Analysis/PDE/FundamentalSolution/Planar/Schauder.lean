/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.FundamentalSolution.Planar.Holder
public import TauCeti.Analysis.Complex.Pompeiu.Newtonian
public import TauCeti.Analysis.PDE.Regularity.Hessian.Schauder.Complex
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff
import TauCeti.Analysis.Normed.Operator.Holder
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-!
# Uniform smooth-data Schauder bounds for the planar Newtonian potential

The estimates here depend only on the source supremum and Hölder constant, together with fixed
support and output discs. Higher derivatives of the smooth source do not enter the estimate.
The potential and its first derivatives are bounded using the integrable logarithmic and
Cauchy kernels. A cutoff then puts its Poisson equation in the whole-space Schauder estimate.
-/

public noncomputable section

open MeasureTheory Metric Set Complex Filter Topology InnerProductSpace Laplacian
open scoped Convolution NNReal ContDiff Gradient

namespace TauCeti

/-- On fixed support and output discs, the Hessian of the Newtonian potential of smooth real
data is Hölder and bounded, with a constant independent of derivatives of the source. -/
theorem exists_holderOnWith_iteratedFDeriv_two_planarNewtonianKernel_convolution
    {α : ℝ≥0} (hα : 0 < α) (hα1 : α < 1) (c : ℂ) {r R : ℝ}
    (hr : 0 ≤ r) (hR : 0 ≤ R) :
    ∃ C : ℝ≥0, ∀ {f : ℂ → ℝ} {H M : ℝ≥0}, ContDiff ℝ ∞ f →
      Function.support f ⊆ closedBall c r → HolderWith H α f → (∀ x, ‖f x‖ ≤ M) →
      HolderOnWith (C * (H + M)) α (iteratedFDeriv ℝ 2 (planarNewtonianKernel ⋆ f))
        (closedBall c R) ∧
      ∀ x ∈ closedBall c R, ‖iteratedFDeriv ℝ 2 (planarNewtonianKernel ⋆ f) x‖ ≤
        C * (H + M) := by
  let b : ContDiffBump c := ⟨R + 1, R + 2, by linarith, by linarith⟩
  let χ : ℂ → ℝ := b
  let s := closedBall c (R + 2)
  have hχ : ContDiff ℝ ∞ χ := b.contDiff
  have hcχ : HasCompactSupport χ := b.hasCompactSupport
  have hχs : tsupport χ ⊆ s := by simpa only [χ, s, b.tsupport_eq] using subset_rfl
  obtain ⟨C₀, hC₀, hN₀⟩ :=
    (hχ.of_le (by simp : (1 : WithTop ℕ∞) ≤ ∞)).exists_holderWith_and_norm_le_of_hasCompactSupport
      hcχ hα1.le
  obtain ⟨C₂, hC₂, hN₂⟩ :=
    (hχ.laplacian (m := 1) (by simp)).exists_holderWith_and_norm_le_of_hasCompactSupport
      hcχ.laplacian hα1.le
  have hχD (v : ℂ) : ContDiff ℝ 1 (fun x ↦ fderiv ℝ χ x v) :=
    (hχ.fderiv_right (m := 1) (by simp)).clm_apply contDiff_const
  obtain ⟨C₁, hC₁, hN₁⟩ := (hχD 1).exists_holderWith_and_norm_le_of_hasCompactSupport
    (hcχ.fderiv_apply (𝕜 := ℝ) 1) hα1.le
  obtain ⟨Cᵢ, hCᵢ, hNᵢ⟩ := (hχD I).exists_holderWith_and_norm_le_of_hasCompactSupport
    (hcχ.fderiv_apply (𝕜 := ℝ) I) hα1.le
  let J := (∫ z, ‖(closedBall (0 : ℂ) (r + (R + 2))).indicator planarNewtonianKernel z‖).toNNReal
  let D := (2 * (r + (R + 2))).toNNReal
  let A := C₀ + C₂ * J + 2 * (C₁ + Cᵢ) * D
  obtain ⟨C, hC⟩ := PDE.exists_holderWith_iteratedFDeriv_two_and_norm_le_of_laplacian_complex
    hα hα1
  refine ⟨C * (A + C₀ * J), fun {f H M} hf hs hH hM ↦ ?_⟩
  have hcf := HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall c r) hs
  let u := planarNewtonianKernel ⋆ f
  have hu : ContDiff ℝ ∞ u := contDiff_planarNewtonianKernel_convolution hf hcf
  have hU : HolderOnWith (J * H) α u s :=
    holderOnWith_planarNewtonianKernel_convolution hα hH hs
  have hUN (x : ℂ) (hx : x ∈ s) : ‖u x‖ ≤ (J * M : ℝ≥0) := by
    convert norm_planarNewtonianKernel_convolution_le hs hM hx using 1
    rw [NNReal.coe_mul, Real.coe_toNNReal _ (integral_nonneg fun z ↦ norm_nonneg _)]
  have hDU :=
    holderOnWith_fderiv_planarNewtonianKernel_convolution_apply_one_and_apply_I
      hα hH (hf.of_le (by simp)) hr (by linarith : 0 ≤ R + 2) hs
  have hDUN (x : ℂ) (hx : x ∈ s) :
      ‖fderiv ℝ u x 1‖ ≤ (D * M : ℝ≥0) ∧ ‖fderiv ℝ u x I‖ ≤ (D * M : ℝ≥0) := by
    simpa only [Real.norm_eq_abs, NNReal.coe_mul, D,
      Real.coe_toNNReal _ (by positivity : 0 ≤ 2 * (r + (R + 2)))] using
      abs_fderiv_planarNewtonianKernel_convolution_apply_one_le_and_apply_I_le
        (hf.of_le (by simp)) hr
        (by linarith : 0 ≤ R + 2) hs hM hx
  have hχ0 (x : ℂ) (hx : x ∉ s) : χ x = 0 :=
    image_eq_zero_of_notMem_tsupport (fun h ↦ hx (hχs h))
  have hχ20 (x : ℂ) (hx : x ∉ s) : Δ χ x = 0 :=
    image_eq_zero_of_notMem_tsupport (fun h ↦ hx (hχs (tsupport_laplacian_subset χ h)))
  have hχD0 (v x : ℂ) (hx : x ∉ s) : fderiv ℝ χ x v = 0 := by
    rw [fderiv_of_notMem_tsupport ℝ (fun h ↦ hx (hχs h))]
    simp
  have h0 := hC₀.smul_of_eq_zero (hH.holderOnWith s) hN₀ (fun x _ ↦ hM x) hχ0
  have h2 := hC₂.smul_of_eq_zero hU hN₂ hUN hχ20
  have h1 := hC₁.smul_of_eq_zero hDU.1 hN₁ (fun x hx ↦ (hDUN x hx).1) (hχD0 1)
  have hi := hCᵢ.smul_of_eq_zero hDU.2 hNᵢ (fun x hx ↦ (hDUN x hx).2) (hχD0 I)
  have hneg : HolderWith (C₀ * H + M * C₀) α (fun x ↦ -(χ x * f x)) := by
    intro x y
    simpa only [edist_neg_neg, smul_eq_mul] using h0 x y
  have hΔ : HolderWith (A * (H + M)) α (Δ (fun x ↦ χ x * u x)) := by
    have h := ((hneg.add h2).add ((h1.add hi).smul (2 : ℝ)))
    convert h using 1
    · dsimp only [A]
      simp only [Real.nnnorm_ofNat]
      ring
    · funext x
      rw [((hχ.of_le (by simp : (2 : WithTop ℕ∞) ≤ ∞)).contDiffAt).laplacian_fun_mul_complex
        ((hu.of_le (by simp)).contDiffAt),
        laplacian_planarNewtonianKernel_convolution (hf.of_le (by simp)) hcf]
      simp only [Pi.neg_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, u]
      ring
  have hcutN (x : ℂ) : |χ x * u x| ≤ (C₀ * J * M : ℝ≥0) := by
    by_cases hx : x ∈ s
    · rw [← Real.norm_eq_abs, norm_mul, NNReal.coe_mul, NNReal.coe_mul]
      exact (mul_le_mul (hN₀ x) (hUN x hx) (norm_nonneg _) C₀.coe_nonneg).trans_eq
        (by push_cast; ring)
    · rw [hχ0 x hx, zero_mul, abs_zero]
      positivity
  obtain ⟨hHS, hDS⟩ := hC (hχ.mul hu) hcχ.mul_right hcutN hΔ
  have hEq (x : ℂ) (hx : x ∈ closedBall c R) :
      iteratedFDeriv ℝ 2 (fun y ↦ χ y * u y) x = iteratedFDeriv ℝ 2 u x := by
    exact (b.eventuallyEq_one_of_mem_ball
      (by exact lt_of_le_of_lt (mem_closedBall.mp hx) (by dsimp [b]; linarith))
      ).iteratedFDeriv_mul_eq
  have hconst : C * (A * (H + M) + C₀ * J * M) ≤
      C * (A + C₀ * J) * (H + M) := by
    calc
      _ ≤ C * (A * (H + M) + C₀ * J * (H + M)) := by gcongr; exact le_add_self
      _ = _ := by ring
  constructor
  · intro x hx y hy
    rw [← hEq x hx, ← hEq y hy]
    exact (hHS.mono hconst).edist_le x y
  · intro x hx
    rw [← hEq x hx]
    exact (hDS x).trans (by exact_mod_cast hconst)

end TauCeti
