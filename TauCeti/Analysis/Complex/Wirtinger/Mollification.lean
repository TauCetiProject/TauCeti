/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Wirtinger.Basic
public import TauCeti.Analysis.Distribution.TestFunction.LineDeriv
public import Mathlib.Analysis.Calculus.ContDiff.Convolution

/-!
# Mollifying a distributional Cauchy–Riemann equation

If the normalized equation `barpartial u = f` holds against real compactly supported test
functions, convolution with a smooth real kernel satisfies the classical equation wherever
the translated kernel support remains in the domain. The assumption is the raw integral
identity; no complete weak derivative of `u` is required.

## References

* L. C. Evans, *Partial Differential Equations*, second edition, §5.3.1.
-/

public section

namespace TauCeti

open MeasureTheory TopologicalSpace ContinuousLinearMap Complex
open scoped ContDiff Convolution Distributions

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
  {Ω : Opens ℂ} {u f : ℂ → F}

/-- Mollification turns the distributional equation `barpartial u = f` into its classical
counterpart at every point whose translated kernel support lies in the domain. -/
theorem conjWirtingerDeriv_convolution_right_of_integral_eq
    (hu : LocallyIntegrable u)
    (h : ∀ φ : 𝓓(Ω, ℝ),
      (∫ z, lineDeriv ℝ (φ : ℂ → ℝ) z 1 • u z) +
        I • (∫ z, lineDeriv ℝ (φ : ℂ → ℝ) z I • u z) =
          -(2 : ℝ) • (∫ z, (φ : ℂ → ℝ) z • f z))
    (ρ : ℂ → ℝ) (hρ : ContDiff ℝ ∞ ρ) (hρc : HasCompactSupport ρ) (x : ℂ)
    (hx : ∀ y ∈ tsupport ρ, x - y ∈ Ω) :
    conjWirtingerDeriv (u ⋆[(lsmul ℝ ℝ).flip] ρ) x 1 =
      (f ⋆[(lsmul ℝ ℝ).flip] ρ) x := by
  have hsmooth : ContDiff ℝ ∞ fun z ↦ ρ (x - z) := by fun_prop
  have hcpt : HasCompactSupport fun z ↦ ρ (x - z) :=
    hρc.comp_homeomorph (Homeomorph.subLeft x)
  have hsupp : tsupport (fun z ↦ ρ (x - z)) ⊆ Ω := fun z hz ↦ by
    simpa using hx _ (tsupport_comp_subset_preimage ρ (f := (x - ·)) (by fun_prop) hz)
  have hline (z v : ℂ) : lineDeriv ℝ (fun t ↦ ρ (x - t)) z v =
      -fderiv ℝ ρ (x - z) v := by
    simpa [Function.comp_def] using ((hρ.differentiable (by simp) (x - z)).hasFDerivAt.comp z
      ((hasFDerivAt_id z).const_sub x)).hasLineDerivAt v |>.lineDeriv
  have hweak := h ⟨_, hsmooth, hcpt, hsupp⟩
  simp only [TestFunction.coe_mk, hline, neg_smul, integral_neg, smul_neg] at hweak
  have hd := hρc.hasFDerivAt_convolution_right (lsmul ℝ ℝ).flip hu (hρ.of_le (by simp)) x
  have hD (v : ℂ) : fderiv ℝ (u ⋆[(lsmul ℝ ℝ).flip] ρ) x v =
      ∫ z, fderiv ℝ ρ (x - z) v • u z := by
    rw [hd.fderiv, convolution_precompR_apply (lsmul ℝ ℝ).flip hu (hρc.fderiv ℝ)
      (hρ.continuous_fderiv (by simp)) x v]
    rfl
  have hsum : fderiv ℝ (u ⋆[(lsmul ℝ ℝ).flip] ρ) x 1 +
      I • fderiv ℝ (u ⋆[(lsmul ℝ ℝ).flip] ρ) x I =
        (2 : ℝ) • (f ⋆[(lsmul ℝ ℝ).flip] ρ) x := by
    rw [hD, hD]
    apply neg_injective
    simpa only [neg_add, neg_smul, convolution_def, flip_apply, lsmul_apply] using hweak
  rw [conjWirtingerDeriv_apply]
  simp only [smul_eq_mul, mul_one, hsum]
  rw [two_smul ℝ, ← two_smul ℂ, smul_smul]
  norm_num

end TauCeti
