/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.SemiFredholm
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# The weighted semi-Fredholm estimate of the linearized Floer operator on a cylinder

Let `D_u` be the linearized Floer operator (`TauCeti.SymplecticForm.floerLinearization`) along a
map `u : ℝ × ℝ → V` of period one in `t`. The Fredholm and gluing theory of Floer cylinders uses
`D_u` on Sobolev spaces with an exponential weight `e^{ρ(s)}`, typically `ρ(s) ≈ δ |s|`, which
forces sections to decay at both ends. This file proves the semi-Fredholm estimate in these
weighted norms,

`∫ e^{2ρ} (‖∂s ξ‖² + ‖∂t ξ‖² + ‖ξ‖²) ≤ C (∫ e^{2ρ} ‖D_u ξ‖² + ∫_{[-T, T] × [0, 1]} e^{2ρ} ‖ξ‖²)`,

for every `C²` weight exponent `ρ` whose slope is bounded by a fixed `δ > 0`, with `C` and `T`
independent of `ρ` and of the section `ξ`.

The weighted estimate follows from the unweighted one by conjugation. Put `η = e^{ρ(s)} ξ`. The
operator differentiates the weight only in the `s` direction, so
`D_u η = e^{ρ} D_u ξ + ρ' η` (`TauCeti.SymplecticForm.floerLinearization_smul_fst`) and
`∂s η = e^{ρ} ∂s ξ + ρ' η`. Hence the weighted norms of `ξ` and of `D_u ξ` are the unweighted
norms of `η` and of `D_u η`, up to errors bounded by `|ρ'| ‖η‖`. When `|ρ'| ≤ δ` with
`4 C δ² ≤ 1`, these errors are absorbed by the left side of the unweighted estimate for `η`.
No spectral information beyond the unweighted estimate is used, and the weight may have either
sign of slope at either end.

## Main results

All in the namespace `TauCeti.SymplecticForm`:

* `setIntegral_exp_mul_le_mul_setIntegral_floerLinearization_add`: for any data `J`, `K_s`, `K_t`
  regular along `u`, an unweighted semi-Fredholm estimate with constants `C`, `T` implies the
  weighted one with constant `8 (1 + δ²) C`, for every weight exponent with slope at most `δ`,
  where `4 C δ² ≤ 1`.
* `exists_forall_setIntegral_exp_mul_le_mul_setIntegral_floerLinearization_add`: the weighted
  semi-Fredholm estimate along a Floer trajectory between nondegenerate orbits.
* `exists_forall_setIntegral_exp_mul_sqrt_le_mul_setIntegral_floerLinearization_add`: its case
  `ρ(s) = δ √(1 + s²)`, the smooth weight comparable to `e^{δ |s|}`.

The Sobolev completion and the Fredholm property itself are not treated here.

## References

* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), Lectures 2 and 3, on the operators `∂s + J ∂t + S(s, t)` along Floer
  trajectories and their exponentially weighted versions.
* R. B. Lockhart and R. C. McOwen, *Elliptic differential operators on noncompact manifolds*,
  Ann. Scuola Norm. Sup. Pisa Cl. Sci. (4) 12 (1985), 409–447, on elliptic operators in weighted
  Sobolev spaces on manifolds with cylindrical ends.
-/

public section

open Filter Set Function MeasureTheory ContinuousLinearMap
open scoped NNReal Manifold

namespace TauCeti.SymplecticForm

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- **The operator on a weighted section.** If `|ρ'| ≤ δ`, then
`∫ ‖D_u (e^{ρ} ξ)‖² ≤ 2 ∫ e^{2ρ} ‖D_u ξ‖² + 2 δ² ∫ ‖e^{ρ} ξ‖²` over `[a, b] × [0, 1]`, since
`D_u (e^{ρ} ξ) = e^{ρ} D_u ξ + ρ' e^{ρ} ξ`. -/
private theorem setIntegral_norm_floerLinearization_exp_smul_sq_le (ω : SymplecticForm V)
    {J : ℝ × ℝ → V → V →L[ℝ] V} {Ks Kt : ℝ × ℝ → V → ℝ} {u : ℝ × ℝ → V}
    (hJ : ∀ z, ContDiffAt ℝ 1 (uncurry J) (z, u z))
    (hKs : ∀ z, ContDiffAt ℝ 2 (uncurry Ks) (z, u z))
    (hKt : ∀ z, ContDiffAt ℝ 2 (uncurry Kt) (z, u z)) (hu : ContDiff ℝ 1 u) {ρ : ℝ → ℝ}
    {δ : ℝ} (hρ : ContDiff ℝ 2 ρ) (hρδ : ∀ s, |deriv ρ s| ≤ δ) {ξ : ℝ × ℝ → V}
    (hξ : ContDiff ℝ 2 ξ) (a b : ℝ) :
    ∫ z in Icc a b ×ˢ Icc (0 : ℝ) 1,
        ‖ω.floerLinearization J Ks Kt u (fun w ↦ Real.exp (ρ w.1) • ξ w) z‖ ^ 2 ≤
      2 * (∫ z in Icc a b ×ˢ Icc (0 : ℝ) 1,
          Real.exp (2 * ρ z.1) * ‖ω.floerLinearization J Ks Kt u ξ z‖ ^ 2) +
        2 * δ ^ 2 * ∫ z in Icc a b ×ˢ Icc (0 : ℝ) 1, ‖Real.exp (ρ z.1) • ξ z‖ ^ 2 := by
  have hη : ContDiff ℝ 2 fun w : ℝ × ℝ ↦ Real.exp (ρ w.1) • ξ w :=
    ((hρ.comp contDiff_fst).exp).smul hξ
  have hI {f : ℝ × ℝ → ℝ} (hf : Continuous f) : IntegrableOn f (Icc a b ×ˢ Icc (0 : ℝ) 1) :=
    hf.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  have hρc := hρ.continuous
  have hξc := hξ.continuous
  have hDξ := ω.continuous_floerLinearization hJ hKs hKt hu (hξ.of_le one_le_two)
  have hDη := ω.continuous_floerLinearization hJ hKs hKt hu (hη.of_le one_le_two)
  rw [← integral_const_mul, ← integral_const_mul, ← integral_add (hI (by fun_prop))
    (hI (by fun_prop))]
  refine setIntegral_mono_on (hI (by fun_prop)) (hI (by fun_prop))
    (measurableSet_Icc.prod measurableSet_Icc) fun z _ ↦ ?_
  have hρz : DifferentiableAt ℝ ρ z.1 := hρ.differentiable two_ne_zero z.1
  rw [ω.floerLinearization_smul_fst J Ks Kt u ξ hρz.hasDerivAt.exp
    (hξ.differentiable two_ne_zero z)]
  set W := Real.exp (ρ z.1)
  set p := deriv ρ z.1
  have hW : 0 < W := Real.exp_pos _
  have he : Real.exp (2 * ρ z.1) = W ^ 2 := by rw [sq, ← Real.exp_add, two_mul]
  have hp : p ^ 2 ≤ δ ^ 2 := sq_le_sq' (abs_le.1 (hρδ z.1)).1 (abs_le.1 (hρδ z.1)).2
  have h : ‖W • ω.floerLinearization J Ks Kt u ξ z + (W * p) • ξ z‖ ≤
      W * ‖ω.floerLinearization J Ks Kt u ξ z‖ + |p| * ‖W • ξ z‖ := by
    refine (norm_add_le _ _).trans_eq ?_
    rw [norm_smul, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_mul,
      abs_of_pos hW]
    ring
  have h₂ : (|p| * ‖W • ξ z‖) ^ 2 ≤ δ ^ 2 * ‖W • ξ z‖ ^ 2 := by
    rw [mul_pow, sq_abs]
    exact mul_le_mul_of_nonneg_right hp (sq_nonneg _)
  calc _ ≤ (W * ‖ω.floerLinearization J Ks Kt u ξ z‖ + |p| * ‖W • ξ z‖) ^ 2 := by gcongr
    _ ≤ 2 * ((W * ‖ω.floerLinearization J Ks Kt u ξ z‖) ^ 2 + (|p| * ‖W • ξ z‖) ^ 2) :=
        add_sq_le
    _ ≤ _ := by rw [he, mul_pow]; linarith

omit [FiniteDimensional ℝ V] in
/-- **The weighted energy density.** If `|ρ'(s)| ≤ δ`, the `e^{2ρ}`-weighted `W^{1,2}` energy
density of `ξ` at a point of the slice `s` is at most `2 + 2 δ²` times the unweighted energy
density of `η = e^{ρ} ξ`, since `e^{ρ} ∂s ξ = ∂s η - ρ' η` and `e^{ρ} ∂t ξ = ∂t η`. -/
private theorem exp_mul_sobolev_le {ρ : ℝ → ℝ} {ξ : ℝ × ℝ → V} {z : ℝ × ℝ} {δ : ℝ}
    (hρ : DifferentiableAt ℝ ρ z.1) (hρδ : |deriv ρ z.1| ≤ δ) (hξ : DifferentiableAt ℝ ξ z) :
    Real.exp (2 * ρ z.1) * (‖fderiv ℝ ξ z stdComplexLineReal‖ ^ 2 +
        ‖fderiv ℝ ξ z stdComplexLineImag‖ ^ 2 + ‖ξ z‖ ^ 2) ≤
      (2 + 2 * δ ^ 2) *
        (‖fderiv ℝ (fun w ↦ Real.exp (ρ w.1) • ξ w) z stdComplexLineReal‖ ^ 2 +
          ‖fderiv ℝ (fun w ↦ Real.exp (ρ w.1) • ξ w) z stdComplexLineImag‖ ^ 2 +
          ‖Real.exp (ρ z.1) • ξ z‖ ^ 2) := by
  -- `d(e^{ρ} ξ)(v) = e^{ρ} dξ(v) + v₁ ρ' e^{ρ} ξ`.
  have hc : HasFDerivAt (fun w : ℝ × ℝ ↦ Real.exp (ρ w.1))
      ((smulRight (1 : ℝ →L[ℝ] ℝ) (Real.exp (ρ z.1) * deriv ρ z.1)).comp (fst ℝ ℝ ℝ)) z :=
    hρ.hasDerivAt.exp.hasFDerivAt.comp z hasFDerivAt_fst
  have hd : HasFDerivAt (fun w ↦ Real.exp (ρ w.1) • ξ w) _ z := hc.smul hξ.hasFDerivAt
  rw [hd.fderiv]
  simp only [add_apply, smul_apply, smulRight_apply]
  set W := Real.exp (ρ z.1)
  set p := deriv ρ z.1
  have h₁ : (smulRight (1 : ℝ →L[ℝ] ℝ) (W * p)).comp (fst ℝ ℝ ℝ) stdComplexLineReal = W * p := by
    simp
  have h₀ : (smulRight (1 : ℝ →L[ℝ] ℝ) (W * p)).comp (fst ℝ ℝ ℝ) stdComplexLineImag = 0 := by
    simp
  rw [h₁, h₀, zero_smul, add_zero]
  have hW : 0 < W := Real.exp_pos _
  have he : Real.exp (2 * ρ z.1) = W ^ 2 := by rw [sq, ← Real.exp_add, two_mul]
  have hp : p ^ 2 ≤ δ ^ 2 := sq_le_sq' (abs_le.1 hρδ).1 (abs_le.1 hρδ).2
  -- `e^{ρ} ∂s ξ = ∂s η - ρ' η` for `η = e^{ρ} ξ`.
  have hs : W • fderiv ℝ ξ z stdComplexLineReal =
      (W • fderiv ℝ ξ z stdComplexLineReal + (W * p) • ξ z) - p • (W • ξ z) := by
    rw [smul_smul, mul_comm p W]
    abel
  have hs' : ‖W • fderiv ℝ ξ z stdComplexLineReal‖ ^ 2 ≤
      2 * ‖W • fderiv ℝ ξ z stdComplexLineReal + (W * p) • ξ z‖ ^ 2 +
        2 * δ ^ 2 * ‖W • ξ z‖ ^ 2 := by
    conv_lhs => rw [hs]
    calc _ ≤ (‖W • fderiv ℝ ξ z stdComplexLineReal + (W * p) • ξ z‖ + ‖p • (W • ξ z)‖) ^ 2 := by
          gcongr
          exact norm_sub_le _ _
      _ ≤ 2 * (‖W • fderiv ℝ ξ z stdComplexLineReal + (W * p) • ξ z‖ ^ 2 +
          ‖p • (W • ξ z)‖ ^ 2) := add_sq_le
      _ ≤ _ := by
          rw [norm_smul p, mul_pow, Real.norm_eq_abs, sq_abs]
          nlinarith [mul_le_mul_of_nonneg_right hp (sq_nonneg ‖W • ξ z‖)]
  rw [norm_smul W (fderiv ℝ ξ z stdComplexLineReal), norm_smul W (ξ z), Real.norm_eq_abs,
    abs_of_pos hW] at hs'
  rw [he, norm_smul W (fderiv ℝ ξ z stdComplexLineImag), norm_smul W (ξ z), Real.norm_eq_abs,
    abs_of_pos hW]
  nlinarith [sq_nonneg δ, sq_nonneg (W * ‖ξ z‖), sq_nonneg (W * ‖fderiv ℝ ξ z stdComplexLineImag‖),
    sq_nonneg ‖W • fderiv ℝ ξ z stdComplexLineReal + (W * p) • ξ z‖]

/-- **The weighted semi-Fredholm estimate from the unweighted one.** Let `J` be `C¹` and `K_s`,
`K_t` be `C²` at the points `(z, u z)`, and `u` be `C¹`. Suppose that the linearized Floer
operator `D_u` satisfies the semi-Fredholm estimate with constants `C ≥ 0` and `T`: every `C²`
map `ξ` of period one in `t` vanishing for `s ∉ (a, b)` satisfies

`∫ (‖∂s ξ‖² + ‖∂t ξ‖² + ‖ξ‖²) ≤ C (∫ ‖D_u ξ‖² + ∫_{[-T, T] × [0, 1]} ‖ξ‖²)`

over `[a, b] × [0, 1]`. Let `4 C δ² ≤ 1`. Then for every `C²` weight exponent `ρ` with
`|ρ'| ≤ δ` the same maps satisfy the weighted estimate

`∫ e^{2ρ} (‖∂s ξ‖² + ‖∂t ξ‖² + ‖ξ‖²) ≤ 8 (1 + δ²) C (∫ e^{2ρ} ‖D_u ξ‖² + ∫' e^{2ρ} ‖ξ‖²)`,

where `∫'` is the integral over `[-T, T] × [0, 1]` and `e^{2ρ}` is evaluated at the `s`
coordinate. -/
theorem setIntegral_exp_mul_le_mul_setIntegral_floerLinearization_add (ω : SymplecticForm V)
    {J : ℝ × ℝ → V → V →L[ℝ] V} {Ks Kt : ℝ × ℝ → V → ℝ} {u : ℝ × ℝ → V}
    (hJ : ∀ z, ContDiffAt ℝ 1 (uncurry J) (z, u z))
    (hKs : ∀ z, ContDiffAt ℝ 2 (uncurry Ks) (z, u z))
    (hKt : ∀ z, ContDiffAt ℝ 2 (uncurry Kt) (z, u z)) (hu : ContDiff ℝ 1 u) {C T δ : ℝ}
    (hC : 0 ≤ C) (hδ : 4 * C * δ ^ 2 ≤ 1)
    (hest : ∀ ⦃ξ : ℝ × ℝ → V⦄, ContDiff ℝ 2 ξ → (∀ s t, ξ (s, t + 1) = ξ (s, t)) →
      ∀ ⦃a b : ℝ⦄, a ≤ b → (∀ s t, s ∉ Ioo a b → ξ (s, t) = 0) →
        ∫ z in Icc a b ×ˢ Icc (0 : ℝ) 1, (‖fderiv ℝ ξ z stdComplexLineReal‖ ^ 2 +
            ‖fderiv ℝ ξ z stdComplexLineImag‖ ^ 2 + ‖ξ z‖ ^ 2) ≤
          C * ((∫ z in Icc a b ×ˢ Icc (0 : ℝ) 1, ‖ω.floerLinearization J Ks Kt u ξ z‖ ^ 2) +
            ∫ z in Icc (-T) T ×ˢ Icc (0 : ℝ) 1, ‖ξ z‖ ^ 2))
    {ρ : ℝ → ℝ} (hρ : ContDiff ℝ 2 ρ) (hρδ : ∀ s, |deriv ρ s| ≤ δ) {ξ : ℝ × ℝ → V}
    (hξ : ContDiff ℝ 2 ξ) (hper : ∀ s t, ξ (s, t + 1) = ξ (s, t)) {a b : ℝ} (hab : a ≤ b)
    (hξ₀ : ∀ s t, s ∉ Ioo a b → ξ (s, t) = 0) :
    ∫ z in Icc a b ×ˢ Icc (0 : ℝ) 1, Real.exp (2 * ρ z.1) *
        (‖fderiv ℝ ξ z stdComplexLineReal‖ ^ 2 + ‖fderiv ℝ ξ z stdComplexLineImag‖ ^ 2 +
          ‖ξ z‖ ^ 2) ≤
      8 * (1 + δ ^ 2) * C * ((∫ z in Icc a b ×ˢ Icc (0 : ℝ) 1,
          Real.exp (2 * ρ z.1) * ‖ω.floerLinearization J Ks Kt u ξ z‖ ^ 2) +
        ∫ z in Icc (-T) T ×ˢ Icc (0 : ℝ) 1, Real.exp (2 * ρ z.1) * ‖ξ z‖ ^ 2) := by
  -- The weighted section `η = e^{ρ(s)} ξ`, of period one and vanishing for `s ∉ (a, b)`.
  set η : ℝ × ℝ → V := fun w ↦ Real.exp (ρ w.1) • ξ w
  have hη : ContDiff ℝ 2 η := ((hρ.comp contDiff_fst).exp).smul hξ
  have hI {f : ℝ × ℝ → ℝ} (hf : Continuous f) (p q : ℝ) :
      IntegrableOn f (Icc p q ×ˢ Icc (0 : ℝ) 1) :=
    hf.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  have hR (p q : ℝ) : MeasurableSet (Icc p q ×ˢ Icc (0 : ℝ) 1) :=
    measurableSet_Icc.prod measurableSet_Icc
  have := hρ.continuous; have := hξ.continuous; have := hξ.continuous_fderiv two_ne_zero
  have := hη.continuous; have := hη.continuous_fderiv two_ne_zero
  set Eη := ∫ z in Icc a b ×ˢ Icc (0 : ℝ) 1, (‖fderiv ℝ η z stdComplexLineReal‖ ^ 2 +
    ‖fderiv ℝ η z stdComplexLineImag‖ ^ 2 + ‖η z‖ ^ 2)
  set X := ∫ z in Icc a b ×ˢ Icc (0 : ℝ) 1,
    Real.exp (2 * ρ z.1) * ‖ω.floerLinearization J Ks Kt u ξ z‖ ^ 2
  set Y := ∫ z in Icc (-T) T ×ˢ Icc (0 : ℝ) 1, Real.exp (2 * ρ z.1) * ‖ξ z‖ ^ 2
  have hY : 0 ≤ Y := setIntegral_nonneg (hR _ _) fun _ _ ↦ by positivity
  have hEη : 0 ≤ Eη := setIntegral_nonneg (hR _ _) fun _ _ ↦ by positivity
  -- The unweighted estimate for `η`; on `[-T, T]` its norm is the weighted norm of `ξ`.
  have h₁ := hest hη (fun s t ↦ by simp only [η, hper])
    hab fun s t hs ↦ by simp only [η, hξ₀ s t hs, smul_zero]
  have h₃ : ∫ z in Icc (-T) T ×ˢ Icc (0 : ℝ) 1, ‖η z‖ ^ 2 = Y :=
    setIntegral_congr_fun (hR _ _) fun z _ ↦ by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), mul_pow, sq (Real.exp _),
        ← Real.exp_add, ← two_mul]
  -- The operator on `η` is the weighted operator on `ξ`, up to `δ ‖η‖ ≤ δ Eη`.
  have hN : ∫ z in Icc a b ×ˢ Icc (0 : ℝ) 1, ‖η z‖ ^ 2 ≤ Eη :=
    setIntegral_mono_on (hI (by fun_prop) _ _) (hI (by fun_prop) _ _) (hR _ _) fun z _ ↦ by
      have := sq_nonneg ‖fderiv ℝ η z stdComplexLineReal‖
      have := sq_nonneg ‖fderiv ℝ η z stdComplexLineImag‖
      linarith
  have h₂ : ∫ z in Icc a b ×ˢ Icc (0 : ℝ) 1, ‖ω.floerLinearization J Ks Kt u η z‖ ^ 2 ≤
      2 * X + 2 * δ ^ 2 * Eη :=
    (ω.setIntegral_norm_floerLinearization_exp_smul_sq_le hJ hKs hKt hu hρ hρδ hξ a b).trans
      (by gcongr)
  -- The weighted energy of `ξ` is controlled by the energy of `η`.
  have h₄ : ∫ z in Icc a b ×ˢ Icc (0 : ℝ) 1, Real.exp (2 * ρ z.1) *
      (‖fderiv ℝ ξ z stdComplexLineReal‖ ^ 2 + ‖fderiv ℝ ξ z stdComplexLineImag‖ ^ 2 +
        ‖ξ z‖ ^ 2) ≤ (2 + 2 * δ ^ 2) * Eη := by
    rw [← integral_const_mul]
    exact setIntegral_mono_on (hI (by fun_prop) _ _) (hI (by fun_prop) _ _) (hR _ _) fun z _ ↦
      exp_mul_sobolev_le (hρ.differentiable two_ne_zero z.1) (hρδ z.1)
        (hξ.differentiable two_ne_zero z)
  -- Absorb `2 C δ² Eη ≤ Eη / 2` into the left side.
  rw [h₃] at h₁
  have h₅ : Eη ≤ 4 * C * (X + Y) := by
    have := mul_le_mul_of_nonneg_left h₂ hC
    nlinarith [mul_le_mul_of_nonneg_right hδ hEη, mul_nonneg hC hY]
  calc _ ≤ (2 + 2 * δ ^ 2) * Eη := h₄
    _ ≤ (2 + 2 * δ ^ 2) * (4 * C * (X + Y)) := by gcongr
    _ = _ := by ring

/-- **The weighted semi-Fredholm estimate along a Floer trajectory.** Under the hypotheses of the
unweighted estimate `exists_forall_setIntegral_le_mul_setIntegral_floerLinearization_add`, for a
Floer trajectory `u` from `xm` to `xp` between nondegenerate one-periodic orbits, there are
`C ≥ 0`, `T` and `δ > 0` such that for every `C²` weight exponent `ρ` with `|ρ'| ≤ δ`, every
`C²` map `ξ` of period one in `t` that vanishes for `s ∉ (a, b)` satisfies

`∫ e^{2ρ} (‖∂s ξ‖² + ‖∂t ξ‖² + ‖ξ‖²) ≤ C (∫ e^{2ρ} ‖D_u ξ‖² + ∫_{[-T, T] × [0, 1]} e^{2ρ} ‖ξ‖²)`

over `[a, b] × [0, 1]`, for the linearized Floer operator `D_u` of the datum `K = H_t dt`. The
constants do not depend on `ρ`, `ξ`, `a` or `b`. -/
theorem exists_forall_setIntegral_exp_mul_le_mul_setIntegral_floerLinearization_add
    (ω : SymplecticForm V) {H : ℝ → V → ℝ} {K : ℝ≥0}
    (hX : LipschitzWith K (ω.timeDependentHamiltonianSuspension H))
    (hH : ContDiff ℝ 2 (Function.uncurry H)) {xm xp : ℝ → V}
    (hxm : ∀ t, HasDerivAt xm (ω.hamiltonianVectorField (H t) (xm t)) t)
    (hndm : IsNondegenerateFixedPt 𝓘(ℝ, V) (ω.timeDependentHamiltonianFlow H hX 0 1) (xm 0))
    (hxp : ∀ t, HasDerivAt xp (ω.hamiltonianVectorField (H t) (xp t)) t)
    (hndp : IsNondegenerateFixedPt 𝓘(ℝ, V) (ω.timeDependentHamiltonianFlow H hX 0 1) (xp 0))
    {J : ℝ → V → AlmostComplexStructure V}
    (hJ : ContDiff ℝ 1 fun p : ℝ × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap)
    (hJxm : ∀ t, ω.Compatible (J t (xm t))) (hJxp : ∀ t, ω.Compatible (J t (xp t)))
    {u : ℝ × ℝ → V} (hu : ContDiff ℝ 1 u) (hJu : ∀ z, ω.Compatible (J z.2 (u z)))
    (huxm : TendstoUniformlyOn (fun s t ↦ u (s, t)) xm atBot (Icc 0 1))
    (huxp : TendstoUniformlyOn (fun s t ↦ u (s, t)) xp atTop (Icc 0 1))
    (hδm : TendstoUniformlyOn
      (fun s t ↦ sliceDefect (fun t ↦ ω.hamiltonianVectorField (H t)) u (s, t)) 0 atBot (Icc 0 1))
    (hδp : TendstoUniformlyOn
      (fun s t ↦ sliceDefect (fun t ↦ ω.hamiltonianVectorField (H t)) u (s, t)) 0 atTop
        (Icc 0 1)) :
    ∃ C, 0 ≤ C ∧ ∃ T, ∃ δ > 0, ∀ ⦃ρ : ℝ → ℝ⦄, ContDiff ℝ 2 ρ → (∀ s, |deriv ρ s| ≤ δ) →
      ∀ ⦃ξ : ℝ × ℝ → V⦄, ContDiff ℝ 2 ξ → (∀ s t, ξ (s, t + 1) = ξ (s, t)) →
      ∀ ⦃a b : ℝ⦄, a ≤ b → (∀ s t, s ∉ Ioo a b → ξ (s, t) = 0) →
        ∫ z in Icc a b ×ˢ Icc (0 : ℝ) 1, Real.exp (2 * ρ z.1) *
            (‖fderiv ℝ ξ z stdComplexLineReal‖ ^ 2 + ‖fderiv ℝ ξ z stdComplexLineImag‖ ^ 2 +
              ‖ξ z‖ ^ 2) ≤
          C * ((∫ z in Icc a b ×ˢ Icc (0 : ℝ) 1, Real.exp (2 * ρ z.1) * ‖ω.floerLinearization
            (fun w y ↦ (J w.2 y).toLinearMap.toContinuousLinearMap) (fun _ _ ↦ 0)
            (fun w ↦ H w.2) u ξ z‖ ^ 2) +
            ∫ z in Icc (-T) T ×ˢ Icc (0 : ℝ) 1, Real.exp (2 * ρ z.1) * ‖ξ z‖ ^ 2) := by
  obtain ⟨C, hC, T, hest⟩ := ω.exists_forall_setIntegral_le_mul_setIntegral_floerLinearization_add
    hX hH hxm hndm hxp hndp hJ hJxm hJxp hu hJu huxm huxp hδm hδp
  set δ := 1 / (2 * (C + 1))
  have hδ : 4 * C * δ ^ 2 ≤ 1 := by
    have h : 4 * C * δ ^ 2 = C / (C + 1) ^ 2 := by
      simp only [δ]
      field_simp
      ring
    rw [h, div_le_one (by positivity)]
    nlinarith
  refine ⟨8 * (1 + δ ^ 2) * C, by positivity, T, δ, by positivity,
    fun ρ hρ hρδ ξ hξ hper a b hab hξ₀ ↦ ?_⟩
  exact ω.setIntegral_exp_mul_le_mul_setIntegral_floerLinearization_add
    (J := fun w y ↦ (J w.2 y).toLinearMap.toContinuousLinearMap) (Ks := fun _ _ ↦ 0)
    (Kt := fun w ↦ H w.2) (fun _ ↦ (hJ.comp (contDiff_fst.snd.prodMk contDiff_snd)).contDiffAt)
    (fun _ ↦ contDiffAt_const) (fun _ ↦ (hH.comp (contDiff_fst.snd.prodMk contDiff_snd)).contDiffAt)
    hu hC hδ hest hρ hρδ hξ hper hab hξ₀

/-- **The semi-Fredholm estimate with weight `e^{δ ⟨s⟩}`.** Under the hypotheses of
`exists_forall_setIntegral_exp_mul_le_mul_setIntegral_floerLinearization_add`, there are `C ≥ 0`,
`T` and `δ₀ > 0` such that for every `|δ| ≤ δ₀` the estimate holds with the weight
`e^{2 δ √(1 + s²)}`, which is comparable to `e^{2 δ |s|}`. For `δ > 0` these are the weighted norms
forcing exponential decay of sections at both ends of the cylinder. -/
theorem exists_forall_setIntegral_exp_mul_sqrt_le_mul_setIntegral_floerLinearization_add
    (ω : SymplecticForm V) {H : ℝ → V → ℝ} {K : ℝ≥0}
    (hX : LipschitzWith K (ω.timeDependentHamiltonianSuspension H))
    (hH : ContDiff ℝ 2 (Function.uncurry H)) {xm xp : ℝ → V}
    (hxm : ∀ t, HasDerivAt xm (ω.hamiltonianVectorField (H t) (xm t)) t)
    (hndm : IsNondegenerateFixedPt 𝓘(ℝ, V) (ω.timeDependentHamiltonianFlow H hX 0 1) (xm 0))
    (hxp : ∀ t, HasDerivAt xp (ω.hamiltonianVectorField (H t) (xp t)) t)
    (hndp : IsNondegenerateFixedPt 𝓘(ℝ, V) (ω.timeDependentHamiltonianFlow H hX 0 1) (xp 0))
    {J : ℝ → V → AlmostComplexStructure V}
    (hJ : ContDiff ℝ 1 fun p : ℝ × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap)
    (hJxm : ∀ t, ω.Compatible (J t (xm t))) (hJxp : ∀ t, ω.Compatible (J t (xp t)))
    {u : ℝ × ℝ → V} (hu : ContDiff ℝ 1 u) (hJu : ∀ z, ω.Compatible (J z.2 (u z)))
    (huxm : TendstoUniformlyOn (fun s t ↦ u (s, t)) xm atBot (Icc 0 1))
    (huxp : TendstoUniformlyOn (fun s t ↦ u (s, t)) xp atTop (Icc 0 1))
    (hδm : TendstoUniformlyOn
      (fun s t ↦ sliceDefect (fun t ↦ ω.hamiltonianVectorField (H t)) u (s, t)) 0 atBot (Icc 0 1))
    (hδp : TendstoUniformlyOn
      (fun s t ↦ sliceDefect (fun t ↦ ω.hamiltonianVectorField (H t)) u (s, t)) 0 atTop
        (Icc 0 1)) :
    ∃ C, 0 ≤ C ∧ ∃ T, ∃ δ₀ > 0, ∀ ⦃δ : ℝ⦄, |δ| ≤ δ₀ →
      ∀ ⦃ξ : ℝ × ℝ → V⦄, ContDiff ℝ 2 ξ → (∀ s t, ξ (s, t + 1) = ξ (s, t)) →
      ∀ ⦃a b : ℝ⦄, a ≤ b → (∀ s t, s ∉ Ioo a b → ξ (s, t) = 0) →
        ∫ z in Icc a b ×ˢ Icc (0 : ℝ) 1, Real.exp (2 * (δ * √(1 + z.1 ^ 2))) *
            (‖fderiv ℝ ξ z stdComplexLineReal‖ ^ 2 + ‖fderiv ℝ ξ z stdComplexLineImag‖ ^ 2 +
              ‖ξ z‖ ^ 2) ≤
          C * ((∫ z in Icc a b ×ˢ Icc (0 : ℝ) 1,
              Real.exp (2 * (δ * √(1 + z.1 ^ 2))) * ‖ω.floerLinearization
            (fun w y ↦ (J w.2 y).toLinearMap.toContinuousLinearMap) (fun _ _ ↦ 0)
            (fun w ↦ H w.2) u ξ z‖ ^ 2) +
            ∫ z in Icc (-T) T ×ˢ Icc (0 : ℝ) 1,
              Real.exp (2 * (δ * √(1 + z.1 ^ 2))) * ‖ξ z‖ ^ 2) := by
  obtain ⟨C, hC, T, δ₀, hδ₀, h⟩ :=
    ω.exists_forall_setIntegral_exp_mul_le_mul_setIntegral_floerLinearization_add hX hH hxm hndm
      hxp hndp hJ hJxm hJxp hu hJu huxm huxp hδm hδp
  refine ⟨C, hC, T, δ₀, hδ₀, fun δ hδ ↦ h (ρ := fun s ↦ δ * √(1 + s ^ 2)) ?_ fun s ↦ ?_⟩
  · exact contDiff_const.mul ((contDiff_const.add (contDiff_id.pow 2)).sqrt fun s ↦ by positivity)
  · -- `ρ' = δ s / √(1 + s²)`, and `|s| ≤ √(1 + s²)`.
    have hpos : 0 < 1 + s ^ 2 := by positivity
    have h1 : HasDerivAt (fun s ↦ 1 + s ^ 2) (2 * s) s := by
      simpa using (hasDerivAt_pow 2 s).const_add 1
    have hq : |2 * s / (2 * √(1 + s ^ 2))| ≤ 1 := by
      rw [mul_div_mul_left _ _ two_ne_zero, abs_div, abs_of_pos (Real.sqrt_pos.2 hpos)]
      exact div_le_one_of_le₀ (Real.abs_le_sqrt (by linarith)) (Real.sqrt_nonneg _)
    rw [((h1.sqrt hpos.ne').const_mul δ).deriv, abs_mul]
    calc _ ≤ |δ| * 1 := by gcongr
      _ ≤ δ₀ := by rwa [mul_one]

end TauCeti.SymplecticForm
