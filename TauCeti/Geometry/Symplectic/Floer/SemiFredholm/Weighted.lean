/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.FDeriv.ExpSmul
public import TauCeti.Geometry.Symplectic.Floer.SemiFredholm

/-!
# The weighted semi-Fredholm estimate of the linearized Floer operator on a cylinder

Let `(V, ω)` be a finite-dimensional symplectic vector space and `D_u` the linearized Floer
operator (`TauCeti.SymplecticForm.floerLinearization`) along a map `u : ℝ × ℝ → V` of period one
in `t`. The Fredholm theory used for gluing and for index computations works in the Sobolev
spaces with an exponential weight `e^{κ(s)}`, where `κ` is a smooth function of the longitudinal
coordinate with small slope, for instance `κ(s) = δ s`, or a function equal to `δ₊ s` near `+∞`
and to `δ₋ s` near `-∞`. The weighted form of the semi-Fredholm estimate is

`∫ e^{2κ} (‖∂s η‖² + ‖∂t η‖² + ‖η‖²) ≤ C (∫ e^{2κ} ‖D_u η‖² + ∫_{[-T, T] × S¹} e^{2κ} ‖η‖²)`

for sections `η` of compact support, with `C` and `T` independent of `η` and of the weight.

The weighted estimate follows from the unweighted one for every weight of small enough slope,
with no further input on the ends. The map `ξ = e^{κ(s)} η` has
`D_u ξ = e^{κ} D_u η + κ' ξ` (`TauCeti.SymplecticForm.floerLinearization_smul_fst`) and
`∂s ξ = e^{κ} (∂s η + κ' η)`, `∂t ξ = e^{κ} ∂t η`. So the weighted norms of `η` and `D_u η` are
the unweighted norms of `ξ` and of `D_u ξ - κ' ξ`, up to the bounded multiplication by `κ'`. If
`|κ'| ≤ ε` with `C₁ ε²` small, the unweighted estimate `W(ξ) ≤ C₁ (‖D_u ξ‖² + ‖ξ‖²_{[-T, T]})`
absorbs the error `ε² ‖ξ‖² ≤ ε² W(ξ)`.

* `SymplecticForm.setIntegral_exp_mul_le_mul_setIntegral_floerLinearization_add` derives the
  weighted estimate, with constant `8 C₁`, for every `C²` weight `κ` with
  `|κ'| ≤ (2 (C₁ + 1))⁻¹`, from any unweighted semi-Fredholm estimate with constant `C₁` for data
  `J`, `K_s`, `K_t` that are regular along `u`.
* `SymplecticForm.exists_pos_forall_setIntegral_exp_mul_le_mul_setIntegral_floerLinearization_add`
  is the weighted estimate along a Floer trajectory between nondegenerate orbits, from the
  unweighted estimate `exists_forall_setIntegral_le_mul_setIntegral_floerLinearization_add`.
* `SymplecticForm.exists_forall_setIntegral_le_mul_setIntegral_floerLinearization_sub_smul_add`
  is the weighted estimate along a Floer trajectory for weights of any slope, read as the
  estimate of `D_u - κ'(s)` on `ξ = e^{κ} η`, when `κ'` equals constants `δ±` near `±∞` for which
  the shifted fields `dX_{H_t}(x±(t)) - δ± J_t(x±(t))` have nondegenerate return maps; for
  one-periodic data this says that `δ±` are not eigenvalues of the asymptotic operators at the
  ends. It is a case of
  `exists_forall_setIntegral_le_mul_setIntegral_floerLinearization_sub_smul_add_of_cylindrical`,
  in `TauCeti.Geometry.Symplectic.Floer.SemiFredholm`.

Sections are `C²` maps `η : ℝ × ℝ → V` of period one in `t` that vanish outside a strip
`(a, b) × ℝ`, and the integrals are over the fundamental domain `[a, b] × [0, 1]`. The Sobolev
completion and the Fredholm property itself are not treated here.

## References

* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), Lecture 2, on the Fredholm property of `∂s + J ∂t + S(s, t)` in weighted
  Sobolev spaces.
* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, 2nd ed., Section 3.1
  and Chapter 10, on the semi-Fredholm estimate and exponential weights on cylindrical ends.
-/

public section

open Set Function MeasureTheory
open scoped NNReal Manifold

namespace TauCeti.SymplecticForm

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- Since `D_u (e^{κ} η) = e^{κ} D_u η + κ' e^{κ} η`, the square of its norm is at most
`2 e^{2κ} ‖D_u η‖² + 2 ε² ‖e^{κ} η‖²` when `|κ'| ≤ ε`. -/
private theorem norm_floerLinearization_exp_smul_sq_le (ω : SymplecticForm V)
    (J : ℝ × ℝ → V → V →L[ℝ] V) (Ks Kt : ℝ × ℝ → V → ℝ) (u : ℝ × ℝ → V) {κ : ℝ → ℝ}
    {κ' ε : ℝ} {η : ℝ × ℝ → V} {z : ℝ × ℝ} (hκ : HasDerivAt κ κ' z.1)
    (hη : DifferentiableAt ℝ η z) (hκ' : |κ'| ≤ ε) :
    ‖ω.floerLinearization J Ks Kt u (fun w ↦ Real.exp (κ w.1) • η w) z‖ ^ 2 ≤
      2 * (Real.exp (2 * κ z.1) * ‖ω.floerLinearization J Ks Kt u η z‖ ^ 2) +
        2 * ε ^ 2 * ‖Real.exp (κ z.1) • η z‖ ^ 2 := by
  rw [ω.floerLinearization_smul_fst J Ks Kt u η hκ.exp hη, mul_comm (Real.exp (κ z.1)),
    ← smul_smul]
  refine (pow_le_pow_left₀ (norm_nonneg _) (norm_add_le _ _) 2).trans (add_sq_le.trans ?_)
  rw [norm_exp_smul_sq, norm_smul _ (Real.exp (κ z.1) • η z), Real.norm_eq_abs, mul_pow, sq_abs]
  have : κ' ^ 2 ≤ ε ^ 2 := sq_le_sq' (neg_le_of_abs_le hκ') (le_of_abs_le hκ')
  have : 0 ≤ ‖Real.exp (κ z.1) • η z‖ ^ 2 := by positivity
  nlinarith

omit [FiniteDimensional ℝ V] in
/-- With `ξ = e^{κ(s)} η` and `|κ'| ≤ 1 / 2`, `e^{2κ}` times the `W^{1,2}` energy density of `η`
is at most twice the energy density of `ξ`, since `e^{κ} ∂s η = ∂s ξ - κ' ξ` and
`e^{κ} ∂t η = ∂t ξ`. -/
private theorem exp_mul_sobolev_le {κ : ℝ → ℝ} {κ' : ℝ} {η : ℝ × ℝ → V} {z : ℝ × ℝ}
    (hκ : HasDerivAt κ κ' z.1) (hη : DifferentiableAt ℝ η z) (hκ' : |κ'| ≤ 1 / 2) :
    Real.exp (2 * κ z.1) *
        (‖fderiv ℝ η z stdComplexLineReal‖ ^ 2 + ‖fderiv ℝ η z stdComplexLineImag‖ ^ 2 +
          ‖η z‖ ^ 2) ≤
      2 * (‖fderiv ℝ (fun w ↦ Real.exp (κ w.1) • η w) z stdComplexLineReal‖ ^ 2 +
        ‖fderiv ℝ (fun w ↦ Real.exp (κ w.1) • η w) z stdComplexLineImag‖ ^ 2 +
          ‖Real.exp (κ z.1) • η z‖ ^ 2) := by
  simp only [fderiv_exp_smul_apply (φ := fun w ↦ κ w.1) (hκ.hasFDerivAt.comp z hasFDerivAt_fst)
      hη, ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst', stdComplexLineReal_fst,
    stdComplexLineImag_fst, map_zero, zero_smul, add_zero, norm_exp_smul_sq,
    ContinuousLinearMap.toSpanSingleton_apply, one_smul]
  have h := norm_sub_le (fderiv ℝ η z stdComplexLineReal + κ' • η z) (κ' • η z)
  rw [add_sub_cancel_right, norm_smul, Real.norm_eq_abs] at h
  have hκη : |κ'| * ‖η z‖ ≤ ‖η z‖ / 2 := by nlinarith [norm_nonneg (η z)]
  have h₂ : ‖fderiv ℝ η z stdComplexLineReal‖ ^ 2 ≤
      2 * ‖fderiv ℝ η z stdComplexLineReal + κ' • η z‖ ^ 2 + ‖η z‖ ^ 2 := by
    have := (pow_le_pow_left₀ (norm_nonneg _) h 2).trans add_sq_le
    nlinarith [pow_le_pow_left₀ (by positivity) hκη 2]
  have : 0 ≤ Real.exp (2 * κ z.1) * ‖η z‖ ^ 2 := by positivity
  have : 0 ≤ Real.exp (2 * κ z.1) * ‖fderiv ℝ η z stdComplexLineImag‖ ^ 2 := by positivity
  nlinarith [mul_le_mul_of_nonneg_left h₂ (Real.exp_pos (2 * κ z.1)).le]

/-- **Absorption of the weight.** Under the hypotheses of
`setIntegral_exp_mul_le_mul_setIntegral_floerLinearization_add`, the unweighted `W^{1,2}` energy
`W` of `ξ = e^{κ(s)} η` satisfies `W ≤ 4 C₁ X + 2 C₁ Y`, where `X` and `Y` are the weighted `L²`
norms of `D_u η` over `[a, b] × [0, 1]` and of `η` over `[-T, T] × [0, 1]`. The error
`2 C₁ ε² W ≤ W / 2` of `D_u ξ - e^{κ} D_u η = κ' ξ` is absorbed into the left side. -/
private theorem setIntegral_sobolev_exp_smul_le (ω : SymplecticForm V)
    {J : ℝ × ℝ → V → V →L[ℝ] V} {Ks Kt : ℝ × ℝ → V → ℝ} {u : ℝ × ℝ → V}
    (hJ : ∀ z, ContDiffAt ℝ 1 (uncurry J) (z, u z))
    (hKs : ∀ z, ContDiffAt ℝ 2 (uncurry Ks) (z, u z))
    (hKt : ∀ z, ContDiffAt ℝ 2 (uncurry Kt) (z, u z)) (hu : ContDiff ℝ 1 u) {C₁ T : ℝ}
    (hC₁ : 0 ≤ C₁)
    (hest : ∀ ⦃ξ : ℝ × ℝ → V⦄, ContDiff ℝ 2 ξ → (∀ s t, ξ (s, t + 1) = ξ (s, t)) →
      ∀ ⦃a b : ℝ⦄, a ≤ b → (∀ s t, s ∉ Ioo a b → ξ (s, t) = 0) →
        ∫ z in Icc a b ×ˢ Icc (0 : ℝ) 1, (‖fderiv ℝ ξ z stdComplexLineReal‖ ^ 2 +
            ‖fderiv ℝ ξ z stdComplexLineImag‖ ^ 2 + ‖ξ z‖ ^ 2) ≤
          C₁ * ((∫ z in Icc a b ×ˢ Icc (0 : ℝ) 1, ‖ω.floerLinearization J Ks Kt u ξ z‖ ^ 2) +
            ∫ z in Icc (-T) T ×ˢ Icc (0 : ℝ) 1, ‖ξ z‖ ^ 2))
    {κ : ℝ → ℝ} (hκ : ContDiff ℝ 2 κ) (hκ' : ∀ s, |deriv κ s| ≤ (2 * (C₁ + 1))⁻¹)
    {η : ℝ × ℝ → V} (hη : ContDiff ℝ 2 η) (hper : ∀ s t, η (s, t + 1) = η (s, t)) {a b : ℝ}
    (hab : a ≤ b) (hη₀ : ∀ s t, s ∉ Ioo a b → η (s, t) = 0) :
    ∫ z in Icc a b ×ˢ Icc (0 : ℝ) 1,
        (‖fderiv ℝ (fun w ↦ Real.exp (κ w.1) • η w) z stdComplexLineReal‖ ^ 2 +
          ‖fderiv ℝ (fun w ↦ Real.exp (κ w.1) • η w) z stdComplexLineImag‖ ^ 2 +
            ‖Real.exp (κ z.1) • η z‖ ^ 2) ≤
      4 * C₁ * (∫ z in Icc a b ×ˢ Icc (0 : ℝ) 1,
          Real.exp (2 * κ z.1) * ‖ω.floerLinearization J Ks Kt u η z‖ ^ 2) +
        2 * C₁ * ∫ z in Icc (-T) T ×ˢ Icc (0 : ℝ) 1, Real.exp (2 * κ z.1) * ‖η z‖ ^ 2 := by
  set ε := (2 * (C₁ + 1))⁻¹
  have hεC : 2 * C₁ * ε ^ 2 ≤ 1 / 2 := by
    have hε : 2 * (C₁ + 1) * ε = 1 := mul_inv_cancel₀ (by positivity)
    have : 0 ≤ ε := by positivity
    nlinarith [mul_nonneg (mul_nonneg hC₁ this) this]
  have hξ : ContDiff ℝ 2 fun w : ℝ × ℝ ↦ Real.exp (κ w.1) • η w :=
    ((Real.contDiff_exp.comp hκ).comp contDiff_fst).smul hη
  have hI {f : ℝ × ℝ → ℝ} (hf : Continuous f) (p q : ℝ) :
      IntegrableOn f (Icc p q ×ˢ Icc (0 : ℝ) 1) :=
    hf.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  have hrect : MeasurableSet (Icc a b ×ˢ Icc (0 : ℝ) 1) := measurableSet_Icc.prod measurableSet_Icc
  have : Continuous fun z : ℝ × ℝ ↦ Real.exp (2 * κ z.1) := by
    have := hκ.continuous
    fun_prop
  have hDη := ω.continuous_floerLinearization hJ hKs hKt hu (hη.of_le one_le_two)
  have hDξ := ω.continuous_floerLinearization hJ hKs hKt hu (hξ.of_le one_le_two)
  have := hξ.continuous
  have hdξ := hξ.continuous_fderiv two_ne_zero
  have := hη.continuous
  have := hκ.continuous
  -- `∫ ‖ξ‖² ≤ W` for the energy `W` of `ξ = e^{κ} η`.
  have hN : ∫ z in Icc a b ×ˢ Icc (0 : ℝ) 1, ‖Real.exp (κ z.1) • η z‖ ^ 2 ≤
      ∫ z in Icc a b ×ˢ Icc (0 : ℝ) 1,
        (‖fderiv ℝ (fun w ↦ Real.exp (κ w.1) • η w) z stdComplexLineReal‖ ^ 2 +
          ‖fderiv ℝ (fun w ↦ Real.exp (κ w.1) • η w) z stdComplexLineImag‖ ^ 2 +
            ‖Real.exp (κ z.1) • η z‖ ^ 2) :=
    setIntegral_mono_on (hI (by fun_prop) _ _) (hI (by fun_prop) _ _) hrect fun z _ ↦ by
      have : 0 ≤ ‖fderiv ℝ (fun w ↦ Real.exp (κ w.1) • η w) z stdComplexLineReal‖ ^ 2 := by
        positivity
      have : 0 ≤ ‖fderiv ℝ (fun w ↦ Real.exp (κ w.1) • η w) z stdComplexLineImag‖ ^ 2 := by
        positivity
      linarith
  -- `∫ ‖D_u ξ‖² ≤ 2 X + 2 ε² ∫ ‖ξ‖²`.
  have hDX := (setIntegral_mono_on (hI (by fun_prop) _ _) (hI (by fun_prop) _ _) hrect
    fun z _ ↦ norm_floerLinearization_exp_smul_sq_le ω J Ks Kt u
      (hκ.differentiable two_ne_zero z.1).hasDerivAt (hη.differentiable two_ne_zero z)
      (hκ' z.1)).trans_eq (by
    rw [integral_add (hI (by fun_prop) _ _) (hI (by fun_prop) _ _), integral_const_mul,
      integral_const_mul])
  -- The unweighted estimate for `ξ`, whose `[-T, T]` term is the weighted one of `η`.
  have hWest := hest hξ (fun s t ↦ by simp only [hper]) hab fun s t hs ↦ by
    simp only [hη₀ s t hs, smul_zero]
  beta_reduce at hWest
  rw [setIntegral_congr_fun (measurableSet_Icc.prod measurableSet_Icc)
    fun z _ ↦ norm_exp_smul_sq (κ z.1) (η z)] at hWest
  have hW₀ := le_trans (setIntegral_nonneg hrect fun _ _ ↦ by positivity) hN
  have : 0 ≤ ∫ z in Icc (-T) T ×ˢ Icc (0 : ℝ) 1, Real.exp (2 * κ z.1) * ‖η z‖ ^ 2 :=
    setIntegral_nonneg (measurableSet_Icc.prod measurableSet_Icc) fun _ _ ↦ by positivity
  -- Absorb `2 C₁ ε² W ≤ W / 2`.
  nlinarith [mul_le_mul_of_nonneg_left hDX hC₁, mul_le_mul_of_nonneg_left hN
    (by positivity : (0 : ℝ) ≤ C₁ * (2 * ε ^ 2)), mul_le_mul_of_nonneg_right hεC hW₀]

/-- **The weighted semi-Fredholm estimate from the unweighted one.** Let `J`, `K_s`, `K_t` be
`C¹`, `C²`, `C²` at the points `(z, u z)` along a `C¹` map `u`, and suppose that the linearized
Floer operator `D_u` satisfies the semi-Fredholm estimate

`∫ (‖∂s ξ‖² + ‖∂t ξ‖² + ‖ξ‖²) ≤ C₁ (∫ ‖D_u ξ‖² + ∫_{[-T, T] × [0, 1]} ‖ξ‖²)`

over `[a, b] × [0, 1]` for every `C²` map `ξ` of period one in `t` vanishing for `s ∉ (a, b)`.
Then for every `C²` weight `κ(s)` with `|κ'| ≤ (2 (C₁ + 1))⁻¹`, every such `η` satisfies

`∫ e^{2κ} (‖∂s η‖² + ‖∂t η‖² + ‖η‖²) ≤ 8 C₁ (∫ e^{2κ} ‖D_u η‖² + ∫_{[-T, T] × [0, 1]} e^{2κ} ‖η‖²)`.
-/
theorem setIntegral_exp_mul_le_mul_setIntegral_floerLinearization_add (ω : SymplecticForm V)
    {J : ℝ × ℝ → V → V →L[ℝ] V} {Ks Kt : ℝ × ℝ → V → ℝ} {u : ℝ × ℝ → V}
    (hJ : ∀ z, ContDiffAt ℝ 1 (uncurry J) (z, u z))
    (hKs : ∀ z, ContDiffAt ℝ 2 (uncurry Ks) (z, u z))
    (hKt : ∀ z, ContDiffAt ℝ 2 (uncurry Kt) (z, u z)) (hu : ContDiff ℝ 1 u) {C₁ T : ℝ}
    (hC₁ : 0 ≤ C₁)
    (hest : ∀ ⦃ξ : ℝ × ℝ → V⦄, ContDiff ℝ 2 ξ → (∀ s t, ξ (s, t + 1) = ξ (s, t)) →
      ∀ ⦃a b : ℝ⦄, a ≤ b → (∀ s t, s ∉ Ioo a b → ξ (s, t) = 0) →
        ∫ z in Icc a b ×ˢ Icc (0 : ℝ) 1, (‖fderiv ℝ ξ z stdComplexLineReal‖ ^ 2 +
            ‖fderiv ℝ ξ z stdComplexLineImag‖ ^ 2 + ‖ξ z‖ ^ 2) ≤
          C₁ * ((∫ z in Icc a b ×ˢ Icc (0 : ℝ) 1, ‖ω.floerLinearization J Ks Kt u ξ z‖ ^ 2) +
            ∫ z in Icc (-T) T ×ˢ Icc (0 : ℝ) 1, ‖ξ z‖ ^ 2))
    {κ : ℝ → ℝ} (hκ : ContDiff ℝ 2 κ) (hκ' : ∀ s, |deriv κ s| ≤ (2 * (C₁ + 1))⁻¹)
    {η : ℝ × ℝ → V} (hη : ContDiff ℝ 2 η) (hper : ∀ s t, η (s, t + 1) = η (s, t)) {a b : ℝ}
    (hab : a ≤ b) (hη₀ : ∀ s t, s ∉ Ioo a b → η (s, t) = 0) :
    ∫ z in Icc a b ×ˢ Icc (0 : ℝ) 1, Real.exp (2 * κ z.1) *
        (‖fderiv ℝ η z stdComplexLineReal‖ ^ 2 + ‖fderiv ℝ η z stdComplexLineImag‖ ^ 2 +
          ‖η z‖ ^ 2) ≤
      8 * C₁ * ((∫ z in Icc a b ×ˢ Icc (0 : ℝ) 1,
          Real.exp (2 * κ z.1) * ‖ω.floerLinearization J Ks Kt u η z‖ ^ 2) +
        ∫ z in Icc (-T) T ×ˢ Icc (0 : ℝ) 1, Real.exp (2 * κ z.1) * ‖η z‖ ^ 2) := by
  have hε₂ : (2 * (C₁ + 1))⁻¹ ≤ 1 / 2 := by
    rw [inv_le_comm₀ (by positivity) (by norm_num)]
    linarith
  have hI {f : ℝ × ℝ → ℝ} (hf : Continuous f) :
      IntegrableOn f (Icc a b ×ˢ Icc (0 : ℝ) 1) :=
    hf.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  have hξ : ContDiff ℝ 2 fun w : ℝ × ℝ ↦ Real.exp (κ w.1) • η w :=
    ((Real.contDiff_exp.comp hκ).comp contDiff_fst).smul hη
  have : Continuous fun z : ℝ × ℝ ↦ Real.exp (2 * κ z.1) := by
    have := hκ.continuous
    fun_prop
  have hηc := hη.continuous
  have hdη := hη.continuous_fderiv two_ne_zero
  have := hξ.continuous
  have hdξ := hξ.continuous_fderiv two_ne_zero
  have : 0 ≤ ∫ z in Icc a b ×ˢ Icc (0 : ℝ) 1,
      Real.exp (2 * κ z.1) * ‖ω.floerLinearization J Ks Kt u η z‖ ^ 2 :=
    setIntegral_nonneg (measurableSet_Icc.prod measurableSet_Icc) fun _ _ ↦ by positivity
  have hY : 0 ≤ ∫ z in Icc (-T) T ×ˢ Icc (0 : ℝ) 1, Real.exp (2 * κ z.1) * ‖η z‖ ^ 2 :=
    setIntegral_nonneg (measurableSet_Icc.prod measurableSet_Icc) fun _ _ ↦ by positivity
  have hW := setIntegral_sobolev_exp_smul_le ω hJ hKs hKt hu hC₁ hest hκ hκ' hη hper hab hη₀
  -- `e^{2κ}` times the energy density of `η` is at most twice that of `ξ = e^{κ} η`.
  calc _ ≤ ∫ z in Icc a b ×ˢ Icc (0 : ℝ) 1,
        2 * (‖fderiv ℝ (fun w ↦ Real.exp (κ w.1) • η w) z stdComplexLineReal‖ ^ 2 +
          ‖fderiv ℝ (fun w ↦ Real.exp (κ w.1) • η w) z stdComplexLineImag‖ ^ 2 +
            ‖Real.exp (κ z.1) • η z‖ ^ 2) :=
        setIntegral_mono_on (hI (by fun_prop)) (hI (by fun_prop))
          (measurableSet_Icc.prod measurableSet_Icc) fun z _ ↦
            exp_mul_sobolev_le (hκ.differentiable two_ne_zero z.1).hasDerivAt
              (hη.differentiable two_ne_zero z) ((hκ' z.1).trans hε₂)
    _ ≤ _ := by
        rw [integral_const_mul]
        nlinarith [mul_nonneg hC₁ hY]

/-- **The weighted semi-Fredholm estimate along a Floer trajectory.** Let `H` be a jointly `C²`
Hamiltonian whose suspended vector field is globally Lipschitz, and let `J_t(y)` be a `C¹` family
of almost complex structures. Let `u : ℝ × ℝ → V` be a `C¹` map along which `J_t` is
`ω`-compatible, whose loops converge uniformly to orbits `xm` at `-∞` and `xp` at `+∞` starting at
nondegenerate fixed points of the time-one map, with `J_t` compatible along them, while its slice
defect `∂t u - X_{H_t}(u)` tends uniformly to zero at both ends, as for a Floer trajectory from
`xm` to `xp`. Then there are `ε > 0`, `C ≥ 0` and `T` such that for every `C²` weight `κ(s)` with
`|κ'| ≤ ε`, every `C²` map `η` of period one in `t` that vanishes for `s ∉ (a, b)` satisfies

`∫ e^{2κ} (‖∂s η‖² + ‖∂t η‖² + ‖η‖²) ≤ C (∫ e^{2κ} ‖D_u η‖² + ∫_{[-T, T] × [0, 1]} e^{2κ} ‖η‖²)`

over `[a, b] × [0, 1]`, for the linearized Floer operator `D_u` of the datum `K = H_t dt`. -/
theorem exists_pos_forall_setIntegral_exp_mul_le_mul_setIntegral_floerLinearization_add
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
    (huxm : TendstoUniformlyOn (fun s t ↦ u (s, t)) xm Filter.atBot (Icc 0 1))
    (huxp : TendstoUniformlyOn (fun s t ↦ u (s, t)) xp Filter.atTop (Icc 0 1))
    (hδm : TendstoUniformlyOn
      (fun s t ↦ sliceDefect (fun t ↦ ω.hamiltonianVectorField (H t)) u (s, t)) 0 Filter.atBot
        (Icc 0 1))
    (hδp : TendstoUniformlyOn
      (fun s t ↦ sliceDefect (fun t ↦ ω.hamiltonianVectorField (H t)) u (s, t)) 0 Filter.atTop
        (Icc 0 1)) :
    ∃ ε > 0, ∃ C, 0 ≤ C ∧ ∃ T, ∀ ⦃κ : ℝ → ℝ⦄, ContDiff ℝ 2 κ → (∀ s, |deriv κ s| ≤ ε) →
      ∀ ⦃η : ℝ × ℝ → V⦄, ContDiff ℝ 2 η → (∀ s t, η (s, t + 1) = η (s, t)) →
      ∀ ⦃a b : ℝ⦄, a ≤ b → (∀ s t, s ∉ Ioo a b → η (s, t) = 0) →
        ∫ z in Icc a b ×ˢ Icc (0 : ℝ) 1, Real.exp (2 * κ z.1) *
            (‖fderiv ℝ η z stdComplexLineReal‖ ^ 2 + ‖fderiv ℝ η z stdComplexLineImag‖ ^ 2 +
              ‖η z‖ ^ 2) ≤
          C * ((∫ z in Icc a b ×ˢ Icc (0 : ℝ) 1, Real.exp (2 * κ z.1) * ‖ω.floerLinearization
            (fun w y ↦ (J w.2 y).toLinearMap.toContinuousLinearMap) (fun _ _ ↦ 0)
            (fun w ↦ H w.2) u η z‖ ^ 2) +
            ∫ z in Icc (-T) T ×ˢ Icc (0 : ℝ) 1, Real.exp (2 * κ z.1) * ‖η z‖ ^ 2) := by
  obtain ⟨C₁, hC₁, T, hest⟩ :=
    ω.exists_forall_setIntegral_le_mul_setIntegral_floerLinearization_add hX hH hxm hndm hxp hndp
      hJ hJxm hJxp hu hJu huxm huxp hδm hδp
  exact ⟨(2 * (C₁ + 1))⁻¹, by positivity, 8 * C₁, by positivity, T,
    fun κ hκ hκ' η hη hper a b hab hη₀ ↦
      ω.setIntegral_exp_mul_le_mul_setIntegral_floerLinearization_add
        (J := fun w y ↦ (J w.2 y).toLinearMap.toContinuousLinearMap) (Ks := fun _ _ ↦ 0)
        (Kt := fun w ↦ H w.2)
        (fun _ ↦ (hJ.comp (contDiff_fst.snd.prodMk contDiff_snd)).contDiffAt)
        (fun _ ↦ contDiffAt_const)
        (fun _ ↦ (hH.comp (contDiff_fst.snd.prodMk contDiff_snd)).contDiffAt) hu hC₁ hest hκ hκ'
        hη hper hab hη₀⟩

/-- **The weighted semi-Fredholm estimate along a Floer trajectory.** Let `H` be a jointly `C²`
Hamiltonian, `J_t(y)` a `C¹` family of almost complex structures and `u : ℝ × ℝ → V` a `C¹` map
along which `J_t` is `ω`-compatible, whose loops converge uniformly to continuous loops `xm` at
`-∞` and `xp` at `+∞`, with `J_t` compatible along them, while its slice defect
`∂t u - X_{H_t}(u)` tends uniformly to zero at both ends, as for a Floer trajectory from `xm` to
`xp`. Let `c : ℝ → ℝ` be continuous, equal to `δm` for `s ≤ -R` and to `δp` for `s ≥ R`, where the
end weights are such that `S±_t - δ± J_t(x±(t))` have nondegenerate return maps, for
`S±_t = dX_{H_t}(x±(t))`; when `H`, `J` and `x±` are one-periodic in `t`, this says that `δ±` is
not an eigenvalue of the asymptotic operator at `x±`. Then
there are `C ≥ 0` and `T` such that every `C²` map `ξ` of period one in `t` that vanishes for
`s ∉ (a, b)` satisfies

`∫ (‖∂s ξ‖² + ‖∂t ξ‖² + ‖ξ‖²) ≤ C (∫ ‖D_u ξ - c(s) ξ‖² + ∫_{[-T, T] × [0, 1]} ‖ξ‖²)`

over `[a, b] × [0, 1]`, for the linearized Floer operator `D_u` of the datum `K = H_t dt`. For
`c = κ'` the operator `D_u - κ'` is `D_u` conjugated by the weight `e^{κ(s)}`
(`floerLinearization_exp_neg_smul`), so this is the semi-Fredholm estimate of `D_u` between the
Sobolev spaces with weight `e^{κ(s)}`, whose slopes at the ends are `δ±`. -/
theorem exists_forall_setIntegral_le_mul_setIntegral_floerLinearization_sub_smul_add
    (ω : SymplecticForm V) {H : ℝ → V → ℝ} (hH : ContDiff ℝ 2 (Function.uncurry H))
    {xm xp : ℝ → V} (hxm : Continuous xm) (hxp : Continuous xp)
    {J : ℝ → V → AlmostComplexStructure V}
    (hJ : ContDiff ℝ 1 fun p : ℝ × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap)
    (hJxm : ∀ t, ω.Compatible (J t (xm t))) (hJxp : ∀ t, ω.Compatible (J t (xp t)))
    {u : ℝ × ℝ → V} (hu : ContDiff ℝ 1 u) (hJu : ∀ z, ω.Compatible (J z.2 (u z)))
    (huxm : TendstoUniformlyOn (fun s t ↦ u (s, t)) xm Filter.atBot (Icc 0 1))
    (huxp : TendstoUniformlyOn (fun s t ↦ u (s, t)) xp Filter.atTop (Icc 0 1))
    (hδm : TendstoUniformlyOn
      (fun s t ↦ sliceDefect (fun t ↦ ω.hamiltonianVectorField (H t)) u (s, t)) 0 Filter.atBot
        (Icc 0 1))
    (hδp : TendstoUniformlyOn
      (fun s t ↦ sliceDefect (fun t ↦ ω.hamiltonianVectorField (H t)) u (s, t)) 0 Filter.atTop
        (Icc 0 1))
    {c : ℝ → ℝ} (hc : Continuous c) {R δm δp : ℝ} (hcm : ∀ s ≤ -R, c s = δm)
    (hcp : ∀ s, R ≤ s → c s = δp)
    (hdetm : LinearMap.det ((1 - dysonSeriesLeft (fun t ↦
      fderiv ℝ (ω.hamiltonianVectorField (H t)) (xm t) -
        δm • (J t (xm t)).toLinearMap.toContinuousLinearMap) 1 : V →L[ℝ] V) : V →ₗ[ℝ] V) ≠ 0)
    (hdetp : LinearMap.det ((1 - dysonSeriesLeft (fun t ↦
      fderiv ℝ (ω.hamiltonianVectorField (H t)) (xp t) -
        δp • (J t (xp t)).toLinearMap.toContinuousLinearMap) 1 : V →L[ℝ] V) : V →ₗ[ℝ] V) ≠ 0) :
    ∃ C, 0 ≤ C ∧ ∃ T, ∀ ⦃ξ : ℝ × ℝ → V⦄, ContDiff ℝ 2 ξ → (∀ s t, ξ (s, t + 1) = ξ (s, t)) →
      ∀ ⦃a b : ℝ⦄, a ≤ b → (∀ s t, s ∉ Ioo a b → ξ (s, t) = 0) →
        ∫ z in Icc a b ×ˢ Icc (0 : ℝ) 1, (‖fderiv ℝ ξ z stdComplexLineReal‖ ^ 2 +
            ‖fderiv ℝ ξ z stdComplexLineImag‖ ^ 2 + ‖ξ z‖ ^ 2) ≤
          C * ((∫ z in Icc a b ×ˢ Icc (0 : ℝ) 1, ‖ω.floerLinearization
            (fun w y ↦ (J w.2 y).toLinearMap.toContinuousLinearMap) (fun _ _ ↦ 0)
            (fun w ↦ H w.2) u ξ z - c z.1 • ξ z‖ ^ 2) +
            ∫ z in Icc (-T) T ×ˢ Icc (0 : ℝ) 1, ‖ξ z‖ ^ 2) :=
  ω.exists_forall_setIntegral_le_mul_setIntegral_floerLinearization_sub_smul_add_of_cylindrical
    (Floer.isCylindricalNearEnds_comp_snd hJ hH (R := R) u) hu hJu hc hcm hcp hH hxm hJ hJxm hdetm
    huxm hδm hH hxp hJ hJxp hdetp huxp hδp

end TauCeti.SymplecticForm
