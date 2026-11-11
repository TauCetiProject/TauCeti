/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import TauCeti.Analysis.Calculus.WittenLaplacian.Quadratic
import TauCeti.Analysis.Calculus.LineDeriv.IntegrationByParts

/-!
# Lower bounds for the quadratic form of the Euclidean Witten Laplacian

Witten's analytic proof of the Morse inequalities rests on two lower bounds for the quadratic form
`⟨Δ_t φ, φ⟩ = ∫ ∑ s, Δ_t φ x s * φ x s` of the Witten Laplacian `Δ_t` of a function `f`
(`TauCeti.euclideanWittenLaplacian`), evaluated on compactly supported forms `φ` on `ℝ^ι`. Away
from the critical points of `f` the form is large, of order `t²`; near a nondegenerate critical
point it is modelled by a sum of harmonic oscillators, which is bounded below by a positive multiple
of `t` in every degree other than the Morse index. This file proves both bounds.

**The energy identity.** Integrating Witten's frame formula
`TauCeti.euclideanWittenLaplacian_apply` by parts, the quadratic form of a compactly supported `C²`
form `φ` is

`⟨Δ_t φ, φ⟩ = ∫ ∑ᵢ |∂ᵢ φ|² + t² ∫ |df|² |φ|² + t ∫ ⟨∑ᵢⱼ Hess f(∂ᵢ, ∂ⱼ) ⁅εᵢ, ιⱼ⁆ φ, φ⟩`

(`TauCeti.integral_sum_euclideanWittenLaplacian_mul`), where `|φ|² = ∑ s, φ x s ^ 2` and `εᵢ`, `ιⱼ`
are exterior multiplication by `dx^i` and contraction with `∂ⱼ`. The first term is nonnegative, and
each commutator satisfies `|⟨⁅εᵢ, ιⱼ⁆ v, v⟩| ≤ |v|²` on the fibre
(`Module.Basis.abs_sum_lie_exteriorCreation_exteriorContraction_apply_mul_le`).

**Localization away from the critical points.** If `|df|² ≥ c` and `∑ᵢⱼ |Hess f(∂ᵢ, ∂ⱼ)| ≤ C` on the
support of `φ`, then `⟨Δ_t φ, φ⟩ ≥ (t² c - |t| C) ‖φ‖²`
(`TauCeti.mul_integral_le_integral_sum_euclideanWittenLaplacian_mul`). For `c > 0` this grows like
`t²`, so forms supported away from the critical points carry no low-lying energy as `t → ∞`.

**The harmonic-oscillator model.** For the diagonal quadratic function `f = ∑ᵢ aᵢ xᵢ² / 2`
(`TauCeti.diagonalQuadratic`) the coefficient of `dx^s` is acted on by `∑ᵢ (-∂ᵢ² + t² aᵢ² xᵢ²)`
shifted by `t ∑ᵢ ±aᵢ` (`TauCeti.euclideanWittenLaplacian_diagonalQuadratic_apply`). The
uncertainty inequality `∫ (∂ᵢ g)² + ω² xᵢ² g² ≥ |ω| ∫ g²`
(`TauCeti.abs_mul_integral_bilinear_le_integral_bilinear_fderiv_apply_add`) bounds each
oscillator below by its ground state energy, so for `t ≥ 0`

`⟨Δ_t φ, φ⟩ ≥ ∑ s, μ(0, s) ∫ φ_s²`

(`TauCeti.sum_mul_integral_le_integral_sum_euclideanWittenLaplacian_diagonalQuadratic_mul`), where
`μ(0, s) = t ∑ᵢ (|aᵢ| ± aᵢ)` is the eigenvalue of the Gaussian ground state in degree `s`
(`TauCeti.diagonalQuadraticWittenEigenvalue`). It vanishes in the degree `s₀ = {i | aᵢ < 0}` of
the Morse index and is at least `2 t c` in every other degree when `c ≤ |aᵢ|` for all `i`, so the
part of `φ` outside degree `s₀` costs energy at least `2 t c` times its squared norm
(`TauCeti.two_mul_mul_integral_le_integral_sum_euclideanWittenLaplacian_diagonalQuadratic_mul`):
the linear-in-`t` gap of the model. These are statements about the quadratic form on compactly
supported smooth forms, not about the spectrum of a self-adjoint realization of `Δ_t`, and the
gap above the ground state within degree `s₀` is not treated here.

The integrals are against an arbitrary additive Haar measure `μ` on `ℝ^ι`; all of them are finite,
since the integrands are continuous with compact support.

## Main results

* `TauCeti.integral_sum_euclideanWittenLaplacian_mul`: the energy identity.
* `TauCeti.mul_integral_le_integral_sum_euclideanWittenLaplacian_mul`: the localization estimate
  away from the critical points.
* `TauCeti.sum_mul_integral_le_integral_sum_euclideanWittenLaplacian_diagonalQuadratic_mul`: the
  harmonic-oscillator lower bound for the quadratic model.
* `TauCeti.integral_sum_euclideanWittenLaplacian_diagonalQuadratic_mul_nonneg`,
  `TauCeti.two_mul_mul_integral_le_integral_sum_euclideanWittenLaplacian_diagonalQuadratic_mul`:
  the model quadratic form is nonnegative, with a gap `2 t c` outside the degree of the Morse
  index.

## References

* E. Witten, *Supersymmetry and Morse theory*, J. Differential Geom. **17** (1982), 661–692, §2.
* B. Helffer and J. Sjöstrand, *Puits multiples en mécanique semi-classique IV: étude du
  complexe de Witten*, Comm. Partial Differential Equations **10** (1985), 245–340, §2.
* H. L. Cycon, R. G. Froese, W. Kirsch and B. Simon, *Schrödinger Operators*, Springer (1987),
  Chapter 11 (Witten's proof of the Morse inequalities).
-/

public section

noncomputable section

namespace TauCeti

open MeasureTheory

variable {ι : Type*} [Fintype ι] {μ : Measure (ι → ℝ)} [μ.IsAddHaarMeasure]
  {f : (ι → ℝ) → ℝ} {φ : (ι → ℝ) → Finset ι → ℝ}

section Integrability

/-- The bilinear form `(y, z) ↦ y s * z s` on coordinate vectors, which pairs the coefficients of
`dx^s`. -/
private def coeffPairing (s : Finset ι) : (Finset ι → ℝ) →L[ℝ] (Finset ι → ℝ) →L[ℝ] ℝ :=
  (ContinuousLinearMap.mul ℝ ℝ).bilinearComp (ContinuousLinearMap.proj s)
    (ContinuousLinearMap.proj s)

private theorem coeffPairing_apply (s : Finset ι) (y z : Finset ι → ℝ) :
    coeffPairing s y z = y s * z s :=
  (rfl)

omit [Fintype ι] in
/-- A continuous function vanishing off the support of a compactly supported form is integrable. -/
private theorem integrable_of_eq_zero_of_notMem_tsupport [Finite ι] (hφc : HasCompactSupport φ)
    {F : (ι → ℝ) → ℝ} (hF : Continuous F) (hF0 : ∀ x ∉ tsupport φ, F x = 0) :
    Integrable F μ :=
  hF.integrable_of_hasCompactSupport (HasCompactSupport.intro hφc hF0)

private theorem continuous_fderiv_apply_apply (hφ : ContDiff ℝ 2 φ) (v : ι → ℝ) (s : Finset ι) :
    Continuous fun x ↦ fderiv ℝ φ x v s :=
  (continuous_apply s).comp ((hφ.continuous_fderiv (by norm_num)).clm_apply continuous_const)

private theorem continuous_fderiv_fderiv_apply_apply (hφ : ContDiff ℝ 2 φ) (v w : ι → ℝ)
    (s : Finset ι) : Continuous fun x ↦ fderiv ℝ (fderiv ℝ φ) x v w s :=
  (continuous_apply s).comp ((((hφ.fderiv_right (m := 1) (by norm_num)).continuous_fderiv
    one_ne_zero).clm_apply continuous_const).clm_apply continuous_const)

private theorem integrable_sum_sq (hφ : ContDiff ℝ 2 φ) (hφc : HasCompactSupport φ) :
    Integrable (fun x ↦ ∑ s, φ x s ^ 2) μ :=
  integrable_of_eq_zero_of_notMem_tsupport hφc
    (continuous_finsetSum _ fun s _ ↦ ((continuous_apply s).comp hφ.continuous).pow 2)
    fun x hx ↦ by simp [image_eq_zero_of_notMem_tsupport hx]

private theorem integrable_neg_fderiv_fderiv_apply_apply_mul (hφ : ContDiff ℝ 2 φ)
    (hφc : HasCompactSupport φ) (v : ι → ℝ) (s : Finset ι) :
    Integrable (fun x ↦ -fderiv ℝ (fderiv ℝ φ) x v v s * φ x s) μ :=
  integrable_of_eq_zero_of_notMem_tsupport hφc
    ((continuous_fderiv_fderiv_apply_apply hφ _ _ s).neg.mul
      ((continuous_apply s).comp hφ.continuous))
    fun x hx ↦ by simp [image_eq_zero_of_notMem_tsupport hx]

private theorem integrable_fderiv_apply_apply_sq (hφ : ContDiff ℝ 2 φ) (hφc : HasCompactSupport φ)
    (v : ι → ℝ) (s : Finset ι) : Integrable (fun x ↦ fderiv ℝ φ x v s ^ 2) μ :=
  integrable_of_eq_zero_of_notMem_tsupport hφc ((continuous_fderiv_apply_apply hφ _ s).pow 2)
    fun x hx ↦ by simp [fderiv_of_notMem_tsupport ℝ hx]

private theorem integrable_mul_apply_sq (hφ : ContDiff ℝ 2 φ) (hφc : HasCompactSupport φ)
    {g : (ι → ℝ) → ℝ} (hg : Continuous g) (s : Finset ι) :
    Integrable (fun x ↦ g x * φ x s ^ 2) μ :=
  integrable_of_eq_zero_of_notMem_tsupport hφc
    (hg.mul (((continuous_apply s).comp hφ.continuous).pow 2))
    fun x hx ↦ by simp [image_eq_zero_of_notMem_tsupport hx]

private theorem integrable_apply_sq (hφ : ContDiff ℝ 2 φ) (hφc : HasCompactSupport φ)
    (s : Finset ι) : Integrable (fun x ↦ φ x s ^ 2) μ := by
  simpa using integrable_mul_apply_sq (μ := μ) hφ hφc continuous_const (g := fun _ ↦ (1 : ℝ)) s

end Integrability

/-- Integration by parts in the direction `v`: the pairing of the coefficient of `-∂ᵥ² φ` with that
of `φ` integrates to the integral of the square of the coefficient of `∂ᵥ φ`. -/
private theorem integral_neg_fderiv_fderiv_apply_apply_mul (hφ : ContDiff ℝ 2 φ)
    (hφc : HasCompactSupport φ) (v : ι → ℝ) (s : Finset ι) :
    ∫ x, -fderiv ℝ (fderiv ℝ φ) x v v s * φ x s ∂μ = ∫ x, fderiv ℝ φ x v s ^ 2 ∂μ := by
  have h := integral_bilinear_fderiv_apply_eq_neg_integral_fderiv_fderiv_apply (μ := μ)
    (coeffPairing s) hφ hφc v v
  simp only [coeffPairing_apply] at h
  simp only [sq, h, neg_mul, integral_neg]

variable [LinearOrder ι]

section General

private theorem integrable_sum_fderiv_sq_mul_sum_sq (hf : ContDiff ℝ 2 f) (hφ : ContDiff ℝ 2 φ)
    (hφc : HasCompactSupport φ) :
    Integrable (fun x ↦ (∑ i, fderiv ℝ f x (Pi.single i 1) ^ 2) * ∑ s, φ x s ^ 2) μ :=
  integrable_of_eq_zero_of_notMem_tsupport hφc
    ((continuous_finsetSum _ fun i _ ↦
      ((hf.continuous_fderiv (by norm_num)).clm_apply continuous_const).pow 2).mul
      (continuous_finsetSum _ fun s _ ↦ ((continuous_apply s).comp hφ.continuous).pow 2))
    fun x hx ↦ by simp [image_eq_zero_of_notMem_tsupport hx]

private theorem integrable_sum_hessian_lie_apply_mul (hf : ContDiff ℝ 2 f)
    (hφ : ContDiff ℝ 2 φ) (hφc : HasCompactSupport φ) :
    Integrable (fun x ↦ ∑ s, (∑ i, ∑ j,
      fderiv ℝ (fderiv ℝ f) x (Pi.single i 1) (Pi.single j 1) •
        ⁅(Pi.basisFun ℝ ι).exteriorCreation i, (Pi.basisFun ℝ ι).exteriorContraction j⁆
          (φ x)) s * φ x s) μ :=
  integrable_of_eq_zero_of_notMem_tsupport hφc
    (continuous_finsetSum _ fun s _ ↦ ((continuous_apply s).comp
      (continuous_finsetSum _ fun i _ ↦ continuous_finsetSum _ fun j _ ↦
        ((((hf.fderiv_right (m := 1) (by norm_num)).continuous_fderiv one_ne_zero).clm_apply
          continuous_const).clm_apply continuous_const).smul
          (LinearMap.continuous_of_finiteDimensional _ |>.comp hφ.continuous))).mul
      ((continuous_apply s).comp hφ.continuous))
    fun x hx ↦ by simp [image_eq_zero_of_notMem_tsupport hx]

/-- Witten's frame formula, paired pointwise with the form itself. -/
private theorem sum_euclideanWittenLaplacian_apply_mul (hf : ContDiff ℝ 2 f)
    (hφ : ContDiff ℝ 2 φ) (t : ℝ) (x : ι → ℝ) :
    ∑ s, euclideanWittenLaplacian f t φ x s * φ x s =
      ∑ i, ∑ s, -fderiv ℝ (fderiv ℝ φ) x (Pi.single i 1) (Pi.single i 1) s * φ x s +
        t ^ 2 * ((∑ i, fderiv ℝ f x (Pi.single i 1) ^ 2) * ∑ s, φ x s ^ 2) +
        t * ∑ s, (∑ i, ∑ j, fderiv ℝ (fderiv ℝ f) x (Pi.single i 1) (Pi.single j 1) •
          ⁅(Pi.basisFun ℝ ι).exteriorCreation i, (Pi.basisFun ℝ ι).exteriorContraction j⁆
            (φ x)) s * φ x s := by
  rw [euclideanWittenLaplacian_apply hf.contDiffAt hφ.contDiffAt]
  simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.neg_apply, add_mul,
    Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum]
  congr 1
  · congr 1
    · exact Finset.sum_comm
    · refine Finset.sum_congr rfl fun s _ ↦ Finset.sum_congr rfl fun i _ ↦ ?_
      ring
  · refine Finset.sum_congr rfl fun s _ ↦ Finset.sum_congr rfl fun i _ ↦
      Finset.sum_congr rfl fun j _ ↦ ?_
    ring

/-- **The energy identity for the Witten Laplacian.** For a `C²` function `f` and a compactly
supported `C²` form `φ` on `ℝ^ι`, integration by parts in Witten's frame formula gives

`⟨Δ_t φ, φ⟩ = ∫ ∑ᵢ |∂ᵢ φ|² + t² ∫ |df|² |φ|² + t ∫ ⟨∑ᵢⱼ Hess f(∂ᵢ, ∂ⱼ) ⁅εᵢ, ιⱼ⁆ φ, φ⟩`,

where `⟨ψ, φ⟩ = ∑ s, ψ s * φ s` is the standard pairing of the coefficients. -/
theorem integral_sum_euclideanWittenLaplacian_mul (hf : ContDiff ℝ 2 f) (hφ : ContDiff ℝ 2 φ)
    (hφc : HasCompactSupport φ) (t : ℝ) :
    ∫ x, ∑ s, euclideanWittenLaplacian f t φ x s * φ x s ∂μ =
      ∫ x, ∑ i, ∑ s, fderiv ℝ φ x (Pi.single i 1) s ^ 2 ∂μ +
        t ^ 2 * ∫ x, (∑ i, fderiv ℝ f x (Pi.single i 1) ^ 2) * ∑ s, φ x s ^ 2 ∂μ +
        t * ∫ x, ∑ s, (∑ i, ∑ j, fderiv ℝ (fderiv ℝ f) x (Pi.single i 1) (Pi.single j 1) •
          ⁅(Pi.basisFun ℝ ι).exteriorCreation i, (Pi.basisFun ℝ ι).exteriorContraction j⁆
            (φ x)) s * φ x s ∂μ := by
  have hA := fun i s ↦ integrable_neg_fderiv_fderiv_apply_apply_mul (μ := μ) hφ hφc
    (Pi.single i 1) s
  have hA' := fun i s ↦ integrable_fderiv_apply_apply_sq (μ := μ) hφ hφc (Pi.single i 1) s
  have hG := integrable_sum_fderiv_sq_mul_sum_sq (μ := μ) hf hφ hφc
  have hK := integrable_sum_hessian_lie_apply_mul (μ := μ) hf hφ hφc
  simp only [sum_euclideanWittenLaplacian_apply_mul hf hφ]
  have hAsum : Integrable (fun x ↦ ∑ i, ∑ s,
      -fderiv ℝ (fderiv ℝ φ) x (Pi.single i 1) (Pi.single i 1) s * φ x s) μ :=
    integrable_finsetSum _ fun i _ ↦ integrable_finsetSum _ fun s _ ↦ hA i s
  have hAG : Integrable (fun x ↦ (∑ i, ∑ s,
      -fderiv ℝ (fderiv ℝ φ) x (Pi.single i 1) (Pi.single i 1) s * φ x s) +
        t ^ 2 * ((∑ i, fderiv ℝ f x (Pi.single i 1) ^ 2) * ∑ s, φ x s ^ 2)) μ :=
    hAsum.add (hG.const_mul _)
  rw [integral_add hAG (hK.const_mul _), integral_add hAsum (hG.const_mul _), integral_const_mul,
    integral_const_mul,
    integral_finsetSum _ fun i _ ↦ integrable_finsetSum _ fun s _ ↦ hA i s,
    integral_finsetSum _ fun i _ ↦ integrable_finsetSum _ fun s _ ↦ hA' i s]
  congr 2
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [integral_finsetSum _ fun s _ ↦ hA i s, integral_finsetSum _ fun s _ ↦ hA' i s]
  exact Finset.sum_congr rfl fun s _ ↦ integral_neg_fderiv_fderiv_apply_apply_mul hφ hφc _ s

/-- **Localization away from the critical points.** If, on the support of a compactly supported
`C²` form `φ`, the gradient of a `C²` function `f` satisfies `c ≤ |df|²` and its Hessian satisfies
`∑ᵢⱼ |Hess f(∂ᵢ, ∂ⱼ)| ≤ C`, then the quadratic form of the Witten Laplacian is bounded below by
`(t² c - |t| C) ‖φ‖²`. For `c > 0` the bound grows like `t²`. -/
theorem mul_integral_le_integral_sum_euclideanWittenLaplacian_mul (hf : ContDiff ℝ 2 f)
    (hφ : ContDiff ℝ 2 φ) (hφc : HasCompactSupport φ) (t : ℝ) {c C : ℝ}
    (hc : ∀ x ∈ tsupport φ, c ≤ ∑ i, fderiv ℝ f x (Pi.single i 1) ^ 2)
    (hC : ∀ x ∈ tsupport φ,
      ∑ i, ∑ j, |fderiv ℝ (fderiv ℝ f) x (Pi.single i 1) (Pi.single j 1)| ≤ C) :
    (t ^ 2 * c - |t| * C) * ∫ x, ∑ s, φ x s ^ 2 ∂μ ≤
      ∫ x, ∑ s, euclideanWittenLaplacian f t φ x s * φ x s ∂μ := by
  rw [integral_sum_euclideanWittenLaplacian_mul hf hφ hφc t]
  have hN := integrable_sum_sq (μ := μ) hφ hφc
  have hφ0 : ∀ x ∉ tsupport φ, φ x = 0 := fun x hx ↦ image_eq_zero_of_notMem_tsupport hx
  have h₁ : 0 ≤ ∫ x, ∑ i, ∑ s, fderiv ℝ φ x (Pi.single i 1) s ^ 2 ∂μ :=
    integral_nonneg fun x ↦ by positivity
  -- the potential `t² |df|²` is at least `t² c` on the support
  have h₂ : c * ∫ x, ∑ s, φ x s ^ 2 ∂μ ≤
      ∫ x, (∑ i, fderiv ℝ f x (Pi.single i 1) ^ 2) * ∑ s, φ x s ^ 2 ∂μ := by
    rw [← integral_const_mul]
    refine integral_mono (hN.const_mul c) (integrable_sum_fderiv_sq_mul_sum_sq hf hφ hφc)
      fun x ↦ ?_
    by_cases hx : x ∈ tsupport φ
    · exact mul_le_mul_of_nonneg_right (hc x hx) (by positivity)
    · simp [hφ0 x hx]
  -- the Hessian term is at least `-|t| C` on the support
  have h₃ : -(|t| * C) * ∫ x, ∑ s, φ x s ^ 2 ∂μ ≤
      t * ∫ x, ∑ s, (∑ i, ∑ j, fderiv ℝ (fderiv ℝ f) x (Pi.single i 1) (Pi.single j 1) •
        ⁅(Pi.basisFun ℝ ι).exteriorCreation i, (Pi.basisFun ℝ ι).exteriorContraction j⁆
          (φ x)) s * φ x s ∂μ := by
    rw [← integral_const_mul, ← integral_const_mul]
    refine integral_mono (hN.const_mul _)
      ((integrable_sum_hessian_lie_apply_mul hf hφ hφc).const_mul t) fun x ↦ ?_
    by_cases hx : x ∈ tsupport φ
    · have hK :=
        (Module.Basis.abs_sum_sum_sum_smul_lie_exteriorCreation_exteriorContraction_apply_mul_le
          (Pi.basisFun ℝ ι) (fun i j ↦ fderiv ℝ (fderiv ℝ f) x (Pi.single i 1) (Pi.single j 1))
          (φ x)).trans
          (mul_le_mul_of_nonneg_right (hC x hx) (by positivity : (0 : ℝ) ≤ ∑ s, φ x s ^ 2))
      have := mul_le_mul_of_nonneg_left hK (abs_nonneg t)
      rw [← abs_mul] at this
      linarith [neg_abs_le (t * ∑ s, (∑ i, ∑ j,
        fderiv ℝ (fderiv ℝ f) x (Pi.single i 1) (Pi.single j 1) •
          ⁅(Pi.basisFun ℝ ι).exteriorCreation i, (Pi.basisFun ℝ ι).exteriorContraction j⁆
            (φ x)) s * φ x s)]
    · simp [hφ0 x hx]
  nlinarith [mul_le_mul_of_nonneg_left h₂ (sq_nonneg t)]

end General

section Model

variable {a : ι → ℝ}

/-- The Witten Laplacian of the quadratic model, paired pointwise with the form itself. -/
private theorem sum_euclideanWittenLaplacian_diagonalQuadratic_apply_mul (hφ : ContDiff ℝ 2 φ)
    (t : ℝ) (x : ι → ℝ) :
    ∑ s, euclideanWittenLaplacian (diagonalQuadratic a) t φ x s * φ x s =
      ∑ s, (∑ i, (-fderiv ℝ (fderiv ℝ φ) x (Pi.single i 1) (Pi.single i 1) s * φ x s +
          t ^ 2 * a i ^ 2 * (x i ^ 2 * φ x s ^ 2)) +
        t * (∑ i, if i ∈ s then a i else -a i) * φ x s ^ 2) := by
  refine Finset.sum_congr rfl fun s _ ↦ ?_
  rw [euclideanWittenLaplacian_diagonalQuadratic_apply hφ.contDiffAt, add_mul, Finset.sum_mul]
  congr 1
  · refine Finset.sum_congr rfl fun i _ ↦ ?_
    ring
  · ring

/-- The oscillator `-∂ᵢ² + t² aᵢ² xᵢ²` on the coefficient of `dx^s` is bounded below by its ground
state energy `t |aᵢ|`. -/
private theorem mul_integral_le_integral_neg_fderiv_fderiv_add (hφ : ContDiff ℝ 2 φ)
    (hφc : HasCompactSupport φ) {t : ℝ} (ht : 0 ≤ t) (i : ι) (s : Finset ι) :
    t * |a i| * ∫ x, φ x s ^ 2 ∂μ ≤
      ∫ x, -fderiv ℝ (fderiv ℝ φ) x (Pi.single i 1) (Pi.single i 1) s * φ x s ∂μ +
        t ^ 2 * a i ^ 2 * ∫ x, x i ^ 2 * φ x s ^ 2 ∂μ := by
  have h := abs_mul_integral_bilinear_le_integral_bilinear_fderiv_apply_add (μ := μ)
    (B := coeffPairing s) (ℓ := ContinuousLinearMap.proj i) (v := Pi.single i 1)
    (fun y z ↦ by simp only [coeffPairing_apply, mul_comm])
    (fun y ↦ by simpa only [coeffPairing_apply] using mul_self_nonneg (y s)) (by simp)
    (hφ.of_le (by norm_num)) hφc (t * a i)
  simp only [coeffPairing_apply, ContinuousLinearMap.proj_apply, ← sq] at h
  rw [integral_neg_fderiv_fderiv_apply_apply_mul hφ hφc,
    show t * |a i| = |t * a i| by rw [abs_mul, abs_of_nonneg ht]]
  rw [mul_pow] at h
  linarith

/-- **The harmonic-oscillator lower bound.** For the diagonal quadratic function
`f = ∑ᵢ aᵢ xᵢ² / 2`, `t ≥ 0` and a compactly supported `C²` form `φ`, the quadratic form of the
Witten Laplacian is at least `∑ s, μ(0, s) ∫ φ_s²`, where `φ_s` is the coefficient of `dx^s` and
`μ(0, s) = t ∑ᵢ (|aᵢ| ± aᵢ)` is the eigenvalue of the Gaussian ground state in degree `s`. -/
theorem sum_mul_integral_le_integral_sum_euclideanWittenLaplacian_diagonalQuadratic_mul
    (a : ι → ℝ) {t : ℝ} (ht : 0 ≤ t) (hφ : ContDiff ℝ 2 φ) (hφc : HasCompactSupport φ) :
    ∑ s, diagonalQuadraticWittenEigenvalue a t 0 s * ∫ x, φ x s ^ 2 ∂μ ≤
      ∫ x, ∑ s, euclideanWittenLaplacian (diagonalQuadratic a) t φ x s * φ x s ∂μ := by
  have hA := fun i s ↦ integrable_neg_fderiv_fderiv_apply_apply_mul (μ := μ) hφ hφc
    (Pi.single i 1) s
  have hX := fun i s ↦ integrable_mul_apply_sq (μ := μ) hφ hφc (g := fun x ↦ x i ^ 2)
    ((continuous_apply i).pow 2) s
  have hN := fun s ↦ integrable_apply_sq (μ := μ) hφ hφc s
  have hAX : ∀ i s, Integrable (fun x ↦
      -fderiv ℝ (fderiv ℝ φ) x (Pi.single i 1) (Pi.single i 1) s * φ x s +
        t ^ 2 * a i ^ 2 * (x i ^ 2 * φ x s ^ 2)) μ :=
    fun i s ↦ (hA i s).add ((hX i s).const_mul _)
  have hS : ∀ s, Integrable (fun x ↦ ∑ i,
      (-fderiv ℝ (fderiv ℝ φ) x (Pi.single i 1) (Pi.single i 1) s * φ x s +
        t ^ 2 * a i ^ 2 * (x i ^ 2 * φ x s ^ 2))) μ :=
    fun s ↦ integrable_finsetSum _ fun i _ ↦ hAX i s
  have hT : ∀ s, Integrable (fun x ↦ (∑ i,
      (-fderiv ℝ (fderiv ℝ φ) x (Pi.single i 1) (Pi.single i 1) s * φ x s +
        t ^ 2 * a i ^ 2 * (x i ^ 2 * φ x s ^ 2))) +
      t * (∑ i, if i ∈ s then a i else -a i) * φ x s ^ 2) μ :=
    fun s ↦ (hS s).add ((hN s).const_mul _)
  simp only [sum_euclideanWittenLaplacian_diagonalQuadratic_apply_mul hφ t]
  rw [integral_finsetSum _ fun s _ ↦ hT s]
  refine Finset.sum_le_sum fun s _ ↦ ?_
  rw [integral_add (hS s) ((hN s).const_mul _), integral_finsetSum _ fun i _ ↦ hAX i s,
    integral_const_mul, diagonalQuadraticWittenEigenvalue_def]
  simp only [Pi.zero_apply, CharP.cast_eq_zero, mul_zero, zero_add, mul_one,
    Finset.sum_add_distrib, mul_add, add_mul, Finset.mul_sum, Finset.sum_mul]
  gcongr with i
  rw [integral_add (hA i s) ((hX i s).const_mul _), integral_const_mul]
  exact mul_integral_le_integral_neg_fderiv_fderiv_add hφ hφc ht i s

/-- The quadratic form of the Witten Laplacian of a diagonal quadratic function is nonnegative
on compactly supported `C²` forms, for `t ≥ 0`. -/
theorem integral_sum_euclideanWittenLaplacian_diagonalQuadratic_mul_nonneg (a : ι → ℝ) {t : ℝ}
    (ht : 0 ≤ t) (hφ : ContDiff ℝ 2 φ) (hφc : HasCompactSupport φ) :
    0 ≤ ∫ x, ∑ s, euclideanWittenLaplacian (diagonalQuadratic a) t φ x s * φ x s ∂μ :=
  (Finset.sum_nonneg fun s _ ↦ mul_nonneg (diagonalQuadraticWittenEigenvalue_nonneg a ht 0 s)
    (integral_nonneg fun _ ↦ sq_nonneg _)).trans
    (sum_mul_integral_le_integral_sum_euclideanWittenLaplacian_diagonalQuadratic_mul a ht hφ hφc)

/-- **The gap of the harmonic-oscillator model.** If `c ≤ |aᵢ|` for every `i` and `t ≥ 0`, the
part of a compactly supported `C²` form `φ` outside the degree `s₀ = {i | aᵢ < 0}` of the Morse
index contributes at least `2 t c` times its squared norm to the quadratic form of the Witten
Laplacian of `∑ᵢ aᵢ xᵢ² / 2`. -/
theorem two_mul_mul_integral_le_integral_sum_euclideanWittenLaplacian_diagonalQuadratic_mul
    {t : ℝ} (ht : 0 ≤ t) {c : ℝ} (hc : ∀ i, c ≤ |a i|) (hφ : ContDiff ℝ 2 φ)
    (hφc : HasCompactSupport φ) :
    2 * t * c *
        ∫ x, ∑ s ∈ Finset.univ.erase (Finset.univ.filter fun i ↦ a i < 0), φ x s ^ 2 ∂μ ≤
      ∫ x, ∑ s, euclideanWittenLaplacian (diagonalQuadratic a) t φ x s * φ x s ∂μ := by
  refine le_trans ?_
    (sum_mul_integral_le_integral_sum_euclideanWittenLaplacian_diagonalQuadratic_mul a ht hφ hφc)
  have hN := fun s ↦ integrable_apply_sq (μ := μ) hφ hφc s
  rw [integral_finsetSum _ fun s _ ↦ hN s, Finset.mul_sum,
    ← Finset.sum_erase_add _ _ (Finset.mem_univ (Finset.univ.filter fun i ↦ a i < 0)),
    diagonalQuadraticWittenEigenvalue_zero_filter_neg, zero_mul, add_zero]
  refine Finset.sum_le_sum fun s hs ↦ mul_le_mul_of_nonneg_right
    (two_mul_mul_le_diagonalQuadraticWittenEigenvalue ht hc fun h ↦ ?_)
    (integral_nonneg fun _ ↦ sq_nonneg _)
  exact (Finset.mem_erase.1 hs).1 h.2

end Model

end TauCeti
