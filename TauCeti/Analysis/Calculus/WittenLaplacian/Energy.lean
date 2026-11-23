/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import TauCeti.Analysis.Calculus.WittenLaplacian.Quadratic
import TauCeti.Analysis.Calculus.LineDeriv.IntegrationByParts
import TauCeti.Analysis.Calculus.SecondDerivative
import TauCeti.Analysis.SpecialFunctions.Hermite.Function.Pi.SpectralGap

/-!
# Lower bounds for the quadratic form of the Euclidean Witten Laplacian

Witten's analytic proof of the Morse inequalities rests on two lower bounds for the quadratic form
`⟨Δ_t φ, φ⟩ = ∫ ∑ s, Δ_t φ x s * φ x s` of the Witten Laplacian `Δ_t` of a function `f`
(`TauCeti.euclideanWittenLaplacian`), evaluated on compactly supported forms `φ` on `ℝ^ι`. Away
from the critical points of `f` the form is large, of order `t²`; near a nondegenerate critical
point it is modelled by a sum of harmonic oscillators, which is bounded below by a positive multiple
of `t` in every degree other than the Morse index. The first bound is
`TauCeti.mul_integral_sum_sq_le_integral_sum_euclideanWittenLaplacian_mul`, in
`TauCeti.Analysis.Calculus.WittenLaplacian.Localization`. This file proves the energy identity
and the second bound.

**The energy identity.** Integrating Witten's frame formula
`TauCeti.euclideanWittenLaplacian_apply` by parts, the quadratic form of a compactly supported `C²`
form `φ` is

`⟨Δ_t φ, φ⟩ = ∫ ∑ᵢ |∂ᵢ φ|² + t² ∫ |df|² |φ|² + t ∫ ⟨∑ᵢⱼ Hess f(∂ᵢ, ∂ⱼ) ⁅εᵢ, ιⱼ⁆ φ, φ⟩`

(`TauCeti.integral_sum_euclideanWittenLaplacian_mul`), where `|φ|² = ∑ s, φ x s ^ 2` and `εᵢ`, `ιⱼ`
are exterior multiplication by `dx^i` and contraction with `∂ⱼ`. The first term is nonnegative, and
each commutator satisfies `|⟨⁅εᵢ, ιⱼ⁆ v, v⟩| ≤ |v|²` on the fibre
(`Module.Basis.abs_sum_lie_exteriorCreation_exteriorContraction_apply_mul_le`).

**The harmonic-oscillator model.** For the diagonal quadratic function `f = ∑ᵢ aᵢ xᵢ² / 2`
(`TauCeti.diagonalQuadratic`) the coefficient of `dx^s` is acted on by `∑ᵢ (-∂ᵢ² + t² aᵢ² xᵢ²)`
shifted by `t ∑ᵢ ±aᵢ` (`TauCeti.euclideanWittenLaplacian_diagonalQuadratic_apply`). The
uncertainty inequality `∫ (∂ᵢ g)² + ω² xᵢ² g² ≥ |ω| ∫ g²`, in the form
`TauCeti.abs_mul_integral_sq_le_integral_neg_fderiv_fderiv_apply_mul_add`, bounds each
oscillator below by its ground state energy `|t aᵢ| ≥ t |aᵢ|`, so for every real `t`

`⟨Δ_t φ, φ⟩ ≥ ∑ s, μ(0, s) ∫ φ_s²`

(`TauCeti.sum_mul_integral_le_integral_sum_euclideanWittenLaplacian_diagonalQuadratic_mul`), where
`μ(0, s) = t ∑ᵢ (|aᵢ| ± aᵢ)` (`TauCeti.diagonalQuadraticWittenEigenvalue`). For `t > 0` and every
`aᵢ ≠ 0` it is the eigenvalue of the Gaussian ground state in degree `s`; otherwise it is only the
coefficient of the bound, which can be negative for `t < 0`. It vanishes in the degree
`s₀ = {i | aᵢ < 0}` of the Morse index and, for `t ≥ 0`, is at least `2 t c` in every other degree
when `c ≤ |aᵢ|` for all `i`, so the part of `φ` outside degree `s₀` costs energy at least `2 t c`
times its squared norm
(`TauCeti.two_mul_mul_integral_le_integral_sum_euclideanWittenLaplacian_diagonalQuadratic_mul`):
the linear-in-`t` gap of the model.

**The gap in the degree of the Morse index.** In degree `s₀` the coefficient `φ_{s₀}` is acted on
by the oscillators shifted down by exactly their ground state energy `t ∑ᵢ |aᵢ|`. Expanding it in
the dilated Hermite functions (`TauCeti.Analysis.SpecialFunctions.Hermite.Function.Pi.SpectralGap`)
shows that, if `φ` is orthogonal to the Gaussian ground state
`Ψ_{0,s₀} = TauCeti.diagonalQuadraticWittenEigenform a t 0 s₀`, this part also costs at least
`2 t c` times its squared norm. So the whole quadratic form is at least `2 t c ∫ |φ|²` on forms
orthogonal to the ground state, by the theorem
`two_mul_mul_integral_le_integral_sum_euclideanWittenLaplacian_diagonalQuadratic_of_orthogonal`
below: under `2 t c` the model has room for the one state `Ψ_{0,s₀}` only. These are statements
about the quadratic form on compactly supported smooth forms, not about the spectrum of a
self-adjoint realization of `Δ_t`.

The integrals are against an arbitrary additive Haar measure `μ` on `ℝ^ι`; all of them are finite,
since the integrands are continuous with compact support.

## Main results

* `TauCeti.integral_sum_euclideanWittenLaplacian_mul`: the energy identity.
* `TauCeti.sum_mul_integral_le_integral_sum_euclideanWittenLaplacian_diagonalQuadratic_mul`: the
  harmonic-oscillator lower bound for the quadratic model.
* `TauCeti.integral_sum_euclideanWittenLaplacian_diagonalQuadratic_mul_nonneg`,
  `TauCeti.two_mul_mul_integral_le_integral_sum_euclideanWittenLaplacian_diagonalQuadratic_mul`:
  the model quadratic form is nonnegative, with a gap `2 t c` outside the degree of the Morse
  index.
* `two_mul_mul_integral_le_integral_sum_euclideanWittenLaplacian_diagonalQuadratic_of_orthogonal`:
  on forms orthogonal to the Gaussian ground state the gap `2 t c` holds in every degree.

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

variable [LinearOrder ι]

section General

/-- The potential term `|df|² |φ|²` of the energy identity is integrable. -/
private theorem integrable_sum_fderiv_sq_mul_sum_sq (hf : ContDiff ℝ 2 f) (hφ : ContDiff ℝ 2 φ)
    (hφc : HasCompactSupport φ) :
    Integrable (fun x ↦ (∑ i, fderiv ℝ f x (Pi.single i 1) ^ 2) * ∑ s, φ x s ^ 2) μ := by
  simp only [Finset.mul_sum]
  exact integrable_finsetSum _ fun s _ ↦ integrable_mul_sq_of_hasCompactSupport
    (ContinuousLinearMap.proj s) (continuous_finsetSum _ fun i _ ↦
      ((hf.continuous_fderiv (by norm_num)).clm_apply continuous_const).pow 2)
    hφ.continuous hφc

private theorem integrable_sum_hessian_lie_apply_mul (hf : ContDiff ℝ 2 f)
    (hφ : ContDiff ℝ 2 φ) (hφc : HasCompactSupport φ) :
    Integrable (fun x ↦ ∑ s, (∑ i, ∑ j,
      fderiv ℝ (fderiv ℝ f) x (Pi.single i 1) (Pi.single j 1) •
        ⁅(Pi.basisFun ℝ ι).exteriorCreation i, (Pi.basisFun ℝ ι).exteriorContraction j⁆
          (φ x)) s * φ x s) μ :=
  (continuous_finsetSum _ fun s _ ↦ ((continuous_apply s).comp
    (continuous_finsetSum _ fun i _ ↦ continuous_finsetSum _ fun j _ ↦
      ((((hf.fderiv_right (m := 1) (by norm_num)).continuous_fderiv one_ne_zero).clm_apply
        continuous_const).clm_apply continuous_const).smul
        (LinearMap.continuous_of_finiteDimensional _ |>.comp hφ.continuous))).mul
    ((continuous_apply s).comp hφ.continuous))
    |>.integrable_of_hasCompactSupport <| hφc.mono' <| Function.support_subset_iff'.2
      fun x hx ↦ by simp [image_eq_zero_of_notMem_tsupport hx]

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
  have hA : ∀ i s, Integrable
      (fun x ↦ -fderiv ℝ (fderiv ℝ φ) x (Pi.single i 1) (Pi.single i 1) s * φ x s) μ :=
    fun i s ↦ integrable_neg_fderiv_fderiv_apply_mul_of_hasCompactSupport
      (ContinuousLinearMap.proj s) hφ hφc (Pi.single i 1) (Pi.single i 1)
  have hA' : ∀ i s, Integrable (fun x ↦ fderiv ℝ φ x (Pi.single i 1) s ^ 2) μ :=
    fun i s ↦ integrable_sq_of_hasCompactSupport (ContinuousLinearMap.proj s)
      ((hφ.continuous_fderiv (by norm_num)).clm_apply continuous_const)
      (hφc.fderiv_apply (𝕜 := ℝ) (Pi.single i 1))
  have hG := integrable_sum_fderiv_sq_mul_sum_sq (μ := μ) hf hφ hφc
  have hK := integrable_sum_hessian_lie_apply_mul (μ := μ) hf hφ hφc
  simp only [sum_euclideanWittenLaplacian_apply_mul hf.contDiffAt hφ.contDiffAt]
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
  exact Finset.sum_congr rfl fun s _ ↦ by
    simpa using integral_neg_fderiv_fderiv_apply_mul_eq_integral_sq (μ := μ)
      (ContinuousLinearMap.proj s) hφ hφc (Pi.single i 1)

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

/-- The quadratic form of the Witten Laplacian of the quadratic model, split into the degrees `s`
and, in each degree, into the oscillators `-∂ᵢ² + t² aᵢ² xᵢ²` and the degree shift. -/
private theorem integral_sum_euclideanWittenLaplacian_diagonalQuadratic_mul_eq (a : ι → ℝ) (t : ℝ)
    (hφ : ContDiff ℝ 2 φ) (hφc : HasCompactSupport φ) :
    ∫ x, ∑ s, euclideanWittenLaplacian (diagonalQuadratic a) t φ x s * φ x s ∂μ =
      ∑ s, (∑ i, (∫ x, -fderiv ℝ (fderiv ℝ φ) x (Pi.single i 1) (Pi.single i 1) s * φ x s ∂μ +
          t ^ 2 * a i ^ 2 * ∫ x, x i ^ 2 * φ x s ^ 2 ∂μ) +
        t * (∑ i, if i ∈ s then a i else -a i) * ∫ x, φ x s ^ 2 ∂μ) := by
  have hA : ∀ i s, Integrable
      (fun x ↦ -fderiv ℝ (fderiv ℝ φ) x (Pi.single i 1) (Pi.single i 1) s * φ x s) μ :=
    fun i s ↦ integrable_neg_fderiv_fderiv_apply_mul_of_hasCompactSupport
      (ContinuousLinearMap.proj s) hφ hφc (Pi.single i 1) (Pi.single i 1)
  have hX : ∀ (i : ι) s, Integrable (fun x ↦ x i ^ 2 * φ x s ^ 2) μ :=
    fun i s ↦ integrable_mul_sq_of_hasCompactSupport (ContinuousLinearMap.proj s)
      ((continuous_apply i).pow 2) hφ.continuous hφc
  have hN : ∀ s, Integrable (fun x ↦ φ x s ^ 2) μ :=
    fun s ↦ integrable_sq_of_hasCompactSupport (ContinuousLinearMap.proj s) hφ.continuous hφc
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
  refine Finset.sum_congr rfl fun s _ ↦ ?_
  rw [integral_add (hS s) ((hN s).const_mul _), integral_finsetSum _ fun i _ ↦ hAX i s,
    integral_const_mul]
  congr 1
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [integral_add (hA i s) ((hX i s).const_mul _), integral_const_mul]

/-- In each degree `s`, the oscillators and the degree shift contribute at least `μ(0, s) ∫ φ_s²`
to the quadratic form of the model: each oscillator `-∂ᵢ² + t² aᵢ² xᵢ²` is at least
`|t aᵢ| ≥ t |aᵢ|` by the uncertainty inequality. -/
private theorem diagonalQuadraticWittenEigenvalue_zero_mul_integral_le (a : ι → ℝ) (t : ℝ)
    (hφ : ContDiff ℝ 2 φ) (hφc : HasCompactSupport φ) (s : Finset ι) :
    diagonalQuadraticWittenEigenvalue a t 0 s * ∫ x, φ x s ^ 2 ∂μ ≤
      ∑ i, (∫ x, -fderiv ℝ (fderiv ℝ φ) x (Pi.single i 1) (Pi.single i 1) s * φ x s ∂μ +
          t ^ 2 * a i ^ 2 * ∫ x, x i ^ 2 * φ x s ^ 2 ∂μ) +
        t * (∑ i, if i ∈ s then a i else -a i) * ∫ x, φ x s ^ 2 ∂μ := by
  have hosc : ∑ i, t * |a i| * ∫ x, φ x s ^ 2 ∂μ ≤
      ∑ i, (∫ x, -fderiv ℝ (fderiv ℝ φ) x (Pi.single i 1) (Pi.single i 1) s * φ x s ∂μ +
        t ^ 2 * a i ^ 2 * ∫ x, x i ^ 2 * φ x s ^ 2 ∂μ) := Finset.sum_le_sum fun i _ ↦ by
    have h := abs_mul_integral_sq_le_integral_neg_fderiv_fderiv_apply_mul_add (μ := μ)
      (ContinuousLinearMap.proj s) (ℓ := ContinuousLinearMap.proj i) (v := Pi.single i 1)
      (by simp) hφ hφc (t * a i)
    simp only [ContinuousLinearMap.proj_apply, mul_pow] at h
    have ht : t * |a i| * ∫ x, φ x s ^ 2 ∂μ ≤ |t * a i| * ∫ x, φ x s ^ 2 ∂μ :=
      mul_le_mul_of_nonneg_right (by rw [abs_mul]; gcongr; exact le_abs_self t)
        (integral_nonneg fun _ ↦ sq_nonneg _)
    linarith
  have hμ : diagonalQuadraticWittenEigenvalue a t 0 s * ∫ x, φ x s ^ 2 ∂μ =
      ∑ i, t * |a i| * ∫ x, φ x s ^ 2 ∂μ +
        t * (∑ i, if i ∈ s then a i else -a i) * ∫ x, φ x s ^ 2 ∂μ := by
    rw [diagonalQuadraticWittenEigenvalue_zero, add_mul, Finset.sum_mul]
  linarith

/-- **The harmonic-oscillator lower bound.** For the diagonal quadratic function
`f = ∑ᵢ aᵢ xᵢ² / 2`, a real `t` and a compactly supported `C²` form `φ`, the quadratic form of the
Witten Laplacian is at least `∑ s, μ(0, s) ∫ φ_s²`, where `φ_s` is the coefficient of `dx^s` and
`μ(0, s) = t ∑ᵢ (|aᵢ| ± aᵢ)`. For `t > 0` and every `aᵢ ≠ 0`, `μ(0, s)` is the eigenvalue of the
Gaussian ground state in degree `s`; for other parameters it is only the coefficient of the bound.
The bound is informative for `t ≥ 0`, where every `μ(0, s)` is nonnegative. -/
theorem sum_mul_integral_le_integral_sum_euclideanWittenLaplacian_diagonalQuadratic_mul
    (a : ι → ℝ) (t : ℝ) (hφ : ContDiff ℝ 2 φ) (hφc : HasCompactSupport φ) :
    ∑ s, diagonalQuadraticWittenEigenvalue a t 0 s * ∫ x, φ x s ^ 2 ∂μ ≤
      ∫ x, ∑ s, euclideanWittenLaplacian (diagonalQuadratic a) t φ x s * φ x s ∂μ := by
  rw [integral_sum_euclideanWittenLaplacian_diagonalQuadratic_mul_eq a t hφ hφc]
  exact Finset.sum_le_sum fun s _ ↦
    diagonalQuadraticWittenEigenvalue_zero_mul_integral_le a t hφ hφc s

/-- The quadratic form of the Witten Laplacian of a diagonal quadratic function is nonnegative
on compactly supported `C²` forms, for every real `t`. For `t ≥ 0` every coefficient `μ(0, s)` of
the harmonic-oscillator lower bound is nonnegative; for `t ≤ 0` the quadratic form is that of
`-a` with parameter `-t`. -/
theorem integral_sum_euclideanWittenLaplacian_diagonalQuadratic_mul_nonneg (a : ι → ℝ) (t : ℝ)
    (hφ : ContDiff ℝ 2 φ) (hφc : HasCompactSupport φ) :
    0 ≤ ∫ x, ∑ s, euclideanWittenLaplacian (diagonalQuadratic a) t φ x s * φ x s ∂μ := by
  have key : ∀ (a : ι → ℝ) {t : ℝ}, 0 ≤ t →
      0 ≤ ∫ x, ∑ s, euclideanWittenLaplacian (diagonalQuadratic a) t φ x s * φ x s ∂μ :=
    fun a t ht ↦ (Finset.sum_nonneg fun s _ ↦ mul_nonneg
      (diagonalQuadraticWittenEigenvalue_nonneg a ht 0 s)
      (integral_nonneg fun _ ↦ sq_nonneg _)).trans
      (sum_mul_integral_le_integral_sum_euclideanWittenLaplacian_diagonalQuadratic_mul a t hφ hφc)
  rcases le_total 0 t with ht | ht
  · exact key a ht
  · convert key (-a) (neg_nonneg.2 ht) using 3 with x
    simp only [sum_euclideanWittenLaplacian_diagonalQuadratic_apply_mul hφ, Pi.neg_apply,
      neg_sq, neg_neg]
    refine Finset.sum_congr rfl fun s _ ↦ ?_
    congr 1
    rw [neg_mul, ← mul_neg, ← Finset.sum_neg_distrib]
    congr 2
    exact Finset.sum_congr rfl fun i _ ↦ by split_ifs <;> simp

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
    (sum_mul_integral_le_integral_sum_euclideanWittenLaplacian_diagonalQuadratic_mul a t hφ hφc)
  have hN : ∀ s, Integrable (fun x ↦ φ x s ^ 2) μ :=
    fun s ↦ integrable_sq_of_hasCompactSupport (ContinuousLinearMap.proj s) hφ.continuous hφc
  rw [integral_finsetSum _ fun s _ ↦ hN s, Finset.mul_sum,
    ← Finset.sum_erase_add _ _ (Finset.mem_univ (Finset.univ.filter fun i ↦ a i < 0)),
    diagonalQuadraticWittenEigenvalue_zero_filter_neg, zero_mul, add_zero]
  refine Finset.sum_le_sum fun s hs ↦ mul_le_mul_of_nonneg_right
    (two_mul_mul_le_diagonalQuadraticWittenEigenvalue ht hc fun h ↦ ?_)
    (integral_nonneg fun _ ↦ sq_nonneg _)
  exact (Finset.mem_erase.1 hs).1 h.2

/-- **The gap of the harmonic-oscillator model above its ground state.** If `c ≤ |aᵢ|` for every
`i` and `t ≥ 0`, every compactly supported `C²` form `φ` orthogonal to the Gaussian ground state
`Ψ_{0,s₀}` (`TauCeti.diagonalQuadraticWittenEigenform`) in the degree `s₀ = {i | aᵢ < 0}` of the
Morse index has quadratic form at least `2 t c ∫ |φ|²` for the Witten Laplacian of
`∑ᵢ aᵢ xᵢ² / 2`. So, on compactly supported forms, the part of the quadratic form below `2 t c` is
carried by the single ground state: in degree `s₀` the excited Hermite states lie at least
`2 t minᵢ |aᵢ|` above it, and in every other degree all states do. -/
theorem
    two_mul_mul_integral_le_integral_sum_euclideanWittenLaplacian_diagonalQuadratic_of_orthogonal
    {t : ℝ} (ht : 0 ≤ t) {c : ℝ} (hc : ∀ i, c ≤ |a i|) (hφ : ContDiff ℝ 2 φ)
    (hφc : HasCompactSupport φ)
    (horth : ∫ x, ∑ s, diagonalQuadraticWittenEigenform a t 0
      (Finset.univ.filter fun i ↦ a i < 0) x s * φ x s ∂μ = 0) :
    2 * t * c * ∫ x, ∑ s, φ x s ^ 2 ∂μ ≤
      ∫ x, ∑ s, euclideanWittenLaplacian (diagonalQuadratic a) t φ x s * φ x s ∂μ := by
  set s₀ := Finset.univ.filter fun i ↦ a i < 0
  have hN : ∀ s, Integrable (fun x ↦ φ x s ^ 2) μ :=
    fun s ↦ integrable_sq_of_hasCompactSupport (ContinuousLinearMap.proj s) hφ.continuous hφc
  rw [integral_sum_euclideanWittenLaplacian_diagonalQuadratic_mul_eq a t hφ hφc,
    integral_finsetSum _ fun s _ ↦ hN s, Finset.mul_sum]
  refine Finset.sum_le_sum fun s _ ↦ ?_
  by_cases hs : s = s₀
  swap
  · -- outside the ground state degree every Hermite eigenvalue is at least `2 t c`
    exact (mul_le_mul_of_nonneg_right (two_mul_mul_le_diagonalQuadraticWittenEigenvalue ht hc
      fun h ↦ hs h.2) (integral_nonneg fun _ ↦ sq_nonneg _)).trans
      (diagonalQuadraticWittenEigenvalue_zero_mul_integral_le a t hφ hφc s)
  subst hs
  -- in degree `s₀` the degree shift `-t ∑ᵢ |aᵢ|` cancels the ground state energy of the oscillators
  have hshift : t * (∑ i, if i ∈ s₀ then a i else -a i) = -∑ i, t * |a i| := by
    have h := diagonalQuadraticWittenEigenvalue_zero_filter_neg a t
    rw [diagonalQuadraticWittenEigenvalue_zero] at h
    linarith
  -- the coefficient `u = φ_{s₀}` is orthogonal to the ground state of the oscillators
  set L := ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Finset ι ↦ ℝ) s₀
  have hL : fderiv ℝ L = fun _ ↦ L := funext fun _ ↦ L.fderiv
  have hD : ∀ x i, fderiv ℝ (fderiv ℝ (L ∘ φ)) x (Pi.single i 1) (Pi.single i 1) =
      fderiv ℝ (fderiv ℝ φ) x (Pi.single i 1) (Pi.single i 1) s₀ := fun x i ↦ by
    simpa [hL, L] using fderiv_fderiv_comp_apply L.contDiff.contDiffAt hφ.contDiffAt
      (Pi.single i 1) (Pi.single i 1)
  have horth' : ∫ x, (∏ i, hermiteFunction 0 (√(t * |a i|) * x i)) * φ x s₀ ∂μ = 0 := by
    simpa [diagonalQuadraticWittenEigenform_apply, Pi.single_apply] using horth
  have h := add_two_mul_mul_integral_sq_le_sum_integral_neg_fderiv_fderiv_mul_add_mul_integral
    (μ := μ) (ω := fun i ↦ t * |a i|) (κ := t * c) (u := L ∘ φ)
    (fun i ↦ mul_le_mul_of_nonneg_left (hc i) ht) (L.contDiff.comp hφ)
    (hφc.comp_left (g := L) L.map_zero) horth'
  simp only [hD, mul_pow, sq_abs, Function.comp_apply, L, ContinuousLinearMap.proj_apply] at h
  rw [hshift]
  linarith

end Model

end TauCeti
