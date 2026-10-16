/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Regularity.Hessian.Lp
public import TauCeti.Analysis.PDE.Ellipticity.ConstantCoefficient
import TauCeti.Analysis.Calculus.IteratedFDeriv.CompContinuousLinearEquiv
import TauCeti.Analysis.PDE.Ellipticity.Basic
import TauCeti.MeasureTheory.Function.Lp.Dilation

/-!
# The Calderón–Zygmund estimate for constant-coefficient operators

Let `A` be a constant `n × n` coefficient matrix whose quadratic form satisfies
`λ ‖ξ‖² ≤ ξᵀ A ξ` with `0 < λ`, and write `L_A u = ∑ᵢⱼ Aᵢⱼ ∂ᵢ∂ⱼu`. For every dimension `n` and `1
< p < ∞`,
this file proves

`‖D²u‖_{Lᵖ} ≤ (C / λ) ‖L_A u‖_{Lᵖ}`

for every Schwartz function `u` on `ℝⁿ`, real valued or with values in a fixed complex Hilbert
space `F`, with a constant `C` depending only on `n` and `p`, and on `F` in the Hilbert-space case
(`TauCeti.PDE.exists_eLpNorm_iteratedFDeriv_two_le_eLpNorm_sum_smul_fderiv_fderiv` and
`TauCeti.PDE.exists_eLpNorm_iteratedFDeriv_two_le_eLpNorm_sum_smul_fderiv_fderiv_real`). The
constant does not depend on `A` beyond the lower ellipticity constant `λ`; no upper bound on `A`
enters. This uniformity is what the `W^{2,p}` theory for continuous coefficients needs: the
coefficients are frozen at a point of each small ball, and the frozen matrices range over all
matrices with a common lower ellipticity constant.

## The argument

The case `A = 1` is the Calderón–Zygmund estimate for the Laplacian
(`TauCeti.exists_eLpNorm_iteratedFDeriv_two_le_eLpNorm_laplacian`). For general `A` there is a
linear automorphism `e` with `‖e⁻¹‖ ≤ λ^(-1/2)` such that `Δ (u ∘ e) = (L_A u) ∘ e`
(`TauCeti.PDE.exists_continuousLinearEquiv_laplacian_comp_eq`). The Schwartz function
`v = u ∘ e` then satisfies `D²u (e y) = D²v y ∘ (e⁻¹ × e⁻¹)`, so `‖D²u ∘ e‖ ≤ λ⁻¹ ‖D²v‖`
pointwise, while `Δ v = (L_A u) ∘ e`. Composing with `e` multiplies both `Lᵖ` norms by the same
factor `|det e|^(-1 / p)` (`TauCeti.eLpNorm_comp_continuousLinearEquiv`), which cancels. This
transfer is stated for any codomain and any exponent in which the estimate for the Laplacian holds
(`TauCeti.PDE.eLpNorm_iteratedFDeriv_two_le_eLpNorm_sum_smul_fderiv_fderiv_of_laplacian`).

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Section 6.1 (reduction of a constant-coefficient operator to the Laplacian by a linear change
  of variables) and Section 9.5 (`W^{2,p}` estimates by freezing the coefficients).
-/

public section

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal Laplacian SchwartzMap

namespace TauCeti

namespace PDE

section Transfer

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {G : Type*} [NormedAddCommGroup G]
  [NormedSpace ℝ G] {A : Matrix ι ι ℝ} {lam : ℝ} {p : ℝ≥0∞}

/-- **Transfer of the Calderón–Zygmund estimate from the Laplacian to constant coefficients.**
Suppose that `‖D²v‖_p ≤ C ‖Δv‖_p` for every Schwartz function `v` on `ℝⁿ` with values in `G`.
If `λ ‖ξ‖² ≤ ξᵀ A ξ` with `0 < λ`, then every such Schwartz function `u` satisfies

`‖D²u‖_p ≤ (C / λ) ‖∑ᵢⱼ Aᵢⱼ ∂ᵢ∂ⱼu‖_p`. -/
theorem eLpNorm_iteratedFDeriv_two_le_eLpNorm_sum_smul_fderiv_fderiv_of_laplacian
    (hlam : 0 < lam) (hA : ∀ ξ : EuclideanSpace ℝ ι, lam * ‖ξ‖ ^ 2 ≤ A.toQuadraticForm' ξ)
    {C : ℝ≥0} (hC : ∀ v : 𝓢(EuclideanSpace ℝ ι, G),
      eLpNorm (iteratedFDeriv ℝ 2 ⇑v) p volume ≤
        C * eLpNorm (⇑(Δ v : 𝓢(EuclideanSpace ℝ ι, G))) p volume)
    (u : 𝓢(EuclideanSpace ℝ ι, G)) :
    eLpNorm (iteratedFDeriv ℝ 2 ⇑u) p volume ≤ ENNReal.ofReal (C / lam) *
      eLpNorm (fun x => ∑ i, ∑ j, A i j • fderiv ℝ (fderiv ℝ ⇑u) x
        (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) p volume := by
  set L : EuclideanSpace ℝ ι → G := fun x => ∑ i, ∑ j, A i j • fderiv ℝ (fderiv ℝ ⇑u) x
    (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)
  obtain ⟨e, he, -, hΔ⟩ := exists_continuousLinearEquiv_laplacian_comp_eq (F := G) hlam hA
    (toQuadraticForm'_le_norm_matrixBilinearForm_mul_sq A)
  -- The Schwartz function `v = u ∘ e`.
  set v := SchwartzMap.compCLMOfContinuousLinearEquiv ℝ e u
  have hv : ⇑v = ⇑u ∘ e := SchwartzMap.compCLMOfContinuousLinearEquiv_apply ℝ e u
  have hΔv : ⇑(Δ v : 𝓢(EuclideanSpace ℝ ι, G)) = L ∘ e := funext fun y => by
    rw [SchwartzMap.laplacian_apply, hv]
    exact hΔ u y ((u.smooth ⊤).of_le (by simp)).contDiffAt
  -- Pointwise, `‖D²u ∘ e‖ ≤ λ⁻¹ ‖D²v‖`, since `D²u (e y) = D²v y ∘ (e⁻¹ × e⁻¹)`.
  have hes : ‖(e.symm : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι)‖ ≤ (√lam)⁻¹ :=
    ContinuousLinearMap.opNorm_le_bound _ (by positivity) he
  have hes2 : ‖(e.symm : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι)‖ *
      ‖(e.symm : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι)‖ ≤ lam⁻¹ :=
    (mul_le_mul hes hes (norm_nonneg _) (by positivity)).trans_eq
      (by rw [← mul_inv, Real.mul_self_sqrt hlam.le])
  have hpt : ∀ y, ‖(iteratedFDeriv ℝ 2 ⇑u ∘ e) y‖ ≤ lam⁻¹ * ‖iteratedFDeriv ℝ 2 ⇑v y‖ :=
    fun y => by
      rw [Function.comp_apply, hv]
      refine (e.norm_iteratedFDeriv_le_pow_mul_norm_iteratedFDeriv_comp_right _ y 2).trans ?_
      rw [sq]
      exact mul_le_mul_of_nonneg_right hes2 (norm_nonneg _)
  -- Composing with `e` scales both `Lᵖ` norms by the same nonzero finite factor `c`.
  set c := ENNReal.ofReal |(LinearMap.det (e : EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ ι))⁻¹| ^
    (1 / p).toReal with hc_def
  have hdet : LinearMap.det (e : EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ ι) ≠ 0 :=
    (LinearEquiv.isUnit_det' e.toLinearEquiv).ne_zero
  have hc0 : c ≠ 0 := (ENNReal.rpow_pos (by simpa using hdet) ENNReal.ofReal_ne_top).ne'
  have hctop : c ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg ENNReal.toReal_nonneg ENNReal.ofReal_ne_top
  have h1 := eLpNorm_comp_continuousLinearEquiv volume (iteratedFDeriv ℝ 2 ⇑u) e p
  have h2 := eLpNorm_comp_continuousLinearEquiv volume L e p
  rw [← hc_def] at h1 h2
  have hmeas : AEStronglyMeasurable (iteratedFDeriv ℝ 2 ⇑u ∘ e) volume :=
    (((u.smooth ⊤).continuous_iteratedFDeriv (by simp)).comp e.continuous).aestronglyMeasurable
  refine (ENNReal.mul_le_mul_iff_right hc0 hctop).1 ?_
  calc c * eLpNorm (iteratedFDeriv ℝ 2 ⇑u) p volume
      = eLpNorm (iteratedFDeriv ℝ 2 ⇑u ∘ e) p volume := h1.symm
    _ ≤ ENNReal.ofReal lam⁻¹ * eLpNorm (iteratedFDeriv ℝ 2 ⇑v) p volume :=
        eLpNorm_le_mul_eLpNorm_of_ae_le_mul hmeas (ae_of_all _ hpt) p
    _ ≤ ENNReal.ofReal lam⁻¹ * (C * eLpNorm (⇑(Δ v : 𝓢(EuclideanSpace ℝ ι, G))) p volume) := by
        gcongr
        exact hC v
    _ = c * (ENNReal.ofReal (C / lam) * eLpNorm L p volume) := by
        rw [hΔv, h2, div_eq_mul_inv, ENNReal.ofReal_mul C.coe_nonneg, ENNReal.ofReal_coe_nnreal]
        ring

end Transfer

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  {p : ℝ≥0∞}

/-- **The Calderón–Zygmund estimate for constant-coefficient operators.** Let `1 < p < ∞`, and let
`F` be a complex Hilbert space. There is a constant `C`, depending only on `n`,
`p` and `F`, such that for every matrix `A` with `λ ‖ξ‖² ≤ ξᵀ A ξ` and `0 < λ`,

`‖D²u‖_{Lᵖ} ≤ (C / λ) ‖∑ᵢⱼ Aᵢⱼ ∂ᵢ∂ⱼu‖_{Lᵖ}`

for every Schwartz function `u` on `ℝⁿ` with values in `F`. -/
theorem exists_eLpNorm_iteratedFDeriv_two_le_eLpNorm_sum_smul_fderiv_fderiv
    (hp : 1 < p) (hp_top : p ≠ ∞) :
    ∃ C : ℝ≥0, ∀ {A : Matrix (Fin n) (Fin n) ℝ} {lam : ℝ}, 0 < lam →
      (∀ ξ : EuclideanSpace ℝ (Fin n), lam * ‖ξ‖ ^ 2 ≤ A.toQuadraticForm' ξ) →
        ∀ u : 𝓢(EuclideanSpace ℝ (Fin n), F), eLpNorm (iteratedFDeriv ℝ 2 ⇑u) p volume ≤
          ENNReal.ofReal (C / lam) * eLpNorm (fun x => ∑ i, ∑ j, A i j •
            fderiv ℝ (fderiv ℝ ⇑u) x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1))
              p volume := by
  obtain ⟨C, hC⟩ := exists_eLpNorm_iteratedFDeriv_two_le_eLpNorm_laplacian (F := F) hp hp_top
  exact ⟨C, fun hlam hA u =>
    eLpNorm_iteratedFDeriv_two_le_eLpNorm_sum_smul_fderiv_fderiv_of_laplacian hlam hA hC u⟩

omit [InnerProductSpace ℂ F] [CompleteSpace F] in
/-- **The Calderón–Zygmund estimate for constant-coefficient operators, real-valued form.** Let
`1 < p < ∞`, in any dimension `n`. There is a constant `C`, depending only on `n` and `p`, such
that for every
matrix `A` with `λ ‖ξ‖² ≤ ξᵀ A ξ` and `0 < λ`,

`‖D²u‖_{Lᵖ} ≤ (C / λ) ‖∑ᵢⱼ Aᵢⱼ ∂ᵢ∂ⱼu‖_{Lᵖ}`

for every real-valued Schwartz function `u` on `ℝⁿ`. -/
theorem exists_eLpNorm_iteratedFDeriv_two_le_eLpNorm_sum_smul_fderiv_fderiv_real
    (hp : 1 < p) (hp_top : p ≠ ∞) :
    ∃ C : ℝ≥0, ∀ {A : Matrix (Fin n) (Fin n) ℝ} {lam : ℝ}, 0 < lam →
      (∀ ξ : EuclideanSpace ℝ (Fin n), lam * ‖ξ‖ ^ 2 ≤ A.toQuadraticForm' ξ) →
        ∀ u : 𝓢(EuclideanSpace ℝ (Fin n), ℝ), eLpNorm (iteratedFDeriv ℝ 2 ⇑u) p volume ≤
          ENNReal.ofReal (C / lam) * eLpNorm (fun x => ∑ i, ∑ j, A i j •
            fderiv ℝ (fderiv ℝ ⇑u) x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1))
              p volume := by
  obtain ⟨C, hC⟩ := exists_eLpNorm_iteratedFDeriv_two_le_eLpNorm_laplacian_real hp hp_top
  exact ⟨C, fun hlam hA u =>
    eLpNorm_iteratedFDeriv_two_le_eLpNorm_sum_smul_fderiv_fderiv_of_laplacian hlam hA hC u⟩

end PDE

end TauCeti
