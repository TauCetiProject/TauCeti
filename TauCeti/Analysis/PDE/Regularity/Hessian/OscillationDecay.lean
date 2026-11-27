/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Harmonic.Decay
public import TauCeti.Analysis.Sobolev.Wkp.Basic
public import Mathlib.LinearAlgebra.QuadraticForm.Basic
public import TauCeti.Analysis.PDE.Ellipticity.Basic
import Mathlib.Analysis.MeanInequalities
import TauCeti.Analysis.Distribution.TestFunction.LinearEquiv
import TauCeti.Analysis.InnerProductSpace.Harmonic.Analytic
import TauCeti.Analysis.InnerProductSpace.Harmonic.Deriv
import TauCeti.Analysis.InnerProductSpace.Harmonic.Weyl
import TauCeti.Analysis.PDE.Ellipticity.ConstantCoefficient
import TauCeti.Analysis.PDE.Regularity.Hessian.Dirichlet.Ball
import TauCeti.Analysis.Sobolev.Wkp.Classical
import TauCeti.Analysis.Sobolev.Wkp.Laplacian
import TauCeti.Analysis.Sobolev.Wkp.Restriction
import TauCeti.MeasureTheory.Function.Lp.Norm
import TauCeti.MeasureTheory.Integral.Average.Jensen
import TauCeti.MeasureTheory.Integral.Average.Oscillation
import TauCeti.MeasureTheory.Measure.Haar.Average
import TauCeti.MeasureTheory.Measure.Haar.NormedSpace
import TauCeti.MeasureTheory.Measure.OpenPos

/-!
# Decay of the mean oscillation of the Hessian for constant coefficients

Let `A` be a constant coefficient matrix with `λ ‖ξ‖² ≤ ξᵀ A ξ`, `0 < λ`, and let
`u ∈ W^{2,p}(Ω)`, `1 ≤ p ≤ ∞`, be a strong solution of the homogeneous equation

`∑ᵢⱼ Aᵢⱼ ∂ᵢ∂ⱼu = 0` almost everywhere on an open set `Ω ⊆ ℝⁿ`.

This file shows that `u` agrees almost everywhere with a smooth function `g` solving the equation
classically on `Ω` (`TauCeti.PDE.exists_contDiffOn_ae_eq_and_sum_smul_fderiv_fderiv_eq_zero`), and
that the `L¹` mean oscillation of its weak Hessian `D²u` decays on concentric balls
`B_ρ ⊆ B_R ⊆ Ω` one order faster than the volume:

`∫_{B_ρ} ‖D²u - (D²u)_ρ‖ ≤ C (Λ / λ)^((n + 1) / 2) (ρ / R)^(n + 1) ∫_{B_R} ‖D²u - c‖`

for every constant `c`, with `C = 2^(3n + 5) (n + 1)` and `ξᵀ A ξ ≤ Λ ‖ξ‖²`
(`TauCeti.PDE.setIntegral_ball_norm_iteratedGradient_sub_setAverage_le_of_sum_mul_inner_eq_zero`).
In averaged form, `⨍_{B_ρ} ‖D²u - (D²u)_ρ‖ ≤ C (Λ / λ)^((n + 1) / 2) (ρ / R) ⨍_{B_R} ‖D²u - c‖`
(`TauCeti.PDE.setAverage_ball_norm_iteratedGradient_sub_setAverage_le_of_sum_mul_inner_eq_zero`).

No integrability of `D²u` beyond `L^p` with `p ≥ 1` is assumed, and the right-hand side involves
only the `L¹` norm. Since `⨍ ‖D²u - c‖ ≤ (⨍ ‖D²u - c‖^q)^(1/q)` for `q ≥ 1`, this is the decay of
the frozen problem in the mean oscillation estimates for the `W^{2,q}` theory with coefficients of
vanishing mean oscillation in the range `1 < q < 2`, where the solutions need not have square
integrable second derivatives and the `L²` decay
(`TauCeti.PDE.setIntegral_ball_norm_iteratedGradient_sub_setAverage_sq_le_add_of_sum_mul_inner_eq`)
does not apply.

With forcing, for `1 < p < ∞` and a strong solution `u ∈ W^{2,p}(Ω)` of `∑ᵢⱼ Aᵢⱼ ∂ᵢ∂ⱼu = F` on
`B_r`, comparison with the solution `w ∈ W^{2,p}(B_r) ∩ W^{1,p}_0(B_r)` of the same equation gives,
with `γ = p`,

`(⨍_{B_ρ} ‖D²u - (D²u)_ρ‖)^γ ≤ K₁ (ρ / r)^γ ⨍_{B_r} ‖D²u‖^γ + K₂ (r / ρ)^(n + 1) ⨍_{B_r} |F|^γ`

with constants depending only on `n`, `p`, `λ` and `Λ`
(`TauCeti.PDE.exists_rpow_setAverage_norm_iteratedGradient_sub_setAverage_le_of_sum_mul_inner_eq`).
The difference `u - w` solves the homogeneous equation, so its `L¹` mean oscillation decays, and
`D²w` is bounded in `Lᵖ(B_r)` by `F` with a constant uniform over the balls and the matrices
(`TauCeti.exists_firstOrder_mem_w1p0Submodule_and_contraction_iteratedGradient_eq_and_norm_le`).
This is the one-ball estimate of the sharp function method in `L¹`.

## The argument

Only the symmetric part of `A` enters, and a linear change of variables `e` with
`Δ (φ ∘ e) = (∑ᵢⱼ Aᵢⱼ ∂ᵢ∂ⱼφ) ∘ e` for smooth `φ`
(`TauCeti.PDE.exists_continuousLinearEquiv_laplacian_comp_eq`) turns the operator into the
Laplacian.

* **Weyl's lemma.** For a test function `φ` on `e⁻¹(Ω)`, the test function `ψ = φ ∘ e⁻¹` on `Ω`
  has `Δφ ∘ e⁻¹ = ∑ᵢⱼ Aᵢⱼ ∂ᵢ∂ⱼψ`, and integrating by parts twice
  (`TauCeti.Wkp.integral_sum_smul_fderiv_fderiv_smul_value_eq_sum_mul_inner_iteratedGradient`)
  gives
  `∫ Δφ (u ∘ e) d(μ.map e⁻¹) = ∫ ψ ∑ᵢⱼ Aᵢⱼ ∂ᵢ∂ⱼu dμ = 0`; the Haar measure `μ.map e⁻¹`, which `e`
  carries to `μ`, avoids the Jacobian of `e`. So `u ∘ e` is weakly harmonic, hence harmonic up to
  a null set (`TauCeti.WeaklyHarmonicOn.exists_harmonicOnNhd_ae_eq`).
* **Decay.** The weak Hessian of `u` is then the classical Hessian `D²g` almost everywhere
  (`TauCeti.Wkp.iteratedGradient_ae_eq_of_contDiffOn`). Its composite with `e` is the derivative
  of the harmonic field `∇g ∘ e` followed by `e⁻¹`, so it is harmonic
  (`InnerProductSpace.HarmonicOnNhd.fderiv`), and the `L¹` decay of harmonic
  functions after a linear change of variables
  (`TauCeti.setIntegral_ball_norm_sub_setAverage_le_of_harmonicOnNhd_comp`) applies, with
  `‖e⁻¹‖ ≤ λ^(-1/2)` and `‖e‖ ≤ Λ^(1/2)`.

## References

* H. Dong, D. Kim, *On the `Lₚ`-solvability of higher order parabolic and elliptic systems with
  BMO coefficients*, Arch. Ration. Mech. Anal. 199 (2011), 889–941 (mean oscillation estimates of
  the frozen problem in `L^q`, `q > 1`).
* N. V. Krylov, *Lectures on Elliptic and Parabolic Equations in Sobolev Spaces*, Graduate Studies
  in Mathematics 96, American Mathematical Society, 2008, Chapter 6.
* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Section 6.1 (reduction of a constant-coefficient operator to the Laplacian).
-/

public section

open InnerProductSpace MeasureTheory Metric TopologicalSpace
open scoped ContDiff Distributions Gradient Laplacian Topology

namespace TauCeti

namespace PDE

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {A : Matrix ι ι ℝ}
  {mu : Measure (EuclideanSpace ℝ ι)} [mu.IsAddHaarMeasure]
  {Omega : Opens (EuclideanSpace ℝ ι)} {p : ENNReal} [Fact (1 ≤ p)] {lam Lam : ℝ}

/-- The weak half of Weyl's lemma for `∑ᵢⱼ Aᵢⱼ ∂ᵢ∂ⱼ`: if the linear automorphism `e` turns the
operator into the Laplacian, then for a strong solution `u ∈ W^{2,p}(Ω)` of `∑ᵢⱼ Aᵢⱼ ∂ᵢ∂ⱼu = 0`
the composite `u ∘ e` is weakly harmonic on `e⁻¹(Ω)` for the Haar measure `μ.map e⁻¹`, which `e`
carries to `μ`. -/
private theorem weaklyHarmonicOn_value_comp {e : EuclideanSpace ℝ ι ≃L[ℝ] EuclideanSpace ℝ ι}
    (he : ∀ (v : EuclideanSpace ℝ ι → ℝ) (y : EuclideanSpace ℝ ι), ContDiffAt ℝ 2 v (e y) →
      Δ (v ∘ e) y = ∑ i, ∑ j, A i j •
        fderiv ℝ (fderiv ℝ v) (e y) (EuclideanSpace.single i 1) (EuclideanSpace.single j 1))
    (u : Wkp mu Omega p 2)
    (heq : ∀ᵐ x ∂mu.restrict Omega, ∑ i, ∑ j, A i j *
      ⟪Wkp.iteratedGradient 1 u x (EuclideanSpace.single i 1), EuclideanSpace.single j 1⟫_ℝ = 0) :
    WeaklyHarmonicOn (mu.map e.symm) ⟨e ⁻¹' Omega, Omega.isOpen.preimage e.continuous⟩
      ((Wkp.value 2 u : EuclideanSpace ℝ ι → ℝ) ∘ e) := by
  set f : EuclideanSpace ℝ ι → ℝ := (Wkp.value 2 u : EuclideanSpace ℝ ι → ℝ)
  set Omega' : Opens (EuclideanSpace ℝ ι) := ⟨e ⁻¹' Omega, Omega.isOpen.preimage e.continuous⟩
  have hmaps : Set.MapsTo e Omega' Omega := fun _ hy => hy
  have hmp : MeasurePreserving e (mu.map e.symm) mu := e.measurePreserving_map_symm mu
  have hemb : MeasurableEmbedding e := e.toHomeomorph.measurableEmbedding
  have hf : LocallyIntegrableOn f Omega mu := Wkp.locallyIntegrableOn_value 2 u
  refine weaklyHarmonicOn_iff.2 ⟨?_, fun φ => ?_⟩
  · refine (locallyIntegrableOn_iff Omega'.isOpen.isLocallyClosed).2 fun K hKΩ hK => ?_
    have hK' : IntegrableOn f (e '' K) mu :=
      hf.integrableOn_compact_subset (Set.image_subset_iff.2 hKΩ) (hK.image e.continuous)
    simpa [Set.preimage_image_eq K e.injective] using
      (hmp.integrableOn_comp_preimage hemb (f := f) (s := e '' K)).2 hK'
  set ψ : 𝓓(Omega, ℝ) := ContinuousLinearEquiv.transportTestFunction ℝ e hmaps φ
  have hψe : (ψ : EuclideanSpace ℝ ι → ℝ) ∘ e = φ := funext fun y => by simp [ψ]
  -- `Δφ ∘ e⁻¹` is the operator applied to the test function `ψ = φ ∘ e⁻¹` on `Ω`.
  have hΔ : ∀ x, Δ (φ : EuclideanSpace ℝ ι → ℝ) (e.symm x) =
      ∑ i, ∑ j, A i j • fderiv ℝ (fderiv ℝ (ψ : EuclideanSpace ℝ ι → ℝ)) x
        (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) := fun x => by
    have h := he ψ (e.symm x) (ψ.contDiff.contDiffAt.of_le (by simp))
    rwa [hψe, ContinuousLinearEquiv.apply_symm_apply] at h
  calc ∫ y, Δ (φ : EuclideanSpace ℝ ι → ℝ) y • (f ∘ e) y ∂(mu.map e.symm)
      = ∫ x, Δ (φ : EuclideanSpace ℝ ι → ℝ) (e.symm x) • f x ∂mu := by
        simpa using
          hmp.integral_comp hemb fun x => Δ (φ : EuclideanSpace ℝ ι → ℝ) (e.symm x) • f x
    _ = ∫ x, (ψ : EuclideanSpace ℝ ι → ℝ) x • ∑ i, ∑ j, A i j *
          ⟪Wkp.iteratedGradient 1 u x (EuclideanSpace.single i 1),
            EuclideanSpace.single j 1⟫_ℝ ∂mu := by
        simp_rw [hΔ]
        exact Wkp.integral_sum_smul_fderiv_fderiv_smul_value_eq_sum_mul_inner_iteratedGradient A
          (fun i => EuclideanSpace.single i 1) u ψ
    _ = 0 := by
        rw [← setIntegral_smul_eq_integral_smul]
        exact (integral_congr_ae (g := fun _ => (0 : ℝ))
          (heq.mono fun x hx => by simp [hx])).trans (by simp)

/-- **Strong solutions of constant-coefficient equations are smooth.** Let `A` be a square
matrix with `λ ‖ξ‖² ≤ ξᵀ A ξ`, `0 < λ`, and let `u ∈ W^{2,p}(Ω)` solve
`∑ᵢⱼ Aᵢⱼ ∂ᵢ∂ⱼu = 0` almost everywhere on the open set `Ω`, with `∂ᵢ∂ⱼu = ⟪D²u eᵢ, eⱼ⟫` the entries
of the weak Hessian. Then `u` agrees almost everywhere on `Ω` with a function `g` that is smooth
on `Ω` and solves `∑ᵢⱼ Aᵢⱼ ∂ᵢ∂ⱼg = 0` classically there. This is Weyl's lemma for the operator
`∑ᵢⱼ Aᵢⱼ ∂ᵢ∂ⱼ`, for strong solutions in `W^{2,p}` with any `p ≥ 1`. -/
theorem exists_contDiffOn_ae_eq_and_sum_smul_fderiv_fderiv_eq_zero (hlam : 0 < lam)
    (hA : ∀ ξ : EuclideanSpace ℝ ι, lam * ‖ξ‖ ^ 2 ≤ A.toQuadraticForm' ξ) (u : Wkp mu Omega p 2)
    (heq : ∀ᵐ x ∂mu.restrict Omega, ∑ i, ∑ j, A i j *
      ⟪Wkp.iteratedGradient 1 u x (EuclideanSpace.single i 1), EuclideanSpace.single j 1⟫_ℝ = 0) :
    ∃ g : EuclideanSpace ℝ ι → ℝ, ContDiffOn ℝ ∞ g Omega ∧
      (Wkp.value 2 u : EuclideanSpace ℝ ι → ℝ) =ᵐ[mu.restrict Omega] g ∧
      ∀ x ∈ Omega, ∑ i, ∑ j, A i j •
        fderiv ℝ (fderiv ℝ g) x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) = 0 := by
  -- The operator is the Laplacian in the coordinates given by a linear automorphism `e`; an upper
  -- bound on the quadratic form, which `e` requires, is the norm of the attached bilinear form.
  have hA' := toQuadraticForm'_le_norm_matrixBilinearForm_mul_sq A
  obtain ⟨e, -, -, -, he⟩ := exists_continuousLinearEquiv_laplacian_comp_eq (F := ℝ) hlam hA hA'
  have hmp : MeasurePreserving e (mu.map e.symm) mu := e.measurePreserving_map_symm mu
  have hemb : MeasurableEmbedding e := e.toHomeomorph.measurableEmbedding
  -- Weyl's lemma gives a harmonic `h` with `u ∘ e = h` almost everywhere; then `g = h ∘ e⁻¹`.
  obtain ⟨h, hh, hfh⟩ := (weaklyHarmonicOn_value_comp he u heq).exists_harmonicOnNhd_ae_eq
  -- Name the representative of `u`, so that the measure in its type can be rewritten.
  set f : EuclideanSpace ℝ ι → ℝ := (Wkp.value 2 u : EuclideanSpace ℝ ι → ℝ)
  have hmem : ∀ x ∈ Omega, e.symm x ∈ e ⁻¹' (Omega : Set (EuclideanSpace ℝ ι)) := fun x hx => by
    simpa using hx
  have han : ∀ x ∈ Omega, AnalyticAt ℝ (h ∘ e.symm) x := fun x hx =>
    (hh _ (hmem x hx)).analyticAt.comp
      ((e.symm : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι).analyticAt x)
  refine ⟨h ∘ e.symm, fun x hx => (han x hx).contDiffAt.contDiffWithinAt, ?_, fun x hx => ?_⟩
  · rw [Filter.EventuallyEq, ← (hmp.restrict_preimage_emb hemb Omega).map_eq, hemb.ae_map_iff]
    filter_upwards [hfh] with y hy
    simpa using hy
  · have hcd : ContDiffAt ℝ 2 (h ∘ e.symm) (e (e.symm x)) := by
      rw [ContinuousLinearEquiv.apply_symm_apply]
      exact (han x hx).contDiffAt
    have hΔ := he (h ∘ e.symm) (e.symm x) hcd
    have hcomp : (h ∘ e.symm) ∘ e = h := funext fun y => by simp
    rw [hcomp, ContinuousLinearEquiv.apply_symm_apply, (hh _ (hmem x hx)).2.eq_of_nhds] at hΔ
    exact hΔ.symm

/-- **Decay of the `L¹` mean oscillation of the Hessian for constant coefficients.** Let `A` be a
square matrix with `λ ‖ξ‖² ≤ ξᵀ A ξ ≤ Λ ‖ξ‖²` and `0 < λ`, and let `u ∈ W^{2,p}(Ω)`, `p ≥ 1`,
solve `∑ᵢⱼ Aᵢⱼ ∂ᵢ∂ⱼu = 0` almost everywhere on a ball `B_R = ball x₀ R ⊆ Ω ⊆ ℝⁿ`. Then for every
constant `c` and every `0 ≤ ρ ≤ R`, the weak Hessian `D²u` satisfies

`∫_{B_ρ} ‖D²u - (D²u)_ρ‖ ≤ C (Λ / λ)^((n + 1) / 2) (ρ / R)^(n + 1) ∫_{B_R} ‖D²u - c‖`
with `C = 2^(3n + 5) (n + 1)`,

where `(D²u)_ρ` is the average of `D²u` over `B_ρ`. The constant depends only on `n` and the
ellipticity ratio `Λ / λ`. -/
theorem setIntegral_ball_norm_iteratedGradient_sub_setAverage_le_of_sum_mul_inner_eq_zero
    (hlam : 0 < lam) (hA : ∀ ξ : EuclideanSpace ℝ ι, lam * ‖ξ‖ ^ 2 ≤ A.toQuadraticForm' ξ)
    (hA' : ∀ ξ : EuclideanSpace ℝ ι, A.toQuadraticForm' ξ ≤ Lam * ‖ξ‖ ^ 2) (u : Wkp mu Omega p 2)
    {x₀ : EuclideanSpace ℝ ι} {ρ R : ℝ} (hball : ball x₀ R ⊆ Omega)
    (heq : ∀ᵐ x ∂mu.restrict (ball x₀ R), ∑ i, ∑ j, A i j *
      ⟪Wkp.iteratedGradient 1 u x (EuclideanSpace.single i 1), EuclideanSpace.single j 1⟫_ℝ = 0)
    (c : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι) (hρ : 0 ≤ ρ) (hρR : ρ ≤ R) :
    ∫ x in ball x₀ ρ,
        ‖Wkp.iteratedGradient 1 u x - ⨍ y in ball x₀ ρ, Wkp.iteratedGradient 1 u y ∂mu‖ ∂mu ≤
      2 ^ (3 * Fintype.card ι + 5) * (Fintype.card ι + 1) * √(Lam / lam) ^ (Fintype.card ι + 1) *
        (ρ / R) ^ (Fintype.card ι + 1) *
          ∫ x in ball x₀ R, ‖Wkp.iteratedGradient 1 u x - c‖ ∂mu := by
  -- Restrict `u` to `B_R`, where the equation holds, and take its smooth representative `g`.
  set B : Opens (EuclideanSpace ℝ ι) := ⟨ball x₀ R, isOpen_ball⟩
  have hB : B ≤ Omega := hball
  have hHB : Wkp.iteratedGradient 1 (Wkp.restrictL hB 2 u)
      =ᵐ[mu.restrict (ball x₀ R)] Wkp.iteratedGradient 1 u :=
    Wkp.iteratedGradient_restrictL_ae hB 1 u
  have heqB : ∀ᵐ x ∂mu.restrict (B : Set (EuclideanSpace ℝ ι)), ∑ i, ∑ j, A i j *
      ⟪Wkp.iteratedGradient 1 (Wkp.restrictL hB 2 u) x (EuclideanSpace.single i 1),
        EuclideanSpace.single j 1⟫_ℝ = 0 := by
    filter_upwards [heq, hHB] with x hx h
    rw [h]
    exact hx
  obtain ⟨g, hg, hval, hLg⟩ :=
    exists_contDiffOn_ae_eq_and_sum_smul_fderiv_fderiv_eq_zero hlam hA _ heqB
  have hg2 : ContDiffOn ℝ 2 g (ball x₀ R) := hg.of_le (by simp)
  -- The weak Hessian is the classical Hessian `D²g = D(∇g)` almost everywhere on `B_R`.
  have hU : Wkp.iteratedGradient 1 u =ᵐ[mu.restrict (ball x₀ R)] fderiv ℝ (∇ g) := by
    filter_upwards [Wkp.iteratedGradient_ae_eq_of_contDiffOn 1 _ (hg.of_le (by simp)) hval, hHB]
      with x hx hx'
    rw [← hx', hx, iteratedGradientChain_succ, iteratedGradientChain_zero]
  -- After the change of variables `e`, the Hessian of `g` becomes harmonic: it is the derivative of
  -- the harmonic field `∇g ∘ e`, followed by `e⁻¹`.
  obtain ⟨e, -, hae, hbe, he⟩ := exists_continuousLinearEquiv_laplacian_comp_eq (F := ℝ) hlam hA hA'
  have hW := harmonicOnNhd_gradient_comp_of_sum_smul_fderiv_fderiv_eq_zero he isOpen_ball hg2 hLg
  set M : (EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι) →L[ℝ]
      (EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι) :=
    (ContinuousLinearMap.compL ℝ _ _ _).flip
      (e.symm : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι)
  have hUe : HarmonicOnNhd (fderiv ℝ (∇ g) ∘ e) (e ⁻¹' ball x₀ R) := by
    convert hW.fderiv.comp_CLM M using 1
    funext y
    ext v
    simp [M, e.comp_right_fderiv]
  have : IsFiniteMeasure (mu.restrict (ball x₀ R)) :=
    isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
  have hint : IntegrableOn (fderiv ℝ (∇ g)) (ball x₀ R) mu :=
    (((Lp.memLp (Wkp.iteratedGradient 1 u)).mono_measure
      (Measure.restrict_mono hball le_rfl)).integrable Fact.out).congr hU
  have hdec := setIntegral_ball_norm_sub_setAverage_le_of_harmonicOnNhd_comp e hae hbe
    (by positivity) hUe hint c hρ hρR
  rw [finrank_euclideanSpace, inv_mul_eq_div, ← Real.sqrt_div' _ hlam.le] at hdec
  have hUρ := ae_restrict_of_ae_restrict_of_subset (ball_subset_ball hρR) hU
  rwa [average_congr hUρ, integral_congr_ae (hUρ.mono fun x hx => by rw [hx]),
    integral_congr_ae (hU.mono fun x hx => by rw [hx])]

/-- **Decay of the mean oscillation of the Hessian for constant coefficients, averaged form.**
Under the hypotheses of
`TauCeti.PDE.setIntegral_ball_norm_iteratedGradient_sub_setAverage_le_of_sum_mul_inner_eq_zero`,
for `0 ≤ ρ ≤ R`,

`⨍_{B_ρ} ‖D²u - (D²u)_ρ‖ ≤ C (Λ / λ)^((n + 1) / 2) (ρ / R) ⨍_{B_R} ‖D²u - c‖`
with `C = 2^(3n + 5) (n + 1)`.

This is the scale-invariant form in which the mean oscillation of the frozen problem enters the
sharp function method. -/
theorem setAverage_ball_norm_iteratedGradient_sub_setAverage_le_of_sum_mul_inner_eq_zero
    (hlam : 0 < lam) (hA : ∀ ξ : EuclideanSpace ℝ ι, lam * ‖ξ‖ ^ 2 ≤ A.toQuadraticForm' ξ)
    (hA' : ∀ ξ : EuclideanSpace ℝ ι, A.toQuadraticForm' ξ ≤ Lam * ‖ξ‖ ^ 2) (u : Wkp mu Omega p 2)
    {x₀ : EuclideanSpace ℝ ι} {ρ R : ℝ} (hball : ball x₀ R ⊆ Omega)
    (heq : ∀ᵐ x ∂mu.restrict (ball x₀ R), ∑ i, ∑ j, A i j *
      ⟪Wkp.iteratedGradient 1 u x (EuclideanSpace.single i 1), EuclideanSpace.single j 1⟫_ℝ = 0)
    (c : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι) (hρ : 0 ≤ ρ) (hρR : ρ ≤ R) :
    ⨍ x in ball x₀ ρ,
        ‖Wkp.iteratedGradient 1 u x - ⨍ y in ball x₀ ρ, Wkp.iteratedGradient 1 u y ∂mu‖ ∂mu ≤
      2 ^ (3 * Fintype.card ι + 5) * (Fintype.card ι + 1) * √(Lam / lam) ^ (Fintype.card ι + 1) *
        (ρ / R) * ⨍ x in ball x₀ R, ‖Wkp.iteratedGradient 1 u x - c‖ ∂mu := by
  rcases hρ.eq_or_lt with rfl | hρ
  · simp
  have hR : 0 < R := hρ.trans_le hρR
  have hω : 0 < mu.real (ball (0 : EuclideanSpace ℝ ι) 1) := measureReal_ball_pos mu 0 one_pos
  have h := setIntegral_ball_norm_iteratedGradient_sub_setAverage_le_of_sum_mul_inner_eq_zero
    hlam hA hA' u hball heq c hρ.le hρR
  rw [setAverage_eq (f := fun x => ‖Wkp.iteratedGradient 1 u x -
      ⨍ y in ball x₀ ρ, Wkp.iteratedGradient 1 u y ∂mu‖) mu (ball x₀ ρ),
    setAverage_eq (f := fun x => ‖Wkp.iteratedGradient 1 u x - c‖) mu (ball x₀ R), smul_eq_mul,
    smul_eq_mul, mu.addHaar_real_ball_of_pos x₀ hρ, mu.addHaar_real_ball_of_pos x₀ hR,
    finrank_euclideanSpace]
  generalize Fintype.card ι = n at h ⊢
  calc (ρ ^ n * mu.real (ball 0 1))⁻¹ * ∫ x in ball x₀ ρ,
        ‖Wkp.iteratedGradient 1 u x - ⨍ y in ball x₀ ρ, Wkp.iteratedGradient 1 u y ∂mu‖ ∂mu
      ≤ (ρ ^ n * mu.real (ball 0 1))⁻¹ * (2 ^ (3 * n + 5) * (n + 1) * √(Lam / lam) ^ (n + 1) *
          (ρ / R) ^ (n + 1) * ∫ x in ball x₀ R, ‖Wkp.iteratedGradient 1 u x - c‖ ∂mu) :=
        mul_le_mul_of_nonneg_left h (by positivity)
    _ = _ := by
        simp only [div_pow]
        field_simp
        ring

/-! ### Constant coefficients with forcing, in `Lᵖ` -/

section Forcing

variable {n : ℕ}

/-- The bookkeeping of the comparison argument: if the `L¹` mean oscillation `O` on `B_ρ` is at most
`K t (X + Y) + 2 Z`, where `X, Y` are `L¹` averages on `B_r` and `Z` one on `B_ρ`, and the
`γ`-th powers of `X, Y, Z` are controlled by `L^γ` averages, then `O^γ` is bounded by the averages
of `‖D²u‖^γ` and of `‖F‖^γ`. -/
private theorem rpow_le_of_le_mul_add_add {O X Y Z Hγ Wr Wρ Fγ K C R t γ : ℝ} (hγ : 1 ≤ γ)
    (hO : 0 ≤ O) (hX : 0 ≤ X) (hY : 0 ≤ Y) (hZ : 0 ≤ Z) (hWr : 0 ≤ Wr) (hK : 0 ≤ K)
    (ht : 0 ≤ t) (ht1 : t ≤ 1) (hR : 1 ≤ R) (hOle : O ≤ K * t * (X + Y) + 2 * Z)
    (hXγ : X ^ γ ≤ Hγ) (hYγ : Y ^ γ ≤ Wr) (hZγ : Z ^ γ ≤ Wρ) (hWρ : Wρ ≤ R * Wr)
    (hWF : Wr ≤ C ^ γ * Fγ) :
    O ^ γ ≤ 3 ^ (γ - 1) * K ^ γ * t ^ γ * Hγ + 3 ^ (γ - 1) * (K ^ γ + 2 ^ γ) * C ^ γ * R * Fγ := by
  have hγ0 : 0 ≤ γ := zero_le_one.trans hγ
  have hKt : 0 ≤ K * t := mul_nonneg hK ht
  have htγ : t ^ γ ≤ 1 := Real.rpow_le_one ht ht1 hγ0
  -- `(a + b + c)^γ ≤ 3^(γ - 1) (a^γ + b^γ + c^γ)` for `a, b, c ≥ 0`.
  have h3 : (K * t * X + K * t * Y + 2 * Z) ^ γ ≤
      3 ^ (γ - 1) * ((K * t * X) ^ γ + (K * t * Y) ^ γ + (2 * Z) ^ γ) := by
    have h := Real.rpow_sum_le_const_mul_sum_rpow_of_nonneg (s := Finset.univ)
      (f := ![K * t * X, K * t * Y, 2 * Z]) hγ (fun i _ => by
        fin_cases i <;> simp [mul_nonneg hKt hX, mul_nonneg hKt hY, hZ])
    simpa [Fin.sum_univ_three] using h
  have hpow := (Real.rpow_le_rpow hO (hOle.trans_eq (by ring)) hγ0).trans h3
  rw [Real.mul_rpow hKt hX, Real.mul_rpow hKt hY, Real.mul_rpow zero_le_two hZ,
    Real.mul_rpow hK ht] at hpow
  have hKγ : 0 ≤ K ^ γ := Real.rpow_nonneg hK γ
  have htγ0 : 0 ≤ t ^ γ := Real.rpow_nonneg ht γ
  -- Each of the three terms is bounded separately.
  have e1 : K ^ γ * t ^ γ * X ^ γ ≤ K ^ γ * t ^ γ * Hγ :=
    mul_le_mul_of_nonneg_left hXγ (mul_nonneg hKγ htγ0)
  have e2 : K ^ γ * t ^ γ * Y ^ γ ≤ K ^ γ * R * C ^ γ * Fγ := by
    calc K ^ γ * t ^ γ * Y ^ γ ≤ K ^ γ * 1 * (R * Wr) := by
          gcongr
          exact hYγ.trans (le_mul_of_one_le_left hWr hR)
      _ ≤ K ^ γ * 1 * (R * (C ^ γ * Fγ)) := by gcongr
      _ = _ := by ring
  have e3 : 2 ^ γ * Z ^ γ ≤ 2 ^ γ * R * C ^ γ * Fγ := by
    calc 2 ^ γ * Z ^ γ ≤ 2 ^ γ * (R * (C ^ γ * Fγ)) := by
          gcongr
          exact hZγ.trans (hWρ.trans (mul_le_mul_of_nonneg_left hWF (zero_le_one.trans hR)))
      _ = _ := by ring
  calc O ^ γ ≤ 3 ^ (γ - 1) * (K ^ γ * t ^ γ * X ^ γ + K ^ γ * t ^ γ * Y ^ γ + 2 ^ γ * Z ^ γ) :=
        hpow
    _ ≤ 3 ^ (γ - 1) * (K ^ γ * t ^ γ * Hγ + K ^ γ * R * C ^ γ * Fγ + 2 ^ γ * R * C ^ γ * Fγ) := by
        gcongr
    _ = _ := by ring

/-- The comparison step: if `H = V + W` almost everywhere on `B_r`, all three integrable there, and
the mean oscillation of `V` decays like `⨍_{B_ρ} ‖V - V_ρ‖ ≤ K t ⨍_{B_r} ‖V‖`, then
`⨍_{B_ρ} ‖H - H_ρ‖ ≤ K t (⨍_{B_r} ‖H‖ + ⨍_{B_r} ‖W‖) + 2 ⨍_{B_ρ} ‖W‖`. -/
private theorem setAverage_norm_sub_setAverage_le_of_ae_eq_sub {G : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] [CompleteSpace G] {H V W : EuclideanSpace ℝ (Fin (n + 1)) → G}
    {x₀ : EuclideanSpace ℝ (Fin (n + 1))} {ρ r K t : ℝ} (hρr : ρ ≤ r) (hKt : 0 ≤ K * t)
    (hH : IntegrableOn H (ball x₀ r)) (hW : IntegrableOn W (ball x₀ r))
    (hV : V =ᵐ[volume.restrict (ball x₀ r)] fun x => H x - W x)
    (hdec : ⨍ x in ball x₀ ρ, ‖V x - ⨍ y in ball x₀ ρ, V y‖ ≤ K * t * ⨍ x in ball x₀ r, ‖V x‖) :
    ⨍ x in ball x₀ ρ, ‖H x - ⨍ y in ball x₀ ρ, H y‖ ≤
      K * t * ((⨍ x in ball x₀ r, ‖H x‖) + ⨍ x in ball x₀ r, ‖W x‖) +
        2 * ⨍ x in ball x₀ ρ, ‖W x‖ := by
  have hsub : ball x₀ ρ ⊆ ball x₀ r := ball_subset_ball hρr
  have hVi : IntegrableOn V (ball x₀ r) := (hH.sub hW).congr hV.symm
  have hHρ : H =ᵐ[volume.restrict (ball x₀ ρ)] fun x => V x + W x :=
    ae_restrict_of_ae_restrict_of_subset hsub (hV.mono fun x hx => by
      dsimp only at hx ⊢
      rw [hx, sub_add_cancel])
  -- The oscillation of `H = V + W` on `B_ρ`.
  have hosc : ⨍ x in ball x₀ ρ, ‖H x - ⨍ y in ball x₀ ρ, H y‖ ≤
      (⨍ x in ball x₀ ρ, ‖V x - ⨍ y in ball x₀ ρ, V y‖) + 2 * ⨍ x in ball x₀ ρ, ‖W x‖ := by
    have e1 : ⨍ y in ball x₀ ρ, H y = ⨍ y in ball x₀ ρ, (V y + W y) := average_congr hHρ
    have e2 : ⨍ x in ball x₀ ρ, ‖H x - ⨍ y in ball x₀ ρ, H y‖ =
        ⨍ x in ball x₀ ρ, ‖V x + W x - ⨍ y in ball x₀ ρ, (V y + W y)‖ := by
      rw [e1]
      exact average_congr (hHρ.mono fun x hx => by
        dsimp only at hx ⊢
        rw [hx])
    rw [e2]
    exact setAverage_norm_add_sub_setAverage_le (hVi.mono_set hsub) (hW.mono_set hsub)
  -- The size of `V = H - W` on `B_r`.
  have hVr : ⨍ x in ball x₀ r, ‖V x‖ ≤ (⨍ x in ball x₀ r, ‖H x‖) + ⨍ x in ball x₀ r, ‖W x‖ := by
    have e : ⨍ x in ball x₀ r, ‖V x‖ = ⨍ x in ball x₀ r, ‖H x - W x‖ :=
      average_congr (hV.mono fun x hx => by simp only [hx])
    rw [e, ← average_add hH.norm hW.norm]
    exact average_mono_ae (hH.sub hW).norm (hH.norm.add hW.norm)
      (ae_of_all _ fun x => norm_sub_le (H x) (W x))
  exact hosc.trans (add_le_add_left (hdec.trans (mul_le_mul_of_nonneg_left hVr hKt)) _)

/-- **Comparison with the frozen problem.** Let `A` be elliptic with constants `λ, Λ`, let
`u ∈ W^{2,p}(Ω)` with `B_r = ball x₀ r ⊆ Ω`, and let `w ∈ W^{2,p}(B_r)` satisfy
`∑ᵢⱼ Aᵢⱼ ∂ᵢ∂ⱼw = ∑ᵢⱼ Aᵢⱼ ∂ᵢ∂ⱼu` almost everywhere on `B_r`. Then `u - w` solves the homogeneous
equation, so for `0 < ρ ≤ r`
`⨍_{B_ρ} ‖D²u - (D²u)_ρ‖ ≤ D (ρ / r) (⨍_{B_r} ‖D²u‖ + ⨍_{B_r} ‖D²w‖) + 2 ⨍_{B_ρ} ‖D²w‖`, with
`D = 2^(3(n + 1) + 5) (n + 2) (Λ / λ)^((n + 2) / 2)` the constant of the `L¹` decay. -/
private theorem setAverage_norm_iteratedGradient_sub_setAverage_le_of_contraction_eq
    {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} (hlam : 0 < lam)
    (hAq : ∀ ξ : EuclideanSpace ℝ (Fin (n + 1)), lam * ‖ξ‖ ^ 2 ≤ A.toQuadraticForm' ξ)
    (hA' : ∀ ξ : EuclideanSpace ℝ (Fin (n + 1)), A.toQuadraticForm' ξ ≤ Lam * ‖ξ‖ ^ 2)
    {U : Opens (EuclideanSpace ℝ (Fin (n + 1)))}
    (u : Wkp (volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))) U p 2)
    {x₀ : EuclideanSpace ℝ (Fin (n + 1))} {ρ r : ℝ}
    (w : Wkp (volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))) ⟨ball x₀ r, isOpen_ball⟩ p 2)
    (hρ : 0 < ρ) (hρr : ρ ≤ r) (hball : ball x₀ r ⊆ U)
    (hw : ∀ᵐ x ∂volume.restrict (ball x₀ r), Matrix.contraction A (Wkp.iteratedGradient 1 w x) =
      Matrix.contraction A (Wkp.iteratedGradient 1 u x)) :
    ⨍ x in ball x₀ ρ,
        ‖Wkp.iteratedGradient 1 u x - ⨍ y in ball x₀ ρ, Wkp.iteratedGradient 1 u y‖ ≤
      2 ^ (3 * Fintype.card (Fin (n + 1)) + 5) * (Fintype.card (Fin (n + 1)) + 1) *
          √(Lam / lam) ^ (Fintype.card (Fin (n + 1)) + 1) * (ρ / r) *
        ((⨍ x in ball x₀ r, ‖Wkp.iteratedGradient 1 u x‖) +
          ⨍ x in ball x₀ r, ‖Wkp.iteratedGradient 1 w x‖) +
      2 * ⨍ x in ball x₀ ρ, ‖Wkp.iteratedGradient 1 w x‖ := by
  have : IsFiniteMeasure (volume.restrict (ball x₀ r)) :=
    isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
  have hBU : (⟨ball x₀ r, isOpen_ball⟩ : Opens _) ≤ U := SetLike.coe_subset_coe.1 hball
  set uB := Wkp.restrictL hBU 2 u
  have huB : Wkp.iteratedGradient 1 uB =ᵐ[volume.restrict (ball x₀ r)]
      Wkp.iteratedGradient 1 u := Wkp.iteratedGradient_restrictL_ae _ 1 u
  -- `v = u - w` solves the homogeneous equation on `B_r`, so its mean oscillation decays.
  have hv : ⇑(Wkp.iteratedGradient 1 (uB - w)) =ᵐ[volume.restrict (ball x₀ r)]
      fun x => Wkp.iteratedGradient 1 u x - Wkp.iteratedGradient 1 w x := by
    rw [Wkp.iteratedGradient_sub]
    filter_upwards [Lp.coeFn_sub (Wkp.iteratedGradient 1 uB) (Wkp.iteratedGradient 1 w), huB]
      with x h1 h2
    rw [h1, Pi.sub_apply, h2]
  have heq0 : ∀ᵐ x ∂volume.restrict (ball x₀ r), ∑ i, ∑ j, A i j *
      ⟪Wkp.iteratedGradient 1 (uB - w) x (EuclideanSpace.single i 1),
        EuclideanSpace.single j 1⟫_ℝ = 0 := by
    filter_upwards [hv, hw] with x h1 h2
    rw [← Matrix.contraction_apply, h1, map_sub, h2, sub_self]
  have hdec := setAverage_ball_norm_iteratedGradient_sub_setAverage_le_of_sum_mul_inner_eq_zero
    hlam hAq hA' (uB - w) subset_rfl heq0 0 hρ.le hρr
  simp only [sub_zero] at hdec
  exact setAverage_norm_sub_setAverage_le_of_ae_eq_sub hρr
    (mul_nonneg (by positivity) (div_nonneg hρ.le (hρ.le.trans hρr)))
    (((Lp.memLp (Wkp.iteratedGradient 1 uB)).ae_eq huB).integrable Fact.out)
    ((Lp.memLp (Wkp.iteratedGradient 1 w)).integrable Fact.out) hv hdec

/-- The bounds on the frozen solution: if `w ∈ W^{2,p}(B_r)` has `‖D²w‖_{Lᵖ(B_r)} ≤ C ‖G‖_{Lᵖ(B_r)}`
with `G = F` almost everywhere on `B_r`, then for `0 < ρ ≤ r`
`⨍_{B_ρ} ‖D²w‖^p ≤ (r / ρ)^(n + 1) ⨍_{B_r} ‖D²w‖^p` and `⨍_{B_r} ‖D²w‖^p ≤ C^p ⨍_{B_r} ‖F‖^p`. -/
private theorem setAverage_norm_iteratedGradient_rpow_le_of_norm_le
    {x₀ : EuclideanSpace ℝ (Fin (n + 1))} {ρ r C : ℝ}
    {w : Wkp (volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))) ⟨ball x₀ r, isOpen_ball⟩ p 2}
    {G : Lp ℝ p (volume.restrict (ball x₀ r))} {F : EuclideanSpace ℝ (Fin (n + 1)) → ℝ}
    (hC : 0 ≤ C) (hwG : ‖Wkp.iteratedGradient 1 w‖ ≤ C * ‖G‖)
    (hGF : G =ᵐ[volume.restrict (ball x₀ r)] F) (hρ : 0 < ρ) (hρr : ρ ≤ r) :
    ⨍ x in ball x₀ ρ, ‖Wkp.iteratedGradient 1 w x‖ ^ p.toReal ≤
        (r / ρ) ^ (n + 1) * ⨍ x in ball x₀ r, ‖Wkp.iteratedGradient 1 w x‖ ^ p.toReal ∧
      ⨍ x in ball x₀ r, ‖Wkp.iteratedGradient 1 w x‖ ^ p.toReal ≤
        C ^ p.toReal * ⨍ x in ball x₀ r, ‖F x‖ ^ p.toReal := by
  refine ⟨?_, (Lp.average_norm_rpow_le_of_norm_le hC hwG).trans_eq ?_⟩
  · have : IsFiniteMeasure (volume.restrict (ball x₀ r)) :=
      isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
    simpa only [finrank_euclideanSpace_fin] using setAverage_ball_le hρ (ball_subset_ball hρr)
      (ae_of_all _ fun x => by positivity)
      (Lp.memLp (Wkp.iteratedGradient 1 w)).integrable_norm_rpow'
  · exact congr_arg _ (average_congr (hGF.mono fun x hx => by simp only [hx]))

/-- **Mean oscillation of the Hessian in `L¹` for constant coefficients with forcing.** Let
`1 < p < ∞` and write `γ = p`. There are constants `K₁, K₂`, depending only on `n`, `p`, `λ` and
`Λ`, with the following property. Let `A` be a constant matrix, uniformly elliptic with constants
`λ, Λ` on a ball `B_r = ball x₀ r ⊆ Ω ⊆ ℝ^{n+1}`, and let `u ∈ W^{2,p}(Ω)` solve
`∑ᵢⱼ Aᵢⱼ ∂ᵢ∂ⱼu = F` almost everywhere on `B_r`. Then for `0 < ρ ≤ r`

`(⨍_{B_ρ} ‖D²u - (D²u)_ρ‖)^γ ≤ K₁ (ρ / r)^γ ⨍_{B_r} ‖D²u‖^γ + K₂ (r / ρ)^(n + 1) ⨍_{B_r} |F|^γ`.

The left side is the `γ`-th power of the mean oscillation in `L¹`, which is the form Krylov's sharp
function method consumes (`TauCeti.PDE.exists_eLpNorm_le_of_forall_rpow_setAverage_norm_sub_le`);
for `γ < 2` the solution need not have square integrable second derivatives. -/
theorem exists_rpow_setAverage_norm_iteratedGradient_sub_setAverage_le_of_sum_mul_inner_eq
    (hp : 1 < p) (hp_top : p ≠ ⊤) (lam Lam : ℝ) :
    ∃ K₁ K₂ : ℝ, ∀ {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
      {U : Opens (EuclideanSpace ℝ (Fin (n + 1)))}
      (u : Wkp (volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))) U p 2)
      {F : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} {x₀ : EuclideanSpace ℝ (Fin (n + 1))} {ρ r : ℝ},
      UniformlyEllipticOn (ball x₀ r) (fun _ => A) lam Lam → ball x₀ r ⊆ U →
      (∀ᵐ x ∂volume.restrict (ball x₀ r), ∑ i, ∑ j, A i j *
        ⟪Wkp.iteratedGradient 1 u x (EuclideanSpace.single i 1), EuclideanSpace.single j 1⟫_ℝ =
          F x) →
      0 < ρ → ρ ≤ r →
      (⨍ x in ball x₀ ρ,
          ‖Wkp.iteratedGradient 1 u x - ⨍ y in ball x₀ ρ, Wkp.iteratedGradient 1 u y‖) ^
            p.toReal ≤
        K₁ * (ρ / r) ^ p.toReal * (⨍ x in ball x₀ r, ‖Wkp.iteratedGradient 1 u x‖ ^ p.toReal) +
          K₂ * (r / ρ) ^ (n + 1) * ⨍ x in ball x₀ r, ‖F x‖ ^ p.toReal := by
  have hγ : 1 < p.toReal := by
    rw [← ENNReal.toReal_one]
    exact (ENNReal.toReal_lt_toReal ENNReal.one_ne_top hp_top).2 hp
  rcases le_or_gt lam 0 with hlam | hlam
  · exact ⟨0, 0, fun {_ _} _ {_ _ _ _} hA => absurd hA.pos (not_lt.2 hlam)⟩
  obtain ⟨CD, hCD⟩ :=
    exists_firstOrder_mem_w1p0Submodule_and_contraction_iteratedGradient_eq_and_norm_le (n := n)
      hp hp_top hlam Lam
  set C := max CD 0
  set Kd : ℝ := 2 ^ (3 * Fintype.card (Fin (n + 1)) + 5) * (Fintype.card (Fin (n + 1)) + 1) *
    √(Lam / lam) ^ (Fintype.card (Fin (n + 1)) + 1)
  refine ⟨3 ^ (p.toReal - 1) * Kd ^ p.toReal, 3 ^ (p.toReal - 1) * (Kd ^ p.toReal + 2 ^ p.toReal) *
    C ^ p.toReal, fun {A U} u {F x₀ ρ r} hA hball heq hρ hρr => ?_⟩
  have hr : 0 < r := hρ.trans_le hρr
  have hAq : ∀ ξ : EuclideanSpace ℝ (Fin (n + 1)), lam * ‖ξ‖ ^ 2 ≤ A.toQuadraticForm' ξ :=
    ((uniformlyEllipticOn_iff.1 hA).2.2 (mem_ball_self hr)).1
  have hAΛ : ‖matrixBilinearForm A‖ ≤ Lam := hA.opNorm_matrixBilinearForm_le (mem_ball_self hr)
  have : IsFiniteMeasure (volume.restrict (ball x₀ r)) :=
    isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
  set H := ⇑(Wkp.iteratedGradient 1 u)
  have hHp : MemLp H p (volume.restrict (ball x₀ r)) :=
    (Lp.memLp (Wkp.iteratedGradient 1 u)).mono_measure (Measure.restrict_mono hball le_rfl)
  -- The frozen problem: `w ∈ W^{2,p}(B_r)` with `∑ Aᵢⱼ ∂ᵢ∂ⱼw = ∑ Aᵢⱼ ∂ᵢ∂ⱼu`, and `‖D²w‖ ≤ C ‖F‖`.
  have hFp : MemLp (fun x => Matrix.contraction A (H x)) p (volume.restrict (ball x₀ r)) :=
    (Matrix.contraction A).comp_memLp' hHp
  obtain ⟨w, -, hw, hwn⟩ := hCD A hAq hAΛ x₀ r hr ⟨ball x₀ r, isOpen_ball⟩ rfl (hFp.toLp _)
  set W := ⇑(Wkp.iteratedGradient 1 w)
  have hA' : ∀ ξ : EuclideanSpace ℝ (Fin (n + 1)), A.toQuadraticForm' ξ ≤ Lam * ‖ξ‖ ^ 2 :=
    fun ξ => (toQuadraticForm'_le_norm_matrixBilinearForm_mul_sq A ξ).trans (by gcongr)
  have hcomp := setAverage_norm_iteratedGradient_sub_setAverage_le_of_contraction_eq hlam hAq
    hA' u w hρ hρr hball (by filter_upwards [hw, hFp.coeFn_toLp] with x h1 h2; rw [h1, h2])
  have hWγ : IntegrableOn (fun x => ‖W x‖ ^ p.toReal) (ball x₀ r) :=
    (Lp.memLp (Wkp.iteratedGradient 1 w)).integrable_norm_rpow'
  obtain ⟨hWρ, hWF⟩ := setAverage_norm_iteratedGradient_rpow_le_of_norm_le (le_max_right CD 0)
    (hwn.trans (mul_le_mul_of_nonneg_right (le_max_left CD 0) (norm_nonneg _)))
    (by filter_upwards [hFp.coeFn_toLp, heq] with x h1 h2; rw [h1, Matrix.contraction_apply, h2])
    hρ hρr
  refine (rpow_le_of_le_mul_add_add hγ.le (average_nonneg fun x => norm_nonneg _)
    (average_nonneg fun x => norm_nonneg _) (average_nonneg fun x => norm_nonneg _)
    (average_nonneg fun x => norm_nonneg _) (average_nonneg fun x => by positivity)
    (by positivity) (by positivity) (div_le_one hr |>.2 hρr)
    (one_le_pow₀ ((one_le_div hρ).2 hρr)) hcomp
    (rpow_setAverage_norm_le_setAverage_norm_rpow hγ.le hHp.integrable_norm_rpow')
    (rpow_setAverage_norm_le_setAverage_norm_rpow hγ.le hWγ)
    (rpow_setAverage_norm_le_setAverage_norm_rpow hγ.le (hWγ.mono_set (ball_subset_ball hρr)))
    hWρ hWF).trans_eq ?_
  ring

end Forcing

end PDE

end TauCeti
