/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Harmonic.Decay
public import TauCeti.Analysis.Sobolev.Wkp.Basic
public import Mathlib.LinearAlgebra.QuadraticForm.Basic
import TauCeti.Analysis.Distribution.TestFunction.LinearEquiv
import TauCeti.Analysis.InnerProductSpace.Harmonic.Analytic
import TauCeti.Analysis.InnerProductSpace.Harmonic.Deriv
import TauCeti.Analysis.InnerProductSpace.Harmonic.Weyl
import TauCeti.Analysis.PDE.Ellipticity.Basic
import TauCeti.Analysis.PDE.Ellipticity.ConstantCoefficient
import TauCeti.Analysis.Sobolev.Wkp.Classical
import TauCeti.Analysis.Sobolev.Wkp.Laplacian
import TauCeti.Analysis.Sobolev.Wkp.Restriction
import TauCeti.MeasureTheory.Measure.Haar.Average
import TauCeti.MeasureTheory.Measure.Haar.NormedSpace

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
only the `L¹` norm. The mean oscillation also decays in every `L^γ`, `γ ≥ 1`: if `‖D²u - c‖^γ` is
integrable on `B_R`, then for `0 < ρ ≤ R`

`⨍_{B_ρ} ‖D²u - (D²u)_ρ‖^γ ≤ (C (Λ / λ)^((n + 1) / 2) (ρ / R))^γ ⨍_{B_R} ‖D²u - c‖^γ`

with the same `C` (in the `TauCeti.PDE` namespace,
`setAverage_ball_norm_iteratedGradient_sub_setAverage_rpow_le_of_sum_mul_inner_eq_zero`). This is
the decay of the frozen problem in Krylov's sharp function method with mean oscillation
in `L^γ` (`TauCeti.PDE.exists_eLpNorm_le_of_forall_setAverage_norm_sub_rpow_le`), which reaches the
`W^{2,q}` theory with coefficients of vanishing mean oscillation in the range `γ < q ≤ 2`, where
the solutions need not have square integrable second derivatives and the `L²` decay
(`TauCeti.PDE.setIntegral_ball_norm_iteratedGradient_sub_setAverage_sq_le_add_of_sum_mul_inner_eq`)
does not apply.

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
  (`InnerProductSpace.HarmonicOnNhd.fderiv`), and the `L^γ` decay of harmonic
  functions after a linear change of variables
  (`TauCeti.setAverage_ball_norm_sub_setAverage_rpow_le_of_harmonicOnNhd_comp`), which follows
  from the pointwise oscillation bound `TauCeti.norm_sub_le_of_harmonicOnNhd_comp`, applies with
  `‖e⁻¹‖ ≤ λ^(-1/2)` and `‖e‖ ≤ Λ^(1/2)`.
  The two `L¹` forms are its case `γ = 1`.

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

/-- The reduction of the Hessian decay to harmonic functions. Let `A` be a square matrix with
`λ ‖ξ‖² ≤ ξᵀ A ξ ≤ Λ ‖ξ‖²` and `0 < λ`, and let `u ∈ W^{2,p}(Ω)` solve `∑ᵢⱼ Aᵢⱼ ∂ᵢ∂ⱼu = 0` almost
everywhere on a ball `B_R = ball x₀ R ⊆ Ω`. Then the weak Hessian `D²u` agrees almost everywhere on
`B_R` with the classical Hessian `D²g = D(∇g)` of a function `g`; it is integrable on `B_R`, and it
becomes harmonic after a linear change of variables `e` with `‖e⁻¹ x‖ ≤ λ^(-1/2) ‖x‖` and
`‖e y‖ ≤ Λ^(1/2) ‖y‖`. -/
private theorem exists_iteratedGradient_ae_eq_and_harmonicOnNhd_comp
    (hlam : 0 < lam) (hA : ∀ ξ : EuclideanSpace ℝ ι, lam * ‖ξ‖ ^ 2 ≤ A.toQuadraticForm' ξ)
    (hA' : ∀ ξ : EuclideanSpace ℝ ι, A.toQuadraticForm' ξ ≤ Lam * ‖ξ‖ ^ 2) (u : Wkp mu Omega p 2)
    {x₀ : EuclideanSpace ℝ ι} {R : ℝ} (hball : ball x₀ R ⊆ Omega)
    (heq : ∀ᵐ x ∂mu.restrict (ball x₀ R), ∑ i, ∑ j, A i j *
      ⟪Wkp.iteratedGradient 1 u x (EuclideanSpace.single i 1), EuclideanSpace.single j 1⟫_ℝ = 0) :
    ∃ (g : EuclideanSpace ℝ ι → ℝ) (e : EuclideanSpace ℝ ι ≃L[ℝ] EuclideanSpace ℝ ι),
      (∀ x, ‖e.symm x‖ ≤ (√lam)⁻¹ * ‖x‖) ∧ (∀ y, ‖e y‖ ≤ √Lam * ‖y‖) ∧
      Wkp.iteratedGradient 1 u =ᵐ[mu.restrict (ball x₀ R)] fderiv ℝ (∇ g) ∧
      HarmonicOnNhd (fderiv ℝ (∇ g) ∘ e) (e ⁻¹' ball x₀ R) ∧
      IntegrableOn (fderiv ℝ (∇ g)) (ball x₀ R) mu := by
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
  exact ⟨g, e, hae, hbe, hU, hUe, (((Lp.memLp (Wkp.iteratedGradient 1 u)).mono_measure
    (Measure.restrict_mono hball le_rfl)).integrable Fact.out).congr hU⟩

/-- **Decay of the `L^γ` mean oscillation of the Hessian for constant coefficients.** Let `A` be a
square matrix with `λ ‖ξ‖² ≤ ξᵀ A ξ ≤ Λ ‖ξ‖²` and `0 < λ`, and let `u ∈ W^{2,p}(Ω)`, `p ≥ 1`,
solve `∑ᵢⱼ Aᵢⱼ ∂ᵢ∂ⱼu = 0` almost everywhere on a ball `B_R = ball x₀ R ⊆ Ω ⊆ ℝⁿ`. Let `γ ≥ 1` and
let `c` be a constant for which `‖D²u - c‖^γ` is integrable on `B_R`. Then for every
`0 < ρ ≤ R` the weak Hessian `D²u` satisfies

`⨍_{B_ρ} ‖D²u - (D²u)_ρ‖^γ ≤ (C (Λ / λ)^((n + 1) / 2) (ρ / R))^γ ⨍_{B_R} ‖D²u - c‖^γ`
with `C = 2^(3n + 5) (n + 1)`,

where `(D²u)_ρ` is the average of `D²u` over `B_ρ`. The constant depends only on `n`, `γ` and the
ellipticity ratio `Λ / λ`. This is the decay of the frozen homogeneous problem in mean
oscillation estimates in `L^γ`; for `γ = 1` it is
`TauCeti.PDE.setAverage_ball_norm_iteratedGradient_sub_setAverage_le_of_sum_mul_inner_eq_zero`. -/
theorem setAverage_ball_norm_iteratedGradient_sub_setAverage_rpow_le_of_sum_mul_inner_eq_zero
    (hlam : 0 < lam) (hA : ∀ ξ : EuclideanSpace ℝ ι, lam * ‖ξ‖ ^ 2 ≤ A.toQuadraticForm' ξ)
    (hA' : ∀ ξ : EuclideanSpace ℝ ι, A.toQuadraticForm' ξ ≤ Lam * ‖ξ‖ ^ 2) (u : Wkp mu Omega p 2)
    {x₀ : EuclideanSpace ℝ ι} {ρ R γ : ℝ} (hball : ball x₀ R ⊆ Omega)
    (heq : ∀ᵐ x ∂mu.restrict (ball x₀ R), ∑ i, ∑ j, A i j *
      ⟪Wkp.iteratedGradient 1 u x (EuclideanSpace.single i 1), EuclideanSpace.single j 1⟫_ℝ = 0)
    (c : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι) (hγ : 1 ≤ γ)
    (hint : IntegrableOn (fun x => ‖Wkp.iteratedGradient 1 u x - c‖ ^ γ) (ball x₀ R) mu)
    (hρ : 0 < ρ) (hρR : ρ ≤ R) :
    ⨍ x in ball x₀ ρ,
        ‖Wkp.iteratedGradient 1 u x - ⨍ y in ball x₀ ρ, Wkp.iteratedGradient 1 u y ∂mu‖ ^ γ ∂mu ≤
      (2 ^ (3 * Fintype.card ι + 5) * (Fintype.card ι + 1) *
        √(Lam / lam) ^ (Fintype.card ι + 1) * (ρ / R)) ^ γ *
          ⨍ x in ball x₀ R, ‖Wkp.iteratedGradient 1 u x - c‖ ^ γ ∂mu := by
  obtain ⟨g, e, hae, hbe, hU, hUe, hi⟩ :=
    exists_iteratedGradient_ae_eq_and_harmonicOnNhd_comp hlam hA hA' u hball heq
  have hic : IntegrableOn (fun x => ‖fderiv ℝ (∇ g) x - c‖ ^ γ) (ball x₀ R) mu :=
    hint.congr (hU.mono fun x hx => by simp only [hx])
  have hdec := setAverage_ball_norm_sub_setAverage_rpow_le_of_harmonicOnNhd_comp e hae hbe
    (by positivity) hUe hi c hic hγ hρ hρR
  rw [finrank_euclideanSpace, inv_mul_eq_div, ← Real.sqrt_div' _ hlam.le] at hdec
  have hUρ := ae_restrict_of_ae_restrict_of_subset (ball_subset_ball hρR) hU
  rwa [average_congr hUρ, average_congr (hUρ.mono fun x hx => by rw [hx]),
    average_congr (hU.mono fun x hx => by rw [hx])]

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
  -- This is the `L^γ` decay at `γ = 1`, where `‖D²u - c‖` is integrable since `D²u ∈ L^p`.
  have : IsFiniteMeasure (mu.restrict (ball x₀ R)) :=
    isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
  have hint :
      IntegrableOn (fun x => ‖Wkp.iteratedGradient 1 u x - c‖ ^ (1 : ℝ)) (ball x₀ R) mu := by
    simp only [Real.rpow_one]
    exact ((((Lp.memLp (Wkp.iteratedGradient 1 u)).mono_measure
      (Measure.restrict_mono hball le_rfl)).integrable Fact.out).sub (integrable_const c)).norm
  simpa only [Real.rpow_one] using
    setAverage_ball_norm_iteratedGradient_sub_setAverage_rpow_le_of_sum_mul_inner_eq_zero hlam hA
      hA' u hball heq c le_rfl hint hρ hρR

/-- **Decay of the `L¹` mean oscillation of the Hessian for constant coefficients.** Let `A` be a
square matrix with `λ ‖ξ‖² ≤ ξᵀ A ξ ≤ Λ ‖ξ‖²` and `0 < λ`, and let `u ∈ W^{2,p}(Ω)`, `p ≥ 1`,
solve `∑ᵢⱼ Aᵢⱼ ∂ᵢ∂ⱼu = 0` almost everywhere on a ball `B_R = ball x₀ R ⊆ Ω ⊆ ℝⁿ`. Then for every
constant `c` and every `0 ≤ ρ ≤ R`, the weak Hessian `D²u` satisfies

`∫_{B_ρ} ‖D²u - (D²u)_ρ‖ ≤ C (Λ / λ)^((n + 1) / 2) (ρ / R)^(n + 1) ∫_{B_R} ‖D²u - c‖`
with `C = 2^(3n + 5) (n + 1)`,

where `(D²u)_ρ` is the average of `D²u` over `B_ρ`. The constant depends only on `n` and the
ellipticity ratio `Λ / λ`. This is the averaged form
`TauCeti.PDE.setAverage_ball_norm_iteratedGradient_sub_setAverage_le_of_sum_mul_inner_eq_zero`
multiplied by the volume of `B_ρ`. -/
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
  rcases hρ.eq_or_lt with rfl | hρ
  · simp
  -- This is the averaged form multiplied by the volume of `B_ρ`.
  have h := setAverage_ball_norm_iteratedGradient_sub_setAverage_le_of_sum_mul_inner_eq_zero
    hlam hA hA' u hball heq c hρ.le hρR
  refine (setIntegral_ball_le_of_setAverage_le hρ (hρ.trans_le hρR) h).trans_eq ?_
  rw [finrank_euclideanSpace]
  ring

end PDE

end TauCeti
