/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Harmonic.Decay
public import TauCeti.Analysis.Sobolev.Wkp.Basic
public import Mathlib.LinearAlgebra.QuadraticForm.Basic
import TauCeti.Analysis.Calculus.FDeriv.ContinuousLinearMap
import TauCeti.Analysis.Distribution.TestFunction.LineDeriv
import TauCeti.Analysis.Distribution.TestFunction.LinearEquiv
import TauCeti.Analysis.InnerProductSpace.Harmonic.Analytic
import TauCeti.Analysis.InnerProductSpace.Harmonic.Deriv
import TauCeti.Analysis.InnerProductSpace.Harmonic.Weyl
import TauCeti.Analysis.PDE.Ellipticity.Basic
import TauCeti.Analysis.PDE.Ellipticity.ConstantCoefficient
import TauCeti.Analysis.Sobolev.Wkp.Classical
import TauCeti.Analysis.Sobolev.Wkp.Laplacian
import TauCeti.Analysis.Sobolev.Wkp.Restriction
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

## The argument

Only the symmetric part of `A` enters, and a linear change of variables `e` with
`Δ (φ ∘ e) = (∑ᵢⱼ Aᵢⱼ ∂ᵢ∂ⱼφ) ∘ e` for smooth `φ`
(`TauCeti.PDE.exists_continuousLinearEquiv_laplacian_comp_eq`) turns the operator into the
Laplacian.

* **Weyl's lemma.** For a test function `φ` on `e⁻¹(Ω)`, the test function `ψ = φ ∘ e⁻¹` on `Ω`
  has `Δφ ∘ e⁻¹ = ∑ᵢⱼ Aᵢⱼ ∂ᵢ∂ⱼψ`, and integrating by parts twice
  (`TauCeti.Wkp.integral_fderiv_fderiv_smul_value_eq_inner_iteratedGradient`) gives
  `∫ Δφ (u ∘ e) d(μ.map e⁻¹) = ∫ ψ ∑ᵢⱼ Aᵢⱼ ∂ᵢ∂ⱼu dμ = 0`; the Haar measure `μ.map e⁻¹`, which `e`
  carries to `μ`, avoids the Jacobian of `e`. So `u ∘ e` is weakly harmonic, hence harmonic up to
  a null set (`TauCeti.WeaklyHarmonicOn.exists_harmonicOnNhd_ae_eq`).
* **Decay.** The weak Hessian of `u` is then the classical Hessian `D²g` almost everywhere
  (`TauCeti.Wkp.iteratedGradient_ae_eq_of_contDiffOn`). Its composite with `e` is the derivative
  of the harmonic field `∇g ∘ e` followed by `e⁻¹`, so it is harmonic
  (`InnerProductSpace.HarmonicOnNhd.harmonicOnNhd_fderiv`), and the `L¹` decay of harmonic
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

/-- The distributional action of the constant-coefficient operator `∑ᵢⱼ Aᵢⱼ ∂ᵢ∂ⱼ` on
`u ∈ W^{2,p}(Ω)` is its strong form: `∫ (∑ᵢⱼ Aᵢⱼ ∂ᵢ∂ⱼψ) u = ∫ ψ ∑ᵢⱼ Aᵢⱼ ⟪D²u eᵢ, eⱼ⟫` for every
test function `ψ` on `Ω`. -/
private theorem integral_sum_smul_fderiv_fderiv_smul_value_eq (u : Wkp mu Omega p 2)
    (ψ : 𝓓(Omega, ℝ)) :
    ∫ x, (∑ i, ∑ j, A i j • fderiv ℝ (fderiv ℝ (ψ : EuclideanSpace ℝ ι → ℝ)) x
        (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) • Wkp.value 2 u x ∂mu =
      ∫ x, (ψ : EuclideanSpace ℝ ι → ℝ) x • ∑ i, ∑ j, A i j *
        ⟪Wkp.iteratedGradient 1 u x (EuclideanSpace.single i 1),
          EuclideanSpace.single j 1⟫_ℝ ∂mu := by
  set e : ι → EuclideanSpace ℝ ι := fun i => EuclideanSpace.single i 1
  -- The second derivatives of `ψ` are test functions, so their products with `u` are integrable.
  set ψ₂ : ι → ι → 𝓓(Omega, ℝ) := fun i j =>
    TestFunction.lineDerivCLM ℝ (e i) (TestFunction.lineDerivCLM ℝ (e j) ψ)
  have hψ₂ : ∀ i j x, ψ₂ i j x = fderiv ℝ (fderiv ℝ (ψ : EuclideanSpace ℝ ι → ℝ)) x (e i) (e j) :=
    fun i j x => by
      have hd : DifferentiableAt ℝ (fderiv ℝ (ψ : EuclideanSpace ℝ ι → ℝ)) x :=
        (ψ.contDiff.fderiv_right (m := 1) (by simp)).differentiable (by simp) x
      rw [TestFunction.coe_lineDerivCLM, TestFunction.coe_lineDerivCLM]
      dsimp only
      rw [TestFunction.lineDeriv_lineDeriv_eq_fderiv_fderiv, fderiv_clm_apply_const_apply hd]
  have hval : LocallyIntegrableOn (Wkp.value 2 u : EuclideanSpace ℝ ι → ℝ) Omega mu :=
    Wkp.locallyIntegrableOn_value 2 u
  have hH : ∀ i j, LocallyIntegrableOn
      (fun x => ⟪Wkp.iteratedGradient 1 u x (e i), e j⟫_ℝ) Omega mu := fun i j => by
    simpa only [ContinuousLinearMap.comp_apply, innerSL_apply_apply, real_inner_comm (e j)] using
      (((Wkp.hasWeakFDerivOn_iteratedGradient 0 u).clm_comp (innerSL ℝ (e j))).hasWeakLineDerivOn
        (e i)).locallyIntegrableOn_deriv
  -- Exchange the finite sums with the integrals on both sides.
  have hsum : ∀ (F : ι → ι → EuclideanSpace ℝ ι → ℝ), (∀ i j, Integrable (F i j) mu) →
      ∫ x, ∑ i, ∑ j, A i j * F i j x ∂mu = ∑ i, ∑ j, A i j * ∫ x, F i j x ∂mu := fun F hF =>
    (integral_finsetSum (f := fun i x => ∑ j, A i j * F i j x) Finset.univ fun i _ =>
      integrable_finsetSum _ fun j _ => (hF i j).const_mul (A i j)).trans
      (Finset.sum_congr rfl fun i _ =>
        (integral_finsetSum (f := fun j x => A i j * F i j x) Finset.univ fun j _ =>
          (hF i j).const_mul (A i j)).trans
          (Finset.sum_congr rfl fun j _ => integral_const_mul _ _))
  calc ∫ x, (∑ i, ∑ j, A i j • fderiv ℝ (fderiv ℝ (ψ : EuclideanSpace ℝ ι → ℝ)) x (e i) (e j)) •
          Wkp.value 2 u x ∂mu
      = ∫ x, ∑ i, ∑ j, A i j * (ψ₂ i j x * Wkp.value 2 u x) ∂mu := by
        refine integral_congr_ae (ae_of_all _ fun x => ?_)
        simp only [hψ₂, smul_eq_mul, Finset.sum_mul, mul_assoc]
    _ = ∑ i, ∑ j, A i j * ∫ x, ψ₂ i j x * Wkp.value 2 u x ∂mu :=
        hsum _ fun i j => (ψ₂ i j).integrable_smul hval
    _ = ∑ i, ∑ j, A i j * ∫ x, (ψ : EuclideanSpace ℝ ι → ℝ) x *
          ⟪Wkp.iteratedGradient 1 u x (e i), e j⟫_ℝ ∂mu := by
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        simp only [hψ₂]
        exact congrArg (A i j * ·)
          (Wkp.integral_fderiv_fderiv_smul_value_eq_inner_iteratedGradient u ψ (e i) (e j))
    _ = _ := by
        refine (hsum (fun i j x => (ψ : EuclideanSpace ℝ ι → ℝ) x *
            ⟪Wkp.iteratedGradient 1 u x (e i), e j⟫_ℝ)
          fun i j => ψ.integrable_smul (hH i j)).symm.trans
          (integral_congr_ae (ae_of_all _ fun x => ?_))
        simp only [smul_eq_mul, Finset.mul_sum, e]
        exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

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
  have hmp : MeasurePreserving e (mu.map e.symm) mu := by
    simpa using e.symm.toHomeomorph.toMeasurableEquiv.measurePreserving_symm mu
  have hemb : MeasurableEmbedding e := e.toHomeomorph.measurableEmbedding
  have hf : LocallyIntegrableOn f Omega mu := Wkp.locallyIntegrableOn_value 2 u
  refine weaklyHarmonicOn_iff.2 ⟨?_, fun φ => ?_⟩
  · refine (locallyIntegrableOn_iff Omega'.isOpen.isLocallyClosed).2 fun K hKΩ hK => ?_
    have hK' : IntegrableOn f (e '' K) mu :=
      hf.integrableOn_compact_subset (Set.image_subset_iff.2 hKΩ) (hK.image e.continuous)
    simpa [Set.preimage_image_eq K e.injective] using
      (hmp.integrableOn_comp_preimage hemb (f := f) (s := e '' K)).2 hK'
  set ψ : 𝓓(Omega, ℝ) := ContinuousLinearEquiv.transportTestFunction e hmaps φ
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
        exact integral_sum_smul_fderiv_fderiv_smul_value_eq u ψ
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
  have hA' : ∀ ξ : EuclideanSpace ℝ ι,
      A.toQuadraticForm' ξ ≤ ‖matrixBilinearForm A‖ * ‖ξ‖ ^ 2 := fun ξ =>
    (le_abs_self _).trans (abs_toQuadraticForm'_le_of_abs_dotProduct_mulVec_le (fun η ζ => by
      rw [← matrixBilinearForm_apply, ← Real.norm_eq_abs]
      exact (matrixBilinearForm A).le_opNorm₂ η ζ) ξ)
  obtain ⟨e, -, -, -, he⟩ := exists_continuousLinearEquiv_laplacian_comp_eq (F := ℝ) hlam hA hA'
  have hmp : MeasurePreserving e (mu.map e.symm) mu := by
    simpa using e.symm.toHomeomorph.toMeasurableEquiv.measurePreserving_symm mu
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
    convert hW.harmonicOnNhd_fderiv.comp_CLM M using 1
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

end PDE

end TauCeti
