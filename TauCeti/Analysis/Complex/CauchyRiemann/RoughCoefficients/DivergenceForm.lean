/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Laplacian
public import TauCeti.Analysis.Complex.CauchyRiemann.RoughCoefficients.Weak
import TauCeti.Analysis.Distribution.TestFunction.Inner
import TauCeti.Analysis.Distribution.TestFunction.LineDeriv
import TauCeti.Analysis.Sobolev.WeakDeriv.ChainRule
import TauCeti.MeasureTheory.Function.Holder
import TauCeti.Topology.UniformSpace.UniformConvergence.ENorm
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.MeasureTheory.Function.L2Space

/-!
# The weak Cauchy–Riemann equation in divergence form

Let `Ω ⊆ ℂ` be open, write `z = s + i t`, and let `V` be a real Hilbert space. Let `ξ` be a weak
solution of `∂_s ξ + J ∂_t ξ + S ξ = η` on `Ω` (`TauCeti.IsWeakCRSolution q Ω J DJ S ξ η`), where
`J` is continuous with `J² = -1`, `DJ` is a weak derivative of `J`, and `J`, `DJ`, `S` are locally
`Lᵖ` for some finite `p` with `1/p + 1/q ≤ 1`. This file proves that `ξ` solves, in the sense of
distributions, the Poisson equation in divergence form

`Δ ξ = ∂_s f + ∂_t g`, with `f = η - S ξ + (∂_t J) ξ` and `g = -J (η - S ξ) - (∂_s J) ξ`,

where `∂_s J = DJ · 1` and `∂_t J = DJ · I`. These are `TauCeti.crDivergenceFst` and
`TauCeti.crDivergenceSnd`. This is the rewriting step in the proof of McDuff–Salamon's
Lemma B.4.6: for smooth data it follows by applying `∂_s - J ∂_t` to the equation and using
`J² = -1`, and the second derivatives of `J` cancel.

For rough `J` the proof tests the weak equation against `ψ = ∂_s Φ - Jᵀ ∂_t Φ`. Its formal
adjoint is `-Δ Φ` plus terms of order at most one in `Φ`, using `Jᵀ Jᵀ = -1`; the term
`((∂_t J) J + J (∂_t J))ᵀ ∂_t Φ` vanishes because `(∂ J) J + J (∂ J) = 0` is the weak derivative
of `J² = -1` (`TauCeti.HasWeakFDerivOn.ae_deriv_comp_add_comp_deriv_eq_zero`). Since `ψ` is not
smooth, `Jᵀ` is replaced by smooth approximations converging uniformly near the support of `Φ`,
with derivatives converging in `Lᵖ`
(`TauCeti.HasWeakFDerivOn.exists_contDiff_tendsto_of_continuousOn`), and the identity passes to
the limit.

## Main results

* `TauCeti.IsWeakCRSolution.integral_inner_laplacian_eq`: for every test function
  `Φ ∈ 𝓓(Ω, V)`, `∫ ⟪Δ Φ, ξ⟫ = -∫ (⟪∂_s Φ, f⟫ + ⟪∂_t Φ, g⟫)`.
* `TauCeti.IsWeakCRSolution.integral_laplacian_smul_eq`: the same identity for real test
  functions `φ ∈ 𝓓(Ω, ℝ)`, `∫ Δ φ • ξ = -∫ (∂_s φ • f + ∂_t φ • g)`, in the form consumed by
  the divergence-form Laplace regularity
  `TauCeti.memWkpLoc_one_of_forall_integral_laplacian_smul_eq` and by the `Lʳ_loc`-plus-harmonic
  decomposition `TauCeti.exists_memLpLoc_weaklyHarmonicOn_sub_of_integral_laplacian_smul_eq`.
* `TauCeti.IsSobolevCRCoefficients.memLpLoc_crDivergenceFst` and
  `TauCeti.IsSobolevCRCoefficients.memLpLoc_crDivergenceSnd`: if `ξ` is locally `L^q` and `η`
  is locally `Lʳ` with `1/p + 1/q ≤ 1/r`, then `f` and `g` are locally `Lʳ`; for `r = 1` these
  are `TauCeti.IsSobolevCRCoefficients.locallyIntegrableOn_crDivergenceFst` and
  `TauCeti.IsSobolevCRCoefficients.locallyIntegrableOn_crDivergenceSnd`.

For the standard structure `J = i` and `S = 0` on `V = ℂ`, the data are `f = η` and `g = -i η`
(`TauCeti.crDivergenceFst_zero_zero`, `TauCeti.crDivergenceSnd_mul_I_zero_zero`).

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix B.4 (Lemma B.4.6).
-/

public noncomputable section

open MeasureTheory TopologicalSpace Complex Filter Set
open scoped InnerProductSpace ContDiff Distributions ENNReal Topology Laplacian

namespace TauCeti

variable {V : Type*} [NormedAddCommGroup V] {Ω : Opens ℂ} {p q r : ℝ≥0∞}

/-! ### The divergence-form data -/

section Data

variable [NormedSpace ℝ V] {J S : ℂ → V →L[ℝ] V} {DJ : ℂ → ℂ →L[ℝ] V →L[ℝ] V} {ξ η : ℂ → V}

/-- The `s`-component `f = η - S ξ + (∂_t J) ξ` of the divergence-form rewriting
`Δ ξ = ∂_s f + ∂_t g` of the weak equation `∂_s ξ + J ∂_t ξ + S ξ = η`, with `∂_t J = DJ · I`. -/
def crDivergenceFst (DJ : ℂ → ℂ →L[ℝ] V →L[ℝ] V) (S : ℂ → V →L[ℝ] V) (ξ η : ℂ → V) (z : ℂ) :
    V :=
  η z - S z (ξ z) + DJ z I (ξ z)

/-- The `t`-component `g = -J (η - S ξ) - (∂_s J) ξ` of the divergence-form rewriting
`Δ ξ = ∂_s f + ∂_t g` of the weak equation `∂_s ξ + J ∂_t ξ + S ξ = η`, with `∂_s J = DJ · 1`. -/
def crDivergenceSnd (J : ℂ → V →L[ℝ] V) (DJ : ℂ → ℂ →L[ℝ] V →L[ℝ] V) (S : ℂ → V →L[ℝ] V)
    (ξ η : ℂ → V) (z : ℂ) : V :=
  -J z (η z - S z (ξ z)) - DJ z 1 (ξ z)

/-- The pointwise defining equation of `TauCeti.crDivergenceFst`. -/
theorem crDivergenceFst_apply (z : ℂ) :
    crDivergenceFst DJ S ξ η z = η z - S z (ξ z) + DJ z I (ξ z) := (rfl)

/-- The pointwise defining equation of `TauCeti.crDivergenceSnd`. -/
theorem crDivergenceSnd_apply (z : ℂ) :
    crDivergenceSnd J DJ S ξ η z = -J z (η z - S z (ξ z)) - DJ z 1 (ξ z) := (rfl)

/-- For constant `J` (so `DJ = 0`) and `S = 0` the `s`-component is the right-hand side `η`. -/
@[simp]
theorem crDivergenceFst_zero_zero : crDivergenceFst (0 : ℂ → ℂ →L[ℝ] V →L[ℝ] V) 0 ξ η = η := by
  funext z
  simp [crDivergenceFst]

/-- For constant `J` (so `DJ = 0`) and `S = 0` the `t`-component is `-J η`. -/
@[simp]
theorem crDivergenceSnd_zero_zero :
    crDivergenceSnd J (0 : ℂ → ℂ →L[ℝ] V →L[ℝ] V) 0 ξ η = fun z => -J z (η z) := by
  funext z
  simp [crDivergenceSnd]

/-- For `ξ = 0` the `s`-component is the right-hand side `η`. -/
@[simp]
theorem crDivergenceFst_zero_left : crDivergenceFst DJ S 0 η = η := by
  funext z
  simp [crDivergenceFst]

/-- For `ξ = 0` the `t`-component is `-J η`. -/
@[simp]
theorem crDivergenceSnd_zero_left : crDivergenceSnd J DJ S 0 η = fun z => -J z (η z) := by
  funext z
  simp [crDivergenceSnd]

/-- The `s`-component depends on its data only up to almost-everywhere equality. -/
theorem crDivergenceFst_congr_ae {μ : Measure ℂ} {DJ' : ℂ → ℂ →L[ℝ] V →L[ℝ] V}
    {S' : ℂ → V →L[ℝ] V} {ξ' η' : ℂ → V} (hDJ : DJ =ᵐ[μ] DJ') (hS : S =ᵐ[μ] S')
    (hξ : ξ =ᵐ[μ] ξ') (hη : η =ᵐ[μ] η') :
    crDivergenceFst DJ S ξ η =ᵐ[μ] crDivergenceFst DJ' S' ξ' η' := by
  filter_upwards [hDJ, hS, hξ, hη] with z h₁ h₂ h₃ h₄
  simp only [crDivergenceFst_apply, h₁, h₂, h₃, h₄]

/-- The `t`-component depends on its data only up to almost-everywhere equality. -/
theorem crDivergenceSnd_congr_ae {μ : Measure ℂ} {J' S' : ℂ → V →L[ℝ] V}
    {DJ' : ℂ → ℂ →L[ℝ] V →L[ℝ] V} {ξ' η' : ℂ → V} (hJ : J =ᵐ[μ] J') (hDJ : DJ =ᵐ[μ] DJ')
    (hS : S =ᵐ[μ] S') (hξ : ξ =ᵐ[μ] ξ') (hη : η =ᵐ[μ] η') :
    crDivergenceSnd J DJ S ξ η =ᵐ[μ] crDivergenceSnd J' DJ' S' ξ' η' := by
  filter_upwards [hJ, hDJ, hS, hξ, hη] with z h₁ h₂ h₃ h₄ h₅
  simp only [crDivergenceSnd_apply, h₁, h₂, h₃, h₄, h₅]

/-- For the standard structure `J = i` on `ℂ` and `S = 0` the `t`-component is `-i η`. -/
theorem crDivergenceSnd_mul_I_zero_zero {ξ η : ℂ → ℂ} :
    crDivergenceSnd (fun _ => ContinuousLinearMap.mul ℝ ℂ I) 0 0 ξ η = fun z => -(I * η z) := by
  simp

end Data

variable [InnerProductSpace ℝ V]
  {J S : ℂ → V →L[ℝ] V} {DJ : ℂ → ℂ →L[ℝ] V →L[ℝ] V} {ξ η : ℂ → V}

/-! ### Integrability of the data -/

section Integrability

/-- The coefficient `∂_v J = DJ · v` inherits local `Lᵖ` membership from `DJ`. -/
private theorem memLpLoc_deriv_apply {D : ℂ → ℂ →L[ℝ] V →L[ℝ] V} (hD : MemLpLoc p Ω D)
    (v : ℂ) : MemLpLoc p Ω (fun z => D z v) :=
  hD.clm_comp (ContinuousLinearMap.apply ℝ (V →L[ℝ] V) v)

/-- If `ξ` is locally `L^q` and `η` locally `Lʳ` with `1/p + 1/q ≤ 1/r`, the `s`-component
`f = η - S ξ + (∂_t J) ξ` of the divergence form is locally `Lʳ`. -/
theorem IsSobolevCRCoefficients.memLpLoc_crDivergenceFst
    (hc : IsSobolevCRCoefficients p Ω J DJ S) (hξ : MemLpLoc q Ω ξ) (hη : MemLpLoc r Ω η)
    (hpqr : p⁻¹ + q⁻¹ ≤ r⁻¹) : MemLpLoc r Ω (crDivergenceFst DJ S ξ η) :=
  (hη.sub (hc.memLpLoc_zeroth.clm_apply hξ hpqr)).add
    ((memLpLoc_deriv_apply hc.memLpLoc_deriv I).clm_apply hξ hpqr)

/-- If `J` is continuous, `ξ` is locally `L^q` and `η` locally `Lʳ` with `1/p + 1/q ≤ 1/r`, the
`t`-component `g = -J (η - S ξ) - (∂_s J) ξ` of the divergence form is locally `Lʳ`. -/
theorem IsSobolevCRCoefficients.memLpLoc_crDivergenceSnd
    (hc : IsSobolevCRCoefficients p Ω J DJ S) (hJc : ContinuousOn J Ω) (hξ : MemLpLoc q Ω ξ)
    (hη : MemLpLoc r Ω η) (hpqr : p⁻¹ + q⁻¹ ≤ r⁻¹) :
    MemLpLoc r Ω (crDivergenceSnd J DJ S ξ η) :=
  ((hη.sub (hc.memLpLoc_zeroth.clm_apply hξ hpqr)).continuousOn_clm_apply hJc).neg.sub
    ((memLpLoc_deriv_apply hc.memLpLoc_deriv 1).clm_apply hξ hpqr)

/-- If `ξ` is locally `L^q` with `1/p + 1/q ≤ 1` and `η` is locally integrable, the `s`-component
of the divergence form is locally integrable. -/
theorem IsSobolevCRCoefficients.locallyIntegrableOn_crDivergenceFst
    (hc : IsSobolevCRCoefficients p Ω J DJ S) (hpq : p⁻¹ + q⁻¹ ≤ 1) (hξ : MemLpLoc q Ω ξ)
    (hη : LocallyIntegrableOn η Ω) : LocallyIntegrableOn (crDivergenceFst DJ S ξ η) Ω :=
  (memLpLoc_one_iff_locallyIntegrableOn Ω.isOpen.isLocallyClosed).1
    (hc.memLpLoc_crDivergenceFst hξ
      ((memLpLoc_one_iff_locallyIntegrableOn Ω.isOpen.isLocallyClosed).2 hη) (by rwa [inv_one]))

/-- If `J` is continuous, `ξ` is locally `L^q` with `1/p + 1/q ≤ 1` and `η` is locally integrable,
the `t`-component of the divergence form is locally integrable. -/
theorem IsSobolevCRCoefficients.locallyIntegrableOn_crDivergenceSnd
    (hc : IsSobolevCRCoefficients p Ω J DJ S) (hJc : ContinuousOn J Ω) (hpq : p⁻¹ + q⁻¹ ≤ 1)
    (hξ : MemLpLoc q Ω ξ) (hη : LocallyIntegrableOn η Ω) :
    LocallyIntegrableOn (crDivergenceSnd J DJ S ξ η) Ω :=
  (memLpLoc_one_iff_locallyIntegrableOn Ω.isOpen.isLocallyClosed).1
    (hc.memLpLoc_crDivergenceSnd hJc hξ
      ((memLpLoc_one_iff_locallyIntegrableOn Ω.isOpen.isLocallyClosed).2 hη) (by rwa [inv_one]))

end Integrability

/-! ### The divergence form of the weak equation -/

section DivergenceForm

/-! #### Calculus of a test function -/

/-- The mixed second derivatives of a test function agree. -/
private theorem fderiv_fderiv_I_one (Φ : 𝓓(Ω, V)) (z : ℂ) :
    fderiv ℝ (fderiv ℝ (Φ : ℂ → V)) z I 1 = fderiv ℝ (fderiv ℝ (Φ : ℂ → V)) z 1 I :=
  (Φ.contDiff.contDiffAt.isSymmSndFDerivAt (by simp)) I 1

/-- The Laplacian on `ℂ` in the coordinates `z = s + i t`. -/
private theorem laplacian_testFunction (Φ : 𝓓(Ω, V)) (z : ℂ) :
    Δ (Φ : ℂ → V) z = fderiv ℝ (fderiv ℝ (Φ : ℂ → V)) z 1 1 +
      fderiv ℝ (fderiv ℝ (Φ : ℂ → V)) z I I := by
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_complexPlane]
  simp only [iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one]


/-- The first derivative in the direction `I` and the second derivatives in the directions
`(1, I)` and `(I, I)` of a test function are bounded. -/
private theorem exists_bound_fderiv_testFunction (Φ : 𝓓(Ω, V)) :
    ∃ C, ∀ z, ‖fderiv ℝ (Φ : ℂ → V) z I‖ ≤ C ∧ ‖fderiv ℝ (fderiv ℝ (Φ : ℂ → V)) z 1 I‖ ≤ C ∧
      ‖fderiv ℝ (fderiv ℝ (Φ : ℂ → V)) z I I‖ ≤ C := by
  have hΦ1 : ContDiff ℝ 1 (fderiv ℝ (Φ : ℂ → V)) := Φ.contDiff.fderiv_right (m := 1) (by simp)
  have hs1 : HasCompactSupport (fderiv ℝ (Φ : ℂ → V)) := Φ.hasCompactSupport.fderiv ℝ
  obtain ⟨C₁, hC₁⟩ := hΦ1.continuous.bounded_above_of_compact_support hs1
  obtain ⟨C₂, hC₂⟩ :=
    (hΦ1.continuous_fderiv one_ne_zero).bounded_above_of_compact_support (hs1.fderiv ℝ)
  refine ⟨max C₁ C₂, fun z => ⟨?_, ?_, ?_⟩⟩
  · calc ‖fderiv ℝ (Φ : ℂ → V) z I‖ ≤ ‖fderiv ℝ (Φ : ℂ → V) z‖ * ‖I‖ :=
          (fderiv ℝ (Φ : ℂ → V) z).le_opNorm I
      _ ≤ max C₁ C₂ := by simpa using (hC₁ z).trans (le_max_left _ _)
  · calc ‖fderiv ℝ (fderiv ℝ (Φ : ℂ → V)) z 1 I‖ ≤
          ‖fderiv ℝ (fderiv ℝ (Φ : ℂ → V)) z‖ * ‖(1 : ℂ)‖ * ‖I‖ :=
          (fderiv ℝ (fderiv ℝ (Φ : ℂ → V)) z).le_opNorm₂ 1 I
      _ ≤ max C₁ C₂ := by simpa using (hC₂ z).trans (le_max_right _ _)
  · calc ‖fderiv ℝ (fderiv ℝ (Φ : ℂ → V)) z I I‖ ≤
          ‖fderiv ℝ (fderiv ℝ (Φ : ℂ → V)) z‖ * ‖I‖ * ‖I‖ :=
          (fderiv ℝ (fderiv ℝ (Φ : ℂ → V)) z).le_opNorm₂ I I
      _ ≤ max C₁ C₂ := by simpa using (hC₂ z).trans (le_max_right _ _)

/-- The test function `∂_s Φ - M ∂_t Φ` for a smooth field of operators `M`. -/
private def crTestField (Φ : 𝓓(Ω, V)) {M : ℂ → V →L[ℝ] V} (hM : ContDiff ℝ ∞ M) : 𝓓(Ω, V) :=
  TestFunction.lineDerivCLM ℝ 1 Φ -
    TestFunction.bilinLeftCLM (ContinuousLinearMap.apply ℝ V) hM (TestFunction.lineDerivCLM ℝ I Φ)

private theorem crTestField_apply (Φ : 𝓓(Ω, V)) {M : ℂ → V →L[ℝ] V} (hM : ContDiff ℝ ∞ M)
    (z : ℂ) :
    crTestField Φ hM z = fderiv ℝ (Φ : ℂ → V) z 1 - M z (fderiv ℝ (Φ : ℂ → V) z I) := by
  simp [crTestField, TestFunction.lineDeriv_eq_fderiv]

private theorem fderiv_crTestField (Φ : 𝓓(Ω, V)) {M : ℂ → V →L[ℝ] V} (hM : ContDiff ℝ ∞ M)
    (z v : ℂ) :
    fderiv ℝ (crTestField Φ hM : ℂ → V) z v = fderiv ℝ (fderiv ℝ (Φ : ℂ → V)) z v 1 -
      fderiv ℝ M z v (fderiv ℝ (Φ : ℂ → V) z I) -
      M z (fderiv ℝ (fderiv ℝ (Φ : ℂ → V)) z v I) := by
  have hD : DifferentiableAt ℝ (fderiv ℝ (Φ : ℂ → V)) z :=
    ((Φ.contDiff.fderiv_right (m := 1) (by simp)).differentiable (by simp)).differentiableAt
  have hMd : DifferentiableAt ℝ M z := (hM.differentiable (by simp)).differentiableAt
  have h1 : DifferentiableAt ℝ (fun y => fderiv ℝ (Φ : ℂ → V) y 1) z :=
    hD.clm_apply (differentiableAt_const _)
  have hI : DifferentiableAt ℝ (fun y => fderiv ℝ (Φ : ℂ → V) y I) z :=
    hD.clm_apply (differentiableAt_const _)
  have hfun : (crTestField Φ hM : ℂ → V) =
      fun y => fderiv ℝ (Φ : ℂ → V) y 1 - M y (fderiv ℝ (Φ : ℂ → V) y I) :=
    funext (crTestField_apply Φ hM)
  rw [hfun, fderiv_fun_sub h1 (hMd.clm_apply hI), fderiv_clm_apply hMd hI,
    fderiv_clm_apply hD (differentiableAt_const _), fderiv_clm_apply hD (differentiableAt_const _)]
  simp
  abel

/-- The terms of the pairing `⟪D* ψ, ξ⟫ - ⟪ψ, η⟫`, for `ψ = ∂_s Φ - M ∂_t Φ`, that depend on the
operator `M` and its derivative `N`. -/
private def remainder (J : ℂ → V →L[ℝ] V) (DJ : ℂ → ℂ →L[ℝ] V →L[ℝ] V) (S : ℂ → V →L[ℝ] V)
    (ξ η : ℂ → V) (Φ : ℂ → V) (z : ℂ) (M : V →L[ℝ] V) (N : ℂ →L[ℝ] V →L[ℝ] V) : ℝ :=
  ⟪N 1 (fderiv ℝ Φ z I), ξ z⟫_ℝ + ⟪M (fderiv ℝ (fderiv ℝ Φ) z 1 I), ξ z⟫_ℝ +
    ⟪N I (fderiv ℝ Φ z I), (J z : V →L[ℝ] V) (ξ z)⟫_ℝ +
    ⟪M (fderiv ℝ (fderiv ℝ Φ) z I I), (J z : V →L[ℝ] V) (ξ z)⟫_ℝ +
    ⟪M (fderiv ℝ Φ z I), (DJ z I : V →L[ℝ] V) (ξ z)⟫_ℝ - ⟪M (fderiv ℝ Φ z I), S z (ξ z)⟫_ℝ +
    ⟪M (fderiv ℝ Φ z I), η z⟫_ℝ

/-- A bound for the remainder term, given a bound `C` for the first and second derivatives of
`Φ` that enter it. -/
private theorem abs_remainder_le {J : ℂ → V →L[ℝ] V} {DJ : ℂ → ℂ →L[ℝ] V →L[ℝ] V}
    {Φ : ℂ → V} {z : ℂ} {C : ℝ} (hC1 : ‖fderiv ℝ Φ z I‖ ≤ C)
    (hC2 : ‖fderiv ℝ (fderiv ℝ Φ) z 1 I‖ ≤ C) (hC3 : ‖fderiv ℝ (fderiv ℝ Φ) z I I‖ ≤ C)
    (M : V →L[ℝ] V) (N : ℂ →L[ℝ] V →L[ℝ] V) :
    |remainder J DJ S ξ η Φ z M N| ≤ ‖N‖ * (C * (‖ξ z‖ + ‖J z (ξ z)‖)) +
      ‖M‖ * (C * (‖ξ z‖ + ‖J z (ξ z)‖ + ‖DJ z I (ξ z)‖ + ‖S z (ξ z)‖ + ‖η z‖)) := by
  have hT : ∀ (T : V →L[ℝ] V) (a b : V) (c : ℝ), ‖a‖ ≤ c → |⟪T a, b⟫_ℝ| ≤ ‖T‖ * (c * ‖b‖) :=
    fun T a b c hac => (abs_real_inner_le_norm _ _).trans (by
      calc ‖T a‖ * ‖b‖ ≤ ‖T‖ * ‖a‖ * ‖b‖ := by gcongr; exact T.le_opNorm a
        _ ≤ ‖T‖ * (c * ‖b‖) := by rw [mul_assoc]; gcongr)
  have hN1 : ‖N 1‖ ≤ ‖N‖ := by simpa using N.le_opNorm 1
  have hNI : ‖N I‖ ≤ ‖N‖ := by simpa using N.le_opNorm I
  have h1 := hT (N 1) _ (ξ z) C hC1
  have h2 := hT M _ (ξ z) C hC2
  have h3 := hT (N I) _ (J z (ξ z)) C hC1
  have h4 := hT M _ (J z (ξ z)) C hC3
  have h5 := hT M _ (DJ z I (ξ z)) C hC1
  have h6 := hT M _ (S z (ξ z)) C hC1
  have h7 := hT M _ (η z) C hC1
  have hC : 0 ≤ C := (norm_nonneg _).trans hC1
  have e1 : ‖N 1‖ * (C * ‖ξ z‖) ≤ ‖N‖ * (C * ‖ξ z‖) := by gcongr
  have e3 : ‖N I‖ * (C * ‖J z (ξ z)‖) ≤ ‖N‖ * (C * ‖J z (ξ z)‖) := by gcongr
  unfold remainder
  obtain ⟨l1, u1⟩ := abs_le.1 h1
  obtain ⟨l2, u2⟩ := abs_le.1 h2
  obtain ⟨l3, u3⟩ := abs_le.1 h3
  obtain ⟨l4, u4⟩ := abs_le.1 h4
  obtain ⟨l5, u5⟩ := abs_le.1 h5
  obtain ⟨l6, u6⟩ := abs_le.1 h6
  obtain ⟨l7, u7⟩ := abs_le.1 h7
  refine abs_le.2 ⟨?_, ?_⟩ <;> linarith

/-- The bound for the remainder term, in extended nonnegative reals. -/
private theorem enorm_remainder_le {J : ℂ → V →L[ℝ] V} {DJ : ℂ → ℂ →L[ℝ] V →L[ℝ] V}
    {Φ : ℂ → V} {z : ℂ} {C : ℝ} (hC1 : ‖fderiv ℝ Φ z I‖ ≤ C)
    (hC2 : ‖fderiv ℝ (fderiv ℝ Φ) z 1 I‖ ≤ C) (hC3 : ‖fderiv ℝ (fderiv ℝ Φ) z I I‖ ≤ C)
    (M : V →L[ℝ] V) (N : ℂ →L[ℝ] V →L[ℝ] V) :
    ‖remainder J DJ S ξ η Φ z M N‖ₑ ≤ ‖N‖ₑ * ‖C * (‖ξ z‖ + ‖J z (ξ z)‖)‖ₑ +
      ‖M‖ₑ * ‖C * (‖ξ z‖ + ‖J z (ξ z)‖ + ‖DJ z I (ξ z)‖ + ‖S z (ξ z)‖ + ‖η z‖)‖ₑ := by
  have hC0 : 0 ≤ C := (norm_nonneg _).trans hC1
  have hbd := abs_remainder_le (J := J) (DJ := DJ) (S := S) (ξ := ξ) (η := η) hC1 hC2 hC3 M N
  have hb1 : 0 ≤ C * (‖ξ z‖ + ‖J z (ξ z)‖) := mul_nonneg hC0 (by positivity)
  have hb2 : 0 ≤ C * (‖ξ z‖ + ‖J z (ξ z)‖ + ‖DJ z I (ξ z)‖ + ‖S z (ξ z)‖ + ‖η z‖) :=
    mul_nonneg hC0 (by positivity)
  refine (Real.eNorm_eq_ofReal_abs _).trans_le ((ENNReal.ofReal_le_ofReal hbd).trans_eq ?_)
  rw [ENNReal.ofReal_add (mul_nonneg (norm_nonneg N) hb1) (mul_nonneg (norm_nonneg M) hb2),
    ENNReal.ofReal_mul (norm_nonneg _), ENNReal.ofReal_mul (norm_nonneg _), ofReal_norm,
    ofReal_norm, ← Real.eNorm_of_nonneg hb1, ← Real.eNorm_of_nonneg hb2]


variable [CompleteSpace V]

/-- The linear algebra behind the comparison of the two pairings, at a single point. -/
private theorem pairing_algebra (a₁ a d₁₁ d₁₂ d₂₂ x y : V) (j dj₁ dj₂ s M N₁ N₂ : V →L[ℝ] V) :
    (-⟪d₁₁ - N₁ a - M d₁₂, x⟫_ℝ - ⟪d₁₂ - N₂ a - M d₂₂, j x⟫_ℝ - ⟪a₁ - M a, dj₂ x⟫_ℝ +
        ⟪a₁ - M a, s x⟫_ℝ - ⟪a₁ - M a, y⟫_ℝ) +
      (⟪d₁₁ + d₂₂, x⟫_ℝ + (⟪a₁, y - s x + dj₂ x⟫_ℝ + ⟪a, -j (y - s x) - dj₁ x⟫_ℝ)) =
    (⟪(N₁ - ContinuousLinearMap.adjoint dj₁) a, x⟫_ℝ +
        ⟪(M - ContinuousLinearMap.adjoint j) d₁₂, x⟫_ℝ +
        ⟪(N₂ - ContinuousLinearMap.adjoint dj₂) a, j x⟫_ℝ +
        ⟪(M - ContinuousLinearMap.adjoint j) d₂₂, j x⟫_ℝ +
        ⟪(M - ContinuousLinearMap.adjoint j) a, dj₂ x⟫_ℝ -
        ⟪(M - ContinuousLinearMap.adjoint j) a, s x⟫_ℝ +
        ⟪(M - ContinuousLinearMap.adjoint j) a, y⟫_ℝ) +
      (⟪a, dj₂ (j x) + j (dj₂ x)⟫_ℝ + ⟪d₂₂, j (j x) + x⟫_ℝ) := by
  simp only [sub_apply, map_sub, inner_add_left, inner_add_right, inner_sub_left,
    inner_sub_right, inner_neg_right, ContinuousLinearMap.adjoint_inner_left]
  ring

/-- The pairing `⟪D* ψ, ξ⟫ - ⟪ψ, η⟫` for `ψ = ∂_s Φ - M ∂_t Φ`, compared with the
divergence-form pairing: the difference is the remainder term at `(M - Jᵀ, ∂M - (∂J)ᵀ)` plus a
term that vanishes when `J² = -1` and `(∂_t J) J + J (∂_t J) = 0`. -/
private theorem pairing_crTestField_add_eq (Φ : 𝓓(Ω, V)) {M : ℂ → V →L[ℝ] V}
    (hM : ContDiff ℝ ∞ M) (z : ℂ) :
    (⟪crFormalAdjoint J DJ S (crTestField Φ hM) z, ξ z⟫_ℝ - ⟪crTestField Φ hM z, η z⟫_ℝ) +
        (⟪Δ (Φ : ℂ → V) z, ξ z⟫_ℝ + (⟪fderiv ℝ (Φ : ℂ → V) z 1, crDivergenceFst DJ S ξ η z⟫_ℝ +
          ⟪fderiv ℝ (Φ : ℂ → V) z I, crDivergenceSnd J DJ S ξ η z⟫_ℝ)) =
      remainder J DJ S ξ η Φ z (M z - star (J z))
        (fderiv ℝ M z - (starL' ℝ : (V →L[ℝ] V) ≃L[ℝ] V →L[ℝ] V).toContinuousLinearMap.comp
          (DJ z)) +
        (⟪fderiv ℝ (Φ : ℂ → V) z I, (DJ z I ∘L J z + J z ∘L DJ z I) (ξ z)⟫_ℝ +
          ⟪fderiv ℝ (fderiv ℝ (Φ : ℂ → V)) z I I, (J z ∘L J z + 1) (ξ z)⟫_ℝ) := by
  rw [inner_crFormalAdjoint, fderiv_crTestField, fderiv_crTestField, crTestField_apply,
    laplacian_testFunction, fderiv_fderiv_I_one, crDivergenceFst_apply, crDivergenceSnd_apply]
  simp only [remainder, sub_apply, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    starL'_apply, ContinuousLinearMap.star_eq_adjoint, add_apply, one_apply_eq_self]
  exact pairing_algebra _ _ _ _ _ _ _ _ _ _ _ _ _ _

/-- Where `J² = -1` and `(∂J) J + J (∂J) = 0`, the pairing `⟪D* ψ, ξ⟫ - ⟪ψ, η⟫` for
`ψ = ∂_s Φ - M ∂_t Φ` differs from the divergence-form pairing by at most the remainder bound at
`(M - Jᵀ, ∂M - (∂J)ᵀ)`, which vanishes off the support of `Φ`. -/
private theorem ae_enorm_pairing_crTestField_add_le (hJ : ∀ z ∈ Ω, J z ∘L J z = -1)
    (hJJ : ∀ᵐ z ∂volume.restrict Ω, ∀ v, DJ z v ∘L J z + J z ∘L DJ z v = 0) (Φ : 𝓓(Ω, V))
    {C : ℝ} (hC : ∀ z, ‖fderiv ℝ (Φ : ℂ → V) z I‖ ≤ C ∧
      ‖fderiv ℝ (fderiv ℝ (Φ : ℂ → V)) z 1 I‖ ≤ C ∧ ‖fderiv ℝ (fderiv ℝ (Φ : ℂ → V)) z I I‖ ≤ C)
    {M : ℂ → V →L[ℝ] V} (hM : ContDiff ℝ ∞ M) :
    ∀ᵐ z, ‖(⟪crFormalAdjoint J DJ S (crTestField Φ hM) z, ξ z⟫_ℝ - ⟪crTestField Φ hM z, η z⟫_ℝ) +
        (⟪Δ (Φ : ℂ → V) z, ξ z⟫_ℝ + (⟪fderiv ℝ (Φ : ℂ → V) z 1, crDivergenceFst DJ S ξ η z⟫_ℝ +
          ⟪fderiv ℝ (Φ : ℂ → V) z I, crDivergenceSnd J DJ S ξ η z⟫_ℝ))‖ₑ ≤
      (tsupport (Φ : ℂ → V)).indicator (fun z =>
        ‖fderiv ℝ M z - (starL' ℝ : (V →L[ℝ] V) ≃L[ℝ] V →L[ℝ] V).toContinuousLinearMap.comp
          (DJ z)‖ₑ * ‖C * (‖ξ z‖ + ‖J z (ξ z)‖)‖ₑ +
        ‖M z - star (J z)‖ₑ *
          ‖C * (‖ξ z‖ + ‖J z (ξ z)‖ + ‖DJ z I (ξ z)‖ + ‖S z (ξ z)‖ + ‖η z‖)‖ₑ) z := by
  rw [ae_restrict_iff' Ω.isOpen.measurableSet] at hJJ
  filter_upwards [hJJ] with z hz
  rw [pairing_crTestField_add_eq]
  by_cases hzK : z ∈ tsupport (Φ : ℂ → V)
  · have hzΩ : z ∈ (Ω : Set ℂ) := Φ.tsupport_subset hzK
    obtain ⟨hC1, hC2, hC3⟩ := hC z
    rw [hz hzΩ I, hJ z hzΩ, indicator_of_mem hzK]
    simpa using enorm_remainder_le (J := J) (DJ := DJ) (S := S) (ξ := ξ) (η := η) hC1 hC2 hC3
      (M z - star (J z)) _
  · have h1 : fderiv ℝ (Φ : ℂ → V) z = 0 := fderiv_of_notMem_tsupport ℝ hzK
    have h2 : fderiv ℝ (fderiv ℝ (Φ : ℂ → V)) z = 0 :=
      fderiv_of_notMem_tsupport ℝ fun h' => hzK (tsupport_fderiv_subset ℝ h')
    rw [indicator_of_notMem hzK]
    simp [remainder, h1, h2]

/-- If smooth fields `A' n` converge to `Jᵀ` uniformly on a compact `K ⊆ Ω`, with derivatives
converging to `(∂J)ᵀ` in `Lᵖ(K)`, then the bound of
`TauCeti.ae_enorm_pairing_crTestField_add_le` for `M = A' n` tends to zero in `L¹(K)`. -/
private theorem tendsto_setLIntegral_pairing_bound (h : IsWeakCRSolution q Ω J DJ S ξ η)
    (hc : IsSobolevCRCoefficients p Ω J DJ S) (hpq : p⁻¹ + q⁻¹ ≤ 1) (hJc : ContinuousOn J Ω)
    {K : Set ℂ} (hK : IsCompact K) (hKΩ : K ⊆ Ω) (C : ℝ) {A' : ℕ → ℂ → V →L[ℝ] V}
    (hA's : ∀ n, ContDiff ℝ ∞ (A' n))
    (hA'u : TendstoUniformlyOn A' (fun z => star (J z)) atTop K)
    (hA'd : Tendsto (fun n => eLpNorm (fderiv ℝ (A' n) - fun z =>
      (starL' ℝ : (V →L[ℝ] V) ≃L[ℝ] V →L[ℝ] V).toContinuousLinearMap.comp (DJ z)) p
        (volume.restrict K)) atTop (𝓝 0)) :
    Tendsto (fun n => ∫⁻ z in K,
      (‖fderiv ℝ (A' n) z - (starL' ℝ : (V →L[ℝ] V) ≃L[ℝ] V →L[ℝ] V).toContinuousLinearMap.comp
          (DJ z)‖ₑ * ‖C * (‖ξ z‖ + ‖J z (ξ z)‖)‖ₑ +
        ‖A' n z - star (J z)‖ₑ *
          ‖C * (‖ξ z‖ + ‖J z (ξ z)‖ + ‖DJ z I (ξ z)‖ + ‖S z (ξ z)‖ + ‖η z‖)‖ₑ)) atTop (𝓝 0) := by
  have : Fact (1 ≤ p) := ⟨ENNReal.inv_le_one.1 (le_self_add.trans hpq)⟩
  have hq1 : 1 ≤ q := ENNReal.inv_le_one.1 (le_add_self.trans hpq)
  have hloc := Ω.isOpen.isLocallyClosed
  have hξ := h.memLpLoc
  have : IsFiniteMeasure (volume.restrict K) := isFiniteMeasure_restrict.2 hK.measure_lt_top.ne
  -- the weights are in `L^{p'}(K)` and `L¹(K)`
  have hξK : MemLp ξ q (volume.restrict K) := memLpLoc_iff.1 hξ K hKΩ hK
  have hJξK : MemLp (fun z => J z (ξ z)) q (volume.restrict K) :=
    memLpLoc_iff.1 (hξ.continuousOn_clm_apply hJc) K hKΩ hK
  have hqp : p.conjExponent ≤ q := by
    rw [← ENNReal.inv_le_inv, ← ENNReal.HolderConjugate.one_sub_inv p p.conjExponent]
    exact ENNReal.le_sub_of_add_le_left
      (ENNReal.inv_ne_top.2 (zero_lt_one.trans_le Fact.out).ne') hpq
  have hw₁ : MemLp (fun z => C * (‖ξ z‖ + ‖J z (ξ z)‖)) p.conjExponent (volume.restrict K) :=
    ((hξK.mono_exponent hqp).norm.add (hJξK.mono_exponent hqp).norm).const_mul C
  have hint : ∀ {w : ℂ → V}, LocallyIntegrableOn w Ω →
      MemLp (fun z => ‖w z‖) 1 (volume.restrict K) := fun hw =>
    (memLp_one_iff_integrable.2 (hw.integrableOn_compact_subset hKΩ hK)).norm
  have hw₂ : MemLp (fun z => C * (‖ξ z‖ + ‖J z (ξ z)‖ + ‖DJ z I (ξ z)‖ + ‖S z (ξ z)‖ + ‖η z‖)) 1
      (volume.restrict K) :=
    (((((hξK.mono_exponent hq1).norm.add (hJξK.mono_exponent hq1).norm).add
      (hint ((memLpLoc_deriv_apply hc.memLpLoc_deriv I).locallyIntegrableOn_clm_apply hξ hpq
        hloc))).add
      (hint (hc.memLpLoc_zeroth.locallyIntegrableOn_clm_apply hξ hpq hloc))).add
      (hint h.locallyIntegrableOn)).const_mul C
  -- the derivative term tends to zero by Hölder's inequality
  have hlim₁ : Tendsto (fun n => ∫⁻ z in K,
      ‖fderiv ℝ (A' n) z - (starL' ℝ : (V →L[ℝ] V) ≃L[ℝ] V →L[ℝ] V).toContinuousLinearMap.comp
        (DJ z)‖ₑ * ‖C * (‖ξ z‖ + ‖J z (ξ z)‖)‖ₑ) atTop (𝓝 0) :=
    tendsto_lintegral_enorm_mul (a := p) (b := p.conjExponent)
      (X := fun n => fderiv ℝ (A' n) - fun z =>
        (starL' ℝ : (V →L[ℝ] V) ≃L[ℝ] V →L[ℝ] V).toContinuousLinearMap.comp (DJ z))
      (g := fun z => C * (‖ξ z‖ + ‖J z (ξ z)‖)) hw₁.eLpNorm_ne_top hA'd
  -- the zeroth-order term tends to zero by uniform convergence
  have he := hA'u.tendsto_iSup_enorm_sub
  have hw₂i : ∫⁻ z in K, ‖C * (‖ξ z‖ + ‖J z (ξ z)‖ + ‖DJ z I (ξ z)‖ + ‖S z (ξ z)‖ + ‖η z‖)‖ₑ ≠
      ⊤ := by
    rw [← eLpNorm_one_eq_lintegral_eNorm hw₂.aestronglyMeasurable]
    exact hw₂.eLpNorm_ne_top
  have hlim₂ : Tendsto (fun n => ∫⁻ z in K, ‖A' n z - star (J z)‖ₑ *
      ‖C * (‖ξ z‖ + ‖J z (ξ z)‖ + ‖DJ z I (ξ z)‖ + ‖S z (ξ z)‖ + ‖η z‖)‖ₑ) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (by simpa only [zero_mul] using ENNReal.Tendsto.mul_const he (Or.inr hw₂i)) (fun _ => bot_le)
      fun n => ?_
    refine (setLIntegral_mono' hK.measurableSet fun z hz => ?_).trans_eq
      (lintegral_const_mul'' _ hw₂.aestronglyMeasurable.eNorm)
    gcongr
    exact le_iSup₂ (f := fun x (_ : x ∈ K) => ‖A' n x - star (J x)‖ₑ) z hz
  have hmeas : ∀ n, AEMeasurable (fun z => ‖fderiv ℝ (A' n) z -
      (starL' ℝ : (V →L[ℝ] V) ≃L[ℝ] V →L[ℝ] V).toContinuousLinearMap.comp (DJ z)‖ₑ *
        ‖C * (‖ξ z‖ + ‖J z (ξ z)‖)‖ₑ) (volume.restrict K) := fun n =>
    ((((hA's n).continuous_fderiv (by simp)).aestronglyMeasurable.sub
      (memLpLoc_iff.1 (hc.memLpLoc_deriv.continuousOn_clm_comp continuousOn_const) K hKΩ
        hK).aestronglyMeasurable).eNorm).mul hw₁.aestronglyMeasurable.eNorm
  have hlim := hlim₁.add hlim₂
  rw [add_zero] at hlim
  exact hlim.congr fun n => (lintegral_add_left' (hmeas n) _).symm

/-- **The weak equation in divergence form, tested against vector fields.** Let `ξ` be a weak
solution of `∂_s ξ + J ∂_t ξ + S ξ = η` on `Ω`, where `J` is continuous with `J² = -1`, the
coefficients are locally `W^{1,p}` and `Lᵖ` for a finite `p`, and `1/p + 1/q ≤ 1`. Then for
every test function `Φ ∈ 𝓓(Ω, V)`,

`∫ ⟪Δ Φ, ξ⟫ = -∫ (⟪∂_s Φ, f⟫ + ⟪∂_t Φ, g⟫)`

with `f = TauCeti.crDivergenceFst DJ S ξ η` and `g = TauCeti.crDivergenceSnd J DJ S ξ η`. -/
theorem IsWeakCRSolution.integral_inner_laplacian_eq
    (h : IsWeakCRSolution q Ω J DJ S ξ η) (hc : IsSobolevCRCoefficients p Ω J DJ S)
    (hp_top : p ≠ ⊤) (hpq : p⁻¹ + q⁻¹ ≤ 1) (hJc : ContinuousOn J Ω)
    (hJ : ∀ z ∈ Ω, J z ∘L J z = -1) (Φ : 𝓓(Ω, V)) :
    ∫ z, ⟪Δ (Φ : ℂ → V) z, ξ z⟫_ℝ =
      -∫ z, (⟪fderiv ℝ (Φ : ℂ → V) z 1, crDivergenceFst DJ S ξ η z⟫_ℝ +
        ⟪fderiv ℝ (Φ : ℂ → V) z I, crDivergenceSnd J DJ S ξ η z⟫_ℝ) := by
  have : Fact (1 ≤ p) := ⟨ENNReal.inv_le_one.1 (le_self_add.trans hpq)⟩
  have hq1 : 1 ≤ q := ENNReal.inv_le_one.1 (le_add_self.trans hpq)
  have hξi : LocallyIntegrableOn ξ Ω := h.memLpLoc.locallyIntegrableOn hq1 Ω.isOpen.isLocallyClosed
  have hf := hc.locallyIntegrableOn_crDivergenceFst hpq h.memLpLoc h.locallyIntegrableOn
  have hg := hc.locallyIntegrableOn_crDivergenceSnd hJc hpq h.memLpLoc h.locallyIntegrableOn
  have hK : IsCompact (tsupport (Φ : ℂ → V)) := Φ.hasCompactSupport
  obtain ⟨C, hC⟩ := exists_bound_fderiv_testFunction Φ
  -- the adjoint field `Jᵀ` and its smooth approximations `A' n`
  have hA := hc.hasWeakFDerivOn.clm_comp
    (starL' ℝ : (V →L[ℝ] V) ≃L[ℝ] V →L[ℝ] V).toContinuousLinearMap
  have hDA := hc.memLpLoc_deriv.continuousOn_clm_comp
    (continuousOn_const (c := (starL' ℝ : (V →L[ℝ] V) ≃L[ℝ] V →L[ℝ] V).toContinuousLinearMap))
  obtain ⟨A', hA's, hA'u, hA'd⟩ := hA.exists_contDiff_tendsto_of_continuousOn hp_top
    (continuous_star.comp_continuousOn hJc) (fun L hL hLΩ => memLpLoc_iff.1 hDA L hLΩ hL) hK
    Φ.tsupport_subset
  -- the integrands
  let Fl : ℂ → ℝ := fun z => -(⟪Δ (Φ : ℂ → V) z, ξ z⟫_ℝ +
    (⟪fderiv ℝ (Φ : ℂ → V) z 1, crDivergenceFst DJ S ξ η z⟫_ℝ +
      ⟪fderiv ℝ (Φ : ℂ → V) z I, crDivergenceSnd J DJ S ξ η z⟫_ℝ))
  let Fn : ℕ → ℂ → ℝ := fun n z => ⟪crFormalAdjoint J DJ S (crTestField Φ (hA's n)) z, ξ z⟫_ℝ -
    ⟪crTestField Φ (hA's n) z, η z⟫_ℝ
  have hΔi : Integrable (fun z => ⟪Δ (Φ : ℂ → V) z, ξ z⟫_ℝ) := by
    have := (LineDeriv.laplacianCLM ℝ ℂ 𝓓(Ω, V) Φ).integrable_inner hξi
    simpa only [TestFunction.laplacianCLM_apply] using this
  have hfgi : Integrable (fun z => ⟪fderiv ℝ (Φ : ℂ → V) z 1, crDivergenceFst DJ S ξ η z⟫_ℝ +
      ⟪fderiv ℝ (Φ : ℂ → V) z I, crDivergenceSnd J DJ S ξ η z⟫_ℝ) :=
    (Φ.integrable_inner_fderiv hf 1).add (Φ.integrable_inner_fderiv hg I)
  have hFl : Integrable Fl := (hΔi.add hfgi).neg
  have hFni : ∀ n, Integrable (Fn n) := fun n =>
    (h.integrable_inner_crFormalAdjoint _).sub ((crTestField Φ (hA's n)).integrable_inner
      h.locallyIntegrableOn)
  have hFn0 : ∀ n, ∫ z, Fn n z = 0 := fun n => by
    simp only [Fn]
    rw [integral_sub (h.integrable_inner_crFormalAdjoint _)
      ((crTestField Φ (hA's n)).integrable_inner h.locallyIntegrableOn),
      h.integral_inner_crFormalAdjoint, sub_self]
  -- the difference tends to zero in `L¹`
  have hJJ := hc.hasWeakFDerivOn.ae_deriv_comp_add_comp_deriv_eq_zero hJc hJ
  have hL1 : Tendsto (fun n => ∫⁻ z, ‖Fn n z - Fl z‖ₑ) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (tendsto_setLIntegral_pairing_bound h hc hpq hJc hK Φ.tsupport_subset C hA's hA'u hA'd)
      (fun _ => by simp) fun n => ?_
    refine (lintegral_mono_ae ?_).trans_eq (lintegral_indicator hK.measurableSet _)
    filter_upwards [ae_enorm_pairing_crTestField_add_le hJ hJJ Φ hC (hA's n)] with z hz
    simpa only [Fn, Fl, sub_neg_eq_add] using hz
  -- pass to the limit in `∫ Fn n = 0`
  have hlim := tendsto_integral_of_L1 Fl hFl.aestronglyMeasurable (Eventually.of_forall hFni) hL1
  simp only [hFn0] at hlim
  have h0 : ∫ z, Fl z = 0 := (tendsto_nhds_unique tendsto_const_nhds hlim).symm
  simp only [Fl] at h0
  rw [integral_neg, neg_eq_zero, integral_add hΔi hfgi] at h0
  linarith

/-- **The weak equation in divergence form.** Let `ξ` be a weak solution of
`∂_s ξ + J ∂_t ξ + S ξ = η` on `Ω`, where `J` is continuous with `J² = -1`, the coefficients are
locally `W^{1,p}` and `Lᵖ` for a finite `p`, and `1/p + 1/q ≤ 1`. Then `ξ` solves
`Δ ξ = ∂_s f + ∂_t g` in the sense of distributions: for every real test function
`φ ∈ 𝓓(Ω, ℝ)`,

`∫ Δ φ • ξ = -∫ (∂_s φ • f + ∂_t φ • g)`

with `f = TauCeti.crDivergenceFst DJ S ξ η` and `g = TauCeti.crDivergenceSnd J DJ S ξ η`. This
is the hypothesis of the divergence-form Laplace regularity
`TauCeti.memWkpLoc_one_of_forall_integral_laplacian_smul_eq` and of the `Lʳ_loc`-plus-harmonic
decomposition `TauCeti.exists_memLpLoc_weaklyHarmonicOn_sub_of_integral_laplacian_smul_eq`. -/
theorem IsWeakCRSolution.integral_laplacian_smul_eq
    (h : IsWeakCRSolution q Ω J DJ S ξ η) (hc : IsSobolevCRCoefficients p Ω J DJ S)
    (hp_top : p ≠ ⊤) (hpq : p⁻¹ + q⁻¹ ≤ 1) (hJc : ContinuousOn J Ω)
    (hJ : ∀ z ∈ Ω, J z ∘L J z = -1) (φ : 𝓓(Ω, ℝ)) :
    ∫ z, Δ (φ : ℂ → ℝ) z • ξ z =
      -∫ z, (fderiv ℝ (φ : ℂ → ℝ) z 1 • crDivergenceFst DJ S ξ η z +
        fderiv ℝ (φ : ℂ → ℝ) z I • crDivergenceSnd J DJ S ξ η z) := by
  have hq1 : 1 ≤ q := ENNReal.inv_le_one.1 (le_add_self.trans hpq)
  have hloc := Ω.isOpen.isLocallyClosed
  have hξi : LocallyIntegrableOn ξ Ω := h.memLpLoc.locallyIntegrableOn hq1 hloc
  have hf := hc.locallyIntegrableOn_crDivergenceFst hpq h.memLpLoc h.locallyIntegrableOn
  have hg := hc.locallyIntegrableOn_crDivergenceSnd hJc hpq h.memLpLoc h.locallyIntegrableOn
  have hΔi : Integrable (fun z => Δ (φ : ℂ → ℝ) z • ξ z) := by
    simpa only [TestFunction.laplacianCLM_apply] using
      (LineDeriv.laplacianCLM ℝ ℂ 𝓓(Ω, ℝ) φ).integrable_smul hξi
  have hfgi : Integrable (fun z => fderiv ℝ (φ : ℂ → ℝ) z 1 • crDivergenceFst DJ S ξ η z +
      fderiv ℝ (φ : ℂ → ℝ) z I • crDivergenceSnd J DJ S ξ η z) := by
    simpa only [TestFunction.lineDeriv_eq_fderiv, Pi.add_def] using
      (integrable_lineDeriv_smul_of_locallyIntegrableOn hf φ 1).add
        (integrable_lineDeriv_smul_of_locallyIntegrableOn hg φ I)
  refine ext_inner_left ℝ fun w => ?_
  have key := h.integral_inner_laplacian_eq hc hp_top hpq hJc hJ
    (TestFunction.postcompCLM (ContinuousLinearMap.toSpanSingleton ℝ w) φ)
  have hcoe : ((TestFunction.postcompCLM (ContinuousLinearMap.toSpanSingleton ℝ w) φ :
      𝓓(Ω, V)) : ℂ → V) = fun z => φ z • w := by
    funext z
    simp
  have hΔ : ∀ z, Δ (fun z => φ z • w) z = Δ (φ : ℂ → ℝ) z • w := fun z => by
    have hφ2 : ContDiff ℝ 2 (φ : ℂ → ℝ) := φ.contDiff.of_le (by simp)
    have := hφ2.contDiffAt.laplacian_CLM_comp_left
      (l := ContinuousLinearMap.toSpanSingleton ℝ w) (x := z)
    simpa [Function.comp_def] using this
  have hd : ∀ z v, fderiv ℝ (fun z => φ z • w) z v = fderiv ℝ (φ : ℂ → ℝ) z v • w := fun z v => by
    rw [fderiv_smul_const ((φ.contDiff.differentiable (by simp)).differentiableAt)]
    simp
  rw [hcoe] at key
  simp only [hΔ, hd, real_inner_smul_left] at key
  rw [← integral_inner hΔi w, inner_neg_right, ← integral_inner hfgi w]
  simpa only [real_inner_smul_right, inner_add_right] using key

end DivergenceForm

end TauCeti
