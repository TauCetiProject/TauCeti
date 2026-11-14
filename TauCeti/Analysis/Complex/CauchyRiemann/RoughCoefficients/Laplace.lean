/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Laplacian
public import TauCeti.Analysis.Complex.CauchyRiemann.RoughCoefficients.Weak
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
import TauCeti.Analysis.Calculus.BumpFunction.Convolution
import TauCeti.Analysis.Distribution.TestFunction.Inner
import TauCeti.Analysis.Distribution.TestFunction.LineDeriv
import TauCeti.Analysis.InnerProductSpace.Adjoint
import TauCeti.Analysis.Sobolev.Mollification.Interior

/-!
# Divergence-form Laplace reduction for Cauchy–Riemann operators with Sobolev coefficients

Let `Ω ⊆ ℂ` be open, write `z = s + i t`, and let `V` be a real Hilbert space. For Sobolev
coefficients `J ∈ W^{1,p}_loc(Ω; V →L[ℝ] V)` and `S ∈ Lᵖ_loc(Ω; V →L[ℝ] V)` with `p < ∞`, assume
`J` is continuous on `Ω` with `J² = -1` everywhere on `Ω`, and let `ξ ∈ L^q_loc(Ω)` weakly solve

`∂_s ξ + J ∂_t ξ + S ξ = η`

in the sense of `TauCeti.IsWeakCRSolution q Ω J DJ S ξ η` with `p⁻¹ + q⁻¹ ≤ 1` (allowing `q = ∞`).

This file proves the divergence-form Laplace reduction
(`TauCeti.IsSobolevCRCoefficients.integral_laplacian_smul_eq`, the analytic core of
McDuff–Salamon Lemma B.4.6): `ξ` weakly solves `Δξ = ∂_s f + ∂_t g` on `Ω` with
`f = η + (∂_t J) ξ - S ξ` and `g = -J f - (∂_s J) ξ - (∂_t J)(J ξ)`. Because `J` is only
`W^{1,p}_loc`, `Jᵀ ∂_t φ` is not a test function; the proof mollifies `J` on a relatively compact
subdomain so that `J_n → J` uniformly on `tsupport φ` while `DJ_n → DJ` in `Lᵖ`, tests the weak
equation against `J_nᵀ ∂_t(φ • w)`, and passes to the limit.

## Main declarations

* `TauCeti.IsSobolevCRCoefficients.integral_laplacian_smul_eq`: the weak divergence-form Laplace
  identity `Δξ = ∂_s f + ∂_t g`.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix B.4 (Lemma B.4.6).
-/

public noncomputable section

open Complex Filter Function Laplacian LineDeriv MeasureTheory Metric Set TopologicalSpace
open scoped ContDiff Convolution Distributions ENNReal InnerProductSpace NNReal Topology

namespace TauCeti

section LaplaceReduction

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  {Ω : Opens ℂ} {p q : ℝ≥0∞}
  {J S : ℂ → V →L[ℝ] V} {DJ : ℂ → ℂ →L[ℝ] V →L[ℝ] V} {ξ η : ℂ → V}

private local instance : NormedAddCommGroup (V →L[ℝ] V) := inferInstance
private local instance : NormedSpace ℝ (V →L[ℝ] V) := inferInstance
private local instance : NormedAddCommGroup (ℂ →L[ℝ] V →L[ℝ] V) := inferInstance
private local instance : NormedSpace ℝ (ℂ →L[ℝ] V →L[ℝ] V) := inferInstance

/-- Local integrability of the auxiliary fields `f` and `g` in the divergence-form Laplace
reduction when `J` is continuous on `Ω`. -/
private theorem IsSobolevCRCoefficients.locallyIntegrableOn_laplace_aux
    (hc : IsSobolevCRCoefficients p Ω J DJ S) (hpq : p⁻¹ + q⁻¹ ≤ 1)
    (hJcont : ContinuousOn J Ω) (hsol : IsWeakCRSolution q Ω J DJ S ξ η) :
    LocallyIntegrableOn (fun z => η z + DJ z I (ξ z) - S z (ξ z)) Ω volume ∧
      LocallyIntegrableOn (fun z => -J z (η z + DJ z I (ξ z) - S z (ξ z)) -
        DJ z 1 (ξ z) - DJ z I (J z (ξ z))) Ω volume := by
  have hloc := Ω.isOpen.isLocallyClosed
  have hDJ1 : MemLpLoc p Ω (fun z => DJ z 1) :=
    hc.memLpLoc_deriv.clm_comp (ContinuousLinearMap.apply ℝ (V →L[ℝ] V) 1)
  have hDJI : MemLpLoc p Ω (fun z => DJ z I) :=
    hc.memLpLoc_deriv.clm_comp (ContinuousLinearMap.apply ℝ (V →L[ℝ] V) I)
  have hJξ : MemLpLoc q Ω (fun z => J z (ξ z)) := hsol.memLpLoc.continuousOn_clm_apply hJcont
  have hf : LocallyIntegrableOn (fun z => η z + DJ z I (ξ z) - S z (ξ z)) Ω volume :=
    (hsol.locallyIntegrableOn.add
      (hDJI.locallyIntegrableOn_clm_apply hsol.memLpLoc hpq hloc)).sub
      (hc.memLpLoc_zeroth.locallyIntegrableOn_clm_apply hsol.memLpLoc hpq hloc)
  have hJf : LocallyIntegrableOn (fun z => J z (η z + DJ z I (ξ z) - S z (ξ z))) Ω volume :=
    hf.continuousOn_clm_apply hloc hJcont
  exact ⟨hf, (hJf.neg.sub (hDJ1.locallyIntegrableOn_clm_apply hsol.memLpLoc hpq hloc)).sub
    (hDJI.locallyIntegrableOn_clm_apply hJξ hpq hloc)⟩

/-- Pointwise expansion of `⟪crFormalAdjoint J DJ S (A† Ψ) z, v⟫_ℝ` for smooth `A`, where `A† Ψ`
is formed via `TestFunction.bilinLeftCLM ContinuousLinearMap.adjointRealCLM.flip`. -/
private theorem inner_crFormalAdjoint_bilinLeftCLM_adjoint {A : ℂ → V →L[ℝ] V}
    (hA : ContDiff ℝ ∞ A) (Ψ : 𝓓(Ω, V)) (z : ℂ) (v : V) :
    ⟪crFormalAdjoint J DJ S
        (TestFunction.bilinLeftCLM
          (ContinuousLinearMap.adjointRealCLM (𝕜 := ℝ) (V := V) (W := V)).flip hA Ψ) z, v⟫_ℝ =
      -⟪(∂_{(1 : ℂ)} Ψ : 𝓓(Ω, V)) z, A z v⟫_ℝ - ⟪(Ψ : ℂ → V) z, fderiv ℝ A z 1 v⟫_ℝ -
        ⟪(∂_{I} Ψ : 𝓓(Ω, V)) z, A z (J z v)⟫_ℝ - ⟪(Ψ : ℂ → V) z, fderiv ℝ A z I (J z v)⟫_ℝ -
        ⟪(Ψ : ℂ → V) z, A z (DJ z I v)⟫_ℝ + ⟪(Ψ : ℂ → V) z, A z (S z v)⟫_ℝ := by
  let B := (ContinuousLinearMap.adjointRealCLM (𝕜 := ℝ) (V := V) (W := V)).flip
  have hdΨ : DifferentiableAt ℝ (Ψ : ℂ → V) z := Ψ.contDiff.differentiable (by simp) z
  have hdA : DifferentiableAt ℝ A z := hA.differentiable (by simp) z
  have hdf (u : ℂ) :
      fderiv ℝ (TestFunction.bilinLeftCLM B hA Ψ : ℂ → V) z u =
        (A z).adjoint ((∂_{u} Ψ : 𝓓(Ω, V)) z) + (fderiv ℝ A z u).adjoint ((Ψ : ℂ → V) z) := by
    rw [TestFunction.bilinLeftCLM_apply, TestFunction.lineDerivOp_apply_eq_fderiv,
      B.fderiv_of_bilinear hdΨ hdA]
    simp only [B, add_apply, ContinuousLinearMap.compL_apply, ContinuousLinearMap.coe_comp,
      Function.comp_apply, ContinuousLinearMap.precompR_apply, ContinuousLinearMap.precompL_apply,
      ContinuousLinearMap.flip_apply, ContinuousLinearMap.adjointRealCLM_apply]
    exact add_comm _ _
  rw [inner_crFormalAdjoint, hdf 1, hdf I]
  simp only [TestFunction.bilinLeftCLM_apply, ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.adjointRealCLM_apply, inner_add_left,
    ContinuousLinearMap.adjoint_inner_left]
  ring

/-- Testing the weak Cauchy–Riemann equation against `J_ρ† Ψ` at mollification scale `ρ` and
replacing `fderiv ℝ J_ρ` on `tsupport Ψ` by the mollified weak derivative `DJ_ρ`. -/
private theorem integral_inner_mollified_adjoint_eq (hpq : p⁻¹ + q⁻¹ ≤ 1)
    (hc : IsSobolevCRCoefficients p Ω J DJ S) (hJcont : ContinuousOn J Ω)
    (hsol : IsWeakCRSolution q Ω J DJ S ξ η) (Ψ : 𝓓(Ω, V)) {W : Opens ℂ}
    (hWΩ : closure (W : Set ℂ) ⊆ Ω) (ρ : ContDiffBump (0 : ℂ))
    (hball : ∀ z ∈ tsupport (Ψ : ℂ → V), closedBall z ρ.rOut ⊆ W)
    (hJW : MemLp J p (volume.restrict W)) (hDJW : MemLp DJ p (volume.restrict W))
    (hJsmooth : ContDiff ℝ ∞
      (ρ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (W : Set ℂ).indicator J)) :
    let J_ρ := ρ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (W : Set ℂ).indicator J;
    let DJ_ρ := ρ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (W : Set ℂ).indicator DJ;
    -(∫ z, ⟪(∂_{(1 : ℂ)} Ψ : 𝓓(Ω, V)) z, J_ρ z (ξ z)⟫_ℝ) -
      (∫ z, ⟪(Ψ : ℂ → V) z, DJ_ρ z 1 (ξ z)⟫_ℝ) -
      (∫ z, ⟪(∂_{I} Ψ : 𝓓(Ω, V)) z, J_ρ z (J z (ξ z))⟫_ℝ) -
      (∫ z, ⟪(Ψ : ℂ → V) z, DJ_ρ z I (J z (ξ z))⟫_ℝ) -
      (∫ z, ⟪(Ψ : ℂ → V) z, J_ρ z (DJ z I (ξ z))⟫_ℝ) +
      (∫ z, ⟪(Ψ : ℂ → V) z, J_ρ z (S z (ξ z))⟫_ℝ) =
      ∫ z, ⟪(Ψ : ℂ → V) z, J_ρ z (η z)⟫_ℝ := by
  intro J_ρ DJ_ρ
  have hp1 : 1 ≤ p := ENNReal.inv_le_one.1 (le_self_add.trans hpq)
  have hq1 : 1 ≤ q := ENNReal.inv_le_one.1 (le_add_self.trans hpq)
  have hloc := Ω.isOpen.isLocallyClosed
  have hDJ_eq (v : ℂ) (w : V) (z : ℂ) :
      ⟪(Ψ : ℂ → V) z, fderiv ℝ J_ρ z v w⟫_ℝ = ⟪(Ψ : ℂ → V) z, DJ_ρ z v w⟫_ℝ := by
    by_cases hz : z ∈ tsupport (Ψ : ℂ → V)
    · have hd := (hc.hasWeakFDerivOn.mono
        (SetLike.coe_subset_coe.1 (subset_closure.trans hWΩ))).fderiv_indicator_convolution_normed
        hJW hDJW hp1 hp1 ρ z (hball z hz)
      simp only [convolution_flip] at hd; rw [hd]
    · simp [image_eq_zero_of_notMem_tsupport hz]
  have hξloc := hsol.memLpLoc.locallyIntegrableOn hq1 hloc
  have hJξloc := (hsol.memLpLoc.continuousOn_clm_apply hJcont).locallyIntegrableOn hq1 hloc
  have hi (Θ : 𝓓(Ω, V)) {A : ℂ → V →L[ℝ] V} (hA : Continuous A) {w : ℂ → V}
      (hw : LocallyIntegrableOn w Ω volume) :
      Integrable (fun z => ⟪(Θ : ℂ → V) z, A z (w z)⟫_ℝ) :=
    Θ.integrable_inner (hw.continuousOn_clm_apply hloc hA.continuousOn)
  have hDJcont (v : ℂ) : Continuous (fun z => fderiv ℝ J_ρ z v) :=
    (hJsmooth.continuous_fderiv (by simp)).clm_apply continuous_const
  have i1 := hi (∂_{(1 : ℂ)} Ψ) hJsmooth.continuous hξloc
  have i2 := hi Ψ (hDJcont 1) hξloc
  have i3 := hi (∂_{I} Ψ) hJsmooth.continuous hJξloc
  have i4 := hi Ψ (hDJcont I) hJξloc
  have i5 := hi Ψ hJsmooth.continuous (w := fun z => DJ z I (ξ z)) ((hc.memLpLoc_deriv.clm_comp
    (ContinuousLinearMap.apply ℝ (V →L[ℝ] V) I)).locallyIntegrableOn_clm_apply
    hsol.memLpLoc hpq hloc)
  have i6 := hi Ψ hJsmooth.continuous
    (hc.memLpLoc_zeroth.locallyIntegrableOn_clm_apply hsol.memLpLoc hpq hloc)
  let Ψ_ρ : 𝓓(Ω, V) := TestFunction.bilinLeftCLM
    (ContinuousLinearMap.adjointRealCLM (𝕜 := ℝ) (V := V) (W := V)).flip hJsmooth Ψ
  have hsplit : ∫ z, ⟪crFormalAdjoint J DJ S Ψ_ρ z, ξ z⟫_ℝ =
      -(∫ z, ⟪(∂_{(1 : ℂ)} Ψ : 𝓓(Ω, V)) z, J_ρ z (ξ z)⟫_ℝ) -
        (∫ z, ⟪(Ψ : ℂ → V) z, fderiv ℝ J_ρ z 1 (ξ z)⟫_ℝ) -
        (∫ z, ⟪(∂_{I} Ψ : 𝓓(Ω, V)) z, J_ρ z (J z (ξ z))⟫_ℝ) -
        (∫ z, ⟪(Ψ : ℂ → V) z, fderiv ℝ J_ρ z I (J z (ξ z))⟫_ℝ) -
        (∫ z, ⟪(Ψ : ℂ → V) z, J_ρ z (DJ z I (ξ z))⟫_ℝ) +
        ∫ z, ⟪(Ψ : ℂ → V) z, J_ρ z (S z (ξ z))⟫_ℝ := by
    simp only [Ψ_ρ, inner_crFormalAdjoint_bilinLeftCLM_adjoint]
    rw [integral_add _ i6, integral_sub _ i5, integral_sub _ i4, integral_sub _ i3,
      integral_sub _ i2, integral_neg]
    exacts [i1.neg, i1.neg.sub i2, (i1.neg.sub i2).sub i3, ((i1.neg.sub i2).sub i3).sub i4,
      (((i1.neg.sub i2).sub i3).sub i4).sub i5]
  simpa only [Ψ_ρ, TestFunction.bilinLeftCLM_apply, ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.adjointRealCLM_apply, ContinuousLinearMap.adjoint_inner_left,
    hDJ_eq] using hsplit.symm.trans (hsol.integral_inner_crFormalAdjoint Ψ_ρ)

/-- Algebraic expansion of the right-hand side pairing in `integral_inner_adjoint_limit`. -/
private theorem integral_inner_adjoint_rhs_eq (hpq : p⁻¹ + q⁻¹ ≤ 1)
    (hc : IsSobolevCRCoefficients p Ω J DJ S) (hJcont : ContinuousOn J Ω)
    (hsol : IsWeakCRSolution q Ω J DJ S ξ η) (Ψ : 𝓓(Ω, V)) :
    -∫ z, ⟪(Ψ : ℂ → V) z,
        -J z (η z + DJ z I (ξ z) - S z (ξ z)) - DJ z 1 (ξ z) - DJ z I (J z (ξ z))⟫_ℝ =
      (∫ z, ⟪(Ψ : ℂ → V) z, J z (η z)⟫_ℝ) +
        (∫ z, ⟪(Ψ : ℂ → V) z, J z (DJ z I (ξ z))⟫_ℝ) -
        (∫ z, ⟪(Ψ : ℂ → V) z, J z (S z (ξ z))⟫_ℝ) +
        (∫ z, ⟪(Ψ : ℂ → V) z, DJ z 1 (ξ z)⟫_ℝ) +
        ∫ z, ⟪(Ψ : ℂ → V) z, DJ z I (J z (ξ z))⟫_ℝ := by
  have hloc := Ω.isOpen.isLocallyClosed
  have hJξ : MemLpLoc q Ω (fun z => J z (ξ z)) := hsol.memLpLoc.continuousOn_clm_apply hJcont
  have hDJI : MemLpLoc p Ω (fun z => DJ z I) :=
    hc.memLpLoc_deriv.clm_comp (ContinuousLinearMap.apply ℝ (V →L[ℝ] V) I)
  have hDJ1 : MemLpLoc p Ω (fun z => DJ z 1) :=
    hc.memLpLoc_deriv.clm_comp (ContinuousLinearMap.apply ℝ (V →L[ℝ] V) 1)
  have hDJIξ : LocallyIntegrableOn (fun z => DJ z I (ξ z)) Ω volume :=
    hDJI.locallyIntegrableOn_clm_apply hsol.memLpLoc hpq hloc
  have hSξ : LocallyIntegrableOn (fun z => S z (ξ z)) Ω volume :=
    hc.memLpLoc_zeroth.locallyIntegrableOn_clm_apply hsol.memLpLoc hpq hloc
  have hclm {w : ℂ → V} (hw : LocallyIntegrableOn w Ω volume) :
      Integrable (fun z => ⟪(Ψ : ℂ → V) z, J z (w z)⟫_ℝ) :=
    Ψ.integrable_inner (hw.continuousOn_clm_apply hloc hJcont)
  obtain ⟨hf, -⟩ := hc.locallyIntegrableOn_laplace_aux hpq hJcont hsol
  have hJf_eq : ∫ z, ⟪(Ψ : ℂ → V) z, J z (η z + DJ z I (ξ z) - S z (ξ z))⟫_ℝ =
      (∫ z, ⟪(Ψ : ℂ → V) z, J z (η z)⟫_ℝ) + (∫ z, ⟪(Ψ : ℂ → V) z, J z (DJ z I (ξ z))⟫_ℝ) -
        ∫ z, ⟪(Ψ : ℂ → V) z, J z (S z (ξ z))⟫_ℝ := by
    simp only [map_sub, map_add, inner_sub_right, inner_add_right]
    rw [integral_sub _ (hclm hSξ), integral_add (hclm hsol.locallyIntegrableOn) (hclm hDJIξ)]
    exact (hclm hsol.locallyIntegrableOn).add (hclm hDJIξ)
  have j1 := hclm hf
  have j2 : Integrable (fun z => ⟪(Ψ : ℂ → V) z, DJ z 1 (ξ z)⟫_ℝ) :=
    Ψ.integrable_inner (hDJ1.locallyIntegrableOn_clm_apply hsol.memLpLoc hpq hloc)
  have j3 : Integrable (fun z => ⟪(Ψ : ℂ → V) z, DJ z I (J z (ξ z))⟫_ℝ) :=
    Ψ.integrable_inner (hDJI.locallyIntegrableOn_clm_apply hJξ hpq hloc)
  have hg_eq : -∫ z, ⟪(Ψ : ℂ → V) z,
        -J z (η z + DJ z I (ξ z) - S z (ξ z)) - DJ z 1 (ξ z) - DJ z I (J z (ξ z))⟫_ℝ =
      (∫ z, ⟪(Ψ : ℂ → V) z, J z (η z + DJ z I (ξ z) - S z (ξ z))⟫_ℝ) +
        (∫ z, ⟪(Ψ : ℂ → V) z, DJ z 1 (ξ z)⟫_ℝ) +
        ∫ z, ⟪(Ψ : ℂ → V) z, DJ z I (J z (ξ z))⟫_ℝ := by
    simp only [inner_sub_right, inner_neg_right]
    rw [integral_sub _ j3, integral_sub _ j2, integral_neg]
    · ring
    exacts [j1.neg, j1.neg.sub j2]
  linarith [hJf_eq, hg_eq]

/-- Limit and algebraic assembly for `IsSobolevCRCoefficients.integral_inner_adjoint_limit`. -/
private theorem integral_inner_adjoint_limit_aux (hp : p ≠ ⊤) (hpq : p⁻¹ + q⁻¹ ≤ 1)
    (hc : IsSobolevCRCoefficients p Ω J DJ S) (hJcont : ContinuousOn J Ω)
    (hJsq : ∀ z ∈ (Ω : Set ℂ), J z * J z = -1) (hsol : IsWeakCRSolution q Ω J DJ S ξ η)
    (Ψ : 𝓓(Ω, V)) {W : Opens ℂ} (hWc : IsCompact (closure (W : Set ℂ)))
    (hWΩ : closure (W : Set ℂ) ⊆ Ω) (hΨW : tsupport (Ψ : ℂ → V) ⊆ W)
    {ρ : ℕ → ContDiffBump (0 : ℂ)} (hρ0 : Tendsto (fun n => (ρ n).rOut) atTop (𝓝 0))
    (hball : ∀ n, ∀ z ∈ tsupport (Ψ : ℂ → V), closedBall z (ρ n).rOut ⊆ W)
    (hunif : TendstoUniformlyOn
      (fun n => (ρ n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
        (W : Set ℂ).indicator J) J atTop (tsupport (Ψ : ℂ → V)))
    (hJW : MemLp J p (volume.restrict W)) (hDJW : MemLp DJ p (volume.restrict W))
    (hξW : MemLp ξ q (volume.restrict W))
    (hJξW : MemLp (fun z => J z (ξ z)) q (volume.restrict W))
    (hJn_smooth : ∀ n, ContDiff ℝ ∞
      ((ρ n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (W : Set ℂ).indicator J)) :
    -(∫ z, ⟪(∂_{(1 : ℂ)} Ψ : 𝓓(Ω, V)) z, J z (ξ z)⟫_ℝ) +
        ∫ z, ⟪(∂_{I} Ψ : 𝓓(Ω, V)) z, ξ z⟫_ℝ =
      -∫ z, ⟪(Ψ : ℂ → V) z,
        -J z (η z + DJ z I (ξ z) - S z (ξ z)) - DJ z 1 (ξ z) - DJ z I (J z (ξ z))⟫_ℝ := by
  have hq1 : 1 ≤ q := ENNReal.inv_le_one.1 (le_add_self.trans hpq)
  have hloc := Ω.isOpen.isLocallyClosed
  have hJξ : MemLpLoc q Ω (fun z => J z (ξ z)) := hsol.memLpLoc.continuousOn_clm_apply hJcont
  have hξloc := hsol.memLpLoc.locallyIntegrableOn hq1 hloc
  have hJξloc := hJξ.locallyIntegrableOn hq1 hloc
  have hDJIξ : LocallyIntegrableOn (fun z => DJ z I (ξ z)) Ω volume :=
    (hc.memLpLoc_deriv.clm_comp
      (ContinuousLinearMap.apply ℝ (V →L[ℝ] V) I)).locallyIntegrableOn_clm_apply
      hsol.memLpLoc hpq hloc
  have hSξ : LocallyIntegrableOn (fun z => S z (ξ z)) Ω volume :=
    hc.memLpLoc_zeroth.locallyIntegrableOn_clm_apply hsol.memLpLoc hpq hloc
  have hJn_cont {s : Set ℂ} : ∀ᶠ n in atTop, ContinuousOn
      ((ρ n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (W : Set ℂ).indicator J) s :=
    .of_forall fun n => (hJn_smooth n).continuous.continuousOn
  have hconv (v : ℂ) {u : ℂ → V} (huW : MemLp u q (volume.restrict W)) :
      Tendsto (fun n => ∫ z, ⟪(Ψ : ℂ → V) z,
          (((ρ n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
            (W : Set ℂ).indicator DJ) z v) (u z)⟫_ℝ)
        atTop (𝓝 (∫ z, ⟪(Ψ : ℂ → V) z, DJ z v (u z)⟫_ℝ)) := by
    simpa using Ψ.tendsto_integral_inner_bilin_normed_convolution
      (ContinuousLinearMap.apply ℝ (V →L[ℝ] V) v) hp hpq hWc hΨW hDJW huW hρ0
  have hlim_lhs :=
    ((((((∂_{(1 : ℂ)} Ψ).tendsto_integral_inner_clm_of_tendstoUniformlyOn hξloc hJn_cont
        (hunif.mono (Ψ.tsupport_lineDerivOp_subset 1))).neg.sub
      (hconv 1 hξW)).sub
      ((∂_{I} Ψ).tendsto_integral_inner_clm_of_tendstoUniformlyOn hJξloc hJn_cont
        (hunif.mono (Ψ.tsupport_lineDerivOp_subset I)))).sub
      (hconv I hJξW)).sub
      (Ψ.tendsto_integral_inner_clm_of_tendstoUniformlyOn hDJIξ hJn_cont hunif)).add
      (Ψ.tendsto_integral_inner_clm_of_tendstoUniformlyOn hSξ hJn_cont hunif)
  have hlim_rhs := Ψ.tendsto_integral_inner_clm_of_tendstoUniformlyOn hsol.locallyIntegrableOn
    hJn_cont hunif
  have hlim := tendsto_nhds_unique hlim_lhs (hlim_rhs.congr fun n =>
    (integral_inner_mollified_adjoint_eq hpq hc hJcont hsol Ψ hWΩ (ρ n) (hball n)
      hJW hDJW (hJn_smooth n)).symm)
  have hJJ : ∫ z, ⟪(∂_{I} Ψ : 𝓓(Ω, V)) z, J z (J z (ξ z))⟫_ℝ =
      -∫ z, ⟪(∂_{I} Ψ : 𝓓(Ω, V)) z, ξ z⟫_ℝ := by
    rw [← integral_neg]
    refine integral_congr_ae (.of_forall fun z => ?_)
    dsimp only
    by_cases hzΩ : z ∈ (Ω : Set ℂ)
    · rw [← mul_apply_eq_comp, hJsq z hzΩ, neg_apply, one_apply_eq_self, inner_neg_right]
    · simp [image_eq_zero_of_notMem_tsupport fun h => hzΩ ((∂_{I} Ψ).tsupport_subset h)]
  rw [hJJ] at hlim
  linarith [hlim, integral_inner_adjoint_rhs_eq hpq hc hJcont hsol Ψ]

/-- Passing `ψ_n = J_n† Ψ` to the limit in the weak Cauchy–Riemann equation yields the adjoint
identity for `-Jᵀ` against arbitrary test functions `Ψ : 𝓓(Ω, V)` when `J² = -1` on `Ω`. -/
private theorem IsSobolevCRCoefficients.integral_inner_adjoint_limit (hp : p ≠ ⊤)
    (hpq : p⁻¹ + q⁻¹ ≤ 1) (hc : IsSobolevCRCoefficients p Ω J DJ S) (hJcont : ContinuousOn J Ω)
    (hJsq : ∀ z ∈ (Ω : Set ℂ), J z * J z = -1) (hsol : IsWeakCRSolution q Ω J DJ S ξ η)
    (Ψ : 𝓓(Ω, V)) :
    -(∫ z, ⟪(∂_{(1 : ℂ)} Ψ : 𝓓(Ω, V)) z, J z (ξ z)⟫_ℝ) +
        ∫ z, ⟪(∂_{I} Ψ : 𝓓(Ω, V)) z, ξ z⟫_ℝ =
      -∫ z, ⟪(Ψ : ℂ → V) z,
        -J z (η z + DJ z I (ξ z) - S z (ξ z)) - DJ z 1 (ξ z) - DJ z I (J z (ξ z))⟫_ℝ := by
  have hp1 : 1 ≤ p := ENNReal.inv_le_one.1 (le_self_add.trans hpq)
  obtain ⟨W, hΨW, hWΩ, hWc⟩ :=
    Opens.exists_between_and_isCompact_closure Ψ.hasCompactSupport Ψ.tsupport_subset
  obtain ⟨ρ, hρ0, hball⟩ :=
    exists_contDiffBump_tendsto_rOut_closedBall_subset W.isOpen Ψ.hasCompactSupport hΨW
  have hunif := tendstoUniformlyOn_normed_convolution_indicator (μ := volume) hρ0 W.isOpen
    Ψ.hasCompactSupport hΨW (hJcont.mono (subset_closure.trans hWΩ))
  have hJW : MemLp J p (volume.restrict W) := hc.memLpLoc_coeff.memLp_of_closure_subset hWc hWΩ
  have hDJW : MemLp DJ p (volume.restrict W) := hc.memLpLoc_deriv.memLp_of_closure_subset hWc hWΩ
  have hξW : MemLp ξ q (volume.restrict W) := hsol.memLpLoc.memLp_of_closure_subset hWc hWΩ
  have hJξW : MemLp (fun z => J z (ξ z)) q (volume.restrict W) :=
    (hsol.memLpLoc.continuousOn_clm_apply hJcont).memLp_of_closure_subset hWc hWΩ
  have hJWext : MemLp ((W : Set ℂ).indicator J) p volume :=
    (memLp_indicator_iff_restrict W.isOpen.measurableSet.nullMeasurableSet).2 hJW
  have hJn_smooth (n : ℕ) : ContDiff ℝ ∞
      ((ρ n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (W : Set ℂ).indicator J) :=
    (ρ n).hasCompactSupport_normed.contDiff_convolution_left _ (ρ n).contDiff_normed
      (hJWext.locallyIntegrable hp1)
  exact integral_inner_adjoint_limit_aux hp hpq hc hJcont hJsq hsol Ψ hWc hWΩ hΨW hρ0 hball hunif
    hJW hDJW hξW hJξW hJn_smooth

/-- Testing the weak Cauchy–Riemann equation against `(∂_1 φ) • w` isolates the `∂_1²` and
mixed `∂_I ∂_1` terms in the divergence-form Laplace identity. -/
private theorem IsSobolevCRCoefficients.integral_inner_lineDeriv_one_smul_eq (hpq : p⁻¹ + q⁻¹ ≤ 1)
    (hc : IsSobolevCRCoefficients p Ω J DJ S) (hsol : IsWeakCRSolution q Ω J DJ S ξ η)
    (φ : 𝓓(Ω, ℝ)) (w : V) :
    -(∫ z, ⟪(∂_{(1 : ℂ)} (∂_{(1 : ℂ)} φ) : 𝓓(Ω, ℝ)) z • w, ξ z⟫_ℝ) -
        (∫ z, ⟪(∂_{I} (∂_{(1 : ℂ)} φ) : 𝓓(Ω, ℝ)) z • w, J z (ξ z)⟫_ℝ) =
      ∫ z, ⟪(∂_{(1 : ℂ)} φ : 𝓓(Ω, ℝ)) z • w, η z + DJ z I (ξ z) - S z (ξ z)⟫_ℝ := by
  have hloc := Ω.isOpen.isLocallyClosed
  set Ψ₁ : 𝓓(Ω, V) :=
    TestFunction.postcompCLM (ContinuousLinearMap.toSpanSingleton ℝ w) (∂_{(1 : ℂ)} φ)
  have hDJI_loc : LocallyIntegrableOn (fun z => DJ z I (ξ z)) Ω volume :=
    (hc.memLpLoc_deriv.clm_comp
      (ContinuousLinearMap.apply ℝ (V →L[ℝ] V) I)).locallyIntegrableOn_clm_apply
      hsol.memLpLoc hpq hloc
  have hS_loc : LocallyIntegrableOn (fun z => S z (ξ z)) Ω volume :=
    hc.memLpLoc_zeroth.locallyIntegrableOn_clm_apply hsol.memLpLoc hpq hloc
  have iDJ : Integrable (fun z => ⟪(Ψ₁ : ℂ → V) z, DJ z I (ξ z)⟫_ℝ) :=
    Ψ₁.integrable_inner hDJI_loc
  have iS : Integrable (fun z => ⟪(Ψ₁ : ℂ → V) z, S z (ξ z)⟫_ℝ) :=
    Ψ₁.integrable_inner hS_loc
  have iη : Integrable (fun z => ⟪(Ψ₁ : ℂ → V) z, η z⟫_ℝ) :=
    Ψ₁.integrable_inner hsol.locallyIntegrableOn
  have h1 := hsol.integral_inner_crFormalAdjoint Ψ₁
  rw [hc.integral_inner_crFormalAdjoint_eq_sub_add hpq hsol.memLpLoc Ψ₁] at h1
  simp only [← TestFunction.lineDerivOp_apply_eq_fderiv] at h1
  simp only [Ψ₁, TestFunction.lineDerivOp_postcompCLM, TestFunction.postcompCLM_apply,
    Function.comp_apply, ContinuousLinearMap.toSpanSingleton_apply] at h1
  have hrhs : ∫ z, ⟪(Ψ₁ : ℂ → V) z, η z + DJ z I (ξ z) - S z (ξ z)⟫_ℝ =
      (∫ z, ⟪(Ψ₁ : ℂ → V) z, η z⟫_ℝ) + (∫ z, ⟪(Ψ₁ : ℂ → V) z, DJ z I (ξ z)⟫_ℝ) -
        ∫ z, ⟪(Ψ₁ : ℂ → V) z, S z (ξ z)⟫_ℝ := by
    simp only [inner_sub_right, inner_add_right]
    rw [integral_sub _ iS, integral_add iη iDJ]
    exact iη.add iDJ
  simp only [Ψ₁, TestFunction.postcompCLM_apply, Function.comp_apply,
    ContinuousLinearMap.toSpanSingleton_apply] at hrhs
  linarith

/-- **Divergence-form Laplace reduction** for weak Cauchy–Riemann solutions with Sobolev
coefficients. Suppose `p < ∞`, `p⁻¹ + q⁻¹ ≤ 1` (allowing `q = ∞`), `J` is continuous on `Ω` with
`J² = -1` everywhere on `Ω`, and `ξ` solves `∂_s ξ + J ∂_t ξ + S ξ = η` weakly on `Ω`. Then `ξ`
solves `Δξ = ∂_s f + ∂_t g` weakly on `Ω`, where `f = η + (∂_t J) ξ - S ξ` and
`g = -J f - (∂_s J) ξ - (∂_t J)(J ξ)`. -/
theorem IsSobolevCRCoefficients.integral_laplacian_smul_eq (hp : p ≠ ⊤) (hpq : p⁻¹ + q⁻¹ ≤ 1)
    (hc : IsSobolevCRCoefficients p Ω J DJ S) (hJcont : ContinuousOn J Ω)
    (hJsq : ∀ z ∈ (Ω : Set ℂ), J z * J z = -1) (hsol : IsWeakCRSolution q Ω J DJ S ξ η)
    (φ : 𝓓(Ω, ℝ)) :
    ∫ z, Δ (φ : ℂ → ℝ) z • ξ z =
      -∫ z, (fderiv ℝ (φ : ℂ → ℝ) z 1 • (η z + DJ z I (ξ z) - S z (ξ z)) +
        fderiv ℝ (φ : ℂ → ℝ) z I •
          (-J z (η z + DJ z I (ξ z) - S z (ξ z)) - DJ z 1 (ξ z) - DJ z I (J z (ξ z)))) := by
  have hloc := Ω.isOpen.isLocallyClosed
  have hq1 : 1 ≤ q := ENNReal.inv_le_one.1 (le_add_self.trans hpq)
  have hξloc := hsol.memLpLoc.locallyIntegrableOn hq1 hloc
  obtain ⟨hf, hg⟩ := hc.locallyIntegrableOn_laplace_aux hpq hJcont hsol
  refine ext_inner_left ℝ fun w => ?_
  have eq1 := hc.integral_inner_lineDeriv_one_smul_eq hpq hsol φ w
  have eq2 := hc.integral_inner_adjoint_limit hp hpq hJcont hJsq hsol
    (TestFunction.postcompCLM (ContinuousLinearMap.toSpanSingleton ℝ w) (∂_{I} φ))
  simp only [TestFunction.lineDerivOp_postcompCLM, TestFunction.postcompCLM_apply,
    Function.comp_apply, ContinuousLinearMap.toSpanSingleton_apply] at eq2
  rw [TestFunction.lineDerivOp_comm φ 1 I] at eq2
  have hΔ (z : ℂ) : Δ (φ : ℂ → ℝ) z =
      (∂_{(1 : ℂ)} (∂_{(1 : ℂ)} φ)) z + (∂_{I} (∂_{I} φ)) z := by
    rw [← TestFunction.laplacianCLM_apply]
    simp [laplacianCLM_eq_sum Complex.orthonormalBasisOneI, Fin.sum_univ_two]
  have hint11 := (∂_{(1 : ℂ)} (∂_{(1 : ℂ)} φ)).integrable_smul hξloc
  have hintII := (∂_{I} (∂_{I} φ)).integrable_smul hξloc
  have hintf := integrable_fderiv_smul_of_locallyIntegrableOn hf φ 1
  have hintg := integrable_fderiv_smul_of_locallyIntegrableOn hg φ I
  have hpull (θ : 𝓓(Ω, ℝ)) {u : ℂ → V} (hu : Integrable (fun z => (θ : ℂ → ℝ) z • u z)) :
      ⟪w, ∫ z, (θ : ℂ → ℝ) z • u z⟫_ℝ = ∫ z, ⟪(θ : ℂ → ℝ) z • w, u z⟫_ℝ := by
    rw [← integral_inner hu w]
    exact integral_congr_ae (.of_forall fun z => by simp [inner_smul_left, inner_smul_right])
  have hlhs : ⟪w, ∫ z, Δ (φ : ℂ → ℝ) z • ξ z⟫_ℝ =
      (∫ z, ⟪(∂_{(1 : ℂ)} (∂_{(1 : ℂ)} φ) : 𝓓(Ω, ℝ)) z • w, ξ z⟫_ℝ) +
        ∫ z, ⟪(∂_{I} (∂_{I} φ) : 𝓓(Ω, ℝ)) z • w, ξ z⟫_ℝ := by
    simp_rw [hΔ, add_smul]
    rw [integral_add hint11 hintII, inner_add_right, hpull _ hint11, hpull _ hintII]
  have hrhs : ⟪w, -∫ z, (fderiv ℝ (φ : ℂ → ℝ) z 1 • (η z + DJ z I (ξ z) - S z (ξ z)) +
        fderiv ℝ (φ : ℂ → ℝ) z I •
          (-J z (η z + DJ z I (ξ z) - S z (ξ z)) - DJ z 1 (ξ z) - DJ z I (J z (ξ z))))⟫_ℝ =
      -(∫ z, ⟪(∂_{(1 : ℂ)} φ : 𝓓(Ω, ℝ)) z • w, η z + DJ z I (ξ z) - S z (ξ z)⟫_ℝ) -
        ∫ z, ⟪(∂_{I} φ : 𝓓(Ω, ℝ)) z • w,
          -J z (η z + DJ z I (ξ z) - S z (ξ z)) - DJ z 1 (ξ z) - DJ z I (J z (ξ z))⟫_ℝ := by
    rw [inner_neg_right, integral_add hintf hintg, inner_add_right]
    simp only [← TestFunction.lineDerivOp_apply_eq_fderiv] at hintf hintg ⊢
    rw [hpull _ hintf, hpull _ hintg]
    ring
  linarith

end LaplaceReduction

end TauCeti
