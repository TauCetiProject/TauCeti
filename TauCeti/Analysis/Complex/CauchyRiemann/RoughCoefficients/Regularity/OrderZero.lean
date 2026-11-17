/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Laplacian
public import TauCeti.Analysis.Complex.CauchyRiemann.RoughCoefficients.Weak
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import TauCeti.Analysis.Calculus.BumpFunction.Convolution
import TauCeti.Analysis.Complex.CauchyRiemann.RoughCoefficients.Regularity.Mollify
import TauCeti.Analysis.Complex.Wirtinger.DivergenceLaplace
import TauCeti.Analysis.Distribution.TestFunction.Basic
import TauCeti.Analysis.Distribution.TestFunction.Inner
import TauCeti.Analysis.Distribution.TestFunction.LineDeriv
import TauCeti.Analysis.Sobolev.Local.Multiplication
import TauCeti.Analysis.Sobolev.Local.SobolevEmbedding
import TauCeti.Analysis.Sobolev.WeakDeriv.Bilinear.Holder

/-!
# Order-zero interior Sobolev regularity for rough-coefficient Cauchy–Riemann operators

Let `Ω ⊆ ℂ` be open and let `V` be a real Hilbert space (finite-dimensional for the Sobolev
regularity theorems). Consider the linear Cauchy–Riemann operator `D ξ = ∂_s ξ + J ∂_t ξ + S ξ`
with Sobolev coefficients `J ∈ W^{1,p}_loc(Ω)` and `S ∈ Lᵖ_loc(Ω)` satisfying `J² = -1` almost
everywhere on `Ω`.

This file proves the divergence-form Laplace reduction and order-zero interior Sobolev regularity
(McDuff–Salamon, Lemma B.4.6):

1. **Divergence-form Laplace reduction**
   (`TauCeti.IsSobolevCRCoefficients.forall_integral_laplacian_smul_eq`).
   For any scalar test function `φ ∈ 𝓓(Ω, ℝ)` and vector `v ∈ V`, testing the weak equation
   `∫ ⟪D* ψ, ξ⟫ = ∫ ⟪ψ, η⟫` against `ψ_n = -(∂_s φ) v + (∂_t φ) J_nᵀ v` (where `J_n` is a
   mollification of `J`) and passing to the limit using `J² = -1` and `(∂_t J) J + J (∂_t J) = 0`
   yields the divergence-form Laplace equation `Δ ξ = ∂_s f + ∂_t g` weakly on `Ω`, with
   `f = η + (∂_t J) ξ - S ξ` and `g = -J η - (∂_s J) ξ + J (S ξ)`.
2. **Order-zero regularity (Lemma B.4.6)**
   (`TauCeti.IsSobolevCRCoefficients.memWkpLoc_one_of_isWeakCRSolution`).
   Combining the divergence-form Laplace regularity theorem
   (`TauCeti.memWkpLoc_one_of_forall_integral_laplacian_smul_eq`) with the 2D Sobolev embedding
   iteratively lowers `1/q₀` by `1/2 - 1/p > 0` in finitely many steps, upgrading any weak solution
   `ξ ∈ L^{q₀}_loc(Ω)` (`1/p + 1/q₀ < 1`) with `η ∈ L^q_loc(Ω)` (`1 < q ≤ p`, `2 < p < ∞`) to
   `ξ ∈ W^{1,q}_loc(Ω)`.

## Main declarations

* `TauCeti.IsSobolevCRCoefficients.forall_integral_laplacian_smul_eq`: divergence-form Laplace
  reduction `Δ ξ = ∂_s f + ∂_t g` weakly on `Ω`.
* `TauCeti.IsSobolevCRCoefficients.memWkpLoc_one_of_isWeakCRSolution_of_le`: one-step `L^{q₀}` to
  `W^{1,r}` regularity for `1/p + 1/q₀ ≤ 1/r`.
* `TauCeti.IsSobolevCRCoefficients.memWkpLoc_one_of_isWeakCRSolution`: McDuff–Salamon Lemma B.4.6.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix B.4 (Lemma B.4.6).
-/

public noncomputable section

open Complex Filter MeasureTheory Set TopologicalSpace
open scoped ContDiff Convolution Distributions ENNReal InnerProductSpace Laplacian LineDeriv
open scoped NNReal Topology

namespace TauCeti

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  {Ω : Opens ℂ} {p q q₀ r : ℝ≥0∞}
  {J S : ℂ → V →L[ℝ] V} {DJ : ℂ → ℂ →L[ℝ] V →L[ℝ] V} {ξ η : ℂ → V}

/-- Evaluating the Hilbert adjoint at a fixed vector `v : V`, as a continuous linear map
`(V →L[ℝ] V) →L[ℝ] V`. -/
private def adjointApplyL (v : V) : (V →L[ℝ] V) →L[ℝ] V :=
  (ContinuousLinearMap.apply ℝ V v).comp
    (ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := V)
      (F := V)).toContinuousLinearEquiv.toContinuousLinearMap

private theorem adjointApplyL_apply (v : V) (A : V →L[ℝ] V) :
    adjointApplyL v A = ContinuousLinearMap.adjoint A v := rfl

/-- Differentiating `J² = -1` weakly in direction `I` shows `(∂_t J) J + J (∂_t J) = 0` almost
everywhere on `Ω`. -/
private theorem ae_derivI_comp_add_comp_derivI_eq_zero (hp2 : 2 ≤ p) (hp_top : p ≠ ⊤)
    (hJ : HasWeakFDerivOn volume Ω J DJ) (hJp : MemLpLoc p Ω J) (hDJp : MemLpLoc p Ω DJ)
    (hJsq : ∀ᵐ z ∂volume.restrict Ω, J z * J z = -1) :
    ∀ᵐ z ∂volume.restrict Ω, (DJ z I).comp (J z) + (J z).comp (DJ z I) = 0 := by
  have hpp : p⁻¹ + p⁻¹ ≤ 1 := by
    have hle : p⁻¹ ≤ (2 : ℝ≥0∞)⁻¹ := ENNReal.inv_le_inv.2 hp2
    exact (add_le_add hle hle).trans_eq ENNReal.inv_two_add_inv_two
  have : Fact (1 ≤ p) := ⟨one_le_two.trans hp2⟩
  have hDJIp : MemLpLoc p Ω (fun z => DJ z I) :=
    hDJp.clm_comp (G := V →L[ℝ] V) (ContinuousLinearMap.apply ℝ (V →L[ℝ] V) I)
  have hleib := (hJ.hasWeakLineDerivOn I).bilin_of_memLp (ContinuousLinearMap.compL ℝ V V V)
    hp_top hp_top hp_top hp_top hpp hpp hpp (hJ.hasWeakLineDerivOn I)
    (fun K hK hKΩ => memLpLoc_iff.1 hJp K hKΩ hK)
    (fun K hK hKΩ => memLpLoc_iff.1 hDJIp K hKΩ hK)
    (fun K hK hKΩ => memLpLoc_iff.1 hJp K hKΩ hK)
    (fun K hK hKΩ => memLpLoc_iff.1 hDJIp K hKΩ hK)
  have hae := (hleib.congr_ae hJsq).ae_eq (hasWeakLineDerivOn_const (-1 : V →L[ℝ] V))
  filter_upwards [hae] with z hz
  simpa only [ContinuousLinearMap.compL_apply, Pi.zero_apply] using hz

/-- Pointwise formula for the Fréchet derivative of the smooth auxiliary test field
`ψ(z) = -(∂_s φ)(z) v + (∂_t φ)(z) J₀(z)ᵀ v`. -/
private theorem hasFDerivAt_laplaceTest (φ : 𝓓(Ω, ℝ)) (v : V) {J₀ : ℂ → V →L[ℝ] V}
    (hJ₀ : ContDiff ℝ ∞ J₀) (z : ℂ) :
    HasFDerivAt
      (fun w => -fderiv ℝ (φ : ℂ → ℝ) w 1 • v +
        fderiv ℝ (φ : ℂ → ℝ) w I • ContinuousLinearMap.adjoint (J₀ w) v)
      (-((ContinuousLinearMap.apply ℝ ℝ 1).comp (fderiv ℝ (fderiv ℝ (φ : ℂ → ℝ)) z)).smulRight v +
        (fderiv ℝ (φ : ℂ → ℝ) z I • ((adjointApplyL v).comp (fderiv ℝ J₀ z)) +
          ((ContinuousLinearMap.apply ℝ ℝ I).comp (fderiv ℝ (fderiv ℝ (φ : ℂ → ℝ)) z)).smulRight
            (ContinuousLinearMap.adjoint (J₀ z) v)))
      z := by
  have hdφ : DifferentiableAt ℝ (fderiv ℝ (φ : ℂ → ℝ)) z :=
    (φ.contDiff.fderiv_right (m := ∞) (by simp)).differentiable (by simp) z
  have hpart (u : ℂ) : HasFDerivAt (fun w => fderiv ℝ (φ : ℂ → ℝ) w u)
      ((ContinuousLinearMap.apply ℝ ℝ u).comp (fderiv ℝ (fderiv ℝ (φ : ℂ → ℝ)) z)) z :=
    (ContinuousLinearMap.apply ℝ ℝ u).hasFDerivAt.comp z hdφ.hasFDerivAt
  have hJ₀d : HasFDerivAt (fun w => adjointApplyL v (J₀ w))
      ((adjointApplyL v).comp (fderiv ℝ J₀ z)) z :=
    (adjointApplyL v).hasFDerivAt.comp z (hJ₀.differentiable (by simp) z).hasFDerivAt
  have hfun : (fun w => -fderiv ℝ (φ : ℂ → ℝ) w 1 • v +
      fderiv ℝ (φ : ℂ → ℝ) w I • ContinuousLinearMap.adjoint (J₀ w) v) =
      (-(fun w => fderiv ℝ (φ : ℂ → ℝ) w 1 • v)) +
        ((fun w => fderiv ℝ (φ : ℂ → ℝ) w I) • fun w => adjointApplyL v (J₀ w)) := by
    ext w; simp [neg_smul, adjointApplyL_apply]
  rw [hfun]
  exact (((hpart 1).smul_const v).neg).add ((hpart I).smul hJ₀d)

/-- Pointwise inner-product expansion of `⟪D* ψ, ξ⟫` for the smooth auxiliary test field
`ψ(z) = -(∂_s φ)(z) v + (∂_t φ)(z) J₀(z)ᵀ v`. -/
private theorem inner_crFormalAdjoint_laplaceTest (φ : 𝓓(Ω, ℝ)) (v : V) {J₀ : ℂ → V →L[ℝ] V}
    (hJ₀ : ContDiff ℝ ∞ J₀) (z : ℂ) :
    let ψ : ℂ → V := fun w => -fderiv ℝ (φ : ℂ → ℝ) w 1 • v +
      fderiv ℝ (φ : ℂ → ℝ) w I • ContinuousLinearMap.adjoint (J₀ w) v
    ⟪crFormalAdjoint J DJ S ψ z, ξ z⟫_ℝ =
      ⟪fderiv ℝ (fderiv ℝ (φ : ℂ → ℝ)) z 1 1 • v, ξ z⟫_ℝ -
      ⟪fderiv ℝ (fderiv ℝ (φ : ℂ → ℝ)) z 1 I • v, J₀ z (ξ z)⟫_ℝ -
      ⟪fderiv ℝ (φ : ℂ → ℝ) z I • v, fderiv ℝ J₀ z 1 (ξ z)⟫_ℝ +
      ⟪fderiv ℝ (fderiv ℝ (φ : ℂ → ℝ)) z 1 I • v, J z (ξ z)⟫_ℝ -
      ⟪fderiv ℝ (fderiv ℝ (φ : ℂ → ℝ)) z I I • v, J₀ z (J z (ξ z))⟫_ℝ -
      ⟪fderiv ℝ (φ : ℂ → ℝ) z I • v, fderiv ℝ J₀ z I (J z (ξ z))⟫_ℝ +
      ⟪fderiv ℝ (φ : ℂ → ℝ) z 1 • v, DJ z I (ξ z)⟫_ℝ -
      ⟪fderiv ℝ (φ : ℂ → ℝ) z I • v, J₀ z (DJ z I (ξ z))⟫_ℝ -
      ⟪fderiv ℝ (φ : ℂ → ℝ) z 1 • v, S z (ξ z)⟫_ℝ +
      ⟪fderiv ℝ (φ : ℂ → ℝ) z I • v, J₀ z (S z (ξ z))⟫_ℝ := by
  intro ψ
  have hsymm : fderiv ℝ (fderiv ℝ (φ : ℂ → ℝ)) z I 1 =
      fderiv ℝ (fderiv ℝ (φ : ℂ → ℝ)) z 1 I :=
    (φ.contDiff.contDiffAt (x := z)).isSymmSndFDerivAt (by simp) I 1
  rw [inner_crFormalAdjoint, (hasFDerivAt_laplaceTest φ v hJ₀ z).fderiv]
  simp only [ψ, add_apply, neg_apply, smul_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply, adjointApplyL_apply,
    inner_add_left, inner_neg_left, inner_smul_left, ContinuousLinearMap.adjoint_inner_left,
    RCLike.conj_to_real, hsymm]
  ring

/-- Scalar test-function form of the divergence-form Laplace identity: for fixed `v ∈ V` and
`φ ∈ 𝓓(Ω, ℝ)`, mollifying `J` and passing to the limit in `∫ ⟪D* ψ_n, ξ⟫ = ∫ ⟪ψ_n, η⟫` gives
`∫ Δφ ⟪v, ξ⟫ = -∫ (∂_s φ ⟪v, f⟫ + ∂_t φ ⟪v, g⟫)`. -/
private theorem integral_laplacian_mul_inner_eq (hc : IsSobolevCRCoefficients p Ω J DJ S)
    (hJinf : MemLpLoc ∞ Ω J) (hp2 : 2 ≤ p) (hp_top : p ≠ ⊤) (hpq : p⁻¹ + q⁻¹ ≤ 1)
    (hJsq : ∀ᵐ z ∂volume.restrict Ω, J z * J z = -1)
    (hsol : IsWeakCRSolution q Ω J DJ S ξ η) (φ : 𝓓(Ω, ℝ)) (v : V) :
    ∫ z, Δ (φ : ℂ → ℝ) z * ⟪v, ξ z⟫_ℝ =
      -∫ z, (fderiv ℝ (φ : ℂ → ℝ) z 1 * ⟪v, η z + DJ z I (ξ z) - S z (ξ z)⟫_ℝ +
        fderiv ℝ (φ : ℂ → ℝ) z I * ⟪v, -J z (η z) - DJ z 1 (ξ z) + J z (S z (ξ z))⟫_ℝ) := by
  -- Step 1: Construct smooth mollifications `Jn` of `J` on `W ⋐ W' ⋐ Ω` with `tsupport φ ⊆ W`.
  have hp1 : 1 ≤ p := one_le_two.trans hp2
  have hq1 : 1 ≤ q := ENNReal.inv_le_one.1 (le_add_self.trans hpq)
  have hloc := Ω.isOpen.isLocallyClosed
  obtain ⟨W, hφW, hWΩ, hWc⟩ :=
    Opens.exists_between_and_isCompact_closure φ.hasCompactSupport φ.tsupport_subset
  obtain ⟨W', hWW', hW'Ω, hW'c⟩ := Opens.exists_between_and_isCompact_closure hWc hWΩ
  obtain ⟨ρ, hρ, hsupp⟩ := ContDiffBump.exists_seq_sub_tsupport_subset (μ := volume) hWc hWW'
  have hWsubW' : (W : Set ℂ) ⊆ W' := subset_closure.trans hWW'
  let Jn : ℕ → ℂ → V →L[ℝ] V := fun n =>
    (ρ n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ((W' : Set ℂ).indicator J)
  have hJW'_inf : MemLp J ∞ (volume.restrict (W' : Set ℂ)) :=
    hJinf.memLp_of_closure_subset hW'c hW'Ω
  have hJn_smooth (n : ℕ) : ContDiff ℝ ∞ (Jn n) :=
    ((ρ n).hasCompactSupport_normed (μ := volume)).contDiff_convolution_left
      (ContinuousLinearMap.lsmul ℝ ℝ) ((ρ n).contDiff_normed (n := (⊤ : ℕ∞)))
      (((memLp_indicator_iff_restrict W'.isOpen.measurableSet.nullMeasurableSet).2
        hJW'_inf).locallyIntegrable le_top)
  -- Step 2: Bundle partial derivatives of `φ` as test functions and record integrability.
  let φs : 𝓓(Ω, ℝ) := ∂_{(1 : ℂ)} φ
  let φt : 𝓓(Ω, ℝ) := ∂_{I} φ
  let φss : 𝓓(Ω, ℝ) := ∂_{(1 : ℂ)} φs
  let φst : 𝓓(Ω, ℝ) := ∂_{I} φs
  let φtt : 𝓓(Ω, ℝ) := ∂_{I} φt
  have hφs_W : tsupport (φs : ℂ → ℝ) ⊆ W := (TestFunction.tsupport_lineDerivOp_subset φ 1).trans hφW
  have hφt_W : tsupport (φt : ℂ → ℝ) ⊆ W := (TestFunction.tsupport_lineDerivOp_subset φ I).trans hφW
  have hφst_W : tsupport (φst : ℂ → ℝ) ⊆ W :=
    (TestFunction.tsupport_lineDerivOp_subset φs I).trans hφs_W
  have hφtt_W : tsupport (φtt : ℂ → ℝ) ⊆ W :=
    (TestFunction.tsupport_lineDerivOp_subset φt I).trans hφt_W
  have hintI (α : 𝓓(Ω, ℝ)) {u : ℂ → V} (hu : LocallyIntegrableOn u Ω volume) :
      Integrable (fun z => ⟪(α : ℂ → ℝ) z • v, u z⟫_ℝ) volume :=
    (TestFunction.postcompCLM (ContinuousLinearMap.toSpanSingleton ℝ v) α).integrable_inner hu
  have hintA (α : 𝓓(Ω, ℝ)) {u : ℂ → V} (hu : LocallyIntegrableOn u Ω volume)
      {A : ℂ → V →L[ℝ] V} (hA : Continuous A) :
      Integrable (fun z => ⟪(α : ℂ → ℝ) z • v, A z (u z)⟫_ℝ) volume :=
    hintI α ((hA.continuousOn.memLpLoc (p := ∞)).locallyIntegrableOn_clm_apply
      ((memLpLoc_one_iff_locallyIntegrableOn hloc).2 hu) (by simp) hloc)
  have hJξq : MemLpLoc q Ω (fun z => J z (ξ z)) := by
    have : ENNReal.HolderTriple ∞ q q := ⟨by simp⟩
    exact memLpLoc_iff.2 fun K hKΩ hK => (ContinuousLinearMap.id ℝ (V →L[ℝ] V)).memLp_of_bilin q
      (memLpLoc_iff.1 hJinf K hKΩ hK) (memLpLoc_iff.1 hsol.memLpLoc K hKΩ hK)
  have hDJIp : MemLpLoc p Ω (fun z => DJ z I) :=
    hc.memLpLoc_deriv.clm_comp (G := V →L[ℝ] V) (ContinuousLinearMap.apply ℝ (V →L[ℝ] V) I)
  have hDJ1p : MemLpLoc p Ω (fun z => DJ z 1) :=
    hc.memLpLoc_deriv.clm_comp (G := V →L[ℝ] V) (ContinuousLinearMap.apply ℝ (V →L[ℝ] V) 1)
  have hξ_loc := hsol.memLpLoc.locallyIntegrableOn hq1 hloc
  have hJξ_loc := hJξq.locallyIntegrableOn hq1 hloc
  have hDJIξ_loc := hDJIp.locallyIntegrableOn_clm_apply hsol.memLpLoc hpq hloc
  have hDJ1ξ_loc := hDJ1p.locallyIntegrableOn_clm_apply hsol.memLpLoc hpq hloc
  have hSξ_loc := hc.memLpLoc_zeroth.locallyIntegrableOn_clm_apply hsol.memLpLoc hpq hloc
  have hJη_loc := hJinf.locallyIntegrableOn_clm_apply
    ((memLpLoc_one_iff_locallyIntegrableOn hloc).2 hsol.locallyIntegrableOn) (by simp) hloc
  have hJSξ_loc := hJinf.locallyIntegrableOn_clm_apply
    ((memLpLoc_one_iff_locallyIntegrableOn hloc).2 hSξ_loc) (by simp) hloc
  -- Step 3: Test the weak equation against `ψ n = -(∂_s φ) v + (∂_t φ) Jnᵀ v` and split.
  let ψ : ℕ → 𝓓(Ω, V) := fun n =>
    { toFun := fun z => -(φs : ℂ → ℝ) z • v + (φt : ℂ → ℝ) z • adjointApplyL v (Jn n z)
      contDiff' := (φs.contDiff.neg.smul contDiff_const).add
        (φt.contDiff.smul ((adjointApplyL v).contDiff.comp (hJn_smooth n)))
      hasCompactSupport' :=
        φs.hasCompactSupport.neg.smul_right.add φt.hasCompactSupport.smul_right
      tsupport_subset' := (tsupport_add _ _).trans (union_subset
        ((tsupport_smul_subset_left _ _).trans
          ((tsupport_neg _).trans_subset φs.tsupport_subset))
        ((tsupport_smul_subset_left _ _).trans φt.tsupport_subset)) }
  have hLHS (n : ℕ) : ∫ z, ⟪crFormalAdjoint J DJ S (ψ n) z, ξ z⟫_ℝ =
      (∫ z, ⟪(φss : ℂ → ℝ) z • v, ξ z⟫_ℝ) - (∫ z, ⟪(φst : ℂ → ℝ) z • v, Jn n z (ξ z)⟫_ℝ) -
      (∫ z, ⟪(φt : ℂ → ℝ) z • v, fderiv ℝ (Jn n) z 1 (ξ z)⟫_ℝ) +
      (∫ z, ⟪(φst : ℂ → ℝ) z • v, J z (ξ z)⟫_ℝ) -
      (∫ z, ⟪(φtt : ℂ → ℝ) z • v, Jn n z (J z (ξ z))⟫_ℝ) -
      (∫ z, ⟪(φt : ℂ → ℝ) z • v, fderiv ℝ (Jn n) z I (J z (ξ z))⟫_ℝ) +
      (∫ z, ⟪(φs : ℂ → ℝ) z • v, DJ z I (ξ z)⟫_ℝ) -
      (∫ z, ⟪(φt : ℂ → ℝ) z • v, Jn n z (DJ z I (ξ z))⟫_ℝ) -
      (∫ z, ⟪(φs : ℂ → ℝ) z • v, S z (ξ z)⟫_ℝ) +
      (∫ z, ⟪(φt : ℂ → ℝ) z • v, Jn n z (S z (ξ z))⟫_ℝ) := by
    have hJn_c := (hJn_smooth n).continuous
    have hfJn_c (w : ℂ) :=
      ((hJn_smooth n).fderiv_right (m := ∞) (by simp)).continuous.clm_apply
        (continuous_const (y := w))
    have i1 := hintI φss hξ_loc
    have i2 := hintA φst hξ_loc hJn_c
    have i3 := hintA φt hξ_loc (hfJn_c 1)
    have i4 := hintI φst hJξ_loc
    have i5 := hintA φtt hJξ_loc hJn_c
    have i6 := hintA φt hJξ_loc (hfJn_c I)
    have i7 := hintI φs hDJIξ_loc
    have i8 := hintA φt hDJIξ_loc hJn_c
    have i9 := hintI φs hSξ_loc
    have i10 := hintA φt hSξ_loc hJn_c
    have hpt : ∀ z, ⟪crFormalAdjoint J DJ S (ψ n) z, ξ z⟫_ℝ =
        ⟪(φss : ℂ → ℝ) z • v, ξ z⟫_ℝ - ⟪(φst : ℂ → ℝ) z • v, Jn n z (ξ z)⟫_ℝ -
        ⟪(φt : ℂ → ℝ) z • v, fderiv ℝ (Jn n) z 1 (ξ z)⟫_ℝ +
        ⟪(φst : ℂ → ℝ) z • v, J z (ξ z)⟫_ℝ -
        ⟪(φtt : ℂ → ℝ) z • v, Jn n z (J z (ξ z))⟫_ℝ -
        ⟪(φt : ℂ → ℝ) z • v, fderiv ℝ (Jn n) z I (J z (ξ z))⟫_ℝ +
        ⟪(φs : ℂ → ℝ) z • v, DJ z I (ξ z)⟫_ℝ - ⟪(φt : ℂ → ℝ) z • v, Jn n z (DJ z I (ξ z))⟫_ℝ -
        ⟪(φs : ℂ → ℝ) z • v, S z (ξ z)⟫_ℝ + ⟪(φt : ℂ → ℝ) z • v, Jn n z (S z (ξ z))⟫_ℝ := by
      intro z
      have hψ_fun : (ψ n : ℂ → V) = fun w => -fderiv ℝ (φ : ℂ → ℝ) w 1 • v +
          fderiv ℝ (φ : ℂ → ℝ) w I • ContinuousLinearMap.adjoint (Jn n w) v := by
        ext w
        simp only [ψ, φs, φt, TestFunction.coe_mk, adjointApplyL_apply,
          TestFunction.lineDerivOp_apply_eq_fderiv]
      have hsymm : fderiv ℝ (fderiv ℝ (φ : ℂ → ℝ)) z I 1 =
          fderiv ℝ (fderiv ℝ (φ : ℂ → ℝ)) z 1 I :=
        (φ.contDiff.contDiffAt (x := z)).isSymmSndFDerivAt (by simp) I 1
      have hdd (w₁ w₂ : ℂ) :
          (∂_{w₂} (∂_{w₁} φ) : 𝓓(Ω, ℝ)) z = fderiv ℝ (fderiv ℝ (φ : ℂ → ℝ)) z w₂ w₁ := by
        have hfun : ((∂_{w₁} φ : 𝓓(Ω, ℝ)) : ℂ → ℝ) =
            ContinuousLinearMap.apply ℝ ℝ w₁ ∘ fderiv ℝ (φ : ℂ → ℝ) :=
          funext fun w => TestFunction.lineDerivOp_apply_eq_fderiv φ w₁ w
        rw [TestFunction.lineDerivOp_apply_eq_fderiv, hfun,
          fderiv_comp _ (ContinuousLinearMap.apply ℝ ℝ w₁).differentiableAt
            ((φ.contDiff.fderiv_right (m := ∞) (by simp)).differentiable (by simp) z)]
        simp
      rw [hψ_fun, inner_crFormalAdjoint_laplaceTest φ v (hJn_smooth n) z]
      simp only [φss, φst, φtt, φs, φt, hdd]
      simp only [TestFunction.lineDerivOp_apply_eq_fderiv, hsymm]
    simp_rw [hpt]
    rw [integral_add _ i10, integral_sub _ i9, integral_sub _ i8, integral_add _ i7,
      integral_sub _ i6, integral_sub _ i5, integral_add _ i4, integral_sub _ i3,
      integral_sub i1 i2]
    all_goals fun_prop
  have hRHS (n : ℕ) : ∫ z, ⟪(ψ n : ℂ → V) z, η z⟫_ℝ =
      -(∫ z, ⟪(φs : ℂ → ℝ) z • v, η z⟫_ℝ) + ∫ z, ⟪(φt : ℂ → ℝ) z • v, Jn n z (η z)⟫_ℝ := by
    have j1 := hintI φs hsol.locallyIntegrableOn
    have j2 := hintA φt hsol.locallyIntegrableOn (hJn_smooth n).continuous
    have heq : (fun z => ⟪(ψ n : ℂ → V) z, η z⟫_ℝ) =
        fun z => -⟪(φs : ℂ → ℝ) z • v, η z⟫_ℝ + ⟪(φt : ℂ → ℝ) z • v, Jn n z (η z)⟫_ℝ := by
      ext z
      simp only [ψ, TestFunction.coe_mk, adjointApplyL_apply, neg_smul, inner_add_left,
        inner_neg_left, inner_smul_left, ContinuousLinearMap.adjoint_inner_left,
        RCLike.conj_to_real]
    rw [heq, integral_add _ j2, integral_neg]
    exact j1.neg
  -- Step 4: Pass `n → ∞` and simplify using `J² = -1` and `(∂_t J) J + J (∂_t J) = 0`.
  have hlim2 := tendsto_integral_smul_inner_mollify hWsubW' hρ hJW'_inf φst hφst_W v hξ_loc
  have hlim3 := tendsto_integral_smul_inner_fderiv_mollify hWsubW' hp1 hpq hρ hsupp hW'c hW'Ω
    hc.hasWeakFDerivOn hJW'_inf hc.memLpLoc_deriv φt hφt_W v hsol.memLpLoc 1
  have hlim5 := tendsto_integral_smul_inner_mollify hWsubW' hρ hJW'_inf φtt hφtt_W v hJξ_loc
  have hlim6 := tendsto_integral_smul_inner_fderiv_mollify hWsubW' hp1 hpq hρ hsupp hW'c hW'Ω
    hc.hasWeakFDerivOn hJW'_inf hc.memLpLoc_deriv φt hφt_W v hJξq I
  have hlim8 := tendsto_integral_smul_inner_mollify hWsubW' hρ hJW'_inf φt hφt_W v hDJIξ_loc
  have hlim10 := tendsto_integral_smul_inner_mollify hWsubW' hρ hJW'_inf φt hφt_W v hSξ_loc
  have hlimR := tendsto_integral_smul_inner_mollify hWsubW' hρ hJW'_inf φt hφt_W v
    hsol.locallyIntegrableOn
  have hEq : (fun n => ∫ z, ⟪crFormalAdjoint J DJ S (ψ n) z, ξ z⟫_ℝ) =
      fun n => ∫ z, ⟪(ψ n : ℂ → V) z, η z⟫_ℝ :=
    funext fun n => hsol.integral_inner_crFormalAdjoint (ψ n)
  simp_rw [hLHS, hRHS] at hEq
  have hlim_eq := tendsto_nhds_unique
    (((((((((tendsto_const_nhds.sub hlim2).sub hlim3).add tendsto_const_nhds).sub
      hlim5).sub hlim6).add tendsto_const_nhds).sub hlim8).sub tendsto_const_nhds).add hlim10)
    (hEq ▸ (tendsto_const_nhds.add hlimR))
  have hJJ : ∫ z, ⟪(φtt : ℂ → ℝ) z • v, J z (J z (ξ z))⟫_ℝ =
      -∫ z, ⟪(φtt : ℂ → ℝ) z • v, ξ z⟫_ℝ := by
    rw [← integral_neg]
    refine integral_congr_ae ?_
    filter_upwards [ae_imp_of_ae_restrict hJsq] with z hz
    by_cases hzΩ : z ∈ (Ω : Set ℂ)
    · have hsq : J z (J z (ξ z)) = -ξ z := by simpa using congr($(hz hzΩ) (ξ z))
      simp [hsq]
    · simp [image_eq_zero_of_notMem_tsupport (fun h => hzΩ (φtt.tsupport_subset h))]
  have hcomm : (∫ z, ⟪(φt : ℂ → ℝ) z • v, DJ z I (J z (ξ z))⟫_ℝ) +
      ∫ z, ⟪(φt : ℂ → ℝ) z • v, J z (DJ z I (ξ z))⟫_ℝ = 0 := by
    have h1 := hintI φt (hDJIp.locallyIntegrableOn_clm_apply hJξq hpq hloc)
    have h2 := hintI φt (hJinf.locallyIntegrableOn_clm_apply
      ((memLpLoc_one_iff_locallyIntegrableOn hloc).2 hDJIξ_loc) (by simp) hloc)
    rw [← integral_add h1 h2]
    refine integral_eq_zero_of_ae ?_
    filter_upwards [ae_imp_of_ae_restrict (ae_derivI_comp_add_comp_derivI_eq_zero hp2 hp_top
      hc.hasWeakFDerivOn hc.memLpLoc_coeff hc.memLpLoc_deriv hJsq)] with z hz
    by_cases hzΩ : z ∈ (Ω : Set ℂ)
    · have h0 : DJ z I (J z (ξ z)) + J z (DJ z I (ξ z)) = 0 := by
        simpa using congr($(hz hzΩ) (ξ z))
      rw [← inner_add_right, h0, inner_zero_right]
      rfl
    · simp [image_eq_zero_of_notMem_tsupport (fun h => hzΩ (φt.tsupport_subset h))]
  have hΔ : ∫ z, Δ (φ : ℂ → ℝ) z * ⟪v, ξ z⟫_ℝ =
      (∫ z, ⟪(φss : ℂ → ℝ) z • v, ξ z⟫_ℝ) + ∫ z, ⟪(φtt : ℂ → ℝ) z • v, ξ z⟫_ℝ := by
    rw [← integral_add (hintI φss hξ_loc) (hintI φtt hξ_loc)]
    refine integral_congr_ae (.of_forall fun z => ?_)
    have hΔ_pt : Δ (φ : ℂ → ℝ) z = (φss : ℂ → ℝ) z + (φtt : ℂ → ℝ) z := by
      rw [← TestFunction.laplacianCLM_apply]
      simp [φss, φtt, φs, φt, LineDeriv.laplacianCLM_eq_sum Complex.orthonormalBasisOneI,
        Fin.sum_univ_two]
    simp only [hΔ_pt, inner_smul_left, RCLike.conj_to_real]
    ring
  have hRHS_f : ∫ z, (fderiv ℝ (φ : ℂ → ℝ) z 1 * ⟪v, η z + DJ z I (ξ z) - S z (ξ z)⟫_ℝ +
        fderiv ℝ (φ : ℂ → ℝ) z I * ⟪v, -J z (η z) - DJ z 1 (ξ z) + J z (S z (ξ z))⟫_ℝ) =
      (∫ z, ⟪(φs : ℂ → ℝ) z • v, η z⟫_ℝ) + (∫ z, ⟪(φs : ℂ → ℝ) z • v, DJ z I (ξ z)⟫_ℝ) -
      (∫ z, ⟪(φs : ℂ → ℝ) z • v, S z (ξ z)⟫_ℝ) - (∫ z, ⟪(φt : ℂ → ℝ) z • v, J z (η z)⟫_ℝ) -
      (∫ z, ⟪(φt : ℂ → ℝ) z • v, DJ z 1 (ξ z)⟫_ℝ) +
      ∫ z, ⟪(φt : ℂ → ℝ) z • v, J z (S z (ξ z))⟫_ℝ := by
    have a1 := hintI φs hsol.locallyIntegrableOn
    have a2 := hintI φs hDJIξ_loc
    have a3 := hintI φs hSξ_loc
    have a4 := hintI φt hJη_loc
    have a5 := hintI φt hDJ1ξ_loc
    have a6 := hintI φt hJSξ_loc
    have hpt : (fun z => fderiv ℝ (φ : ℂ → ℝ) z 1 * ⟪v, η z + DJ z I (ξ z) - S z (ξ z)⟫_ℝ +
        fderiv ℝ (φ : ℂ → ℝ) z I * ⟪v, -J z (η z) - DJ z 1 (ξ z) + J z (S z (ξ z))⟫_ℝ) =
        fun z => ⟪(φs : ℂ → ℝ) z • v, η z⟫_ℝ + ⟪(φs : ℂ → ℝ) z • v, DJ z I (ξ z)⟫_ℝ -
          ⟪(φs : ℂ → ℝ) z • v, S z (ξ z)⟫_ℝ - ⟪(φt : ℂ → ℝ) z • v, J z (η z)⟫_ℝ -
          ⟪(φt : ℂ → ℝ) z • v, DJ z 1 (ξ z)⟫_ℝ + ⟪(φt : ℂ → ℝ) z • v, J z (S z (ξ z))⟫_ℝ := by
      ext z
      simp only [φs, φt, TestFunction.lineDerivOp_apply_eq_fderiv, inner_add_right,
        inner_sub_right, inner_neg_right, inner_smul_left, RCLike.conj_to_real]
      ring
    rw [hpt, integral_add _ a6, integral_sub _ a5, integral_sub _ a4, integral_sub _ a3,
      integral_add a1 a2]
    all_goals fun_prop
  rw [hΔ, hRHS_f]
  linarith [hlim_eq, hJJ, hcomm]

/-- **Divergence-form Laplace reduction.** Let `2 ≤ p < ∞`, `1/p + 1/q ≤ 1`, and suppose the
Sobolev coefficients `(J, DJ, S)` satisfy `J ∈ L^∞_loc` and `J² = -1` almost everywhere on `Ω`.
Then any weak solution `ξ` of `∂_s ξ + J ∂_t ξ + S ξ = η` satisfies the divergence-form Laplace
equation `Δ ξ = ∂_s f + ∂_t g` weakly on `Ω`, where `f = η + (∂_t J) ξ - S ξ` and
`g = -J η - (∂_s J) ξ + J (S ξ)`. -/
theorem IsSobolevCRCoefficients.forall_integral_laplacian_smul_eq
    (hc : IsSobolevCRCoefficients p Ω J DJ S) (hJinf : MemLpLoc ∞ Ω J)
    (hp2 : 2 ≤ p) (hp_top : p ≠ ⊤) (hpq : p⁻¹ + q⁻¹ ≤ 1)
    (hJsq : ∀ᵐ z ∂volume.restrict Ω, J z * J z = -1)
    (hsol : IsWeakCRSolution q Ω J DJ S ξ η) (φ : 𝓓(Ω, ℝ)) :
    ∫ z, Δ (φ : ℂ → ℝ) z • ξ z =
      -∫ z, (fderiv ℝ (φ : ℂ → ℝ) z 1 • (η z + DJ z I (ξ z) - S z (ξ z)) +
        fderiv ℝ (φ : ℂ → ℝ) z I • (-J z (η z) - DJ z 1 (ξ z) + J z (S z (ξ z)))) := by
  have hq1 : 1 ≤ q := ENNReal.inv_le_one.1 (le_add_self.trans hpq)
  have hloc := Ω.isOpen.isLocallyClosed
  have hξ_loc := hsol.memLpLoc.locallyIntegrableOn hq1 hloc
  have hDJIp : MemLpLoc p Ω (fun z => DJ z I) :=
    hc.memLpLoc_deriv.clm_comp (G := V →L[ℝ] V) (ContinuousLinearMap.apply ℝ (V →L[ℝ] V) I)
  have hDJ1p : MemLpLoc p Ω (fun z => DJ z 1) :=
    hc.memLpLoc_deriv.clm_comp (G := V →L[ℝ] V) (ContinuousLinearMap.apply ℝ (V →L[ℝ] V) 1)
  have hSξ_loc := hc.memLpLoc_zeroth.locallyIntegrableOn_clm_apply hsol.memLpLoc hpq hloc
  have hf_loc : LocallyIntegrableOn (fun z => η z + DJ z I (ξ z) - S z (ξ z)) Ω volume :=
    (hsol.locallyIntegrableOn.add (hDJIp.locallyIntegrableOn_clm_apply hsol.memLpLoc hpq hloc)).sub
      hSξ_loc
  have hg_loc : LocallyIntegrableOn (fun z => -J z (η z) - DJ z 1 (ξ z) + J z (S z (ξ z)))
      Ω volume :=
    ((hJinf.locallyIntegrableOn_clm_apply
        ((memLpLoc_one_iff_locallyIntegrableOn hloc).2 hsol.locallyIntegrableOn)
        (by simp) hloc).neg.sub
      (hDJ1p.locallyIntegrableOn_clm_apply hsol.memLpLoc hpq hloc)).add
      (hJinf.locallyIntegrableOn_clm_apply
        ((memLpLoc_one_iff_locallyIntegrableOn hloc).2 hSξ_loc) (by simp) hloc)
  have hint_lhs : Integrable (fun z => Δ (φ : ℂ → ℝ) z • ξ z) volume := by
    simpa only [TestFunction.laplacianCLM_apply] using
      (LineDeriv.laplacianCLM ℝ ℂ 𝓓(Ω, ℝ) φ).integrable_smul hξ_loc
  have hint_rhs : Integrable (fun z =>
      fderiv ℝ (φ : ℂ → ℝ) z 1 • (η z + DJ z I (ξ z) - S z (ξ z)) +
        fderiv ℝ (φ : ℂ → ℝ) z I • (-J z (η z) - DJ z 1 (ξ z) + J z (S z (ξ z)))) volume :=
    (integrable_fderiv_smul_of_locallyIntegrableOn hf_loc φ 1).add
      (integrable_fderiv_smul_of_locallyIntegrableOn hg_loc φ I)
  refine ext_inner_left ℝ fun v => ?_
  rw [inner_neg_right, ← innerSL_apply_apply (𝕜 := ℝ), ← innerSL_apply_apply (𝕜 := ℝ),
    ← (innerSL ℝ v).integral_comp_comm hint_lhs, ← (innerSL ℝ v).integral_comp_comm hint_rhs]
  simpa only [Function.comp_apply, innerSL_apply_apply, inner_add_right, inner_smul_right] using
    integral_laplacian_mul_inner_eq hc hJinf hp2 hp_top hpq hJsq hsol φ v

/-- **One-step order-zero regularity.** Let `2 < p < ∞`, `1 < r < ∞`, and `1/p + 1/q ≤ 1/r`.
For Sobolev coefficients `(J, DJ, S)` of class `p` with `J² = -1` almost everywhere, any weak
solution `ξ ∈ L^q_loc` of `∂_s ξ + J ∂_t ξ + S ξ = η` with `η ∈ Lʳ_loc` belongs to
`W^{1,r}_loc(Ω)`. -/
theorem IsSobolevCRCoefficients.memWkpLoc_one_of_isWeakCRSolution_of_le [FiniteDimensional ℝ V]
    (hc : IsSobolevCRCoefficients p Ω J DJ S) (hp : 2 < p) (hp_top : p ≠ ⊤)
    (hr : 1 < r) (hr_top : r ≠ ⊤) (hpqr : p⁻¹ + q⁻¹ ≤ r⁻¹)
    (hJsq : ∀ᵐ z ∂volume.restrict Ω, J z * J z = -1)
    (hsol : IsWeakCRSolution q Ω J DJ S ξ η) (hη : MemLpLoc r Ω η) :
    MemWkpLoc r Ω 1 ξ := by
  have hpq : p⁻¹ + q⁻¹ ≤ 1 := hpqr.trans (ENNReal.inv_le_one.2 hr.le)
  have hq1 : 1 ≤ q := ENNReal.inv_le_one.1 (le_add_self.trans hpq)
  lift p to ℝ≥0 using hp_top
  have hp2 : (2 : ℝ≥0) < p := by exact_mod_cast hp
  have : Fact (1 ≤ (p : ℝ≥0∞)) := ⟨one_le_two.trans hp.le⟩
  have hJ1 : MemWkpLoc p Ω 1 J :=
    memWkpLoc_succ_iff_of_isOpen.2 ⟨hc.memLpLoc_coeff, DJ, hc.hasWeakFDerivOn,
      memWkpLoc_zero_iff.2 hc.memLpLoc_deriv⟩
  have hJinf : MemLpLoc ∞ Ω J := hJ1.memLpLoc_of_holderTriple hp2 le_rfl
  have hclm {p₁ q₁ : ℝ≥0∞} {A : ℂ → V →L[ℝ] V} {w : ℂ → V} (hA : MemLpLoc p₁ Ω A)
      (hw : MemLpLoc q₁ Ω w) (h : p₁⁻¹ + q₁⁻¹ ≤ r⁻¹) : MemLpLoc r Ω (fun z => A z (w z)) := by
    have : ENNReal.HolderTriple p₁ q₁ (p₁⁻¹ + q₁⁻¹)⁻¹ := ⟨(inv_inv _).symm⟩
    have hrle : r ≤ (p₁⁻¹ + q₁⁻¹)⁻¹ := by rw [← inv_inv r]; exact ENNReal.inv_le_inv.2 h
    refine memLpLoc_iff.2 fun K hKΩ hK => ?_
    have : IsFiniteMeasure (volume.restrict K) := isFiniteMeasure_restrict.2 hK.measure_lt_top.ne
    exact ((ContinuousLinearMap.id ℝ (V →L[ℝ] V)).memLp_of_bilin (p₁⁻¹ + q₁⁻¹)⁻¹
      (memLpLoc_iff.1 hA K hKΩ hK) (memLpLoc_iff.1 hw K hKΩ hK)).mono_exponent hrle
  have hDJIp : MemLpLoc p Ω (fun z => DJ z I) :=
    hc.memLpLoc_deriv.clm_comp (G := V →L[ℝ] V) (ContinuousLinearMap.apply ℝ (V →L[ℝ] V) I)
  have hDJ1p : MemLpLoc p Ω (fun z => DJ z 1) :=
    hc.memLpLoc_deriv.clm_comp (G := V →L[ℝ] V) (ContinuousLinearMap.apply ℝ (V →L[ℝ] V) 1)
  have hSξ : MemLpLoc r Ω (fun z => S z (ξ z)) := hclm hc.memLpLoc_zeroth hsol.memLpLoc hpqr
  have hf : MemLpLoc r Ω (fun z => η z + DJ z I (ξ z) - S z (ξ z)) :=
    (hη.add (hclm hDJIp hsol.memLpLoc hpqr)).sub hSξ
  have hg : MemLpLoc r Ω (fun z => -J z (η z) - DJ z 1 (ξ z) + J z (S z (ξ z))) :=
    ((hclm hJinf hη (by simp)).neg.sub (hclm hDJ1p hsol.memLpLoc hpqr)).add
      (hclm hJinf hSξ (by simp))
  exact memWkpLoc_one_of_forall_integral_laplacian_smul_eq hr hr_top
    (hsol.memLpLoc.locallyIntegrableOn hq1 Ω.isOpen.isLocallyClosed) hf hg
    (hc.forall_integral_laplacian_smul_eq hJinf hp.le ENNReal.coe_ne_top hpq hJsq hsol)

/-- One Sobolev-embedding bootstrap step for `IsWeakCRSolution`: starting from `ξ ∈ L^{q₀}_loc`
with `1/p + 1/q₀ < 1`, either we immediately reach `ξ ∈ W^{1,q}_loc(Ω)` (including whenever the
intermediate exponent `r = (1/p + 1/q₀)⁻¹` satisfies `r ≥ 2`), or we upgrade to `ξ ∈ L^{q₁}_loc`
with `1/q₁ = 1/q₀ - (1/2 - 1/p)`. -/
private theorem memWkpLoc_one_step [FiniteDimensional ℝ V] {p q q₀ : ℝ≥0}
    (hc : IsSobolevCRCoefficients p Ω J DJ S) (hp : 2 < p) (hq : 1 < q) (hqp : q ≤ p)
    (hq₀0 : (0 : ℝ) < q₀) (hpq₀R : (p : ℝ)⁻¹ + (q₀ : ℝ)⁻¹ < 1)
    (hJsq : ∀ᵐ z ∂volume.restrict Ω, J z * J z = -1)
    (hη : MemLpLoc q Ω η) (hsol : IsWeakCRSolution q₀ Ω J DJ S ξ η) :
    MemWkpLoc q Ω 1 ξ ∨
      ∃ q₁ : ℝ≥0, (0 : ℝ) < q₁ ∧ MemLpLoc q₁ Ω ξ ∧
        (q₁ : ℝ)⁻¹ = (q₀ : ℝ)⁻¹ - (2⁻¹ - (p : ℝ)⁻¹) := by
  have hpR : (2 : ℝ) < p := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < p := by linarith
  have finish_gt_two {s : ℝ≥0} (hs2 : (2 : ℝ) < s) (hξs : MemWkpLoc s Ω 1 ξ) :
      MemWkpLoc q Ω 1 ξ := by
    have : Fact (1 ≤ (s : ℝ≥0∞)) := ⟨by exact_mod_cast (by linarith : (1 : ℝ) ≤ s)⟩
    have hξinf : MemLpLoc ∞ Ω ξ := hξs.memLpLoc_of_holderTriple (by exact_mod_cast hs2) le_rfl
    have hqp_enn : (q : ℝ≥0∞) ≤ p := by exact_mod_cast hqp
    exact hc.memWkpLoc_one_of_isWeakCRSolution_of_le (by exact_mod_cast hp) ENNReal.coe_ne_top
      (by exact_mod_cast hq) ENNReal.coe_ne_top (by simpa using ENNReal.inv_le_inv.2 hqp_enn) hJsq
      (isWeakCRSolution_iff.2 ⟨hξinf, hsol.locallyIntegrableOn, (isWeakCRSolution_iff.1 hsol).2.2⟩)
      hη
  have step_to_r {a : ℝ≥0} (ha0 : (0 : ℝ) < a) (hpa : (p : ℝ)⁻¹ + (a : ℝ)⁻¹ < 1)
      (hsola : IsWeakCRSolution a Ω J DJ S ξ η) :
      let r : ℝ≥0 := ⟨((p : ℝ)⁻¹ + (a : ℝ)⁻¹)⁻¹, by positivity⟩
      MemWkpLoc q Ω 1 ξ ∨ MemWkpLoc r Ω 1 ξ := by
    intro r
    have hr_coe : (r : ℝ) = ((p : ℝ)⁻¹ + (a : ℝ)⁻¹)⁻¹ := rfl
    have hr_inv : (r : ℝ)⁻¹ = (p : ℝ)⁻¹ + (a : ℝ)⁻¹ := by rw [hr_coe, inv_inv]
    have hr1 : (1 : ℝ) < r := by rw [hr_coe]; exact one_lt_inv_iff₀.2 ⟨by positivity, hpa⟩
    have hr_enn : (p : ℝ≥0∞)⁻¹ + (a : ℝ≥0∞)⁻¹ = (r : ℝ≥0∞)⁻¹ := by
      rw [← ENNReal.coe_inv (by exact_mod_cast hp0.ne'),
        ← ENNReal.coe_inv (by exact_mod_cast ha0.ne'),
        ← ENNReal.coe_inv (by exact_mod_cast (by linarith : (0 : ℝ) < r).ne'), ← ENNReal.coe_add]
      congr 1; ext; exact hr_inv.symm
    by_cases hqr : q ≤ r
    · refine Or.inl (hc.memWkpLoc_one_of_isWeakCRSolution_of_le (by exact_mod_cast hp)
        ENNReal.coe_ne_top (by exact_mod_cast hq) ENNReal.coe_ne_top ?_ hJsq hsola hη)
      rw [hr_enn]; exact ENNReal.inv_le_inv.2 (by exact_mod_cast hqr)
    · exact Or.inr (hc.memWkpLoc_one_of_isWeakCRSolution_of_le (by exact_mod_cast hp)
        ENNReal.coe_ne_top (by exact_mod_cast hr1) ENNReal.coe_ne_top hr_enn.le hJsq hsola
        (hη.mono_exponent (by exact_mod_cast (not_le.1 hqr).le)))
  set r : ℝ≥0 := ⟨((p : ℝ)⁻¹ + (q₀ : ℝ)⁻¹)⁻¹, by positivity⟩
  have hr_coe : (r : ℝ) = ((p : ℝ)⁻¹ + (q₀ : ℝ)⁻¹)⁻¹ := rfl
  have hr_inv : (r : ℝ)⁻¹ = (p : ℝ)⁻¹ + (q₀ : ℝ)⁻¹ := by rw [hr_coe, inv_inv]
  have hr1 : (1 : ℝ) < r := by rw [hr_coe]; exact one_lt_inv_iff₀.2 ⟨by positivity, hpq₀R⟩
  rcases step_to_r hq₀0 hpq₀R hsol with hdone | hξr
  · exact Or.inl hdone
  rcases lt_trichotomy (r : ℝ) 2 with hr2 | hr2 | hr2
  · have hsub : (0 : ℝ) < (r : ℝ)⁻¹ - 2⁻¹ := sub_pos.2 (inv_strictAnti₀ (by linarith) hr2)
    set q₁ : ℝ≥0 := ⟨((r : ℝ)⁻¹ - 2⁻¹)⁻¹, by positivity⟩
    have hq₁_coe : (q₁ : ℝ) = ((r : ℝ)⁻¹ - 2⁻¹)⁻¹ := rfl
    have hq₁_inv : (q₁ : ℝ)⁻¹ = (r : ℝ)⁻¹ - 2⁻¹ := by rw [hq₁_coe, inv_inv]
    have hq₁0 : (0 : ℝ) < q₁ := by rw [hq₁_coe]; positivity
    have hrq₁ : r ≤ q₁ := by
      rw [← NNReal.coe_le_coe, ← inv_le_inv₀ hq₁0 (by linarith), hq₁_inv]; linarith
    have hξq₁ : MemLpLoc q₁ Ω ξ :=
      hξr.memLpLoc_of_inv_sub_inv_le (by exact_mod_cast hr1.le) hrq₁ (by rw [hq₁_inv]; linarith)
    exact Or.inr ⟨q₁, hq₁0, hξq₁, by linarith [hq₁_inv, hr_inv]⟩
  · -- Critical case `r = 2`: embed into a large finite `q₁` so the next step has `r₂ > 2`.
    have hδ : (0 : ℝ) < 2⁻¹ - (p : ℝ)⁻¹ := sub_pos.2 (inv_strictAnti₀ (by positivity) hpR)
    set q₁ : ℝ≥0 := ⟨((2⁻¹ - (p : ℝ)⁻¹) / 2)⁻¹, by positivity⟩
    have hq₁_coe : (q₁ : ℝ) = ((2⁻¹ - (p : ℝ)⁻¹) / 2)⁻¹ := rfl
    have hq₁_inv : (q₁ : ℝ)⁻¹ = (2⁻¹ - (p : ℝ)⁻¹) / 2 := by rw [hq₁_coe, inv_inv]
    have hq₁0 : (0 : ℝ) < q₁ := by rw [hq₁_coe]; positivity
    have hrq₁ : r ≤ q₁ := by
      rw [← NNReal.coe_le_coe, ← inv_le_inv₀ hq₁0 (by linarith), hr2, hq₁_inv]
      linarith [inv_pos.2 hp0]
    have hgap : (r : ℝ)⁻¹ - (q₁ : ℝ)⁻¹ ≤ 2⁻¹ := by rw [hr2, hq₁_inv]; linarith
    have hξq₁ : MemLpLoc q₁ Ω ξ :=
      hξr.memLpLoc_of_inv_sub_inv_le (by exact_mod_cast hr1.le) hrq₁ hgap
    have hpq₁ : (p : ℝ)⁻¹ + (q₁ : ℝ)⁻¹ < 2⁻¹ := by linarith [hq₁_inv, hδ]
    have hsol₁ : IsWeakCRSolution q₁ Ω J DJ S ξ η :=
      isWeakCRSolution_iff.2 ⟨hξq₁, hsol.locallyIntegrableOn, (isWeakCRSolution_iff.1 hsol).2.2⟩
    rcases step_to_r hq₁0 (by linarith) hsol₁ with hdone | hξr₂
    · exact Or.inl hdone
    · refine Or.inl (finish_gt_two ?_ hξr₂)
      exact (lt_inv_comm₀ (by positivity) (by positivity)).1 (by simpa using hpq₁)
  · exact Or.inl (finish_gt_two hr2 hξr)

/-- **Order-zero interior regularity (McDuff–Salamon Lemma B.4.6).** Let `2 < p < ∞`, `1 < q ≤ p`,
and let `q₀` satisfy `1/p + 1/q₀ < 1`. For Sobolev coefficients `(J, DJ, S)` of class `p` with
`J² = -1` almost everywhere, any weak solution `ξ ∈ L^{q₀}_loc` of `∂_s ξ + J ∂_t ξ + S ξ = η`
with `η ∈ L^q_loc` belongs to `W^{1,q}_loc(Ω)`. -/
theorem IsSobolevCRCoefficients.memWkpLoc_one_of_isWeakCRSolution [FiniteDimensional ℝ V]
    (hc : IsSobolevCRCoefficients p Ω J DJ S) (hp : 2 < p) (hp_top : p ≠ ⊤)
    (hpq₀ : p⁻¹ + q₀⁻¹ < 1) (hq : 1 < q) (hqp : q ≤ p)
    (hJsq : ∀ᵐ z ∂volume.restrict Ω, J z * J z = -1)
    (hsol : IsWeakCRSolution q₀ Ω J DJ S ξ η) (hη : MemLpLoc q Ω η) :
    MemWkpLoc q Ω 1 ξ := by
  have hq_top : q ≠ ⊤ := ne_top_of_le_ne_top hp_top hqp
  rcases eq_or_ne q₀ ⊤ with rfl | hq₀_top
  · refine hc.memWkpLoc_one_of_isWeakCRSolution_of_le hp hp_top hq hq_top ?_ hJsq hsol hη
    simpa using ENNReal.inv_le_inv.2 hqp
  lift p to ℝ≥0 using hp_top
  lift q to ℝ≥0 using hq_top
  lift q₀ to ℝ≥0 using hq₀_top
  have hpN : 2 < p := by exact_mod_cast hp
  have hqN : 1 < q := by exact_mod_cast hq
  have hqpN : q ≤ p := by exact_mod_cast hqp
  have hpR : (2 : ℝ) < p := by exact_mod_cast hpN
  have hp0 : (0 : ℝ) < p := by linarith
  have hδ : (0 : ℝ) < 2⁻¹ - (p : ℝ)⁻¹ := sub_pos.2 (inv_strictAnti₀ (by positivity) hpR)
  have hq₀0 : (0 : ℝ) < q₀ := by
    by_contra h
    have h0 : q₀ = 0 := le_antisymm (by exact_mod_cast not_lt.1 h) bot_le
    simp [h0] at hpq₀
  have hpq₀R : (p : ℝ)⁻¹ + (q₀ : ℝ)⁻¹ < 1 := by
    rw [← ENNReal.coe_inv (by exact_mod_cast hp0.ne'),
      ← ENNReal.coe_inv (by exact_mod_cast hq₀0.ne'), ← ENNReal.coe_add] at hpq₀
    have h' : (p⁻¹ + q₀⁻¹ : ℝ≥0) < 1 := by exact_mod_cast hpq₀
    exact_mod_cast h'
  -- Each Sobolev step lowers `1/q₀` by `δ = 1/2 - 1/p > 0`, terminating in finitely many steps.
  have hind : ∀ n : ℕ, ∀ a : ℝ≥0, (0 : ℝ) < a → (p : ℝ)⁻¹ + (a : ℝ)⁻¹ < 1 →
      (a : ℝ)⁻¹ < n * (2⁻¹ - (p : ℝ)⁻¹) →
      IsWeakCRSolution a Ω J DJ S ξ η → MemWkpLoc q Ω 1 ξ := by
    intro n
    induction n with
    | zero =>
      intro a ha0 _ hlt _
      have : (0 : ℝ) < (a : ℝ)⁻¹ := inv_pos.2 ha0
      linarith
    | succ n ih =>
      intro a ha0 hpa hlt hsola
      rcases memWkpLoc_one_step hc hpN hqN hqpN ha0 hpa hJsq hη hsola with
        hdone | ⟨q₁, hq₁0, hξ₁, hq₁_inv⟩
      · exact hdone
      · refine ih q₁ hq₁0 (by linarith) (by push_cast at hlt; linarith) ?_
        exact isWeakCRSolution_iff.2
          ⟨hξ₁, hsol.locallyIntegrableOn, (isWeakCRSolution_iff.1 hsol).2.2⟩
  obtain ⟨n, hn⟩ := exists_nat_gt ((q₀ : ℝ)⁻¹ / (2⁻¹ - (p : ℝ)⁻¹))
  exact hind n q₀ hq₀0 hpq₀R ((div_lt_iff₀ hδ).1 hn) hsol

end TauCeti
