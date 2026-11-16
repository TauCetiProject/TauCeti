/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Laplacian
public import TauCeti.Analysis.Complex.CauchyRiemann.RoughCoefficients.Weak
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.ProdLp
import TauCeti.Analysis.Calculus.BumpFunction.Convolution
import TauCeti.Analysis.Complex.CauchyRiemann.RoughCoefficients.Differentiated
import TauCeti.Analysis.Complex.OperatorNorm
import TauCeti.Analysis.Complex.Wirtinger.DivergenceLaplace
import TauCeti.Analysis.Convolution.Basic
import TauCeti.Analysis.Distribution.TestFunction.Basic
import TauCeti.Analysis.Distribution.TestFunction.Inner
import TauCeti.Analysis.Distribution.TestFunction.LineDeriv
import TauCeti.Analysis.Sobolev.Local.Morrey.Higher
import TauCeti.Analysis.Sobolev.Local.Multiplication.Higher
import TauCeti.Analysis.Sobolev.Local.SobolevEmbedding
import TauCeti.Analysis.Sobolev.Mollification.Interior
import TauCeti.Analysis.Sobolev.WeakDeriv.Bilinear.Holder
import TauCeti.Analysis.Sobolev.WeakDeriv.Convolution
import TauCeti.Data.ENNReal.Holder

/-!
# Interior Sobolev regularity for Cauchy–Riemann operators with Sobolev coefficients

Let `Ω ⊆ ℂ` be open and let `V` be a real Hilbert space (finite-dimensional for the Sobolev
regularity theorems). Consider the linear Cauchy–Riemann operator `D ξ = ∂_s ξ + J ∂_t ξ + S ξ`
with Sobolev coefficients `J ∈ W^{1,p}_loc(Ω)` and `S ∈ Lᵖ_loc(Ω)` satisfying `J² = -1` almost
everywhere on `Ω`.

The argument follows McDuff–Salamon, Appendix B.4 (Lemma B.4.6 and Proposition B.4.9):

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
3. **Higher-order regularity (Proposition B.4.9)**
   (`TauCeti.memWkpLoc_succ_of_isWeakCRSolution`).
   For `k ≥ 1`, knowing `ξ ∈ W^{k,q}_loc(Ω)` implies `ξ ∈ W^{1,q}_loc(Ω)` satisfies the strong
   equation almost everywhere. Testing against `J_nᵀ φ` and mollifying shows that the partial
   derivative pair `Ξ = (∂_s ξ, ∂_t ξ)` in `WithLp 2 (V × V)` is itself a weak solution of the
   differentiated system `∂_s Ξ + diag(J, J) ∂_t Ξ + S₂ Ξ = η₂` without requiring a priori `W^{2,q}`
   regularity. Induction on `k` then gives `ξ ∈ W^{k+1,q}_loc(Ω)`.
4. **Normed-space and smooth-coefficient corollaries.**
   Transporting along a continuous linear equivalence `V ≃L[ℝ] EuclideanSpace ℝ (Fin d)` removes
   the Hilbert-space hypothesis for `W^{1,q}_loc` strong solutions
   (`TauCeti.memWkpLoc_succ_of_ae_cauchyRiemann`) and homogeneous linear weak solutions
   (`TauCeti.IsWeakLinearCauchyRiemannOn.memWkpLoc_succ`). For smooth `J, S, η`, combining all
   orders with Morrey's embedding gives a `C^∞` representative
   (`TauCeti.exists_contDiffOn_infty_ae_eq_of_isWeakCRSolution`).

## Main declarations

* `TauCeti.IsSobolevCRCoefficients.forall_integral_laplacian_smul_eq`: divergence-form Laplace
  reduction `Δ ξ = ∂_s f + ∂_t g` weakly on `Ω`.
* `TauCeti.IsSobolevCRCoefficients.memWkpLoc_one_of_isWeakCRSolution_of_le`: one-step `L^{q₀}` to
  `W^{1,r}` regularity for `1/p + 1/q₀ ≤ 1/r`.
* `TauCeti.IsSobolevCRCoefficients.memWkpLoc_one_of_isWeakCRSolution`: McDuff–Salamon Lemma B.4.6.
* `TauCeti.memWkpLoc_succ_of_isWeakCRSolution`: McDuff–Salamon Proposition B.4.9.
* `TauCeti.memWkpLoc_succ_of_ae_cauchyRiemann`: higher-order regularity for `W^{1,q}_loc` strong
  solutions in an arbitrary finite-dimensional real normed space.
* `TauCeti.IsWeakLinearCauchyRiemannOn.memWkpLoc_succ`: higher-order regularity for homogeneous
  linear weak solutions.
* `TauCeti.exists_contDiffOn_infty_ae_eq_of_isWeakCRSolution`: smooth-coefficient hypoellipticity.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix B.4 (Lemma B.4.6 and Proposition B.4.9).
-/

public noncomputable section

open Complex Filter MeasureTheory Set TopologicalSpace
open scoped Distributions ENNReal InnerProductSpace Laplacian LineDeriv NNReal Topology ContDiff
open scoped Convolution

namespace TauCeti

/-! ### Mollification helpers for the formal adjoint pairing -/

section MollifyHelpers

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  {Ω : Opens ℂ}

/-- Evaluating the Hilbert adjoint at a fixed vector `v : V`, as a continuous linear map
`(V →L[ℝ] V) →L[ℝ] V`. -/
private def adjointApplyL (v : V) : (V →L[ℝ] V) →L[ℝ] V :=
  (ContinuousLinearMap.apply ℝ V v).comp
    (ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := V)
      (F := V)).toContinuousLinearEquiv.toContinuousLinearMap

private theorem adjointApplyL_apply (v : V) (A : V →L[ℝ] V) :
    adjointApplyL v A = ContinuousLinearMap.adjoint A v := rfl

/-- Applying `adjointApplyL v` commutes with normalized-bump mollification of `W'.indicator J`. -/
private theorem adjointApplyL_mollify_eq (v : V) (ρ : ContDiffBump (0 : ℂ)) {W' : Opens ℂ}
    {J : ℂ → V →L[ℝ] V} (hJ : MemLp J ∞ (volume.restrict (W' : Set ℂ))) (z : ℂ) :
    ContinuousLinearMap.adjoint ((ρ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
      ((W' : Set ℂ).indicator J)) z) v =
      (ρ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
        ((W' : Set ℂ).indicator (fun x => ContinuousLinearMap.adjoint (J x) v))) z := by
  have hloc : LocallyIntegrable ((W' : Set ℂ).indicator J) volume :=
    ((memLp_indicator_iff_restrict W'.isOpen.measurableSet.nullMeasurableSet).2
      hJ).locallyIntegrable le_top
  have hex := (ρ.hasCompactSupport_normed (μ := volume)).convolutionExists_left
    (ContinuousLinearMap.lsmul ℝ ℝ) (ρ.contDiff_normed (n := (⊤ : ℕ∞))).continuous hloc z
  rw [← adjointApplyL_apply v, ← (adjointApplyL v).convolution_lsmul_comp_comm hex]
  congr 1; ext x
  by_cases hx : x ∈ (W' : Set ℂ) <;> simp [indicator, hx, adjointApplyL_apply]

/-- On `W ⋐ W'`, evaluating `(fderiv ℝ J_n z w)ᵀ v` equals the mollification of
`W'.indicator (fun x => (DJ x w)ᵀ v)`. -/
private theorem adjoint_fderiv_mollify_eq (v : V) (w : ℂ) (ρ : ContDiffBump (0 : ℂ))
    {W W' : Opens ℂ} {p : ℝ≥0∞} (hp1 : 1 ≤ p)
    (hsupp : ∀ z ∈ (W : Set ℂ), ∀ y ∈ tsupport (ρ.normed volume), z - y ∈ (W' : Set ℂ))
    (hW'c : IsCompact (closure (W' : Set ℂ))) (hW'Ω : closure (W' : Set ℂ) ⊆ Ω)
    {J : ℂ → V →L[ℝ] V} {DJ : ℂ → ℂ →L[ℝ] V →L[ℝ] V}
    (hJ : HasWeakFDerivOn volume Ω J DJ) (hJinf : MemLp J ∞ (volume.restrict (W' : Set ℂ)))
    (hDJp : MemLpLoc p Ω DJ) {z : ℂ} (hz : z ∈ (W : Set ℂ)) :
    ContinuousLinearMap.adjoint (fderiv ℝ (ρ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
      ((W' : Set ℂ).indicator J)) z w) v =
      (ρ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
        ((W' : Set ℂ).indicator (fun x => ContinuousLinearMap.adjoint (DJ x w) v))) z := by
  have hloc : LocallyIntegrable ((W' : Set ℂ).indicator J) volume :=
    ((memLp_indicator_iff_restrict W'.isOpen.measurableSet.nullMeasurableSet).2
      hJinf).locallyIntegrable le_top
  have hJsmooth : ContDiff ℝ ∞ (ρ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
      ((W' : Set ℂ).indicator J)) :=
    (ρ.hasCompactSupport_normed (μ := volume)).contDiff_convolution_left
      (ContinuousLinearMap.lsmul ℝ ℝ) (ρ.contDiff_normed (n := (⊤ : ℕ∞))) hloc
  have hL : (fun x => adjointApplyL v ((ρ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
      ((W' : Set ℂ).indicator J)) x)) =
      ρ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
        ((W' : Set ℂ).indicator (fun x => ContinuousLinearMap.adjoint (J x) v)) :=
    funext fun x => adjointApplyL_mollify_eq v ρ hJinf x
  have h1 : fderiv ℝ (fun x => adjointApplyL v
      ((ρ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ((W' : Set ℂ).indicator J)) x))
      z w = ContinuousLinearMap.adjoint (fderiv ℝ
        (ρ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
          ((W' : Set ℂ).indicator J)) z w) v := by
    have hd := ((adjointApplyL v).hasFDerivAt.comp z
      (hJsmooth.differentiable (by simp) z).hasFDerivAt).fderiv
    simpa [Function.comp_def, adjointApplyL_apply] using congr($hd w)
  rw [← h1, hL]
  have hJv : HasWeakFDerivOn volume W' (fun x => adjointApplyL v (J x))
      (fun x => (adjointApplyL v).comp (DJ x)) :=
    (hJ.mono (subset_closure.trans hW'Ω)).clm_comp (adjointApplyL v)
  have hJv_inf : MemLp (fun x => adjointApplyL v (J x)) ∞ (volume.restrict (W' : Set ℂ)) :=
    (adjointApplyL v).comp_memLp' hJinf
  have hDJv_loc : MemLpLoc p Ω (fun x => (adjointApplyL v).comp (DJ x)) := by
    rw [ContinuousLinearMap.fun_eq_smulRightL_reCLM_add_smulRightL_imCLM
      (fun x => (adjointApplyL v).comp (DJ x))]
    have h1' : MemLpLoc p Ω (fun x => ((adjointApplyL v).comp (DJ x)) 1) :=
      (hDJp.clm_comp (G := V →L[ℝ] V) (ContinuousLinearMap.apply ℝ (V →L[ℝ] V) 1)).clm_comp
        (adjointApplyL v)
    have hI' : MemLpLoc p Ω (fun x => ((adjointApplyL v).comp (DJ x)) I) :=
      (hDJp.clm_comp (G := V →L[ℝ] V) (ContinuousLinearMap.apply ℝ (V →L[ℝ] V) I)).clm_comp
        (adjointApplyL v)
    exact (h1'.clm_comp (ContinuousLinearMap.smulRightL ℝ ℂ V Complex.reCLM)).add
      (hI'.clm_comp (ContinuousLinearMap.smulRightL ℝ ℂ V Complex.imCLM))
  have hDJv_p : MemLp (fun x => (adjointApplyL v).comp (DJ x)) p (volume.restrict (W' : Set ℂ)) :=
    hDJv_loc.memLp_of_closure_subset hW'c hW'Ω
  have hf := hJv.fderiv_indicator_convolution_right hJv_inf hDJv_p le_top hp1 (ρ.normed volume)
    (ρ.contDiff_normed (n := (⊤ : ℕ∞))) (ρ.hasCompactSupport_normed (μ := volume)) z (hsupp z hz)
  simp only [convolution_flip] at hf
  have hcomp : (fun x => adjointApplyL v (J x)) =
      fun x => ContinuousLinearMap.adjoint (J x) v := rfl
  rw [hcomp] at hf
  rw [hf]
  have hlocD : LocallyIntegrable
      ((W' : Set ℂ).indicator (fun x => (adjointApplyL v).comp (DJ x))) volume :=
    ((memLp_indicator_iff_restrict W'.isOpen.measurableSet.nullMeasurableSet).2
      hDJv_p).locallyIntegrable hp1
  have hexD := (ρ.hasCompactSupport_normed (μ := volume)).convolutionExists_left
    (ContinuousLinearMap.lsmul ℝ ℝ) (ρ.contDiff_normed (n := (⊤ : ℕ∞))).continuous hlocD z
  rw [← ContinuousLinearMap.apply_apply (𝕜 := ℝ) (v := w),
    ← (ContinuousLinearMap.apply ℝ V w).convolution_lsmul_comp_comm hexD]
  congr 1; ext x
  by_cases hx : x ∈ (W' : Set ℂ) <;> simp [indicator, hx, adjointApplyL_apply]

/-- Passing to the limit in `∫ ⟪α z • v, (ρ_n ⋆ W'.indicator J) z (u z)⟫` for a scalar test
function `α ∈ 𝓓(Ω, ℝ)` supported in `W ⊆ W'`, fixed `v ∈ V`, bounded `J`, and locally integrable
`u`. Works in any real Hilbert space without finite-dimensionality. -/
private theorem tendsto_integral_smul_inner_mollify {W W' : Opens ℂ} (hWW' : (W : Set ℂ) ⊆ W')
    {ρ : ℕ → ContDiffBump (0 : ℂ)} (hρ : Tendsto (fun n => (ρ n).rOut) atTop (𝓝 0))
    {J : ℂ → V →L[ℝ] V} (hJ : MemLp J ∞ (volume.restrict (W' : Set ℂ)))
    (α : 𝓓(Ω, ℝ)) (hαW : tsupport (α : ℂ → ℝ) ⊆ W) (v : V)
    {u : ℂ → V} (hu : LocallyIntegrableOn u Ω volume) :
    Tendsto (fun n => ∫ z, ⟪(α : ℂ → ℝ) z • v,
        ((ρ n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
          ((W' : Set ℂ).indicator J)) z (u z)⟫_ℝ)
      atTop (𝓝 (∫ z, ⟪(α : ℂ → ℝ) z • v, J z (u z)⟫_ℝ)) := by
  let B : V →L[ℝ] V →L[ℝ] ℝ := innerSL ℝ
  have hB (x y : V) : B x y = ⟪x, y⟫_ℝ := rfl
  have hf_inf : MemLp ((W' : Set ℂ).indicator (fun x => ContinuousLinearMap.adjoint (J x) v))
      ∞ volume :=
    (memLp_indicator_iff_restrict W'.isOpen.measurableSet.nullMeasurableSet).2
      ((adjointApplyL v).comp_memLp' hJ)
  have hlim := B.tendsto_integral_bilin_normed_convolution_top hρ (α.integrable_smul hu) hf_inf
  have hEq_lim : (∫ z, B ((α : ℂ → ℝ) z • u z)
      ((W' : Set ℂ).indicator (fun x => ContinuousLinearMap.adjoint (J x) v) z)) =
      ∫ z, ⟪(α : ℂ → ℝ) z • v, J z (u z)⟫_ℝ := by
    refine integral_congr_ae (.of_forall fun z => ?_)
    dsimp only
    by_cases hz : z ∈ tsupport (α : ℂ → ℝ)
    · rw [hB, indicator_of_mem (hWW' (hαW hz)), ContinuousLinearMap.adjoint_inner_right,
        map_smul, inner_smul_left, inner_smul_left, RCLike.conj_to_real, real_inner_comm]
    · simp [image_eq_zero_of_notMem_tsupport hz]
  rw [← hEq_lim]
  refine hlim.congr fun n => integral_congr_ae (.of_forall fun z => ?_)
  dsimp only
  rw [hB, ← adjointApplyL_mollify_eq v (ρ n) hJ z, ContinuousLinearMap.adjoint_inner_right,
    map_smul, inner_smul_left, inner_smul_left, RCLike.conj_to_real, real_inner_comm]

/-- Passing to the limit in `∫ ⟪α z • v, fderiv ℝ J_n z w (u z)⟫` for a scalar test function
`α ∈ 𝓓(Ω, ℝ)` supported in `W ⊆ W'`, fixed `v ∈ V`, `J ∈ W^{1,p}` bounded on `W'`, and
`u ∈ L^q_loc(Ω)` with `p⁻¹ + q⁻¹ ≤ 1`. -/
private theorem tendsto_integral_smul_inner_fderiv_mollify {W W' : Opens ℂ}
    (hWW' : (W : Set ℂ) ⊆ W') {p q : ℝ≥0∞} (hp1 : 1 ≤ p) (hpq : p⁻¹ + q⁻¹ ≤ 1)
    {ρ : ℕ → ContDiffBump (0 : ℂ)} (hρ : Tendsto (fun n => (ρ n).rOut) atTop (𝓝 0))
    (hsupp : ∀ n, ∀ z ∈ (W : Set ℂ), ∀ y ∈ tsupport ((ρ n).normed volume), z - y ∈ (W' : Set ℂ))
    (hW'c : IsCompact (closure (W' : Set ℂ))) (hW'Ω : closure (W' : Set ℂ) ⊆ Ω)
    {J : ℂ → V →L[ℝ] V} {DJ : ℂ → ℂ →L[ℝ] V →L[ℝ] V}
    (hJ : HasWeakFDerivOn volume Ω J DJ) (hJinf : MemLp J ∞ (volume.restrict (W' : Set ℂ)))
    (hDJp : MemLpLoc p Ω DJ) (α : 𝓓(Ω, ℝ)) (hαW : tsupport (α : ℂ → ℝ) ⊆ W) (v : V)
    {u : ℂ → V} (hu : MemLpLoc q Ω u) (w : ℂ) :
    Tendsto (fun n => ∫ z, ⟪(α : ℂ → ℝ) z • v, fderiv ℝ ((ρ n).normed volume ⋆[
        ContinuousLinearMap.lsmul ℝ ℝ, volume] ((W' : Set ℂ).indicator J)) z w (u z)⟫_ℝ)
      atTop (𝓝 (∫ z, ⟪(α : ℂ → ℝ) z • v, DJ z w (u z)⟫_ℝ)) := by
  let B : V →L[ℝ] V →L[ℝ] ℝ := innerSL ℝ
  have hB (x y : V) : B x y = ⟪x, y⟫_ℝ := rfl
  let p' : ℝ≥0∞ := (1 - p⁻¹)⁻¹
  have : p.HolderConjugate p' := by
    simpa only [ENNReal.HolderConjugate, inv_one] using ENNReal.HolderTriple.of_le hp1
  have hp'q : p' ≤ q := by
    have hinv : q⁻¹ ≤ 1 - p⁻¹ :=
      ENNReal.le_sub_of_add_le_left (ENNReal.inv_ne_top.2 (zero_lt_one.trans_le hp1).ne') hpq
    rw [← inv_inv q]
    exact ENNReal.inv_le_inv.2 hinv
  have ha_memLp : MemLp (fun z => (α : ℂ → ℝ) z • u z) p' volume := by
    have hα_top : MemLp (α : ℂ → ℝ) ∞ volume := by
      obtain ⟨C, hC⟩ := α.hasCompactSupport.exists_bound_of_continuousOn α.continuous.continuousOn
      refine memLp_top_of_bound α.continuous.aestronglyMeasurable (max C 0) (.of_forall fun z => ?_)
      by_cases hz : z ∈ tsupport (α : ℂ → ℝ)
      · exact (hC z hz).trans (le_max_left C 0)
      · simp [image_eq_zero_of_notMem_tsupport hz]
    have huK : MemLp ((tsupport (α : ℂ → ℝ)).indicator u) p' volume :=
      (memLp_indicator_iff_restrict (isClosed_tsupport _).measurableSet.nullMeasurableSet).2
        (memLpLoc_iff.1 (hu.mono_exponent hp'q) _ α.tsupport_subset α.hasCompactSupport)
    have : ENNReal.HolderTriple ∞ p' p' := ⟨by simp⟩
    refine ((ContinuousLinearMap.lsmul ℝ ℝ).memLp_of_bilin p' hα_top huK).ae_eq
      (.of_forall fun z => ?_)
    by_cases hz : z ∈ tsupport (α : ℂ → ℝ)
    · simp [indicator_of_mem hz]
    · simp [image_eq_zero_of_notMem_tsupport hz]
  have hDJw : MemLpLoc p Ω (fun x => DJ x w) :=
    hDJp.clm_comp (G := V →L[ℝ] V) (ContinuousLinearMap.apply ℝ (V →L[ℝ] V) w)
  have hf_p : MemLp ((W' : Set ℂ).indicator (fun x => ContinuousLinearMap.adjoint (DJ x w) v))
      p volume :=
    (memLp_indicator_iff_restrict W'.isOpen.measurableSet.nullMeasurableSet).2
      ((hDJw.clm_comp (adjointApplyL v)).memLp_of_closure_subset hW'c hW'Ω)
  have hlim := B.tendsto_integral_bilin_normed_convolution (p := p) (q := p') hρ ha_memLp hf_p
  have hEq_lim : (∫ z, B ((α : ℂ → ℝ) z • u z)
      ((W' : Set ℂ).indicator (fun x => ContinuousLinearMap.adjoint (DJ x w) v) z)) =
      ∫ z, ⟪(α : ℂ → ℝ) z • v, DJ z w (u z)⟫_ℝ := by
    refine integral_congr_ae (.of_forall fun z => ?_)
    dsimp only
    by_cases hz : z ∈ tsupport (α : ℂ → ℝ)
    · rw [hB, indicator_of_mem (hWW' (hαW hz)), ContinuousLinearMap.adjoint_inner_right,
        map_smul, inner_smul_left, inner_smul_left, RCLike.conj_to_real, real_inner_comm]
    · simp [image_eq_zero_of_notMem_tsupport hz]
  rw [← hEq_lim]
  refine hlim.congr fun n => integral_congr_ae (.of_forall fun z => ?_)
  dsimp only
  by_cases hz : z ∈ tsupport (α : ℂ → ℝ)
  · rw [hB, ← adjoint_fderiv_mollify_eq v w (ρ n) hp1 (hsupp n) hW'c hW'Ω hJ hJinf hDJp (hαW hz),
      ContinuousLinearMap.adjoint_inner_right, map_smul, inner_smul_left, inner_smul_left,
      RCLike.conj_to_real, real_inner_comm]
  · simp [image_eq_zero_of_notMem_tsupport hz]

end MollifyHelpers

/-! ### Divergence-form Laplace reduction and order-zero regularity -/

section OrderZero

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  {Ω : Opens ℂ} {p q q₀ r : ℝ≥0∞}
  {J S : ℂ → V →L[ℝ] V} {DJ : ℂ → ℂ →L[ℝ] V →L[ℝ] V} {ξ η : ℂ → V}

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

end OrderZero

/-! ### The weak differentiated system and higher-order regularity -/

section HigherOrder

section ProdL2

variable (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- Conjugating an operator on `V × V` by `WithLp.prodContinuousLinearEquiv 2 ℝ V V`. -/
private def conjProdL2L :
    (V × V →L[ℝ] V × V) →L[ℝ] (WithLp 2 (V × V) →L[ℝ] WithLp 2 (V × V)) :=
  (ContinuousLinearMap.compL ℝ (WithLp 2 (V × V)) (V × V) (WithLp 2 (V × V))
    (WithLp.prodContinuousLinearEquiv 2 ℝ V V).symm.toContinuousLinearMap).comp
    ((ContinuousLinearMap.compL ℝ (WithLp 2 (V × V)) (V × V) (V × V)).flip
      (WithLp.prodContinuousLinearEquiv 2 ℝ V V).toContinuousLinearMap)

private theorem conjProdL2L_apply {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (A : V × V →L[ℝ] V × V) (x : WithLp 2 (V × V)) :
    conjProdL2L V A x = WithLp.toLp 2 (A (WithLp.ofLp x)) := rfl

/-- The diagonal map `A ↦ conjProdL2L (A.prodMap A)` as a continuous linear map. -/
private def diagProdL2L :
    (V →L[ℝ] V) →L[ℝ] (WithLp 2 (V × V) →L[ℝ] WithLp 2 (V × V)) :=
  (conjProdL2L V).comp ((ContinuousLinearMap.prodMapL ℝ V V V V).comp
    ((ContinuousLinearMap.id ℝ (V →L[ℝ] V)).prod (ContinuousLinearMap.id ℝ (V →L[ℝ] V))))

private theorem diagProdL2L_apply {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (A : V →L[ℝ] V) (x : WithLp 2 (V × V)) :
    diagProdL2L V A x = WithLp.toLp 2 (A x.ofLp.1, A x.ofLp.2) := rfl

end ProdL2

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  {Ω : Opens ℂ}

omit [CompleteSpace V] in
/-- For any test function `ψ ∈ 𝓓(Ω, V)` and any weakly differentiable field `ξ` with weak
derivative `Dξ`, `∫ ⟪∂_s ψ, ∂_t ξ⟫ = ∫ ⟪∂_t ψ, ∂_s ξ⟫`. -/
private theorem integral_inner_fderiv_one_eq_fderiv_I [FiniteDimensional ℝ V]
    {ξ : ℂ → V} {Dξ : ℂ → ℂ →L[ℝ] V} (hξ : HasWeakFDerivOn volume Ω ξ Dξ) (ψ : 𝓓(Ω, V)) :
    ∫ z, ⟪fderiv ℝ (ψ : ℂ → V) z 1, Dξ z I⟫_ℝ =
      ∫ z, ⟪fderiv ℝ (ψ : ℂ → V) z I, Dξ z 1⟫_ℝ := by
  have h1 := (hξ.hasWeakLineDerivOn I).integral_inner_lineDeriv_eq_neg (∂_{(1 : ℂ)} ψ)
  have h2 := (hξ.hasWeakLineDerivOn 1).integral_inner_lineDeriv_eq_neg (∂_{I} ψ)
  simp only [TestFunction.lineDerivOp_apply_eq_fderiv] at h1 h2
  simp_rw [← TestFunction.lineDerivOp_apply] at h1 h2
  rw [TestFunction.lineDerivOp_comm] at h1
  linarith

/-- Scalar-test-function form of the commutator identity: for `α ∈ 𝓓(Ω, ℝ)` and `v ∈ V`,
`∫ ⟪(∂_s α) v, J ∂_t ξ⟫ + ∫ ⟪α v, (∂_s J) ∂_t ξ⟫ =
∫ ⟪(∂_t α) v, J ∂_s ξ⟫ + ∫ ⟪α v, (∂_t J) ∂_s ξ⟫`. -/
private theorem integral_comm_differentiated_smul [FiniteDimensional ℝ V] {p q : ℝ≥0∞}
    (hp1 : 1 ≤ p) (hpq : p⁻¹ + q⁻¹ ≤ 1)
    {J : ℂ → V →L[ℝ] V} {DJ : ℂ → ℂ →L[ℝ] V →L[ℝ] V}
    (hJ : HasWeakFDerivOn volume Ω J DJ) (hJinf : MemLpLoc ∞ Ω J) (hDJp : MemLpLoc p Ω DJ)
    {ξ : ℂ → V} {Dξ : ℂ → ℂ →L[ℝ] V} (hξ : HasWeakFDerivOn volume Ω ξ Dξ)
    (hDξq : MemLpLoc q Ω Dξ) (α : 𝓓(Ω, ℝ)) (v : V) :
    (∫ z, ⟪fderiv ℝ (α : ℂ → ℝ) z 1 • v, J z (Dξ z I)⟫_ℝ) +
      (∫ z, ⟪(α : ℂ → ℝ) z • v, DJ z 1 (Dξ z I)⟫_ℝ) =
    (∫ z, ⟪fderiv ℝ (α : ℂ → ℝ) z I • v, J z (Dξ z 1)⟫_ℝ) +
      ∫ z, ⟪(α : ℂ → ℝ) z • v, DJ z I (Dξ z 1)⟫_ℝ := by
  have hq1 : 1 ≤ q := ENNReal.inv_le_one.1 (le_add_self.trans hpq)
  have hloc := Ω.isOpen.isLocallyClosed
  obtain ⟨W, hαW, hWΩ, hWc⟩ :=
    Opens.exists_between_and_isCompact_closure α.hasCompactSupport α.tsupport_subset
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
  let ψ : ℕ → 𝓓(Ω, V) := fun n =>
    { toFun := fun z => (α : ℂ → ℝ) z • ContinuousLinearMap.adjoint (Jn n z) v
      contDiff' := α.contDiff.smul ((adjointApplyL v).contDiff.comp (hJn_smooth n))
      hasCompactSupport' := α.hasCompactSupport.smul_right
      tsupport_subset' := (tsupport_smul_subset_left _ _).trans α.tsupport_subset }
  have hDξ1q : MemLpLoc q Ω (fun z => Dξ z 1) := hDξq.clm_comp (ContinuousLinearMap.apply ℝ V 1)
  have hDξIq : MemLpLoc q Ω (fun z => Dξ z I) := hDξq.clm_comp (ContinuousLinearMap.apply ℝ V I)
  have hDξ1_loc := hDξ1q.locallyIntegrableOn hq1 hloc
  have hDξI_loc := hDξIq.locallyIntegrableOn hq1 hloc
  have hfderiv_ψ (n : ℕ) (z w : ℂ) :
      fderiv ℝ (ψ n : ℂ → V) z w =
        (α : ℂ → ℝ) z • ContinuousLinearMap.adjoint (fderiv ℝ (Jn n) z w) v +
          fderiv ℝ (α : ℂ → ℝ) z w • ContinuousLinearMap.adjoint (Jn n z) v := by
    have h1 := (α.contDiff.differentiable (by simp) z).hasFDerivAt
    have h2 := (adjointApplyL v).hasFDerivAt.comp z
      ((hJn_smooth n).differentiable (by simp) z).hasFDerivAt
    have hfun : ((α : ℂ → ℝ) • (adjointApplyL v ∘ Jn n)) = (ψ n : ℂ → V) := rfl
    have h3 := (hfun ▸ (h1.smul h2)).fderiv
    simpa [adjointApplyL_apply] using congr($h3 w)
  let α1 : 𝓓(Ω, ℝ) := ∂_{(1 : ℂ)} α
  let αI : 𝓓(Ω, ℝ) := ∂_{I} α
  have hintI (β : 𝓓(Ω, ℝ)) {u : ℂ → V} (hu : LocallyIntegrableOn u Ω volume) :
      Integrable (fun z => ⟪(β : ℂ → ℝ) z • v, u z⟫_ℝ) volume :=
    (TestFunction.postcompCLM (ContinuousLinearMap.toSpanSingleton ℝ v) β).integrable_inner hu
  have hEq (n : ℕ) :
      (∫ z, ⟪(α1 : ℂ → ℝ) z • v, Jn n z (Dξ z I)⟫_ℝ) +
        (∫ z, ⟪(α : ℂ → ℝ) z • v, fderiv ℝ (Jn n) z 1 (Dξ z I)⟫_ℝ) =
      (∫ z, ⟪(αI : ℂ → ℝ) z • v, Jn n z (Dξ z 1)⟫_ℝ) +
        ∫ z, ⟪(α : ℂ → ℝ) z • v, fderiv ℝ (Jn n) z I (Dξ z 1)⟫_ℝ := by
    have hcomm := integral_inner_fderiv_one_eq_fderiv_I hξ (ψ n)
    have hJn_loc {u : ℂ → V} (hu : LocallyIntegrableOn u Ω volume) :
        LocallyIntegrableOn (fun z => Jn n z (u z)) Ω volume :=
      ((hJn_smooth n).continuous.continuousOn.memLpLoc (p := ∞)).locallyIntegrableOn_clm_apply
        ((memLpLoc_one_iff_locallyIntegrableOn hloc).2 hu) (by simp) hloc
    have hfJn_loc (w : ℂ) {u : ℂ → V} (hu : LocallyIntegrableOn u Ω volume) :
        LocallyIntegrableOn (fun z => fderiv ℝ (Jn n) z w (u z)) Ω volume :=
      ((((hJn_smooth n).fderiv_right (m := ∞) (by simp)).continuous.clm_apply
        (continuous_const (y := w))).continuousOn.memLpLoc (p := ∞)).locallyIntegrableOn_clm_apply
        ((memLpLoc_one_iff_locallyIntegrableOn hloc).2 hu) (by simp) hloc
    have hdir (w : ℂ) (β : 𝓓(Ω, ℝ)) (hβ : ∀ z, (β : ℂ → ℝ) z = fderiv ℝ (α : ℂ → ℝ) z w)
        {u : ℂ → V} (hu : LocallyIntegrableOn u Ω volume) :
        ∫ z, ⟪fderiv ℝ (ψ n : ℂ → V) z w, u z⟫_ℝ =
          (∫ z, ⟪(α : ℂ → ℝ) z • v, fderiv ℝ (Jn n) z w (u z)⟫_ℝ) +
            ∫ z, ⟪(β : ℂ → ℝ) z • v, Jn n z (u z)⟫_ℝ := by
      have hpt (z : ℂ) : ⟪fderiv ℝ (ψ n : ℂ → V) z w, u z⟫_ℝ =
          ⟪(α : ℂ → ℝ) z • v, fderiv ℝ (Jn n) z w (u z)⟫_ℝ +
            ⟪(β : ℂ → ℝ) z • v, Jn n z (u z)⟫_ℝ := by
        simp only [hfderiv_ψ, inner_add_left, inner_smul_left, RCLike.conj_to_real,
          ContinuousLinearMap.adjoint_inner_left, hβ]
      simp_rw [hpt]
      exact integral_add (hintI α (hfJn_loc w hu)) (hintI β (hJn_loc hu))
    have hL := hdir 1 α1 (TestFunction.lineDerivOp_apply_eq_fderiv α 1) hDξI_loc
    have hR := hdir I αI (TestFunction.lineDerivOp_apply_eq_fderiv α I) hDξ1_loc
    linarith
  have l1 := tendsto_integral_smul_inner_mollify hWsubW' hρ hJW'_inf α1
    ((TestFunction.tsupport_lineDerivOp_subset α 1).trans hαW) v hDξI_loc
  have l2 := tendsto_integral_smul_inner_fderiv_mollify hWsubW' hp1 hpq hρ hsupp hW'c hW'Ω
    hJ hJW'_inf hDJp α hαW v hDξIq 1
  have l3 := tendsto_integral_smul_inner_mollify hWsubW' hρ hJW'_inf αI
    ((TestFunction.tsupport_lineDerivOp_subset α I).trans hαW) v hDξ1_loc
  have l4 := tendsto_integral_smul_inner_fderiv_mollify hWsubW' hp1 hpq hρ hsupp hW'c hW'Ω
    hJ hJW'_inf hDJp α hαW v hDξ1q I
  have hlim := tendsto_nhds_unique (l1.add l2) ((funext hEq) ▸ (l3.add l4))
  simpa only [α1, αI, TestFunction.lineDerivOp_apply_eq_fderiv] using hlim

/-- Key commutator identity for the first component of the weak differentiated system:
`∫ ⟪∂_s φ, J ∂_t ξ⟫ + ∫ ⟪φ, (∂_s J) ∂_t ξ⟫ = ∫ ⟪∂_t φ, J ∂_s ξ⟫ + ∫ ⟪φ, (∂_t J) ∂_s ξ⟫`. -/
private theorem integral_comm_differentiated [FiniteDimensional ℝ V] {p q : ℝ≥0∞}
    (hp1 : 1 ≤ p) (hpq : p⁻¹ + q⁻¹ ≤ 1)
    {J : ℂ → V →L[ℝ] V} {DJ : ℂ → ℂ →L[ℝ] V →L[ℝ] V}
    (hJ : HasWeakFDerivOn volume Ω J DJ) (hJinf : MemLpLoc ∞ Ω J) (hDJp : MemLpLoc p Ω DJ)
    {ξ : ℂ → V} {Dξ : ℂ → ℂ →L[ℝ] V} (hξ : HasWeakFDerivOn volume Ω ξ Dξ)
    (hDξq : MemLpLoc q Ω Dξ) (φ : 𝓓(Ω, V)) :
    (∫ z, ⟪fderiv ℝ (φ : ℂ → V) z 1, J z (Dξ z I)⟫_ℝ) +
      (∫ z, ⟪(φ : ℂ → V) z, DJ z 1 (Dξ z I)⟫_ℝ) =
    (∫ z, ⟪fderiv ℝ (φ : ℂ → V) z I, J z (Dξ z 1)⟫_ℝ) +
      ∫ z, ⟪(φ : ℂ → V) z, DJ z I (Dξ z 1)⟫_ℝ := by
  have hq1 : 1 ≤ q := ENNReal.inv_le_one.1 (le_add_self.trans hpq)
  have hloc := Ω.isOpen.isLocallyClosed
  let b := stdOrthonormalBasis ℝ V
  let α : Fin (Module.finrank ℝ V) → 𝓓(Ω, ℝ) :=
    fun i => TestFunction.postcompCLM (innerSL ℝ (b i)) φ
  have hφ_eq (z : ℂ) : (φ : ℂ → V) z = ∑ i, (α i : ℂ → ℝ) z • b i := by
    simpa [α, TestFunction.postcompCLM_apply] using (b.sum_repr' ((φ : ℂ → V) z)).symm
  have hfderiv_α (i : Fin (Module.finrank ℝ V)) (z w : ℂ) :
      fderiv ℝ (α i : ℂ → ℝ) z w = ⟪b i, fderiv ℝ (φ : ℂ → V) z w⟫_ℝ := by
    have h := ((innerSL ℝ (b i)).hasFDerivAt.comp z
      (φ.contDiff.differentiable (by simp) z).hasFDerivAt).fderiv
    simpa [α, TestFunction.postcompCLM_apply] using congr($h w)
  have hfderiv_φ_eq (z w : ℂ) :
      fderiv ℝ (φ : ℂ → V) z w = ∑ i, fderiv ℝ (α i : ℂ → ℝ) z w • b i := by
    simpa [hfderiv_α] using (b.sum_repr' (fderiv ℝ (φ : ℂ → V) z w)).symm
  have hDξ1q : MemLpLoc q Ω (fun z => Dξ z 1) := hDξq.clm_comp (ContinuousLinearMap.apply ℝ V 1)
  have hDξIq : MemLpLoc q Ω (fun z => Dξ z I) := hDξq.clm_comp (ContinuousLinearMap.apply ℝ V I)
  have hDJ1p : MemLpLoc p Ω (fun z => DJ z 1) :=
    hDJp.clm_comp (G := V →L[ℝ] V) (ContinuousLinearMap.apply ℝ (V →L[ℝ] V) 1)
  have hDJIp : MemLpLoc p Ω (fun z => DJ z I) :=
    hDJp.clm_comp (G := V →L[ℝ] V) (ContinuousLinearMap.apply ℝ (V →L[ℝ] V) I)
  have hloc_JDξ1 := hJinf.locallyIntegrableOn_clm_apply
    ((memLpLoc_one_iff_locallyIntegrableOn hloc).2 (hDξ1q.locallyIntegrableOn hq1 hloc))
    (by simp) hloc
  have hloc_JDξI := hJinf.locallyIntegrableOn_clm_apply
    ((memLpLoc_one_iff_locallyIntegrableOn hloc).2 (hDξIq.locallyIntegrableOn hq1 hloc))
    (by simp) hloc
  have hloc_DJ1DξI := hDJ1p.locallyIntegrableOn_clm_apply hDξIq hpq hloc
  have hloc_DJIDξ1 := hDJIp.locallyIntegrableOn_clm_apply hDξ1q hpq hloc
  have hint_smul (i : Fin (Module.finrank ℝ V)) {u : ℂ → V}
      (hu : LocallyIntegrableOn u Ω volume) :
      Integrable (fun z => ⟪(α i : ℂ → ℝ) z • b i, u z⟫_ℝ) volume :=
    (TestFunction.postcompCLM
      (ContinuousLinearMap.toSpanSingleton ℝ (b i)) (α i)).integrable_inner hu
  have hint_deriv (i : Fin (Module.finrank ℝ V)) (w : ℂ) {u : ℂ → V}
      (hu : LocallyIntegrableOn u Ω volume) :
      Integrable (fun z => ⟪fderiv ℝ (α i : ℂ → ℝ) z w • b i, u z⟫_ℝ) volume := by
    simpa only [TestFunction.postcompCLM_apply, Function.comp_apply,
      ContinuousLinearMap.toSpanSingleton_apply, TestFunction.lineDerivOp_apply_eq_fderiv] using
      (TestFunction.postcompCLM (ContinuousLinearMap.toSpanSingleton ℝ (b i))
        (∂_{w} (α i))).integrable_inner hu
  have hsum := Finset.sum_congr (s₁ := Finset.univ) rfl fun i _ =>
    integral_comm_differentiated_smul hp1 hpq hJ hJinf hDJp hξ hDξq (α i) (b i)
  simp only [Finset.sum_add_distrib] at hsum
  rw [← integral_finsetSum _ fun i _ => hint_deriv i 1 hloc_JDξI,
    ← integral_finsetSum _ fun i _ => hint_smul i hloc_DJ1DξI,
    ← integral_finsetSum _ fun i _ => hint_deriv i I hloc_JDξ1,
    ← integral_finsetSum _ fun i _ => hint_smul i hloc_DJIDξ1] at hsum
  simpa only [← sum_inner, ← hφ_eq, ← hfderiv_φ_eq] using hsum

/-- **The weak differentiated system (assuming only `ξ ∈ W^{1,q}_loc`).** Let `2 < p < ∞`,
`1/p + 1/q ≤ 1`, `1 < q ≤ p`, `J, S ∈ W^{1,p}_loc`, `ξ, η ∈ W^{1,q}_loc` with weak derivatives
`DJ, DS, Dξ, Dη`, and `∂_s ξ + J ∂_t ξ + S ξ = η` almost everywhere on `Ω`. Then
`Ξ = toLp 2 (∂_s ξ, ∂_t ξ)` is a weak solution on `WithLp 2 (V × V)` of the differentiated system
with `J₂ = diag(J, J)`, `S₂ = [[S, ∂_s J], [0, S + ∂_t J]]`, and
`η₂ = toLp 2 (∂_s η - (∂_s S) ξ, ∂_t η - (∂_t S) ξ)`. -/
private theorem isWeakCRSolution_differentiated [FiniteDimensional ℝ V] {p q : ℝ≥0}
    (hp : 2 < p) (hq : 1 < q) (hqp : q ≤ p) (hpq : (p : ℝ≥0∞)⁻¹ + (q : ℝ≥0∞)⁻¹ ≤ 1)
    {J S : ℂ → V →L[ℝ] V} {DJ DS : ℂ → ℂ →L[ℝ] V →L[ℝ] V}
    {ξ η : ℂ → V} {Dξ Dη : ℂ → ℂ →L[ℝ] V}
    (hJ : MemWkpLoc p Ω 1 J) (hDJ : HasWeakFDerivOn volume Ω J DJ)
    (hS : MemWkpLoc p Ω 1 S) (hDS : HasWeakFDerivOn volume Ω S DS)
    (hξ : MemWkpLoc q Ω 1 ξ) (hDξ : HasWeakFDerivOn volume Ω ξ Dξ)
    (hη : MemWkpLoc q Ω 1 η) (hDη : HasWeakFDerivOn volume Ω η Dη)
    (heq : ∀ᵐ z ∂volume.restrict Ω, Dξ z 1 + J z (Dξ z I) + S z (ξ z) = η z) :
    IsWeakCRSolution q Ω
      (fun z => diagProdL2L V (J z))
      (fun z => (diagProdL2L V).comp (DJ z))
      (fun z => conjProdL2L V (differentiatedCRCoefficient (S z) (DJ z)))
      (fun z => WithLp.toLp 2 (Dξ z 1, Dξ z I))
      (fun z => WithLp.toLp 2 (Dη z 1 - DS z 1 (ξ z), Dη z I - DS z I (ξ z))) := by
  -- Step 1: Verify Sobolev regularity of the differentiated coefficients, `Ξ`, and `η₂`.
  have : Fact (1 ≤ (p : ℝ≥0∞)) := ⟨by exact_mod_cast (one_lt_two.trans hp).le⟩
  have : Fact (1 ≤ (q : ℝ≥0∞)) := ⟨by exact_mod_cast hq.le⟩
  have hp1 : (1 : ℝ≥0∞) ≤ p := Fact.out
  have hq1 : (1 : ℝ≥0∞) ≤ q := Fact.out
  have hloc := Ω.isOpen.isLocallyClosed
  have hJinf : MemLpLoc ∞ Ω J := hJ.memLpLoc_of_holderTriple hp le_rfl
  have hSinf : MemLpLoc ∞ Ω S := hS.memLpLoc_of_holderTriple hp le_rfl
  have hDJp := hJ.memLpLoc_of_hasWeakFDerivOn hDJ
  have hDSp := hS.memLpLoc_of_hasWeakFDerivOn hDS
  have hDξq := hξ.memLpLoc_of_hasWeakFDerivOn hDξ
  have hDηq := hη.memLpLoc_of_hasWeakFDerivOn hDη
  let eL2 : (V × V) ≃L[ℝ] WithLp 2 (V × V) := (WithLp.prodContinuousLinearEquiv 2 ℝ V V).symm
  have hΞq : MemLpLoc q Ω (fun z => WithLp.toLp 2 (Dξ z 1, Dξ z I)) :=
    (memWkpLoc_zero_iff.1 (hξ.memWkpLoc_partials_of_hasWeakFDerivOn hDξ)).clm_comp
      eL2.toContinuousLinearMap
  have hEtaTilde_q : MemLpLoc q Ω
      (fun z => WithLp.toLp 2 (Dη z 1 - DS z 1 (ξ z), Dη z I - DS z I (ξ z))) :=
    (memLpLoc_differentiatedCR_rightSide hp hq.le hqp hS hDS hξ hη hDη).clm_comp
      eL2.toContinuousLinearMap
  have hS2p : MemLpLoc p Ω (fun z => differentiatedCRCoefficient (S z) (DJ z)) :=
    memWkpLoc_zero_iff.1 (hS.of_succ.differentiatedCRCoefficient hJ hDJ)
  have hJ_tilde : MemWkpLoc p Ω 1 (fun z => diagProdL2L V (J z)) :=
    hJ.clm_comp (G := WithLp 2 (V × V) →L[ℝ] WithLp 2 (V × V)) (diagProdL2L V)
  have hDJ_tilde : HasWeakFDerivOn volume Ω (fun z => diagProdL2L V (J z))
      (fun z => (diagProdL2L V).comp (DJ z)) :=
    hDJ.clm_comp (G := WithLp 2 (V × V) →L[ℝ] WithLp 2 (V × V)) (diagProdL2L V)
  have hc2 : IsSobolevCRCoefficients p Ω
      (fun z => diagProdL2L V (J z))
      (fun z => (diagProdL2L V).comp (DJ z))
      (fun z => conjProdL2L V (differentiatedCRCoefficient (S z) (DJ z))) :=
    ⟨hDJ_tilde, hJ_tilde.memLpLoc, hJ_tilde.memLpLoc_of_hasWeakFDerivOn hDJ_tilde,
      hS2p.clm_comp (G := WithLp 2 (V × V) →L[ℝ] WithLp 2 (V × V)) (conjProdL2L V)⟩
  have hSξ_weak : HasWeakFDerivOn volume Ω (fun z => S z (ξ z))
      (fun z => (ContinuousLinearMap.id ℝ (V →L[ℝ] V)).precompL ℂ (DS z) (ξ z) +
        (ContinuousLinearMap.id ℝ (V →L[ℝ] V)).precompR ℂ (S z) (Dξ z)) :=
    hDS.bilin_of_memLpLoc (ContinuousLinearMap.id ℝ (V →L[ℝ] V)) hp hq hqp
      (hSinf.mono_exponent le_top) hDSp hDξ hξ.memLpLoc hDξq
  -- Step 2: Record local integrability of every partial term and decompose `Φ = (φ₁, φ₂)`.
  have hDξq_w (w : ℂ) : MemLpLoc q Ω (fun z => Dξ z w) :=
    hDξq.clm_comp (ContinuousLinearMap.apply ℝ V w)
  have hDJp_w (w : ℂ) : MemLpLoc p Ω (fun z => DJ z w) :=
    hDJp.clm_comp (G := V →L[ℝ] V) (ContinuousLinearMap.apply ℝ (V →L[ℝ] V) w)
  have hDSp_w (w : ℂ) : MemLpLoc p Ω (fun z => DS z w) :=
    hDSp.clm_comp (G := V →L[ℝ] V) (ContinuousLinearMap.apply ℝ (V →L[ℝ] V) w)
  have hDηq_w (w : ℂ) : MemLpLoc q Ω (fun z => Dη z w) :=
    hDηq.clm_comp (ContinuousLinearMap.apply ℝ V w)
  have hloc_Dξ (w : ℂ) := (hDξq_w w).locallyIntegrableOn hq1 hloc
  have hloc_JDξ (w : ℂ) := hJ.memLpLoc.locallyIntegrableOn_clm_apply (hDξq_w w) hpq hloc
  have hloc_DJDξ (w₁ w₂ : ℂ) := (hDJp_w w₁).locallyIntegrableOn_clm_apply (hDξq_w w₂) hpq hloc
  have hloc_SDξ (w : ℂ) := hS.memLpLoc.locallyIntegrableOn_clm_apply (hDξq_w w) hpq hloc
  have hloc_Sξ := hS.memLpLoc.locallyIntegrableOn_clm_apply hξ.memLpLoc hpq hloc
  have hloc_η := hη.memLpLoc.locallyIntegrableOn hq1 hloc
  have hloc_Dη (w : ℂ) := (hDηq_w w).locallyIntegrableOn hq1 hloc
  have hloc_DSξ (w : ℂ) := (hDSp_w w).locallyIntegrableOn_clm_apply hξ.memLpLoc hpq hloc
  refine isWeakCRSolution_iff.2 ⟨hΞq, hEtaTilde_q.locallyIntegrableOn hq1 hloc, fun Φ =>
    ⟨hc2.integrable_inner_crFormalAdjoint hpq hΞq Φ, ?_⟩⟩
  let p₁ : WithLp 2 (V × V) →L[ℝ] V :=
    (ContinuousLinearMap.fst ℝ V V).comp eL2.symm.toContinuousLinearMap
  let p₂ : WithLp 2 (V × V) →L[ℝ] V :=
    (ContinuousLinearMap.snd ℝ V V).comp eL2.symm.toContinuousLinearMap
  let φ₁ : 𝓓(Ω, V) := TestFunction.postcompCLM p₁ Φ
  let φ₂ : 𝓓(Ω, V) := TestFunction.postcompCLM p₂ Φ
  have hfderiv_φ₁ (z w : ℂ) : fderiv ℝ (φ₁ : ℂ → V) z w = p₁ (fderiv ℝ (Φ : ℂ → _) z w) := by
    have h := (p₁.hasFDerivAt.comp z (Φ.contDiff.differentiable (by simp) z).hasFDerivAt).fderiv
    simpa [φ₁, TestFunction.postcompCLM_apply] using congr($h w)
  have hfderiv_φ₂ (z w : ℂ) : fderiv ℝ (φ₂ : ℂ → V) z w = p₂ (fderiv ℝ (Φ : ℂ → _) z w) := by
    have h := (p₂.hasFDerivAt.comp z (Φ.contDiff.differentiable (by simp) z).hasFDerivAt).fderiv
    simpa [φ₂, TestFunction.postcompCLM_apply] using congr($h w)
  have hLHS_pt (z : ℂ) :
      ⟪crFormalAdjoint (fun z => diagProdL2L V (J z)) (fun z => (diagProdL2L V).comp (DJ z))
        (fun z => conjProdL2L V (differentiatedCRCoefficient (S z) (DJ z))) Φ z,
        WithLp.toLp 2 (Dξ z 1, Dξ z I)⟫_ℝ =
      (-⟪fderiv ℝ (φ₁ : ℂ → V) z 1, Dξ z 1⟫_ℝ - ⟪fderiv ℝ (φ₁ : ℂ → V) z I, J z (Dξ z 1)⟫_ℝ -
        ⟪(φ₁ : ℂ → V) z, DJ z I (Dξ z 1)⟫_ℝ + ⟪(φ₁ : ℂ → V) z, S z (Dξ z 1)⟫_ℝ +
        ⟪(φ₁ : ℂ → V) z, DJ z 1 (Dξ z I)⟫_ℝ) +
      (-⟪fderiv ℝ (φ₂ : ℂ → V) z 1, Dξ z I⟫_ℝ - ⟪fderiv ℝ (φ₂ : ℂ → V) z I, J z (Dξ z I)⟫_ℝ +
        ⟪(φ₂ : ℂ → V) z, S z (Dξ z I)⟫_ℝ) := by
    rw [inner_crFormalAdjoint]
    simp only [hfderiv_φ₁, hfderiv_φ₂]
    simp only [diagProdL2L_apply, conjProdL2L_apply, ContinuousLinearMap.comp_apply,
      differentiatedCRCoefficient_apply, WithLp.prod_inner_apply, inner_add_right,
      p₁, p₂, φ₁, φ₂, eL2, TestFunction.postcompCLM_apply, Function.comp_apply,
      ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.symm_symm,
      WithLp.prodContinuousLinearEquiv_apply, ContinuousLinearMap.coe_fst',
      ContinuousLinearMap.coe_snd']
    ring
  have hRHS_pt (z : ℂ) :
      ⟪(Φ : ℂ → _) z, WithLp.toLp 2 (Dη z 1 - DS z 1 (ξ z), Dη z I - DS z I (ξ z))⟫_ℝ =
      (⟪(φ₁ : ℂ → V) z, Dη z 1⟫_ℝ - ⟪(φ₁ : ℂ → V) z, DS z 1 (ξ z)⟫_ℝ) +
      (⟪(φ₂ : ℂ → V) z, Dη z I⟫_ℝ - ⟪(φ₂ : ℂ → V) z, DS z I (ξ z)⟫_ℝ) := by
    simp only [WithLp.prod_inner_apply, inner_sub_right, φ₁, φ₂, p₁, p₂, eL2,
      TestFunction.postcompCLM_apply, Function.comp_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.symm_symm,
      WithLp.prodContinuousLinearEquiv_apply, ContinuousLinearMap.coe_fst',
      ContinuousLinearMap.coe_snd']
  -- Step 3: Prove the `φ₁` and `φ₂` weak identities via `heq`, weak Leibniz on `S ξ`, and
  -- `integral_comm_differentiated`.
  have hSξ_ibp (w : ℂ) (φ : 𝓓(Ω, V)) :
      ∫ z, ⟪fderiv ℝ (φ : ℂ → V) z w, S z (ξ z)⟫_ℝ =
        -((∫ z, ⟪(φ : ℂ → V) z, DS z w (ξ z)⟫_ℝ) + ∫ z, ⟪(φ : ℂ → V) z, S z (Dξ z w)⟫_ℝ) := by
    have h := (hSξ_weak.hasWeakLineDerivOn w).integral_inner_lineDeriv_eq_neg φ
    simp only [TestFunction.lineDeriv_eq_fderiv, add_apply, ContinuousLinearMap.precompL_apply,
      ContinuousLinearMap.precompR_apply, ContinuousLinearMap.id_apply, inner_add_right] at h
    exact h.trans (congrArg Neg.neg
      (integral_add (φ.integrable_inner (hloc_DSξ w)) (φ.integrable_inner (hloc_SDξ w))))
  have hcomp1 :
      -(∫ z, ⟪fderiv ℝ (φ₁ : ℂ → V) z 1, Dξ z 1⟫_ℝ) -
      (∫ z, ⟪fderiv ℝ (φ₁ : ℂ → V) z I, J z (Dξ z 1)⟫_ℝ) -
      (∫ z, ⟪(φ₁ : ℂ → V) z, DJ z I (Dξ z 1)⟫_ℝ) +
      (∫ z, ⟪(φ₁ : ℂ → V) z, S z (Dξ z 1)⟫_ℝ) +
      (∫ z, ⟪(φ₁ : ℂ → V) z, DJ z 1 (Dξ z I)⟫_ℝ) =
      (∫ z, ⟪(φ₁ : ℂ → V) z, Dη z 1⟫_ℝ) - ∫ z, ⟪(φ₁ : ℂ → V) z, DS z 1 (ξ z)⟫_ℝ := by
    have hsubst : ∫ z, ⟪fderiv ℝ (φ₁ : ℂ → V) z 1, Dξ z 1⟫_ℝ =
        (∫ z, ⟪fderiv ℝ (φ₁ : ℂ → V) z 1, η z⟫_ℝ) -
        (∫ z, ⟪fderiv ℝ (φ₁ : ℂ → V) z 1, J z (Dξ z I)⟫_ℝ) -
        ∫ z, ⟪fderiv ℝ (φ₁ : ℂ → V) z 1, S z (ξ z)⟫_ℝ := by
      have k1 := φ₁.integrable_inner_fderiv hloc_η 1
      have k2 := φ₁.integrable_inner_fderiv (hloc_JDξ I) 1
      have k3 := φ₁.integrable_inner_fderiv hloc_Sξ 1
      rw [← integral_sub k1 k2, ← integral_sub _ k3]
      · refine integral_congr_ae ?_
        filter_upwards [ae_imp_of_ae_restrict heq] with z hz
        by_cases hzΩ : z ∈ (Ω : Set ℂ)
        · have he : Dξ z 1 = η z - J z (Dξ z I) - S z (ξ z) := by rw [← hz hzΩ]; abel
          simp [he, inner_sub_right]
        · simp [fderiv_of_notMem_tsupport ℝ (fun h => hzΩ (φ₁.tsupport_subset h))]
      · exact k1.sub k2
    have hη1 : ∫ z, ⟪fderiv ℝ (φ₁ : ℂ → V) z 1, η z⟫_ℝ = -∫ z, ⟪(φ₁ : ℂ → V) z, Dη z 1⟫_ℝ := by
      simpa only [TestFunction.lineDeriv_eq_fderiv] using
        (hDη.hasWeakLineDerivOn 1).integral_inner_lineDeriv_eq_neg φ₁
    have hSξ1 := hSξ_ibp 1 φ₁
    have hcomm := integral_comm_differentiated hp1 hpq hDJ hJinf hDJp hDξ hDξq φ₁
    linarith
  have hcomp2 :
      -(∫ z, ⟪fderiv ℝ (φ₂ : ℂ → V) z 1, Dξ z I⟫_ℝ) -
      (∫ z, ⟪fderiv ℝ (φ₂ : ℂ → V) z I, J z (Dξ z I)⟫_ℝ) +
      (∫ z, ⟪(φ₂ : ℂ → V) z, S z (Dξ z I)⟫_ℝ) =
      (∫ z, ⟪(φ₂ : ℂ → V) z, Dη z I⟫_ℝ) - ∫ z, ⟪(φ₂ : ℂ → V) z, DS z I (ξ z)⟫_ℝ := by
    have hswap := integral_inner_fderiv_one_eq_fderiv_I hDξ φ₂
    have hsubst : (∫ z, ⟪fderiv ℝ (φ₂ : ℂ → V) z I, Dξ z 1⟫_ℝ) +
        (∫ z, ⟪fderiv ℝ (φ₂ : ℂ → V) z I, J z (Dξ z I)⟫_ℝ) =
        (∫ z, ⟪fderiv ℝ (φ₂ : ℂ → V) z I, η z⟫_ℝ) -
        ∫ z, ⟪fderiv ℝ (φ₂ : ℂ → V) z I, S z (ξ z)⟫_ℝ := by
      rw [← integral_add (φ₂.integrable_inner_fderiv (hloc_Dξ 1) I)
          (φ₂.integrable_inner_fderiv (hloc_JDξ I) I),
        ← integral_sub (φ₂.integrable_inner_fderiv hloc_η I)
          (φ₂.integrable_inner_fderiv hloc_Sξ I)]
      refine integral_congr_ae ?_
      filter_upwards [ae_imp_of_ae_restrict heq] with z hz
      by_cases hzΩ : z ∈ (Ω : Set ℂ)
      · rw [← inner_add_right, eq_sub_of_add_eq (hz hzΩ), inner_sub_right]
      · simp [fderiv_of_notMem_tsupport ℝ (fun h => hzΩ (φ₂.tsupport_subset h))]
    have hηI : ∫ z, ⟪fderiv ℝ (φ₂ : ℂ → V) z I, η z⟫_ℝ = -∫ z, ⟪(φ₂ : ℂ → V) z, Dη z I⟫_ℝ := by
      simpa only [TestFunction.lineDeriv_eq_fderiv] using
        (hDη.hasWeakLineDerivOn I).integral_inner_lineDeriv_eq_neg φ₂
    have hSξI := hSξ_ibp I φ₂
    linarith
  simp_rw [hLHS_pt, hRHS_pt]
  have i1 := φ₁.integrable_inner_fderiv (hloc_Dξ 1) 1
  have i2 := φ₁.integrable_inner_fderiv (hloc_JDξ 1) I
  have i3 := φ₁.integrable_inner (hloc_DJDξ I 1)
  have i4 := φ₁.integrable_inner (hloc_SDξ 1)
  have i5 := φ₁.integrable_inner (hloc_DJDξ 1 I)
  have j1 := φ₂.integrable_inner_fderiv (hloc_Dξ I) 1
  have j2 := φ₂.integrable_inner_fderiv (hloc_JDξ I) I
  have j3 := φ₂.integrable_inner (hloc_SDξ I)
  have r1 := φ₁.integrable_inner (hloc_Dη 1)
  have r2 := φ₁.integrable_inner (hloc_DSξ 1)
  have r3 := φ₂.integrable_inner (hloc_Dη I)
  have r4 := φ₂.integrable_inner (hloc_DSξ I)
  rw [integral_add _ _, integral_add _ i5, integral_add _ i4, integral_sub _ i3,
    integral_sub _ i2, integral_neg, integral_add _ j3, integral_sub _ j2, integral_neg,
    integral_add _ _, integral_sub r1 r2, integral_sub r3 r4, hcomp1, hcomp2]
  all_goals fun_prop

/-- Regularity of the differentiated right-hand side `(∂_s η - (∂_s S) ξ, ∂_t η - (∂_t S) ξ)` at
arbitrary order `k ≥ 0`. -/
private theorem memWkpLoc_differentiated_rightSide [FiniteDimensional ℝ V] {p q : ℝ≥0}
    (hp : 2 < p) (hq : 1 < q) (hqp : q ≤ p) {k : ℕ}
    {S : ℂ → V →L[ℝ] V} {DS : ℂ → ℂ →L[ℝ] V →L[ℝ] V}
    {ξ η : ℂ → V} {Dη : ℂ → ℂ →L[ℝ] V}
    (hS : MemWkpLoc p Ω (k + 1) S) (hDS : HasWeakFDerivOn volume Ω S DS)
    (hξ : MemWkpLoc q Ω (k + 1) ξ) (hη : MemWkpLoc q Ω (k + 1) η)
    (hDη : HasWeakFDerivOn volume Ω η Dη) :
    MemWkpLoc q Ω k (fun z => WithLp.toLp 2 (Dη z 1 - DS z 1 (ξ z), Dη z I - DS z I (ξ z))) := by
  let eL2 : (V × V) ≃L[ℝ] WithLp 2 (V × V) := (WithLp.prodContinuousLinearEquiv 2 ℝ V V).symm
  cases k with
  | zero =>
    exact memWkpLoc_zero_iff.2
      ((memLpLoc_differentiatedCR_rightSide hp hq.le hqp hS hDS hξ hη hDη).clm_comp
        eL2.toContinuousLinearMap)
  | succ k =>
    have hDSk := hS.memWkpLoc_of_hasWeakFDerivOn hDS
    have hDηk := hη.memWkpLoc_of_hasWeakFDerivOn hDη
    have hcomp (w : ℂ) : MemWkpLoc q Ω (k + 1) (fun z => Dη z w - DS z w (ξ z)) :=
      (hDηk.clm_comp (ContinuousLinearMap.apply ℝ V w)).sub
        ((hDSk.clm_comp (ContinuousLinearMap.apply ℝ (V →L[ℝ] V) w)).clm_apply_succ hp hq hqp
          hξ.of_succ)
    exact ((hcomp 1).prodMk (hcomp I)).clm_comp eL2.toContinuousLinearMap

/-- **Higher-order interior weak regularity (McDuff–Salamon Proposition B.4.9).** Let `2 < p < ∞`,
`1/p + 1/q₀ < 1`, `1/p + 1/q < 1`, `q ≤ p`, and `k ≥ 0`. Suppose `J ∈ W^{max 1 k, p}_loc(Ω)` has
weak derivative `DJ` and satisfies `J² = -1` almost everywhere, `S ∈ W^{k,p}_loc(Ω)`, and
`η ∈ W^{k,q}_loc(Ω)`. Then any weak solution `ξ ∈ L^{q₀}_loc(Ω)` of `∂_s ξ + J ∂_t ξ + S ξ = η`
belongs to `W^{k+1,q}_loc(Ω)`. -/
theorem memWkpLoc_succ_of_isWeakCRSolution {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] {Ω : Opens ℂ} {p q q₀ : ℝ≥0∞}
    (hp : 2 < p) (hp_top : p ≠ ⊤) (hpq₀ : p⁻¹ + q₀⁻¹ < 1) (hpq : p⁻¹ + q⁻¹ < 1) (hqp : q ≤ p)
    {k : ℕ} {J S : ℂ → V →L[ℝ] V} {DJ : ℂ → ℂ →L[ℝ] V →L[ℝ] V} {ξ η : ℂ → V}
    (hJ : MemWkpLoc p Ω (max 1 k) J) (hDJ : HasWeakFDerivOn volume Ω J DJ)
    (hS : MemWkpLoc p Ω k S)
    (hJsq : ∀ᵐ z ∂volume.restrict Ω, J z * J z = -1)
    (hsol : IsWeakCRSolution q₀ Ω J DJ S ξ η) (hη : MemWkpLoc q Ω k η) :
    MemWkpLoc q Ω (k + 1) ξ := by
  have hq1 : 1 < q := by
    have hq_inv : q⁻¹ < 1 := le_add_self.trans_lt hpq
    rwa [← inv_one, ENNReal.inv_lt_inv] at hq_inv
  have hq_top : q ≠ ⊤ := ne_top_of_le_ne_top hp_top hqp
  induction k generalizing V q₀ J DJ S ξ η with
  | zero =>
    have hc : IsSobolevCRCoefficients p Ω J DJ S :=
      ⟨hDJ, hJ.memLpLoc, hJ.memLpLoc_of_hasWeakFDerivOn hDJ, memWkpLoc_zero_iff.1 hS⟩
    exact hc.memWkpLoc_one_of_isWeakCRSolution hp hp_top hpq₀ hq1 hqp hJsq hsol
      (memWkpLoc_zero_iff.1 hη)
  | succ k ih =>
    rw [Nat.max_eq_right (Nat.succ_pos k)] at hJ
    have hJ' : MemWkpLoc p Ω (max 1 k) J := hJ.of_le (by omega)
    have hξk : MemWkpLoc q Ω (k + 1) ξ :=
      ih hpq₀ hJ' hDJ hS.of_succ hJsq hsol hη.of_succ
    have hξ1 : MemWkpLoc q Ω 1 ξ := hξk.of_le (Nat.succ_pos k)
    obtain ⟨Dξ, hDξ, -⟩ := hξ1.exists_weakFDeriv_of_isOpen
    obtain ⟨DS, hDS, -⟩ := (hS.of_le (Nat.succ_pos k)).exists_weakFDeriv_of_isOpen
    obtain ⟨Dη, hDη, -⟩ := (hη.of_le (Nat.succ_pos k)).exists_weakFDeriv_of_isOpen
    have hJ1 : MemWkpLoc p Ω 1 J := hJ.of_le (Nat.succ_pos k)
    have hS1 : MemWkpLoc p Ω 1 S := hS.of_le (Nat.succ_pos k)
    have hη1 : MemWkpLoc q Ω 1 η := hη.of_le (Nat.succ_pos k)
    have hc : IsSobolevCRCoefficients p Ω J DJ S :=
      ⟨hDJ, hJ1.memLpLoc, hJ1.memLpLoc_of_hasWeakFDerivOn hDJ, hS1.memLpLoc⟩
    have hsol_q : IsWeakCRSolution q Ω J DJ S ξ η :=
      isWeakCRSolution_iff.2 ⟨hξ1.memLpLoc, hsol.locallyIntegrableOn,
        (isWeakCRSolution_iff.1 hsol).2.2⟩
    have heq : ∀ᵐ z ∂volume.restrict Ω, Dξ z 1 + J z (Dξ z I) + S z (ξ z) = η z :=
      (hc.isWeakCRSolution_iff_ae hpq.le hp_top hq_top hDξ hξ1.memLpLoc
        (hξ1.memLpLoc_of_hasWeakFDerivOn hDξ) hsol.locallyIntegrableOn).1 hsol_q
    lift p to ℝ≥0 using hp_top
    lift q to ℝ≥0 using hq_top
    have hpR : 2 < p := by exact_mod_cast hp
    have hqR : 1 < q := by exact_mod_cast hq1
    have hqpR : q ≤ p := by exact_mod_cast hqp
    have hsol_diff := isWeakCRSolution_differentiated hpR hqR hqpR hpq.le hJ1 hDJ hS1 hDS hξ1 hDξ
      hη1 hDη heq
    have hJTilde : MemWkpLoc p Ω (max 1 k) (fun z => diagProdL2L V (J z)) :=
      hJ'.clm_comp (G := WithLp 2 (V × V) →L[ℝ] WithLp 2 (V × V)) (diagProdL2L V)
    have hDJTilde : HasWeakFDerivOn volume Ω (fun z => diagProdL2L V (J z))
        (fun z => (diagProdL2L V).comp (DJ z)) :=
      hDJ.clm_comp (G := WithLp 2 (V × V) →L[ℝ] WithLp 2 (V × V)) (diagProdL2L V)
    have hSTilde : MemWkpLoc p Ω k
        (fun z => conjProdL2L V (differentiatedCRCoefficient (S z) (DJ z))) :=
      (hS.of_succ.differentiatedCRCoefficient hJ hDJ).clm_comp
        (G := WithLp 2 (V × V) →L[ℝ] WithLp 2 (V × V)) (conjProdL2L V)
    have hJTilde_sq : ∀ᵐ z ∂volume.restrict Ω,
        diagProdL2L V (J z) * diagProdL2L V (J z) = -1 := by
      filter_upwards [hJsq] with z hz
      ext x
      have h1 : J z (J z x.ofLp.1) = -x.ofLp.1 := by simpa using congr($hz x.ofLp.1)
      have h2 : J z (J z x.ofLp.2) = -x.ofLp.2 := by simpa using congr($hz x.ofLp.2)
      simp only [mul_apply_eq_comp, diagProdL2L_apply, neg_apply, one_apply_eq_self]
      exact congrArg (WithLp.toLp 2) (Prod.ext h1 h2)
    have hEtaTilde := memWkpLoc_differentiated_rightSide hpR hqR hqpR hS hDS hξk hη hDη
    have hΞ : MemWkpLoc q Ω (k + 1) (fun z => WithLp.toLp 2 (Dξ z 1, Dξ z I)) :=
      ih (V := WithLp 2 (V × V)) hpq hJTilde hDJTilde hSTilde hJTilde_sq hsol_diff hEtaTilde
    have hDξ1 : MemWkpLoc q Ω (k + 1) (fun z => Dξ z 1) :=
      hΞ.clm_comp ((ContinuousLinearMap.fst ℝ V V).comp
        (WithLp.prodContinuousLinearEquiv 2 ℝ V V).toContinuousLinearMap)
    have hDξI : MemWkpLoc q Ω (k + 1) (fun z => Dξ z I) :=
      hΞ.clm_comp ((ContinuousLinearMap.snd ℝ V V).comp
        (WithLp.prodContinuousLinearEquiv 2 ℝ V V).toContinuousLinearMap)
    have hDξ_reg : MemWkpLoc q Ω (k + 1) Dξ := by
      rw [ContinuousLinearMap.fun_eq_smulRightL_reCLM_add_smulRightL_imCLM Dξ]
      exact (hDξ1.clm_comp (ContinuousLinearMap.smulRightL ℝ ℂ V Complex.reCLM)).add
        (hDξI.clm_comp (ContinuousLinearMap.smulRightL ℝ ℂ V Complex.imCLM))
    exact memWkpLoc_succ_iff_of_isOpen.2 ⟨hξ1.memLpLoc, Dξ, hDξ, hDξ_reg⟩

/-- **Higher-order interior regularity for `W^{1,q}_loc` solutions in an arbitrary
finite-dimensional real normed space.** Let `2 < p < ∞`, `1/p + 1/q < 1`, `q ≤ p`, and `k ≥ 0`.
If `J ∈ W^{max 1 k, p}_loc(Ω)` satisfies `J² = -1` almost everywhere, `S ∈ W^{k,p}_loc(Ω)`,
`η ∈ W^{k,q}_loc(Ω)`, and `ξ ∈ W^{1,q}_loc(Ω)` satisfies `∂_s ξ + J ∂_t ξ + S ξ = η` almost
everywhere on `Ω`, then `ξ ∈ W^{k+1,q}_loc(Ω)`. -/
theorem memWkpLoc_succ_of_ae_cauchyRiemann {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] {Ω : Opens ℂ} {p q : ℝ≥0∞}
    (hp : 2 < p) (hp_top : p ≠ ⊤) (hpq : p⁻¹ + q⁻¹ < 1) (hqp : q ≤ p) {k : ℕ}
    {J S : ℂ → V →L[ℝ] V} {ξ η : ℂ → V} {Dξ : ℂ → ℂ →L[ℝ] V}
    (hJ : MemWkpLoc p Ω (max 1 k) J) (hS : MemWkpLoc p Ω k S)
    (hJsq : ∀ᵐ z ∂volume.restrict Ω, J z * J z = -1)
    (hξ : MemWkpLoc q Ω 1 ξ) (hDξ : HasWeakFDerivOn volume Ω ξ Dξ)
    (hη : MemWkpLoc q Ω k η)
    (heq : ∀ᵐ z ∂volume.restrict Ω, Dξ z 1 + J z (Dξ z I) + S z (ξ z) = η z) :
    MemWkpLoc q Ω (k + 1) ξ := by
  have : CompleteSpace V := FiniteDimensional.completeSpace ℝ V
  have hq1 : 1 < q := by
    have hq_inv : q⁻¹ < 1 := le_add_self.trans_lt hpq
    rwa [← inv_one, ENNReal.inv_lt_inv] at hq_inv
  have hq_top : q ≠ ⊤ := ne_top_of_le_ne_top hp_top hqp
  let e : V ≃L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ V)) :=
    ContinuousLinearEquiv.ofFinrankEq (by simp)
  let conj : (V →L[ℝ] V) →L[ℝ]
      (EuclideanSpace ℝ (Fin (Module.finrank ℝ V)) →L[ℝ]
        EuclideanSpace ℝ (Fin (Module.finrank ℝ V))) :=
    (ContinuousLinearMap.compL ℝ _ V _ e.toContinuousLinearMap).comp
      ((ContinuousLinearMap.compL ℝ _ V V).flip e.symm.toContinuousLinearMap)
  have hconj (A : V →L[ℝ] V) (x : EuclideanSpace ℝ (Fin (Module.finrank ℝ V))) :
      conj A x = e (A (e.symm x)) := rfl
  let Je := fun z => conj (J z)
  let Se := fun z => conj (S z)
  let ξe := fun z => e (ξ z)
  let ηe := fun z => e (η z)
  let Dξe := fun z => e.toContinuousLinearMap.comp (Dξ z)
  have hJe : MemWkpLoc p Ω (max 1 k) Je :=
    hJ.clm_comp (G := EuclideanSpace ℝ (Fin (Module.finrank ℝ V)) →L[ℝ]
      EuclideanSpace ℝ (Fin (Module.finrank ℝ V))) conj
  have hJe1 : MemWkpLoc p Ω 1 Je := hJe.of_le (le_max_left 1 k)
  obtain ⟨DJe, hDJe, -⟩ := hJe1.exists_weakFDeriv_of_isOpen
  have hSe : MemWkpLoc p Ω k Se :=
    hS.clm_comp (G := EuclideanSpace ℝ (Fin (Module.finrank ℝ V)) →L[ℝ]
      EuclideanSpace ℝ (Fin (Module.finrank ℝ V))) conj
  have hηe : MemWkpLoc q Ω k ηe := hη.clm_comp e.toContinuousLinearMap
  have hξe : MemWkpLoc q Ω 1 ξe := hξ.clm_comp e.toContinuousLinearMap
  have hDξe : HasWeakFDerivOn volume Ω ξe Dξe := hDξ.clm_comp e.toContinuousLinearMap
  have hc : IsSobolevCRCoefficients p Ω Je DJe Se :=
    ⟨hDJe, hJe1.memLpLoc, hJe1.memLpLoc_of_hasWeakFDerivOn hDJe, hSe.memLpLoc⟩
  have heq_e : ∀ᵐ z ∂volume.restrict Ω, Dξe z 1 + Je z (Dξe z I) + Se z (ξe z) = ηe z := by
    filter_upwards [heq] with z hz
    simp only [Dξe, Je, Se, ξe, ηe, hconj, ContinuousLinearMap.comp_apply,
      ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.symm_apply_apply]
    rw [← map_add, ← map_add, hz]
  have hsol : IsWeakCRSolution q Ω Je DJe Se ξe ηe :=
    (hc.isWeakCRSolution_iff_ae hpq.le hp_top hq_top hDξe hξe.memLpLoc
      (hξe.memLpLoc_of_hasWeakFDerivOn hDξe)
      (hηe.memLpLoc.locallyIntegrableOn hq1.le Ω.isOpen.isLocallyClosed)).2 heq_e
  have hJesq : ∀ᵐ z ∂volume.restrict Ω, Je z * Je z = -1 := by
    filter_upwards [hJsq] with z hz
    ext x
    simp only [Je, hconj, mul_apply_eq_comp, ContinuousLinearEquiv.symm_apply_apply,
      neg_apply, one_apply_eq_self]
    have h := congr($hz (e.symm x))
    simp only [mul_apply_eq_comp, neg_apply, one_apply_eq_self] at h
    rw [h, map_neg, ContinuousLinearEquiv.apply_symm_apply]
  exact e.comp_memWkpLoc_iff.1
    (memWkpLoc_succ_of_isWeakCRSolution hp hp_top hpq hpq hqp hJe hDJe hSe hJesq hsol hηe)

/-- **Higher-order regularity for homogeneous linear weak solutions.** Let `2 < p < ∞`,
`1/p + 1/q < 1`, `q ≤ p`, and `k ≥ 0`. If `J ∈ W^{max 1 k, p}_loc(Ω)` satisfies `J² = -1` almost
everywhere and `S ∈ W^{k,p}_loc(Ω)`, then any solution of `TauCeti.IsWeakLinearCauchyRiemannOn`
for `(q, Ω, J, S)` belongs to `W^{k+1,q}_loc(Ω)`. -/
theorem IsWeakLinearCauchyRiemannOn.memWkpLoc_succ {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [FiniteDimensional ℝ V] {Ω : Opens ℂ} {p q : ℝ≥0∞}
    {J S : ℂ → V →L[ℝ] V} {ξ : ℂ → V} (hξ : IsWeakLinearCauchyRiemannOn q Ω J S ξ)
    (hp : 2 < p) (hp_top : p ≠ ⊤) (hpq : p⁻¹ + q⁻¹ < 1) (hqp : q ≤ p) {k : ℕ}
    (hJ : MemWkpLoc p Ω (max 1 k) J) (hS : MemWkpLoc p Ω k S)
    (hJsq : ∀ᵐ z ∂volume.restrict Ω, J z * J z = -1) :
    MemWkpLoc q Ω (k + 1) ξ := by
  have : CompleteSpace V := FiniteDimensional.completeSpace ℝ V
  obtain ⟨-, -, D, hD, -, hae⟩ := isWeakLinearCauchyRiemannOn_iff_of_isOpen.1 hξ
  exact memWkpLoc_succ_of_ae_cauchyRiemann hp hp_top hpq hqp hJ hS hJsq hξ.memWkpLoc_one hD
    memWkpLoc_zero_fun hae

/-- **Smooth-coefficient interior regularity (hypoellipticity).** If `J`, `S`, and `η` are smooth
on `Ω` with `J² = -1` on `Ω`, and `ξ ∈ L^{q₀}_loc(Ω)` (`1 < q₀`) is a weak solution of
`∂_s ξ + J ∂_t ξ + S ξ = η`, then `ξ` agrees almost everywhere on `Ω` with a smooth function on
`Ω`. -/
theorem exists_contDiffOn_infty_ae_eq_of_isWeakCRSolution {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] {Ω : Opens ℂ} {q₀ : ℝ≥0∞}
    (hq₀ : 1 < q₀) {J S : ℂ → V →L[ℝ] V} {ξ η : ℂ → V}
    (hJ : ContDiffOn ℝ ∞ J Ω) (hS : ContDiffOn ℝ ∞ S Ω) (hη : ContDiffOn ℝ ∞ η Ω)
    (hJsq : ∀ z ∈ (Ω : Set ℂ), J z * J z = -1)
    (hsol : IsWeakCRSolution q₀ Ω J (fderiv ℝ J) S ξ η) :
    ∃ g : ℂ → V, ContDiffOn ℝ ∞ g Ω ∧ ξ =ᵐ[volume.restrict Ω] g := by
  have hq₀_inv : q₀⁻¹ < 1 := by rw [← inv_one]; exact ENNReal.inv_lt_inv.2 hq₀
  have hgap : (0 : ℝ) < 1 - q₀⁻¹.toReal := by
    have hlt : q₀⁻¹.toReal < 1 := by
      simpa using (ENNReal.toReal_lt_toReal (ne_top_of_lt hq₀_inv) ENNReal.one_ne_top).2 hq₀_inv
    linarith
  set p : ℝ≥0 := ⟨max 3 ((1 - q₀⁻¹.toReal)⁻¹ + 1), by positivity⟩
  have hp2 : (2 : ℝ≥0∞) < p := by
    have : (2 : ℝ) < p := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
    exact_mod_cast this
  have hp_inv : (p : ℝ≥0∞)⁻¹ + q₀⁻¹ < 1 := by
    have hp_pos : (0 : ℝ) < p := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
    have h1 : (1 - q₀⁻¹.toReal)⁻¹ < (p : ℝ) := lt_of_lt_of_le (by linarith) (le_max_right _ _)
    have h2 : (p : ℝ)⁻¹ < 1 - q₀⁻¹.toReal := by
      rw [← inv_inv (1 - q₀⁻¹.toReal)]; exact inv_strictAnti₀ (by positivity) h1
    have hne : (p : ℝ≥0∞)⁻¹ + q₀⁻¹ ≠ ⊤ :=
      ENNReal.add_ne_top.2
        ⟨ENNReal.inv_ne_top.2 (by exact_mod_cast hp_pos.ne'), ne_top_of_lt hq₀_inv⟩
    exact (ENNReal.toReal_lt_toReal hne ENNReal.one_ne_top).1 (by
      rw [ENNReal.toReal_add (ENNReal.inv_ne_top.2 (by exact_mod_cast hp_pos.ne'))
        (ne_top_of_lt hq₀_inv), ENNReal.toReal_inv, ENNReal.coe_toReal, ENNReal.toReal_one]
      linarith)
  have hpp : (p : ℝ≥0∞)⁻¹ + (p : ℝ≥0∞)⁻¹ < 1 := by
    have hlt : (p : ℝ≥0∞)⁻¹ < (2 : ℝ≥0∞)⁻¹ := ENNReal.inv_lt_inv.2 hp2
    exact (ENNReal.add_lt_add hlt hlt).trans_eq ENNReal.inv_two_add_inv_two
  have hJ1 : ContDiffOn ℝ 1 J Ω := hJ.of_le (by simp)
  have hDJ : HasWeakFDerivOn volume Ω J (fderiv ℝ J) :=
    hasWeakFDerivOn_of_differentiableOn
      ((hJ1.continuousOn_fderiv_of_isOpen Ω.isOpen le_rfl).locallyIntegrableOn
        Ω.isOpen.measurableSet)
      fun z hz => (hJ1.differentiableOn one_ne_zero z hz).differentiableAt (Ω.isOpen.mem_nhds hz)
  have hJsq_ae : ∀ᵐ z ∂volume.restrict Ω, J z * J z = -1 :=
    (ae_restrict_iff' Ω.isOpen.measurableSet).2 (.of_forall hJsq)
  have hall (k : ℕ) : MemWkpLoc p Ω (k + 1) ξ :=
    memWkpLoc_succ_of_isWeakCRSolution hp2 ENNReal.coe_ne_top hp_inv hpp le_rfl
      ((hJ.of_le (by simp)).memWkpLoc subset_rfl) hDJ
      ((hS.of_le (by simp)).memWkpLoc subset_rfl) hJsq_ae hsol
      ((hη.of_le (by simp)).memWkpLoc subset_rfl)
  obtain ⟨g, hg0, hξg⟩ := (hall 0).exists_contDiffOn_ae_eq hp2
  refine ⟨g, contDiffOn_infty.2 fun k => ?_, hξg⟩
  obtain ⟨gk, hgk, hξgk⟩ := (hall k).exists_contDiffOn_ae_eq hp2
  have heq : EqOn gk g Ω :=
    Measure.eqOn_open_of_ae_eq (hξgk.symm.trans hξg) Ω.isOpen hgk.continuousOn hg0.continuousOn
  exact hgk.congr fun z hz => (heq hz).symm

end HigherOrder

end TauCeti
