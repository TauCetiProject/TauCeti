/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import TauCeti.Analysis.Green.HalfPlane
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff

/-!
# Green's formula on the half-plane for `∂_s + J ∂_t + S` with variable coefficients

Let `V` be a real inner product space, write `z = s + i t`, and let `J, S : ℂ → (V →L[ℝ] V)` be
coefficient fields, with `J` of class `C¹` and `S` continuous. For the real Cauchy–Riemann
operator `D ξ = ∂_s ξ + J ∂_t ξ + S ξ`, integrating by parts over the half-plane `{0 < t}`
against a compactly supported `C¹` map `φ : ℂ → V`, which need not vanish on `ℝ`, gives

`∫ ⟪∂_s φ + Jᵀ ∂_t φ - Sᵀ φ, ξ⟫ = -∫ ⟪φ, D ξ + (∂_t J) ξ⟫ - ∫_ℝ ⟪φ(s), J(s) ξ(s)⟫ ds`,

where `ᵀ` is the Hilbert adjoint `ContinuousLinearMap.adjoint`. The term `(∂_t J) ξ` comes from
moving `∂_t` across the coefficient `J`, and the boundary term from the `t`-integration. This is
McDuff–Salamon's weak equation (B.4.3), with the zeroth-order term added, for a classical
solution `D ξ = η`.

The boundary integrand `⟪φ(s), J(s) ξ(s)⟫` vanishes when `φ(s)` and `ξ(s)` lie in a set `F`
that is orthogonal to `J(s) F`, that is, `⟪v, J(s) w⟫ = 0` for all `v, w ∈ F`. For `J(s) = i` and
`F = ℝⁿ ⊆ ℂⁿ` this is the boundary condition `φ(s), ξ(s) ∈ ℝⁿ`, the local model of a totally real
boundary condition after trivialization (McDuff–Salamon, Appendix B.4). In that case the left side
is the weak formulation tested against test functions that are real on `ℝ` but need not vanish
there, so a classical solution with real boundary values is a weak solution in the sense of
(B.4.3). For `V = ℂ` the orthogonality of `F = ℝ` and `i F` is `Real.inner_ofReal_I_mul_ofReal`.

The constant-coefficient formula `TauCeti.setIntegral_im_pos_re_inner_cauchyRiemann`, with its
analysis of the dual boundary condition, covers `J = i`, `S = 0` on a complex inner product
space. It places the compact support on the other factor, the map `ξ` to which `∂_s + i ∂_t` is
applied, and needs no completeness since no Hilbert adjoint appears.

## Main results

* `TauCeti.setIntegral_im_pos_inner_cauchyRiemann_adjoint`: the formula above on the half-plane,
  for `ξ`, `J` only `C¹` and `S` only continuous on an open set containing the support of `φ`.
* `TauCeti.setIntegral_halfDisc_inner_cauchyRiemann_adjoint`: the same formula on the half-disc
  `D⁺_r = {|z| < r, 0 < t}` for `φ` supported in the open disc of radius `r`, with boundary term
  over `(-r, r)`.
* `TauCeti.setIntegral_im_pos_inner_cauchyRiemann_adjoint_of_inner_eq_zero` and
  `TauCeti.setIntegral_halfDisc_inner_cauchyRiemann_adjoint_of_inner_eq_zero`: if the boundary
  integrand `⟪φ(s), J(s) ξ(s)⟫` vanishes, the weak equation (B.4.3) holds.
* `TauCeti.setIntegral_im_pos_inner_cauchyRiemann_adjoint_of_mem` and
  `TauCeti.setIntegral_halfDisc_inner_cauchyRiemann_adjoint_of_mem`: the same when `φ` and `ξ`
  take values on `ℝ` in a set `F` with `⟪F, J(s) F⟫ = 0`.

## References

* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, second edition,
  Appendix B.4, equation (B.4.3).
-/

public section

open Complex MeasureTheory Metric Set
open scoped InnerProductSpace

namespace TauCeti

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  {φ ξ : ℂ → V} {J S : ℂ → V →L[ℝ] V} {U : Set ℂ}

/-- **Green's formula for `∂_s + J ∂_t + S` on the half-plane.** For a compactly supported `C¹`
map `φ`, and `ξ`, `J` of class `C¹` and `S` continuous on an open set containing the support of
`φ`,

`∫_{0 < t} ⟪∂_s φ + Jᵀ ∂_t φ - Sᵀ φ, ξ⟫ =
  -∫_{0 < t} ⟪φ, ∂_s ξ + J ∂_t ξ + S ξ + (∂_t J) ξ⟫ - ∫_ℝ ⟪φ(s), J(s) ξ(s)⟫ ds`.

This is McDuff–Salamon (B.4.3) for a classical solution, before imposing a boundary
condition. -/
theorem setIntegral_im_pos_inner_cauchyRiemann_adjoint (hφ : ContDiff ℝ 1 φ)
    (hφc : HasCompactSupport φ) (hU : IsOpen U) (hξ : ContDiffOn ℝ 1 ξ U)
    (hJ : ContDiffOn ℝ 1 J U) (hS : ContinuousOn S U) (hφU : tsupport φ ⊆ U) :
    ∫ z in {z : ℂ | 0 < z.im}, ⟪fderiv ℝ φ z 1 + ContinuousLinearMap.adjoint (J z)
        (fderiv ℝ φ z I) - ContinuousLinearMap.adjoint (S z) (φ z), ξ z⟫_ℝ =
      -(∫ z in {z : ℂ | 0 < z.im}, ⟪φ z, fderiv ℝ ξ z 1 + J z (fderiv ℝ ξ z I) + S z (ξ z) +
        fderiv ℝ J z I (ξ z)⟫_ℝ) - ∫ s : ℝ, ⟪φ s, J s (ξ s)⟫_ℝ := by
  have hφd := hφ.differentiable one_ne_zero
  have hJξ : ContDiffOn ℝ 1 (fun z ↦ J z (ξ z)) U := hJ.clm_apply hξ
  -- The pairings `h = ⟪ξ, φ⟫` and `g = ⟪J ξ, φ⟫` are compactly supported and `C¹` on `ℂ`.
  set h : ℂ → ℝ := fun z ↦ innerSL ℝ (ξ z) (φ z)
  set g : ℂ → ℝ := fun z ↦ innerSL ℝ (J z (ξ z)) (φ z)
  have hh : ContDiff ℝ 1 h := (innerSL ℝ).contDiff_of_tsupport_subset_right hξ hφ.contDiffOn hU hφU
  have hg : ContDiff ℝ 1 g :=
    (innerSL ℝ).contDiff_of_tsupport_subset_right hJξ hφ.contDiffOn hU hφU
  have hhc : HasCompactSupport h := hφc.mono fun z hz h0 ↦ hz (by simp [h, h0])
  have hgc : HasCompactSupport g := hφc.mono fun z hz h0 ↦ hz (by simp [g, h0])
  have hh' (z v : ℂ) : fderiv ℝ h z v = ⟪ξ z, fderiv ℝ φ z v⟫_ℝ + ⟪fderiv ℝ ξ z v, φ z⟫_ℝ := by
    rw [(innerSL ℝ).fderiv_of_tsupport_subset_right (hξ.differentiableOn one_ne_zero) hφd hU hφU]
    simp only [add_apply, ContinuousLinearMap.precompR_apply, ContinuousLinearMap.precompL_apply,
      ContinuousLinearMap.compL_apply, ContinuousLinearMap.comp_apply]
    exact congrArg₂ (· + ·) (innerSL_apply_apply (𝕜 := ℝ) _ _) (innerSL_apply_apply (𝕜 := ℝ) _ _)
  have hg' (z v : ℂ) : fderiv ℝ g z v =
      ⟪J z (ξ z), fderiv ℝ φ z v⟫_ℝ + ⟪fderiv ℝ (fun z ↦ J z (ξ z)) z v, φ z⟫_ℝ := by
    rw [(innerSL ℝ).fderiv_of_tsupport_subset_right (hJξ.differentiableOn one_ne_zero) hφd hU hφU]
    simp only [add_apply, ContinuousLinearMap.precompR_apply, ContinuousLinearMap.precompL_apply,
      ContinuousLinearMap.compL_apply, ContinuousLinearMap.comp_apply]
    exact congrArg₂ (· + ·) (innerSL_apply_apply (𝕜 := ℝ) _ _) (innerSL_apply_apply (𝕜 := ℝ) _ _)
  -- Pointwise, the left integrand is `∂_s h + ∂_t g` minus the right volume integrand `F`.
  set F : ℂ → ℝ := fun z ↦
    ⟪φ z, fderiv ℝ ξ z 1 + J z (fderiv ℝ ξ z I) + S z (ξ z) + fderiv ℝ J z I (ξ z)⟫_ℝ
  have hpt (z : ℂ) : ⟪fderiv ℝ φ z 1 + ContinuousLinearMap.adjoint (J z) (fderiv ℝ φ z I) -
      ContinuousLinearMap.adjoint (S z) (φ z), ξ z⟫_ℝ =
        fderiv ℝ h z 1 + fderiv ℝ g z I - F z := by
    by_cases hz : z ∈ tsupport φ
    · have hzU : U ∈ nhds z := hU.mem_nhds (hφU hz)
      have hJd := (hJ.differentiableOn one_ne_zero z (hφU hz)).differentiableAt hzU
      have hξd := (hξ.differentiableOn one_ne_zero z (hφU hz)).differentiableAt hzU
      rw [hh', hg', fderiv_clm_apply hJd hξd]
      simp only [F, inner_add_left, inner_sub_left, inner_add_right,
        ContinuousLinearMap.adjoint_inner_left, add_apply,
        ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply]
      rw [real_inner_comm (ξ z), real_inner_comm (J z (ξ z)),
        real_inner_comm (φ z) (fderiv ℝ ξ z 1), real_inner_comm (φ z) (J z (fderiv ℝ ξ z I)),
        real_inner_comm (φ z) (fderiv ℝ J z I (ξ z))]
      ring
    · simp [hh', hg', F, fderiv_of_notMem_tsupport ℝ hz, image_eq_zero_of_notMem_tsupport hz]
  -- The three terms are integrable, and the directional Green identities apply to `h` and `g`.
  have hA : Integrable fun z ↦ fderiv ℝ h z 1 :=
    ((hh.continuous_fderiv one_ne_zero).clm_apply continuous_const).integrable_of_hasCompactSupport
      (hhc.fderiv_apply (𝕜 := ℝ) 1)
  have hB : Integrable fun z ↦ fderiv ℝ g z I :=
    ((hg.continuous_fderiv one_ne_zero).clm_apply continuous_const).integrable_of_hasCompactSupport
      (hgc.fderiv_apply (𝕜 := ℝ) I)
  have hF : Integrable F := by
    have hdξ := hξ.continuousOn_fderiv_of_isOpen hU le_rfl
    have hdJ := hJ.continuousOn_fderiv_of_isOpen hU le_rfl
    have hcont : ContinuousOn F U :=
      hφ.continuous.continuousOn.inner ((((hdξ.clm_apply continuousOn_const).add
        (hJ.continuousOn.clm_apply (hdξ.clm_apply continuousOn_const))).add
        (hS.clm_apply hξ.continuousOn)).add
        ((hdJ.clm_apply continuousOn_const).clm_apply hξ.continuousOn))
    refine IntegrableOn.integrable_of_forall_notMem_eq_zero
      ((hcont.mono hφU).integrableOn_compact hφc) fun z hz ↦ ?_
    simp [F, image_eq_zero_of_notMem_tsupport hz]
  simp_rw [hpt]
  rw [integral_sub (f := fun z ↦ fderiv ℝ h z 1 + fderiv ℝ g z I) (hA.add hB).integrableOn
      hF.integrableOn,
    integral_add hA.integrableOn hB.integrableOn, setIntegral_im_pos_fderiv_one_eq_zero hh hhc,
    setIntegral_im_pos_fderiv_I_eq_neg_integral hg hgc, zero_add]
  simp only [g, innerSL_apply_apply, real_inner_comm (φ _)]
  ring

/-- **Green's formula for `∂_s + J ∂_t + S` on the half-disc.** For `φ` supported in the open
disc of radius `r`, and `ξ`, `J` of class `C¹` and `S` continuous there, the formula of
`setIntegral_im_pos_inner_cauchyRiemann_adjoint` holds on the half-disc
`D⁺_r = {|z| < r, 0 < t}`, with boundary term over `(-r, r)`. -/
theorem setIntegral_halfDisc_inner_cauchyRiemann_adjoint {r : ℝ} (hφ : ContDiff ℝ 1 φ)
    (hξ : ContDiffOn ℝ 1 ξ (ball 0 r))
    (hJ : ContDiffOn ℝ 1 J (ball 0 r)) (hS : ContinuousOn S (ball 0 r))
    (hφr : tsupport φ ⊆ ball 0 r) :
    ∫ z in ball 0 r ∩ {z : ℂ | 0 < z.im}, ⟪fderiv ℝ φ z 1 + ContinuousLinearMap.adjoint (J z)
        (fderiv ℝ φ z I) - ContinuousLinearMap.adjoint (S z) (φ z), ξ z⟫_ℝ =
      -(∫ z in ball 0 r ∩ {z : ℂ | 0 < z.im}, ⟪φ z, fderiv ℝ ξ z 1 + J z (fderiv ℝ ξ z I) +
        S z (ξ z) + fderiv ℝ J z I (ξ z)⟫_ℝ) - ∫ s in Ioo (-r) r, ⟪φ s, J s (ξ s)⟫_ℝ := by
  have hout {z : ℂ} (hz : z ∉ ball 0 r) : z ∉ tsupport φ := fun h ↦ hz (hφr h)
  have hφc : HasCompactSupport φ := (isCompact_closedBall (0 : ℂ) r).of_isClosed_subset
    (isClosed_tsupport φ) (hφr.trans ball_subset_closedBall)
  rw [setIntegral_inter_im_pos_eq_setIntegral_im_pos fun z _ hz ↦ by
      simp [fderiv_of_notMem_tsupport ℝ (hout hz), image_eq_zero_of_notMem_tsupport (hout hz)],
    setIntegral_inter_im_pos_eq_setIntegral_im_pos fun z _ hz ↦ by
      simp [image_eq_zero_of_notMem_tsupport (hout hz)],
    setIntegral_Ioo_eq_integral_of_ofReal_notMem_ball fun s hs ↦ by
      simp [image_eq_zero_of_notMem_tsupport (hout hs)]]
  exact setIntegral_im_pos_inner_cauchyRiemann_adjoint hφ hφc isOpen_ball hξ hJ hS hφr

/-- **The weak equation (B.4.3) on the half-plane.** If the boundary integrand
`⟪φ(s), J(s) ξ(s)⟫` vanishes at every real `s` in `U`, the boundary term of
`setIntegral_im_pos_inner_cauchyRiemann_adjoint` vanishes:
`∫_{0 < t} ⟪∂_s φ + Jᵀ ∂_t φ - Sᵀ φ, ξ⟫ = -∫_{0 < t} ⟪φ, D ξ + (∂_t J) ξ⟫`. -/
theorem setIntegral_im_pos_inner_cauchyRiemann_adjoint_of_inner_eq_zero (hφ : ContDiff ℝ 1 φ)
    (hφc : HasCompactSupport φ) (hU : IsOpen U) (hξ : ContDiffOn ℝ 1 ξ U)
    (hJ : ContDiffOn ℝ 1 J U) (hS : ContinuousOn S U) (hφU : tsupport φ ⊆ U)
    (h : ∀ s : ℝ, (s : ℂ) ∈ U → ⟪φ s, J s (ξ s)⟫_ℝ = 0) :
    ∫ z in {z : ℂ | 0 < z.im}, ⟪fderiv ℝ φ z 1 + ContinuousLinearMap.adjoint (J z)
        (fderiv ℝ φ z I) - ContinuousLinearMap.adjoint (S z) (φ z), ξ z⟫_ℝ =
      -∫ z in {z : ℂ | 0 < z.im}, ⟪φ z, fderiv ℝ ξ z 1 + J z (fderiv ℝ ξ z I) + S z (ξ z) +
        fderiv ℝ J z I (ξ z)⟫_ℝ := by
  have h' (s : ℝ) : ⟪φ s, J s (ξ s)⟫_ℝ = 0 := by
    by_cases hs : (s : ℂ) ∈ U
    · exact h s hs
    · simp [image_eq_zero_of_notMem_tsupport fun h ↦ hs (hφU h)]
  rw [setIntegral_im_pos_inner_cauchyRiemann_adjoint hφ hφc hU hξ hJ hS hφU]
  simp [h']

/-- **The weak equation (B.4.3) on the half-disc.** If the boundary integrand
`⟪φ(s), J(s) ξ(s)⟫` vanishes on `(-r, r)`, the boundary term of
`setIntegral_halfDisc_inner_cauchyRiemann_adjoint` vanishes. -/
theorem setIntegral_halfDisc_inner_cauchyRiemann_adjoint_of_inner_eq_zero {r : ℝ}
    (hφ : ContDiff ℝ 1 φ) (hξ : ContDiffOn ℝ 1 ξ (ball 0 r))
    (hJ : ContDiffOn ℝ 1 J (ball 0 r)) (hS : ContinuousOn S (ball 0 r))
    (hφr : tsupport φ ⊆ ball 0 r) (h : ∀ s ∈ Ioo (-r) r, ⟪φ s, J s (ξ s)⟫_ℝ = 0) :
    ∫ z in ball 0 r ∩ {z : ℂ | 0 < z.im}, ⟪fderiv ℝ φ z 1 + ContinuousLinearMap.adjoint (J z)
        (fderiv ℝ φ z I) - ContinuousLinearMap.adjoint (S z) (φ z), ξ z⟫_ℝ =
      -∫ z in ball 0 r ∩ {z : ℂ | 0 < z.im}, ⟪φ z, fderiv ℝ ξ z 1 + J z (fderiv ℝ ξ z I) +
        S z (ξ z) + fderiv ℝ J z I (ξ z)⟫_ℝ := by
  rw [setIntegral_halfDisc_inner_cauchyRiemann_adjoint hφ hξ hJ hS hφr,
    setIntegral_eq_zero_of_forall_eq_zero h, sub_zero]

/-- **The weak equation (B.4.3) on the half-plane, for a boundary set.** If on `ℝ ∩ U` the maps
`φ` and `ξ` take values in a set `F` with `⟪F, J(s) F⟫ = 0`, for instance `F = ℝⁿ ⊆ ℂⁿ` and
`J(s) = i`, the boundary term of `setIntegral_im_pos_inner_cauchyRiemann_adjoint` vanishes. -/
theorem setIntegral_im_pos_inner_cauchyRiemann_adjoint_of_mem {F : Set V}
    (hφ : ContDiff ℝ 1 φ) (hφc : HasCompactSupport φ) (hU : IsOpen U) (hξ : ContDiffOn ℝ 1 ξ U)
    (hJ : ContDiffOn ℝ 1 J U) (hS : ContinuousOn S U) (hφU : tsupport φ ⊆ U)
    (hJF : ∀ s : ℝ, (s : ℂ) ∈ U → ∀ v ∈ F, ∀ w ∈ F, ⟪v, J s w⟫_ℝ = 0)
    (hφF : ∀ s : ℝ, (s : ℂ) ∈ U → φ s ∈ F) (hξF : ∀ s : ℝ, (s : ℂ) ∈ U → ξ s ∈ F) :
    ∫ z in {z : ℂ | 0 < z.im}, ⟪fderiv ℝ φ z 1 + ContinuousLinearMap.adjoint (J z)
        (fderiv ℝ φ z I) - ContinuousLinearMap.adjoint (S z) (φ z), ξ z⟫_ℝ =
      -∫ z in {z : ℂ | 0 < z.im}, ⟪φ z, fderiv ℝ ξ z 1 + J z (fderiv ℝ ξ z I) + S z (ξ z) +
        fderiv ℝ J z I (ξ z)⟫_ℝ :=
  setIntegral_im_pos_inner_cauchyRiemann_adjoint_of_inner_eq_zero hφ hφc hU hξ hJ hS hφU
    fun s hs ↦ hJF s hs _ (hφF s hs) _ (hξF s hs)

/-- **The weak equation (B.4.3) on the half-disc, for a boundary set.** If on `(-r, r)` the maps
`φ` and `ξ` take values in a set `F` with `⟪F, J(s) F⟫ = 0`, the boundary term of
`setIntegral_halfDisc_inner_cauchyRiemann_adjoint` vanishes. -/
theorem setIntegral_halfDisc_inner_cauchyRiemann_adjoint_of_mem {F : Set V} {r : ℝ}
    (hφ : ContDiff ℝ 1 φ) (hξ : ContDiffOn ℝ 1 ξ (ball 0 r))
    (hJ : ContDiffOn ℝ 1 J (ball 0 r)) (hS : ContinuousOn S (ball 0 r))
    (hφr : tsupport φ ⊆ ball 0 r)
    (hJF : ∀ s ∈ Ioo (-r) r, ∀ v ∈ F, ∀ w ∈ F, ⟪v, J s w⟫_ℝ = 0)
    (hφF : ∀ s ∈ Ioo (-r) r, φ s ∈ F) (hξF : ∀ s ∈ Ioo (-r) r, ξ s ∈ F) :
    ∫ z in ball 0 r ∩ {z : ℂ | 0 < z.im}, ⟪fderiv ℝ φ z 1 + ContinuousLinearMap.adjoint (J z)
        (fderiv ℝ φ z I) - ContinuousLinearMap.adjoint (S z) (φ z), ξ z⟫_ℝ =
      -∫ z in ball 0 r ∩ {z : ℂ | 0 < z.im}, ⟪φ z, fderiv ℝ ξ z 1 + J z (fderiv ℝ ξ z I) +
        S z (ξ z) + fderiv ℝ J z I (ξ z)⟫_ℝ :=
  setIntegral_halfDisc_inner_cauchyRiemann_adjoint_of_inner_eq_zero hφ hξ hJ hS hφr
    fun s hs ↦ hJF s hs _ (hφF s hs) _ (hξF s hs)

end TauCeti
