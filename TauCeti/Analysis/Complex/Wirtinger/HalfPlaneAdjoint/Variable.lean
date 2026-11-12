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

The boundary integrand `⟪φ(s), J(s) ξ(s)⟫` vanishes when `φ(s)` and `ξ(s)` lie in a real
subspace `F` with `⟪v, J(s) w⟫ = 0` for all `v, w ∈ F`. For `J(s) = i` and `F = ℝⁿ ⊆ ℂⁿ` this is
the totally real boundary condition `φ(s), ξ(s) ∈ ℝⁿ` of the roadmap. In that case the left side
is the weak formulation tested against test functions that are real on `ℝ` but need not vanish
there, so a classical solution with real boundary values is a weak solution in the sense of
(B.4.3). For `V = ℂ` the condition on `F = ℝ` is `Real.inner_ofReal_I_mul_ofReal`. The
constant-coefficient formula `TauCeti.setIntegral_im_pos_re_inner_cauchyRiemann`, with its
analysis of the dual boundary condition, is the case `J = i`, `S = 0` on a complex inner product
space.

## Main results

* `TauCeti.setIntegral_im_pos_inner_cauchyRiemann_adjoint`: the formula above on the half-plane,
  for `ξ`, `J` only `C¹` and `S` only continuous on an open set containing the support of `φ`.
* `TauCeti.setIntegral_halfDisc_inner_cauchyRiemann_adjoint`: the same formula on the half-disc
  `D⁺_r = {|z| < r, 0 < t}` for `φ` supported in the open disc of radius `r`, with boundary term
  over `(-r, r)`.
* `TauCeti.setIntegral_im_pos_inner_cauchyRiemann_adjoint_of_mem` and
  `TauCeti.setIntegral_halfDisc_inner_cauchyRiemann_adjoint_of_mem`: if `φ` and `ξ` take values
  on `ℝ` in a subspace `F` with `⟪F, J(s) F⟫ = 0`, the boundary term vanishes and the weak
  equation (B.4.3) holds.

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
  set h : ℂ → ℝ := fun z ↦ innerSL ℝ (ξ z) (φ z)
  set g : ℂ → ℝ := fun z ↦ innerSL ℝ (J z (ξ z)) (φ z)
  have hh : ContDiff ℝ 1 h := (innerSL ℝ).contDiff_of_tsupport_subset_right hξ hφ.contDiffOn hU hφU
  have hg : ContDiff ℝ 1 g :=
    (innerSL ℝ).contDiff_of_tsupport_subset_right hJξ hφ.contDiffOn hU hφU
  have hhc : HasCompactSupport h := hφc.mono fun z hz h0 ↦ hz (by simp [h, h0])
  have hgc : HasCompactSupport g := hφc.mono fun z hz h0 ↦ hz (by simp [g, h0])
  have hh' (z v : ℂ) : fderiv ℝ h z v = ⟪ξ z, fderiv ℝ φ z v⟫_ℝ + ⟪fderiv ℝ ξ z v, φ z⟫_ℝ := by
    rw [(innerSL ℝ).fderiv_of_tsupport_subset_right (hξ.differentiableOn one_ne_zero) hφd hU hφU]
    rfl
  have hg' (z v : ℂ) : fderiv ℝ g z v =
      ⟪J z (ξ z), fderiv ℝ φ z v⟫_ℝ + ⟪fderiv ℝ (fun z ↦ J z (ξ z)) z v, φ z⟫_ℝ := by
    rw [(innerSL ℝ).fderiv_of_tsupport_subset_right (hJξ.differentiableOn one_ne_zero) hφd hU hφU]
    rfl
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
    (hφc : HasCompactSupport φ) (hξ : ContDiffOn ℝ 1 ξ (ball 0 r))
    (hJ : ContDiffOn ℝ 1 J (ball 0 r)) (hS : ContinuousOn S (ball 0 r))
    (hφr : tsupport φ ⊆ ball 0 r) :
    ∫ z in ball 0 r ∩ {z : ℂ | 0 < z.im}, ⟪fderiv ℝ φ z 1 + ContinuousLinearMap.adjoint (J z)
        (fderiv ℝ φ z I) - ContinuousLinearMap.adjoint (S z) (φ z), ξ z⟫_ℝ =
      -(∫ z in ball 0 r ∩ {z : ℂ | 0 < z.im}, ⟪φ z, fderiv ℝ ξ z 1 + J z (fderiv ℝ ξ z I) +
        S z (ξ z) + fderiv ℝ J z I (ξ z)⟫_ℝ) - ∫ s in Ioo (-r) r, ⟪φ s, J s (ξ s)⟫_ℝ := by
  have hH : MeasurableSet {z : ℂ | 0 < z.im} :=
    measurableSet_lt measurable_const Complex.measurable_im
  have hout {z : ℂ} (hz : z ∉ ball 0 r) : z ∉ tsupport φ := fun h ↦ hz (hφr h)
  have h₁ : ∫ z in ball 0 r ∩ {z : ℂ | 0 < z.im}, ⟪fderiv ℝ φ z 1 +
      ContinuousLinearMap.adjoint (J z) (fderiv ℝ φ z I) -
        ContinuousLinearMap.adjoint (S z) (φ z), ξ z⟫_ℝ =
      ∫ z in {z : ℂ | 0 < z.im}, ⟪fderiv ℝ φ z 1 +
        ContinuousLinearMap.adjoint (J z) (fderiv ℝ φ z I) -
          ContinuousLinearMap.adjoint (S z) (φ z), ξ z⟫_ℝ :=
    (setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hH inter_subset_right fun z hz ↦ by
      have hz' := hout fun h ↦ hz.2 ⟨h, hz.1⟩
      simp [fderiv_of_notMem_tsupport ℝ hz', image_eq_zero_of_notMem_tsupport hz']).symm
  have h₂ : ∫ z in ball 0 r ∩ {z : ℂ | 0 < z.im}, ⟪φ z, fderiv ℝ ξ z 1 + J z (fderiv ℝ ξ z I) +
      S z (ξ z) + fderiv ℝ J z I (ξ z)⟫_ℝ =
      ∫ z in {z : ℂ | 0 < z.im}, ⟪φ z, fderiv ℝ ξ z 1 + J z (fderiv ℝ ξ z I) +
        S z (ξ z) + fderiv ℝ J z I (ξ z)⟫_ℝ :=
    (setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hH inter_subset_right fun z hz ↦ by
      simp [image_eq_zero_of_notMem_tsupport (hout fun h ↦ hz.2 ⟨h, hz.1⟩)]).symm
  have h₃ : ∫ s in Ioo (-r) r, ⟪φ s, J s (ξ s)⟫_ℝ = ∫ s : ℝ, ⟪φ s, J s (ξ s)⟫_ℝ := by
    refine setIntegral_eq_integral_of_forall_compl_eq_zero fun s hs ↦ ?_
    have hs' : (s : ℂ) ∉ ball 0 r := fun h ↦ hs (by
      rwa [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs, abs_lt] at h)
    simp [image_eq_zero_of_notMem_tsupport (hout hs')]
  rw [h₁, h₂, h₃]
  exact setIntegral_im_pos_inner_cauchyRiemann_adjoint hφ hφc isOpen_ball hξ hJ hS hφr

omit [CompleteSpace V] in
/-- On `ℝ`, the boundary integrand `⟪φ(s), J(s) ξ(s)⟫` vanishes when `φ(s)` and `ξ(s)` lie in a
subspace `F` with `⟪F, J(s) F⟫ = 0`, at every `s` in `U` and outside the support of `φ`. -/
private theorem inner_apply_eq_zero_of_mem (F : Submodule ℝ V) (hφU : tsupport φ ⊆ U)
    (hJF : ∀ s : ℝ, (s : ℂ) ∈ U → ∀ v ∈ F, ∀ w ∈ F, ⟪v, J s w⟫_ℝ = 0)
    (hφF : ∀ s : ℝ, φ s ∈ F) (hξF : ∀ s : ℝ, (s : ℂ) ∈ U → ξ s ∈ F) (s : ℝ) :
    ⟪φ s, J s (ξ s)⟫_ℝ = 0 := by
  by_cases hs : (s : ℂ) ∈ U
  · exact hJF s hs _ (hφF s) _ (hξF s hs)
  · simp [image_eq_zero_of_notMem_tsupport fun h ↦ hs (hφU h)]

/-- **The weak equation (B.4.3) on the half-plane.** If on `ℝ` the maps `φ` and `ξ` take values
in a subspace `F` with `⟪F, J(s) F⟫ = 0`, for instance `F = ℝⁿ ⊆ ℂⁿ` and `J(s) = i`, the boundary
term of `setIntegral_im_pos_inner_cauchyRiemann_adjoint` vanishes:
`∫_{0 < t} ⟪∂_s φ + Jᵀ ∂_t φ - Sᵀ φ, ξ⟫ = -∫_{0 < t} ⟪φ, D ξ + (∂_t J) ξ⟫`. -/
theorem setIntegral_im_pos_inner_cauchyRiemann_adjoint_of_mem {F : Submodule ℝ V}
    (hφ : ContDiff ℝ 1 φ) (hφc : HasCompactSupport φ) (hU : IsOpen U) (hξ : ContDiffOn ℝ 1 ξ U)
    (hJ : ContDiffOn ℝ 1 J U) (hS : ContinuousOn S U) (hφU : tsupport φ ⊆ U)
    (hJF : ∀ s : ℝ, (s : ℂ) ∈ U → ∀ v ∈ F, ∀ w ∈ F, ⟪v, J s w⟫_ℝ = 0)
    (hφF : ∀ s : ℝ, φ s ∈ F) (hξF : ∀ s : ℝ, (s : ℂ) ∈ U → ξ s ∈ F) :
    ∫ z in {z : ℂ | 0 < z.im}, ⟪fderiv ℝ φ z 1 + ContinuousLinearMap.adjoint (J z)
        (fderiv ℝ φ z I) - ContinuousLinearMap.adjoint (S z) (φ z), ξ z⟫_ℝ =
      -∫ z in {z : ℂ | 0 < z.im}, ⟪φ z, fderiv ℝ ξ z 1 + J z (fderiv ℝ ξ z I) + S z (ξ z) +
        fderiv ℝ J z I (ξ z)⟫_ℝ := by
  rw [setIntegral_im_pos_inner_cauchyRiemann_adjoint hφ hφc hU hξ hJ hS hφU]
  simp [inner_apply_eq_zero_of_mem F hφU hJF hφF hξF]

/-- **The weak equation (B.4.3) on the half-disc.** If on `(-r, r)` the maps `φ` and `ξ` take
values in a subspace `F` with `⟪F, J(s) F⟫ = 0`, the boundary term of
`setIntegral_halfDisc_inner_cauchyRiemann_adjoint` vanishes. -/
theorem setIntegral_halfDisc_inner_cauchyRiemann_adjoint_of_mem {F : Submodule ℝ V} {r : ℝ}
    (hφ : ContDiff ℝ 1 φ) (hφc : HasCompactSupport φ) (hξ : ContDiffOn ℝ 1 ξ (ball 0 r))
    (hJ : ContDiffOn ℝ 1 J (ball 0 r)) (hS : ContinuousOn S (ball 0 r))
    (hφr : tsupport φ ⊆ ball 0 r)
    (hJF : ∀ s : ℝ, (s : ℂ) ∈ ball 0 r → ∀ v ∈ F, ∀ w ∈ F, ⟪v, J s w⟫_ℝ = 0)
    (hφF : ∀ s : ℝ, φ s ∈ F) (hξF : ∀ s : ℝ, (s : ℂ) ∈ ball 0 r → ξ s ∈ F) :
    ∫ z in ball 0 r ∩ {z : ℂ | 0 < z.im}, ⟪fderiv ℝ φ z 1 + ContinuousLinearMap.adjoint (J z)
        (fderiv ℝ φ z I) - ContinuousLinearMap.adjoint (S z) (φ z), ξ z⟫_ℝ =
      -∫ z in ball 0 r ∩ {z : ℂ | 0 < z.im}, ⟪φ z, fderiv ℝ ξ z 1 + J z (fderiv ℝ ξ z I) +
        S z (ξ z) + fderiv ℝ J z I (ξ z)⟫_ℝ := by
  rw [setIntegral_halfDisc_inner_cauchyRiemann_adjoint hφ hφc hξ hJ hS hφr]
  simp [inner_apply_eq_zero_of_mem F hφr hJF hφF hξF]

end TauCeti
