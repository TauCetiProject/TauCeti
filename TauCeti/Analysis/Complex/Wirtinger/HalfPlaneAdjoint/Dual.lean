/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
public import TauCeti.Analysis.Complex.CauchyRiemann.RoughCoefficients.Weak
public import TauCeti.Analysis.Complex.Wirtinger.HalfPlaneAdjoint.Variable
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff
import TauCeti.Analysis.Complex.Wirtinger.HalfPlaneAdjoint.Basic

/-!
# Lemma C.1.9 on the half-plane with variable coefficients and the dual boundary condition

Let `V` be a real inner product space, write `z = s + i t`, and let `J, S : ℂ → (V →L[ℝ] V)` be
coefficient fields, with `J` of class `C¹` and `S` continuous. For the real Cauchy–Riemann
operator `D ξ = ∂_s ξ + J ∂_t ξ + S ξ` and its formal adjoint
`D* φ = -∂_s φ - Jᵀ ∂_t φ - (∂_t J)ᵀ φ + Sᵀ φ` (`TauCeti.crFormalAdjoint J (fderiv ℝ J) S`, the
normalization of the weak equation `TauCeti.IsWeakCRSolution`), integration by parts over the
half-plane `{0 < t}` gives

`∫_{0 < t} ⟪D* φ, ξ⟫ = ∫_{0 < t} ⟪φ, D ξ⟫ + ∫_ℝ ⟪φ(s), J(s) ξ(s)⟫ ds`

for `C¹` maps `φ`, `ξ` with `tsupport φ ∩ tsupport ξ` compact, so either factor may be the
compactly supported test map. The `∂_t J` term of `D*` cancels the derivative of `J` produced by
integrating `J ∂_t ξ` by parts. So `∫ ⟪D* φ, ξ⟫ = ∫ ⟪φ, D ξ⟫` as soon as the boundary integrand
vanishes: this is McDuff–Salamon Lemma C.1.9 on the half-plane.

If `ξ` satisfies the boundary condition `ξ(s) ∈ Λ` for a real subspace `Λ`, the boundary term
vanishes for every such `ξ` exactly when `φ(s) ⊥ J(s) Λ` for every real `s`
(`Submodule.forall_integral_inner_clm_apply_eq_zero_iff`): this is the dual boundary condition
carried by `D*`. It depends on `J(s)` and not only on `Λ`. When `Λ` admits an orthogonal
projection and `J(s)` maps `Λ` onto `Λᗮ`, as for a metric compatible with a totally real
boundary condition (the bundle statement along the boundary is
`TauCeti.exists_contMDiffRiemannianMetric_compatible_totallyReal_on`), the dual condition is
again `φ(s) ∈ Λ`, so `D*` carries the same boundary condition as `D`.

The case `J = i`, `S = 0` on a complex inner product space, with the same normalization
`D* = -∂_s + i ∂_t`, is `TauCeti.setIntegral_im_pos_re_inner_cauchyRiemann`, which places the
compact support on `ξ` and needs no completeness, and
`Submodule.forall_integral_re_inner_I_smul_eq_zero_iff`.

## Main results

* `TauCeti.setIntegral_im_pos_inner_crFormalAdjoint`: the formula above on the half-plane, for
  `φ`, `ξ`, `J` only `C¹` and `S` only continuous on an open set containing
  `tsupport φ ∩ tsupport ξ`, and `TauCeti.setIntegral_halfDisc_inner_crFormalAdjoint` on the
  half-disc `D⁺_r = {|z| < r, 0 < t}`.
* `TauCeti.setIntegral_im_pos_inner_crFormalAdjoint_of_inner_eq_zero` and
  `TauCeti.setIntegral_halfDisc_inner_crFormalAdjoint_of_inner_eq_zero`: Lemma C.1.9,
  `∫ ⟪D* φ, ξ⟫ = ∫ ⟪φ, D ξ⟫` on the half-plane and on the half-disc, when
  `⟪φ(s), J(s) ξ(s)⟫ = 0` on the real axis.
* `Submodule.forall_integral_inner_clm_apply_eq_zero_iff_mem_of_isOpen` and
  `Submodule.forall_integral_inner_clm_apply_eq_zero_iff_mem`: if `Λ` admits an orthogonal
  projection and `J(s)` maps `Λ` onto `Λᗮ`, the dual condition is `η(s) ∈ Λ`, on `U ∩ ℝ` for an
  open `U ⊆ ℂ` or on all of `ℝ`.
* Check: `TauCeti.comp_self_eq_neg_one_and_not_forall_integral_inner_one_clm_apply_eq_zero` (for
  the complex structure `A i A⁻¹` on `ℂ` and `Λ = ℝ`, the constant `η = 1`, which satisfies the
  dual condition of `i`, violates the dual condition). The wrong dual condition `η(s) ∈ J(s) Λ`
  leaves a positive boundary term by `TauCeti.integral_inner_clm_apply_pos`.

## References

* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, second edition,
  Lemma C.1.9.
-/

public section

open Complex MeasureTheory Metric Set Filter
open scoped InnerProductSpace ContDiff Topology

namespace TauCeti

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  {φ ξ : ℂ → V} {J S : ℂ → V →L[ℝ] V} {U : Set ℂ}

/-- Off `tsupport φ ∩ tsupport ξ`, the three integrands of Green's formula for the formal adjoint
vanish. -/
private theorem inner_eq_zero_of_notMem_tsupport_inter {z : ℂ}
    (hz : z ∉ tsupport φ ∩ tsupport ξ) :
    ⟪crFormalAdjoint J (fderiv ℝ J) S φ z, ξ z⟫_ℝ = 0 ∧
      ⟪φ z, fderiv ℝ ξ z 1 + J z (fderiv ℝ ξ z I) + S z (ξ z)⟫_ℝ = 0 ∧
        ⟪φ z, J z (ξ z)⟫_ℝ = 0 := by
  rcases not_and_or.1 hz with h | h
  · simp [crFormalAdjoint_of_notMem_tsupport h, image_eq_zero_of_notMem_tsupport h]
  · simp [fderiv_of_notMem_tsupport ℝ h, image_eq_zero_of_notMem_tsupport h]

/-- **Green's formula for the formal adjoint on the half-plane.** For `φ`, `ξ`, `J` of class `C¹`
and `S` continuous on an open set `U` containing the compact set `tsupport φ ∩ tsupport ξ`,

`∫_{0 < t} ⟪D* φ, ξ⟫ = ∫_{0 < t} ⟪φ, ∂_s ξ + J ∂_t ξ + S ξ⟫ + ∫_ℝ ⟪φ(s), J(s) ξ(s)⟫ ds`,

where `D*` is `TauCeti.crFormalAdjoint J (fderiv ℝ J) S`. Either factor may carry the compact
support: `φ` as a test map against a solution `ξ`, or `ξ` as a test map against a dual
solution `φ`. -/
theorem setIntegral_im_pos_inner_crFormalAdjoint (hU : IsOpen U) (hφ : ContDiffOn ℝ 1 φ U)
    (hξ : ContDiffOn ℝ 1 ξ U) (hJ : ContDiffOn ℝ 1 J U) (hS : ContinuousOn S U)
    (hc : IsCompact (tsupport φ ∩ tsupport ξ)) (hφξU : tsupport φ ∩ tsupport ξ ⊆ U) :
    ∫ z in {z : ℂ | 0 < z.im}, ⟪crFormalAdjoint J (fderiv ℝ J) S φ z, ξ z⟫_ℝ =
      (∫ z in {z : ℂ | 0 < z.im}, ⟪φ z, fderiv ℝ ξ z 1 + J z (fderiv ℝ ξ z I) + S z (ξ z)⟫_ℝ) +
        ∫ s : ℝ, ⟪φ s, J s (ξ s)⟫_ℝ := by
  -- Cut `φ` off to `φ'`, compactly supported in `U` and equal to `φ` near `tsupport ξ`.
  obtain ⟨χ, hχ, -, hχ1, hχc, hχU⟩ := hc.exists_contDiff_cutoff_eventuallyEq_one hU hφξU
  set φ' : ℂ → V := fun z ↦ χ z • φ z
  have hφ' : ContDiff ℝ 1 φ' :=
    hφ.contDiff_smul_of_tsupport_subset hU (hχ.of_le (by simp)).contDiffOn hχU
  have hφ'U : tsupport φ' ⊆ U := (tsupport_smul_subset_left _ _).trans hχU
  have heq {z : ℂ} (hz : z ∈ tsupport ξ) : φ' =ᶠ[𝓝 z] φ := by
    by_cases hzφ : z ∈ tsupport φ
    · filter_upwards [hχ1 z ⟨hzφ, hz⟩] with y hy
      simp [φ', hy]
    · filter_upwards [notMem_tsupport_iff_eventuallyEq.1 hzφ] with y hy
      simp [φ', hy]
  -- With `S' = S - ∂_t J`, `D* φ' = -(∂_s φ' + Jᵀ ∂_t φ' - S'ᵀ φ')` and `S' + ∂_t J = S`, so this
  -- is `setIntegral_im_pos_inner_cauchyRiemann_adjoint` for `φ'` and `S'`.
  have hS' : ContinuousOn (fun z ↦ S z - fderiv ℝ J z I) U :=
    hS.sub ((hJ.continuousOn_fderiv_of_isOpen hU le_rfl).clm_apply continuousOn_const)
  have hl (z : ℂ) : ⟪crFormalAdjoint J (fderiv ℝ J) S φ z, ξ z⟫_ℝ =
      -⟪fderiv ℝ φ' z 1 + ContinuousLinearMap.adjoint (J z) (fderiv ℝ φ' z I) -
        ContinuousLinearMap.adjoint (S z - fderiv ℝ J z I) (φ' z), ξ z⟫_ℝ := by
    by_cases hz : z ∈ tsupport ξ
    · simp only [crFormalAdjoint_def, (heq hz).fderiv_eq, (heq hz).eq_of_nhds, map_sub,
        sub_apply, inner_add_left, inner_sub_left, inner_neg_left]
      ring
    · simp [image_eq_zero_of_notMem_tsupport hz]
  have hr (z : ℂ) : ⟪φ z, fderiv ℝ ξ z 1 + J z (fderiv ℝ ξ z I) + S z (ξ z)⟫_ℝ =
      ⟪φ' z, fderiv ℝ ξ z 1 + J z (fderiv ℝ ξ z I) + (S z - fderiv ℝ J z I) (ξ z) +
        fderiv ℝ J z I (ξ z)⟫_ℝ := by
    by_cases hz : z ∈ tsupport ξ
    · simp only [(heq hz).eq_of_nhds, sub_apply, add_assoc, sub_add_cancel]
    · simp [fderiv_of_notMem_tsupport ℝ hz, image_eq_zero_of_notMem_tsupport hz]
  have hb (s : ℝ) : ⟪φ s, J s (ξ s)⟫_ℝ = ⟪φ' s, J s (ξ s)⟫_ℝ := by
    by_cases hs : (s : ℂ) ∈ tsupport ξ
    · rw [(heq hs).eq_of_nhds]
    · simp [image_eq_zero_of_notMem_tsupport hs]
  simp_rw [hl, hr, hb]
  rw [integral_neg, setIntegral_im_pos_inner_cauchyRiemann_adjoint hφ' hχc.smul_right hU hξ hJ
    hS' hφ'U]
  ring

/-- **Green's formula for the formal adjoint on the half-disc.** For `φ`, `ξ`, `J` of class `C¹`
and `S` continuous on the open disc of radius `r`, with `tsupport φ ∩ tsupport ξ` inside that
disc, the formula of `TauCeti.setIntegral_im_pos_inner_crFormalAdjoint` holds on the half-disc
`D⁺_r = {|z| < r, 0 < t}`, with boundary term over `(-r, r)`. -/
theorem setIntegral_halfDisc_inner_crFormalAdjoint {r : ℝ} (hφ : ContDiffOn ℝ 1 φ (ball 0 r))
    (hξ : ContDiffOn ℝ 1 ξ (ball 0 r)) (hJ : ContDiffOn ℝ 1 J (ball 0 r))
    (hS : ContinuousOn S (ball 0 r)) (hφξr : tsupport φ ∩ tsupport ξ ⊆ ball 0 r) :
    ∫ z in ball 0 r ∩ {z : ℂ | 0 < z.im}, ⟪crFormalAdjoint J (fderiv ℝ J) S φ z, ξ z⟫_ℝ =
      (∫ z in ball 0 r ∩ {z : ℂ | 0 < z.im},
        ⟪φ z, fderiv ℝ ξ z 1 + J z (fderiv ℝ ξ z I) + S z (ξ z)⟫_ℝ) +
        ∫ s in Ioo (-r) r, ⟪φ s, J s (ξ s)⟫_ℝ := by
  have hout {z : ℂ} (hz : z ∉ ball 0 r) : z ∉ tsupport φ ∩ tsupport ξ := fun h ↦ hz (hφξr h)
  have hc : IsCompact (tsupport φ ∩ tsupport ξ) :=
    (isCompact_closedBall (0 : ℂ) r).of_isClosed_subset
      ((isClosed_tsupport φ).inter (isClosed_tsupport ξ)) (hφξr.trans ball_subset_closedBall)
  rw [setIntegral_inter_im_pos_eq_setIntegral_im_pos fun z _ hz ↦
      (inner_eq_zero_of_notMem_tsupport_inter (hout hz)).1,
    setIntegral_inter_im_pos_eq_setIntegral_im_pos fun z _ hz ↦
      (inner_eq_zero_of_notMem_tsupport_inter (S := S) (hout hz)).2.1,
    setIntegral_Ioo_eq_integral_of_ofReal_notMem_ball fun s hs ↦
      (inner_eq_zero_of_notMem_tsupport_inter (S := S) (hout hs)).2.2]
  exact setIntegral_im_pos_inner_crFormalAdjoint isOpen_ball hφ hξ hJ hS hc hφξr

/-- **Lemma C.1.9 on the half-plane.** If the boundary integrand `⟪φ(s), J(s) ξ(s)⟫` vanishes at
every real `s` in `U`, then `∫_{0 < t} ⟪D* φ, ξ⟫ = ∫_{0 < t} ⟪φ, ∂_s ξ + J ∂_t ξ + S ξ⟫`. -/
theorem setIntegral_im_pos_inner_crFormalAdjoint_of_inner_eq_zero (hU : IsOpen U)
    (hφ : ContDiffOn ℝ 1 φ U) (hξ : ContDiffOn ℝ 1 ξ U) (hJ : ContDiffOn ℝ 1 J U)
    (hS : ContinuousOn S U) (hc : IsCompact (tsupport φ ∩ tsupport ξ))
    (hφξU : tsupport φ ∩ tsupport ξ ⊆ U) (h : ∀ s : ℝ, (s : ℂ) ∈ U → ⟪φ s, J s (ξ s)⟫_ℝ = 0) :
    ∫ z in {z : ℂ | 0 < z.im}, ⟪crFormalAdjoint J (fderiv ℝ J) S φ z, ξ z⟫_ℝ =
      ∫ z in {z : ℂ | 0 < z.im}, ⟪φ z, fderiv ℝ ξ z 1 + J z (fderiv ℝ ξ z I) + S z (ξ z)⟫_ℝ := by
  have h' (s : ℝ) : ⟪φ s, J s (ξ s)⟫_ℝ = 0 := by
    by_cases hs : (s : ℂ) ∈ U
    · exact h s hs
    · exact (inner_eq_zero_of_notMem_tsupport_inter (S := S) fun h ↦ hs (hφξU h)).2.2
  rw [setIntegral_im_pos_inner_crFormalAdjoint hU hφ hξ hJ hS hc hφξU]
  simp [h']

/-- **Lemma C.1.9 on the half-disc.** If the boundary integrand `⟪φ(s), J(s) ξ(s)⟫` vanishes on
`(-r, r)`, then `∫_{D⁺_r} ⟪D* φ, ξ⟫ = ∫_{D⁺_r} ⟪φ, ∂_s ξ + J ∂_t ξ + S ξ⟫`. -/
theorem setIntegral_halfDisc_inner_crFormalAdjoint_of_inner_eq_zero {r : ℝ}
    (hφ : ContDiffOn ℝ 1 φ (ball 0 r)) (hξ : ContDiffOn ℝ 1 ξ (ball 0 r))
    (hJ : ContDiffOn ℝ 1 J (ball 0 r)) (hS : ContinuousOn S (ball 0 r))
    (hφξr : tsupport φ ∩ tsupport ξ ⊆ ball 0 r) (h : ∀ s ∈ Ioo (-r) r, ⟪φ s, J s (ξ s)⟫_ℝ = 0) :
    ∫ z in ball 0 r ∩ {z : ℂ | 0 < z.im}, ⟪crFormalAdjoint J (fderiv ℝ J) S φ z, ξ z⟫_ℝ =
      ∫ z in ball 0 r ∩ {z : ℂ | 0 < z.im},
        ⟪φ z, fderiv ℝ ξ z 1 + J z (fderiv ℝ ξ z I) + S z (ξ z)⟫_ℝ := by
  rw [setIntegral_halfDisc_inner_crFormalAdjoint hφ hξ hJ hS hφξr,
    setIntegral_eq_zero_of_forall_eq_zero h, add_zero]

end TauCeti

/-! ### The dual boundary condition for a compatible metric -/

section Dual

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {J : ℝ → V →L[ℝ] V}
  {η : ℝ → V}

/-- **Compatible boundary conditions on an open set.** Let `Λ` be a real subspace admitting an
orthogonal projection. If `J(s)` maps `Λ` onto `Λᗮ` for every real `s ∈ U`, the dual boundary
condition of `Submodule.forall_integral_inner_clm_apply_eq_zero_iff_of_isOpen` is `η(s) ∈ Λ`: the
formal adjoint carries the same boundary condition as the operator. -/
theorem Submodule.forall_integral_inner_clm_apply_eq_zero_iff_mem_of_isOpen
    (Λ : Submodule ℝ V) [Λ.HasOrthogonalProjection] {U : Set ℂ} (hU : IsOpen U)
    (hJΛ : ∀ s : ℝ, (s : ℂ) ∈ U → Λ.map (J s : V →ₗ[ℝ] V) = Λᗮ)
    (hJ : ContinuousOn J (ofReal ⁻¹' U)) (hη : ContinuousOn η (ofReal ⁻¹' U)) :
    (∀ ξ : ℂ → V, ContDiff ℝ ∞ ξ → HasCompactSupport ξ → tsupport ξ ⊆ U → (∀ s : ℝ, ξ s ∈ Λ) →
      ∫ s : ℝ, ⟪η s, J s (ξ s)⟫_ℝ = 0) ↔ ∀ s : ℝ, (s : ℂ) ∈ U → η s ∈ Λ := by
  rw [Λ.forall_integral_inner_clm_apply_eq_zero_iff_of_isOpen hU hJ hη]
  refine forall_congr' fun s ↦ forall_congr' fun hs ↦ ?_
  conv_rhs => rw [← Λ.orthogonal_orthogonal, ← hJΛ s hs]
  simp [Submodule.mem_orthogonal']

/-- **Compatible boundary conditions.** Let `Λ` be a real subspace admitting an orthogonal
projection. If `J(s)` maps `Λ` onto `Λᗮ` for every real `s`, the dual boundary condition of
`Submodule.forall_integral_inner_clm_apply_eq_zero_iff` is `η(s) ∈ Λ`: the formal adjoint
carries the same boundary condition as the operator. -/
theorem Submodule.forall_integral_inner_clm_apply_eq_zero_iff_mem (Λ : Submodule ℝ V)
    [Λ.HasOrthogonalProjection] (hJΛ : ∀ s : ℝ, Λ.map (J s : V →ₗ[ℝ] V) = Λᗮ)
    (hJ : Continuous J) (hη : Continuous η) :
    (∀ ξ : ℂ → V, ContDiff ℝ ∞ ξ → HasCompactSupport ξ → (∀ s : ℝ, ξ s ∈ Λ) →
      ∫ s : ℝ, ⟪η s, J s (ξ s)⟫_ℝ = 0) ↔ ∀ s : ℝ, η s ∈ Λ := by
  simpa using Λ.forall_integral_inner_clm_apply_eq_zero_iff_mem_of_isOpen isOpen_univ
    (fun s _ ↦ hJΛ s) hJ.continuousOn hη.continuousOn

namespace TauCeti

/-- **Check: the dual condition depends on `J`, not only on `Λ`.** On `V = ℂ` with `Λ = ℝ`, let
`J' = A i A⁻¹` for the real linear `A(x + iy) = x + i(x + y)`, which moves `ℝ`; explicitly
`J'(x + iy) = (x - y) + i(2x - y)`, and `J'² = -1`. For `J = i` the dual condition is `η(s) ∈ ℝ`
(`Real.inner_ofReal_I_mul_ofReal`), so the constant `η = 1` satisfies it; for `J'` the boundary
term of `η = 1` does not vanish for every `ξ` with real boundary values. -/
theorem comp_self_eq_neg_one_and_not_forall_integral_inner_one_clm_apply_eq_zero :
    let J' : ℂ →L[ℝ] ℂ := reCLM.smulRight (1 + 2 * I) + imCLM.smulRight (-1 - I)
    J'.comp J' = -1 ∧ ¬ ∀ ξ : ℂ → ℂ, ContDiff ℝ ∞ ξ → HasCompactSupport ξ →
      (∀ s : ℝ, ξ s ∈ Submodule.span ℝ {(1 : ℂ)}) → ∫ s : ℝ, ⟪(1 : ℂ), J' (ξ s)⟫_ℝ = 0 := by
  intro J'
  refine ⟨ContinuousLinearMap.ext fun z ↦ Complex.ext ?_ ?_, fun h ↦ ?_⟩
  · simp [J']
    ring
  · simp [J']
    ring
  rw [Submodule.forall_integral_inner_clm_apply_eq_zero_iff (J := fun _ ↦ J') (η := fun _ ↦ 1) _
    continuous_const continuous_const] at h
  have := h 0 1 (Submodule.mem_span_singleton_self 1)
  simp [J', Complex.inner] at this

end TauCeti

end Dual
