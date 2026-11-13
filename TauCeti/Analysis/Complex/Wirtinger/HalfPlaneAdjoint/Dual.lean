/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
public import TauCeti.Analysis.Complex.CauchyRiemann.RoughCoefficients.Weak
public import TauCeti.Analysis.Complex.Wirtinger.HalfPlaneAdjoint.Variable
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import TauCeti.Analysis.Normed.Group.CompactSupport

/-!
# Lemma C.1.9 on the half-plane with variable coefficients and the dual boundary condition

Let `V` be a real inner product space, write `z = s + i t`, and let `J, S : ℂ → (V →L[ℝ] V)` be
coefficient fields, with `J` of class `C¹` and `S` continuous. For the real Cauchy–Riemann
operator `D ξ = ∂_s ξ + J ∂_t ξ + S ξ` and its formal adjoint
`D* φ = -∂_s φ - Jᵀ ∂_t φ - (∂_t J)ᵀ φ + Sᵀ φ` (`TauCeti.crFormalAdjoint J (fderiv ℝ J) S`, the
normalization of the weak equation `TauCeti.IsWeakCRSolution`), integration by parts over the
half-plane `{0 < t}` gives

`∫_{0 < t} ⟪D* φ, ξ⟫ = ∫_{0 < t} ⟪φ, D ξ⟫ + ∫_ℝ ⟪φ(s), J(s) ξ(s)⟫ ds`

for a compactly supported `C¹` map `φ`. The `∂_t J` term of `D*` cancels the derivative of `J`
produced by integrating `J ∂_t ξ` by parts. So `∫ ⟪D* φ, ξ⟫ = ∫ ⟪φ, D ξ⟫` as soon as the boundary
integrand vanishes: this is McDuff–Salamon Lemma C.1.9 on the half-plane.

If `ξ` satisfies the boundary condition `ξ(s) ∈ Λ` for a real subspace `Λ`, the boundary term
vanishes for every such `ξ` exactly when `φ(s) ⊥ J(s) Λ` for every real `s`: this is the dual
boundary condition carried by `D*`. It depends on `J(s)` and not only on `Λ`. When `J(s)` maps
`Λ` onto `Λᗮ`, as for a metric compatible with a totally real boundary condition (the bundle
statement is `TauCeti.exists_contMDiffRiemannianMetric_compatible_totallyReal`), the dual
condition is again `φ(s) ∈ Λ`, so `D*` carries the same boundary condition as `D`.

The case `J = i`, `S = 0` on a complex inner product space, in the opposite normalization
`D* = -∂_s + i ∂_t`, is `TauCeti.setIntegral_im_pos_re_inner_cauchyRiemann` and
`Submodule.forall_integral_re_inner_I_smul_eq_zero_iff`.

## Main results

* `TauCeti.setIntegral_im_pos_inner_crFormalAdjoint`: the formula above on the half-plane, for
  `ξ`, `J` only `C¹` and `S` only continuous on an open set containing the support of `φ`.
* `TauCeti.setIntegral_im_pos_inner_crFormalAdjoint_eq` and
  `TauCeti.setIntegral_halfDisc_inner_crFormalAdjoint_eq`: Lemma C.1.9, `∫ ⟪D* φ, ξ⟫ = ∫ ⟪φ, D ξ⟫`
  on the half-plane and on the half-disc `D⁺_r`, when `⟪φ(s), J(s) ξ(s)⟫ = 0` on the real axis.
* `Submodule.forall_integral_inner_clm_apply_eq_zero_iff`: the boundary term vanishes for every
  smooth compactly supported `ξ` with values in `Λ` on `ℝ` exactly when `⟪η(s), J(s) v⟫ = 0` for
  all `v ∈ Λ` and real `s`.
* `Submodule.forall_integral_inner_clm_apply_eq_zero_iff_mem`: if `J(s)` maps `Λ` onto `Λᗮ`, the
  dual condition is `η(s) ∈ Λ`.
* Checks: `TauCeti.not_forall_integral_inner_one_clm_apply_eq_zero` (for the complex structure
  `A i A⁻¹` on `ℂ` and `Λ = ℝ`, the constant `η = 1`, which satisfies the dual condition of `i`,
  violates the dual condition), and `TauCeti.integral_inner_clm_apply_pos` (the wrong dual
  condition `η(s) ∈ J(s) Λ` leaves a positive boundary term).

## References

* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, second edition,
  Lemma C.1.9.
-/

public section

open Complex MeasureTheory Metric Set
open scoped InnerProductSpace ContDiff

namespace TauCeti

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  {φ ξ : ℂ → V} {J S : ℂ → V →L[ℝ] V} {U : Set ℂ}

/-- **Green's formula for the formal adjoint on the half-plane.** For a compactly supported `C¹`
map `φ`, and `ξ`, `J` of class `C¹` and `S` continuous on an open set containing the support of
`φ`,

`∫_{0 < t} ⟪D* φ, ξ⟫ = ∫_{0 < t} ⟪φ, ∂_s ξ + J ∂_t ξ + S ξ⟫ + ∫_ℝ ⟪φ(s), J(s) ξ(s)⟫ ds`,

where `D*` is `TauCeti.crFormalAdjoint J (fderiv ℝ J) S`. -/
theorem setIntegral_im_pos_inner_crFormalAdjoint (hφ : ContDiff ℝ 1 φ)
    (hφc : HasCompactSupport φ) (hU : IsOpen U) (hξ : ContDiffOn ℝ 1 ξ U)
    (hJ : ContDiffOn ℝ 1 J U) (hS : ContinuousOn S U) (hφU : tsupport φ ⊆ U) :
    ∫ z in {z : ℂ | 0 < z.im}, ⟪crFormalAdjoint J (fderiv ℝ J) S φ z, ξ z⟫_ℝ =
      (∫ z in {z : ℂ | 0 < z.im}, ⟪φ z, fderiv ℝ ξ z 1 + J z (fderiv ℝ ξ z I) + S z (ξ z)⟫_ℝ) +
        ∫ s : ℝ, ⟪φ s, J s (ξ s)⟫_ℝ := by
  have hint {f : ℂ → ℝ} (hf : ContinuousOn f U) (h0 : ∀ z, z ∉ tsupport φ → f z = 0) :
      Integrable f :=
    ((hf.mono hφU).integrableOn_compact hφc).integrable_of_forall_notMem_eq_zero h0
  have hdφ := hφ.continuous_fderiv one_ne_zero
  have hdξ := hξ.continuousOn_fderiv_of_isOpen hU le_rfl
  have hdJ := hJ.continuousOn_fderiv_of_isOpen hU le_rfl
  have hadj {A : ℂ → V →L[ℝ] V} (hA : ContinuousOn A U) :
      ContinuousOn (fun z => ContinuousLinearMap.adjoint (A z)) U :=
    (ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := V) (F := V)).continuous.comp_continuousOn hA
  -- `⟪D* φ, ξ⟫ = -G - T`, with `G` the left integrand of the Green formula of `Variable.lean`.
  set G : ℂ → ℝ := fun z => ⟪fderiv ℝ φ z 1 + ContinuousLinearMap.adjoint (J z)
    (fderiv ℝ φ z I) - ContinuousLinearMap.adjoint (S z) (φ z), ξ z⟫_ℝ
  set P : ℂ → ℝ := fun z => ⟪φ z, fderiv ℝ ξ z 1 + J z (fderiv ℝ ξ z I) + S z (ξ z)⟫_ℝ
  set T : ℂ → ℝ := fun z => ⟪φ z, fderiv ℝ J z I (ξ z)⟫_ℝ
  have hpt (z : ℂ) : ⟪crFormalAdjoint J (fderiv ℝ J) S φ z, ξ z⟫_ℝ = -G z - T z := by
    simp only [G, T, inner_crFormalAdjoint, inner_add_left, inner_sub_left,
      ContinuousLinearMap.adjoint_inner_left]
    ring
  have hG : Integrable G := hint
    ((((hdφ.clm_apply continuous_const).continuousOn.add ((hadj hJ.continuousOn).clm_apply
      (hdφ.clm_apply continuous_const).continuousOn)).sub
      ((hadj hS).clm_apply hφ.continuous.continuousOn)).inner hξ.continuousOn)
    fun z hz => by simp [G, fderiv_of_notMem_tsupport ℝ hz, image_eq_zero_of_notMem_tsupport hz]
  have hP : Integrable P := hint
    (hφ.continuous.continuousOn.inner (((hdξ.clm_apply continuousOn_const).add
      (hJ.continuousOn.clm_apply (hdξ.clm_apply continuousOn_const))).add
      (hS.clm_apply hξ.continuousOn)))
    fun z hz => by simp [P, image_eq_zero_of_notMem_tsupport hz]
  have hT : Integrable T := hint
    (hφ.continuous.continuousOn.inner
      ((hdJ.clm_apply continuousOn_const).clm_apply hξ.continuousOn))
    fun z hz => by simp [T, image_eq_zero_of_notMem_tsupport hz]
  have hsplit : ∫ z in {z : ℂ | 0 < z.im}, ⟪φ z, fderiv ℝ ξ z 1 + J z (fderiv ℝ ξ z I) +
      S z (ξ z) + fderiv ℝ J z I (ξ z)⟫_ℝ =
      (∫ z in {z : ℂ | 0 < z.im}, P z) + ∫ z in {z : ℂ | 0 < z.im}, T z := by
    simp only [inner_add_right (x := φ _) (y := _ + _ + _)]
    exact integral_add hP.integrableOn hT.integrableOn
  simp_rw [hpt]
  rw [integral_sub (f := fun z => -G z) hG.neg.integrableOn hT.integrableOn, integral_neg,
    setIntegral_im_pos_inner_cauchyRiemann_adjoint hφ hφc hU hξ hJ hS hφU, hsplit]
  ring

/-- **Green's formula for the formal adjoint on the half-disc.** For `φ` supported in the open
disc of radius `r`, and `ξ`, `J` of class `C¹` and `S` continuous there, the formula of
`TauCeti.setIntegral_im_pos_inner_crFormalAdjoint` holds on the half-disc
`D⁺_r = {|z| < r, 0 < t}`, with boundary term over `(-r, r)`. -/
theorem setIntegral_halfDisc_inner_crFormalAdjoint {r : ℝ} (hφ : ContDiff ℝ 1 φ)
    (hξ : ContDiffOn ℝ 1 ξ (ball 0 r)) (hJ : ContDiffOn ℝ 1 J (ball 0 r))
    (hS : ContinuousOn S (ball 0 r)) (hφr : tsupport φ ⊆ ball 0 r) :
    ∫ z in ball 0 r ∩ {z : ℂ | 0 < z.im}, ⟪crFormalAdjoint J (fderiv ℝ J) S φ z, ξ z⟫_ℝ =
      (∫ z in ball 0 r ∩ {z : ℂ | 0 < z.im},
        ⟪φ z, fderiv ℝ ξ z 1 + J z (fderiv ℝ ξ z I) + S z (ξ z)⟫_ℝ) +
        ∫ s in Ioo (-r) r, ⟪φ s, J s (ξ s)⟫_ℝ := by
  have hout {z : ℂ} (hz : z ∉ ball 0 r) : z ∉ tsupport φ := fun h ↦ hz (hφr h)
  have hφc : HasCompactSupport φ := (isCompact_closedBall (0 : ℂ) r).of_isClosed_subset
    (isClosed_tsupport φ) (hφr.trans ball_subset_closedBall)
  rw [setIntegral_inter_im_pos_eq_setIntegral_im_pos fun z _ hz ↦ by
      simp [crFormalAdjoint_of_notMem_tsupport (hout hz)],
    setIntegral_inter_im_pos_eq_setIntegral_im_pos fun z _ hz ↦ by
      simp [image_eq_zero_of_notMem_tsupport (hout hz)],
    setIntegral_Ioo_eq_integral_of_ofReal_notMem_ball fun s hs ↦ by
      simp [image_eq_zero_of_notMem_tsupport (hout hs)]]
  exact setIntegral_im_pos_inner_crFormalAdjoint hφ hφc isOpen_ball hξ hJ hS hφr

/-- **Lemma C.1.9 on the half-plane.** If the boundary integrand `⟪φ(s), J(s) ξ(s)⟫` vanishes at
every real `s` in `U`, then `∫_{0 < t} ⟪D* φ, ξ⟫ = ∫_{0 < t} ⟪φ, ∂_s ξ + J ∂_t ξ + S ξ⟫`. -/
theorem setIntegral_im_pos_inner_crFormalAdjoint_eq (hφ : ContDiff ℝ 1 φ)
    (hφc : HasCompactSupport φ) (hU : IsOpen U) (hξ : ContDiffOn ℝ 1 ξ U)
    (hJ : ContDiffOn ℝ 1 J U) (hS : ContinuousOn S U) (hφU : tsupport φ ⊆ U)
    (h : ∀ s : ℝ, (s : ℂ) ∈ U → ⟪φ s, J s (ξ s)⟫_ℝ = 0) :
    ∫ z in {z : ℂ | 0 < z.im}, ⟪crFormalAdjoint J (fderiv ℝ J) S φ z, ξ z⟫_ℝ =
      ∫ z in {z : ℂ | 0 < z.im}, ⟪φ z, fderiv ℝ ξ z 1 + J z (fderiv ℝ ξ z I) + S z (ξ z)⟫_ℝ := by
  have h' (s : ℝ) : ⟪φ s, J s (ξ s)⟫_ℝ = 0 := by
    by_cases hs : (s : ℂ) ∈ U
    · exact h s hs
    · simp [image_eq_zero_of_notMem_tsupport fun h ↦ hs (hφU h)]
  rw [setIntegral_im_pos_inner_crFormalAdjoint hφ hφc hU hξ hJ hS hφU]
  simp [h']

/-- **Lemma C.1.9 on the half-disc.** If the boundary integrand `⟪φ(s), J(s) ξ(s)⟫` vanishes on
`(-r, r)`, then `∫_{D⁺_r} ⟪D* φ, ξ⟫ = ∫_{D⁺_r} ⟪φ, ∂_s ξ + J ∂_t ξ + S ξ⟫`. -/
theorem setIntegral_halfDisc_inner_crFormalAdjoint_eq {r : ℝ} (hφ : ContDiff ℝ 1 φ)
    (hξ : ContDiffOn ℝ 1 ξ (ball 0 r)) (hJ : ContDiffOn ℝ 1 J (ball 0 r))
    (hS : ContinuousOn S (ball 0 r)) (hφr : tsupport φ ⊆ ball 0 r)
    (h : ∀ s ∈ Ioo (-r) r, ⟪φ s, J s (ξ s)⟫_ℝ = 0) :
    ∫ z in ball 0 r ∩ {z : ℂ | 0 < z.im}, ⟪crFormalAdjoint J (fderiv ℝ J) S φ z, ξ z⟫_ℝ =
      ∫ z in ball 0 r ∩ {z : ℂ | 0 < z.im},
        ⟪φ z, fderiv ℝ ξ z 1 + J z (fderiv ℝ ξ z I) + S z (ξ z)⟫_ℝ := by
  rw [setIntegral_halfDisc_inner_crFormalAdjoint hφ hξ hJ hS hφr,
    setIntegral_eq_zero_of_forall_eq_zero h, add_zero]

end TauCeti

/-! ### The dual boundary condition -/

section Dual

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {J : ℂ → V →L[ℝ] V}
  {η : ℂ → V}

/-- **The dual boundary condition.** The boundary term `∫_ℝ ⟪η(s), J(s) ξ(s)⟫ ds` vanishes for
every smooth compactly supported `ξ` taking values in a real subspace `Λ` on `ℝ` exactly when
`⟪η(s), J(s) v⟫ = 0` for all `v ∈ Λ` and real `s`, that is, when `η(s) ⊥ J(s) Λ`. -/
theorem Submodule.forall_integral_inner_clm_apply_eq_zero_iff (Λ : Submodule ℝ V)
    (hJ : Continuous fun s : ℝ ↦ J s) (hη : Continuous fun s : ℝ ↦ η s) :
    (∀ ξ : ℂ → V, ContDiff ℝ ∞ ξ → HasCompactSupport ξ → (∀ s : ℝ, ξ s ∈ Λ) →
      ∫ s : ℝ, ⟪η s, J s (ξ s)⟫_ℝ = 0) ↔
      ∀ s : ℝ, ∀ v ∈ Λ, ⟪η s, J s v⟫_ℝ = 0 := by
  refine ⟨fun h s₀ v hv ↦ ?_, fun h ξ _ _ hξΛ ↦ by simp [h _ _ (hξΛ _)]⟩
  set f : ℝ → ℝ := fun s ↦ ⟪η s, J s v⟫_ℝ
  have hf : Continuous f := hη.inner (hJ.clm_apply continuous_const)
  suffices hf0 : f = 0 from congr_fun hf0 s₀
  refine (hf.ae_eq_iff_eq volume continuous_const).1
    (ae_eq_zero_of_integral_contDiff_smul_eq_zero hf.locallyIntegrable fun φ hφ hφc ↦ ?_)
  obtain ⟨R, hR, hφR⟩ := hφc.exists_pos_le_norm_notMem_tsupport
  let ψ : ContDiffBump (0 : ℂ) := ⟨R, R + 1, hR, by linarith⟩
  set ξ : ℂ → V := fun z ↦ (φ z.re * ψ z) • v
  have hξs (s : ℝ) : ξ s = φ s • v := by
    by_cases hs : R ≤ ‖(s : ℂ)‖
    · rw [Complex.norm_real] at hs
      simp [ξ, image_eq_zero_of_notMem_tsupport (hφR s hs)]
    · rw [not_le] at hs
      simp [ξ, ψ.one_of_mem_closedBall (mem_closedBall_zero_iff.2 hs.le)]
  have hξ : ContDiff ℝ ∞ ξ :=
    ((hφ.comp Complex.reCLM.contDiff).mul ψ.contDiff).smul contDiff_const
  have hξc : HasCompactSupport ξ :=
    (ψ.hasCompactSupport.mul_left (f := fun z : ℂ ↦ φ z.re)).smul_right
  have := h ξ hξ hξc fun s ↦ hξs s ▸ Λ.smul_mem _ hv
  simpa [hξs, f, inner_smul_right] using this

/-- If `A` maps `Λ` onto its orthogonal complement, then `A Λ` has orthogonal complement `Λ`. -/
theorem Submodule.orthogonal_map_eq_of_map_eq_orthogonal (Λ : Submodule ℝ V)
    [Λ.HasOrthogonalProjection] {A : V →L[ℝ] V} (h : Λ.map (A : V →ₗ[ℝ] V) = Λᗮ) :
    (Λ.map (A : V →ₗ[ℝ] V))ᗮ = Λ := by
  rw [h, Submodule.orthogonal_orthogonal]

/-- **Compatible boundary conditions.** If `J(s)` maps `Λ` onto `Λᗮ` for every real `s`, the
dual boundary condition of `Submodule.forall_integral_inner_clm_apply_eq_zero_iff` is
`η(s) ∈ Λ`: the formal adjoint carries the same boundary condition as the operator. -/
theorem Submodule.forall_integral_inner_clm_apply_eq_zero_iff_mem (Λ : Submodule ℝ V)
    [Λ.HasOrthogonalProjection] (hJΛ : ∀ s : ℝ, Λ.map (J s : V →ₗ[ℝ] V) = Λᗮ)
    (hJ : Continuous fun s : ℝ ↦ J s) (hη : Continuous fun s : ℝ ↦ η s) :
    (∀ ξ : ℂ → V, ContDiff ℝ ∞ ξ → HasCompactSupport ξ → (∀ s : ℝ, ξ s ∈ Λ) →
      ∫ s : ℝ, ⟪η s, J s (ξ s)⟫_ℝ = 0) ↔ ∀ s : ℝ, η s ∈ Λ := by
  rw [Λ.forall_integral_inner_clm_apply_eq_zero_iff hJ hη]
  refine forall_congr' fun s ↦ ?_
  conv_rhs => rw [← Λ.orthogonal_map_eq_of_map_eq_orthogonal (hJΛ s)]
  simp [Submodule.mem_orthogonal']

namespace TauCeti

/-- **Check: the wrong dual boundary condition.** If `η(s) = J(s) ξ(s)` on `ℝ`, which for `ξ`
with values in `Λ` is the condition `η(s) ∈ J(s) Λ`, the boundary integral
`∫_ℝ ⟪η(s), J(s) ξ(s)⟫ = ∫_ℝ ‖J(s) ξ(s)‖²` is positive as soon as `J(s) ξ(s)` is nonzero somewhere
on `ℝ`, so the boundary term does not vanish. -/
theorem integral_inner_clm_apply_pos {ξ : ℂ → V} (hJ : Continuous fun s : ℝ ↦ J s)
    (hξ : Continuous ξ) (hξc : HasCompactSupport ξ) {s₀ : ℝ} (hs₀ : J s₀ (ξ s₀) ≠ 0)
    (hη : ∀ s : ℝ, η s = J s (ξ s)) :
    0 < ∫ s : ℝ, ⟪η s, J s (ξ s)⟫_ℝ := by
  simp_rw [hη, real_inner_self_eq_norm_sq]
  have hc : Continuous fun s : ℝ ↦ J s (ξ s) := hJ.clm_apply (hξ.comp continuous_ofReal)
  have hcs : HasCompactSupport fun s : ℝ ↦ ξ s :=
    hξc.comp_isClosedEmbedding Complex.isometry_ofReal.isClosedEmbedding
  exact (hc.norm.pow 2).integral_pos_of_hasCompactSupport_nonneg_ne_zero
    (hcs.mono fun s hs h0 ↦ hs (by simp [h0])) (fun s ↦ sq_nonneg _)
    (pow_ne_zero 2 (norm_ne_zero_iff.2 hs₀))

/-- **Check: the dual condition depends on `J`, not only on `Λ`.** On `V = ℂ` with `Λ = ℝ`, let
`J' = A i A⁻¹` for the real linear `A(x + iy) = x + i(x + y)`, which moves `ℝ`; explicitly
`J'(x + iy) = (x - y) + i(2x - y)`, and `J'² = -1`. For `J = i` the dual condition is `η(s) ∈ ℝ`
(`Real.inner_ofReal_I_mul_ofReal`), so the constant `η = 1` satisfies it; for `J'` the boundary
term of `η = 1` does not vanish for every `ξ` with real boundary values. -/
theorem not_forall_integral_inner_one_clm_apply_eq_zero :
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
