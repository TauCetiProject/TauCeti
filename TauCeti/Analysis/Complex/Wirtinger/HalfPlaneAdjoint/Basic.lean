/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import TauCeti.Analysis.Complex.Wirtinger.Basic
public import TauCeti.Analysis.Green.HalfPlane
public import TauCeti.LinearAlgebra.TotallyReal.Euclidean
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff
import TauCeti.Analysis.InnerProductSpace.ReInner
import TauCeti.Analysis.Normed.Group.CompactSupport

/-!
# The formal adjoint of `∂_s + i ∂_t` on the half-plane

Let `ξ η : ℂ → E` be `C¹` maps into a complex inner product space, with `ξ` compactly supported,
and write `z = s + i t`. Integrating by parts over the half-plane `{0 < t}` gives

`∫ Re ⟪η, ∂_s ξ + i ∂_t ξ⟫ = ∫ Re ⟪-∂_s η + i ∂_t η, ξ⟫ - ∫_ℝ Re ⟪i ξ(s), η(s)⟫ ds`.

So the formal adjoint of the real Cauchy–Riemann operator `D = ∂_s + i ∂_t` is the `∂`-type
operator `D* = -∂_s + i ∂_t`, and integration by parts in `t` leaves the boundary term
`-∫_ℝ Re ⟪i ξ, η⟫`. In Wirtinger form, `D = 2 \bar∂` and `D* = -2 ∂`. This is the planar model of
McDuff–Salamon, Lemma C.1.9.

The boundary term vanishes for every `ξ` taking values on `ℝ` in a real subspace `L` exactly when
`η` takes values on `ℝ` in the orthogonal complement of `i L` for `Re ⟪·, ·⟫`. For `L = ℝⁿ ⊆ ℂⁿ`
this complement is `ℝⁿ` itself, so the dual boundary condition is again `η ∈ ℝⁿ`. The plausible
wrong dual condition `η ∈ i ℝⁿ` does not make the term vanish: for `η = i ξ` on `ℝ` it is
`-∫_ℝ ‖ξ‖² < 0` as soon as `ξ` is nonzero somewhere on `ℝ`.

These boundary statements are proved for a general boundary term `∫_ℝ ⟪η(s), J(s) ξ(s)⟫ ds` on a
real inner product space, with a variable coefficient `J(s)` in place of `i`: it vanishes for
every `ξ` with values in `Λ` on `ℝ` exactly when `η(s) ⊥ J(s) Λ`.

## Main results

* `TauCeti.setIntegral_im_pos_re_inner_cauchyRiemann`: the integration by parts formula above,
  for `η` only `C¹` on an open set containing the support of `ξ`.
* `TauCeti.setIntegral_im_pos_re_inner_conjWirtingerDeriv`: the same formula in Wirtinger form.
* `TauCeti.setIntegral_halfDisc_re_inner_cauchyRiemann`: the formula on the half-disc
  `D⁺_r = {|z| < r, 0 < t}` for `ξ` supported in the open disc of radius `r`.
* `Submodule.forall_integral_inner_clm_apply_eq_zero_iff_of_isOpen` and
  `Submodule.forall_integral_inner_clm_apply_eq_zero_iff`: the general boundary term vanishes for
  all smooth `ξ` supported in an open `U ⊆ ℂ` (or in `ℂ`) with values in `Λ` on `ℝ` exactly when
  `⟪η(s), J(s) v⟫ = 0` for all `v ∈ Λ` and real `s ∈ U`.
* `TauCeti.integral_inner_clm_apply_pos`: for `η = J ξ` on `ℝ` the general boundary integral is
  positive.
* `Submodule.forall_integral_re_inner_I_smul_eq_zero_iff`: the boundary term vanishes for all
  smooth `ξ` with values in `L` on `ℝ` exactly when `Re ⟪i v, η(s)⟫ = 0` for all `v ∈ L`.
* `TauCeti.forall_integral_re_inner_I_smul_eq_zero_iff_mem_realSubspace`: for `L = ℝⁿ ⊆ ℂⁿ`, this
  dual condition is `η(s) ∈ ℝⁿ`.
* `TauCeti.integral_re_inner_I_smul_pos`: for `η = i ξ` on `ℝ` the boundary integral is positive.

## References

* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, second edition,
  Lemma C.1.9.
-/

public section

open Complex MeasureTheory Metric Set
open scoped InnerProductSpace ContDiff

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

variable {ξ η : ℂ → E} {U : Set ℂ}

/-- **Integration by parts for `∂_s + i ∂_t` on the half-plane.** For a compactly supported `C¹`
map `ξ` and a map `η` that is `C¹` on an open set containing the support of `ξ`,

`∫_{0 < t} Re ⟪η, ∂_s ξ + i ∂_t ξ⟫ = ∫_{0 < t} Re ⟪-∂_s η + i ∂_t η, ξ⟫ - ∫_ℝ Re ⟪i ξ, η⟫`.

So the formal adjoint of `D = ∂_s + i ∂_t` is `D* = -∂_s + i ∂_t`, and integration by parts in
`t` leaves the boundary term `-∫_ℝ Re ⟪i ξ, η⟫`. -/
theorem setIntegral_im_pos_re_inner_cauchyRiemann (hξ : ContDiff ℝ 1 ξ)
    (hξc : HasCompactSupport ξ) (hU : IsOpen U) (hη : ContDiffOn ℝ 1 η U)
    (hξU : tsupport ξ ⊆ U) :
    ∫ z in {z : ℂ | 0 < z.im}, re ⟪η z, fderiv ℝ ξ z 1 + I • fderiv ℝ ξ z I⟫_ℂ =
      (∫ z in {z : ℂ | 0 < z.im}, re ⟪-fderiv ℝ η z 1 + I • fderiv ℝ η z I, ξ z⟫_ℂ) -
        ∫ s : ℝ, re ⟪I • ξ s, η s⟫_ℂ := by
  have hξd := hξ.differentiable one_ne_zero
  have hIξ : ContDiff ℝ 1 fun z ↦ I • ξ z := hξ.const_smul I
  have hIξU : tsupport (fun z ↦ I • ξ z) ⊆ U := (tsupport_smul_subset_right _ _).trans hξU
  set h : ℂ → ℝ := fun z ↦ reInnerCLM (η z) (ξ z)
  set g : ℂ → ℝ := fun z ↦ reInnerCLM (η z) (I • ξ z)
  have hh : ContDiff ℝ 1 h := reInnerCLM.contDiff_of_tsupport_subset_right hη hξ.contDiffOn hU hξU
  have hg : ContDiff ℝ 1 g :=
    reInnerCLM.contDiff_of_tsupport_subset_right hη hIξ.contDiffOn hU hIξU
  have hhc : HasCompactSupport h := hξc.mono fun z hz h0 ↦ hz (by simp [h, h0])
  have hgc : HasCompactSupport g := hξc.mono fun z hz h0 ↦ hz (by simp [g, h0])
  have hh' (z v : ℂ) : fderiv ℝ h z v =
      re ⟪η z, fderiv ℝ ξ z v⟫_ℂ + re ⟪fderiv ℝ η z v, ξ z⟫_ℂ := by
    rw [reInnerCLM.fderiv_of_tsupport_subset_right (hη.differentiableOn one_ne_zero) hξd hU hξU]
    simp
  have hg' (z v : ℂ) : fderiv ℝ g z v =
      re ⟪η z, I • fderiv ℝ ξ z v⟫_ℂ + re ⟪fderiv ℝ η z v, I • ξ z⟫_ℂ := by
    rw [reInnerCLM.fderiv_of_tsupport_subset_right (hη.differentiableOn one_ne_zero)
      (hIξ.differentiable one_ne_zero) hU hIξU]
    simp [fderiv_fun_const_smul (hξd z)]
  have hpt (z : ℂ) : re ⟪η z, fderiv ℝ ξ z 1 + I • fderiv ℝ ξ z I⟫_ℂ =
      fderiv ℝ h z 1 + fderiv ℝ g z I +
        re ⟪-fderiv ℝ η z 1 + I • fderiv ℝ η z I, ξ z⟫_ℂ := by
    rw [hh', hg']
    simp only [inner_add_left, inner_add_right, inner_neg_left, inner_smul_left, inner_smul_right,
      Complex.add_re, Complex.neg_re, Complex.mul_re, Complex.conj_re, Complex.conj_im,
      Complex.I_re, Complex.I_im]
    ring
  have hA : Integrable fun z ↦ fderiv ℝ h z 1 :=
    ((hh.continuous_fderiv one_ne_zero).clm_apply continuous_const).integrable_of_hasCompactSupport
      (hhc.fderiv_apply (𝕜 := ℝ) 1)
  have hB : Integrable fun z ↦ fderiv ℝ g z I :=
    ((hg.continuous_fderiv one_ne_zero).clm_apply continuous_const).integrable_of_hasCompactSupport
      (hgc.fderiv_apply (𝕜 := ℝ) I)
  have hL : Integrable fun z ↦ re ⟪η z, fderiv ℝ ξ z 1 + I • fderiv ℝ ξ z I⟫_ℂ := by
    have hcont : ContinuousOn (fun z ↦ re ⟪η z, fderiv ℝ ξ z 1 + I • fderiv ℝ ξ z I⟫_ℂ) U :=
      Complex.continuous_re.comp_continuousOn (hη.continuousOn.inner (Continuous.continuousOn
        (((hξ.continuous_fderiv one_ne_zero).clm_apply continuous_const).add
          (((hξ.continuous_fderiv one_ne_zero).clm_apply continuous_const).const_smul I))))
    refine IntegrableOn.integrable_of_forall_notMem_eq_zero
      ((hcont.mono hξU).integrableOn_compact hξc) fun z hz ↦ ?_
    simp [fderiv_of_notMem_tsupport ℝ hz]
  have hC : Integrable fun z ↦ re ⟪-fderiv ℝ η z 1 + I • fderiv ℝ η z I, ξ z⟫_ℂ :=
    ((hL.sub hA).sub hB).congr (ae_of_all _ fun z ↦ by simp only [Pi.sub_apply, hpt z]; ring)
  simp_rw [hpt]
  rw [integral_add (f := fun z ↦ fderiv ℝ h z 1 + fderiv ℝ g z I) (hA.add hB).integrableOn
      hC.integrableOn,
    integral_add hA.integrableOn hB.integrableOn, setIntegral_im_pos_fderiv_one_eq_zero hh hhc,
    setIntegral_im_pos_fderiv_I_eq_neg_integral hg hgc, zero_add]
  have hsym (s : ℝ) : g s = re ⟪I • ξ s, η s⟫_ℂ := by
    simpa only [g, reInnerCLM_apply, RCLike.re_to_complex] using
      inner_re_symm (𝕜 := ℂ) (η s) (I • ξ s)
  simp only [hsym]
  ring

/-- **Integration by parts for `\bar∂` on the half-plane.** In Wirtinger form the formal
adjoint of `\bar∂` is `-∂`:
`∫_{0 < t} Re ⟪η, \bar∂ ξ⟫ = -∫_{0 < t} Re ⟪∂ η, ξ⟫ - ½ ∫_ℝ Re ⟪i ξ, η⟫`. -/
theorem setIntegral_im_pos_re_inner_conjWirtingerDeriv (hξ : ContDiff ℝ 1 ξ)
    (hξc : HasCompactSupport ξ) (hU : IsOpen U) (hη : ContDiffOn ℝ 1 η U)
    (hξU : tsupport ξ ⊆ U) :
    ∫ z in {z : ℂ | 0 < z.im}, re ⟪η z, conjWirtingerDeriv ξ z 1⟫_ℂ =
      -(∫ z in {z : ℂ | 0 < z.im}, re ⟪wirtingerDeriv η z 1, ξ z⟫_ℂ) -
        2⁻¹ * ∫ s : ℝ, re ⟪I • ξ s, η s⟫_ℂ := by
  have hl (z : ℂ) : re ⟪η z, conjWirtingerDeriv ξ z 1⟫_ℂ =
      2⁻¹ * re ⟪η z, fderiv ℝ ξ z 1 + I • fderiv ℝ ξ z I⟫_ℂ := by
    rw [conjWirtingerDeriv_apply, smul_eq_mul, mul_one, inner_smul_right]
    simp [Complex.mul_re]
  have hr (z : ℂ) : re ⟪wirtingerDeriv η z 1, ξ z⟫_ℂ =
      -(2⁻¹ * re ⟪-fderiv ℝ η z 1 + I • fderiv ℝ η z I, ξ z⟫_ℂ) := by
    simp [wirtingerDeriv_apply, inner_smul_left, inner_sub_left, inner_add_left]
    ring
  simp_rw [hl, hr, integral_neg, neg_neg, integral_const_mul,
    setIntegral_im_pos_re_inner_cauchyRiemann hξ hξc hU hη hξU]
  ring

/-- **Integration by parts on the half-disc.** For `ξ` supported in the open disc of radius
`r` and `η` only `C¹` there, the formula of `setIntegral_im_pos_re_inner_cauchyRiemann` holds on
the half-disc `D⁺_r = {|z| < r, 0 < t}`, with boundary term over `(-r, r)`. -/
theorem setIntegral_halfDisc_re_inner_cauchyRiemann {r : ℝ} (hξ : ContDiff ℝ 1 ξ)
    (hη : ContDiffOn ℝ 1 η (ball 0 r))
    (hξr : tsupport ξ ⊆ ball 0 r) :
    ∫ z in ball 0 r ∩ {z : ℂ | 0 < z.im}, re ⟪η z, fderiv ℝ ξ z 1 + I • fderiv ℝ ξ z I⟫_ℂ =
      (∫ z in ball 0 r ∩ {z : ℂ | 0 < z.im},
        re ⟪-fderiv ℝ η z 1 + I • fderiv ℝ η z I, ξ z⟫_ℂ) -
        ∫ s in Ioo (-r) r, re ⟪I • ξ s, η s⟫_ℂ := by
  have hout {z : ℂ} (hz : z ∉ ball 0 r) : z ∉ tsupport ξ := fun h ↦ hz (hξr h)
  have hξc : HasCompactSupport ξ := (isCompact_closedBall (0 : ℂ) r).of_isClosed_subset
    (isClosed_tsupport ξ) (hξr.trans ball_subset_closedBall)
  rw [setIntegral_inter_im_pos_eq_setIntegral_im_pos fun z _ hz ↦ by
      simp [fderiv_of_notMem_tsupport ℝ (hout hz)],
    setIntegral_inter_im_pos_eq_setIntegral_im_pos fun z _ hz ↦ by
      simp [image_eq_zero_of_notMem_tsupport (hout hz)],
    setIntegral_Ioo_eq_integral_of_ofReal_notMem_ball fun s hs ↦ by
      simp [image_eq_zero_of_notMem_tsupport (hout hs)]]
  exact setIntegral_im_pos_re_inner_cauchyRiemann hξ hξc isOpen_ball hη hξr

/-- **The dual boundary condition on an open set.** For a real inner product space `V`, maps
`J : ℝ → (V →L[ℝ] V)` and `η : ℝ → V` continuous on `U ∩ ℝ` for an open `U ⊆ ℂ`, and a real
subspace `Λ`, the boundary term `∫_ℝ ⟪η(s), J(s) ξ(s)⟫ ds` vanishes for every smooth compactly
supported `ξ` with support in `U` and values in `Λ` on `ℝ` exactly when `⟪η(s), J(s) v⟫ = 0` for
all `v ∈ Λ` and real `s ∈ U`, that is, when `η(s) ⊥ J(s) Λ` on `U ∩ ℝ`. -/
theorem _root_.Submodule.forall_integral_inner_clm_apply_eq_zero_iff_of_isOpen {V : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] (Λ : Submodule ℝ V) {J : ℝ → V →L[ℝ] V}
    {η : ℝ → V} (hU : IsOpen U) (hJ : ContinuousOn J (ofReal ⁻¹' U))
    (hη : ContinuousOn η (ofReal ⁻¹' U)) :
    (∀ ξ : ℂ → V, ContDiff ℝ ∞ ξ → HasCompactSupport ξ → tsupport ξ ⊆ U → (∀ s : ℝ, ξ s ∈ Λ) →
      ∫ s : ℝ, ⟪η s, J s (ξ s)⟫_ℝ = 0) ↔
      ∀ s : ℝ, (s : ℂ) ∈ U → ∀ v ∈ Λ, ⟪η s, J s v⟫_ℝ = 0 := by
  refine ⟨fun h s₀ hs₀ v hv ↦ ?_, fun h ξ _ _ hξU hξΛ ↦ ?_⟩
  · have hW : IsOpen (ofReal ⁻¹' U) := hU.preimage continuous_ofReal
    set f : ℝ → ℝ := fun s ↦ ⟪η s, J s v⟫_ℝ
    have hf : ContinuousOn f (ofReal ⁻¹' U) := hη.inner (hJ.clm_apply continuousOn_const)
    refine Measure.eqOn_open_of_ae_eq (μ := volume) (g := 0) ((ae_restrict_iff' hW.measurableSet).2
      (hW.ae_eq_zero_of_integral_contDiff_smul_eq_zero (hf.locallyIntegrableOn hW.measurableSet)
        fun φ hφ hφc hφU ↦ ?_)) hW hf continuousOn_const hs₀
    -- Extend `φ • v` from `ℝ` to `ℂ` by a cutoff equal to one near `tsupport φ`.
    obtain ⟨χ, hχ, -, hχ1, hχc, hχU⟩ :=
      (hφc.isCompact.image continuous_ofReal).exists_contDiff_cutoff_eventuallyEq_one hU
        (image_subset_iff.2 hφU)
    set ξ : ℂ → V := fun z ↦ (φ z.re * χ z) • v
    have hξs (s : ℝ) : ξ s = φ s • v := by
      by_cases hs : s ∈ tsupport φ
      · simp [ξ, (hχ1 _ (mem_image_of_mem _ hs)).self_of_nhds]
      · simp [ξ, image_eq_zero_of_notMem_tsupport hs]
    have hξ : ContDiff ℝ ∞ ξ :=
      ((hφ.comp Complex.reCLM.contDiff).mul hχ).smul contDiff_const
    have hξc : HasCompactSupport ξ := (hχc.mul_left (f := fun z : ℂ ↦ φ z.re)).smul_right
    have hξU : tsupport ξ ⊆ U :=
      ((tsupport_smul_subset_left _ _).trans tsupport_mul_subset_right).trans hχU
    have := h ξ hξ hξc hξU fun s ↦ hξs s ▸ Λ.smul_mem _ hv
    simpa [hξs, f, inner_smul_right] using this
  · have h' (s : ℝ) : ⟪η s, J s (ξ s)⟫_ℝ = 0 := by
      by_cases hs : (s : ℂ) ∈ U
      · exact h s hs _ (hξΛ s)
      · simp [image_eq_zero_of_notMem_tsupport fun h ↦ hs (hξU h)]
    simp [h']

/-- **The dual boundary condition.** The boundary term `∫_ℝ ⟪η(s), J(s) ξ(s)⟫ ds` vanishes for
every smooth compactly supported `ξ` taking values in a real subspace `Λ` on `ℝ` exactly when
`⟪η(s), J(s) v⟫ = 0` for all `v ∈ Λ` and real `s`, that is, when `η(s) ⊥ J(s) Λ`. -/
theorem _root_.Submodule.forall_integral_inner_clm_apply_eq_zero_iff {V : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] (Λ : Submodule ℝ V) {J : ℝ → V →L[ℝ] V}
    {η : ℝ → V} (hJ : Continuous J) (hη : Continuous η) :
    (∀ ξ : ℂ → V, ContDiff ℝ ∞ ξ → HasCompactSupport ξ → (∀ s : ℝ, ξ s ∈ Λ) →
      ∫ s : ℝ, ⟪η s, J s (ξ s)⟫_ℝ = 0) ↔
      ∀ s : ℝ, ∀ v ∈ Λ, ⟪η s, J s v⟫_ℝ = 0 := by
  simpa using Λ.forall_integral_inner_clm_apply_eq_zero_iff_of_isOpen isOpen_univ
    hJ.continuousOn hη.continuousOn

/-- **The dual boundary condition for `J = i`.** The boundary term `∫_ℝ Re ⟪i ξ, η⟫` vanishes
for every smooth compactly supported `ξ` taking values in a real subspace `L` on `ℝ` exactly when
`Re ⟪i v, η(s)⟫ = 0` for all `v ∈ L` and real `s`, that is, when `η` takes values on `ℝ` in the
orthogonal complement of `i L` for `Re ⟪·, ·⟫`. -/
theorem _root_.Submodule.forall_integral_re_inner_I_smul_eq_zero_iff (L : Submodule ℝ E)
    (hη : Continuous fun s : ℝ ↦ η s) :
    (∀ ξ : ℂ → E, ContDiff ℝ ∞ ξ → HasCompactSupport ξ → (∀ s : ℝ, ξ s ∈ L) →
      ∫ s : ℝ, re ⟪I • ξ s, η s⟫_ℂ = 0) ↔
      ∀ s : ℝ, ∀ v ∈ L, re ⟪I • v, η s⟫_ℂ = 0 := by
  let := InnerProductSpace.complexToReal (G := E)
  have h (x y : E) : re ⟪I • x, y⟫_ℂ = ⟪y, ContinuousLinearMap.lsmul ℝ ℂ I x⟫_ℝ := by
    rw [ContinuousLinearMap.lsmul_apply, real_inner_eq_re_inner ℂ, ← RCLike.re_to_complex,
      inner_re_symm]
  simp_rw [h]
  exact L.forall_integral_inner_clm_apply_eq_zero_iff continuous_const hη

/-- **The dual boundary condition for `F = ℝⁿ`.** On `ℂⁿ`, the boundary term `∫_ℝ Re ⟪i ξ, η⟫`
vanishes for every smooth compactly supported `ξ` that is real on `ℝ` exactly when `η` is real
on `ℝ`. -/
theorem forall_integral_re_inner_I_smul_eq_zero_iff_mem_realSubspace {n : Type*} [Fintype n]
    {η : ℂ → EuclideanSpace ℂ n} (hη : Continuous fun s : ℝ ↦ η s) :
    (∀ ξ : ℂ → EuclideanSpace ℂ n, ContDiff ℝ ∞ ξ → HasCompactSupport ξ →
      (∀ s : ℝ, ξ s ∈ realSubspace n) → ∫ s : ℝ, re ⟪I • ξ s, η s⟫_ℂ = 0) ↔
      ∀ s : ℝ, η s ∈ realSubspace n := by
  simp_rw [Submodule.forall_integral_re_inner_I_smul_eq_zero_iff _ hη,
    forall_re_inner_I_smul_eq_zero_iff_mem_realSubspace]

/-- **The wrong dual boundary condition.** If `η(s) = J(s) ξ(s)` on `ℝ`, which for `ξ` with
values in `Λ` is the condition `η(s) ∈ J(s) Λ`, the boundary integral
`∫_ℝ ⟪η(s), J(s) ξ(s)⟫ = ∫_ℝ ‖J(s) ξ(s)‖²` is positive as soon as `J(s) ξ(s)` is nonzero somewhere
on `ℝ`, so the boundary term does not vanish. -/
theorem integral_inner_clm_apply_pos {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {J : ℝ → V →L[ℝ] V} {η ξ : ℝ → V} (hJ : Continuous J) (hξ : Continuous ξ)
    (hξc : HasCompactSupport ξ) {s₀ : ℝ} (hs₀ : J s₀ (ξ s₀) ≠ 0)
    (hη : ∀ s : ℝ, η s = J s (ξ s)) :
    0 < ∫ s : ℝ, ⟪η s, J s (ξ s)⟫_ℝ := by
  simp_rw [hη, real_inner_self_eq_norm_sq]
  exact ((hJ.clm_apply hξ).norm.pow 2).integral_pos_of_hasCompactSupport_nonneg_ne_zero
    (hξc.mono fun s hs h0 ↦ hs (by simp [h0])) (fun s ↦ sq_nonneg _)
    (pow_ne_zero 2 (norm_ne_zero_iff.2 hs₀))

/-- **The wrong dual boundary condition for `J = i`.** If `η = i ξ` on `ℝ`, which for `ξ` real on
`ℝ` is the condition `η ∈ i ℝⁿ`, the boundary integral `∫_ℝ Re ⟪i ξ, η⟫ = ∫_ℝ ‖ξ‖²` is positive
as soon as `ξ` is nonzero somewhere on `ℝ`, so the boundary term does not vanish. -/
theorem integral_re_inner_I_smul_pos (hξ : Continuous ξ) (hξc : HasCompactSupport ξ) {s₀ : ℝ}
    (hs₀ : ξ s₀ ≠ 0) (hη : ∀ s : ℝ, η s = I • ξ s) :
    0 < ∫ s : ℝ, re ⟪I • ξ s, η s⟫_ℂ := by
  let := InnerProductSpace.complexToReal (G := E)
  have h (x y : E) : re ⟪I • x, y⟫_ℂ = ⟪y, ContinuousLinearMap.lsmul ℝ ℂ I x⟫_ℝ := by
    rw [ContinuousLinearMap.lsmul_apply, real_inner_eq_re_inner ℂ, ← RCLike.re_to_complex,
      inner_re_symm]
  simp_rw [h]
  exact integral_inner_clm_apply_pos (η := fun s : ℝ ↦ η s) continuous_const
    (hξ.comp continuous_ofReal)
    (hξc.comp_isClosedEmbedding Complex.isometry_ofReal.isClosedEmbedding)
    (by simpa using hs₀) fun s ↦ by simp [hη]

end TauCeti
