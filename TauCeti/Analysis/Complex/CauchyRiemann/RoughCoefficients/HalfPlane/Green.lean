/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.CauchyRiemann.RoughCoefficients.HalfPlane.Basic
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff
import TauCeti.Analysis.Distribution.TestFunction.LineDeriv
import TauCeti.Analysis.Sobolev.Leibniz
import TauCeti.Analysis.Sobolev.Local.Reflection.Odd
import TauCeti.Analysis.Sobolev.WeakDeriv.Bilinear.Holder
import TauCeti.MeasureTheory.Measure.Lebesgue.Complex

/-!
# Green's formula up to the real axis for Sobolev solutions

Let `Ω ⊆ ℂ` be open, write `z = s + i t` and `U = Ω ∩ {0 ≤ t}`, and let `V` be a
finite-dimensional real inner product space. For coefficient fields `J, S : ℂ → (V →L[ℝ] V)`
with weak derivative `DJ` of `J` on the open upper part `Ω ∩ {0 < t}`, and a field `ξ` with weak
derivative `Dξ` there, all locally `Lᵖ` or `L^q` up to the axis, this file proves Green's formula
on the upper half-plane

`∫_{0 < t} ⟪D* φ, ξ⟫ = ∫_{0 < t} ⟪φ, Dξ 1 + J (Dξ I) + S ξ⟫`

for every test function `φ ∈ 𝓓(Ω, V)` with `⟪φ(s), J(s) ξ(s)⟫ = 0` on `ℝ ∩ Ω`, when `J ξ` is
continuous on `U` (`TauCeti.setIntegral_im_pos_inner_crFormalAdjoint_of_hasWeakFDerivOn`). Here
`D*` is the formal adjoint `TauCeti.crFormalAdjoint`. This is the Sobolev form of
`TauCeti.setIntegral_im_pos_inner_crFormalAdjoint_of_inner_eq_zero`, which assumes `C¹` data. As a
consequence (`TauCeti.isWeakCRSolutionHalf_iff_ae`), when `⟪Λ, J(s) ξ(s)⟫ = 0` on `ℝ ∩ Ω` the
weak equation up to the boundary `TauCeti.IsWeakCRSolutionHalf` holds exactly when
`Dξ 1 + J (Dξ I) + S ξ = η` almost everywhere on `Ω ∩ {0 < t}`.

The derivative `∂_s` is tangent to the axis and produces no boundary term. For `∂_t`, the
pairing `⟪φ, J ξ⟫` vanishes on the axis, and the integration by parts up to the axis for
functions vanishing there
(`TauCeti.HasWeakLineDerivOn.setIntegral_fderiv_smul_eq_neg_of_continuousOn`)
applies to it, tested against a cutoff equal to `1` near the support of `φ`. Both cases are
`TauCeti.setIntegral_im_pos_inner_fderiv_eq_neg`, through
`TauCeti.HasWeakLineDerivOn.setIntegral_im_pos_eq_zero`.

## Main results

* `TauCeti.HasWeakLineDerivOn.setIntegral_im_pos_eq_zero`: the integral over the upper half-plane
  of a compactly supported weak derivative vanishes, when the direction is tangent to the axis or
  the function vanishes on it.

* `TauCeti.setIntegral_im_pos_inner_fderiv_eq_neg`: integration by parts on the upper half-plane
  for a field `w` weakly differentiable in the direction `v` on `Ω ∩ {0 < t}`, paired with a
  vector-valued test function `φ`, when `v` is tangent to the axis or `⟪φ, w⟫` is continuous up
  to the axis and vanishes on it.
* `TauCeti.setIntegral_im_pos_inner_crFormalAdjoint_of_hasWeakFDerivOn`: Green's formula above.
* `TauCeti.isWeakCRSolutionHalf_iff_ae`: the weak equation up to the boundary for Sobolev data
  is the almost-everywhere equation in the open upper part, given the boundary condition.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix B.4, equation (B.4.3).
-/

public section

open MeasureTheory TopologicalSpace Complex Set Filter
open scoped InnerProductSpace ContDiff Distributions ENNReal Topology

namespace TauCeti

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {Ω : Opens ℂ}

/-- The pairing of a field continuous on `U` with a locally `L¹` field is locally `L¹`. -/
private theorem memLpLoc_one_inner {U : Set ℂ} {ψ w : ℂ → V} (hψ : ContinuousOn ψ U)
    (hw : MemLpLoc 1 U w) : MemLpLoc 1 U (fun z => ⟪ψ z, w z⟫_ℝ) := by
  convert (hw.clm_comp (innerSL ℝ)).clm_apply_continuousOn hψ using 2 with z
  rw [innerSL_apply_apply, real_inner_comm]

/-- The pairing of a test function with a field locally `L¹` up to the axis is integrable on the
upper half-plane. -/
private theorem integrableOn_im_pos_inner (φ : 𝓓(Ω, V)) {w : ℂ → V}
    (hw : MemLpLoc 1 ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) w) :
    IntegrableOn (fun z => ⟪(φ : ℂ → V) z, w z⟫_ℝ) {z : ℂ | 0 < z.im} := by
  have hK : IsCompact (tsupport (φ : ℂ → V) ∩ {z | 0 ≤ z.im}) :=
    φ.hasCompactSupport.isCompact.inter_right (isClosed_le continuous_const continuous_im)
  have hKi : IntegrableOn (fun z => ⟪(φ : ℂ → V) z, w z⟫_ℝ)
      (tsupport (φ : ℂ → V) ∩ {z | 0 ≤ z.im}) :=
    memLp_one_iff_integrable.1 (memLpLoc_iff.1 (memLpLoc_one_inner φ.continuous.continuousOn hw) _
      (inter_subset_inter_left _ φ.tsupport_subset) hK)
  refine hKi.of_forall_sdiff_eq_zero
    (measurableSet_lt measurable_const measurable_im) fun z hz => ?_
  simp [image_eq_zero_of_notMem_tsupport fun h => hz.2 ⟨h, show (0 : ℝ) ≤ z.im from le_of_lt hz.1⟩]

/-- The pairing of a directional derivative of a test function with a field locally `L¹` up to
the axis is integrable on the upper half-plane. -/
private theorem integrableOn_im_pos_inner_fderiv (φ : 𝓓(Ω, V)) {w : ℂ → V}
    (hw : MemLpLoc 1 ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) w) (v : ℂ) :
    IntegrableOn (fun z => ⟪fderiv ℝ (φ : ℂ → V) z v, w z⟫_ℝ) {z : ℂ | 0 < z.im} := by
  simpa only [TestFunction.coe_lineDerivCLM, TestFunction.lineDeriv_eq_fderiv] using
    integrableOn_im_pos_inner (TestFunction.lineDerivCLM ℝ v φ) hw

/-- **The integral of a compactly supported weak derivative up to the axis vanishes.** Let `g'` be
a weak derivative of the real function `g` in the direction `v` on the upper part of `Ω`, with
`g`, `g'` locally `L¹` up to the axis and vanishing off a compact set `K` whose part in the closed
upper half-plane lies in `Ω`. If `v` is tangent to the axis, or `g` is continuous up to the axis
and zero on `ℝ ∩ Ω`, then `∫_{0 < t} g' = 0`. The proof tests against a cutoff equal to `1` near
`K ∩ {0 ≤ t}`. -/
theorem HasWeakLineDerivOn.setIntegral_im_pos_eq_zero {g g' : ℂ → ℝ} {v : ℂ}
    (hg : HasWeakLineDerivOn volume (Opens.interior ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im})) g g' v)
    (hg1 : MemLpLoc 1 ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) g)
    (hg'1 : MemLpLoc 1 ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) g') {K : Set ℂ} (hK : IsCompact K)
    (hKΩ : K ∩ {z | 0 ≤ z.im} ⊆ Ω) (hgK : ∀ z ∉ K, g z = 0) (hg'K : ∀ z ∉ K, g' z = 0)
    (hv : v.im = 0 ∨ ContinuousOn g ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) ∧
      ∀ s : ℝ, (s : ℂ) ∈ Ω → g s = 0) :
    ∫ z in {z : ℂ | 0 < z.im}, g' z = 0 := by
  have hH : MeasurableSet {z : ℂ | 0 < z.im} := measurableSet_lt measurable_const measurable_im
  obtain ⟨ψ, hψ, -, hψ1, hψc, hψΩ⟩ := (hK.inter_right (isClosed_le continuous_const
    continuous_im)).exists_contDiff_cutoff_eventuallyEq_one Ω.isOpen hKΩ
  have key : ∫ z in {z : ℂ | 0 < z.im}, fderiv ℝ ψ z v • g z =
      -∫ z in {z : ℂ | 0 < z.im}, ψ z • g' z := by
    rcases hv with hv | ⟨hgc, hg0⟩
    · exact hg.setIntegral_fderiv_smul_eq_neg hg1 hg'1 hψ hψc (fun z hz => hψΩ hz.1) (Or.inl hv)
    · exact hg.setIntegral_fderiv_smul_eq_neg_of_continuousOn hgc hg0 hg'1 hψ hψc
        fun z hz => hψΩ hz.1
  -- On the upper half-plane `ψ = 1` near `K`, so `∂_v ψ • g = 0` and `ψ • g' = g'`.
  have hl (z : ℂ) (hz : z ∈ {z : ℂ | 0 < z.im}) : fderiv ℝ ψ z v • g z = 0 := by
    by_cases hzK : z ∈ K
    · have h1 : ψ =ᶠ[𝓝 z] fun _ => (1 : ℝ) := hψ1 z ⟨hzK, show (0 : ℝ) ≤ z.im from le_of_lt hz⟩
      simp [h1.fderiv_eq]
    · simp [hgK z hzK]
  have hr (z : ℂ) (hz : z ∈ {z : ℂ | 0 < z.im}) : ψ z • g' z = g' z := by
    by_cases hzK : z ∈ K
    · simp [(hψ1 z ⟨hzK, show (0 : ℝ) ≤ z.im from le_of_lt hz⟩).self_of_nhds]
    · simp [hg'K z hzK]
  rwa [setIntegral_congr_fun hH hl, setIntegral_congr_fun hH hr, integral_zero, eq_comm,
    neg_eq_zero] at key

/-- **Integration by parts on the upper half-plane against a vector-valued test function.** Let
`w'` be a weak derivative of `w` in the direction `v` on the upper part of `Ω`, with `w` and `w'`
locally `L¹` up to the axis, and let `φ ∈ 𝓓(Ω, V)`. If `v` is tangent to the axis, or if `w` is
continuous up to the axis with `⟪φ(s), w(s)⟫ = 0` on `ℝ ∩ Ω`, then
`∫_{0 < t} ⟪∂_v φ, w⟫ = -∫_{0 < t} ⟪φ, w'⟫`: the boundary term `∫_ℝ ⟪φ, w⟫ v.im` vanishes. -/
theorem setIntegral_im_pos_inner_fderiv_eq_neg [FiniteDimensional ℝ V] (φ : 𝓓(Ω, V))
    {w w' : ℂ → V} {v : ℂ}
    (hw : HasWeakLineDerivOn volume Ω.upperHalf w w' v)
    (hw1 : MemLpLoc 1 ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) w)
    (hw'1 : MemLpLoc 1 ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) w')
    (hv : v.im = 0 ∨ ContinuousOn w ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) ∧
      ∀ s : ℝ, (s : ℂ) ∈ Ω → ⟪(φ : ℂ → V) s, w s⟫_ℝ = 0) :
    ∫ z in {z : ℂ | 0 < z.im}, ⟪fderiv ℝ (φ : ℂ → V) z v, w z⟫_ℝ =
      -∫ z in {z : ℂ | 0 < z.im}, ⟪(φ : ℂ → V) z, w' z⟫_ℝ := by
  have : CompleteSpace V := FiniteDimensional.completeSpace ℝ V
  have hφ1 : ContDiff ℝ 1 (φ : ℂ → V) := φ.contDiff.of_le (by simp)
  have hdφ (z : ℂ) : fderiv ℝ (fun z => innerSL ℝ ((φ : ℂ → V) z)) z v =
      innerSL ℝ (fderiv ℝ (φ : ℂ → V) z v) := by
    rw [fderiv_fun_comp z (innerSL ℝ).differentiableAt (hφ1.differentiable one_ne_zero z),
      ContinuousLinearMap.fderiv, ContinuousLinearMap.comp_apply]
  -- The pairing `⟪φ, w⟫` is weakly differentiable on the upper part, by the Leibniz rule.
  have hg : HasWeakLineDerivOn volume (Opens.interior ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}))
      (fun z => ⟪(φ : ℂ → V) z, w z⟫_ℝ)
      (fun z => ⟪(φ : ℂ → V) z, w' z⟫_ℝ + ⟪fderiv ℝ (φ : ℂ → V) z v, w z⟫_ℝ) v := by
    rw [Opens.interior_inter_setOf_im_nonneg_eq_upperHalf]
    simpa [hdφ] using hw.contDiffOn_clm_apply_of_ne_zero
      (Φ := fun z => innerSL ℝ ((φ : ℂ → V) z)) ((innerSL ℝ).contDiff.comp hφ1).contDiffOn
      one_ne_zero
  have hc := φ.continuous.continuousOn (s := (Ω : Set ℂ) ∩ {z | 0 ≤ z.im})
  have hdc : ContinuousOn (fun z => fderiv ℝ (φ : ℂ → V) z v) ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) :=
    ((φ.contDiff.continuous_fderiv (by simp)).clm_apply continuous_const).continuousOn
  have key := hg.setIntegral_im_pos_eq_zero (memLpLoc_one_inner hc hw1)
    ((memLpLoc_one_inner hc hw'1).add (memLpLoc_one_inner hdc hw1))
    φ.hasCompactSupport.isCompact (fun z hz => φ.tsupport_subset hz.1)
    (fun z hz => by simp [image_eq_zero_of_notMem_tsupport hz])
    (fun z hz => by simp [image_eq_zero_of_notMem_tsupport hz, fderiv_of_notMem_tsupport ℝ hz])
    (hv.imp_right fun ⟨hwc, hw0⟩ => ⟨hc.inner hwc, hw0⟩)
  rw [integral_add (integrableOn_im_pos_inner φ hw'1)
    (integrableOn_im_pos_inner_fderiv φ hw1 v)] at key
  linarith

variable [CompleteSpace V] {p q : ℝ≥0∞} {J S : ℂ → V →L[ℝ] V} {DJ : ℂ → ℂ →L[ℝ] V →L[ℝ] V}
  {ξ η : ℂ → V} {Dξ : ℂ → ℂ →L[ℝ] V} {Λ : Submodule ℝ V}

/-- For coefficients `J`, `DJ`, `S` locally `Lᵖ` up to the axis and `1/p + 1/q ≤ 1`, the pairing
`⟪D* φ, ξ⟫` of the weak equation up to the boundary is integrable on the upper half-plane for
every field `ξ` locally `L^q` up to the axis. No relation between `J` and `DJ` is needed. -/
theorem integrableOn_im_pos_inner_crFormalAdjoint_of_memLpLoc
    (hJp : MemLpLoc p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) J)
    (hDJp : MemLpLoc p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) DJ)
    (hSp : MemLpLoc p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) S) (hpq : p⁻¹ + q⁻¹ ≤ 1)
    (hξq : MemLpLoc q ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) ξ) (φ : 𝓓(Ω, V)) :
    IntegrableOn (fun z => ⟪crFormalAdjoint J DJ S φ z, ξ z⟫_ℝ) {z : ℂ | 0 < z.im} := by
  have t1 := integrableOn_im_pos_inner_fderiv φ
    (hξq.mono_exponent (ENNReal.inv_le_one.1 (le_add_self.trans hpq))) 1
  have t2 := integrableOn_im_pos_inner_fderiv φ (hJp.memLpLoc_one_clm_apply hξq hpq) I
  have t3 := integrableOn_im_pos_inner φ
    ((hDJp.clm_comp (ContinuousLinearMap.apply ℝ (V →L[ℝ] V) I)).memLpLoc_one_clm_apply hξq hpq)
  have t4 := integrableOn_im_pos_inner φ (hSp.memLpLoc_one_clm_apply hξq hpq)
  simp only [inner_crFormalAdjoint]
  exact ((t1.neg.sub t2).sub t3).add t4

variable [FiniteDimensional ℝ V]

/-- **Green's formula up to the real axis** for the real Cauchy–Riemann operator with Sobolev
coefficients. Let `DJ` and `Dξ` be weak derivatives of `J` and `ξ` on the upper part of `Ω`, with
`J`, `DJ`, `S` locally `Lᵖ` and `ξ`, `Dξ` locally `L^q` up to the axis, `1/p + 1/q ≤ 1` and
`p, q` finite. If `J ξ` is continuous on `Ω ∩ {0 ≤ t}` and `⟪φ(s), J(s) ξ(s)⟫ = 0` on `ℝ ∩ Ω`,
then `∫_{0 < t} ⟪D* φ, ξ⟫ = ∫_{0 < t} ⟪φ, Dξ 1 + J (Dξ I) + S ξ⟫`. -/
theorem setIntegral_im_pos_inner_crFormalAdjoint_of_hasWeakFDerivOn (hpq : p⁻¹ + q⁻¹ ≤ 1)
    (hp : p ≠ ⊤) (hq : q ≠ ⊤) (hJ : HasWeakFDerivOn volume Ω.upperHalf J DJ)
    (hJp : MemLpLoc p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) J)
    (hDJp : MemLpLoc p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) DJ)
    (hSp : MemLpLoc p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) S)
    (hξ : HasWeakFDerivOn volume Ω.upperHalf ξ Dξ)
    (hξq : MemLpLoc q ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) ξ)
    (hDξq : MemLpLoc q ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) Dξ)
    (hJξ : ContinuousOn (fun z => J z (ξ z)) ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}))
    (φ : 𝓓(Ω, V)) (hφ : ∀ s : ℝ, (s : ℂ) ∈ Ω → ⟪(φ : ℂ → V) s, J s (ξ s)⟫_ℝ = 0) :
    ∫ z in {z : ℂ | 0 < z.im}, ⟪crFormalAdjoint J DJ S φ z, ξ z⟫_ℝ =
      ∫ z in {z : ℂ | 0 < z.im}, ⟪(φ : ℂ → V) z, Dξ z 1 + J z (Dξ z I) + S z (ξ z)⟫_ℝ := by
  have hq1 := ENNReal.inv_le_one.1 (le_add_self.trans hpq)
  have : Fact (1 ≤ p) := ⟨ENNReal.inv_le_one.1 (le_self_add.trans hpq)⟩
  have : Fact (1 ≤ q) := ⟨hq1⟩
  have hsub : (Ω.upperHalf : Set ℂ) ⊆ (Ω : Set ℂ) ∩ {z | 0 ≤ z.im} :=
    fun z hz => ⟨(Opens.mem_upperHalf.1 hz).1, (Opens.mem_upperHalf.1 hz).2.le⟩
  have hDJI : MemLpLoc p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) fun z => DJ z I :=
    hDJp.clm_comp (ContinuousLinearMap.apply ℝ (V →L[ℝ] V) I)
  have hDξ1 : MemLpLoc q ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) fun z => Dξ z 1 :=
    hDξq.clm_comp (ContinuousLinearMap.apply ℝ V 1)
  have hDξI : MemLpLoc q ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) fun z => Dξ z I :=
    hDξq.clm_comp (ContinuousLinearMap.apply ℝ V I)
  -- The weak Leibniz rule for `J ξ` in the direction `I` on the upper part.
  have hJξW : HasWeakLineDerivOn volume Ω.upperHalf (fun z => J z (ξ z))
      (fun z => DJ z I (ξ z) + J z (Dξ z I)) I := by
    simpa using (hJ.hasWeakLineDerivOn I).bilin_of_memLp
      (ContinuousLinearMap.id ℝ (V →L[ℝ] V)) hp hp hq hq hpq hpq hpq (hξ.hasWeakLineDerivOn I)
      (fun K hK hKΩ => memLpLoc_iff.1 hJp K (hKΩ.trans hsub) hK)
      (fun K hK hKΩ => memLpLoc_iff.1 hDJI K (hKΩ.trans hsub) hK)
      (fun K hK hKΩ => memLpLoc_iff.1 hξq K (hKΩ.trans hsub) hK)
      (fun K hK hKΩ => memLpLoc_iff.1 hDξI K (hKΩ.trans hsub) hK)
  have hA := hDJI.memLpLoc_one_clm_apply hξq hpq
  have hB := hJp.memLpLoc_one_clm_apply hDξI hpq
  have h1 := setIntegral_im_pos_inner_fderiv_eq_neg φ (hξ.hasWeakLineDerivOn 1)
    (hξq.mono_exponent hq1) (hDξ1.mono_exponent hq1) (Or.inl (by simp))
  have hI := setIntegral_im_pos_inner_fderiv_eq_neg φ hJξW (hJp.memLpLoc_one_clm_apply hξq hpq)
    (hA.add hB) (Or.inr ⟨hJξ, hφ⟩)
  simp only [inner_add_right] at hI
  have i1 := integrableOn_im_pos_inner_fderiv φ (hξq.mono_exponent hq1) 1
  have i2 := integrableOn_im_pos_inner_fderiv φ (hJp.memLpLoc_one_clm_apply hξq hpq) I
  have i3 := integrableOn_im_pos_inner φ hA
  have i4 := integrableOn_im_pos_inner φ (hSp.memLpLoc_one_clm_apply hξq hpq)
  have i5 := integrableOn_im_pos_inner φ (hDξ1.mono_exponent hq1)
  have i6 := integrableOn_im_pos_inner φ hB
  rw [integral_add i3 i6] at hI
  simp only [inner_crFormalAdjoint, inner_add_right]
  rw [integral_add _ i4, integral_sub _ i3, integral_sub _ i2, integral_neg, integral_add _ i4,
    integral_add i5 i6]
  · linarith
  exacts [i5.add i6, i1.neg, i1.neg.sub i2, (i1.neg.sub i2).sub i3]

/-- **Weak solutions up to the boundary with a weak derivative.** Under the hypotheses on `J`,
`DJ`, `S`, `ξ` and `Dξ` of `TauCeti.setIntegral_im_pos_inner_crFormalAdjoint_of_hasWeakFDerivOn`
and the boundary condition `⟪Λ, J(s) ξ(s)⟫ = 0` on `ℝ ∩ Ω`, the field `ξ` is a weak solution up
to the boundary of `∂_s ξ + J ∂_t ξ + S ξ = η` exactly when `Dξ 1 + J (Dξ I) + S ξ = η` almost
everywhere on `Ω ∩ {0 < t}`. -/
theorem isWeakCRSolutionHalf_iff_ae (hpq : p⁻¹ + q⁻¹ ≤ 1) (hp : p ≠ ⊤) (hq : q ≠ ⊤)
    (hJ : HasWeakFDerivOn volume Ω.upperHalf J DJ)
    (hJp : MemLpLoc p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) J)
    (hDJp : MemLpLoc p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) DJ)
    (hSp : MemLpLoc p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) S)
    (hξ : HasWeakFDerivOn volume Ω.upperHalf ξ Dξ)
    (hξq : MemLpLoc q ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) ξ)
    (hDξq : MemLpLoc q ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) Dξ)
    (hJξ : ContinuousOn (fun z => J z (ξ z)) ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}))
    (hΛ : ∀ s : ℝ, (s : ℂ) ∈ Ω → ∀ v ∈ Λ, ⟪v, J s (ξ s)⟫_ℝ = 0) :
    IsWeakCRSolutionHalf q Ω Λ J DJ S ξ η ↔
      ∀ᵐ z ∂volume.restrict (Ω.upperHalf : Set ℂ),
        Dξ z 1 + J z (Dξ z I) + S z (ξ z) = η z := by
  have hsub : (Ω.upperHalf : Set ℂ) ⊆ (Ω : Set ℂ) ∩ {z | 0 ≤ z.im} :=
    fun z hz => ⟨(Opens.mem_upperHalf.1 hz).1, (Opens.mem_upperHalf.1 hz).2.le⟩
  have hc : IsSobolevCRCoefficients p Ω.upperHalf J DJ S :=
    ⟨hJ, hJp.mono_set hsub, hDJp.mono_set hsub, hSp.mono_set hsub⟩
  refine ⟨fun h => (hc.isWeakCRSolution_iff_ae hpq hp hq hξ (hξq.mono_set hsub)
    (hDξq.mono_set hsub) (h.locallyIntegrableOn.mono_set hsub)).1 h.isWeakCRSolution,
    fun h => ?_⟩
  have hH : MeasurableSet {z : ℂ | 0 < z.im} := measurableSet_lt measurable_const measurable_im
  -- `η` agrees almost everywhere on `Ω ∩ {0 ≤ t}` with the left-hand side, since `ℝ` is null.
  have hη : LocallyIntegrableOn η ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) := by
    have hq1 := ENNReal.inv_le_one.1 (le_add_self.trans hpq)
    refine (((((hDξq.clm_comp (ContinuousLinearMap.apply ℝ V 1)).mono_exponent hq1).add
      (hJp.memLpLoc_one_clm_apply (hDξq.clm_comp (ContinuousLinearMap.apply ℝ V I)) hpq)).add
      (hSp.memLpLoc_one_clm_apply hξq hpq)).locallyIntegrableOn le_rfl
      (Ω.isOpen.isLocallyClosed_inter_setOfPred_le_im 0)).congr ?_
    rw [Measure.restrict_congr_set (ae_eq_set_inter (by rfl) (Complex.setOf_le_im_ae_eq 0)),
      ← Opens.coe_upperHalf]
    exact h
  refine isWeakCRSolutionHalf_iff.2 ⟨hξq, hη, fun φ hφΛ => ⟨?_, ?_⟩⟩
  · exact integrableOn_im_pos_inner_crFormalAdjoint_of_memLpLoc hJp hDJp hSp hpq hξq φ
  · rw [setIntegral_im_pos_inner_crFormalAdjoint_of_hasWeakFDerivOn hpq hp hq hJ hJp hDJp hSp hξ
      hξq hDξq hJξ φ fun s hs => hΛ s hs _ (hφΛ s)]
    refine setIntegral_congr_ae hH ?_
    filter_upwards [ae_imp_of_ae_restrict h] with z hz hz0
    by_cases hzΩ : z ∈ (Ω : Set ℂ)
    · rw [hz (Opens.mem_upperHalf.2 ⟨hzΩ, hz0⟩)]
    · simp [image_eq_zero_of_notMem_tsupport fun h' => hzΩ (φ.tsupport_subset h')]

end TauCeti
