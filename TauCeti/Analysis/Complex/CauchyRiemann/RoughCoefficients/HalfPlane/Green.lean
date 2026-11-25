/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.CauchyRiemann.RoughCoefficients.HalfPlane.Basic
import TauCeti.Analysis.Sobolev.Local.Reflection.InnerIntegrationByParts
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
pairing `⟪φ, J ξ⟫` vanishes on the axis. Both cases are the integration by parts up to the axis
against vector-valued test functions, `TauCeti.setIntegral_im_pos_inner_fderiv_eq_neg`.

## Main results

* `TauCeti.integrableOn_im_pos_inner_crFormalAdjoint_of_memLpLoc`: the pairing `⟪D* φ, ξ⟫` is
  integrable on the upper half-plane for locally `Lᵖ` coefficients.
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

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  {Ω : Opens ℂ} {p q : ℝ≥0∞} {J S : ℂ → V →L[ℝ] V} {DJ : ℂ → ℂ →L[ℝ] V →L[ℝ] V}
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
  have hpos : {z : ℂ | 0 < z.im} ⊆ {z | 0 ≤ z.im} := ofPred_subset_ofPred.2 fun _ => le_of_lt
  have hi {w : ℂ → V} (hw : MemLpLoc 1 ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) w) :=
    IntegrableOn.mono_set (φ.integrable_inner hw.locallyIntegrableOn_restrict_setOf_im_nonneg) hpos
  have hd {w : ℂ → V} (hw : MemLpLoc 1 ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) w) (v : ℂ) :=
    IntegrableOn.mono_set
      (φ.integrable_inner_fderiv hw.locallyIntegrableOn_restrict_setOf_im_nonneg v) hpos
  have t1 := hd (hξq.mono_exponent (ENNReal.inv_le_one.1 (le_add_self.trans hpq))) 1
  have t2 := hd (hJp.memLpLoc_one_clm_apply hξq hpq) I
  have t3 := hi ((hDJp.clm_comp (ContinuousLinearMap.apply ℝ (V →L[ℝ] V) I)).memLpLoc_one_clm_apply
    hξq hpq)
  have t4 := hi (hSp.memLpLoc_one_clm_apply hξq hpq)
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
      (fun K hK hKΩ => memLpLoc_iff.1 hJp K (hKΩ.trans Ω.coe_upperHalf_subset) hK)
      (fun K hK hKΩ => memLpLoc_iff.1 hDJI K (hKΩ.trans Ω.coe_upperHalf_subset) hK)
      (fun K hK hKΩ => memLpLoc_iff.1 hξq K (hKΩ.trans Ω.coe_upperHalf_subset) hK)
      (fun K hK hKΩ => memLpLoc_iff.1 hDξI K (hKΩ.trans Ω.coe_upperHalf_subset) hK)
  have hA := hDJI.memLpLoc_one_clm_apply hξq hpq
  have hB := hJp.memLpLoc_one_clm_apply hDξI hpq
  have h1 := setIntegral_im_pos_inner_fderiv_eq_neg φ (hξ.hasWeakLineDerivOn 1)
    (hξq.mono_exponent hq1) (hDξ1.mono_exponent hq1) (Or.inl (by simp))
  have hI := setIntegral_im_pos_inner_fderiv_eq_neg φ hJξW (hJp.memLpLoc_one_clm_apply hξq hpq)
    (hA.add hB) (Or.inr ⟨hJξ, hφ⟩)
  simp only [inner_add_right] at hI
  -- Pairings of `φ` and its derivatives with fields locally `L¹` up to the axis are integrable.
  have hpos : {z : ℂ | 0 < z.im} ⊆ {z | 0 ≤ z.im} := ofPred_subset_ofPred.2 fun _ => le_of_lt
  have hi {w : ℂ → V} (hw : MemLpLoc 1 ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) w) :=
    IntegrableOn.mono_set (φ.integrable_inner hw.locallyIntegrableOn_restrict_setOf_im_nonneg) hpos
  have hd {w : ℂ → V} (hw : MemLpLoc 1 ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) w) (v : ℂ) :=
    IntegrableOn.mono_set
      (φ.integrable_inner_fderiv hw.locallyIntegrableOn_restrict_setOf_im_nonneg v) hpos
  have i1 := hd (hξq.mono_exponent hq1) 1
  have i2 := hd (hJp.memLpLoc_one_clm_apply hξq hpq) I
  have i3 := hi hA
  have i4 := hi (hSp.memLpLoc_one_clm_apply hξq hpq)
  have i5 := hi (hDξ1.mono_exponent hq1)
  have i6 := hi hB
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
  have hsub := Ω.coe_upperHalf_subset
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
