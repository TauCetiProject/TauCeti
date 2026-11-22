/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.JetOperator
public import TauCeti.Analysis.Sobolev.Strip.Basic
public import TauCeti.Geometry.Symplectic.JHolomorphic.Energy.Strip
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import TauCeti.MeasureTheory.Function.LocallyIntegrable
import TauCeti.MeasureTheory.Function.Lp.Norm

/-!
# The Cauchy--Riemann operator on `W^{1,2}` of the strip

The Cauchy--Riemann operator `∂s + J ∂t` (`TauCeti.StripSobolev.cauchyRiemann`) acts on the
Sobolev space `W^{1,2}` of the strip with boundary values in `L₀` and `L₁`
(`TauCeti.StripSobolev.H1`), with values in `L²`. For disjoint isotropic `L₀` and `L₁`, for
instance a transverse pair of Lagrangian subspaces, the energy estimate
`TauCeti.exists_integral_norm_sq_add_partialDeriv_sq_strip_le_mul` on test sections
(`TauCeti.StripSobolev.exists_norm_jetLp_le_mul_norm_cauchyRiemann_jetLp`) passes to the closure:
the operator is bounded below, hence injective with closed range. This is the linearized operator
of the constant Floer strip at a transverse intersection point of two Lagrangian submanifolds, in
a unitary trivialization. Its surjectivity is not proved here.

## Main results

* `TauCeti.StripSobolev.exists_norm_le_mul_norm_cauchyRiemann`: on `W^{1,2}`, the Cauchy--Riemann
  operator with disjoint isotropic boundary subspaces is bounded below.
* `TauCeti.StripSobolev.ker_cauchyRiemann_eq_bot` and
  `TauCeti.StripSobolev.isClosed_range_cauchyRiemann`: it is injective with closed range.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., Appendix B,
  on the energy identity and linear Lagrangian boundary integration by parts.
-/

public section

namespace TauCeti.StripSobolev

open MeasureTheory Set
open scoped RealInnerProductSpace Topology
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
variable {J : AlmostComplexStructure V} {L₀ L₁ : Submodule ℝ V}

/-- The coefficient `(v, v_s, v_t) ↦ v_s + J v_t` of the Cauchy--Riemann operator `∂s + J ∂t`
on jets: the coefficient field `TauCeti.firstOrderJetCoeff` of `∂s + J ∂t + 0`. -/
noncomputable def cauchyRiemannJetCoeff (J : AlmostComplexStructure V) : V × V × V →L[ℝ] V :=
  firstOrderJetCoeff (LinearMap.toContinuousLinearMap J.toLinearMap) 0

@[simp]
theorem cauchyRiemannJetCoeff_apply (J : AlmostComplexStructure V) (v : V × V × V) :
    cauchyRiemannJetCoeff J v = v.2.1 + J v.2.2 := by
  simp [cauchyRiemannJetCoeff]

/-- On the jet `(ξ, ∂s ξ, ∂t ξ)` of a map, the coefficient gives `∂s ξ + J ∂t ξ`. -/
theorem cauchyRiemannJetCoeff_jet (J : AlmostComplexStructure V) (ξ : ℝ × ℝ → V)
    (z : ℝ × ℝ) :
    cauchyRiemannJetCoeff J (jet ξ z) =
      fderiv ℝ ξ z stdComplexLineReal + J (fderiv ℝ ξ z stdComplexLineImag) := by
  rw [cauchyRiemannJetCoeff_apply, jet_apply, stdComplexLineReal_eq, stdComplexLineImag_eq]

variable (J L₀ L₁) in
/-- The Cauchy--Riemann operator `∂s + J ∂t` from the Sobolev space `W^{1,2}` of the strip with
boundary values in `L₀` and `L₁` (`TauCeti.StripSobolev.H1`) to `L²(ℝ × [0, 1], V)`. -/
noncomputable def cauchyRiemann : H1 L₀ L₁ →L[ℝ] Lp V 2 stripMeasure :=
  ((cauchyRiemannJetCoeff J).compLpL 2 stripMeasure).comp (H1 L₀ L₁).subtypeL

/-- The Cauchy--Riemann operator is the pointwise action of its coefficient on `L²` jets,
restricted to `H1`. -/
theorem cauchyRiemann_apply (x : H1 L₀ L₁) :
    cauchyRiemann J L₀ L₁ x =
      (cauchyRiemannJetCoeff J).compLpL 2 stripMeasure (x : Lp (V × V × V) 2 stripMeasure) :=
  (rfl)

/-- The Cauchy--Riemann operator acts pointwise on `L²` jets: `(v, v_s, v_t) ↦ v_s + J v_t`. -/
theorem coeFn_cauchyRiemann (x : H1 L₀ L₁) :
    cauchyRiemann J L₀ L₁ x =ᵐ[stripMeasure]
      fun z ↦ ((x : Lp (V × V × V) 2 stripMeasure) z).2.1 +
        J ((x : Lp (V × V × V) 2 stripMeasure) z).2.2 := by
  filter_upwards [(cauchyRiemannJetCoeff J).coeFn_compLpL (p := 2) (μ := stripMeasure)
    (x : Lp (V × V × V) 2 stripMeasure)] with z hz
  rw [cauchyRiemann_apply, hz, cauchyRiemannJetCoeff_apply]

/-- On the jet of a test section `ξ`, the Cauchy--Riemann operator is `∂s ξ + J ∂t ξ`. -/
theorem cauchyRiemann_jetLp_ae_eq (ξ : testSection L₀ L₁) :
    cauchyRiemann J L₀ L₁ ⟨jetLp (testSection L₀ L₁) ξ, jetLp_mem_jetClosure ξ⟩ =ᵐ[stripMeasure]
      fun z ↦ fderiv ℝ (ξ : ℝ × ℝ → V) z stdComplexLineReal +
        J (fderiv ℝ (ξ : ℝ × ℝ → V) z stdComplexLineImag) := by
  filter_upwards [coeFn_cauchyRiemann (J := J)
    ⟨jetLp (testSection L₀ L₁) ξ, jetLp_mem_jetClosure ξ⟩, coeFn_jetLp ξ] with z h₁ h₂
  rw [h₁, h₂, ← cauchyRiemannJetCoeff_apply, cauchyRiemannJetCoeff_jet]

/-- The squared `L²` norm of the Cauchy--Riemann operator on the jet of a test section `ξ` is the
integral of `‖∂s ξ + J ∂t ξ‖²` over the strip. -/
theorem sq_norm_cauchyRiemann_jetLp (ξ : testSection L₀ L₁) :
    ‖cauchyRiemann J L₀ L₁ ⟨jetLp (testSection L₀ L₁) ξ, jetLp_mem_jetClosure ξ⟩‖ ^ 2 =
      ∫ z in univ ×ˢ Icc (0 : ℝ) 1, ‖fderiv ℝ (ξ : ℝ × ℝ → V) z stdComplexLineReal +
        J (fderiv ℝ (ξ : ℝ × ℝ → V) z stdComplexLineImag)‖ ^ 2 := by
  rw [← Lp.integral_norm_sq_eq_norm_sq]
  refine integral_congr_ae ?_
  filter_upwards [cauchyRiemann_jetLp_ae_eq (J := J) ξ] with z hz
  rw [hz]

omit [FiniteDimensional ℝ V] in
/-- A `C²` map of the plane vanishing for `|s|` large agrees, near every point of the strip
`ℝ × [0, 1]`, with a compactly supported `C²` map: multiply it by a bump function of `t` equal to
one near `[0, 1]`. -/
private theorem exists_hasCompactSupport_eventuallyEq_strip {ξ : ℝ × ℝ → V} (hξ : ContDiff ℝ 2 ξ)
    {R : ℝ} (hR : ∀ s t, R ≤ |s| → ξ (s, t) = 0) :
    ∃ η : ℝ × ℝ → V, ContDiff ℝ 2 η ∧ HasCompactSupport η ∧
      ∀ z ∈ univ ×ˢ Icc (0 : ℝ) 1, η =ᶠ[𝓝 z] ξ := by
  let χ : ContDiffBump (1 / 2 : ℝ) := ⟨3 / 2, 2, by norm_num, by norm_num⟩
  refine ⟨fun z ↦ χ z.2 • ξ z, (χ.contDiff.comp contDiff_snd).smul hξ, ?_, fun z hz ↦ ?_⟩
  · refine HasCompactSupport.intro (K := Icc (-R) R ×ˢ Metric.closedBall (1 / 2) 2)
      (isCompact_Icc.prod (isCompact_closedBall _ _)) fun z hz ↦ ?_
    rw [mem_prod, not_and_or] at hz
    rcases hz with hz | hz
    · rw [hR z.1 z.2 (not_le.1 (mt abs_le.1 hz)).le, smul_zero]
    · rw [Function.notMem_support.1 fun h ↦ hz (Metric.ball_subset_closedBall
        (χ.support_eq ▸ h)), zero_smul]
  · have h1 : χ =ᶠ[𝓝 z.2] 1 := χ.eventuallyEq_one_of_mem_ball <| by
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      constructor <;> linarith [hz.2.1, hz.2.2, show χ.rIn = 3 / 2 from rfl]
    filter_upwards [h1.comp_tendsto continuous_snd.continuousAt] with w hw
    simp only [Function.comp_apply, Pi.one_apply] at hw
    rw [hw, one_smul]

section InnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
variable {ω : SymplecticForm V} {J : AlmostComplexStructure V} {L₀ L₁ : Submodule ℝ V}

/-- The Cauchy--Riemann estimate on the jets of test sections: with transverse isotropic boundary
conditions, `‖ξ‖_{W^{1,2}} ≤ C ‖∂s ξ + J ∂t ξ‖_{L²}` for every test section `ξ`, with `C`
independent of `ξ`. -/
theorem exists_norm_jetLp_le_mul_norm_cauchyRiemann_jetLp (hg : ∀ v w, ω v (J w) = ⟪v, w⟫)
    (hL₀ : ω.IsIsotropic L₀) (hL₁ : ω.IsIsotropic L₁) (hL : Disjoint L₀ L₁) :
    ∃ C, ∀ ξ : testSection L₀ L₁,
      ‖jetLp (testSection L₀ L₁) ξ‖ ≤
        C * ‖cauchyRiemann J L₀ L₁ ⟨jetLp (testSection L₀ L₁) ξ, jetLp_mem_jetClosure ξ⟩‖ := by
  obtain ⟨C, hC, hest⟩ := exists_integral_norm_sq_add_partialDeriv_sq_strip_le_mul hg hL₀ hL₁ hL
  refine ⟨√C, fun ξ ↦ ?_⟩
  obtain ⟨hξ, h₀, h₁, R, hR⟩ := mem_testSection_iff.1 ξ.property
  -- On the strip, `ξ` agrees with a compactly supported `C²` map `η`.
  obtain ⟨η, hη, hc, hηξ⟩ := exists_hasCompactSupport_eventuallyEq_strip hξ hR
  have hstrip : MeasurableSet (univ ×ˢ Icc (0 : ℝ) 1 : Set (ℝ × ℝ)) :=
    MeasurableSet.univ.prod measurableSet_Icc
  have hcongr (z : ℝ × ℝ) (hz : z ∈ univ ×ˢ Icc (0 : ℝ) 1) :
      η z = (ξ : ℝ × ℝ → V) z ∧ fderiv ℝ η z = fderiv ℝ (ξ : ℝ × ℝ → V) z :=
    ⟨(hηξ z hz).eq_of_nhds, (hηξ z hz).fderiv_eq⟩
  have hdu : Continuous (fderiv ℝ η) := hη.continuous_fderiv (by norm_num)
  have hint : Integrable (fun z ↦ ‖(ξ : ℝ × ℝ → V) z‖ ^ 2 +
      (‖fderiv ℝ (ξ : ℝ × ℝ → V) z stdComplexLineReal‖ ^ 2 +
        ‖fderiv ℝ (ξ : ℝ × ℝ → V) z stdComplexLineImag‖ ^ 2)) stripMeasure := by
    refine IntegrableOn.congr_fun (((hη.continuous.integrable_norm_sq_of_hasCompactSupport hc).add
      (((hdu.clm_apply continuous_const).integrable_norm_sq_of_hasCompactSupport
        (hc.fderiv_apply ℝ stdComplexLineReal)).add
      ((hdu.clm_apply continuous_const).integrable_norm_sq_of_hasCompactSupport
        (hc.fderiv_apply ℝ stdComplexLineImag)))).integrableOn) (fun z hz ↦ ?_) hstrip
    simp only [Pi.add_apply, (hcongr z hz).1, (hcongr z hz).2]
  have hest' := hest η hη hc (fun s ↦ (hcongr (s, 0) ⟨mem_univ _, by norm_num⟩).1 ▸ h₀ s)
    (fun s ↦ (hcongr (s, 1) ⟨mem_univ _, by norm_num⟩).1 ▸ h₁ s)
  have hsq : ‖jetLp (testSection L₀ L₁) ξ‖ ^ 2 ≤
      (√C * ‖cauchyRiemann J L₀ L₁ ⟨jetLp (testSection L₀ L₁) ξ, jetLp_mem_jetClosure ξ⟩‖) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hC.le, sq_norm_cauchyRiemann_jetLp, sq_norm_jetLp]
    refine (integral_mono_of_nonneg (.of_forall fun z ↦ by positivity) hint
      (.of_forall fun z ↦ (sq_norm_jet_le _ z).trans_eq ?_)).trans ?_
    · rw [stdComplexLineReal_eq, stdComplexLineImag_eq]
      ring
    refine Eq.trans_le ?_ (hest'.trans_eq ?_)
    · exact setIntegral_congr_fun hstrip fun z hz ↦ by
        simp only [(hcongr z hz).1, (hcongr z hz).2]
    · exact congrArg (C * ·) (setIntegral_congr_fun hstrip fun z hz ↦ by
        simp only [(hcongr z hz).2])
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 hsq

/-- **The Cauchy--Riemann operator of the strip with transverse isotropic boundary conditions is
bounded below.** Let `J` be compatible with `ω` in the inner product of `V`, and let `L₀`, `L₁` be
isotropic subspaces with `L₀ ∩ L₁ = 0`, for instance a transverse pair of Lagrangian subspaces.
Then `‖x‖ ≤ C ‖(∂s + J ∂t) x‖` for every `x` in the Sobolev space `W^{1,2}` of the strip with
boundary values in `L₀` and `L₁`. -/
theorem exists_norm_le_mul_norm_cauchyRiemann (hg : ∀ v w, ω v (J w) = ⟪v, w⟫)
    (hL₀ : ω.IsIsotropic L₀) (hL₁ : ω.IsIsotropic L₁) (hL : Disjoint L₀ L₁) :
    ∃ C, ∀ x : H1 L₀ L₁, ‖x‖ ≤ C * ‖cauchyRiemann J L₀ L₁ x‖ := by
  obtain ⟨C, hC⟩ := exists_norm_jetLp_le_mul_norm_cauchyRiemann_jetLp hg hL₀ hL₁ hL
  set D := (cauchyRiemannJetCoeff J).compLpL 2 stripMeasure with hD
  -- The estimate on the jets of test sections passes to their closure `H1`.
  refine ⟨C, fun x ↦ ?_⟩
  have hsub := jetClosure_subset_of_isClosed (S := testSection L₀ L₁)
    (s := {f | ‖f‖ ≤ C * ‖D f‖})
    (isClosed_le continuous_norm (continuous_const.mul (continuous_norm.comp D.continuous)))
    (by
      rintro _ ⟨ξ, rfl⟩
      simpa only [mem_ofPred_eq, hD, cauchyRiemann_apply, Submodule.coe_mk] using hC ξ)
  have hx := hsub x.property
  rwa [mem_ofPred_eq, hD, ← cauchyRiemann_apply, Submodule.norm_coe] at hx

/-- With transverse isotropic boundary conditions the Cauchy--Riemann operator on `W^{1,2}` of the
strip is injective. -/
theorem ker_cauchyRiemann_eq_bot (hg : ∀ v w, ω v (J w) = ⟪v, w⟫)
    (hL₀ : ω.IsIsotropic L₀) (hL₁ : ω.IsIsotropic L₁) (hL : Disjoint L₀ L₁) :
    (cauchyRiemann J L₀ L₁).ker = ⊥ := by
  obtain ⟨C, hC⟩ := exists_norm_le_mul_norm_cauchyRiemann hg hL₀ hL₁ hL
  refine (Submodule.eq_bot_iff _).2 fun x hx ↦ norm_le_zero_iff.1 ?_
  rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe] at hx
  have h := hC x
  rwa [hx, norm_zero, mul_zero] at h

/-- With transverse isotropic boundary conditions the Cauchy--Riemann operator on `W^{1,2}` of the
strip has closed range. -/
theorem isClosed_range_cauchyRiemann (hg : ∀ v w, ω v (J w) = ⟪v, w⟫)
    (hL₀ : ω.IsIsotropic L₀) (hL₁ : ω.IsIsotropic L₁) (hL : Disjoint L₀ L₁) :
    IsClosed (Set.range (cauchyRiemann J L₀ L₁)) := by
  obtain ⟨C, hC⟩ := exists_norm_le_mul_norm_cauchyRiemann hg hL₀ hL₁ hL
  refine ((cauchyRiemann J L₀ L₁).antilipschitz_of_bound (K := C.toNNReal) fun x ↦
    (hC x).trans ?_).isClosed_range (cauchyRiemann J L₀ L₁).uniformContinuous
  exact mul_le_mul_of_nonneg_right (Real.le_coe_toNNReal C) (norm_nonneg _)

end InnerProductSpace

end TauCeti.StripSobolev
