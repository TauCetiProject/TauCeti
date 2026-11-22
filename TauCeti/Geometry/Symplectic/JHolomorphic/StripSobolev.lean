/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Strip.Rellich
public import TauCeti.Geometry.Symplectic.JHolomorphic.Energy.Strip
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import TauCeti.MeasureTheory.Function.Lp.Norm

/-!
# The Cauchy--Riemann operator on `W^{1,2}` of the strip

The Cauchy--Riemann operator `∂s + J ∂t` (`TauCeti.StripSobolev.cauchyRiemann`) acts on the
Sobolev space `W^{1,2}` of the strip with boundary values in `L₀` and `L₁`
(`TauCeti.StripSobolev.H1`), with values in `L²`, as the first-order operator
`TauCeti.jetOperator` of a constant coefficient. For disjoint isotropic `L₀` and
`L₁`, for instance a transverse pair of Lagrangian subspaces, the energy estimate
`TauCeti.exists_integral_norm_sq_add_partialDeriv_sq_strip_le_mul` on test sections
(`TauCeti.StripSobolev.exists_norm_jetLp_le_mul_norm_cauchyRiemann_jetLp`) passes to the closure:
it is the case `A = 0` of the semi-Fredholm estimate below together with a global `L²` bound, so
the operator is bounded below, hence injective with closed range. This is the linearized operator
of the constant Floer strip at a transverse intersection point of two Lagrangian submanifolds, in
a unitary trivialization. Its surjectivity is not proved here.

Adding a continuous zeroth-order term `A` that vanishes for `|s|` large, the operator
`∂s + J ∂t + A` (with coefficient field `TauCeti.StripSobolev.cauchyRiemannAddJetCoeff J A`) is no
longer bounded below in general, but the same energy estimate gives the semi-Fredholm estimate
`TauCeti.StripSobolev.HasSemiFredholmEstimate` with an error term on the compact piece where `A`
lives (`TauCeti.StripSobolev.exists_hasSemiFredholmEstimate_cauchyRiemannAddJetCoeff`). With
Rellich's theorem on the strip, Peetre's argument gives finite-dimensional kernel
(`TauCeti.StripSobolev.finiteDimensional_ker_jetOperator_cauchyRiemannAddJetCoeff`) and closed
range (`TauCeti.StripSobolev.isClosed_range_jetOperator_cauchyRiemannAddJetCoeff`).

## Main results

* `TauCeti.StripSobolev.exists_norm_le_mul_norm_cauchyRiemann`: on `W^{1,2}`, the Cauchy--Riemann
  operator with disjoint isotropic boundary subspaces is bounded below.
* `TauCeti.StripSobolev.ker_cauchyRiemann_eq_bot` and
  `TauCeti.StripSobolev.isClosed_range_cauchyRiemann`: it is injective with closed range.
* `TauCeti.StripSobolev.exists_hasSemiFredholmEstimate_cauchyRiemannAddJetCoeff`: the
  semi-Fredholm estimate for `∂s + J ∂t + A` with `A` compactly supported in `s`.
* `TauCeti.StripSobolev.finiteDimensional_ker_jetOperator_cauchyRiemannAddJetCoeff` and
  `TauCeti.StripSobolev.isClosed_range_jetOperator_cauchyRiemannAddJetCoeff`: its realization on
  `W^{1,2}` has finite-dimensional kernel and closed range.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., Appendix B,
  on the energy identity and linear Lagrangian boundary integration by parts.
-/

public section

namespace TauCeti.StripSobolev

open MeasureTheory Set Filter
open scoped RealInnerProductSpace Topology ENNReal
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
boundary values in `L₀` and `L₁` (`TauCeti.StripSobolev.H1`) to `L²(ℝ × [0, 1], V)`: the
first-order operator `TauCeti.jetOperator` of the constant coefficient field
`TauCeti.StripSobolev.cauchyRiemannJetCoeff J`, restricted to `H1`. -/
noncomputable def cauchyRiemann : H1 L₀ L₁ →L[ℝ] Lp V 2 stripMeasure :=
  (jetOperator stripMeasure fun _ ↦ cauchyRiemannJetCoeff J).comp (H1 L₀ L₁).subtypeL

/-- The Cauchy--Riemann operator is the first-order operator of its constant coefficient field on
`L²` jets, restricted to `H1`. -/
theorem cauchyRiemann_apply (x : H1 L₀ L₁) :
    cauchyRiemann J L₀ L₁ x =
      jetOperator stripMeasure (fun _ ↦ cauchyRiemannJetCoeff J)
        (x : Lp (V × V × V) 2 stripMeasure) :=
  (rfl)

/-- The Cauchy--Riemann operator acts pointwise on `L²` jets: `(v, v_s, v_t) ↦ v_s + J v_t`. -/
theorem coeFn_cauchyRiemann (x : H1 L₀ L₁) :
    cauchyRiemann J L₀ L₁ x =ᵐ[stripMeasure]
      fun z ↦ ((x : Lp (V × V × V) 2 stripMeasure) z).2.1 +
        J ((x : Lp (V × V × V) 2 stripMeasure) z).2.2 := by
  filter_upwards [coeFn_jetOperator (memLp_top_const (cauchyRiemannJetCoeff J))
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

/-- The energy estimate for `∂s + J ∂t` on the strip, for the test sections with transverse
isotropic boundary values, in the integral form of the semi-Fredholm estimate. -/
private theorem exists_setIntegral_energy_le_mul_setIntegral_cauchyRiemann
    (hg : ∀ v w, ω v (J w) = ⟪v, w⟫) (hL₀ : ω.IsIsotropic L₀) (hL₁ : ω.IsIsotropic L₁)
    (hL : Disjoint L₀ L₁) :
    ∃ C > 0, ∀ ξ ∈ testSection L₀ L₁,
      ∫ z in univ ×ˢ Icc (0 : ℝ) 1,
          (‖fderiv ℝ ξ z (1, 0)‖ ^ 2 + ‖fderiv ℝ ξ z (0, 1)‖ ^ 2 + ‖ξ z‖ ^ 2) ≤
        C * ∫ z in univ ×ˢ Icc (0 : ℝ) 1, ‖fderiv ℝ ξ z (1, 0) + J (fderiv ℝ ξ z (0, 1))‖ ^ 2 := by
  obtain ⟨C, hC, hest⟩ := exists_integral_norm_sq_add_partialDeriv_sq_strip_le_mul hg hL₀ hL₁ hL
  refine ⟨C, hC, fun ξ hξS ↦ ?_⟩
  obtain ⟨hξ, h₀, h₁, R, hR⟩ := mem_testSection_iff.1 hξS
  -- On the strip, `ξ` agrees with a compactly supported `C²` map `η`.
  obtain ⟨η, hη, hc, hηξ⟩ := exists_hasCompactSupport_eventuallyEq_strip hξ hR
  have hP : MeasurableSet (univ ×ˢ Icc (0 : ℝ) 1 : Set (ℝ × ℝ)) :=
    MeasurableSet.univ.prod measurableSet_Icc
  have hcongr (z : ℝ × ℝ) (hz : z ∈ univ ×ˢ Icc (0 : ℝ) 1) :
      η z = ξ z ∧ fderiv ℝ η z = fderiv ℝ ξ z :=
    ⟨(hηξ z hz).eq_of_nhds, (hηξ z hz).fderiv_eq⟩
  have hest' := hest η hη hc (fun s ↦ (hcongr (s, 0) ⟨mem_univ _, by norm_num⟩).1 ▸ h₀ s)
    (fun s ↦ (hcongr (s, 1) ⟨mem_univ _, by norm_num⟩).1 ▸ h₁ s)
  rw [stdComplexLineReal_eq, stdComplexLineImag_eq] at hest'
  refine Eq.trans_le ?_ (hest'.trans_eq ?_)
  · exact setIntegral_congr_fun hP fun z hz ↦ by
      simp only [(hcongr z hz).1, (hcongr z hz).2]
      ring
  · exact congrArg (C * ·) (setIntegral_congr_fun hP fun z hz ↦ by
      simp only [(hcongr z hz).2])

/-- The Cauchy--Riemann estimate on the jets of test sections: with transverse isotropic boundary
conditions, `‖ξ‖_{W^{1,2}} ≤ C ‖∂s ξ + J ∂t ξ‖_{L²}` for every test section `ξ`, with `C`
independent of `ξ`. -/
theorem exists_norm_jetLp_le_mul_norm_cauchyRiemann_jetLp (hg : ∀ v w, ω v (J w) = ⟪v, w⟫)
    (hL₀ : ω.IsIsotropic L₀) (hL₁ : ω.IsIsotropic L₁) (hL : Disjoint L₀ L₁) :
    ∃ C, ∀ ξ : testSection L₀ L₁,
      ‖jetLp (testSection L₀ L₁) ξ‖ ≤
        C * ‖cauchyRiemann J L₀ L₁ ⟨jetLp (testSection L₀ L₁) ξ, jetLp_mem_jetClosure ξ⟩‖ := by
  obtain ⟨C, hC, hest⟩ := exists_setIntegral_energy_le_mul_setIntegral_cauchyRiemann hg hL₀ hL₁ hL
  refine ⟨√C, fun ξ ↦ ?_⟩
  have hsq : ‖jetLp (testSection L₀ L₁) ξ‖ ^ 2 ≤
      (√C * ‖cauchyRiemann J L₀ L₁ ⟨jetLp (testSection L₀ L₁) ξ, jetLp_mem_jetClosure ξ⟩‖) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hC.le, sq_norm_cauchyRiemann_jetLp, stdComplexLineReal_eq,
      stdComplexLineImag_eq]
    exact (sq_norm_jetLp_le_integral ξ (IsTestSpace.contDiff _ ξ.property)).trans
      (hest ξ ξ.property)
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 hsq

end InnerProductSpace

/-! ### Compactly supported zeroth-order perturbations -/

variable (J) in
/-- The coefficient field `z ↦ ((v, v_s, v_t) ↦ v_s + J v_t + A z v)` on jets of the operator
`∂s + J ∂t + A` with zeroth-order term `A`. -/
noncomputable def cauchyRiemannAddJetCoeff (A : ℝ × ℝ → V →L[ℝ] V) (z : ℝ × ℝ) :
    V × V × V →L[ℝ] V :=
  cauchyRiemannJetCoeff J + (A z).comp (ContinuousLinearMap.fst ℝ V (V × V))

@[simp]
theorem cauchyRiemannAddJetCoeff_apply (A : ℝ × ℝ → V →L[ℝ] V) (z : ℝ × ℝ) (v : V × V × V) :
    cauchyRiemannAddJetCoeff J A z v = v.2.1 + J v.2.2 + A z v.1 := by
  simp [cauchyRiemannAddJetCoeff]

/-- On the jet `(ξ, ∂s ξ, ∂t ξ)` of a map, the coefficient field gives `∂s ξ + J ∂t ξ + A ξ`. -/
theorem cauchyRiemannAddJetCoeff_jet (J : AlmostComplexStructure V) (A : ℝ × ℝ → V →L[ℝ] V)
    (ξ : ℝ × ℝ → V) (z : ℝ × ℝ) :
    cauchyRiemannAddJetCoeff J A z (jet ξ z) =
      fderiv ℝ ξ z stdComplexLineReal + J (fderiv ℝ ξ z stdComplexLineImag) + A z (ξ z) := by
  simp [jet_apply, stdComplexLineReal_eq, stdComplexLineImag_eq]

/-- Without zeroth-order term, the coefficient field is the constant coefficient of `∂s + J ∂t`. -/
@[simp]
theorem cauchyRiemannAddJetCoeff_zero (J : AlmostComplexStructure V) :
    cauchyRiemannAddJetCoeff J 0 = fun _ ↦ cauchyRiemannJetCoeff J :=
  funext fun _ ↦ by simp [cauchyRiemannAddJetCoeff]

/-- A continuous zeroth-order term gives a continuous coefficient field. -/
theorem continuous_cauchyRiemannAddJetCoeff {A : ℝ × ℝ → V →L[ℝ] V} (hA : Continuous A) :
    Continuous (cauchyRiemannAddJetCoeff J A) :=
  continuous_const.add (hA.clm_comp continuous_const)

/-- A continuous zeroth-order term vanishing for `|s| > T` gives an essentially bounded coefficient
field on the strip. -/
theorem memLp_cauchyRiemannAddJetCoeff {A : ℝ × ℝ → V →L[ℝ] V} (hA : Continuous A) {T : ℝ}
    (hAT : ∀ z : ℝ × ℝ, T < |z.1| → A z = 0) :
    MemLp (cauchyRiemannAddJetCoeff J A) ∞ stripMeasure :=
  (memLp_top_const (cauchyRiemannJetCoeff J)).add (memLp_stripMeasure_of_continuous
    (u := fun z ↦ (A z).comp (ContinuousLinearMap.fst ℝ V (V × V)))
    (hA.clm_comp continuous_const) (R := T) (fun z hz ↦ by simp [hAT z hz]) ∞)

/-- The Cauchy--Riemann defect `∂s ξ + J ∂t ξ` of a `C¹` section `ξ` vanishing for `|s| > R` is
bounded in `L²` of the strip by `D ξ = ∂s ξ + J ∂t ξ + A ξ` and by `ξ` on the piece
`[-T, T] × [0, 1]` outside which `A` vanishes, where `‖A‖ ≤ B` on the strip. -/
private theorem setIntegral_cauchyRiemann_le {A : ℝ × ℝ → V →L[ℝ] V} (hA : Continuous A)
    {B T : ℝ} (hB : ∀ z ∈ univ ×ˢ Icc (0 : ℝ) 1, ‖A z‖ ≤ B)
    (hAT : ∀ z : ℝ × ℝ, T < |z.1| → A z = 0) {ξ : ℝ × ℝ → V} (hξ : ContDiff ℝ 1 ξ) {R : ℝ}
    (hR : ∀ s t, R ≤ |s| → ξ (s, t) = 0) :
    ∫ z in univ ×ˢ Icc (0 : ℝ) 1, ‖fderiv ℝ ξ z (1, 0) + J (fderiv ℝ ξ z (0, 1))‖ ^ 2 ≤
      2 * (∫ z in univ ×ˢ Icc (0 : ℝ) 1, ‖cauchyRiemannAddJetCoeff J A z (jet ξ z)‖ ^ 2) +
        2 * B ^ 2 * ∫ z in Icc (-T) T ×ˢ Icc (0 : ℝ) 1, ‖ξ z‖ ^ 2 := by
  set P : Set (ℝ × ℝ) := univ ×ˢ Icc (0 : ℝ) 1
  set K : Set (ℝ × ℝ) := Icc (-T) T ×ˢ Icc (0 : ℝ) 1
  have hK : MeasurableSet K := measurableSet_Icc.prod measurableSet_Icc
  -- The integrands are continuous and vanish for `|s| > R`.
  have hd := hξ.continuous_fderiv one_ne_zero
  have hiF : IntegrableOn (fun z ↦ ‖cauchyRiemannAddJetCoeff J A z (jet ξ z)‖ ^ 2) P :=
    integrable_of_jet_eq_zero hR
      (((continuous_cauchyRiemannAddJetCoeff hA).clm_apply (continuous_jet hξ)).norm.pow 2)
      fun z hz ↦ by simp [hz]
  have hiG : IntegrableOn (fun z ↦ ‖ξ z‖ ^ 2) P := integrable_norm_sq_of_continuous hξ.continuous hR
  have hiD : IntegrableOn (fun z ↦ ‖fderiv ℝ ξ z (1, 0) + J (fderiv ℝ ξ z (0, 1))‖ ^ 2) P :=
    integrable_of_jet_eq_zero hR
      (((hd.clm_apply continuous_const).add ((LinearMap.toContinuousLinearMap
        J.toLinearMap).continuous.comp (hd.clm_apply continuous_const))).norm.pow 2)
      fun z hz ↦ by simp_all [jet_apply]
  -- Pointwise, `∂s ξ + J ∂t ξ = D ξ - A ξ`, and `A ξ` lives on `[-T, T] × [0, 1]`.
  have hpt : ∀ z ∈ P, ‖fderiv ℝ ξ z (1, 0) + J (fderiv ℝ ξ z (0, 1))‖ ^ 2 ≤
      2 * ‖cauchyRiemannAddJetCoeff J A z (jet ξ z)‖ ^ 2 +
        2 * B ^ 2 * K.indicator (fun z ↦ ‖ξ z‖ ^ 2) z := by
    intro z hz
    have hsplit : fderiv ℝ ξ z (1, 0) + J (fderiv ℝ ξ z (0, 1)) =
        cauchyRiemannAddJetCoeff J A z (jet ξ z) - A z (ξ z) := by
      rw [cauchyRiemannAddJetCoeff_jet, stdComplexLineReal_eq, stdComplexLineImag_eq]
      abel
    have hAξ : ‖A z (ξ z)‖ ^ 2 ≤ B ^ 2 * K.indicator (fun z ↦ ‖ξ z‖ ^ 2) z := by
      by_cases hzK : z ∈ K
      · rw [indicator_of_mem hzK, ← mul_pow]
        exact pow_le_pow_left₀ (norm_nonneg _) ((A z).le_opNorm _ |>.trans
          (mul_le_mul_of_nonneg_right (hB z hz) (norm_nonneg _))) 2
      · have hzT : T < |z.1| := by
          by_contra h
          exact hzK ⟨abs_le.1 (not_lt.1 h), hz.2⟩
        rw [hAT z hzT, indicator_of_notMem hzK]
        simp
    have hsub := pow_le_pow_left₀ (norm_nonneg _)
      (norm_sub_le (cauchyRiemannAddJetCoeff J A z (jet ξ z)) (A z (ξ z))) 2
    rw [hsplit]
    nlinarith [sq_nonneg (‖cauchyRiemannAddJetCoeff J A z (jet ξ z)‖ - ‖A z (ξ z)‖)]
  have hiK := (hiG.indicator hK).const_mul (2 * B ^ 2)
  refine (setIntegral_mono_on hiD ((hiF.const_mul 2).add hiK)
    (MeasurableSet.univ.prod measurableSet_Icc) hpt).trans_eq ?_
  simp only [Pi.add_apply]
  rw [integral_add (hiF.const_mul 2) hiK, integral_const_mul, integral_const_mul,
    setIntegral_indicator hK, inter_eq_right.2 (prod_mono (subset_univ _) subset_rfl)]

section InnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
variable {ω : SymplecticForm V} {J : AlmostComplexStructure V} {L₀ L₁ : Submodule ℝ V}

/-- **The semi-Fredholm estimate for `∂s + J ∂t + A` on the strip.** Let `J` be compatible with
`ω` in the inner product of `V`, let `L₀`, `L₁` be isotropic subspaces with `L₀ ∩ L₁ = 0`, for
instance a transverse pair of Lagrangian subspaces, and let `A` be a continuous zeroth-order term
vanishing for `|s| > T`. Then the operator `∂s + J ∂t + A` satisfies the semi-Fredholm estimate
on the test sections with boundary values in `L₀` and `L₁`, with error term on
`[-T, T] × [0, 1]`: the energy estimate for `∂s + J ∂t` controls everything, up to `A ξ`, which
lives on that compact piece. -/
theorem exists_hasSemiFredholmEstimate_cauchyRiemannAddJetCoeff
    (hg : ∀ v w, ω v (J w) = ⟪v, w⟫) (hL₀ : ω.IsIsotropic L₀) (hL₁ : ω.IsIsotropic L₁)
    (hL : Disjoint L₀ L₁) {A : ℝ × ℝ → V →L[ℝ] V} (hA : Continuous A) {T : ℝ}
    (hAT : ∀ z : ℝ × ℝ, T < |z.1| → A z = 0) :
    ∃ C, HasSemiFredholmEstimate (testSection L₀ L₁) (cauchyRiemannAddJetCoeff J A) C T := by
  obtain ⟨C, hC, hest⟩ := exists_setIntegral_energy_le_mul_setIntegral_cauchyRiemann hg hL₀ hL₁ hL
  obtain ⟨B, -, hB⟩ := exists_forall_mem_strip_norm_le hA hAT
  refine ⟨2 * C * (1 + B ^ 2), hasSemiFredholmEstimate_iff.2 fun ξ hξS a b _ hvan ↦ ?_⟩
  obtain ⟨R, hR⟩ := IsTestSpace.exists_forall_le_abs_eq_zero _ hξS
  have hξ := IsTestSpace.contDiff _ hξS
  have hD := setIntegral_cauchyRiemann_le (J := J) hA hB hAT hξ hR
  rw [integral_strip_eq_setIntegral_Icc_of_jet_eq_zero
    (F := fun z ↦ ‖cauchyRiemannAddJetCoeff J A z (jet ξ z)‖ ^ 2) hvan
    fun z hz ↦ by simp [hz]] at hD
  -- The energy over `[a, b] × [0, 1]` is at most the energy over the strip.
  have hQ := setIntegral_mono_set (μ := volume) (s := Icc a b ×ˢ Icc (0 : ℝ) 1)
    (t := univ ×ˢ Icc (0 : ℝ) 1)
    (f := fun z ↦ ‖fderiv ℝ ξ z (1, 0)‖ ^ 2 + ‖fderiv ℝ ξ z (0, 1)‖ ^ 2 + ‖ξ z‖ ^ 2)
    (integrable_of_jet_eq_zero hR (continuous_norm_partialDeriv_sq_add_norm_sq hξ)
      fun _ ↦ norm_partialDeriv_sq_add_norm_sq_eq_zero_of_jet_eq_zero)
    (Eventually.of_forall fun z ↦ by positivity)
    (Eventually.of_forall (prod_mono (subset_univ _) subset_rfl))
  have hFnn : 0 ≤ ∫ z in Icc a b ×ˢ Icc (0 : ℝ) 1, ‖cauchyRiemannAddJetCoeff J A z (jet ξ z)‖ ^ 2 :=
    integral_nonneg fun z ↦ by positivity
  have hGnn : 0 ≤ ∫ z in Icc (-T) T ×ˢ Icc (0 : ℝ) 1, ‖ξ z‖ ^ 2 :=
    integral_nonneg fun z ↦ by positivity
  refine (hQ.trans (hest ξ hξS)).trans ?_
  nlinarith [mul_le_mul_of_nonneg_left hD hC.le,
    mul_nonneg (mul_nonneg hC.le (sq_nonneg B)) hFnn, mul_nonneg hC.le hGnn]

/-- **`∂s + J ∂t + A` has finite-dimensional kernel on `W^{1,2}` of the strip.** With `J`
compatible with `ω`, transverse isotropic boundary subspaces `L₀`, `L₁` and a continuous
zeroth-order term `A` vanishing for `|s|` large, the operator `∂s + J ∂t + A` from the Sobolev
space `W^{1,2}` of the strip with boundary values in `L₀` and `L₁` to `L²` has finite-dimensional
kernel, by Peetre's argument. -/
theorem finiteDimensional_ker_jetOperator_cauchyRiemannAddJetCoeff
    (hg : ∀ v w, ω v (J w) = ⟪v, w⟫) (hL₀ : ω.IsIsotropic L₀) (hL₁ : ω.IsIsotropic L₁)
    (hL : Disjoint L₀ L₁) {A : ℝ × ℝ → V →L[ℝ] V} (hA : Continuous A) {T : ℝ}
    (hAT : ∀ z : ℝ × ℝ, T < |z.1| → A z = 0) :
    FiniteDimensional ℝ
      ((jetOperator stripMeasure (cauchyRiemannAddJetCoeff J A)).comp (H1 L₀ L₁).subtypeL).ker := by
  obtain ⟨C, hC⟩ := exists_hasSemiFredholmEstimate_cauchyRiemannAddJetCoeff hg hL₀ hL₁ hL hA hAT
  exact finiteDimensional_ker_jetOperator_comp_subtypeL (memLp_cauchyRiemannAddJetCoeff hA hAT) hC

/-- **`∂s + J ∂t + A` has closed range on `W^{1,2}` of the strip**, under the hypotheses of
`TauCeti.StripSobolev.finiteDimensional_ker_jetOperator_cauchyRiemannAddJetCoeff`. -/
theorem isClosed_range_jetOperator_cauchyRiemannAddJetCoeff
    (hg : ∀ v w, ω v (J w) = ⟪v, w⟫) (hL₀ : ω.IsIsotropic L₀) (hL₁ : ω.IsIsotropic L₁)
    (hL : Disjoint L₀ L₁) {A : ℝ × ℝ → V →L[ℝ] V} (hA : Continuous A) {T : ℝ}
    (hAT : ∀ z : ℝ × ℝ, T < |z.1| → A z = 0) :
    IsClosed
      (((jetOperator stripMeasure (cauchyRiemannAddJetCoeff J A)).comp (H1 L₀ L₁).subtypeL).range :
        Set (Lp V 2 stripMeasure)) := by
  obtain ⟨C, hC⟩ := exists_hasSemiFredholmEstimate_cauchyRiemannAddJetCoeff hg hL₀ hL₁ hL hA hAT
  exact isClosed_range_jetOperator_comp_subtypeL (memLp_cauchyRiemannAddJetCoeff hA hAT) hC

/-- **The Cauchy--Riemann operator of the strip with transverse isotropic boundary conditions is
bounded below.** Let `J` be compatible with `ω` in the inner product of `V`, and let `L₀`, `L₁` be
isotropic subspaces with `L₀ ∩ L₁ = 0`, for instance a transverse pair of Lagrangian subspaces.
Then `‖x‖ ≤ C ‖(∂s + J ∂t) x‖` for every `x` in the Sobolev space `W^{1,2}` of the strip with
boundary values in `L₀` and `L₁`. -/
theorem exists_norm_le_mul_norm_cauchyRiemann (hg : ∀ v w, ω v (J w) = ⟪v, w⟫)
    (hL₀ : ω.IsIsotropic L₀) (hL₁ : ω.IsIsotropic L₁) (hL : Disjoint L₀ L₁) :
    ∃ C, ∀ x : H1 L₀ L₁, ‖x‖ ≤ C * ‖cauchyRiemann J L₀ L₁ x‖ := by
  obtain ⟨C, -, hest⟩ := exists_setIntegral_energy_le_mul_setIntegral_cauchyRiemann hg hL₀ hL₁ hL
  -- The semi-Fredholm estimate for `A = 0`, together with the global `L²` bound from the energy
  -- estimate, gives the bound below by Peetre's argument.
  obtain ⟨C', hC'⟩ := exists_hasSemiFredholmEstimate_cauchyRiemannAddJetCoeff hg hL₀ hL₁ hL
    (A := 0) continuous_const (T := 0) fun _ _ ↦ rfl
  rw [cauchyRiemannAddJetCoeff_zero] at hC'
  obtain ⟨K, hK⟩ := exists_forall_norm_le_mul_norm_jetOperator_comp_subtypeL
    (memLp_top_const (cauchyRiemannJetCoeff J)) hC' (C' := C) fun ξ ↦ by
      obtain ⟨R, hR⟩ := IsTestSpace.exists_forall_le_abs_eq_zero _ ξ.property
      have hξ := IsTestSpace.contDiff _ ξ.property
      refine (integral_mono (integrable_norm_sq_of_continuous hξ.continuous hR)
        (integrable_of_jet_eq_zero hR (continuous_norm_partialDeriv_sq_add_norm_sq hξ)
        fun _ ↦ norm_partialDeriv_sq_add_norm_sq_eq_zero_of_jet_eq_zero) fun z ↦
          le_add_of_nonneg_left (by positivity)).trans ?_
      simpa only [cauchyRiemannJetCoeff_jet, stdComplexLineReal_eq, stdComplexLineImag_eq] using
        hest ξ ξ.property
  exact ⟨K, fun x ↦ by
    simpa only [cauchyRiemann_apply, ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply]
      using hK x⟩

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
