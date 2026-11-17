/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Strip
public import TauCeti.Geometry.Symplectic.JHolomorphic.Energy.Strip
import TauCeti.MeasureTheory.Function.LocallyIntegrable
import TauCeti.MeasureTheory.Function.Lp.Norm

/-!
# The Cauchy--Riemann operator on `W^{1,2}` of the strip

The Cauchy--Riemann operator `∂s + J ∂t` (`TauCeti.StripSobolev.cauchyRiemann`) acts on the
Sobolev space `W^{1,2}` of the strip with boundary values in `L₀` and `L₁`
(`TauCeti.StripSobolev.H1`), with values in `L²`. For disjoint isotropic `L₀` and `L₁`, for
instance a transverse pair of Lagrangian subspaces, the energy estimate
`TauCeti.exists_integral_norm_sq_add_partialDeriv_sq_strip_le_mul` on test sections
(`TauCeti.StripSobolev.exists_norm_jetₗ_le_mul_norm_cauchyRiemann_jetₗ`) passes to the closure:
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
open scoped RealInnerProductSpace
open CylinderSobolev (stripMeasure jet jet_apply sq_norm_jet_le coeFn_jetLp sq_norm_jetLp
  jetLp_mem_jetClosure jetClosure_subset_of_isClosed)

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
variable {ω : SymplecticForm V} {J : AlmostComplexStructure V} {L₀ L₁ : Submodule ℝ V}

/-- The coefficient `(v, v_s, v_t) ↦ v_s + J v_t` of the Cauchy--Riemann operator `∂s + J ∂t`
on jets. -/
noncomputable def cauchyRiemannJetCoeff (J : AlmostComplexStructure V) : V × V × V →L[ℝ] V :=
  (ContinuousLinearMap.fst ℝ V V).comp (ContinuousLinearMap.snd ℝ V (V × V)) +
    (LinearMap.toContinuousLinearMap J.toLinearMap).comp
      ((ContinuousLinearMap.snd ℝ V V).comp (ContinuousLinearMap.snd ℝ V (V × V)))

@[simp]
theorem cauchyRiemannJetCoeff_apply (J : AlmostComplexStructure V) (v : V × V × V) :
    cauchyRiemannJetCoeff J v = v.2.1 + J v.2.2 :=
  (rfl)

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
        J ((x : Lp (V × V × V) 2 stripMeasure) z).2.2 :=
  (cauchyRiemannJetCoeff J).coeFn_compLpL _

/-- On the jet of a test section `ξ`, the Cauchy--Riemann operator is `∂s ξ + J ∂t ξ`. -/
theorem cauchyRiemann_jetₗ_ae_eq (ξ : testSection L₀ L₁) :
    cauchyRiemann J L₀ L₁ ⟨jetₗ L₀ L₁ ξ, jetLp_mem_jetClosure ξ⟩ =ᵐ[stripMeasure]
      fun z ↦ fderiv ℝ (ξ : ℝ × ℝ → V) z stdComplexLineReal +
        J (fderiv ℝ (ξ : ℝ × ℝ → V) z stdComplexLineImag) := by
  filter_upwards [coeFn_cauchyRiemann (J := J) ⟨jetₗ L₀ L₁ ξ, jetLp_mem_jetClosure ξ⟩,
    coeFn_jetLp ξ] with z h₁ h₂
  rw [h₁, h₂, ← cauchyRiemannJetCoeff_apply, cauchyRiemannJetCoeff_jet]

/-- The squared `L²` norm of the Cauchy--Riemann operator on the jet of a test section `ξ` is the
integral of `‖∂s ξ + J ∂t ξ‖²` over the strip. -/
theorem sq_norm_cauchyRiemann_jetₗ (ξ : testSection L₀ L₁) :
    ‖cauchyRiemann J L₀ L₁ ⟨jetₗ L₀ L₁ ξ, jetLp_mem_jetClosure ξ⟩‖ ^ 2 =
      ∫ z in univ ×ˢ Icc (0 : ℝ) 1, ‖fderiv ℝ (ξ : ℝ × ℝ → V) z stdComplexLineReal +
        J (fderiv ℝ (ξ : ℝ × ℝ → V) z stdComplexLineImag)‖ ^ 2 := by
  rw [← Lp.integral_norm_sq_eq_norm_sq]
  refine integral_congr_ae ?_
  filter_upwards [cauchyRiemann_jetₗ_ae_eq (J := J) ξ] with z hz
  rw [hz]

/-- The Cauchy--Riemann estimate on the jets of test sections: with transverse isotropic boundary
conditions, `‖ξ‖_{W^{1,2}} ≤ C ‖∂s ξ + J ∂t ξ‖_{L²}` for every test section `ξ`, with `C`
independent of `ξ`. -/
theorem exists_norm_jetₗ_le_mul_norm_cauchyRiemann_jetₗ (hg : ∀ v w, ω v (J w) = ⟪v, w⟫)
    (hL₀ : ω.IsIsotropic L₀) (hL₁ : ω.IsIsotropic L₁) (hL : Disjoint L₀ L₁) :
    ∃ C, ∀ ξ : testSection L₀ L₁,
      ‖jetₗ L₀ L₁ ξ‖ ≤ C * ‖cauchyRiemann J L₀ L₁ ⟨jetₗ L₀ L₁ ξ, jetLp_mem_jetClosure ξ⟩‖ := by
  obtain ⟨C, hC, hest⟩ := exists_integral_norm_sq_add_partialDeriv_sq_strip_le_mul hg hL₀ hL₁ hL
  refine ⟨√C, fun ξ ↦ ?_⟩
  obtain ⟨hξ, hc, h₀, h₁⟩ := mem_testSection_iff.1 ξ.2
  have hdu : Continuous (fderiv ℝ (ξ : ℝ × ℝ → V)) := hξ.continuous_fderiv (by norm_num)
  have hint : Integrable (fun z ↦ ‖(ξ : ℝ × ℝ → V) z‖ ^ 2 +
      (‖fderiv ℝ (ξ : ℝ × ℝ → V) z stdComplexLineReal‖ ^ 2 +
        ‖fderiv ℝ (ξ : ℝ × ℝ → V) z stdComplexLineImag‖ ^ 2)) stripMeasure :=
    ((hξ.continuous.integrable_norm_sq_of_hasCompactSupport hc).add
      (((hdu.clm_apply continuous_const).integrable_norm_sq_of_hasCompactSupport
        (hc.fderiv_apply ℝ stdComplexLineReal)).add
      ((hdu.clm_apply continuous_const).integrable_norm_sq_of_hasCompactSupport
        (hc.fderiv_apply ℝ stdComplexLineImag)))).integrableOn
  have hsq : ‖jetₗ L₀ L₁ ξ‖ ^ 2 ≤
      (√C * ‖cauchyRiemann J L₀ L₁ ⟨jetₗ L₀ L₁ ξ, jetLp_mem_jetClosure ξ⟩‖) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hC.le, sq_norm_cauchyRiemann_jetₗ, sq_norm_jetLp]
    refine (integral_mono_of_nonneg (.of_forall fun z ↦ by positivity) hint
      (.of_forall fun z ↦ (sq_norm_jet_le _ z).trans_eq ?_)).trans ?_
    · rw [stdComplexLineReal_eq, stdComplexLineImag_eq]
      ring
    exact hest ξ hξ hc h₀ h₁
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 hsq

/-- **The Cauchy--Riemann operator of the strip with transverse isotropic boundary conditions is
bounded below.** Let `J` be compatible with `ω` in the inner product of `V`, and let `L₀`, `L₁` be
isotropic subspaces with `L₀ ∩ L₁ = 0`, for instance a transverse pair of Lagrangian subspaces.
Then `‖x‖ ≤ C ‖(∂s + J ∂t) x‖` for every `x` in the Sobolev space `W^{1,2}` of the strip with
boundary values in `L₀` and `L₁`. -/
theorem exists_norm_le_mul_norm_cauchyRiemann (hg : ∀ v w, ω v (J w) = ⟪v, w⟫)
    (hL₀ : ω.IsIsotropic L₀) (hL₁ : ω.IsIsotropic L₁) (hL : Disjoint L₀ L₁) :
    ∃ C, ∀ x : H1 L₀ L₁, ‖x‖ ≤ C * ‖cauchyRiemann J L₀ L₁ x‖ := by
  obtain ⟨C, hC⟩ := exists_norm_jetₗ_le_mul_norm_cauchyRiemann_jetₗ hg hL₀ hL₁ hL
  set D := (cauchyRiemannJetCoeff J).compLpL 2 stripMeasure
  -- The estimate on the jets of test sections passes to their closure `H1`.
  refine ⟨C, fun x ↦ ?_⟩
  have hsub := jetClosure_subset_of_isClosed (S := testSection L₀ L₁)
    (s := {f | ‖f‖ ≤ C * ‖D f‖})
    (isClosed_le continuous_norm (continuous_const.mul (continuous_norm.comp D.continuous)))
    (by rintro _ ⟨ξ, rfl⟩; exact hC ξ)
  exact hsub x.2

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

end TauCeti.StripSobolev
