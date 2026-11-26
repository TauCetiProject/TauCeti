/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.ODE.TrajectoryOperator
public import TauCeti.Analysis.Sobolev.Cylinder.Slice.ZeroMode
public import TauCeti.Geometry.Symplectic.Floer.Sobolev.Realization
public import TauCeti.Geometry.Symplectic.Floer.TimeIndependent.NonzeroModes
import TauCeti.MeasureTheory.Function.Lp.Norm
import TauCeti.MeasureTheory.Integral.Rectangle

/-!
# The Sobolev realization of the linearized operator along a time-independent cylinder

Let `(V, ω)` be a finite-dimensional symplectic vector space whose inner product is the metric
`ω(·, J ·)` of a constant compatible almost complex structure `J`, let `H : V → ℝ` be a `C²`
autonomous Hamiltonian and `γ` a continuous curve, and let

`D ξ = ∂s ξ + J (∂t ξ - dX_H(γ(s)) ξ)`

be the linearized Floer operator along the time-independent cylinder `(s, t) ↦ γ(s)`
(`TauCeti.SymplecticForm.floerLinearization_const_eq`), realized on the Sobolev space as
`TauCeti.SymplecticForm.floerSobolevOperator : W^{1,2}(ℝ × S¹, V) → L²(ℝ × S¹, V)`. Its
coefficients do not depend on `t`. This file shows that, when `‖dX_H(γ(s))‖ ≤ a < 2π` for every
`s`, the realization commutes with the projection onto the zero Fourier mode, that the other
modes carry no kernel, and that on the zero mode it is the Morse operator
`M ζ = ζ' - J dX_H(γ) ζ` on `W^{1,2}(ℝ, V)`, so that `D` and `M` have the same kernel.

* **The coefficients.** For a constant `J` the coefficient field of `D` on jets is that of
  `∂s + J ∂t - J dX_H(u)` (`TauCeti.SymplecticForm.floerJetCoeff_const_eq`). Along `γ` it does not
  depend on `t`, and it is essentially bounded on the cylinder as soon as `dX_H` is bounded along
  `γ` (`TauCeti.SymplecticForm.memLp_floerJetCoeff_const_comp_fst`).
* **Commuting with the slice average.** Hence `D` commutes with the slice average, the projection
  `TauCeti.CylinderSobolev.sliceAverageL` onto the zero mode
  (`TauCeti.SymplecticForm.floerSobolevOperator_sliceAverageL`).
* **The gap on the nonzero modes.** On the complement of the zero mode `D` is bounded below:
  `(2π - a)² ‖x - P x‖² ≤ ((2π)² + 1) ‖D (x - P x)‖²` for every `x ∈ W^{1,2}` and its slice average
  `P x`
  (`TauCeti.SymplecticForm.mul_sq_norm_sub_sliceAverageL_le_mul_sq_norm_floerSobolevOperator`). On
  test sections this is the estimate of Wirtinger's inequality on the slices,
  `TauCeti.SymplecticForm.mul_setIntegral_norm_sq_le_setIntegral_norm_floerLinearization_sq`, with
  its counterpart for the derivatives; it extends to `W^{1,2}` because the slice average maps the
  jet of a test section `ξ` to the jet of the test section `ξbar`, and the jets of test sections are
  dense.
* **The kernel lies in the zero mode.** Consequently every element of the kernel of `D` on
  `W^{1,2}` is its own slice average, a section that does not depend on `t`
  (`TauCeti.SymplecticForm.sliceAverageL_eq_self_of_floerSobolevOperator_eq_zero`), whatever the
  regularity of the element.
* **The zero mode is the Morse operator.** The zero mode of `W^{1,2}(ℝ × S¹, V)` is the image of
  `W^{1,2}(ℝ, V)` under `TauCeti.CylinderSobolev.zeroModeL`, which reads a path `ζ` as the section
  `(s, t) ↦ ζ(s)`. For `A` the `L∞` class of `s ↦ -J dX_H(γ(s))`, `D` maps the zero mode of `ζ` to
  the zero mode of `M ζ`, where `M = TauCeti.WeakDerivStep.trajectoryOperator A` is the Morse
  operator (`TauCeti.SymplecticForm.floerSobolevOperator_zeroModeL`).
* **The kernels agree.** Hence the kernel of `D` is the image of the kernel of `M` under the zero
  mode (`TauCeti.SymplecticForm.ker_floerSobolevOperator_eq_map_zeroModeL`). So the two kernels
  have the same dimension, and `D` is injective exactly when `M` is
  (`finrank_ker_floerSobolevOperator_eq_finrank_ker_trajectoryOperator` and
  `injective_floerSobolevOperator_iff_injective_trajectoryOperator`, in the namespace
  `TauCeti.SymplecticForm`).

The kernel statements are the `W^{1,2}` analogue of
`TauCeti.SymplecticForm.forall_floerLinearization_comp_fst_eq_zero_iff`: kernel elements that lie in
`W^{1,2}` do not depend on `t` and solve the Morse equation, without that theorem's hypotheses on
the second derivative of `X_H` and on `γ'`. They do not imply it, since it covers every bounded
periodic `C²` kernel element; bounded kernel elements that are not square integrable on the
cylinder, such as nonzero ones that do not decay in `s`, are not treated here. The cokernels of
`D` and `M`, and hence their Fredholm properties and indices, are compared in
`TauCeti.Geometry.Symplectic.Floer.TimeIndependent.Index`.

## References

* A. Floer, *Witten's complex and infinite dimensional Morse theory*, J. Differential Geom.
  **30** (1989), 207–221.
* D. Salamon and E. Zehnder, *Morse theory for periodic solutions of Hamiltonian systems and the
  Maslov index*, Comm. Pure Appl. Math. **45** (1992), 1303–1360, on the linearized operator at
  time-independent solutions of a small Hamiltonian.
-/

public section

open Real Set MeasureTheory ContinuousLinearMap
open TauCeti.StripSobolev TauCeti.CylinderSobolev
open scoped RealInnerProductSpace ENNReal

namespace TauCeti.SymplecticForm

section Coefficients

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {ω : SymplecticForm V} {J : AlmostComplexStructure V} {H : V → ℝ} {γ : ℝ → V}

/-- Along a time-independent cylinder `(s, t) ↦ γ(s)` the coefficient field of the linearized
operator does not depend on `t`. -/
theorem floerJetCoeff_const_comp_fst_mk (ω : SymplecticForm V) (J : AlmostComplexStructure V)
    (H : V → ℝ) (γ : ℝ → V) (s t : ℝ) :
    ω.floerJetCoeff (fun _ _ ↦ J.toLinearMap.toContinuousLinearMap) (fun _ _ ↦ 0) (fun _ ↦ H)
        (fun z ↦ γ z.1) (s, t) =
      ω.floerJetCoeff (fun _ _ ↦ J.toLinearMap.toContinuousLinearMap) (fun _ _ ↦ 0) (fun _ ↦ H)
        (fun z ↦ γ z.1) (s, 0) := by
  rw [floerJetCoeff_const_eq, floerJetCoeff_const_eq]

/-- Along a continuous curve `γ` on which `dX_H` is bounded, the coefficient field of the
linearized operator of a `C²` autonomous Hamiltonian is essentially bounded on the cylinder. -/
theorem memLp_floerJetCoeff_const_comp_fst (hH : ContDiff ℝ 2 H) (hγ : Continuous γ) {a : ℝ}
    (haγ : ∀ s, ‖fderiv ℝ (ω.hamiltonianVectorField H) (γ s)‖ ≤ a) :
    MemLp (ω.floerJetCoeff (fun _ _ ↦ J.toLinearMap.toContinuousLinearMap) (fun _ _ ↦ 0)
      (fun _ ↦ H) (fun z ↦ γ z.1)) ∞ stripMeasure := by
  set Jc : V →L[ℝ] V := J.toLinearMap.toContinuousLinearMap
  have hX : Continuous (fderiv ℝ (ω.hamiltonianVectorField H)) :=
    (ω.contDiff_hamiltonianVectorField (n := 1) hH).continuous_fderiv one_ne_zero
  have hC : Continuous fun z : ℝ × ℝ ↦ -(Jc.comp (fderiv ℝ (ω.hamiltonianVectorField H) (γ z.1))) :=
    (continuous_const.clm_comp (hX.comp (hγ.comp continuous_fst))).neg
  have hcont : Continuous (ω.floerJetCoeff (fun _ _ ↦ Jc) (fun _ _ ↦ 0) (fun _ ↦ H)
      (fun z ↦ γ z.1)) := by
    rw [funext (floerJetCoeff_const_eq ω J H (fun z ↦ γ z.1))]
    exact continuous_iff_continuousAt.2 fun z ↦
      continuousAt_firstOrderJetCoeff continuousAt_const hC.continuousAt
  refine memLp_top_of_bound hcont.aestronglyMeasurable (1 + ‖Jc‖ + ‖Jc‖ * a)
    (.of_forall fun z ↦ ?_)
  rw [floerJetCoeff_const_eq]
  refine (norm_firstOrderJetCoeff_le _ _).trans ?_
  rw [norm_neg]
  gcongr
  exact (opNorm_comp_le _ _).trans (mul_le_mul_of_nonneg_left (haγ z.1) (norm_nonneg _))

/-- **The linearized operator commutes with the slice average.** Along a time-independent cylinder
`(s, t) ↦ γ(s)`, the Sobolev realization of the linearized operator of an autonomous Hamiltonian for
a constant `J` commutes with the projection onto the zero Fourier mode. -/
theorem floerSobolevOperator_sliceAverageL (ω : SymplecticForm V) (J : AlmostComplexStructure V)
    (H : V → ℝ) (γ : ℝ → V) (x : H1 V) :
    ω.floerSobolevOperator (fun _ _ ↦ J.toLinearMap.toContinuousLinearMap) (fun _ _ ↦ 0)
        (fun _ ↦ H) (fun z ↦ γ z.1) (sliceAverageL x) =
      sliceAverageLp (ω.floerSobolevOperator (fun _ _ ↦ J.toLinearMap.toContinuousLinearMap)
        (fun _ _ ↦ 0) (fun _ ↦ H) (fun z ↦ γ z.1) x) := by
  rw [floerSobolevOperator_def, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    Submodule.subtypeL_apply, Submodule.subtypeL_apply, coe_sliceAverageL,
    sliceAverageLp_jetOperator (floerJetCoeff_const_comp_fst_mk ω J H γ)]

/-- **The zero mode of the linearized operator is the Morse operator.** Let `H` be a `C²`
autonomous Hamiltonian and `γ` a continuous curve along which `dX_H` is bounded, and let `A` be the
`L∞` class of `s ↦ -J dX_H(γ(s))`. The Sobolev realization of the linearized operator along the
time-independent cylinder `(s, t) ↦ γ(s)` maps the zero mode of a path `ζ ∈ W^{1,2}(ℝ, V)` to the
zero mode of `M ζ = ζ' - J dX_H(γ) ζ`, the trajectory operator
`TauCeti.WeakDerivStep.trajectoryOperator A`. -/
theorem floerSobolevOperator_zeroModeL
    {A : Lp (V →L[ℝ] V) ∞ (volume.restrict ((⊤ : TopologicalSpace.Opens ℝ) : Set ℝ))}
    (hH : ContDiff ℝ 2 H) (hγ : Continuous γ) {a : ℝ}
    (haγ : ∀ s, ‖fderiv ℝ (ω.hamiltonianVectorField H) (γ s)‖ ≤ a)
    (hA : ⇑A =ᵐ[volume.restrict ((⊤ : TopologicalSpace.Opens ℝ) : Set ℝ)]
      fun s ↦ -(J.toLinearMap.toContinuousLinearMap.comp
        (fderiv ℝ (ω.hamiltonianVectorField H) (γ s))))
    (u : WeakDerivStep volume ⊤ 2 (ContinuousLinearMap.id ℝ
      (Lp V 2 (volume.restrict ((⊤ : TopologicalSpace.Opens ℝ) : Set ℝ))))) :
    ω.floerSobolevOperator (fun _ _ ↦ J.toLinearMap.toContinuousLinearMap) (fun _ _ ↦ 0)
        (fun _ ↦ H) (fun z ↦ γ z.1) (zeroModeL V u) =
      zeroModeLp V (WeakDerivStep.trajectoryOperator A u) := by
  have hpull := measurePreserving_fst_stripMeasure.quasiMeasurePreserving
  refine Lp.ext ?_
  filter_upwards [coeFn_floerSobolevOperator ω (memLp_floerJetCoeff_const_comp_fst hH hγ haγ)
      (zeroModeL V u), coeFn_zeroModeL u, coeFn_zeroModeLp (WeakDerivStep.trajectoryOperator A u),
    hpull.ae_eq_comp (WeakDerivStep.trajectoryOperator_apply_ae A u), hpull.ae_eq_comp hA]
    with z h₁ h₂ h₃ h₄ h₅
  simp only [Function.comp_apply] at h₄ h₅
  rw [h₁, h₂, h₃, h₄, h₅, floerJetCoeff_const_eq, firstOrderJetCoeff_apply, map_zero, add_zero]

end Coefficients

section Gap

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {ω : SymplecticForm V} {J : AlmostComplexStructure V} {H : V → ℝ} {γ : ℝ → V}

/-- On the jet of a test section `η` vanishing for `|s| ≥ R`, the squared norm of the Sobolev
realization of `D` is the integral of `‖D η‖²` over the rectangle `[-R, R] × [0, 1]`. -/
private theorem sq_norm_floerSobolevOperator_jetLp_eq_setIntegral (hH : ContDiff ℝ 2 H)
    (hγ : Continuous γ) {a : ℝ} (haγ : ∀ s, ‖fderiv ℝ (ω.hamiltonianVectorField H) (γ s)‖ ≤ a)
    (η : testSection V) {R : ℝ} (hR : ∀ s t, R ≤ |s| → (η : ℝ × ℝ → V) (s, t) = 0) :
    ‖ω.floerSobolevOperator (fun _ _ ↦ J.toLinearMap.toContinuousLinearMap) (fun _ _ ↦ 0)
        (fun _ ↦ H) (fun z ↦ γ z.1) ⟨jetLp (testSection V) η, jetLp_mem_jetClosure η⟩‖ ^ 2 =
      ∫ z in Icc (-R) R ×ˢ Icc 0 1, ‖ω.floerLinearization
        (fun _ _ ↦ J.toLinearMap.toContinuousLinearMap) (fun _ _ ↦ 0) (fun _ ↦ H)
        (fun z ↦ γ z.1) η z‖ ^ 2 := by
  rw [← Lp.integral_norm_sq_eq_norm_sq, integral_congr_ae (g := fun z ↦ ‖ω.floerLinearization
      (fun _ _ ↦ J.toLinearMap.toContinuousLinearMap) (fun _ _ ↦ 0) (fun _ ↦ H)
      (fun z ↦ γ z.1) η z‖ ^ 2) (by
    filter_upwards [floerSobolevOperator_jetLp_ae_eq ω
      (memLp_floerJetCoeff_const_comp_fst hH hγ haγ) η] with z hz
    rw [hz])]
  refine integral_strip_eq_setIntegral_of_jet_eq_zero hR fun z hz ↦ ?_
  simp only [jet_apply, Prod.mk_eq_zero] at hz
  simp [floerLinearization_const_eq, hz.1, hz.2.1, hz.2.2]

/-- The gap on the nonzero modes for the jet of a test section whose slices have mean zero. -/
private theorem mul_sq_norm_jetLp_le_of_forall_intervalIntegral_eq_zero
    (hg : ∀ v w, ω v (J w) = ⟪v, w⟫) (hH : ContDiff ℝ 2 H) (hγ : Continuous γ) {a : ℝ}
    (ha : a ≤ 2 * π) (haγ : ∀ s, ‖fderiv ℝ (ω.hamiltonianVectorField H) (γ s)‖ ≤ a)
    (η : testSection V) (hmean : ∀ s, ∫ t in (0 : ℝ)..1, (η : ℝ × ℝ → V) (s, t) = 0) :
    (2 * π - a) ^ 2 * ‖jetLp (testSection V) η‖ ^ 2 ≤
      ((2 * π) ^ 2 + 1) * ‖ω.floerSobolevOperator (fun _ _ ↦ J.toLinearMap.toContinuousLinearMap)
        (fun _ _ ↦ 0) (fun _ ↦ H) (fun z ↦ γ z.1)
        ⟨jetLp (testSection V) η, jetLp_mem_jetClosure η⟩‖ ^ 2 := by
  obtain ⟨hη2, hηp, R, hR⟩ := mem_testSection_iff.1 η.property
  have hη1 : ContDiff ℝ 1 (η : ℝ × ℝ → V) := hη2.of_le one_le_two
  set R₀ := max R 0
  have hR₀ : ∀ s t, R₀ ≤ |s| → (η : ℝ × ℝ → V) (s, t) = 0 :=
    fun s t hs ↦ hR s t ((le_max_left _ _).trans hs)
  have hs : -R₀ ≤ R₀ := by linarith [le_max_right R 0]
  have h₀ : ∀ t, (η : ℝ × ℝ → V) (-R₀, t) = 0 :=
    fun t ↦ hR₀ _ t (by rw [abs_neg, abs_of_nonneg (le_max_right _ _)])
  have h₁ : ∀ t, (η : ℝ × ℝ → V) (R₀, t) = 0 :=
    fun t ↦ hR₀ _ t (abs_of_nonneg (le_max_right _ _)).ge
  have hA := mul_setIntegral_norm_sq_le_setIntegral_norm_floerLinearization_sq hg hH hγ ha
    (fun s _ ↦ haγ s) hη2 hηp hmean hs h₀ h₁
  have hB := mul_setIntegral_norm_fderiv_sq_add_le_setIntegral_norm_floerLinearization_sq hg hH hγ
    ha (fun s _ ↦ haγ s) hη2 hηp hmean hs h₀ h₁
  -- The squared norm of the jet is at most the `W^{1,2}` energy over the rectangle.
  have hJ := sq_norm_jetLp_le_setIntegral hη1 hR₀
  have hd := hη1.continuous_fderiv one_ne_zero
  have hi₁ : IntegrableOn (fun z ↦ ‖fderiv ℝ (η : ℝ × ℝ → V) z (1, 0)‖ ^ 2 +
      ‖fderiv ℝ (η : ℝ × ℝ → V) z (0, 1)‖ ^ 2) (Icc (-R₀) R₀ ×ˢ Icc 0 1) :=
    (((hd.clm_apply continuous_const).norm.pow 2).add
      ((hd.clm_apply continuous_const).norm.pow 2)).integrableOn_Icc_prod_Icc
  have hi₂ : IntegrableOn (fun z ↦ ‖(η : ℝ × ℝ → V) z‖ ^ 2) (Icc (-R₀) R₀ ×ˢ Icc 0 1) :=
    (hη1.continuous.norm.pow 2).integrableOn_Icc_prod_Icc
  rw [integral_add hi₁ hi₂] at hJ
  -- The squared norm of `D` on the jet is the integral of `‖D η‖²` over the rectangle.
  rw [sq_norm_floerSobolevOperator_jetLp_eq_setIntegral hH hγ haγ η hR₀]
  have hpos : 0 ≤ (2 * π - a) ^ 2 := sq_nonneg _
  nlinarith [mul_le_mul_of_nonneg_left hJ hpos]

/-- **The gap on the nonzero modes on `W^{1,2}`.** Let the inner product of `V` be the metric
`ω(·, J ·)`, let `H` be a `C²` autonomous Hamiltonian and `γ` a continuous curve with
`‖dX_H(γ(s))‖ ≤ a ≤ 2π` for every `s`. Then the Sobolev realization `D` of the linearized operator
along `(s, t) ↦ γ(s)` satisfies `(2π - a)² ‖x - P x‖² ≤ ((2π)² + 1) ‖D (x - P x)‖²` for every
`x ∈ W^{1,2}(ℝ × S¹, V)`, where `P x` is the slice average of `x`. -/
theorem mul_sq_norm_sub_sliceAverageL_le_mul_sq_norm_floerSobolevOperator
    (hg : ∀ v w, ω v (J w) = ⟪v, w⟫) (hH : ContDiff ℝ 2 H) (hγ : Continuous γ) {a : ℝ}
    (ha : a ≤ 2 * π) (haγ : ∀ s, ‖fderiv ℝ (ω.hamiltonianVectorField H) (γ s)‖ ≤ a) (x : H1 V) :
    (2 * π - a) ^ 2 * ‖x - sliceAverageL x‖ ^ 2 ≤
      ((2 * π) ^ 2 + 1) * ‖ω.floerSobolevOperator (fun _ _ ↦ J.toLinearMap.toContinuousLinearMap)
        (fun _ _ ↦ 0) (fun _ ↦ H) (fun z ↦ γ z.1) (x - sliceAverageL x)‖ ^ 2 := by
  set D := ω.floerSobolevOperator (fun _ _ ↦ J.toLinearMap.toContinuousLinearMap) (fun _ _ ↦ 0)
    (fun _ ↦ H) (fun z ↦ γ z.1)
  have hcl : IsClosed {y : H1 V | (2 * π - a) ^ 2 * ‖y - sliceAverageL y‖ ^ 2 ≤
      ((2 * π) ^ 2 + 1) * ‖D (y - sliceAverageL y)‖ ^ 2} :=
    isClosed_le (continuous_const.mul ((continuous_id.sub sliceAverageL.continuous).norm.pow 2))
      (continuous_const.mul ((D.continuous.comp
        (continuous_id.sub sliceAverageL.continuous)).norm.pow 2))
  refine (denseRange_codRestrict_jetLp (testSection V)).induction_on x hcl fun ξ ↦ ?_
  -- On the jet of a test section `ξ`, `x - P x` is the jet of the test section `ξ - ξbar`.
  set η : testSection V := ξ - ⟨sliceAverage ξ, sliceAverage_mem_testSection ξ.property⟩
  have hx : (jetLp (testSection V)).codRestrict (H1 V) jetLp_mem_jetClosure ξ -
      sliceAverageL ((jetLp (testSection V)).codRestrict (H1 V) jetLp_mem_jetClosure ξ) =
        ⟨jetLp (testSection V) η, jetLp_mem_jetClosure η⟩ := by
    refine Subtype.ext ?_
    rw [Submodule.coe_sub, coe_sliceAverageL, LinearMap.codRestrict_apply, sliceAverageLp_jetLp]
    simp [η, map_sub]
  have hmean : ∀ s, ∫ t in (0 : ℝ)..1, (η : ℝ × ℝ → V) (s, t) = 0 := fun s ↦ by
    have hint : IntervalIntegrable (fun t ↦ (ξ : ℝ × ℝ → V) (s, t)) volume 0 1 :=
      ((mem_testSection_iff.1 ξ.property).1.continuous.comp (.prodMk_right s)).intervalIntegrable
        0 1
    rw [← sliceAverage_sub_sliceAverage (z := (s, 0)) hint, sliceAverage_apply]
    simp [η]
  simp only [hx]
  rw [← Submodule.norm_coe]
  exact mul_sq_norm_jetLp_le_of_forall_intervalIntegral_eq_zero hg hH hγ ha haγ η hmean

/-- **The nonzero modes are bounded below.** Under the hypotheses of
`TauCeti.SymplecticForm.mul_sq_norm_sub_sliceAverageL_le_mul_sq_norm_floerSobolevOperator`, an
element `x` of `W^{1,2}(ℝ × S¹, V)` whose slice average vanishes satisfies
`(2π - a)² ‖x‖² ≤ ((2π)² + 1) ‖D x‖²`. -/
theorem mul_sq_norm_le_mul_sq_norm_floerSobolevOperator_of_sliceAverageL_eq_zero
    (hg : ∀ v w, ω v (J w) = ⟪v, w⟫) (hH : ContDiff ℝ 2 H) (hγ : Continuous γ) {a : ℝ}
    (ha : a ≤ 2 * π) (haγ : ∀ s, ‖fderiv ℝ (ω.hamiltonianVectorField H) (γ s)‖ ≤ a) {x : H1 V}
    (hx : sliceAverageL x = 0) :
    (2 * π - a) ^ 2 * ‖x‖ ^ 2 ≤
      ((2 * π) ^ 2 + 1) * ‖ω.floerSobolevOperator (fun _ _ ↦ J.toLinearMap.toContinuousLinearMap)
        (fun _ _ ↦ 0) (fun _ ↦ H) (fun z ↦ γ z.1) x‖ ^ 2 := by
  simpa [hx] using
    mul_sq_norm_sub_sliceAverageL_le_mul_sq_norm_floerSobolevOperator hg hH hγ ha haγ x

/-- **The kernel lies in the zero mode.** Let the inner product of `V` be the metric `ω(·, J ·)`,
let `H` be a `C²` autonomous Hamiltonian and `γ` a continuous curve with
`‖dX_H(γ(s))‖ ≤ a < 2π` for every `s`. Every element `x` of `W^{1,2}(ℝ × S¹, V)` in the kernel of
the Sobolev realization of the linearized operator along `(s, t) ↦ γ(s)` is its own slice average:
it does not depend on `t`. -/
theorem sliceAverageL_eq_self_of_floerSobolevOperator_eq_zero (hg : ∀ v w, ω v (J w) = ⟪v, w⟫)
    (hH : ContDiff ℝ 2 H) (hγ : Continuous γ) {a : ℝ} (ha : a < 2 * π)
    (haγ : ∀ s, ‖fderiv ℝ (ω.hamiltonianVectorField H) (γ s)‖ ≤ a) {x : H1 V}
    (hx : ω.floerSobolevOperator (fun _ _ ↦ J.toLinearMap.toContinuousLinearMap) (fun _ _ ↦ 0)
      (fun _ ↦ H) (fun z ↦ γ z.1) x = 0) :
    sliceAverageL x = x := by
  have hD : ω.floerSobolevOperator (fun _ _ ↦ J.toLinearMap.toContinuousLinearMap) (fun _ _ ↦ 0)
      (fun _ ↦ H) (fun z ↦ γ z.1) (x - sliceAverageL x) = 0 := by
    rw [map_sub, floerSobolevOperator_sliceAverageL, hx, map_zero, sub_zero]
  have h := mul_sq_norm_sub_sliceAverageL_le_mul_sq_norm_floerSobolevOperator hg hH hγ ha.le haγ x
  rw [hD, norm_zero] at h
  have hpos : 0 < (2 * π - a) ^ 2 := pow_pos (sub_pos.2 ha) 2
  have h0 : ‖x - sliceAverageL x‖ ^ 2 ≤ 0 := by nlinarith
  rw [eq_comm, ← sub_eq_zero, ← norm_eq_zero]
  exact pow_eq_zero_iff two_ne_zero |>.1 (le_antisymm h0 (sq_nonneg _))

end Gap

section ZeroMode

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {ω : SymplecticForm V} {J : AlmostComplexStructure V} {H : V → ℝ} {γ : ℝ → V}
  {A : Lp (V →L[ℝ] V) ∞ (volume.restrict ((⊤ : TopologicalSpace.Opens ℝ) : Set ℝ))}

/-- **The kernel of the linearized operator is the kernel of the Morse operator.** Let the inner
product of `V` be the metric `ω(·, J ·)`, let `H` be a `C²` autonomous Hamiltonian and `γ` a
continuous curve with `‖dX_H(γ(s))‖ ≤ a < 2π` for every `s`, and let `A` be the `L∞` class of
`s ↦ -J dX_H(γ(s))`. The kernel of the Sobolev realization of the linearized operator along the
time-independent cylinder `(s, t) ↦ γ(s)` on `W^{1,2}(ℝ × S¹, V)` is the image under the zero mode
of the kernel of the Morse operator `ζ ↦ ζ' - J dX_H(γ) ζ` on `W^{1,2}(ℝ, V)`. -/
theorem ker_floerSobolevOperator_eq_map_zeroModeL (hg : ∀ v w, ω v (J w) = ⟪v, w⟫)
    (hH : ContDiff ℝ 2 H) (hγ : Continuous γ) {a : ℝ} (ha : a < 2 * π)
    (haγ : ∀ s, ‖fderiv ℝ (ω.hamiltonianVectorField H) (γ s)‖ ≤ a)
    (hA : ⇑A =ᵐ[volume.restrict ((⊤ : TopologicalSpace.Opens ℝ) : Set ℝ)]
      fun s ↦ -(J.toLinearMap.toContinuousLinearMap.comp
        (fderiv ℝ (ω.hamiltonianVectorField H) (γ s)))) :
    (ω.floerSobolevOperator (fun _ _ ↦ J.toLinearMap.toContinuousLinearMap) (fun _ _ ↦ 0)
        (fun _ ↦ H) (fun z ↦ γ z.1)).ker =
      (WeakDerivStep.trajectoryOperator (p := 2) A).ker.map (zeroModeL V).toLinearMap := by
  ext x
  simp only [LinearMap.mem_ker, Submodule.mem_map, ContinuousLinearMap.coe_coe]
  constructor
  · intro hx
    obtain ⟨u, rfl⟩ := sliceAverageL_eq_self_iff.1
      (sliceAverageL_eq_self_of_floerSobolevOperator_eq_zero hg hH hγ ha haγ hx)
    rw [floerSobolevOperator_zeroModeL hH hγ haγ hA] at hx
    exact ⟨u, (zeroModeLp V).injective (by rw [hx, map_zero]), rfl⟩
  · rintro ⟨u, hu, rfl⟩
    rw [floerSobolevOperator_zeroModeL hH hγ haγ hA, hu, map_zero]

/-- Under the hypotheses of
`TauCeti.SymplecticForm.ker_floerSobolevOperator_eq_map_zeroModeL`, the kernels of the linearized
operator along `(s, t) ↦ γ(s)` and of the Morse operator `ζ ↦ ζ' - J dX_H(γ) ζ` have the same
dimension. -/
theorem finrank_ker_floerSobolevOperator_eq_finrank_ker_trajectoryOperator
    (hg : ∀ v w, ω v (J w) = ⟪v, w⟫)
    (hH : ContDiff ℝ 2 H) (hγ : Continuous γ) {a : ℝ} (ha : a < 2 * π)
    (haγ : ∀ s, ‖fderiv ℝ (ω.hamiltonianVectorField H) (γ s)‖ ≤ a)
    (hA : ⇑A =ᵐ[volume.restrict ((⊤ : TopologicalSpace.Opens ℝ) : Set ℝ)]
      fun s ↦ -(J.toLinearMap.toContinuousLinearMap.comp
        (fderiv ℝ (ω.hamiltonianVectorField H) (γ s)))) :
    Module.finrank ℝ (ω.floerSobolevOperator (fun _ _ ↦ J.toLinearMap.toContinuousLinearMap)
        (fun _ _ ↦ 0) (fun _ ↦ H) (fun z ↦ γ z.1)).ker =
      Module.finrank ℝ (WeakDerivStep.trajectoryOperator (p := 2) A).ker := by
  rw [ker_floerSobolevOperator_eq_map_zeroModeL hg hH hγ ha haγ hA]
  exact (Submodule.equivMapOfInjective _ zeroModeL_injective _).finrank_eq.symm

/-- Under the hypotheses of
`TauCeti.SymplecticForm.ker_floerSobolevOperator_eq_map_zeroModeL`, the linearized operator along
`(s, t) ↦ γ(s)` is injective on `W^{1,2}(ℝ × S¹, V)` exactly when the Morse operator
`ζ ↦ ζ' - J dX_H(γ) ζ` is injective on `W^{1,2}(ℝ, V)`. -/
theorem injective_floerSobolevOperator_iff_injective_trajectoryOperator
    (hg : ∀ v w, ω v (J w) = ⟪v, w⟫)
    (hH : ContDiff ℝ 2 H) (hγ : Continuous γ) {a : ℝ} (ha : a < 2 * π)
    (haγ : ∀ s, ‖fderiv ℝ (ω.hamiltonianVectorField H) (γ s)‖ ≤ a)
    (hA : ⇑A =ᵐ[volume.restrict ((⊤ : TopologicalSpace.Opens ℝ) : Set ℝ)]
      fun s ↦ -(J.toLinearMap.toContinuousLinearMap.comp
        (fderiv ℝ (ω.hamiltonianVectorField H) (γ s)))) :
    Function.Injective (ω.floerSobolevOperator (fun _ _ ↦ J.toLinearMap.toContinuousLinearMap)
        (fun _ _ ↦ 0) (fun _ ↦ H) (fun z ↦ γ z.1)) ↔
      Function.Injective (WeakDerivStep.trajectoryOperator (p := 2) A) := by
  rw [← ContinuousLinearMap.coe_coe, ← LinearMap.ker_eq_bot,
    ker_floerSobolevOperator_eq_map_zeroModeL hg hH hγ ha haγ hA,
    ← Submodule.map_bot (zeroModeL V).toLinearMap,
    (Submodule.map_injective_of_injective zeroModeL_injective).eq_iff, LinearMap.ker_eq_bot,
    ContinuousLinearMap.coe_coe]

end ZeroMode

end TauCeti.SymplecticForm
