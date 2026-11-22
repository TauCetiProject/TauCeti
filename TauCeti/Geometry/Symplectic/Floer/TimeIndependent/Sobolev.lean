/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Cylinder.SliceAverage
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
`s`, the realization splits along the zero Fourier mode, on which it is the Morse operator
`ζ ↦ ζ' - J dX_H(γ) ζ`, and that the other modes carry no kernel.

* **The coefficients.** For a constant `J` the coefficient field of `D` on jets is that of
  `∂s + J ∂t - J dX_H(u)` (`TauCeti.SymplecticForm.floerJetCoeff_const_eq`). Along `γ` it does not
  depend on `t`, and it is essentially bounded on the cylinder as soon as `dX_H` is bounded along
  `γ` (`TauCeti.SymplecticForm.memLp_floerJetCoeff_const_comp_fst`).
* **Commuting with the slice average.** Hence `D` commutes with the slice average, the projection
  `TauCeti.CylinderSobolev.sliceAverageL` onto the zero mode
  (`TauCeti.SymplecticForm.floerSobolevOperator_sliceAverageL`).
* **The gap on the nonzero modes.** On the complement of the zero mode `D` is bounded below:
  `(2π - a)² ‖x - P x‖² ≤ ((2π)² + 1) ‖D (x - P x)‖²` for every `x ∈ W^{1,2}` and its slice average
  `P x` (`TauCeti.SymplecticForm.sq_norm_sub_sliceAverageL_le`). On test sections this is the
  estimate of Wirtinger's inequality on the slices,
  `TauCeti.SymplecticForm.mul_setIntegral_norm_sq_le_setIntegral_norm_floerLinearization_sq`, with
  its counterpart for the derivatives; it extends to
  `W^{1,2}` because the slice average maps the jet of a test section `ξ` to the jet of the test
  section `ξbar`, and the jets of test sections are dense.
* **The kernel lies in the zero mode.** Consequently every element of the kernel of `D` on
  `W^{1,2}` is its own slice average, a section that does not depend on `t`
  (`TauCeti.SymplecticForm.sliceAverageL_eq_self_of_floerSobolevOperator_eq_zero`), whatever the
  regularity of the element.

This is the Sobolev counterpart of the classical statement
`TauCeti.SymplecticForm.forall_floerLinearization_comp_fst_eq_zero_iff`, without its hypotheses on
the second derivative of `X_H` and on `γ'`: the kernel of `D` is carried by its zero Fourier mode,
the Morse operator. The cokernel, and the identification of the zero mode with the Morse operator on
`W^{1,2}(ℝ, V)`, are not treated here.

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

/-- **The coefficients of the linearized operator for a constant almost complex structure.** For a
constant `J`, the perturbation `K = H dt` of an autonomous Hamiltonian and any map `u`, the
coefficient field of the linearized Floer operator on jets is that of `∂s + J ∂t - J dX_H(u)`. -/
theorem floerJetCoeff_const_eq (ω : SymplecticForm V) (J : AlmostComplexStructure V)
    (H : V → ℝ) (u : ℝ × ℝ → V) (z : ℝ × ℝ) :
    ω.floerJetCoeff (fun _ _ ↦ J.toLinearMap.toContinuousLinearMap) (fun _ _ ↦ 0) (fun _ ↦ H) u z =
      firstOrderJetCoeff J.toLinearMap.toContinuousLinearMap
        (-(J.toLinearMap.toContinuousLinearMap.comp
          (fderiv ℝ (ω.hamiltonianVectorField H) (u z)))) := by
  rw [floerJetCoeff_def]
  congr 1
  ext v
  simp [floerLinearizationCoeff_apply, hamiltonianVectorField_const]

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

end Coefficients

section Gap

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {ω : SymplecticForm V} {J : AlmostComplexStructure V} {H : V → ℝ} {γ : ℝ → V}

/-- A function on the plane vanishing for `|s| > R` has the same integral for the strip measure as
over the rectangle `[-R, R] × [0, 1]`. -/
private theorem integral_stripMeasure_eq_setIntegral {g : ℝ × ℝ → ℝ} {R : ℝ}
    (hg : ∀ z : ℝ × ℝ, R < |z.1| → g z = 0) :
    ∫ z, g z ∂stripMeasure = ∫ z in Icc (-R) R ×ˢ Icc 0 1, g z :=
  setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (MeasurableSet.univ.prod measurableSet_Icc)
    (prod_mono (subset_univ _) subset_rfl) fun z hz ↦ hg z (by
      have h : z.1 ∉ Icc (-R) R := fun h ↦ hz.2 ⟨h, hz.1.2⟩
      rwa [mem_Icc, ← abs_le, not_le] at h)

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
  refine integral_stripMeasure_eq_setIntegral fun z hz ↦ ?_
  have h := jet_eq_zero_of_lt_abs hR hz
  simp only [jet_apply, Prod.mk_eq_zero] at h
  simp [floerLinearization_const_eq, h.1, h.2.1, h.2.2]

/-- The gap on the nonzero modes for the jet of a test section whose slices have mean zero. -/
private theorem sq_norm_jetLp_le_of_forall_intervalIntegral_eq_zero
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
  have hc : ∀ z : ℝ × ℝ, R₀ < |z.1| → (η : ℝ × ℝ → V) z = 0 ∧
      fderiv ℝ (η : ℝ × ℝ → V) z (1, 0) = 0 ∧ fderiv ℝ (η : ℝ × ℝ → V) z (0, 1) = 0 :=
    fun z hz ↦ by simpa [jet_apply] using jet_eq_zero_of_lt_abs hR₀ hz
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
  have hJ := sq_norm_jetLp_le_integral η hη1
  rw [integral_stripMeasure_eq_setIntegral (R := R₀) fun z hz ↦ by
    obtain ⟨e₁, e₂, e₃⟩ := hc z hz
    simp [e₁, e₂, e₃]] at hJ
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
theorem sq_norm_sub_sliceAverageL_le (hg : ∀ v w, ω v (J w) = ⟪v, w⟫) (hH : ContDiff ℝ 2 H)
    (hγ : Continuous γ) {a : ℝ} (ha : a ≤ 2 * π)
    (haγ : ∀ s, ‖fderiv ℝ (ω.hamiltonianVectorField H) (γ s)‖ ≤ a) (x : H1 V) :
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
    have hfun : (fun t ↦ (η : ℝ × ℝ → V) (s, t)) =
        fun t ↦ (ξ : ℝ × ℝ → V) (s, t) - sliceAverage ξ (s, 0) :=
      funext fun t ↦ by simp [η, sliceAverage_mk _ s t]
    rw [hfun, intervalIntegral.integral_sub hint intervalIntegrable_const,
      intervalIntegral.integral_const, sub_zero, one_smul, sliceAverage_apply, sub_self]
  simp only [hx]
  rw [← Submodule.norm_coe]
  exact sq_norm_jetLp_le_of_forall_intervalIntegral_eq_zero hg hH hγ ha haγ η hmean

/-- **The nonzero modes are bounded below.** Under the hypotheses of
`TauCeti.SymplecticForm.sq_norm_sub_sliceAverageL_le`, an element `x` of `W^{1,2}(ℝ × S¹, V)` whose
slice average vanishes satisfies `(2π - a)² ‖x‖² ≤ ((2π)² + 1) ‖D x‖²`. -/
theorem sq_norm_le_of_sliceAverageL_eq_zero (hg : ∀ v w, ω v (J w) = ⟪v, w⟫)
    (hH : ContDiff ℝ 2 H) (hγ : Continuous γ) {a : ℝ} (ha : a ≤ 2 * π)
    (haγ : ∀ s, ‖fderiv ℝ (ω.hamiltonianVectorField H) (γ s)‖ ≤ a) {x : H1 V}
    (hx : sliceAverageL x = 0) :
    (2 * π - a) ^ 2 * ‖x‖ ^ 2 ≤
      ((2 * π) ^ 2 + 1) * ‖ω.floerSobolevOperator (fun _ _ ↦ J.toLinearMap.toContinuousLinearMap)
        (fun _ _ ↦ 0) (fun _ ↦ H) (fun z ↦ γ z.1) x‖ ^ 2 := by
  simpa [hx] using sq_norm_sub_sliceAverageL_le hg hH hγ ha haγ x

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
  have h := sq_norm_sub_sliceAverageL_le hg hH hγ ha.le haγ x
  rw [hD, norm_zero] at h
  have hpos : 0 < (2 * π - a) ^ 2 := pow_pos (sub_pos.2 ha) 2
  have h0 : ‖x - sliceAverageL x‖ ^ 2 ≤ 0 := by nlinarith
  rw [eq_comm, ← sub_eq_zero, ← norm_eq_zero]
  exact pow_eq_zero_iff two_ne_zero |>.1 (le_antisymm h0 (sq_nonneg _))

end Gap

end TauCeti.SymplecticForm
