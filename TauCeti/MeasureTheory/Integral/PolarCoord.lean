/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.PolarCoord
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.SpecialFunctions.Complex.CircleMap
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Equiv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.Module
import TauCeti.Analysis.SpecialFunctions.Complex.CircleMap

/-!
# Polar-coordinate derivatives and integration over a closed annulus

The polar-coordinate change of variables for a translated closed annulus is the integral on
`[a, b] × [-π, π]` with radial Jacobian `r`, when `a ≥ 0`; for its closed upper half
`{z | z₀.im ≤ z.im}` it is the integral on `[a, b] × [0, π]`
(`Complex.integral_comp_polarCoord_symm_Icc_zero_pi`). The two angular endpoints have
measure zero, so the closed polar rectangle gives the same integral as the slit-plane chart.
This form of Mathlib's `Complex.integral_comp_polarCoord_symm` is suitable for combining polar
integration with Green's formula on a rectangle, without extending a map across the inner disc.
For a continuous density in a real normed space,
`TauCeti.integral_annulus_eq_integral_circleMap` expresses the same integral as an iterated
integral with the radial variable outermost.

The derivative formulas describe the radial and angular vectors of the inverse complex polar
map. Evaluating the alternating part of a bilinear pairing on those vectors gives its value on
`1` and `Complex.I`, multiplied by the radial Jacobian.
-/

public section

open MeasureTheory Set
open scoped Real

namespace TauCeti

open Complex

/-- The translated inverse complex polar map is smooth, including at zero radius. -/
theorem contDiff_add_polarCoord_symm (z₀ : ℂ) {n : WithTop ℕ∞} :
    ContDiff ℝ n (fun p ↦ z₀ + Complex.polarCoord.symm p) := by
  simp only [Complex.polarCoord_symm_apply, ← Complex.ofRealCLM_apply]
  fun_prop

/-- A polar point whose radius lies in a nonnegative closed interval maps into the annulus. -/
theorem add_polarCoord_symm_mem_annulus (z₀ : ℂ) {a b : ℝ} (ha : 0 ≤ a)
    {p : ℝ × ℝ} (hp : p.1 ∈ Icc a b) :
    z₀ + Complex.polarCoord.symm p ∈ {z : ℂ | a ≤ ‖z - z₀‖ ∧ ‖z - z₀‖ ≤ b} := by
  simpa only [mem_Icc, mem_ofPred_eq, add_sub_cancel_left, Complex.norm_polarCoord_symm,
    abs_of_nonneg (ha.trans hp.1)] using hp

/-- A constant-radius slice of the translated polar map is the circle parametrization. -/
theorem add_polarCoord_symm_eq_circleMap (z₀ : ℂ) (p : ℝ × ℝ) :
    z₀ + Complex.polarCoord.symm p = circleMap z₀ p.1 p.2 := by
  simp [Complex.polarCoord_symm_apply, circleMap, Complex.exp_mul_I]

/-- A polar point of the rectangle `[a, b] × [0, π]`, with `0 ≤ a`, maps into the closed upper
half of the annulus. -/
theorem add_polarCoord_symm_mem_upperHalfAnnulus (z₀ : ℂ) {a b : ℝ} (ha : 0 ≤ a)
    {p : ℝ × ℝ} (hp : p ∈ Icc (a, 0) (b, π)) :
    z₀ + Complex.polarCoord.symm p ∈ {z : ℂ | z₀.im ≤ z.im ∧ a ≤ ‖z - z₀‖ ∧ ‖z - z₀‖ ≤ b} := by
  rw [add_polarCoord_symm_eq_circleMap]
  exact circleMap_mem_upperHalfAnnulus ha ⟨hp.1.1, hp.2.1⟩ ⟨hp.1.2, hp.2.2⟩

/-- A polar point of the open rectangle `(a, b) × (0, π)`, with `0 ≤ a`, maps into the open
upper half-annulus of radii `a` and `b` about `z₀`. -/
theorem add_polarCoord_symm_mem_openUpperHalfAnnulus (z₀ : ℂ) {a b : ℝ} (ha : 0 ≤ a)
    {p : ℝ × ℝ} (hp : p ∈ Ioo a b ×ˢ Ioo 0 π) :
    z₀ + Complex.polarCoord.symm p ∈ {z : ℂ | z₀.im < z.im ∧ a < ‖z - z₀‖ ∧ ‖z - z₀‖ < b} := by
  obtain ⟨⟨hr₁, hr₂⟩, hθ₁, hθ₂⟩ := hp
  have hr : 0 < p.1 := ha.trans_lt hr₁
  rw [mem_ofPred_eq, add_sub_cancel_left, Complex.norm_polarCoord_symm, abs_of_pos hr,
    add_polarCoord_symm_eq_circleMap, circleMap_im, lt_add_iff_pos_right]
  exact ⟨mul_pos hr (Real.sin_pos_of_pos_of_lt_pi hθ₁ hθ₂), hr₁, hr₂⟩

/-- The derivative of the translated inverse complex polar-coordinate map at any `(r, θ)`.
No restriction to the positive-radius chart is needed for this derivative formula. -/
theorem hasFDerivAt_add_polarCoord_symm (p : ℝ × ℝ) (z₀ : ℂ) :
  HasFDerivAt (fun p ↦ z₀ + Complex.polarCoord.symm p)
    (Complex.equivRealProdCLM.symm.toContinuousLinearMap.comp (fderivPolarCoordSymm p)) p := by
  exact (Complex.equivRealProdCLM.symm.hasFDerivAt.comp p
    (hasFDerivAt_polarCoord_symm p)).const_add z₀

/-- The radial derivative of the inverse polar-coordinate map, expressed as a complex number,
is the unit vector at the given angle. -/
theorem equivRealProd_symm_fderivPolarCoordSymm_apply_one_zero (p : ℝ × ℝ) :
    Complex.equivRealProdCLM.symm (fderivPolarCoordSymm p (1, 0)) =
      Complex.exp (p.2 * I) := by
  simp [fderivPolarCoordSymm, Matrix.toLin_finTwoProd_toContinuousLinearMap,
    Complex.equivRealProdCLM_symm_apply, Complex.exp_mul_I]

/-- The angular derivative of the inverse polar-coordinate map, expressed as a complex number,
is the tangent vector to the circle with the given radius and angle. -/
theorem equivRealProd_symm_fderivPolarCoordSymm_apply_zero_one (p : ℝ × ℝ) :
    Complex.equivRealProdCLM.symm (fderivPolarCoordSymm p (0, 1)) =
      circleMap 0 p.1 p.2 * I := by
  simp [fderivPolarCoordSymm, Matrix.toLin_finTwoProd_toContinuousLinearMap,
    Complex.equivRealProdCLM_symm_apply, Complex.exp_mul_I, circleMap]
  ring_nf
  simp [I_sq]

/-- The alternating part of a bilinear map, after a real-linear map `L`, evaluated
on the radial and angular polar-coordinate vectors is the radius times its value on `1` and `I`.
The identity holds for every real radius, including zero and negative radii. -/
theorem _root_.LinearMap.apply_exp_circleMap_sub_swap
    {V W : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
    (B : V →ₗ[ℝ] V →ₗ[ℝ] W) (L : ℂ →ₗ[ℝ] V) (r θ : ℝ) :
    B (L (Complex.exp (θ * I))) (L (circleMap 0 r θ * I)) -
        B (L (circleMap 0 r θ * I)) (L (Complex.exp (θ * I))) =
      r • (B (L 1) (L I) - B (L I) (L 1)) := by
  have he : Complex.exp (θ * I) = Real.cos θ • (1 : ℂ) + Real.sin θ • I := by
    simp [Complex.exp_mul_I, real_smul]
  have hI : circleMap 0 r θ * I = (-r * Real.sin θ) • (1 : ℂ) +
      (r * Real.cos θ) • I := by
    simp [circleMap, he, real_smul]
    ring_nf
    simp [I_sq, sub_eq_add_neg]
  rw [he, hI]
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply]
  have htrig := Real.sin_sq_add_cos_sq θ
  match_scalars <;> nlinarith [congrArg (r * ·) htrig]

end TauCeti

namespace Complex

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- The radial Jacobian makes the complex polar pullback of an integrable function integrable.
This does not assert integrability on every angular slice; exceptional radii are only null. -/
theorem _root_.MeasureTheory.Integrable.comp_complexPolarCoord_symm {f : ℂ → W}
    (hf : Integrable f volume) :
    IntegrableOn (fun p : ℝ × ℝ => p.1 • f (Complex.polarCoord.symm p))
      _root_.polarCoord.target := by
  have hr : Integrable (f ∘ Complex.measurableEquivRealProd.symm) volume :=
    (Complex.volume_preserving_equiv_real_prod.symm.integrable_comp_emb
      Complex.measurableEquivRealProd.symm.measurableEmbedding).mpr hf
  have h := (integrableOn_image_iff_integrableOn_abs_det_fderiv_smul
    (μ := (volume : Measure (ℝ × ℝ))) _root_.polarCoord.open_target.measurableSet
    (fun p _ => (hasFDerivAt_polarCoord_symm p).hasFDerivWithinAt)
    _root_.polarCoord.symm.injOn (f ∘ Complex.measurableEquivRealProd.symm)).mp
      (by simpa only [OpenPartialHomeomorph.symm_image_target_eq_source] using hr.integrableOn)
  refine h.congr (ae_restrict_of_forall_mem _root_.polarCoord.open_target.measurableSet
    fun p hp => ?_)
  dsimp only
  rw [det_fderivPolarCoordSymm, abs_of_pos hp.1]
  rfl

/-- Polar Fubini for an integrable planar function, with angular slices understood almost
everywhere in the radius. Integrable point singularities require no continuous extension. -/
theorem _root_.MeasureTheory.Integrable.integral_eq_integral_circleMap {f : ℂ → W}
    (hf : Integrable f volume) (c : ℂ) :
    (∫ z, f z) = ∫ r in Ioi (0 : ℝ), r • ∫ θ in -π..π, f (circleMap c r θ) := by
  have hg : Integrable (fun z : ℂ => f (c + z)) volume := hf.comp_add_left c
  have hp := hg.comp_complexPolarCoord_symm
  rw [← integral_add_left_eq_self f c, ← Complex.integral_comp_polarCoord_symm]
  rw [_root_.polarCoord_target, Measure.volume_eq_prod] at hp ⊢
  rw [setIntegral_prod _ hp]
  simp only [TauCeti.add_polarCoord_symm_eq_circleMap, integral_smul,
    ← integral_Ioc_eq_integral_Ioo,
    intervalIntegral.integral_of_le (by linarith [Real.pi_pos] : -π ≤ π)]

/-- Polar integration over a region `S` whose polar points in the slit-plane chart are exactly
those of `[a, b] × T`, for an angular set `T` that agrees almost everywhere with its part in
`(-π, π)`. -/
private theorem integral_comp_polarCoord_symm_prod (f : ℂ → W) (z₀ : ℂ) {a b : ℝ} (ha : 0 ≤ a)
    {T : Set ℝ} (hT : MeasurableSet T) (hTae : Ioo (-π) π ∩ T =ᵐ[volume] T) {S : Set ℂ}
    (hS : MeasurableSet S)
    (hST : ∀ r θ, 0 < r → θ ∈ Ioo (-π) π →
      (z₀ + Complex.polarCoord.symm (r, θ) ∈ S ↔ r ∈ Icc a b ∧ θ ∈ T)) :
    (∫ p in Icc a b ×ˢ T, p.1 • f (z₀ + Complex.polarCoord.symm p)) = ∫ z in S, f z := by
  rw [← integral_indicator hS, ← integral_add_left_eq_self (S.indicator f) z₀,
    ← Complex.integral_comp_polarCoord_symm]
  have hEq : EqOn (fun p : ℝ × ℝ ↦ p.1 • S.indicator f (z₀ + Complex.polarCoord.symm p))
      ((Icc a b ×ˢ T).indicator (fun p : ℝ × ℝ ↦ p.1 • f (z₀ + Complex.polarCoord.symm p)))
      _root_.polarCoord.target := by
    rintro ⟨r, θ⟩ ⟨hr, hθ⟩
    dsimp only
    by_cases h : z₀ + Complex.polarCoord.symm (r, θ) ∈ S
    · rw [indicator_of_mem h, indicator_of_mem ((hST r θ hr hθ).1 h)]
    · rw [indicator_of_notMem h, indicator_of_notMem (mt (hST r θ hr hθ).2 h), smul_zero]
  rw [setIntegral_congr_fun (by simp [_root_.polarCoord_target]; measurability) hEq,
    setIntegral_indicator (measurableSet_Icc.prod hT)]
  have he : _root_.polarCoord.target ∩ (Icc a b ×ˢ T) =
      (Ioi 0 ∩ Icc a b) ×ˢ (Ioo (-π) π ∩ T) := by
    ext ⟨r, θ⟩
    simp only [_root_.polarCoord_target, mem_inter_iff, mem_prod]
    tauto
  have hrad : Ioi (0 : ℝ) ∩ Icc a b =ᵐ[volume] Icc a b := by
    filter_upwards [Ioi_ae_eq_Ici (μ := (volume : Measure ℝ)) (a := 0)] with r hr
    simp only [mem_inter_iff]
    rw [hr]
    exact ⟨And.right, fun h ↦ ⟨ha.trans h.1, h⟩⟩
  rw [he, Measure.volume_eq_prod]
  exact setIntegral_congr_set (Measure.set_prod_ae_eq hrad hTae).symm

/-- Polar integration over the closed annulus of radii `a` and `b` about `z₀`, with radial
Jacobian `p.1`, including the disc case `a = 0`. The angular interval includes both endpoints,
whose contribution is null. -/
theorem integral_comp_polarCoord_symm_Icc (f : ℂ → W) (z₀ : ℂ) {a b : ℝ} (ha : 0 ≤ a) :
    (∫ p in Icc (a, -π) (b, π), p.1 • f (z₀ + Complex.polarCoord.symm p)) =
      ∫ z in {z : ℂ | a ≤ ‖z - z₀‖ ∧ ‖z - z₀‖ ≤ b}, f z := by
  have hS : MeasurableSet {z : ℂ | a ≤ ‖z - z₀‖ ∧ ‖z - z₀‖ ≤ b} := by
    have hn : Continuous (fun z : ℂ ↦ ‖z - z₀‖) := by fun_prop
    exact (isClosed_le continuous_const hn).measurableSet.inter
      (isClosed_le hn continuous_const).measurableSet
  rw [Icc_prod_eq]
  refine integral_comp_polarCoord_symm_prod f z₀ ha measurableSet_Icc ?_ hS
    fun r θ hr hθ ↦ ?_
  · rw [inter_eq_left.2 Ioo_subset_Icc_self]
    exact Ioo_ae_eq_Icc
  · simp only [mem_ofPred_eq, add_sub_cancel_left, Complex.norm_polarCoord_symm, abs_of_pos hr]
    exact ⟨fun h ↦ ⟨h, Ioo_subset_Icc_self hθ⟩, And.left⟩

/-- Polar integration over the closed upper half of the annulus of radii `a` and `b` about `z₀`,
with radial Jacobian `p.1`, including the half-disc case `a = 0`. The angular interval `[0, π]`
includes both endpoints, whose contribution is null. -/
theorem integral_comp_polarCoord_symm_Icc_zero_pi (f : ℂ → W) (z₀ : ℂ) {a b : ℝ} (ha : 0 ≤ a) :
    (∫ p in Icc (a, 0) (b, π), p.1 • f (z₀ + Complex.polarCoord.symm p)) =
      ∫ z in {z : ℂ | z₀.im ≤ z.im ∧ a ≤ ‖z - z₀‖ ∧ ‖z - z₀‖ ≤ b}, f z := by
  have hS : MeasurableSet {z : ℂ | z₀.im ≤ z.im ∧ a ≤ ‖z - z₀‖ ∧ ‖z - z₀‖ ≤ b} :=
    (TauCeti.isClosed_upperHalfAnnulus z₀ a b).measurableSet
  have hang : Ioo (-π) π ∩ Icc 0 π =ᵐ[volume] Icc (0 : ℝ) π := by
    have : Ioo (-π) π ∩ Icc 0 π = Ico 0 π := by
      ext θ
      simp only [mem_inter_iff, mem_Ioo, mem_Icc, mem_Ico]
      constructor
      · rintro ⟨⟨_, h⟩, h0, _⟩
        exact ⟨h0, h⟩
      · rintro ⟨h0, h⟩
        exact ⟨⟨by linarith [Real.pi_pos], h⟩, h0, h.le⟩
    rw [this]
    exact Ico_ae_eq_Icc
  rw [Icc_prod_eq]
  refine integral_comp_polarCoord_symm_prod f z₀ ha measurableSet_Icc hang hS
    fun r θ hr hθ ↦ ?_
  have him : z₀.im ≤ (z₀ + Complex.polarCoord.symm (r, θ)).im ↔ θ ∈ Icc 0 π := by
    rw [TauCeti.add_polarCoord_symm_eq_circleMap, TauCeti.circleMap_im, le_add_iff_nonneg_right,
      mul_nonneg_iff_of_pos_left hr]
    refine ⟨fun h ↦ ⟨not_lt.1 fun hneg ↦ ?_, hθ.2.le⟩, fun h ↦
      Real.sin_nonneg_of_nonneg_of_le_pi h.1 h.2⟩
    exact (Real.sin_neg_of_neg_of_neg_pi_lt hneg hθ.1).not_ge h
  simp only [mem_ofPred_eq, him, add_sub_cancel_left, Complex.norm_polarCoord_symm,
    abs_of_pos hr, mem_Icc]
  tauto

end Complex

namespace TauCeti

open Complex

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Polar Fubini for a continuous density in a real normed space on a closed annulus, including
the disc case `a = 0`, with the radial integral outermost and the angular variable running once
around the circle. -/
theorem integral_annulus_eq_integral_circleMap {f : ℂ → F} {z₀ : ℂ} {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b)
    (hf : ContinuousOn f {z : ℂ | a ≤ ‖z - z₀‖ ∧ ‖z - z₀‖ ≤ b}) :
    (∫ z in {z : ℂ | a ≤ ‖z - z₀‖ ∧ ‖z - z₀‖ ≤ b}, f z) =
      ∫ r in a..b, r • ∫ θ in -π..π, f (circleMap z₀ r θ) := by
  have hP : Continuous (fun p : ℝ × ℝ ↦ circleMap z₀ p.1 p.2) := by
    simp only [circleMap]
    fun_prop
  have hmem (p : ℝ × ℝ) (hp : p ∈ Icc a b ×ˢ Icc (-π) π) :
      circleMap z₀ p.1 p.2 ∈ {z : ℂ | a ≤ ‖z - z₀‖ ∧ ‖z - z₀‖ ≤ b} :=
    TauCeti.circleMap_mem_setOf_le_norm_sub_le ha hp.1 p.2
  have hint : IntegrableOn (fun p : ℝ × ℝ ↦ p.1 • f (circleMap z₀ p.1 p.2))
      (Icc a b ×ˢ Icc (-π) π) :=
    (continuous_fst.continuousOn.smul (hf.comp hP.continuousOn hmem)).integrableOn_compact
      (isCompact_Icc.prod isCompact_Icc)
  rw [← Complex.integral_comp_polarCoord_symm_Icc f z₀ ha, Icc_prod_eq,
    Measure.volume_eq_prod]
  simp_rw [add_polarCoord_symm_eq_circleMap]
  rw [setIntegral_prod _ hint]
  simp_rw [integral_smul, integral_Icc_eq_integral_Ioc]
  rw [← intervalIntegral.integral_of_le hab]
  simp_rw [intervalIntegral.integral_of_le (by linarith [Real.pi_pos] : -π ≤ π)]

end TauCeti
