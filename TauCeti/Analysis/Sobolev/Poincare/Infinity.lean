/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import TauCeti.Analysis.Complex.RealChart
import TauCeti.Analysis.Sobolev.Poincare.TransverseBoundary
import TauCeti.MeasureTheory.Function.Jacobian.Plane
import TauCeti.MeasureTheory.Function.LocallyIntegrable

/-!
# The Poincaré inequality at infinity in the plane

Read in the coordinate `w ∈ ℂ ≅ ℝ × ℝ`, a map `χ` on the Riemann sphere which vanishes near `0`
and is compactly supported in `ℂ` has `L²` norm near the point at infinity equal, up to a factor
comparable to one, to

`∫ ‖χ w‖² / |w|⁴`,

because the spherical area element is `4 |dw|² / (1 + |w|²)²`. This file bounds it by the
Dirichlet energy: if `χ` is `C¹`, compactly supported and vanishes on the disc `|w| < R`, then

`∫ ‖χ w‖² / |w|⁴ ≤ (4 / R)² ∫ (‖∂s χ‖² + ‖∂t χ‖²)`

(`TauCeti.integral_inv_sq_mul_norm_sq_le`). This is the Poincaré inequality on a small disc at
the point at infinity. In the coordinate `z = w⁻¹` centred at infinity, the map `η = χ ∘ (·⁻¹)` is
supported in the disc `|z| ≤ 1 / R`, the weight `|w|⁻⁴` is the Jacobian of the inversion, so the
left side is `∫ ‖η‖²`, and the Dirichlet energy is conformally invariant. The Poincaré inequality on
a strip of width `4 / R` containing that disc
(`TauCeti.integral_norm_sq_le_mul_integral_norm_fderiv_sq_of_abs_snd`) then gives the bound.

The norm on the target is arbitrary, so the Dirichlet energy is only conformally invariant up to
the inequality `‖a v₁ + b v₂‖² ≤ (a² + b²) (‖v₁‖² + ‖v₂‖²)`, which is enough here.
-/

public section

namespace TauCeti

open Filter MeasureTheory Set
open scoped Topology
open _root_.Complex (normSq normSq_apply normSq_inv normSq_mul normSq_neg normSq_pos
  equivRealProdCLM)
open TauCeti.Complex (realChart realChart_apply)

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The squared modulus of the complex number with real coordinates `z`. -/
private theorem normSq_equivRealProdCLM_symm (z : ℝ × ℝ) :
    normSq (equivRealProdCLM.symm z) = z.1 ^ 2 + z.2 ^ 2 := by
  simp [normSq_apply, sq]

/-- The squared modulus of the inverse of the complex number with real coordinates `z`. -/
private theorem normSq_symm_realChart_inv (z : ℝ × ℝ) :
    normSq (equivRealProdCLM.symm (realChart (·⁻¹) z)) = (z.1 ^ 2 + z.2 ^ 2)⁻¹ := by
  rw [TauCeti.Complex.equivRealProdCLM_symm_realChart, normSq_inv,
    normSq_equivRealProdCLM_symm]

/-- The inversion is an involution in real coordinates. -/
private theorem realChart_inv_realChart_inv (z : ℝ × ℝ) :
    realChart (·⁻¹) (realChart (·⁻¹) z) = z := by
  rw [realChart_apply, realChart_apply, ContinuousLinearEquiv.symm_apply_apply, inv_inv,
    ContinuousLinearEquiv.apply_symm_apply]

private theorem symm_ne_zero_iff (z : ℝ × ℝ) : equivRealProdCLM.symm z ≠ 0 ↔ z ≠ 0 := by
  rw [ne_eq, ne_eq, ContinuousLinearEquiv.map_eq_zero_iff]

/-- The complex derivative of the inversion at a nonzero point. -/
private theorem hasDerivAt_inv_symm {z : ℝ × ℝ} (hz : z ≠ 0) :
    HasDerivAt (fun y : ℂ ↦ y⁻¹) (-(equivRealProdCLM.symm z ^ 2)⁻¹) (equivRealProdCLM.symm z) :=
  hasDerivAt_inv ((symm_ne_zero_iff z).2 hz)

/-- The squared length of the derivative of the inversion, applied to a unit vector, is its
Jacobian determinant. -/
private theorem fst_sq_add_snd_sq_fderiv_realChart_inv {z : ℝ × ℝ} (hz : z ≠ 0) :
    (fderiv ℝ (realChart (·⁻¹)) z (0, 1)).1 ^ 2 + (fderiv ℝ (realChart (·⁻¹)) z (0, 1)).2 ^ 2 =
      (fderiv ℝ (realChart (·⁻¹)) z).det := by
  rw [TauCeti.Complex.det_fderiv_realChart (hasDerivAt_inv_symm hz),
    TauCeti.Complex.fderiv_realChart_apply (hasDerivAt_inv_symm hz),
    ← normSq_equivRealProdCLM_symm, ContinuousLinearEquiv.symm_apply_apply, normSq_mul,
    normSq_equivRealProdCLM_symm (0, 1)]
  norm_num

/-- **Cauchy–Schwarz for a vector in the image of two directions.** -/
private theorem norm_smul_add_smul_sq_le (a b : ℝ) (v w : V) :
    ‖a • v + b • w‖ ^ 2 ≤ (a ^ 2 + b ^ 2) * (‖v‖ ^ 2 + ‖w‖ ^ 2) := by
  have h : ‖a • v + b • w‖ ≤ |a| * ‖v‖ + |b| * ‖w‖ :=
    (norm_add_le _ _).trans (by rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs])
  have h0 : 0 ≤ ‖a • v + b • w‖ := norm_nonneg _
  have hab : (|a| * ‖v‖ + |b| * ‖w‖) ^ 2 ≤ (a ^ 2 + b ^ 2) * (‖v‖ ^ 2 + ‖w‖ ^ 2) := by
    nlinarith [sq_nonneg (|a| * ‖w‖ - |b| * ‖v‖), sq_abs a, sq_abs b]
  exact (pow_le_pow_left₀ h0 h 2).trans hab

/-- In real coordinates, the squared modulus of the inverse is the inverse of the squared
modulus. -/
private theorem fst_sq_add_snd_sq_realChart_inv (z : ℝ × ℝ) :
    (realChart (·⁻¹) z).1 ^ 2 + (realChart (·⁻¹) z).2 ^ 2 = (z.1 ^ 2 + z.2 ^ 2)⁻¹ := by
  rw [← normSq_equivRealProdCLM_symm, normSq_symm_realChart_inv]

private theorem fst_sq_add_snd_sq_pos {z : ℝ × ℝ} (hz : z ≠ 0) : 0 < z.1 ^ 2 + z.2 ^ 2 := by
  rw [← normSq_equivRealProdCLM_symm]
  exact normSq_pos.2 ((symm_ne_zero_iff z).2 hz)

private theorem realChart_inv_zero : realChart (·⁻¹) (0 : ℝ × ℝ) = 0 := by
  simp [realChart_apply]

/-- The inversion maps the punctured plane onto itself. -/
private theorem image_realChart_inv_compl_singleton :
    realChart (·⁻¹) '' ({0}ᶜ : Set (ℝ × ℝ)) = {0}ᶜ := by
  have hmaps (z : ℝ × ℝ) (hz : z ≠ 0) : realChart (·⁻¹) z ≠ 0 := fun h ↦ by
    have := fst_sq_add_snd_sq_realChart_inv z
    rw [h] at this
    simp only [Prod.fst_zero, Prod.snd_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow, add_zero] at this
    exact (inv_ne_zero (fst_sq_add_snd_sq_pos hz).ne') this.symm
  ext w
  refine ⟨?_, fun hw ↦ ⟨realChart (·⁻¹) w, hmaps w hw, realChart_inv_realChart_inv w⟩⟩
  rintro ⟨z, hz, rfl⟩
  exact hmaps z hz

private theorem injOn_realChart_inv : InjOn (realChart (·⁻¹)) ({0}ᶜ : Set (ℝ × ℝ)) :=
  fun x _ y _ h ↦ by
    rw [← realChart_inv_realChart_inv x, ← realChart_inv_realChart_inv y, h]

private theorem hasFDerivAt_realChart_inv {z : ℝ × ℝ} (hz : z ≠ 0) :
    HasFDerivAt (realChart (·⁻¹)) (fderiv ℝ (realChart (·⁻¹)) z) z :=
  (TauCeti.Complex.hasFDerivAt_realChart (hasDerivAt_inv_symm hz)).differentiableAt.hasFDerivAt

/-- The Jacobian determinant of the inversion is `|z|⁻⁴`. -/
private theorem det_fderiv_realChart_inv {z : ℝ × ℝ} (hz : z ≠ 0) :
    (fderiv ℝ (realChart (·⁻¹)) z).det = ((z.1 ^ 2 + z.2 ^ 2) ^ 2)⁻¹ := by
  rw [TauCeti.Complex.det_fderiv_realChart (hasDerivAt_inv_symm hz), normSq_neg, normSq_inv,
    map_pow, normSq_equivRealProdCLM_symm]

omit [NormedSpace ℝ V] in
/-- **The weight `|w|⁻⁴` is the Jacobian of the inversion.** For a map `χ` with `χ 0 = 0`, the
integral of `‖χ w‖² / |w|⁴` is the integral of `‖χ‖²` read in the coordinate `z = w⁻¹`. -/
private theorem integral_inv_sq_mul_norm_sq_eq {χ : ℝ × ℝ → V} (h0 : χ 0 = 0) :
    ∫ z, ((z.1 ^ 2 + z.2 ^ 2) ^ 2)⁻¹ * ‖χ z‖ ^ 2 = ∫ z, ‖χ (realChart (·⁻¹) z)‖ ^ 2 := by
  have hs : MeasurableSet ({0}ᶜ : Set (ℝ × ℝ)) := (measurableSet_singleton 0).compl
  have h1 := integral_image_eq_integral_of_eq_abs_det_smul (g := fun z : ℝ × ℝ ↦
      ((z.1 ^ 2 + z.2 ^ 2) ^ 2)⁻¹ * ‖χ z‖ ^ 2) (f := fun z ↦ ‖χ (realChart (·⁻¹) z)‖ ^ 2) hs
    injOn_realChart_inv (fun z hz ↦ (hasFDerivAt_realChart_inv hz).differentiableAt)
      fun z hz ↦ by
        have hp := (fst_sq_add_snd_sq_pos hz).ne'
        rw [det_fderiv_realChart_inv hz, abs_of_nonneg (by positivity),
          fst_sq_add_snd_sq_realChart_inv, smul_eq_mul]
        field_simp
  rw [image_realChart_inv_compl_singleton] at h1
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := {0}ᶜ) fun z hz ↦ ?_, h1,
    setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz ↦ ?_]
  all_goals
    simp only [mem_compl_iff, mem_singleton_iff, not_not] at hz
    subst hz
    simp [realChart_inv_zero, h0]

omit [NormedSpace ℝ V] in
/-- A map of the plane vanishing on the disc `s² + t² < R²` and outside a disc
`s² + t² ≤ M`, read in the coordinate `z = w⁻¹`, vanishes near `0` and off the disc
`s² + t² ≤ R⁻²`. -/
private theorem comp_realChart_inv_eq_zero {χ : ℝ × ℝ → V} {R M : ℝ} (hR : 0 < R) (hM : 0 ≤ M)
    (h0 : ∀ z : ℝ × ℝ, z.1 ^ 2 + z.2 ^ 2 < R ^ 2 → χ z = 0)
    (hM' : ∀ w : ℝ × ℝ, M < w.1 ^ 2 + w.2 ^ 2 → χ w = 0) (z : ℝ × ℝ)
    (hz : z.1 ^ 2 + z.2 ^ 2 < (M + 1)⁻¹ ∨ R⁻¹ ^ 2 < z.1 ^ 2 + z.2 ^ 2) :
    χ (realChart (·⁻¹) z) = 0 := by
  by_cases hz0 : z = 0
  · rw [hz0, realChart_inv_zero]
    exact h0 0 (by simpa using pow_pos hR 2)
  have hp := fst_sq_add_snd_sq_pos hz0
  rcases hz with hz | hz
  · refine hM' _ ?_
    rw [fst_sq_add_snd_sq_realChart_inv]
    calc M < M + 1 := lt_add_one M
      _ < (z.1 ^ 2 + z.2 ^ 2)⁻¹ := by rw [lt_inv_comm₀ (by linarith) hp]; exact hz
  · refine h0 _ ?_
    rw [fst_sq_add_snd_sq_realChart_inv]
    calc (z.1 ^ 2 + z.2 ^ 2)⁻¹ < (R⁻¹ ^ 2)⁻¹ := inv_strictAnti₀ (by positivity) hz
      _ = R ^ 2 := by rw [inv_pow, inv_inv]

omit [NormedSpace ℝ V] in
/-- The support of a compactly supported map lies in a disc `s² + t² ≤ M`. -/
private theorem exists_nonneg_forall_lt_eq_zero {χ : ℝ × ℝ → V} (hc : HasCompactSupport χ) :
    ∃ M, 0 ≤ M ∧ ∀ w : ℝ × ℝ, M < w.1 ^ 2 + w.2 ^ 2 → χ w = 0 := by
  obtain ⟨r, hr⟩ := hc.isCompact.isBounded.subset_closedBall 0
  refine ⟨2 * r ^ 2, by positivity, fun w hw ↦ image_eq_zero_of_notMem_tsupport fun hmem ↦ ?_⟩
  have hw' := mem_closedBall_zero_iff.1 (hr hmem)
  have h1 : |w.1| ≤ r := (norm_fst_le w).trans hw'
  have h2 : |w.2| ≤ r := (norm_snd_le w).trans hw'
  nlinarith [sq_abs w.1, sq_abs w.2, abs_nonneg w.1, abs_nonneg w.2]

/-- A map vanishing near `0` and on a punctured neighbourhood of `∞`, read in the coordinate
`z = w⁻¹`, is `C¹` and compactly supported if it is. -/
private theorem contDiff_comp_realChart_inv {χ : ℝ × ℝ → V} (hχ : ContDiff ℝ 1 χ)
    (hη : (fun z ↦ χ (realChart (·⁻¹) z)) =ᶠ[𝓝 0] 0) :
    ContDiff ℝ 1 fun z ↦ χ (realChart (·⁻¹) z) := by
  refine contDiff_iff_contDiffAt.2 fun z ↦ ?_
  by_cases hz : z = 0
  · subst hz
    exact (contDiffAt_const (c := (0 : V))).congr_of_eventuallyEq hη
  · have hιeq : realChart (·⁻¹) = equivRealProdCLM ∘ (·⁻¹) ∘ equivRealProdCLM.symm :=
      funext fun z ↦ realChart_apply _ z
    have hι : ContDiffAt ℝ 1 (realChart (·⁻¹)) z := hιeq ▸
      equivRealProdCLM.contDiff.contDiffAt.comp z
        (((contDiffAt_inv ℂ ((symm_ne_zero_iff z).2 hz)).restrict_scalars ℝ).comp z
          equivRealProdCLM.symm.contDiff.contDiffAt)
    exact hχ.contDiffAt.comp z hι

/-- **The Dirichlet energy does not grow under the inversion.** For a `C¹` map `χ` whose
Dirichlet energy is integrable and which vanishes near `0`, and whose expression in the coordinate
`z = w⁻¹` vanishes near `0`, the energy of the derivative across the strip in the coordinate `z`
is at most the Dirichlet energy of `χ`. -/
private theorem integral_norm_fderiv_comp_realChart_inv_sq_le {χ : ℝ × ℝ → V}
    (hχ : ContDiff ℝ 1 χ)
    (hE : Integrable fun w ↦ ‖fderiv ℝ χ w (1, 0)‖ ^ 2 + ‖fderiv ℝ χ w (0, 1)‖ ^ 2)
    (hχ0 : χ =ᶠ[𝓝 0] 0) (hη : (fun z ↦ χ (realChart (·⁻¹) z)) =ᶠ[𝓝 0] 0) :
    ∫ z, ‖fderiv ℝ (fun z ↦ χ (realChart (·⁻¹) z)) z (0, 1)‖ ^ 2 ≤
      ∫ w, (‖fderiv ℝ χ w (1, 0)‖ ^ 2 + ‖fderiv ℝ χ w (0, 1)‖ ^ 2) := by
  have := Measure.prod.instIsAddHaarMeasure (volume : Measure ℝ) (volume : Measure ℝ)
  set ι : ℝ × ℝ → ℝ × ℝ := realChart (·⁻¹)
  set E : ℝ × ℝ → ℝ := fun w ↦ ‖fderiv ℝ χ w (1, 0)‖ ^ 2 + ‖fderiv ℝ χ w (0, 1)‖ ^ 2
  have hs : MeasurableSet ({0}ᶜ : Set (ℝ × ℝ)) := (measurableSet_singleton 0).compl
  have hzero {F : ℝ × ℝ → ℝ} (hF : F 0 = 0) : ∫ z in ({0}ᶜ : Set (ℝ × ℝ)), F z = ∫ z, F z :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz ↦ by
      simp only [mem_compl_iff, mem_singleton_iff, not_not] at hz
      rwa [hz]
  have hpt (z : ℝ × ℝ) (hz : z ∈ ({0}ᶜ : Set (ℝ × ℝ))) :
      ‖fderiv ℝ (fun z ↦ χ (ι z)) z (0, 1)‖ ^ 2 ≤ |(fderiv ℝ ι z).det| • E (ι z) := by
    have hι := hasFDerivAt_realChart_inv hz
    rw [show (fun z ↦ χ (ι z)) = χ ∘ ι from rfl, fderiv_comp z
      (hχ.differentiable one_ne_zero (ι z)) hι.differentiableAt, ContinuousLinearMap.comp_apply,
      abs_of_nonneg (by rw [det_fderiv_realChart_inv hz]; positivity),
      ← fst_sq_add_snd_sq_fderiv_realChart_inv hz, smul_eq_mul]
    set p := fderiv ℝ ι z (0, 1)
    have hp : fderiv ℝ χ (ι z) p =
        p.1 • fderiv ℝ χ (ι z) (1, 0) + p.2 • fderiv ℝ χ (ι z) (0, 1) := by
      rw [← map_smul, ← map_smul, ← map_add]
      congr 1
      ext <;> simp
    rw [hp]
    exact norm_smul_add_smul_sq_le _ _ _ _
  have hEi : IntegrableOn (fun z ↦ |(fderiv ℝ ι z).det| • E (ι z)) {0}ᶜ :=
    (integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume hs
      (fun z hz ↦ (hasFDerivAt_realChart_inv hz).hasFDerivWithinAt) injOn_realChart_inv E).1
      hE.integrableOn
  calc ∫ z, ‖fderiv ℝ (fun z ↦ χ (ι z)) z (0, 1)‖ ^ 2
      = ∫ z in {0}ᶜ, ‖fderiv ℝ (fun z ↦ χ (ι z)) z (0, 1)‖ ^ 2 :=
        (hzero (by simp [hη.fderiv_eq])).symm
    _ ≤ ∫ z in {0}ᶜ, |(fderiv ℝ ι z).det| • E (ι z) :=
        integral_mono_of_nonneg (Eventually.of_forall fun _ ↦ sq_nonneg _) hEi
          ((ae_restrict_iff' hs).2 (Eventually.of_forall hpt))
    _ = ∫ z in ι '' {0}ᶜ, E z :=
        (integral_image_eq_integral_of_eq_abs_det_smul hs injOn_realChart_inv
          (fun z hz ↦ (hasFDerivAt_realChart_inv hz).differentiableAt) fun _ _ ↦ rfl).symm
    _ = ∫ z, E z := by
        rw [image_realChart_inv_compl_singleton]
        exact hzero (by simp [E, hχ0.fderiv_eq])

/-- **The Poincaré inequality at infinity in the plane.** Let `χ` be a compactly supported `C¹`
map on `ℝ × ℝ ≅ ℂ` which vanishes on the disc `s² + t² < R²`, `R > 0`. Then

`∫ ‖χ w‖² / |w|⁴ ≤ (4 / R)² ∫ (‖∂s χ‖² + ‖∂t χ‖²)`.

The weight `|w|⁻⁴` is the area element of the sphere near its point at infinity, up to a factor
tending to `4`, so this bounds the `L²` norm of `χ` near infinity by its Dirichlet energy. -/
theorem integral_inv_sq_mul_norm_sq_le {χ : ℝ × ℝ → V} {R : ℝ} (hR : 0 < R)
    (hχ : ContDiff ℝ 1 χ) (hc : HasCompactSupport χ)
    (h0 : ∀ z : ℝ × ℝ, z.1 ^ 2 + z.2 ^ 2 < R ^ 2 → χ z = 0) :
    ∫ z, ((z.1 ^ 2 + z.2 ^ 2) ^ 2)⁻¹ * ‖χ z‖ ^ 2 ≤
      (4 / R) ^ 2 * ∫ z, (‖fderiv ℝ χ z (1, 0)‖ ^ 2 + ‖fderiv ℝ χ z (0, 1)‖ ^ 2) := by
  have := Measure.prod.instIsAddHaarMeasure (volume : Measure ℝ) (volume : Measure ℝ)
  obtain ⟨M, hM0, hM⟩ := exists_nonneg_forall_lt_eq_zero hc
  have hR2 : (0 : ℝ) < R ^ 2 := by positivity
  have hdisc {r : ℝ} (hr : 0 < r) : {z : ℝ × ℝ | z.1 ^ 2 + z.2 ^ 2 < r} ∈ 𝓝 0 :=
    (isOpen_lt (by fun_prop) continuous_const).mem_nhds (by simpa using hr)
  have hχ0 : χ =ᶠ[𝓝 0] 0 := Filter.mem_of_superset (hdisc hR2) h0
  have hη : (fun z ↦ χ (realChart (·⁻¹) z)) =ᶠ[𝓝 0] 0 :=
    Filter.mem_of_superset (hdisc (inv_pos.2 (by linarith))) fun z hz ↦
      comp_realChart_inv_eq_zero hR hM0 h0 hM z (Or.inl hz)
  -- In the coordinate `z = w⁻¹` the map is supported in the disc `|z| ≤ 1 / R`.
  have hηc : HasCompactSupport fun z ↦ χ (realChart (·⁻¹) z) := by
    refine HasCompactSupport.intro (isCompact_closedBall (0 : ℝ × ℝ) R⁻¹) fun z hz ↦
      comp_realChart_inv_eq_zero hR hM0 h0 hM z (Or.inr ?_)
    rw [mem_closedBall_zero_iff, not_le, Prod.norm_def, lt_max_iff, Real.norm_eq_abs,
      Real.norm_eq_abs] at hz
    have hR' : 0 ≤ R⁻¹ := inv_nonneg.2 hR.le
    rcases hz with hz | hz
    · nlinarith [sq_abs z.1, sq_nonneg z.2]
    · nlinarith [sq_abs z.2, sq_nonneg z.1]
  have hpoinc := integral_norm_sq_le_mul_integral_norm_fderiv_sq_of_abs_snd
    (contDiff_comp_realChart_inv hχ hη) hηc (r := 2 * R⁻¹) fun z hz ↦
      comp_realChart_inv_eq_zero hR hM0 h0 hM z (Or.inr (by
        have hR' : 0 < R⁻¹ := inv_pos.2 hR
        nlinarith [sq_abs z.2, sq_nonneg z.1, abs_nonneg z.2]))
  have hdχ : Continuous (fderiv ℝ χ) := hχ.continuous_fderiv one_ne_zero
  have hE : Integrable fun w ↦ ‖fderiv ℝ χ w (1, 0)‖ ^ 2 + ‖fderiv ℝ χ w (0, 1)‖ ^ 2 :=
    ((hdχ.clm_apply continuous_const).integrable_norm_sq_of_hasCompactSupport
      (hc.fderiv_apply (𝕜 := ℝ) (1, 0))).add
    ((hdχ.clm_apply continuous_const).integrable_norm_sq_of_hasCompactSupport
      (hc.fderiv_apply (𝕜 := ℝ) (0, 1)))
  rw [integral_inv_sq_mul_norm_sq_eq (h0 0 (by simpa using hR2))]
  calc _ ≤ (2 * (2 * R⁻¹)) ^ 2 * ∫ z, ‖fderiv ℝ (fun z ↦ χ (realChart (·⁻¹) z)) z (0, 1)‖ ^ 2 :=
        hpoinc
    _ ≤ (2 * (2 * R⁻¹)) ^ 2 *
          ∫ w, (‖fderiv ℝ χ w (1, 0)‖ ^ 2 + ‖fderiv ℝ χ w (0, 1)‖ ^ 2) := by
        exact mul_le_mul_of_nonneg_left
          (integral_norm_fderiv_comp_realChart_inv_sq_le hχ hE hχ0 hη) (sq_nonneg _)
    _ = _ := by ring

end TauCeti
