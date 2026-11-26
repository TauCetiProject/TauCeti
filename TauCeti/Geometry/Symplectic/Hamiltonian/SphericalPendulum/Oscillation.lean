/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.SphericalPendulum.Motion
import TauCeti.Analysis.Calculus.Deriv.Slope
import TauCeti.Topology.Order.IntermediateValue

/-!
# The oscillation of the height of the spherical pendulum

Along a motion of the spherical pendulum defined at all times, with energy `h` and vertical
angular momentum `j` such that `(h, j)` lies strictly above the curve of relative equilibria
(`j ≠ 0` and `h` above the minimum of the effective potential), the height `z = q₃` stays between
the turning points `z₋ < z₊`, and the vertical momentum `p₃` vanishes exactly at them
(`TauCeti.snd_two_ne_zero_iff_apply_two_mem_Ioo_of_mem_sphericalPendulumPhaseSpace`). While
`p₃ ≠ 0` the height is monotone
(`TauCeti.strictMonoOn_fst_apply_two_of_isMIntegralCurveOn_sphericalPendulum`,
`TauCeti.strictAntiOn_fst_apply_two_of_isMIntegralCurveOn_sphericalPendulum`), so such a passage
lasts at most `∫_{z₋}^{z₊} dz / √(2 (h - z) (1 - z²) - j²)`, which is finite because `z₋` and `z₊`
are simple roots of the radicand
(`TauCeti.intervalIntegrable_inv_sqrt_two_mul_sub_mul_one_sub_sq_sub_sq`). At a turning point
`p₃' = 3 z² - 2 h z - 1` does not vanish, so `p₃` changes sign there. Hence every motion reaches
`z₋`, and from `z₋` the height rises to `z₊` and falls back to `z₋` in exactly the period
`T(h, j)`.

## Main results

* `TauCeti.exists_apply_two_eq_sphericalPendulumLowerTurningPoint_of_isMIntegralCurve`: every
  motion reaches the lower turning point.
* `TauCeti.exists_mem_Ioo_apply_two_eq_sphericalPendulumUpperTurningPoint_of_isMIntegralCurve`:
  one oscillation of the height takes the period `T(h, j)`.

## References

* R. H. Cushman and L. M. Bates, *Global Aspects of Classical Integrable Systems*, 2nd ed.,
  Birkhäuser, 2015, Chapter IV (the spherical pendulum).
-/

public section

open Function Set Filter MeasureTheory
open scoped Topology Manifold

namespace TauCeti

section Oscillation

variable {h j z₀ : ℝ} {γ : ℝ → sphericalPendulumPhaseSpace} {t₀ : ℝ}
  (hj : j ≠ 0) (hz₀ : z₀ ∈ Ioo (-1) 1) (hV : sphericalPendulumEffectivePotential j z₀ < h)
  (hγ : IsMIntegralCurve γ (sphericalPendulumSymplecticForm.hamiltonianVectorField
    fun y ↦ sphericalPendulumHamiltonian y))
  (hF : sphericalPendulumEnergyMomentum (γ t₀) = (h, j))

include hγ hF in
/-- A motion defined at all times stays in the fibre `F⁻¹(h, j)` through its value at one time. -/
private theorem energyMomentum_eq (t : ℝ) : sphericalPendulumEnergyMomentum (γ t) = (h, j) :=
  (sphericalPendulumEnergyMomentum_eq_of_isMIntegralCurveOn isPreconnected_univ
    (hγ.isMIntegralCurveOn univ) (mem_univ t₀) (mem_univ t)).trans hF

include hj hz₀ hV hγ hF in
/-- The height of a motion stays between the turning points. -/
private theorem height_mem_Icc (t : ℝ) :
    (γ t : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)).1 2 ∈
      Icc (sphericalPendulumLowerTurningPoint h j) (sphericalPendulumUpperTurningPoint h j) := by
  rw [← image_apply_two_preimage_sphericalPendulumEnergyMomentum_eq_Icc hj hz₀ hV]
  exact ⟨γ t, ⟨(γ t).property, energyMomentum_eq hγ hF t⟩, rfl⟩

include hj hz₀ hV hγ hF in
/-- The vertical momentum of a motion vanishes exactly when its height is a turning point. -/
private theorem momentum_ne_zero_iff (t : ℝ) :
    (γ t : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)).2 2 ≠ 0 ↔
      (γ t : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)).1 2 ∈
        Ioo (sphericalPendulumLowerTurningPoint h j) (sphericalPendulumUpperTurningPoint h j) :=
  snd_two_ne_zero_iff_apply_two_mem_Ioo_of_mem_sphericalPendulumPhaseSpace hj hz₀ hV
    (γ t).property (energyMomentum_eq hγ hF t)

include hj hz₀ hV hγ hF in
/-- Where the vertical momentum of a motion vanishes, its height is one of the turning points. -/
private theorem height_eq_or_eq (t : ℝ)
    (hp : (γ t : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)).2 2 = 0) :
    (γ t : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)).1 2 =
        sphericalPendulumLowerTurningPoint h j ∨
      (γ t : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)).1 2 =
        sphericalPendulumUpperTurningPoint h j := by
  have hz := height_mem_Icc hj hz₀ hV hγ hF t
  have hnot := mt (momentum_ne_zero_iff hj hz₀ hV hγ hF t).2 (not_not.2 hp)
  rcases hz.1.eq_or_lt with hz₁ | hz₁
  · exact Or.inl hz₁.symm
  · exact Or.inr (le_antisymm hz.2 (not_lt.1 fun hz₂ ↦ hnot ⟨hz₁, hz₂⟩))

include hγ hF in
/-- Along a motion of energy `h` defined at all times, the vertical momentum `p₃` moves with
velocity `3 q₃² - 2 h q₃ - 1`, half the derivative of the radicand `2 (h - z) (1 - z²) - j²` at the
height `z = q₃`. -/
private theorem hasDerivAt_momentum (t : ℝ) :
    HasDerivAt (fun t ↦ (γ t : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)).2 2)
      (3 * (γ t : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)).1 2 ^ 2 -
        2 * h * (γ t : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)).1 2 - 1) t := by
  have hH : ‖(γ t : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)).2‖ ^ 2 / 2 +
      (γ t : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)).1 2 = h := by
    have hE (x : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)) :
        (sphericalPendulumEnergyMomentum x).1 = ‖x.2‖ ^ 2 / 2 + x.1 2 := by
      rw [← Prod.mk.eta (p := x), sphericalPendulumEnergyMomentum_apply]
    rw [← hE, energyMomentum_eq hγ hF t]
  refine (hasDerivWithinAt_univ.1 <|
    hasDerivWithinAt_snd_apply_two_of_isMIntegralCurveOn_sphericalPendulum
      (hγ.isMIntegralCurveOn univ) (mem_univ t)).congr_deriv ?_
  linear_combination (-2 * (γ t : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)).1 2) * hH

include hj hz₀ hV in
/-- The half period `∫_{z₋}^{z₊} dz / √(2 (h - z) (1 - z²) - j²)` is nonnegative. -/
private theorem halfPeriod_nonneg :
    0 ≤ ∫ z in (sphericalPendulumLowerTurningPoint h j)..
      (sphericalPendulumUpperTurningPoint h j), (√(2 * (h - z) * (1 - z ^ 2) - j ^ 2))⁻¹ :=
  intervalIntegral.integral_nonneg
    (sphericalPendulumLowerTurningPoint_lt_sphericalPendulumUpperTurningPoint hj hz₀ hV).le
    fun _ _ ↦ inv_nonneg.2 (Real.sqrt_nonneg _)

include hj hz₀ hV hγ hF

/-- **Passages are short.** During a time interval on which the vertical momentum of a motion does
not vanish, its height runs monotonically between the turning points, so the length of the interval
is at most the half period `∫_{z₋}^{z₊} dz / √(2 (h - z) (1 - z²) - j²)`. -/
private theorem sub_le_integral {s t : ℝ}
    (hp : ∀ u ∈ Ioo s t, (γ u : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)).2 2 ≠ 0) :
    t - s ≤ ∫ z in (sphericalPendulumLowerTurningPoint h j)..
      (sphericalPendulumUpperTurningPoint h j), (√(2 * (h - z) * (1 - z ^ 2) - j ^ 2))⁻¹ := by
  by_cases hst : s < t
  case neg => exact (sub_nonpos.mpr (le_of_not_gt hst)).trans (halfPeriod_nonneg hj hz₀ hV)
  have hint := intervalIntegrable_inv_sqrt_two_mul_sub_mul_one_sub_sq_sub_sq hj hz₀ hV
  have hnn : 0 ≤ᵐ[volume.restrict (Ioc (sphericalPendulumLowerTurningPoint h j)
      (sphericalPendulumUpperTurningPoint h j))] fun z ↦ (√(2 * (h - z) * (1 - z ^ 2) - j ^ 2))⁻¹ :=
    ae_of_all _ fun z ↦ inv_nonneg.2 (Real.sqrt_nonneg _)
  have hpos (z₁ z₂ : ℝ) (h₁ : sphericalPendulumLowerTurningPoint h j ≤ z₁)
      (h₂ : z₂ ≤ sphericalPendulumUpperTurningPoint h j) :
      ∀ z ∈ Ioo z₁ z₂, 0 < 2 * (h - z) * (1 - z ^ 2) - j ^ 2 := fun z hz ↦
    two_mul_sub_mul_one_sub_sq_sub_sq_pos hj hz₀ hV ⟨h₁.trans_lt hz.1, hz.2.trans_le h₂⟩
  have hz := height_mem_Icc hj hz₀ hV hγ hF
  have hFs := energyMomentum_eq hγ hF s
  set z := fun t ↦ (γ t : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)).1 2
  set p := fun t ↦ (γ t : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)).2 2
  -- The vertical momentum has a constant sign on `(s, t)`.
  have hpc : Continuous p := continuous_iff_continuousAt.2 fun u ↦
    (hasDerivAt_momentum hγ hF u).continuousAt
  have hsign {u w : ℝ} (hu : u ∈ Ioo s t) (hw : w ∈ Ioo s t) :
      SignType.sign (p u) = SignType.sign (p w) :=
    isPreconnected_Ioo.sign_eq_of_continuousOn hpc.continuousOn hp hu hw
  have hm : (s + t) / 2 ∈ Ioo s t := ⟨by linarith, by linarith⟩
  rcases (hp _ hm).lt_or_gt with hneg | hpos'
  · -- The height decreases from `z s` to `z t`.
    have hanti := strictAntiOn_fst_apply_two_of_isMIntegralCurveOn_sphericalPendulum
      (hγ.isMIntegralCurveOn _) fun u hu ↦
      sign_eq_neg_one_iff.1 ((hsign hu hm).trans (sign_eq_neg_one_iff.2 hneg))
    have hst₁ : z t < z s := hanti ⟨le_rfl, hst.le⟩ ⟨hst.le, le_rfl⟩ hst
    rw [sub_eq_integral_inv_sqrt_of_isMIntegralCurveOn_sphericalPendulum hst.le
      (hγ.isMIntegralCurveOn _) hFs (hpos (z t) (z s) (hz t).1 (hz s).2) (Or.inr ⟨rfl, rfl⟩)
      fun u hu ↦ ⟨hanti (Ioo_subset_Icc_self hu) ⟨hst.le, le_rfl⟩ hu.2,
        hanti ⟨le_rfl, hst.le⟩ (Ioo_subset_Icc_self hu) hu.1⟩]
    exact intervalIntegral.integral_mono_interval (hz t).1 hst₁.le (hz s).2 hnn hint
  · -- The height increases from `z s` to `z t`.
    have hmono := strictMonoOn_fst_apply_two_of_isMIntegralCurveOn_sphericalPendulum
      (hγ.isMIntegralCurveOn _) fun u hu ↦
      sign_eq_one_iff.1 ((hsign hu hm).trans (sign_eq_one_iff.2 hpos'))
    have hst₁ : z s < z t := hmono ⟨le_rfl, hst.le⟩ ⟨hst.le, le_rfl⟩ hst
    rw [sub_eq_integral_inv_sqrt_of_isMIntegralCurveOn_sphericalPendulum hst.le
      (hγ.isMIntegralCurveOn _) hFs (hpos (z s) (z t) (hz s).1 (hz t).2) (Or.inl ⟨rfl, rfl⟩)
      fun u hu ↦ ⟨hmono ⟨le_rfl, hst.le⟩ (Ioo_subset_Icc_self hu) hu.1,
        hmono (Ioo_subset_Icc_self hu) ⟨hst.le, le_rfl⟩ hu.2⟩]
    exact intervalIntegral.integral_mono_interval (hz s).1 hst₁.le (hz t).2 hnn hint

/-- **The next turning time.** If the vertical momentum `p₃` of a motion vanishes at time `t₁` and
`σ p₃` has positive derivative there, then `p₃` vanishes again at a later time `t₂`, and `σ p₃` is
positive in between. -/
private theorem exists_next_turning {σ t₁ : ℝ}
    (hp₀ : (γ t₁ : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)).2 2 = 0)
    (hd : 0 < σ * (3 * (γ t₁ : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)).1 2 ^ 2 -
      2 * h * (γ t₁ : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)).1 2 - 1)) :
    ∃ t₂, t₁ < t₂ ∧ (γ t₂ : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)).2 2 = 0 ∧
      ∀ u ∈ Ioo t₁ t₂, 0 < σ * (γ u : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)).2 2 := by
  have hfd (t : ℝ) := (hasDerivAt_momentum hγ hF t).const_mul σ
  have hfc : Continuous fun t ↦
      σ * (γ t : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)).2 2 :=
    continuous_iff_continuousAt.2 fun t ↦ (hfd t).continuousAt
  obtain ⟨t₂, ⟨h₁₂, -⟩, hf₂, hpos⟩ := hfc.continuousOn.exists_mem_Ioo_le_and_forall_gt
    (b := t₁ + 1 + ∫ z in (sphericalPendulumLowerTurningPoint h j)..
      (sphericalPendulumUpperTurningPoint h j), (√(2 * (h - z) * (1 - z ^ 2) - j ^ 2))⁻¹)
    -- `σ p₃` vanishes at `t₁` with positive derivative, so it is positive right after `t₁`.
    (by simpa [hp₀] using (hfd t₁).hasDerivWithinAt.eventually_nhdsGT_lt_of_pos hd) <| by
    -- Passages are short, so `σ p₃` does not stay positive.
    by_contra! hfpos
    have := sub_le_integral hj hz₀ hV hγ hF (s := t₁)
      fun w hw ↦ right_ne_zero_of_mul (hfpos w hw).ne'
    linarith
  -- `σ p₃` is positive just before `t₂`, so it vanishes at `t₂`.
  have hge : 0 ≤ σ * (γ t₂ : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)).2 2 :=
    ge_of_tendsto ((hfc.tendsto _).mono_left nhdsWithin_le_nhds)
      (eventually_of_mem (Ioo_mem_nhdsLT h₁₂) fun u hu ↦ (hpos u hu).le)
  have hσ := left_ne_zero_of_mul hd.ne'
  exact ⟨t₂, h₁₂, (mul_eq_zero.1 (le_antisymm hf₂ hge)).resolve_left hσ, hpos⟩

/-- From the lower turning point the height rises to the upper turning point, with positive
vertical momentum in between. -/
private theorem exists_upper {t₁ : ℝ}
    (h₁ : (γ t₁ : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)).1 2 =
      sphericalPendulumLowerTurningPoint h j) :
    ∃ t₂, t₁ < t₂ ∧ (γ t₂ : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)).1 2 =
        sphericalPendulumUpperTurningPoint h j ∧
      ∀ u ∈ Ioo t₁ t₂, 0 < (γ u : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)).2 2 := by
  have hp₁ : (γ t₁ : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)).2 2 = 0 :=
    not_not.1 fun hp ↦ ((momentum_ne_zero_iff hj hz₀ hV hγ hF t₁).1 hp).1.ne' h₁
  obtain ⟨t₂, h₁₂, hp₂, hpos⟩ := exists_next_turning hj hz₀ hV hγ hF (σ := 1) hp₁
    (by
      rw [one_mul, h₁]
      exact three_mul_sphericalPendulumLowerTurningPoint_sq_sub_pos hj hz₀ hV)
  simp only [one_mul] at hpos
  refine ⟨t₂, h₁₂, ?_, hpos⟩
  refine (height_eq_or_eq hj hz₀ hV hγ hF t₂ hp₂).resolve_left fun h₂ ↦ ?_
  have := strictMonoOn_fst_apply_two_of_isMIntegralCurveOn_sphericalPendulum
      (hγ.isMIntegralCurveOn _) hpos
    ⟨le_rfl, h₁₂.le⟩ ⟨h₁₂.le, le_rfl⟩ h₁₂
  simp only [h₁, h₂, lt_self_iff_false] at this

/-- From the upper turning point the height falls to the lower turning point, with negative
vertical momentum in between. -/
private theorem exists_lower {t₂ : ℝ}
    (h₂ : (γ t₂ : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)).1 2 =
      sphericalPendulumUpperTurningPoint h j) :
    ∃ t₃, t₂ < t₃ ∧ (γ t₃ : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)).1 2 =
        sphericalPendulumLowerTurningPoint h j ∧
      ∀ u ∈ Ioo t₂ t₃, (γ u : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)).2 2 < 0 := by
  have hp₂ : (γ t₂ : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)).2 2 = 0 :=
    not_not.1 fun hp ↦ ((momentum_ne_zero_iff hj hz₀ hV hγ hF t₂).1 hp).2.ne h₂
  obtain ⟨t₃, h₂₃, hp₃, hneg⟩ := exists_next_turning hj hz₀ hV hγ hF (σ := -1)
    hp₂ (by
      rw [h₂, neg_one_mul, neg_pos]
      exact three_mul_sphericalPendulumUpperTurningPoint_sq_sub_neg hj hz₀ hV)
  simp only [neg_one_mul, neg_pos] at hneg
  refine ⟨t₃, h₂₃, ?_, hneg⟩
  refine (height_eq_or_eq hj hz₀ hV hγ hF t₃ hp₃).resolve_right fun h₃ ↦ ?_
  have := strictAntiOn_fst_apply_two_of_isMIntegralCurveOn_sphericalPendulum
      (hγ.isMIntegralCurveOn _) hneg
    ⟨le_rfl, h₂₃.le⟩ ⟨h₂₃.le, le_rfl⟩ h₂₃
  simp only [h₂, h₃, lt_self_iff_false] at this

/-- **Every motion reaches the lower turning point.** Above the curve of relative equilibria, a
motion of the spherical pendulum defined at all times has a time at which its height is the lower
turning point `z₋`. -/
theorem exists_apply_two_eq_sphericalPendulumLowerTurningPoint_of_isMIntegralCurve :
    ∃ t, (γ t : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)).1 2 =
      sphericalPendulumLowerTurningPoint h j := by
  -- Passages are short, so the vertical momentum vanishes at some time, at a turning point.
  obtain ⟨u, -, hu⟩ : ∃ u ∈ Ioo t₀ (t₀ + 1 + ∫ z in (sphericalPendulumLowerTurningPoint h j)..
      (sphericalPendulumUpperTurningPoint h j), (√(2 * (h - z) * (1 - z ^ 2) - j ^ 2))⁻¹),
      (γ u : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)).2 2 = 0 := by
    by_contra! hne
    have := sub_le_integral hj hz₀ hV hγ hF hne
    linarith
  rcases height_eq_or_eq hj hz₀ hV hγ hF u hu with hu' | hu'
  · exact ⟨u, hu'⟩
  · obtain ⟨t, -, ht, -⟩ := exists_lower hj hz₀ hV hγ hF hu'
    exact ⟨t, ht⟩

/-- **One oscillation of the height.** Above the curve of relative equilibria, let a motion of the
spherical pendulum defined at all times have its height at the lower turning point `z₋` at time
`t₁`. Then the height rises to the upper turning point `z₊` at a time `t₂` with
`t₁ < t₂ < t₁ + T(h, j)`, with positive vertical momentum `p₃` in between, and falls back to `z₋`
at time `t₁ + T(h, j)`, with negative `p₃` in between. -/
theorem exists_mem_Ioo_apply_two_eq_sphericalPendulumUpperTurningPoint_of_isMIntegralCurve
    {t₁ : ℝ} (h₁ : (γ t₁ : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)).1 2 =
      sphericalPendulumLowerTurningPoint h j) :
    ∃ t₂ ∈ Ioo t₁ (t₁ + sphericalPendulumPeriod h j),
      (γ t₂ : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)).1 2 =
        sphericalPendulumUpperTurningPoint h j ∧
      (γ (t₁ + sphericalPendulumPeriod h j) :
          EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)).1 2 =
        sphericalPendulumLowerTurningPoint h j ∧
      (∀ u ∈ Ioo t₁ t₂, 0 < (γ u : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)).2 2) ∧
      ∀ u ∈ Ioo t₂ (t₁ + sphericalPendulumPeriod h j),
        (γ u : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)).2 2 < 0 := by
  obtain ⟨t₂, h₁₂, h₂, hpos⟩ := exists_upper hj hz₀ hV hγ hF h₁
  obtain ⟨t₃, h₂₃, h₃, hneg⟩ := exists_lower hj hz₀ hV hγ hF h₂
  have hT := sub_eq_sphericalPendulumPeriod_of_isMIntegralCurveOn hj hz₀ hV h₁₂.le h₂₃.le
    (hγ.isMIntegralCurveOn _) (energyMomentum_eq hγ hF t₁) h₁ h₂ h₃ fun u hu ↦
      (momentum_ne_zero_iff hj hz₀ hV hγ hF u).1 <| hu.elim (fun hu ↦ (hpos u hu).ne')
        fun hu ↦ (hneg u hu).ne
  obtain rfl : t₃ = t₁ + sphericalPendulumPeriod h j := by linarith
  exact ⟨t₂, ⟨h₁₂, h₂₃⟩, h₂, h₃, hpos, hneg⟩

end Oscillation

end TauCeti
