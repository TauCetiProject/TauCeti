/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.SphericalPendulum.Motion
import TauCeti.Analysis.Calculus.Deriv.Slope

/-!
# The oscillation of the height of the spherical pendulum

Along a motion of the spherical pendulum defined at all times, with energy `h` and vertical
angular momentum `j` such that `(h, j)` lies strictly above the curve of relative equilibria
(`j ≠ 0` and `h` above the minimum of the effective potential), the height `z = q₃` stays between
the turning points `z₋ < z₊`, and the vertical momentum `p₃` vanishes exactly at them
(`TauCeti.snd_two_ne_zero_iff_apply_two_mem_Ioo_of_mem_sphericalPendulumPhaseSpace`). While
`p₃ ≠ 0` the height is monotone
(`TauCeti.strictMonoOn_fst_apply_two_of_isMIntegralCurve_sphericalPendulum`,
`TauCeti.strictAntiOn_fst_apply_two_of_isMIntegralCurve_sphericalPendulum`), so such a passage
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
* `TauCeti.strictMonoOn_fst_apply_two_of_isMIntegralCurve_sphericalPendulum`,
  `TauCeti.strictAntiOn_fst_apply_two_of_isMIntegralCurve_sphericalPendulum`: the height is
  monotone while the vertical momentum keeps its sign.

## References

* R. H. Cushman and L. M. Bates, *Global Aspects of Classical Integrable Systems*, 2nd ed.,
  Birkhäuser, 2015, Chapter IV (the spherical pendulum).
-/

public section

open Function Set Filter MeasureTheory
open scoped Topology Manifold

namespace TauCeti

/-- **The first zero.** A continuous function that is positive just after `a` but not at every
time after `a` has a first zero after `a`. -/
private theorem exists_first_zero {f : ℝ → ℝ} {a : ℝ} (hf : Continuous f)
    (ha : ∀ᶠ x in 𝓝[>] a, 0 < f x) (hne : ∃ b, a < b ∧ f b ≤ 0) :
    ∃ b, a < b ∧ f b = 0 ∧ ∀ x ∈ Ioo a b, 0 < f x := by
  obtain ⟨u, hu, hfu⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 ha
  set c := (a + u) / 2
  have hac : a < c := by simp only [c]; linarith [mem_Ioi.1 hu]
  have hcu : c < u := by simp only [c]; linarith [mem_Ioi.1 hu]
  -- The first time after `c` at which `f ≤ 0`.
  set S := {t | c ≤ t ∧ f t ≤ 0}
  have hS : IsClosed S := (isClosed_le continuous_const continuous_id).inter
    (isClosed_le hf continuous_const)
  have hbdd : BddBelow S := ⟨c, fun _ ht ↦ ht.1⟩
  have hSne : S.Nonempty := by
    obtain ⟨b, hab, hb⟩ := hne
    refine ⟨b, not_lt.1 fun hbc ↦ ?_, hb⟩
    exact (hfu ⟨hab, hbc.trans hcu⟩).not_ge hb
  have hb : sInf S ∈ S := hS.csInf_mem hSne hbdd
  have hpos : ∀ x ∈ Ioo a (sInf S), 0 < f x := fun x hx ↦ by
    rcases lt_or_ge x u with hxu | hxu
    · exact hfu ⟨hx.1, hxu⟩
    · exact not_le.1 fun hfx ↦ notMem_of_lt_csInf hx.2 hbdd ⟨hcu.le.trans hxu, hfx⟩
  have hab : a < sInf S := hac.trans_le hb.1
  have hge : 0 ≤ f (sInf S) := ge_of_tendsto ((hf.tendsto _).mono_left nhdsWithin_le_nhds)
    (eventually_of_mem (Ioo_mem_nhdsLT hab) fun x hx ↦ (hpos x hx).le)
  exact ⟨sInf S, hab, le_antisymm hb.2 hge, hpos⟩

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

include hγ in
/-- Along a motion defined at all times, the height `q₃` moves with velocity `p₃`. -/
private theorem hasDerivAt_height (t : ℝ) :
    HasDerivAt (fun t ↦ (γ t : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)).1 2)
      ((γ t : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)).2 2) t :=
  hasDerivWithinAt_univ.1 <| hasDerivWithinAt_fst_apply_two_of_isMIntegralCurveOn_sphericalPendulum
    (hγ.isMIntegralCurveOn univ) (mem_univ t)

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
/-- The vertical momentum increases at the lower turning point: `3 z₋² - 2 h z₋ - 1 > 0`. -/
private theorem turning_lower_pos :
    0 < 3 * sphericalPendulumLowerTurningPoint h j ^ 2 -
      2 * h * sphericalPendulumLowerTurningPoint h j - 1 := by
  have hfac := two_mul_sub_mul_one_sub_sq_sub_sq_eq hj hz₀ hV
  have hab := sphericalPendulumLowerTurningPoint_lt_sphericalPendulumUpperTurningPoint hj hz₀ hV
  have hb := sphericalPendulumUpperTurningPoint_lt_one hj hz₀ hV
  have hc := one_lt_sub_sphericalPendulumLowerTurningPoint_sub_sphericalPendulumUpperTurningPoint
    hj hz₀ hV
  set a := sphericalPendulumLowerTurningPoint h j
  set b := sphericalPendulumUpperTurningPoint h j
  -- Comparing coefficients in the factorization, `3 z₋² - 2 h z₋ - 1 = (z₊ - z₋) (z₃ - z₋)`.
  have : 3 * a ^ 2 - 2 * h * a - 1 = (b - a) * (h - a - b - a) := by
    linear_combination (hfac 1 - hfac (-1)) / 4
  rw [this]
  exact mul_pos (by linarith) (by linarith)

include hj hz₀ hV in
/-- The vertical momentum decreases at the upper turning point: `3 z₊² - 2 h z₊ - 1 < 0`. -/
private theorem turning_upper_neg :
    3 * sphericalPendulumUpperTurningPoint h j ^ 2 -
      2 * h * sphericalPendulumUpperTurningPoint h j - 1 < 0 := by
  have hfac := two_mul_sub_mul_one_sub_sq_sub_sq_eq hj hz₀ hV
  have hab := sphericalPendulumLowerTurningPoint_lt_sphericalPendulumUpperTurningPoint hj hz₀ hV
  have hb := sphericalPendulumUpperTurningPoint_lt_one hj hz₀ hV
  have hc := one_lt_sub_sphericalPendulumLowerTurningPoint_sub_sphericalPendulumUpperTurningPoint
    hj hz₀ hV
  set a := sphericalPendulumLowerTurningPoint h j
  set b := sphericalPendulumUpperTurningPoint h j
  -- Comparing coefficients in the factorization, `3 z₊² - 2 h z₊ - 1 = -(z₊ - z₋) (z₃ - z₊)`.
  have : 3 * b ^ 2 - 2 * h * b - 1 = -((b - a) * (h - a - b - b)) := by
    linear_combination (hfac 1 - hfac (-1)) / 4
  rw [this, neg_lt_zero]
  exact mul_pos (by linarith) (by linarith)

include hγ in
/-- While the vertical momentum is positive, the height of a motion increases strictly. -/
theorem strictMonoOn_fst_apply_two_of_isMIntegralCurve_sphericalPendulum {s t : ℝ}
    (hp : ∀ u ∈ Ioo s t, 0 < (γ u : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)).2 2) :
    StrictMonoOn (fun t ↦ (γ t : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)).1 2)
      (Icc s t) :=
  strictMonoOn_of_deriv_pos (convex_Icc s t)
    (fun u _ ↦ (hasDerivAt_height hγ u).continuousAt.continuousWithinAt) fun u hu ↦ by
      rw [interior_Icc] at hu
      rw [(hasDerivAt_height hγ u).deriv]
      exact hp u hu

include hγ in
/-- While the vertical momentum is negative, the height of a motion decreases strictly. -/
theorem strictAntiOn_fst_apply_two_of_isMIntegralCurve_sphericalPendulum {s t : ℝ}
    (hp : ∀ u ∈ Ioo s t, (γ u : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)).2 2 < 0) :
    StrictAntiOn (fun t ↦ (γ t : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)).1 2)
      (Icc s t) :=
  strictAntiOn_of_deriv_neg (convex_Icc s t)
    (fun u _ ↦ (hasDerivAt_height hγ u).continuousAt.continuousWithinAt) fun u hu ↦ by
      rw [interior_Icc] at hu
      rw [(hasDerivAt_height hγ u).deriv]
      exact hp u hu

include hj hz₀ hV in
/-- The half period `∫_{z₋}^{z₊} dz / √(2 (h - z) (1 - z²) - j²)` is nonnegative. -/
private theorem halfPeriod_nonneg :
    0 ≤ ∫ z in (sphericalPendulumLowerTurningPoint h j)..
      (sphericalPendulumUpperTurningPoint h j), (√(2 * (h - z) * (1 - z ^ 2) - j ^ 2))⁻¹ :=
  intervalIntegral.integral_nonneg
    (sphericalPendulumLowerTurningPoint_lt_sphericalPendulumUpperTurningPoint hj hz₀ hV).le
    fun _ _ ↦ inv_nonneg.2 (Real.sqrt_nonneg _)

include hj hz₀ hV hγ hF in
/-- **Passages are short.** During a time interval on which the vertical momentum of a motion does
not vanish, its height runs monotonically between the turning points, so the length of the interval
is at most the half period `∫_{z₋}^{z₊} dz / √(2 (h - z) (1 - z²) - j²)`. -/
private theorem sub_le_integral {s t : ℝ} (hst : s ≤ t)
    (hp : ∀ u ∈ Ioo s t, (γ u : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)).2 2 ≠ 0) :
    t - s ≤ ∫ z in (sphericalPendulumLowerTurningPoint h j)..
      (sphericalPendulumUpperTurningPoint h j), (√(2 * (h - z) * (1 - z ^ 2) - j ^ 2))⁻¹ := by
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
  rcases hst.eq_or_lt with rfl | hst'
  · rw [sub_self]
    exact halfPeriod_nonneg hj hz₀ hV
  have hm : (s + t) / 2 ∈ Ioo s t := ⟨by linarith, by linarith⟩
  rcases (hp _ hm).lt_or_gt with hneg | hpos'
  · -- The height decreases from `z s` to `z t`.
    have hanti := strictAntiOn_fst_apply_two_of_isMIntegralCurve_sphericalPendulum hγ fun u hu ↦
      sign_eq_neg_one_iff.1 ((hsign hu hm).trans (sign_eq_neg_one_iff.2 hneg))
    have hst₁ : z t < z s := hanti ⟨le_rfl, hst⟩ ⟨hst, le_rfl⟩ hst'
    rw [sub_eq_integral_inv_sqrt_of_isMIntegralCurveOn_sphericalPendulum hst
      (hγ.isMIntegralCurveOn _) hFs (hpos (z t) (z s) (hz t).1 (hz s).2) (Or.inr ⟨rfl, rfl⟩)
      fun u hu ↦ ⟨hanti (Ioo_subset_Icc_self hu) ⟨hst, le_rfl⟩ hu.2,
        hanti ⟨le_rfl, hst⟩ (Ioo_subset_Icc_self hu) hu.1⟩]
    exact intervalIntegral.integral_mono_interval (hz t).1 hst₁.le (hz s).2 hnn hint
  · -- The height increases from `z s` to `z t`.
    have hmono := strictMonoOn_fst_apply_two_of_isMIntegralCurve_sphericalPendulum hγ fun u hu ↦
      sign_eq_one_iff.1 ((hsign hu hm).trans (sign_eq_one_iff.2 hpos'))
    have hst₁ : z s < z t := hmono ⟨le_rfl, hst⟩ ⟨hst, le_rfl⟩ hst'
    rw [sub_eq_integral_inv_sqrt_of_isMIntegralCurveOn_sphericalPendulum hst
      (hγ.isMIntegralCurveOn _) hFs (hpos (z s) (z t) (hz s).1 (hz t).2) (Or.inl ⟨rfl, rfl⟩)
      fun u hu ↦ ⟨hmono ⟨le_rfl, hst⟩ (Ioo_subset_Icc_self hu) hu.1,
        hmono (Ioo_subset_Icc_self hu) ⟨hst, le_rfl⟩ hu.2⟩]
    exact intervalIntegral.integral_mono_interval (hz s).1 hst₁.le (hz t).2 hnn hint

include hj hz₀ hV hγ hF in
/-- **The next turning time.** If the vertical momentum `p₃` of a motion vanishes at time `t₁` and
`σ p₃` has positive derivative there, then `p₃` vanishes again at a later time `t₂`, and `σ p₃` is
positive in between. -/
private theorem exists_next_turning {σ t₁ : ℝ} (hσ : σ ≠ 0)
    (hp₀ : (γ t₁ : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)).2 2 = 0)
    (hd : 0 < σ * (3 * (γ t₁ : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)).1 2 ^ 2 -
      2 * h * (γ t₁ : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)).1 2 - 1)) :
    ∃ t₂, t₁ < t₂ ∧ (γ t₂ : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)).2 2 = 0 ∧
      ∀ u ∈ Ioo t₁ t₂, 0 < σ * (γ u : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)).2 2 := by
  have hfd (t : ℝ) := (hasDerivAt_momentum hγ hF t).const_mul σ
  obtain ⟨t₂, h₁₂, hf₂, hpos⟩ := exists_first_zero
    (continuous_iff_continuousAt.2 fun t ↦ (hfd t).continuousAt)
    -- `σ p₃` vanishes at `t₁` with positive derivative, so it is positive right after `t₁`.
    (by simpa [hp₀] using (hfd t₁).hasDerivWithinAt.eventually_nhdsGT_lt_of_pos hd) <| by
    -- Passages are short, so `σ p₃` does not stay positive.
    by_contra! hfpos
    have := sub_le_integral hj hz₀ hV hγ hF (s := t₁)
      (t := t₁ + 1 + ∫ z in (sphericalPendulumLowerTurningPoint h j)..
        (sphericalPendulumUpperTurningPoint h j), (√(2 * (h - z) * (1 - z ^ 2) - j ^ 2))⁻¹)
      (by linarith [halfPeriod_nonneg hj hz₀ hV])
      fun w hw ↦ right_ne_zero_of_mul (hfpos w hw.1).ne'
    linarith [halfPeriod_nonneg hj hz₀ hV]
  exact ⟨t₂, h₁₂, (mul_eq_zero.1 hf₂).resolve_left hσ, hpos⟩

include hj hz₀ hV hγ hF in
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
  obtain ⟨t₂, h₁₂, hp₂, hpos⟩ := exists_next_turning hj hz₀ hV hγ hF one_ne_zero hp₁
    (by rw [one_mul, h₁]; exact turning_lower_pos hj hz₀ hV)
  simp only [one_mul] at hpos
  refine ⟨t₂, h₁₂, ?_, hpos⟩
  refine (height_eq_or_eq hj hz₀ hV hγ hF t₂ hp₂).resolve_left fun h₂ ↦ ?_
  have := strictMonoOn_fst_apply_two_of_isMIntegralCurve_sphericalPendulum hγ hpos
    ⟨le_rfl, h₁₂.le⟩ ⟨h₁₂.le, le_rfl⟩ h₁₂
  simp only [h₁, h₂, lt_self_iff_false] at this

include hj hz₀ hV hγ hF in
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
  obtain ⟨t₃, h₂₃, hp₃, hneg⟩ := exists_next_turning hj hz₀ hV hγ hF (neg_ne_zero.2 one_ne_zero)
    hp₂ (by rw [h₂, neg_one_mul, neg_pos]; exact turning_upper_neg hj hz₀ hV)
  simp only [neg_one_mul, neg_pos] at hneg
  refine ⟨t₃, h₂₃, ?_, hneg⟩
  refine (height_eq_or_eq hj hz₀ hV hγ hF t₃ hp₃).resolve_right fun h₃ ↦ ?_
  have := strictAntiOn_fst_apply_two_of_isMIntegralCurve_sphericalPendulum hγ hneg
    ⟨le_rfl, h₂₃.le⟩ ⟨h₂₃.le, le_rfl⟩ h₂₃
  simp only [h₂, h₃, lt_self_iff_false] at this

include hj hz₀ hV hγ hF in
/-- **Every motion reaches the lower turning point.** Above the curve of relative equilibria, a
motion of the spherical pendulum defined at all times has a time at which its height is the lower
turning point `z₋`. -/
theorem exists_apply_two_eq_sphericalPendulumLowerTurningPoint_of_isMIntegralCurve :
    ∃ t, (γ t : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)).1 2 =
      sphericalPendulumLowerTurningPoint h j := by
  have hL := halfPeriod_nonneg hj hz₀ hV
  -- Passages are short, so the vertical momentum vanishes at some time, at a turning point.
  obtain ⟨u, -, hu⟩ : ∃ u ∈ Ioo t₀ (t₀ + 1 + ∫ z in (sphericalPendulumLowerTurningPoint h j)..
      (sphericalPendulumUpperTurningPoint h j), (√(2 * (h - z) * (1 - z ^ 2) - j ^ 2))⁻¹),
      (γ u : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)).2 2 = 0 := by
    by_contra! hne
    have := sub_le_integral hj hz₀ hV hγ hF (by linarith) hne
    linarith
  rcases height_eq_or_eq hj hz₀ hV hγ hF u hu with hu' | hu'
  · exact ⟨u, hu'⟩
  · obtain ⟨t, -, ht, -⟩ := exists_lower hj hz₀ hV hγ hF hu'
    exact ⟨t, ht⟩

include hj hz₀ hV hγ hF in
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
