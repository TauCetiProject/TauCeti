/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.PositiveScalarCurvature.Bending.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.Order.MonotoneContinuity

/-!
# Reparametrising a bending curve

The speed of a Gromov–Lawson bending curve `u ↦ (r u, h u)` (`TauCeti.IsGromovLawsonBendingCurve`)
is arbitrary, and the bending inequality is invariant under reparametrisation, since it involves
the curve only through its angle, radius and curvature `k = θ' / v`. So every bending curve can be
reparametrised by an increasing diffeomorphism of `ℝ` fixing `0` into one whose speed is its radius
(`TauCeti.IsGromovLawsonBendingCurve.exists_orderIso_speed_eq_radius`): the new parameter is
`∫₀ᵘ v / r`, which tends to `-∞` along the initial horizontal part, because there it is
`log r(0) - log r(u)`, and to `+∞` along the final vertical part, because it is at least
`h(u) / r(0)` for `u ≥ 0`. With speed equal to the radius, the hypersurface swept out by the curve
has the rotationally symmetric induced metric `r² (g_(S^(q - 1)) + du²)`.

## Main results

* `TauCeti.IsGromovLawsonBendingCurve.comp`: an increasing reparametrisation of a bending curve
  fixing `0` is a bending curve for the same constants.
* `TauCeti.IsGromovLawsonBendingCurve.exists_orderIso_speed_eq_radius`: every bending curve has
  such a reparametrisation with speed equal to its radius.
* `TauCeti.exists_isGromovLawsonBendingCurve_speed_eq_radius`: bending curves with speed equal to
  their radius exist for every codimension `q ≥ 3`, lower bound `R₀ > 0`, error constant `C` and
  tube radius `r₀ > 0`.

## References

* M. Gromov, H. B. Lawson, *The classification of simply connected manifolds of positive scalar
  curvature*, Ann. of Math. 111 (1980), 423–434, proof of Theorem A.
* J. Rosenberg, S. Stolz, *Metrics of positive scalar curvature and connections with surgery*,
  Surveys on surgery theory, Vol. 2, Ann. of Math. Stud. 149 (2001), 353–386, Section 3.
-/

public section

noncomputable section

open Real Set Filter
open scoped ContDiff

namespace TauCeti

namespace IsGromovLawsonBendingCurve

variable {q : ℕ} {R₀ C r₀ : ℝ} {r h θ v : ℝ → ℝ}

/-- **Reparametrising a bending curve.** Let `ψ` be a smooth function with positive derivative,
`ψ 0 = 0`, tending to `-∞` at `-∞` and to `+∞` at `+∞`. Composing a bending curve with `ψ` gives a
bending curve for the same constants, with speed `(v ∘ ψ) ψ'`: the angle, the radius and the
curvature `θ' / v` are unchanged along the curve. -/
theorem comp (hγ : IsGromovLawsonBendingCurve q R₀ C r₀ r h θ v) {ψ : ℝ → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (hψ' : ∀ σ, 0 < deriv ψ σ) (hψ₀ : ψ 0 = 0)
    (hψ_bot : Tendsto ψ atBot atBot) (hψ_top : Tendsto ψ atTop atTop) :
    IsGromovLawsonBendingCurve q R₀ C r₀ (r ∘ ψ) (h ∘ ψ) (θ ∘ ψ)
      (fun σ ↦ v (ψ σ) * deriv ψ σ) := by
  have hmono : StrictMono ψ := strictMono_of_deriv_pos hψ'
  have hd (σ : ℝ) : HasDerivAt ψ (deriv ψ σ) σ :=
    ((hψ.differentiable (by simp)) σ).hasDerivAt
  have hnonpos {σ : ℝ} (hσ : σ ≤ 0) : ψ σ ≤ 0 := hψ₀ ▸ hmono.monotone hσ
  refine
    { contDiff_angle := hγ.contDiff_angle.comp hψ
      contDiff_speed := (hγ.contDiff_speed.comp hψ).mul (contDiff_infty_iff_deriv.1 hψ).2
      speed_pos := fun σ ↦ mul_pos (hγ.speed_pos _) (hψ' σ)
      hasDerivAt_radius := fun σ ↦ ((hγ.hasDerivAt_radius (ψ σ)).comp σ (hd σ)).congr_deriv
        (by simp only [Function.comp_apply]; ring)
      hasDerivAt_height := fun σ ↦ ((hγ.hasDerivAt_height (ψ σ)).comp σ (hd σ)).congr_deriv
        (by simp only [Function.comp_apply]; ring)
      monotone_angle := hγ.monotone_angle.comp hmono.monotone
      angle_of_nonpos := fun hσ ↦ hγ.angle_of_nonpos (hnonpos hσ)
      height_of_nonpos := fun hσ ↦ hγ.height_of_nonpos (hnonpos hσ)
      radius_pos := fun σ ↦ hγ.radius_pos (ψ σ)
      radius_zero_lt := by simpa only [Function.comp_apply, hψ₀] using hγ.radius_zero_lt
      tendsto_radius_atBot := hγ.tendsto_radius_atBot.comp hψ_bot
      exists_angle_eq := ?_
      tendsto_height_atTop := hγ.tendsto_height_atTop.comp hψ_top
      scalar_pos := fun σ ↦ ?_ }
  · obtain ⟨b, hb⟩ := hγ.exists_angle_eq
    obtain ⟨b', hb'⟩ := eventually_atTop.1 (tendsto_atTop.1 hψ_top b)
    exact ⟨b', fun σ hσ ↦ hb _ (hb' σ hσ)⟩
  · have hθ : deriv (θ ∘ ψ) σ = deriv θ (ψ σ) * deriv ψ σ :=
      (((hγ.contDiff_angle.differentiable (by simp)) (ψ σ)).hasDerivAt.comp σ (hd σ)).deriv
    have hk : deriv (θ ∘ ψ) σ / (v (ψ σ) * deriv ψ σ) = deriv θ (ψ σ) / v (ψ σ) := by
      rw [hθ, mul_div_mul_right _ _ (hψ' σ).ne']
    simp only [Function.comp_apply]
    rw [hk]
    exact hγ.scalar_pos (ψ σ)

/-- Along the initial horizontal part of a bending curve, `∫₀ᵘ v / r ≤ log r(0) - log r(u)`, since
`u ↦ ∫₀ᵘ v / r + log r(u)` has derivative `v (1 - cos θ) / r ≥ 0`; so the integral tends to `-∞`
at `-∞`. -/
private theorem tendsto_integral_speed_div_radius_atBot
    (hγ : IsGromovLawsonBendingCurve q R₀ C r₀ r h θ v) :
    Tendsto (fun u ↦ ∫ t in (0 : ℝ)..u, v t / r t) atBot atBot := by
  have hs' (u : ℝ) : HasDerivAt (fun u ↦ ∫ t in (0 : ℝ)..u, v t / r t) (v u / r u) u :=
    ((hγ.contDiff_speed.div hγ.contDiff_radius fun t ↦ (hγ.radius_pos t).ne').continuous
      |>.integral_hasStrictDerivAt 0 u).hasDerivAt
  have hlog (u : ℝ) : HasDerivAt (fun u ↦ (∫ t in (0 : ℝ)..u, v t / r t) + log (r u))
      (v u / r u + -(v u * cos (θ u)) / r u) u :=
    (hs' u).add ((hγ.hasDerivAt_radius u).log (hγ.radius_pos u).ne')
  have hF : Monotone fun u ↦ (∫ t in (0 : ℝ)..u, v t / r t) + log (r u) := by
    refine monotone_of_deriv_nonneg (fun u ↦ (hlog u).differentiableAt) fun u ↦ ?_
    rw [(hlog u).deriv]
    have : v u * cos (θ u) ≤ v u := mul_le_of_le_one_right (hγ.speed_pos u).le (cos_le_one _)
    simp only [neg_div, ← sub_eq_add_neg, ← sub_div]
    exact div_nonneg (by linarith) (hγ.radius_pos u).le
  have hlim : Tendsto (fun u ↦ log (r 0) + -log (r u)) atBot atBot :=
    tendsto_atBot_add_const_left _ _
      (tendsto_neg_atTop_atBot.comp (tendsto_log_atTop.comp hγ.tendsto_radius_atBot))
  refine tendsto_atBot_mono' _ ?_ hlim
  filter_upwards [eventually_le_atBot 0] with u hu
  have := hF hu
  simp only [intervalIntegral.integral_same, zero_add] at this
  linarith

/-- For `u ≥ 0`, `∫₀ᵘ v / r ≥ h(u) / r(0)`, since `u ↦ ∫₀ᵘ v / r - h(u) / r(0)` has derivative
`v / r - v sin θ / r(0)`, which is nonnegative because `r` is nonincreasing and `sin θ = 0` for
`u ≤ 0`; so the integral tends to `+∞` at `+∞`. -/
private theorem tendsto_integral_speed_div_radius_atTop
    (hγ : IsGromovLawsonBendingCurve q R₀ C r₀ r h θ v) :
    Tendsto (fun u ↦ ∫ t in (0 : ℝ)..u, v t / r t) atTop atTop := by
  have hs' (u : ℝ) : HasDerivAt (fun u ↦ ∫ t in (0 : ℝ)..u, v t / r t) (v u / r u) u :=
    ((hγ.contDiff_speed.div hγ.contDiff_radius fun t ↦ (hγ.radius_pos t).ne').continuous
      |>.integral_hasStrictDerivAt 0 u).hasDerivAt
  have hG' (u : ℝ) : HasDerivAt (fun u ↦ (∫ t in (0 : ℝ)..u, v t / r t) - h u / r 0)
      (v u / r u - v u * sin (θ u) / r 0) u :=
    (hs' u).sub ((hγ.hasDerivAt_height u).div_const _)
  have hG : Monotone fun u ↦ (∫ t in (0 : ℝ)..u, v t / r t) - h u / r 0 := by
    refine monotone_of_deriv_nonneg (fun u ↦ (hG' u).differentiableAt) fun u ↦ ?_
    rw [(hG' u).deriv, sub_nonneg]
    rcases le_total u 0 with hu | hu
    · rw [hγ.angle_of_nonpos hu, sin_zero, mul_zero, zero_div]
      exact (div_pos (hγ.speed_pos u) (hγ.radius_pos u)).le
    · calc v u * sin (θ u) / r 0 ≤ v u / r 0 := div_le_div_of_nonneg_right
            (mul_le_of_le_one_right (hγ.speed_pos u).le (sin_le_one _)) (hγ.radius_pos 0).le
        _ ≤ v u / r u := div_le_div_of_nonneg_left (hγ.speed_pos u).le (hγ.radius_pos u)
            (hγ.antitone_radius hu)
  refine tendsto_atTop_mono' _ ?_ (hγ.tendsto_height_atTop.atTop_div_const (hγ.radius_pos 0))
  filter_upwards [eventually_ge_atTop 0] with u hu
  have := hG hu
  simp only [intervalIntegral.integral_same, hγ.height_of_nonpos le_rfl, zero_div,
    sub_zero] at this
  linarith

/-- **Speed equal to the radius.** Every bending curve has an increasing reparametrisation `ψ`
fixing `0` whose speed is its radius, so that it sweeps out the same hypersurface with induced
metric the rotationally symmetric metric with profile `log (r ∘ ψ)`. The inverse of `ψ` is
`u ↦ ∫₀ᵘ v / r`. -/
theorem exists_orderIso_speed_eq_radius (hγ : IsGromovLawsonBendingCurve q R₀ C r₀ r h θ v) :
    ∃ ψ : ℝ ≃o ℝ, ContDiff ℝ ∞ ψ ∧ ψ 0 = 0 ∧
      IsGromovLawsonBendingCurve q R₀ C r₀ (r ∘ ψ) (h ∘ ψ) (θ ∘ ψ) (r ∘ ψ) := by
  -- The new parameter `s u = ∫₀ᵘ v / r` has derivative `v / r > 0`.
  set a : ℝ → ℝ := fun u ↦ v u / r u
  have ha : ContDiff ℝ ∞ a :=
    hγ.contDiff_speed.div hγ.contDiff_radius fun u ↦ (hγ.radius_pos u).ne'
  have ha_pos (u : ℝ) : 0 < a u := div_pos (hγ.speed_pos u) (hγ.radius_pos u)
  set s : ℝ → ℝ := fun u ↦ ∫ t in (0 : ℝ)..u, a t
  have hs' (u : ℝ) : HasDerivAt s (a u) u :=
    (ha.continuous.integral_hasStrictDerivAt 0 u).hasDerivAt
  have hs : ContDiff ℝ ∞ s := contDiff_infty_iff_deriv.2
    ⟨fun u ↦ (hs' u).differentiableAt, (funext fun u ↦ (hs' u).deriv : deriv s = a) ▸ ha⟩
  have hs_mono : StrictMono s := strictMono_of_deriv_pos fun u ↦ (hs' u).deriv ▸ ha_pos u
  -- `s` is an increasing smooth bijection of `ℝ`; its inverse `ψ` is the reparametrisation.
  set e : ℝ ≃o ℝ := hs_mono.orderIsoOfSurjective s (hs.continuous.surjective
    hγ.tendsto_integral_speed_div_radius_atTop hγ.tendsto_integral_speed_div_radius_atBot)
  have he : (e.toHomeomorph : ℝ → ℝ) = s := by
    rw [OrderIso.coe_toHomeomorph, StrictMono.coe_orderIsoOfSurjective]
  have hψ : ContDiff ℝ ∞ e.symm := by
    rw [← OrderIso.coe_toHomeomorph_symm]
    exact e.toHomeomorph.contDiff_symm_deriv (fun u ↦ (ha_pos u).ne') (he ▸ hs') (he ▸ hs)
  have hψ' (σ : ℝ) : HasDerivAt e.symm (a (e.symm σ))⁻¹ σ :=
    (hs' (e.symm σ)).of_local_left_inverse e.symm.continuous.continuousAt (ha_pos _).ne'
      (Eventually.of_forall fun y ↦ e.apply_symm_apply y)
  have hψ₀ : e.symm 0 = 0 := e.symm_apply_eq.2 intervalIntegral.integral_same.symm
  have hγ' := hγ.comp hψ (fun σ ↦ (hψ' σ).deriv ▸ inv_pos.2 (ha_pos _)) hψ₀
    e.symm.tendsto_atBot e.symm.tendsto_atTop
  refine ⟨e.symm, hψ, hψ₀, ?_⟩
  convert hγ' using 1
  funext σ
  rw [(hψ' σ).deriv, Function.comp_apply, inv_div, mul_div_cancel₀ _ (hγ.speed_pos _).ne']

end IsGromovLawsonBendingCurve

/-- **Bending curves with speed equal to their radius.** For every codimension `q ≥ 3`, lower
bound `R₀ > 0`, error constant `C` and tube radius `r₀ > 0` there is a bending curve whose speed is
its radius. -/
theorem exists_isGromovLawsonBendingCurve_speed_eq_radius {q : ℕ} (hq : 3 ≤ q) {R₀ r₀ : ℝ}
    (hR₀ : 0 < R₀) (C : ℝ) (hr₀ : 0 < r₀) :
    ∃ r h θ : ℝ → ℝ, IsGromovLawsonBendingCurve q R₀ C r₀ r h θ r := by
  obtain ⟨r, h, θ, v, hγ⟩ := exists_isGromovLawsonBendingCurve hq hR₀ C hr₀
  obtain ⟨ψ, -, -, hγ'⟩ := hγ.exists_orderIso_speed_eq_radius
  exact ⟨r ∘ ψ, h ∘ ψ, θ ∘ ψ, hγ'⟩

end TauCeti
