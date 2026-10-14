/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.ODE.Gronwall
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Topology.Semicontinuity.Basic
import TauCeti.Analysis.ODE.Gronwall

/-!
# The evolution variational inequality

Let `φ : X → EReal` be an energy on a metric space and `λ : ℝ`. A curve `u : [0, ∞) → X` is a
solution of the *evolution variational inequality* `EVI_λ` if it is continuous, has finite energy
at every positive time, and for every point `y` of the effective domain `{y | φ y ≠ ⊤}` and every
time `t > 0`

`(1/2) d⁺/dt d(u t, y)² + (λ/2) d(u t, y)² ≤ φ y - φ (u t)`,

where `d⁺/dt` is the upper right Dini derivative. This is one of the metric formulations of the
gradient flow of `φ`, the one adapted to `λ`-convex energies: for a differentiable curve in a
Hilbert space it reads `⟪u', u - y⟫ ≤ φ y - φ u - (λ/2) ‖u - y‖²`, the variational form of the
subdifferential inclusion `-u' ∈ ∂φ(u)` for a `λ`-convex energy. For instance the flow
`t ↦ e⁻ᵗ x` of `‖x‖² / 2` is an `EVI_1` solution (`TauCeti.isEVISolution_exp_neg_smul`). Unlike
curves of maximal slope, `EVI_λ` solutions are `λ`-contracting, which makes them unique.

For a lower semicontinuous energy, the results below are the basic structural properties of an
`EVI_λ` solution `u`:

* the energy `t ↦ φ (u t)` is nonincreasing on `(0, ∞)`;
* the differential inequality integrates, with `E_λ(t) = ∫₀ᵗ e^{λr} dr`, to
  `(e^{λ(t-s)}/2) d(u t, y)² - (1/2) d(u s, y)² ≤ E_λ(t - s) (φ y - φ (u t))` for `0 ≤ s ≤ t`;
* in particular the energy is regularized at positive times:
  `φ (u t) ≤ φ y + (d(u 0, y)² - e^{λt} d(u t, y)²) / (2 E_λ(t))`;
* two solutions satisfy `d(u t, v t) ≤ e^{-λt} d(u 0, v 0)`, so a solution is determined by its
  initial point.

## Main definitions

* `TauCeti.IsEVISolution λ φ u`: `u` is an `EVI_λ` solution for `φ`.

## Main results

* `TauCeti.IsEVISolution.comp_add_const`: a time translate `t ↦ u (t + s)`, `s ≥ 0`, of a
  solution is a solution.
* `TauCeti.IsEVISolution.antitoneOn`: the energy is nonincreasing along a solution.
* `TauCeti.IsEVISolution.exp_mul_dist_sq_sub_le`: the integrated form of the evolution variational
  inequality.
* `TauCeti.IsEVISolution.apply_le`: the energy regularization estimate.
* `TauCeti.IsEVISolution.dist_le`: the `λ`-contraction estimate, and
  `TauCeti.IsEVISolution.eqOn`: uniqueness of the solution with a given initial point.
* `TauCeti.isEVISolution_exp_neg_smul`: the flow `t ↦ e⁻ᵗ x` of `‖x‖² / 2` on a real inner
  product space is an `EVI_1` solution.

## Implementation notes

The time variable runs over `ℝ`, and only the values of `u` on `[0, ∞)` matter. The energy is
required to be finite along the curve at positive times, as for curves of maximal slope, while the
test points `y` range over the whole effective domain. The integrated inequality is stated with an
arbitrary real upper bound `c` for `φ y - φ (u t)`, which avoids multiplying extended reals.

The underlying space is a pseudometric space, as for curves of maximal slope and geodesic convexity
in this directory.

## References

* L. Ambrosio, N. Gigli, G. Savaré, *Gradient Flows in Metric Spaces and in the Space of
  Probability Measures*, 2nd ed., Birkhäuser 2008, Chapter 4.
* M. Muratori, G. Savaré, *Gradient flows and evolution variational inequalities in metric
  spaces. I: Structural properties*, J. Funct. Anal. 278 (2020), Section 3.
-/

public section

open Filter Set Topology Real

namespace TauCeti

section PseudoMetricSpace

variable {X : Type*} [PseudoMetricSpace X] {lam lam' : ℝ} {φ : X → EReal} {u v : ℝ → X} {y : X}
  {s t : ℝ}

/-- The curve `u` is a solution of the *evolution variational inequality* `EVI_λ` for the energy
`φ`, where `λ = lam`: it is continuous on `[0, ∞)`, its energy is finite at positive times, and for
every `y` with `φ y ≠ ⊤` and every `t > 0`

`(1/2) d⁺/dt d(u t, y)² + (λ/2) d(u t, y)² ≤ φ y - φ (u t)`,

where `d⁺/dt` is the upper right Dini derivative, the limit superior of the difference quotients
from the right. -/
structure IsEVISolution (lam : ℝ) (φ : X → EReal) (u : ℝ → X) : Prop where
  /-- An `EVI_λ` solution is continuous on `[0, ∞)`. -/
  continuousOn : ContinuousOn u (Ici 0)
  /-- The energy of an `EVI_λ` solution at a positive time is not `⊤`. -/
  apply_ne_top {t : ℝ} (ht : 0 < t) : φ (u t) ≠ ⊤
  /-- The energy of an `EVI_λ` solution at a positive time is not `⊥`. -/
  apply_ne_bot {t : ℝ} (ht : 0 < t) : φ (u t) ≠ ⊥
  /-- The evolution variational inequality. -/
  limsup_slope_add_le {y : X} (hy : φ y ≠ ⊤) {t : ℝ} (ht : 0 < t) :
    limsup (fun s ↦ ((slope (fun r ↦ dist (u r) y ^ 2 / 2) t s : ℝ) : EReal)) (𝓝[>] t) +
      ((lam * (dist (u t) y ^ 2 / 2) : ℝ) : EReal) ≤ φ y - φ (u t)

namespace IsEVISolution

/-- An `EVI_λ` solution is an `EVI_λ'` solution for every `λ' ≤ λ`. -/
theorem mono (h : IsEVISolution lam φ u) (hlam : lam' ≤ lam) : IsEVISolution lam' φ u where
  continuousOn := h.continuousOn
  apply_ne_top := h.apply_ne_top
  apply_ne_bot := h.apply_ne_bot
  limsup_slope_add_le hy _ ht := (add_le_add_right (EReal.coe_le_coe_iff.2 <|
    mul_le_mul_of_nonneg_right hlam (by positivity)) _).trans (h.limsup_slope_add_le hy ht)

/-- Being an `EVI_λ` solution depends only on the values of the curve at nonnegative times. -/
theorem congr (h : IsEVISolution lam φ u) (huv : EqOn u v (Ici 0)) : IsEVISolution lam φ v where
  continuousOn := h.continuousOn.congr huv.symm
  apply_ne_top ht := huv (mem_Ici.2 ht.le) ▸ h.apply_ne_top ht
  apply_ne_bot ht := huv (mem_Ici.2 ht.le) ▸ h.apply_ne_bot ht
  limsup_slope_add_le {y} hy {t} ht := by
    have hev : (fun s ↦ ((slope (fun r ↦ dist (v r) y ^ 2 / 2) t s : ℝ) : EReal)) =ᶠ[𝓝[>] t]
        fun s ↦ ((slope (fun r ↦ dist (u r) y ^ 2 / 2) t s : ℝ) : EReal) := by
      filter_upwards [self_mem_nhdsWithin] with s (hs : t < s)
      simp only [slope_def_field, huv (mem_Ici.2 ht.le), huv (mem_Ici.2 (ht.trans hs).le)]
    rw [limsup_congr hev, ← huv (mem_Ici.2 ht.le)]
    exact h.limsup_slope_add_le hy ht

/-- **Time translation.** For `s ≥ 0`, the curve `t ↦ u (t + s)` started at time `s` along an
`EVI_λ` solution `u` is again an `EVI_λ` solution. -/
theorem comp_add_const (h : IsEVISolution lam φ u) (hs : 0 ≤ s) :
    IsEVISolution lam φ (fun t ↦ u (t + s)) where
  continuousOn := h.continuousOn.comp (by fun_prop) fun t (ht : 0 ≤ t) ↦
    mem_Ici.2 (add_nonneg ht hs)
  apply_ne_top ht := h.apply_ne_top (add_pos_of_pos_of_nonneg ht hs)
  apply_ne_bot ht := h.apply_ne_bot (add_pos_of_pos_of_nonneg ht hs)
  limsup_slope_add_le {y} hy {t} ht := by
    -- The difference quotients of the translated curve at `t` are those of `u` at `t + s`.
    have hslope : (fun z ↦ ((slope (fun r ↦ dist (u (r + s)) y ^ 2 / 2) t z : ℝ) : EReal)) =
        (fun z ↦ ((slope (fun r ↦ dist (u r) y ^ 2 / 2) (t + s) z : ℝ) : EReal)) ∘ (· + s) := by
      ext z
      simp only [Function.comp_apply, slope_def_field, add_sub_add_right_eq_sub]
    have hmap : Tendsto (· + s) (𝓝[>] t) (𝓝[>] (t + s)) :=
      tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
        ((by fun_prop : Continuous (· + s)).tendsto' t (t + s) rfl |>.mono_left nhdsWithin_le_nhds)
        (eventually_nhdsWithin_of_forall fun z (hz : t < z) ↦ mem_Ioi.2 (by linarith))
    rw [hslope, limsup_comp]
    exact (add_le_add (limsup_le_limsup_of_le hmap (u := fun z ↦
      ((slope (fun r ↦ dist (u r) y ^ 2 / 2) (t + s) z : ℝ) : EReal))) le_rfl).trans
      (h.limsup_slope_add_le hy (add_pos_of_pos_of_nonneg ht hs))

/-- The evolution variational inequality bounds the difference quotients of `d(u ·, y)² / 2`
eventually from the right: for `t > 0` and any real `r > c - λ d(u t, y)² / 2`, where `c` bounds
`φ y - φ (u t)`, the difference quotients at `t` are eventually less than `r`. -/
theorem eventually_slope_lt (h : IsEVISolution lam φ u) (hy : φ y ≠ ⊤) (ht : 0 < t) {c : ℝ}
    (hc : φ y - φ (u t) ≤ c) {r : ℝ} (hr : c - lam * (dist (u t) y ^ 2 / 2) < r) :
    ∀ᶠ s in 𝓝[>] t, slope (fun r ↦ dist (u r) y ^ 2 / 2) t s < r := by
  have hL := (h.limsup_slope_add_le hy ht).trans hc
  rw [← EReal.le_sub_iff_add_le (.inl (EReal.coe_ne_bot _)) (.inl (EReal.coe_ne_top _)),
    ← EReal.coe_sub] at hL
  filter_upwards [eventually_lt_of_limsup_lt (hL.trans_lt (EReal.coe_lt_coe_iff.2 hr))]
    with s hs using EReal.coe_lt_coe_iff.1 hs

/-- Grönwall's inequality for `d(u ·, y)² / 2` on an interval `[s, t]` of positive times along
which `c` bounds `φ y - φ (u r)`. -/
private theorem le_gronwallBound (h : IsEVISolution lam φ u) (hy : φ y ≠ ⊤) (hs : 0 < s)
    (hst : s ≤ t) {c : ℝ} (hc : ∀ r ∈ Ico s t, φ y - φ (u r) ≤ c) :
    dist (u t) y ^ 2 / 2 ≤ gronwallBound (dist (u s) y ^ 2 / 2) (-lam) c (t - s) := by
  have hu : ContinuousOn u (Icc s t) :=
    h.continuousOn.mono (Icc_subset_Ici_self.trans (Ici_subset_Ici.2 hs.le))
  refine le_gronwallBound_of_liminf_deriv_right_le (f := fun r ↦ dist (u r) y ^ 2 / 2)
    (f' := fun r ↦ c - lam * (dist (u r) y ^ 2 / 2))
    (by fun_prop) (fun r hr q hq ↦ ?_) le_rfl (fun r _ ↦ le_of_eq (by ring)) t ⟨hst, le_rfl⟩
  have hr0 : 0 < r := hs.trans_le hr.1
  exact (h.eventually_slope_lt hy hr0 (hc r hr) hq).frequently.mono fun z hz ↦ by
    rwa [slope_def_field, div_eq_inv_mul] at hz

/-- The integrated form of the evolution variational inequality on an interval of positive
times. -/
private theorem exp_mul_dist_sq_sub_le_of_pos (h : IsEVISolution lam φ u)
    (hφ : AntitoneOn (fun t ↦ φ (u t)) (Ioi 0)) (hy : φ y ≠ ⊤) (hs : 0 < s) (hst : s ≤ t) {c : ℝ}
    (hc : φ y - φ (u t) ≤ c) :
    exp (lam * (t - s)) * (dist (u t) y ^ 2 / 2) - dist (u s) y ^ 2 / 2 ≤
      (∫ r in 0..(t - s), exp (lam * r)) * c := by
  have hg := h.le_gronwallBound hy hs hst fun r hr ↦
    (EReal.sub_le_sub le_rfl (hφ (hs.trans_le hr.1) (hs.trans_le hst) hr.2.le)).trans hc
  have := mul_le_mul_of_nonneg_left hg (exp_pos (lam * (t - s))).le
  rw [exp_mul_gronwallBound_neg] at this
  linarith

/-- The energy is nonincreasing along an `EVI_λ` solution of a lower semicontinuous energy. -/
theorem antitoneOn (h : IsEVISolution lam φ u) (hφ : LowerSemicontinuous φ) :
    AntitoneOn (fun t ↦ φ (u t)) (Ioi 0) := by
  intro s (hs : 0 < s) t (ht : 0 < t) hst
  by_contra hlt
  push Not at hlt
  -- The last time `a ∈ [s, t]` at which the energy is at most `φ (u s)`.
  set S := Icc s t ∩ u ⁻¹' (φ ⁻¹' Iic (φ (u s)))
  have hu : ContinuousOn u (Icc s t) :=
    h.continuousOn.mono (Icc_subset_Ici_self.trans (Ici_subset_Ici.2 hs.le))
  have hS : IsClosed S := hu.preimage_isClosed_of_isClosed isClosed_Icc (hφ.isClosed_preimage _)
  have hsS : s ∈ S := ⟨⟨le_rfl, hst⟩, mem_preimage.2 (mem_preimage.2 (mem_Iic.2 le_rfl))⟩
  have hbdd : BddAbove S := ⟨t, fun r hr ↦ hr.1.2⟩
  set a := sSup S
  have haS : a ∈ S := hS.csSup_mem ⟨s, hsS⟩ hbdd
  have ha : 0 < a := hs.trans_le (le_csSup hbdd hsS)
  have hat : a ≤ t := haS.1.2
  -- After `a`, the energy exceeds `φ (u a)`, so the distance to `u a` stays `0` up to `t`.
  have hgt : ∀ r ∈ Ico a t, φ (u a) ≤ φ (u r) := by
    intro r hr
    rcases hr.1.eq_or_lt with rfl | har
    · exact le_rfl
    · have hrS : r ∉ S := fun hrS ↦ (le_csSup hbdd hrS).not_gt har
      have : φ (u s) < φ (u r) := by
        by_contra hle
        exact hrS ⟨⟨haS.1.1.trans har.le, hr.2.le⟩, not_lt.1 hle⟩
      exact haS.2.trans this.le
  have hg := h.le_gronwallBound (h.apply_ne_top ha) ha hat (c := 0) fun r hr ↦
    EReal.sub_nonpos.2 (hgt r hr)
  simp only [dist_self, zero_pow two_ne_zero, zero_div, gronwallBound_ε0_δ0] at hg
  have hdist : dist (u t) (u a) = 0 := by nlinarith [dist_nonneg (x := u t) (y := u a)]
  -- Then `d(u ·, u a)² / 2` has a minimum at `t`, while the evolution variational inequality at
  -- `t`, tested at `u a`, makes it strictly decrease to the right of `t`.
  have hpa := EReal.coe_toReal (h.apply_ne_top ha) (h.apply_ne_bot ha)
  have hpt := EReal.coe_toReal (h.apply_ne_top ht) (h.apply_ne_bot ht)
  have hlt' : (φ (u a)).toReal < (φ (u t)).toReal := by
    rw [← EReal.coe_lt_coe_iff, hpa, hpt]
    exact haS.2.trans_lt hlt
  have hev := h.eventually_slope_lt (y := u a) (h.apply_ne_top ha) ht
    (c := (φ (u a)).toReal - (φ (u t)).toReal) (by rw [EReal.coe_sub, hpa, hpt])
    (r := ((φ (u a)).toReal - (φ (u t)).toReal) / 2) (by rw [hdist]; linarith)
  obtain ⟨z, hz, htz⟩ := (hev.and self_mem_nhdsWithin).exists
  rw [slope_def_field, hdist, zero_pow two_ne_zero, zero_div, sub_zero] at hz
  have : 0 ≤ dist (u z) (u a) ^ 2 / 2 / (z - t) := div_nonneg (by positivity) (sub_pos.2 htz).le
  linarith

/-- **The integrated evolution variational inequality.** For an `EVI_λ` solution `u` of a lower
semicontinuous energy, a point `y` with `φ y ≠ ⊤`, times `0 ≤ s ≤ t` and a real bound
`φ y - φ (u t) ≤ c`,

`(e^{λ(t-s)}/2) d(u t, y)² - (1/2) d(u s, y)² ≤ E_λ(t - s) c`, where `E_λ(T) = ∫₀ᵀ e^{λr} dr`. -/
theorem exp_mul_dist_sq_sub_le (h : IsEVISolution lam φ u) (hφ : LowerSemicontinuous φ)
    (hy : φ y ≠ ⊤) (hs : 0 ≤ s) (hst : s ≤ t) {c : ℝ} (hc : φ y - φ (u t) ≤ c) :
    exp (lam * (t - s)) * (dist (u t) y ^ 2 / 2) - dist (u s) y ^ 2 / 2 ≤
      (∫ r in 0..(t - s), exp (lam * r)) * c := by
  rcases hs.eq_or_lt with rfl | hs
  · rcases hst.eq_or_lt with rfl | ht
    · simp
    -- At `s = 0`, pass to the limit from positive starting times.
    have hcl : (0 : ℝ) ∈ closure (Ioc 0 t) := by
      rw [closure_Ioc ht.ne]
      exact ⟨le_rfl, ht.le⟩
    have hcont : ContinuousWithinAt (fun r ↦ dist (u r) y ^ 2 / 2) (Ioc 0 t) 0 :=
      (((h.continuousOn 0 self_mem_Ici).mono (Ioc_subset_Ioi_self.trans Ioi_subset_Ici_self)).dist
        continuousWithinAt_const).pow 2 |>.div_const 2
    refine ContinuousWithinAt.closure_le hcl (f := fun s ↦ exp (lam * (t - s)) *
        (dist (u t) y ^ 2 / 2) - dist (u s) y ^ 2 / 2)
      (g := fun s ↦ (∫ r in 0..(t - s), exp (lam * r)) * c) ?_ ?_
      (fun s hs ↦ exp_mul_dist_sq_sub_le_of_pos h (h.antitoneOn hφ) hy hs.1 hs.2 hc)
    · exact ((by fun_prop : Continuous fun s ↦ exp (lam * (t - s)) *
        (dist (u t) y ^ 2 / 2)).continuousWithinAt).sub hcont
    · have hE : Continuous fun T ↦ ∫ r in 0..T, exp (lam * r) :=
        intervalIntegral.continuous_primitive (fun _ _ ↦ (by fun_prop : Continuous fun r ↦
          exp (lam * r)).intervalIntegrable _ _) 0
      exact ((hE.comp (continuous_sub_left t)).mul continuous_const).continuousWithinAt
  · exact exp_mul_dist_sq_sub_le_of_pos h (h.antitoneOn hφ) hy hs hst hc

/-- **The energy regularization estimate.** For an `EVI_λ` solution `u` of a lower semicontinuous
energy, a point `y` with `φ y ≠ ⊤` and a time `t > 0`,

`φ (u t) ≤ φ y + (d(u 0, y)² - e^{λt} d(u t, y)²) / (2 E_λ(t))`, where `E_λ(t) = ∫₀ᵗ e^{λr} dr`. -/
theorem apply_le (h : IsEVISolution lam φ u) (hφ : LowerSemicontinuous φ) (hy : φ y ≠ ⊤)
    (ht : 0 < t) :
    φ (u t) ≤ φ y + (((dist (u 0) y ^ 2 - exp (lam * t) * dist (u t) y ^ 2) /
      (2 * ∫ r in 0..t, exp (lam * r)) : ℝ) : EReal) := by
  have hE := integral_exp_mul_pos lam ht
  have hint : ∀ c : ℝ, φ y - φ (u t) ≤ c → exp (lam * t) * (dist (u t) y ^ 2 / 2) -
      dist (u 0) y ^ 2 / 2 ≤ (∫ r in 0..t, exp (lam * r)) * c := fun c hc ↦ by
    simpa using h.exp_mul_dist_sq_sub_le hφ hy le_rfl ht.le hc
  lift φ (u t) to ℝ using ⟨h.apply_ne_top ht, h.apply_ne_bot ht⟩ with p hp
  induction hφy : φ y using EReal.rec with
  | bot =>
    -- A test point of energy `⊥` would violate the integrated inequality.
    set L := exp (lam * t) * (dist (u t) y ^ 2 / 2) - dist (u 0) y ^ 2 / 2
    have := hint (L / (∫ r in 0..t, exp (lam * r)) - 1) (by simp [hφy])
    rw [mul_sub, mul_div_cancel₀ _ hE.ne'] at this
    linarith
  | top => exact absurd hφy hy
  | coe q =>
    have := hint (q - p) (by rw [hφy]; exact (EReal.coe_sub q p).ge)
    rw [← EReal.coe_add, EReal.coe_le_coe_iff, ← sub_le_iff_le_add', le_div_iff₀ (by positivity)]
    nlinarith

/-- The difference quotients of `d(u ·, v ·)² / 2` for two `EVI_λ` solutions of a lower
semicontinuous energy are eventually less than any `r > -2λ d(u t, v t)² / 2` from the right of a
time `t > 0`. -/
private theorem eventually_slope_dist_sq_lt (hu : IsEVISolution lam φ u)
    (hv : IsEVISolution lam φ v) (hφ : LowerSemicontinuous φ) (ht : 0 < t) {r : ℝ}
    (hr : -(2 * lam) * (dist (u t) (v t) ^ 2 / 2) < r) :
    ∀ᶠ z in 𝓝[>] t, slope (fun r ↦ dist (u r) (v r) ^ 2 / 2) t z < r := by
  set A := dist (u t) (v t) ^ 2 / 2 with hA
  set ε := (r + 2 * lam * A) / 4 with hε
  have hε0 : 0 < ε := by linarith
  set pu := (φ (u t)).toReal
  set pv := (φ (v t)).toReal
  have hpu : φ (u t) = pu := (EReal.coe_toReal (hu.apply_ne_top ht) (hu.apply_ne_bot ht)).symm
  have hpv : φ (v t) = pv := (EReal.coe_toReal (hv.apply_ne_top ht) (hv.apply_ne_bot ht)).symm
  have hcu : ContinuousAt u t := hu.continuousOn.continuousAt (Ici_mem_nhds ht)
  have hcv : ContinuousAt v t := hv.continuousOn.continuousAt (Ici_mem_nhds ht)
  -- The evolution variational inequality for `v`, tested at `u t`.
  have h₁ := hv.eventually_slope_lt (y := u t) (hu.apply_ne_top ht) ht (c := pu - pv)
    (by rw [hpu, hpv]; exact (EReal.coe_sub _ _).ge) (r := pu - pv - lam * A + ε)
    (by rw [dist_comm, ← hA]; linarith)
  -- Lower semicontinuity of the energy along `u` at `t`.
  have hlt : ((pu - ε : ℝ) : EReal) < φ (u t) := by
    rw [hpu, EReal.coe_lt_coe_iff]
    linarith
  have h₂ : ∀ᶠ z in 𝓝[>] t, ((pu - ε : ℝ) : EReal) < φ (u z) :=
    nhdsWithin_le_nhds <| hcu.eventually <| hφ (u t) _ hlt
  -- The first-order behaviour of `E_λ(z - t)` and of `e^{λ(z - t)}` at `z = t`.
  have hsub : HasDerivAt (fun z : ℝ ↦ z - t) 1 t := (hasDerivAt_id t).sub_const t
  have hE : HasDerivAt (fun z ↦ ∫ r in 0..(z - t), exp (lam * r)) 1 t := by
    simpa [Function.comp_def] using ((by fun_prop : Continuous fun r ↦
      exp (lam * r)).integral_hasStrictDerivAt 0 (t - t)).hasDerivAt.comp (h := fun z ↦ z - t) t
        hsub
  have hexp : HasDerivAt (fun z ↦ exp (lam * (z - t))) lam t := by
    simpa using (((hasDerivAt_id t).sub_const t).const_mul lam).exp
  have h₃ : ∀ᶠ z in 𝓝[>] t,
      slope (fun z ↦ ∫ r in 0..(z - t), exp (lam * r)) t z * (pv - pu + ε) < pv - pu + 2 * ε :=
    (((hasDerivWithinAt_iff_tendsto_slope' (lt_irrefl t)).1 hE.hasDerivWithinAt).mul_const
      _).eventually_lt_const (by linarith)
  have h₄ : ∀ᶠ z in 𝓝[>] t,
      -slope (fun z ↦ exp (lam * (z - t))) t z * (dist (u z) (v z) ^ 2 / 2) < -lam * A + ε := by
    have hd : Tendsto (fun z ↦ dist (u z) (v z) ^ 2 / 2) (𝓝[>] t) (𝓝 A) :=
      (((hcu.dist hcv).pow 2).div_const 2).mono_left nhdsWithin_le_nhds
    exact (((hasDerivWithinAt_iff_tendsto_slope' (lt_irrefl t)).1
      hexp.hasDerivWithinAt).neg.mul hd).eventually_lt_const (by linarith)
  filter_upwards [h₁, h₂, h₃, h₄, self_mem_nhdsWithin] with z h₁ h₂ h₃ h₄ (hz : t < z)
  have hz0 : 0 < z := ht.trans hz
  have hzt : 0 < z - t := sub_pos.2 hz
  set qz := (φ (u z)).toReal
  have hqz : φ (u z) = qz := (EReal.coe_toReal (hu.apply_ne_top hz0) (hu.apply_ne_bot hz0)).symm
  rw [hqz, EReal.coe_lt_coe_iff] at h₂
  -- The integrated inequality for `u` on `[t, z]`, tested at `v z`.
  have h₅ := hu.exp_mul_dist_sq_sub_le hφ (hv.apply_ne_top hz0) ht.le hz.le (c := pv - qz) <| by
    rw [hqz, EReal.coe_sub, ← hpv]
    exact EReal.sub_le_sub ((hv.antitoneOn hφ) ht hz0 hz.le) le_rfl
  have hEpos := integral_exp_mul_pos lam hzt
  -- With `g = d(v ·, u t)² / 2`, split `a z - a t = (a z - g z) + (g z - g t)` for
  -- `a = d(u ·, v ·)² / 2`: `h₅`, `h₂`, `h₃` and `h₄` bound the first term, `h₁` the second.
  simp only [slope_def_field, sub_self, intervalIntegral.integral_same, mul_zero, exp_zero]
    at h₁ h₃ h₄ ⊢
  rw [div_mul_eq_mul_div, div_lt_iff₀ hzt] at h₃
  rw [neg_mul, neg_lt, div_mul_eq_mul_div, lt_div_iff₀ hzt] at h₄
  rw [div_lt_iff₀ hzt] at h₁ ⊢
  rw [dist_comm (v z), dist_comm (v t)] at h₁
  nlinarith [mul_le_mul_of_nonneg_left (by linarith : pv - qz ≤ pv - pu + ε) hEpos.le]

/-- Grönwall's inequality for `d(u ·, v ·)² / 2` between two positive times. -/
private theorem dist_sq_le_of_pos (hu : IsEVISolution lam φ u) (hv : IsEVISolution lam φ v)
    (hφ : LowerSemicontinuous φ) (hs : 0 < s) (hst : s ≤ t) :
    dist (u t) (v t) ^ 2 / 2 ≤ dist (u s) (v s) ^ 2 / 2 * exp (-(2 * lam) * (t - s)) := by
  have hsub : Icc s t ⊆ Ici 0 := Icc_subset_Ici_self.trans (Ici_subset_Ici.2 hs.le)
  have hu' : ContinuousOn u (Icc s t) := hu.continuousOn.mono hsub
  have hv' : ContinuousOn v (Icc s t) := hv.continuousOn.mono hsub
  have := le_gronwallBound_of_liminf_deriv_right_le (f := fun r ↦ dist (u r) (v r) ^ 2 / 2)
    (f' := fun r ↦ -(2 * lam) * (dist (u r) (v r) ^ 2 / 2)) (K := -(2 * lam)) (ε := 0)
    (by fun_prop) (fun r hr q hq ↦ ?_) le_rfl (fun r _ ↦ by rw [add_zero]) t ⟨hst, le_rfl⟩
  · rwa [gronwallBound_ε0] at this
  · exact (eventually_slope_dist_sq_lt hu hv hφ (hs.trans_le hr.1) hq).frequently.mono
      fun z hz ↦ by rwa [slope_def_field, div_eq_inv_mul] at hz

/-- **`λ`-contraction of `EVI_λ` solutions.** Two `EVI_λ` solutions `u` and `v` of a lower
semicontinuous energy satisfy `d(u t, v t) ≤ e^{-λt} d(u 0, v 0)` for every `t ≥ 0`. -/
theorem dist_le (hu : IsEVISolution lam φ u) (hv : IsEVISolution lam φ v)
    (hφ : LowerSemicontinuous φ) (ht : 0 ≤ t) :
    dist (u t) (v t) ≤ exp (-(lam * t)) * dist (u 0) (v 0) := by
  rcases ht.eq_or_lt with rfl | ht
  · simp
  -- Pass to the limit `s → 0` in the estimate between the positive times `s` and `t`.
  have hcl : (0 : ℝ) ∈ closure (Ioc 0 t) := by
    rw [closure_Ioc ht.ne]
    exact ⟨le_rfl, ht.le⟩
  have hcont : ContinuousWithinAt (fun s ↦ dist (u s) (v s) ^ 2 / 2 *
      exp (-(2 * lam) * (t - s))) (Ioc 0 t) 0 := by
    have hsub : Ioc 0 t ⊆ Ici 0 := Ioc_subset_Ioi_self.trans Ioi_subset_Ici_self
    have hu0 := (hu.continuousOn 0 self_mem_Ici).mono hsub
    have hv0 := (hv.continuousOn 0 self_mem_Ici).mono hsub
    exact (((hu0.dist hv0).pow 2).div_const 2).mul (by fun_prop : Continuous fun s ↦
      exp (-(2 * lam) * (t - s))).continuousWithinAt
  have h := continuousWithinAt_const.closure_le hcl hcont fun s hs ↦
    dist_sq_le_of_pos hu hv hφ hs.1 hs.2
  have hexp : exp (-(2 * lam) * (t - 0)) = exp (-(lam * t)) ^ 2 := by
    rw [← exp_nat_mul]
    ring_nf
  rw [hexp] at h
  exact (pow_le_pow_iff_left₀ dist_nonneg (by positivity) two_ne_zero).1 (by nlinarith)

end IsEVISolution

end PseudoMetricSpace

/-- **Uniqueness of `EVI_λ` solutions.** In a metric space, two `EVI_λ` solutions of a lower
semicontinuous energy with the same initial point agree on `[0, ∞)`. -/
theorem IsEVISolution.eqOn {X : Type*} [MetricSpace X] {lam : ℝ} {φ : X → EReal} {u v : ℝ → X}
    (hu : IsEVISolution lam φ u) (hv : IsEVISolution lam φ v) (hφ : LowerSemicontinuous φ)
    (h₀ : u 0 = v 0) : EqOn u v (Ici 0) := fun _ ht ↦
  dist_le_zero.1 <| by simpa [h₀] using hu.dist_le hv hφ ht

section InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The flow `t ↦ e⁻ᵗ x` of the energy `‖x‖² / 2` on a real inner product space is an `EVI_1`
solution: along it `(1/2) d/dt ‖u t - y‖² + (1/2) ‖u t - y‖² = ‖y‖² / 2 - ‖u t‖² / 2`. -/
theorem isEVISolution_exp_neg_smul (x : E) :
    IsEVISolution 1 (fun y ↦ ((‖y‖ ^ 2 / 2 : ℝ) : EReal)) (fun t ↦ exp (-t) • x) where
  continuousOn := by fun_prop
  apply_ne_top _ := EReal.coe_ne_top _
  apply_ne_bot _ := EReal.coe_ne_bot _
  limsup_slope_add_le {y} _ {t} _ := by
    set w := exp (-t) • x
    have hd : HasDerivAt (fun r ↦ dist (exp (-r) • x) y ^ 2 / 2) (inner ℝ (w - y) (-w)) t := by
      simp only [dist_eq_norm]
      convert ((((hasDerivAt_neg t).exp.smul_const x).sub_const y).norm_sq.div_const 2) using 1
      simp [w, inner_neg_right]
      ring
    have hT : Tendsto (fun s ↦ ((slope (fun r ↦ dist (exp (-r) • x) y ^ 2 / 2) t s : ℝ) : EReal))
        (𝓝[>] t) (𝓝 (inner ℝ (w - y) (-w) : ℝ)) :=
      (continuous_coe_real_ereal.tendsto _).comp
        ((hasDerivWithinAt_iff_tendsto_slope' (lt_irrefl t)).1 hd.hasDerivWithinAt)
    rw [hT.limsup_eq, ← EReal.coe_add, ← EReal.coe_sub, EReal.coe_le_coe_iff, dist_eq_norm,
      inner_neg_right, inner_sub_left, real_inner_self_eq_norm_sq, norm_sub_sq_real,
      real_inner_comm]
    linarith

end InnerProductSpace

end TauCeti
