/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.GradientFlow.EVI.Basic
public import TauCeti.Topology.Semicontinuity.GammaConvergence
import TauCeti.Analysis.ODE.Gronwall

/-!
# Stability of evolution variational inequalities

The endpoint energy regularization estimate characterizes EVI solutions of a lower
semicontinuous energy, among continuous curves of finite energy at positive times.
This formulation involves only distances and endpoint energies, rather than derivatives,
and is therefore suited to passing to limits.

For energies with a common EVI parameter on a fixed metric carrier, Γ-convergence and
pointwise convergence of the solution curves to a continuous curve imply that the limit
is an EVI solution, assuming a nonempty effective domain and no negative-infinite energy
along the limit curve at positive times. No convergence of energies along the curves is assumed: the
Γ-liminf inequality and recovery sequences for the comparison points suffice. Compactness
of trajectories is a separate input, not a consequence of Γ-convergence.

## Main results

* `TauCeti.isEVISolution_of_apply_le`: recover the differential EVI from its endpoint
  regularization estimate.
* `TauCeti.TendstoGamma.isEVISolution_of_tendsto`: stability under Γ-convergence.

## References

* L. Ambrosio, N. Gigli, G. Savaré, *Gradient Flows in Metric Spaces and in the Space of
  Probability Measures*, 2nd ed., Birkhäuser 2008, Chapter 4.
* M. Muratori, G. Savaré, *Gradient flows and evolution variational inequalities in metric
  spaces. I: Structural properties*, J. Funct. Anal. 278 (2020), Sections 3 and 4.
-/

public section

open Filter Set Topology Real MeasureTheory

namespace TauCeti

variable {X : Type*} [PseudoMetricSpace X] {lam : ℝ} {φ : X → EReal} {u : ℝ → X}

/-- A lower bound on the endpoint energy turns the EVI regularization estimate into a
comparison of squared-distance slopes with the scalar Grönwall solution. -/
private theorem slope_le_gronwallBound_of_apply_le {y : X} {s t b c : ℝ}
    (hst : s < t) (hb : (b : EReal) = φ y) (hc : (c : EReal) ≤ φ (u t))
    (hreg : φ (u t) ≤ φ y + (((dist (u s) y ^ 2 - exp (lam * (t - s)) *
      dist (u t) y ^ 2) / (2 * ∫ r in 0..(t - s), exp (lam * r)) : ℝ) : EReal)) :
    slope (fun r ↦ dist (u r) y ^ 2 / 2) s t ≤
      slope (fun r ↦ gronwallBound (dist (u s) y ^ 2 / 2) (-lam) (b - c) (r - s)) s t := by
  have hEpos := integral_exp_mul_pos lam (sub_pos.2 hst)
  rw [← hb, ← EReal.coe_add] at hreg
  have hreal := EReal.coe_le_coe_iff.1 (hc.trans hreg)
  have hmul := (le_div_iff₀ (by positivity :
    0 < 2 * ∫ r in 0..(t - s), exp (lam * r))).1 (sub_le_iff_le_add'.2 hreal)
  have hdist : dist (u t) y ^ 2 / 2 ≤
      gronwallBound (dist (u s) y ^ 2 / 2) (-lam) (b - c) (t - s) := by
    apply (mul_le_mul_iff_right₀ (exp_pos (lam * (t - s)))).1
    rw [exp_mul_gronwallBound_neg]
    nlinarith
  simp only [slope_def_field, sub_self, gronwallBound_x0]
  exact div_le_div_of_nonneg_right (sub_le_sub_right hdist _) (sub_pos.2 hst).le

/-- The endpoint energy regularization estimate on every positive-length time interval
implies the EVI, provided the energy is lower semicontinuous and finite along the curve at
positive times. -/
theorem isEVISolution_of_apply_le (hφ : LowerSemicontinuous φ)
    (hu : ContinuousOn u (Ici 0))
    (htop : ∀ t > 0, φ (u t) ≠ ⊤) (hbot : ∀ t > 0, φ (u t) ≠ ⊥)
    (h : ∀ y, φ y ≠ ⊤ → ∀ s t : ℝ, 0 ≤ s → s < t →
      φ (u t) ≤ φ y + (((dist (u s) y ^ 2 - exp (lam * (t - s)) * dist (u t) y ^ 2) /
        (2 * ∫ r in 0..(t - s), exp (lam * r)) : ℝ) : EReal)) :
    IsEVISolution lam φ u where
  continuousOn := hu
  apply_ne_top := htop _
  apply_ne_bot := hbot _
  limsup_slope_add_le {y} hy {t} ht := by
    have he := EReal.coe_toReal (htop t ht) (hbot t ht)
    have hybot : φ y ≠ ⊥ := by
      intro hybot
      have hle := h y hy 0 t le_rfl ht
      rw [hybot, EReal.bot_add] at hle
      exact hbot t ht (le_bot_iff.1 hle)
    have hey := EReal.coe_toReal hy hybot
    set a := dist (u t) y ^ 2 / 2
    set b := (φ y).toReal
    set e := (φ (u t)).toReal
    have hlim : limsup (fun s ↦ ((slope (fun r ↦ dist (u r) y ^ 2 / 2) t s : ℝ) : EReal))
        (𝓝[>] t) ≤ ((b - e - lam * a : ℝ) : EReal) := by
      apply EReal.le_of_forall_lt_iff_le.1
      intro R hR
      have hR' : b - e - lam * a < R := EReal.coe_lt_coe_iff.1 hR
      let c := e - (R - (b - e - lam * a)) / 2
      have hc : c < e := by dsimp [c]; linarith
      have hcR : b - c - lam * a < R := by dsimp [c]; linarith
      have hcu : ContinuousAt u t := hu.continuousAt (Ici_mem_nhds ht)
      have henergy : ∀ᶠ r in 𝓝[>] t, (c : EReal) < φ (u r) :=
        ((hφ (u t)).comp hcu) c (by simpa only [Function.comp_apply, ← he,
          EReal.coe_lt_coe_iff] using hc) |>.filter_mono
          nhdsWithin_le_nhds
      -- Compare with the solution of q' + lam * q = b - c.
      let q : ℝ → ℝ := fun r ↦ gronwallBound a (-lam) (b - c) (r - t)
      have hq : HasDerivAt q (b - c - lam * a) t := by
        simpa [q, gronwallBound_x0, sub_eq_add_neg, add_comm, mul_comm] using
          hasDerivAt_gronwallBound_shift a (-lam) (b - c) t t
      have hbound : ∀ᶠ r in 𝓝[>] t,
          slope (fun z ↦ dist (u z) y ^ 2 / 2) t r ≤ slope q t r := by
        filter_upwards [henergy, self_mem_nhdsWithin] with r hr htr
        exact slope_le_gronwallBound_of_apply_le htr hey hr.le (h y hy t r ht.le htr)
      have hqR : ∀ᶠ r in 𝓝[>] t, slope q t r < R :=
        hq.hasDerivWithinAt.limsup_slope_le' (lt_irrefl t) hcR
      exact limsup_le_of_le (by isBoundedDefault)
        ((hbound.and hqR).mono fun _ hr ↦ EReal.coe_le_coe_iff.2 (hr.1.trans hr.2.le))
    rw [← hey, ← he, ← EReal.coe_sub]
    calc _ ≤ ((b - e - lam * a : ℝ) : EReal) + ((lam * a : ℝ) : EReal) :=
          add_le_add hlim le_rfl
      _ = _ := by rw [← EReal.coe_add]; congr 1; ring

/-- Γ-convergence preserves the endpoint regularization estimate of EVI solutions, using
recovery sequences for the comparison point and the Γ-liminf inequality along the curves. -/
private theorem TendstoGamma.apply_le_of_isEVISolution
    {F : ℕ → X → EReal} {U : ℕ → ℝ → X} (hΓ : TendstoGamma F φ)
    (hF : ∀ n, LowerSemicontinuous (F n)) (hU : ∀ n, IsEVISolution lam (F n) (U n))
    (hlim : ∀ t ≥ 0, Tendsto (fun n ↦ U n t) atTop (𝓝 (u t)))
    {y : X} (hy : φ y ≠ ⊤) {s t : ℝ} (hs : 0 ≤ s) (hst : s < t) :
    φ (u t) ≤ φ y + (((dist (u s) y ^ 2 - exp (lam * (t - s)) * dist (u t) y ^ 2) /
      (2 * ∫ r in 0..(t - s), exp (lam * r)) : ℝ) : EReal) := by
  obtain ⟨v, hv, hrec⟩ := hΓ.exists_tendsto_limsup_le y
  let C : X → X → X → ℝ := fun x z w ↦
    (dist x w ^ 2 - exp (lam * (t - s)) * dist z w ^ 2) /
      (2 * ∫ r in 0..(t - s), exp (lam * r))
  have hC : Tendsto (fun n ↦ ((C (U n s) (U n t) (v n) : ℝ) : EReal)) atTop
      (𝓝 ((C (u s) (u t) y : ℝ) : EReal)) := by
    apply (continuous_coe_real_ereal.tendsto _).comp
    dsimp [C]
    exact (((hlim s hs).dist hv).pow 2 |>.sub
      (tendsto_const_nhds.mul (((hlim t (hs.trans hst.le)).dist hv).pow 2))).div_const _
  have hfinite : ∀ᶠ n in atTop, F n (v n) ≠ ⊤ :=
    (eventually_lt_of_limsup_lt (hrec.trans_lt (lt_top_iff_ne_top.2 hy))).mono
      fun _ hn ↦ hn.ne
  have hreg : ∀ᶠ n in atTop, F n (U n t) ≤ F n (v n) +
      ((C (U n s) (U n t) (v n) : ℝ) : EReal) := by
    filter_upwards [hfinite] with n hn
    simpa [C, sub_add_cancel] using
      ((hU n).comp_add_const hs).apply_le (hF n) hn (sub_pos.2 hst)
  calc φ (u t)
      ≤ liminf (fun n ↦ F n (U n t)) atTop := hΓ.le_liminf (hlim t (hs.trans hst.le))
    _ ≤ limsup (fun n ↦ F n (v n) + ((C (U n s) (U n t) (v n) : ℝ) : EReal)) atTop :=
      (liminf_le_liminf hreg).trans liminf_le_limsup
    _ ≤ limsup (fun n ↦ F n (v n)) atTop +
        limsup (fun n ↦ ((C (U n s) (U n t) (v n) : ℝ) : EReal)) atTop :=
      EReal.limsup_add_le
        (.inr (by rw [hC.limsup_eq]; exact EReal.coe_ne_top _))
        (.inr (by rw [hC.limsup_eq]; exact EReal.coe_ne_bot _))
    _ ≤ _ := by rw [hC.limsup_eq]; exact add_le_add hrec le_rfl

/-- **Stability of EVI flows under Γ-convergence on a fixed carrier.** Suppose the energies
`F n` are lower semicontinuous and Γ-converge to `φ`, and their `EVI_lam` solutions converge
pointwise at nonnegative times to a continuous curve `u`. If `φ` is not identically `⊤` and
never takes the value `⊥` along `u` at positive times, then `u` is an `EVI_lam` solution.
In particular, neither energy convergence along the curves nor trajectory compactness is
hidden in Γ-convergence; convergence to a continuous trajectory is an explicit hypothesis. -/
theorem TendstoGamma.isEVISolution_of_tendsto
    {F : ℕ → X → EReal} {U : ℕ → ℝ → X} (hΓ : TendstoGamma F φ)
    (hF : ∀ n, LowerSemicontinuous (F n)) (hU : ∀ n, IsEVISolution lam (F n) (U n))
    (hlim : ∀ t ≥ 0, Tendsto (fun n ↦ U n t) atTop (𝓝 (u t)))
    (hu : ContinuousOn u (Ici 0)) (hdom : ∃ y, φ y ≠ ⊤)
    (hbot : ∀ t > 0, φ (u t) ≠ ⊥) : IsEVISolution lam φ u := by
  have hreg := fun y hy s t hs hst ↦ hΓ.apply_le_of_isEVISolution hF hU hlim
    (y := y) hy (s := s) (t := t) hs hst
  have htop : ∀ t > 0, φ (u t) ≠ ⊤ := by
    obtain ⟨y, hy⟩ := hdom
    intro t ht
    exact ne_top_of_le_ne_top (EReal.add_ne_top hy (EReal.coe_ne_top _))
      (hreg y hy 0 t le_rfl ht)
  exact isEVISolution_of_apply_le hΓ.lowerSemicontinuous hu htop hbot hreg

end TauCeti
