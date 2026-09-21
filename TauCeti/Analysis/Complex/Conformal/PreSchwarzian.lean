/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.LogDeriv
public import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# Composition, asymptotics, and rigidity of the pre-Schwarzian derivative

The **pre-Schwarzian derivative** of a holomorphic function `f` is `logDeriv (deriv f) = f'' / f'`.
Postcomposing `f` with `w ↦ a * w + b` for `a ≠ 0` leaves it unchanged, and this file proves the
converse: on a domain -- an open preconnected subset of `ℂ` -- two holomorphic functions with
nonvanishing derivatives and the same pre-Schwarzian derivative differ by exactly such a
postcomposition.

This is the statement that integrates a pre-Schwarzian differential equation, such as the
Schwarz--Christoffel equation `f'' / f' = ∑ i, e i / (z - a i)`, back to its solutions.

The chain rule describes the effect of changing the source coordinate. In particular, if `g` is
holomorphic near zero with `g'(0) ≠ 0`, the map `f z = g (-1 / z)` satisfies
`z * f''(z) / f'(z) → -2` at infinity. Thus its pre-Schwarzian tends to zero, the decay condition
needed to identify a meromorphic pre-Schwarzian by its finite poles and residues.

## Main result

* `TauCeti.exists_eqOn_const_mul_add_iff_logDeriv_deriv_eqOn` -- two holomorphic functions with
  nonvanishing derivatives on a domain have the same pre-Schwarzian derivative exactly when one
  is `w ↦ a * w + b` applied to the other, for some `a ≠ 0`.

## References

* L. Ahlfors, *Complex Analysis*, Ch. 6, Section 2.
-/

public section

namespace TauCeti

open Filter Set Topology

/-- The pre-Schwarzian chain rule for locally conformal holomorphic functions. -/
theorem logDeriv_deriv_comp {f g : ℂ → ℂ} {z : ℂ}
    (hf : AnalyticAt ℂ f (g z)) (hg : AnalyticAt ℂ g z)
    (hfn : deriv f (g z) ≠ 0) (hgn : deriv g z ≠ 0) :
    logDeriv (deriv (f ∘ g)) z =
      logDeriv (deriv f) (g z) * deriv g z + logDeriv (deriv g) z := by
  have heq : deriv (f ∘ g) =ᶠ[𝓝 z] fun w => deriv f (g w) * deriv g w := by
    filter_upwards [hg.continuousAt.preimage_mem_nhds hf.eventually_analyticAt,
      hg.eventually_analyticAt] with w hfw hgw
    exact deriv_comp w hfw.differentiableAt hgw.differentiableAt
  rw [(logDeriv_congr_nhds heq).eq_of_nhds,
    logDeriv_fun_mul (f := fun w => deriv f (g w)) z hfn hgn
      (hf.deriv.differentiableAt.comp z hg.differentiableAt) hg.deriv.differentiableAt]
  rw [← Function.comp_def (deriv f) g,
    logDeriv_comp hf.deriv.differentiableAt hg.differentiableAt]

/-- In the coordinate `w = -1 / z`, the pre-Schwarzian acquires the term `-2 / z`. -/
theorem logDeriv_deriv_comp_neg_inv {g : ℂ → ℂ} {z : ℂ}
    (hg : AnalyticAt ℂ g (-z⁻¹)) (hgn : deriv g (-z⁻¹) ≠ 0) (hz : z ≠ 0) :
    logDeriv (deriv (fun w => g (-w⁻¹))) z =
      logDeriv (deriv g) (-z⁻¹) / z ^ 2 - 2 / z := by
  have hd : deriv (fun w : ℂ => -w⁻¹) = fun w => (w ^ 2)⁻¹ := by
    ext w
    simp [deriv_inv]
  have h := logDeriv_deriv_comp (g := fun w : ℂ => -w⁻¹) hg
    ((analyticAt_id.inv hz).neg) hgn (by simp [hd, hz])
  rw [hd] at h
  have hlog : logDeriv (fun w : ℂ => (w ^ 2)⁻¹) z = -(2 : ℂ) / z := by
    simpa using logDeriv_zpow z (-2)
  simpa [Function.comp_def, hlog, div_eq_mul_inv, sub_eq_add_neg] using h

/-- If the inverse coordinate of a map is holomorphic and regular at zero, its pre-Schwarzian
has leading term `-2 / z` at infinity. The limit is through the whole complex plane. -/
theorem tendsto_mul_logDeriv_deriv_comp_neg_inv {g : ℂ → ℂ}
    (hg : AnalyticAt ℂ g 0) (hgn : deriv g 0 ≠ 0) :
    Tendsto (fun z : ℂ => z * logDeriv (deriv (fun w => g (-w⁻¹))) z)
      (Bornology.cobounded ℂ) (𝓝 (-2)) := by
  have hi : Tendsto (fun z : ℂ => -z⁻¹) (Bornology.cobounded ℂ) (𝓝 0) := by
    simpa using (tendsto_inv₀_cobounded (α := ℂ)).neg
  have hc : ContinuousAt (logDeriv (deriv g)) 0 :=
    hg.deriv.deriv.continuousAt.div hg.deriv.continuousAt hgn
  have hlim := ((hc.tendsto.comp hi).mul tendsto_inv₀_cobounded).sub
    (tendsto_const_nhds (x := (2 : ℂ)))
  simp only [mul_zero, zero_sub] at hlim
  apply hlim.congr'
  filter_upwards [hi.eventually hg.eventually_analyticAt,
    hi.eventually (hg.deriv.continuousAt.eventually_ne hgn),
    (tendsto_inv₀_cobounded' (α := ℂ)).eventually self_mem_nhdsWithin] with z hz hn hz0
  have hz' : z ≠ 0 := by simpa using hz0
  rw [logDeriv_deriv_comp_neg_inv hz hn hz']
  simp only [Function.comp_apply]
  field_simp

/-- A map regular in the inverse coordinate has pre-Schwarzian tending to zero at infinity. -/
theorem tendsto_logDeriv_deriv_comp_neg_inv {g : ℂ → ℂ}
    (hg : AnalyticAt ℂ g 0) (hgn : deriv g 0 ≠ 0) :
    Tendsto (logDeriv (deriv (fun w => g (-w⁻¹))))
      (Bornology.cobounded ℂ) (𝓝 0) := by
  have h := (tendsto_mul_logDeriv_deriv_comp_neg_inv hg hgn).mul
    (tendsto_inv₀_cobounded (α := ℂ))
  simp only [mul_zero] at h
  apply h.congr'
  filter_upwards [(tendsto_inv₀_cobounded' (α := ℂ)).eventually self_mem_nhdsWithin]
    with z hz
  have hz' : z ≠ 0 := by simpa using hz
  field_simp

/-- **Rigidity of the pre-Schwarzian derivative.** Two holomorphic functions with nonvanishing
derivatives on a domain have equal pre-Schwarzian derivatives exactly when one is obtained from
the other by postcomposition with `w ↦ a * w + b` for a nonzero constant `a`. -/
theorem exists_eqOn_const_mul_add_iff_logDeriv_deriv_eqOn {Ω : Set ℂ} (hΩopen : IsOpen Ω)
    (hΩconn : IsPreconnected Ω) {f g : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f Ω) (hg : DifferentiableOn ℂ g Ω)
    (hfn : ∀ z ∈ Ω, deriv f z ≠ 0) (hgn : ∀ z ∈ Ω, deriv g z ≠ 0) :
    (∃ a : ℂ, a ≠ 0 ∧ ∃ b : ℂ, EqOn f (fun z => a * g z + b) Ω) ↔
      EqOn (logDeriv (deriv f)) (logDeriv (deriv g)) Ω := by
  rw [logDeriv_eqOn_iff (hf.deriv hΩopen) (hg.deriv hΩopen) hΩopen hΩconn hgn hfn]
  constructor
  · rintro ⟨a, ha, b, hfg⟩
    refine ⟨a, ha, fun z hz => ?_⟩
    have hderiv := hfg.deriv hΩopen hz
    simpa [deriv_const_mul_field] using hderiv
  · rintro ⟨a, ha, hderiv⟩
    refine ⟨a, ha, ?_⟩
    have hag : DifferentiableOn ℂ (fun z => a * g z) Ω :=
      fun z hz => (hg z hz).const_mul a
    obtain ⟨b, hb⟩ := hΩopen.exists_eq_add_of_deriv_eq hΩconn hf hag fun z hz => by
      simpa [deriv_const_mul_field] using hderiv hz
    exact ⟨b, hb⟩

end TauCeti
