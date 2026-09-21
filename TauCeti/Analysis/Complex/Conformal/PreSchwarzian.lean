/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.LogDeriv
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.CauchyIntegral
import TauCeti.Analysis.SpecialFunctions.Pow.LogDeriv

/-!
# The pre-Schwarzian derivative: rigidity, and the pole at a corner

The **pre-Schwarzian derivative** of a holomorphic function `f` is `logDeriv (deriv f) = f'' / f'`.
Postcomposing `f` with `w ↦ a * w + b` for `a ≠ 0` leaves it unchanged, and this file proves the
converse: on a domain -- an open preconnected subset of `ℂ` -- two holomorphic functions with
nonvanishing derivatives and the same pre-Schwarzian derivative differ by exactly such a
postcomposition.  That is the statement which integrates a pre-Schwarzian differential equation,
such as the Schwarz--Christoffel equation `f'' / f' = ∑ i, e i / (z - a i)`, back to its solutions.

The second half of the file computes the pre-Schwarzian derivative of a **corner power**
`f = w + h ^ β`, where `h` is holomorphic and `β` is a fixed complex exponent.  Its pre-Schwarzian
is `(β - 1) * logDeriv h + logDeriv (deriv h)`, independently of the branch, and at a simple zero
`p` of `h` one has the residue asymptotic `(z - p) * logDeriv (deriv f) z → β - 1`.
So the exponent of a corner power is read off from the residue of the pre-Schwarzian
derivative at that corner, which is how a map with a corner of opening `α` contributes the
residue `α / π - 1` to the Schwarz--Christoffel partial-fraction identity.

## Main results

* `TauCeti.exists_eqOn_const_mul_add_iff_logDeriv_deriv_eqOn` -- two holomorphic functions with
  nonvanishing derivatives on a domain have the same pre-Schwarzian derivative exactly when one
  is `w ↦ a * w + b` applied to the other, for some `a ≠ 0`.
* `TauCeti.logDeriv_deriv_of_eqOn_add_cpow` -- the pre-Schwarzian derivative of a corner power.
* `TauCeti.tendsto_sub_mul_logDeriv_deriv_of_eqOn_add_cpow` -- at a simple zero of the base, the
  pre-Schwarzian derivative of a corner power has residue asymptotic `β - 1`.

## References

* L. Ahlfors, *Complex Analysis*, Ch. 6, Section 2.
-/

public section

namespace TauCeti

open Set

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

section Corner

open Complex Filter Topology

variable {h f : ℂ → ℂ} {s : Set ℂ} {p w β : ℂ}

/-- **The pre-Schwarzian derivative of a corner power.**  Where `f` agrees with `w + h ^ β` on an
open set on which the holomorphic base `h` avoids the branch cut, the pre-Schwarzian derivative of
`f` is `(β - 1) * logDeriv h + logDeriv (deriv h)`.  The branch used to define the power leaves no
trace. -/
theorem logDeriv_deriv_of_eqOn_add_cpow (hs : IsOpen s) (hh : DifferentiableOn ℂ h s)
    (hslit : ∀ z ∈ s, h z ∈ slitPlane) (hβ : β ≠ 0) (hf : EqOn f (fun z => w + h z ^ β) s)
    {z : ℂ} (hz : z ∈ s) (hdh : deriv h z ≠ 0) :
    logDeriv (deriv f) z = (β - 1) * logDeriv h z + logDeriv (deriv h) z := by
  have hderiv : EqOn (deriv f) (fun y => β * (h y ^ (β - 1) * deriv h y)) s := by
    intro y hy
    have hy' : s ∈ 𝓝 y := hs.mem_nhds hy
    rw [(hf.eventuallyEq_of_mem hy').deriv_eq, deriv_const_add,
      deriv_cpow_const (hh.differentiableAt hy') (hslit y hy), mul_assoc]
  have hzs : s ∈ 𝓝 z := hs.mem_nhds hz
  have hhz : DifferentiableAt ℂ h z := hh.differentiableAt hzs
  have hpow : h z ^ (β - 1) ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (slitPlane_ne_zero (hslit z hz)))
  have hdh' : DifferentiableAt ℂ (deriv h) z := ((hh.analyticAt hzs).deriv).differentiableAt
  rw [(logDeriv_congr_nhds (hderiv.eventuallyEq_of_mem hzs)).eq_of_nhds, logDeriv_const_mul _ _ hβ,
    logDeriv_fun_mul z hpow hdh (hhz.cpow_const (hslit z hz)) hdh',
    logDeriv_fun_cpow hhz (hslit z hz)]

/-- **The residue asymptotic of the pre-Schwarzian derivative at a corner.**  If the
holomorphic base `h` has a simple zero at `p` and `f` agrees with `w + h ^ β` on an open set `s`
avoiding the branch cut, and `s` nontrivially approaches `p`, then
`(z - p) * logDeriv (deriv f) z` tends to `β - 1` as `z` tends to `p` inside `s`.  The exponent
`β` is thus the residue of the pre-Schwarzian derivative at the corner, shifted by one. -/
theorem tendsto_sub_mul_logDeriv_deriv_of_eqOn_add_cpow {U : Set ℂ} (hU : IsOpen U) (hpU : p ∈ U)
    (hh : DifferentiableOn ℂ h U) (hhp : h p = 0) (hdh : deriv h p ≠ 0) (hs : IsOpen s)
    (_hne : (𝓝[s] p).NeBot) (hsU : s ⊆ U) (hslit : ∀ z ∈ s, h z ∈ slitPlane) (hβ : β ≠ 0)
    (hf : EqOn f (fun z => w + h z ^ β) s) :
    Tendsto (fun z => (z - p) * logDeriv (deriv f) z) (𝓝[s] p) (𝓝 (β - 1)) := by
  have hAn : AnalyticAt ℂ h p := hh.analyticAt (hU.mem_nhds hpU)
  -- The base vanishes at `p`, so `p` avoids the branch cut only by leaving `s`.
  have hps : p ∉ s := fun hp => by simpa [hhp, slitPlane] using hslit p hp
  have hle : 𝓝[s] p ≤ 𝓝[≠] p :=
    nhdsWithin_mono p fun z hz hzp => hps (Set.mem_of_eq_of_mem hzp.symm hz)
  have hbase : Tendsto (fun z => (z - p) * logDeriv h z) (𝓝[s] p) (𝓝 1) :=
    (hAn.tendsto_mul_logDeriv_simple_zero hhp hdh).mono_left hle
  -- `logDeriv (deriv h) = deriv (deriv h) / deriv h`, continuous at `p` since `deriv h p ≠ 0`.
  have hcont : ContinuousAt (logDeriv (deriv h)) p := by
    simpa only [logDeriv, Pi.div_def] using
      hAn.deriv.deriv.continuousAt.div hAn.deriv.continuousAt hdh
  have hsub : Tendsto (fun z : ℂ => z - p) (𝓝[s] p) (𝓝 0) := by
    have hp : Tendsto (fun z : ℂ => z - p) (𝓝 p) (𝓝 (p - p)) :=
      (continuous_id.sub continuous_const).continuousAt
    simpa using hp.mono_left nhdsWithin_le_nhds
  have hrest : Tendsto (fun z => (z - p) * logDeriv (deriv h) z) (𝓝[s] p) (𝓝 0) := by
    simpa using hsub.mul (hcont.tendsto.mono_left nhdsWithin_le_nhds)
  have hmem : {z : ℂ | deriv h z ≠ 0} ∈ 𝓝[s] p :=
    mem_nhdsWithin_of_mem_nhds (hAn.deriv.continuousAt.eventually_ne hdh)
  refine Tendsto.congr' ?_ (by simpa using (hbase.const_mul (β - 1)).add hrest)
  filter_upwards [self_mem_nhdsWithin, hmem] with z hz hdhz
  rw [logDeriv_deriv_of_eqOn_add_cpow hs (hh.mono hsU) hslit hβ hf hz hdhz]
  ring

end Corner

end TauCeti
