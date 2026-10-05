/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.LogDeriv
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.CauchyIntegral
import TauCeti.Analysis.SpecialFunctions.Pow.LogDeriv
import TauCeti.Analysis.Complex.AtInfinity
import TauCeti.Analysis.Complex.UpperHalfPlane.Topology

/-!
# The pre-Schwarzian derivative: composition, rigidity, and asymptotics

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
residue `α / π - 1` to the Schwarz--Christoffel partial-fraction identity.  The exponent `β = 0`
is played by a **logarithm** `f` of `h`, `exp ∘ f = h`: its pre-Schwarzian is
`logDeriv (deriv h) - logDeriv h`, with residue asymptotic `-1` at a simple zero of `h`.

The chain rule describes the effect of changing the source coordinate. In particular, if `g` is
holomorphic near zero with `g'(0) ≠ 0`, the map `f z = g (-1 / z)` satisfies
`z * f''(z) / f'(z) → -2` at infinity. Thus its pre-Schwarzian tends to zero, the decay condition
needed to identify a meromorphic pre-Schwarzian by its finite poles and residues.

## Main results

* `TauCeti.exists_eqOn_const_mul_add_iff_logDeriv_deriv_eqOn` -- two holomorphic functions with
  nonvanishing derivatives on a domain have the same pre-Schwarzian derivative exactly when one
  is `w ↦ a * w + b` applied to the other, for some `a ≠ 0`.
* `TauCeti.logDeriv_deriv_of_eqOn_add_cpow` -- the pre-Schwarzian derivative of a corner power.
* `TauCeti.tendsto_sub_mul_logDeriv_deriv_of_eqOn_add_cpow` -- at a simple zero of the base, the
  pre-Schwarzian derivative of a corner power has residue asymptotic `β - 1`.
* `TauCeti.logDeriv_deriv_of_eqOn_exp` and `TauCeti.tendsto_sub_mul_logDeriv_deriv_of_eqOn_exp` --
  the same for a logarithm, with residue asymptotic `-1`.
* `TauCeti.logDeriv_deriv_comp` -- the pre-Schwarzian chain rule.
* `TauCeti.tendsto_logDeriv_deriv_comp_neg_inv` -- decay at infinity for a map regular in the
  inverse coordinate.
* `TauCeti.tendsto_mul_logDeriv_deriv_of_tendsto_mul_logDeriv_deriv_neg_inv` -- a residue
  asymptotic `L` at `0` in the normalized inverse coordinate gives `-L - 2` at infinity.

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
  exact tendsto_zero_of_tendsto_mul_cobounded le_rfl
    (tendsto_mul_logDeriv_deriv_comp_neg_inv hg hgn)

open Bornology _root_.UpperHalfPlane in
/-- The pre-Schwarzian chain rule at infinity, as a limit.  Read the map `f` of the upper
half-plane in the coordinate `w ↦ -1 / w` and normalize the target by `w ↦ (w - c) / b`.  If the
pre-Schwarzian of the result has the residue asymptotic `w * F''(w) / F'(w) → L` as `w` tends to
`0` in the upper half of a ball, then `z * f''(z) / f'(z) → -L - 2` at infinity. -/
theorem tendsto_mul_logDeriv_deriv_of_tendsto_mul_logDeriv_deriv_neg_inv
    {f : ℂ → ℂ} {c b L : ℂ} {r : ℝ} (hr : 0 < r) (hb : b ≠ 0)
    (hf : DifferentiableOn ℂ f upperHalfPlaneSet)
    (hfn : ∀ z ∈ upperHalfPlaneSet, deriv f z ≠ 0)
    (hL : Tendsto (fun w => w * logDeriv (deriv fun w => (f (-w⁻¹) - c) / b) w)
      (𝓝[Metric.ball 0 r ∩ upperHalfPlaneSet] 0) (𝓝 L)) :
    Tendsto (fun z : ℂ => z * logDeriv (deriv f) z)
      (cobounded ℂ ⊓ 𝓟 upperHalfPlaneSet) (𝓝 (-L - 2)) := by
  set s := Metric.ball (0 : ℂ) r ∩ upperHalfPlaneSet
  have hchain : ∀ w ∈ s, logDeriv (deriv fun w => (f (-w⁻¹) - c) / b) w =
      logDeriv (deriv f) (-w⁻¹) / w ^ 2 - 2 / w := by
    intro w hw
    have hw0 : w ≠ 0 := fun h0 => by simpa [h0] using hw.2
    have hz : -w⁻¹ ∈ upperHalfPlaneSet := im_neg_inv_pos.mpr hw.2
    have hderiv : (deriv fun w : ℂ => (f (-w⁻¹) - c) / b) =
        fun w => deriv (fun w : ℂ => f (-w⁻¹)) w / b := by
      ext w
      simp only [deriv_div_const, deriv_sub_const]
    rw [hderiv]
    simp only [div_eq_mul_inv (deriv _ _), logDeriv_mul_const w b⁻¹ (inv_ne_zero hb)]
    exact logDeriv_deriv_comp_neg_inv (hf.analyticAt (isOpen_upperHalfPlaneSet.mem_nhds hz))
      (hfn _ hz) hw0
  have h0 : Tendsto (fun z : ℂ => -z⁻¹) (cobounded ℂ ⊓ 𝓟 upperHalfPlaneSet) (𝓝 0) := by
    simpa using ((tendsto_inv₀_cobounded (α := ℂ)).neg).mono_left inf_le_left
  have hT : Tendsto (fun z : ℂ => -z⁻¹) (cobounded ℂ ⊓ 𝓟 upperHalfPlaneSet) (𝓝[s] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨h0, ?_⟩
    filter_upwards [h0.eventually (Metric.ball_mem_nhds 0 hr),
      mem_inf_of_right (mem_principal_self upperHalfPlaneSet)] with z hz hzH
    exact ⟨hz, im_neg_inv_pos.mpr hzH⟩
  refine (((hL.comp hT).neg).sub_const 2).congr' ?_
  filter_upwards [hT.eventually self_mem_nhdsWithin,
    mem_inf_of_right (mem_principal_self upperHalfPlaneSet)] with z hz hzH
  have hz0 : z ≠ 0 := fun h0 => by simp [h0] at hzH
  simp only [Function.comp_apply, hchain _ hz, inv_neg, inv_inv, neg_neg]
  field_simp
  ring

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

/-- **The pre-Schwarzian derivative of a logarithm.**  Where the holomorphic function `f` is a
logarithm of `h` on an open set, `exp ∘ f = h`, the pre-Schwarzian derivative of `f` is
`logDeriv (deriv h) - logDeriv h`.  This is the exponent `β = 0` counterpart of
`TauCeti.logDeriv_deriv_of_eqOn_add_cpow`. -/
theorem logDeriv_deriv_of_eqOn_exp (hs : IsOpen s) (hf : DifferentiableOn ℂ f s)
    (hexp : EqOn (fun z => exp (f z)) h s) {z : ℂ} (hz : z ∈ s) (hdh : deriv h z ≠ 0) :
    logDeriv (deriv f) z = logDeriv (deriv h) z - logDeriv h z := by
  have hh : DifferentiableOn ℂ h s := hf.cexp.congr fun y hy => (hexp hy).symm
  -- `h' = exp f * f' = h * f'`, so `f'` is the logarithmic derivative of `h`
  have hderiv : EqOn (deriv f) (fun y => deriv h y / h y) s := by
    intro y hy
    have hy' : s ∈ 𝓝 y := hs.mem_nhds hy
    beta_reduce
    rw [← (hexp.eventuallyEq_of_mem hy').deriv_eq, deriv_cexp (hf.differentiableAt hy'),
      ← hexp hy, mul_div_cancel_left₀ _ (exp_ne_zero _)]
  have hzs : s ∈ 𝓝 z := hs.mem_nhds hz
  have hAn : AnalyticAt ℂ h z := hh.analyticAt hzs
  have hhz : h z ≠ 0 := hexp hz ▸ exp_ne_zero _
  rw [(logDeriv_congr_nhds (hderiv.eventuallyEq_of_mem hzs)).eq_of_nhds,
    logDeriv_fun_div z hdh hhz hAn.deriv.differentiableAt hAn.differentiableAt]

/-- **The residue asymptotic of the pre-Schwarzian derivative of a logarithm.**  If `h` has a
simple zero at `p` and the holomorphic function `f` is a logarithm of `h` on an open set `s`, then
`(z - p) * logDeriv (deriv f) z` tends to `-1` as `z` tends to `p` inside `s`.  This is the
exponent `β = 0` counterpart of `TauCeti.tendsto_sub_mul_logDeriv_deriv_of_eqOn_add_cpow`: a
logarithm opens a straight edge through `p` into a parallel-sided end at infinity. -/
theorem tendsto_sub_mul_logDeriv_deriv_of_eqOn_exp (hh : AnalyticAt ℂ h p) (hhp : h p = 0)
    (hdh : deriv h p ≠ 0) (hs : IsOpen s) (hf : DifferentiableOn ℂ f s)
    (hexp : EqOn (fun z => exp (f z)) h s) :
    Tendsto (fun z => (z - p) * logDeriv (deriv f) z) (𝓝[s] p) (𝓝 (-1)) := by
  -- `h` has no zero on `s`, where it is an exponential, so `p ∉ s`.
  have hps : p ∉ s := fun hp => exp_ne_zero (f p) ((hexp hp).trans hhp)
  have hle : 𝓝[s] p ≤ 𝓝[≠] p :=
    nhdsWithin_mono p fun z hz hzp => hps (Set.mem_of_eq_of_mem hzp.symm hz)
  have hbase : Tendsto (fun z => (z - p) * logDeriv h z) (𝓝[s] p) (𝓝 1) :=
    (hh.tendsto_mul_logDeriv_simple_zero hhp hdh).mono_left hle
  -- `logDeriv (deriv h) = deriv (deriv h) / deriv h`, continuous at `p` since `deriv h p ≠ 0`.
  have hcont : ContinuousAt (logDeriv (deriv h)) p := by
    simpa only [logDeriv, Pi.div_def] using
      hh.deriv.deriv.continuousAt.div hh.deriv.continuousAt hdh
  have hsub : Tendsto (fun z : ℂ => z - p) (𝓝[s] p) (𝓝 0) := by
    have hp : Tendsto (fun z : ℂ => z - p) (𝓝 p) (𝓝 (p - p)) :=
      (continuous_id.sub continuous_const).continuousAt
    simpa using hp.mono_left nhdsWithin_le_nhds
  have hrest : Tendsto (fun z => (z - p) * logDeriv (deriv h) z) (𝓝[s] p) (𝓝 0) := by
    simpa using hsub.mul (hcont.tendsto.mono_left nhdsWithin_le_nhds)
  have hmem : {z : ℂ | deriv h z ≠ 0} ∈ 𝓝[s] p :=
    mem_nhdsWithin_of_mem_nhds (hh.deriv.continuousAt.eventually_ne hdh)
  refine Tendsto.congr' ?_ (by simpa using hrest.sub hbase)
  filter_upwards [self_mem_nhdsWithin, hmem] with z hz hdhz
  rw [logDeriv_deriv_of_eqOn_exp hs hf hexp hz hdhz]
  ring

end Corner

end TauCeti
