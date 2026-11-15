/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.WindingPhase
import TauCeti.Analysis.Calculus.ContDiff.Bounds
import TauCeti.Analysis.PDE.Vortex.FramedGauge.DerivativeDecay
import TauCeti.Analysis.SpecialFunctions.Exp.Shift
import TauCeti.Topology.Compactness.Compact

/-!
# Smooth framed vortices in the affine Sobolev field space

Let `x` be a plane vortex with `C²` section and `|α| → 1` at infinity whose section is normalized at
its end, equal outside a compact set to `|α|` times the winding phase `(z / |z|)^m`. In the
winding-`m` end trivialization, `y = gaugeTransform (windingPhase m)⁻¹ x` is smooth near infinity
(`TauCeti.Vortex.eventually_contDiffAt_gaugeTransform_inv`) and every iterated derivative of
`y - vacuumField` is `O(exp (-c |z|))` for every rate `c < 1 / 2`
(`TauCeti.Vortex.isBigO_iteratedFDeriv_gaugeTransform_inv_sub_vacuumField`). Outside the cutoff disc
of `referenceField f m`, the reference field has end trivialization `vacuumField`
(`TauCeti.Vortex.gaugeTransform_inv_windingPhase_referenceField`) and section `windingPhase m`
(`TauCeti.Vortex.referenceSection_eq_phase`), so `x - referenceField f m` is recovered from
`y - vacuumField` by rotating its section variation by `referenceSection f m`, whose iterated
derivatives are globally bounded (`TauCeti.Vortex.exists_norm_iteratedFDeriv_referenceSection_le`).
Every iterated derivative of `x - referenceField f m` is therefore `O(exp (-c |z|))` at infinity for
every `c < 1 / 2` (`TauCeti.Vortex.isBigO_iteratedFDeriv_sub_referenceField_apply`,
`TauCeti.Vortex.isBigO_iteratedFDeriv_sub_referenceField`), and globally bounded at order `n` by
`K exp (-c |z|)` when `x` is `C^n`
(`TauCeti.Vortex.exists_norm_iteratedFDeriv_sub_referenceField_le_mul_exp`).

When `x` is smooth, each coordinate of `x - referenceField f m` lies in `realSobolevFunctions` by
`TemperedDistribution.mem_realSobolevFunctions_of_isBigO_iteratedFDeriv_exp`, so `x` belongs to the
affine Sobolev model `framedFieldSpace f m s` at every real order `s`
(`TauCeti.Vortex.mem_framedFieldSpace_of_sectionValue_eq_mul_windingPhase`). Combining with the
end-phase normalization `TauCeti.Vortex.exists_framedGaugeGroup_sectionValue_smul_eq` shows that
every smooth degree-`m` framed plane vortex has a smooth framed gauge transform lying in
`framedFieldSpace f m s` for every `f` and `s`, with exponential decay of all iterated derivatives
(`TauCeti.Vortex.exists_framedGaugeGroup_smul_mem_framedFieldSpace_norm_iteratedFDeriv_le_mul_exp`).
Note that the normalizing smooth framed gauge need only tend to `1` at infinity (for instance with a
`1 / |z|` tail) and need not itself lie in a Sobolev gauge group; only the normalized representative
lies in `A_m^s`.

## Main results

* `TauCeti.Vortex.isBigO_iteratedFDeriv_sub_referenceField_apply`,
  `TauCeti.Vortex.isBigO_iteratedFDeriv_sub_referenceField`: for a plane vortex with `C²` section,
  `|α| → 1`, and section equal to `|α|` times `windingPhase m` near infinity, every iterated
  derivative of `x - referenceField f m` (and of each coordinate) is `O(exp (-c |z|))` at infinity
  for every `c < 1 / 2`.
* `TauCeti.Vortex.exists_norm_iteratedFDeriv_sub_referenceField_le_mul_exp`: when `x` is `C^n` with
  `C²` section, `‖Dⁿ(x - referenceField f m)(z)‖ ≤ K exp (-c |z|)` on the whole plane.
* `TauCeti.Vortex.mem_framedFieldSpace_of_sectionValue_eq_mul_windingPhase`: a smooth
  end-normalized vortex lies in `framedFieldSpace f m s` for every cutoff `f` and order `s : ℝ`.
* `TauCeti.Vortex.exists_framedGaugeGroup_smul_mem_framedFieldSpace_norm_iteratedFDeriv_le_mul_exp`:
  every smooth framed degree-`m` vortex has a smooth framed gauge representative lying in
  `framedFieldSpace f m s` for all `f` and `s` whose difference from `referenceField f m` decays
  exponentially with all derivatives.

## References

* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III.
* C. H. Taubes, *Arbitrary N-vortex solutions to the first order Ginzburg–Landau equations*,
  Comm. Math. Phys. 72 (1980), 277–292.
-/

public section

noncomputable section

namespace TauCeti.Vortex

open Asymptotics Complex Filter
open scoped ContDiff Topology

variable {x : ℂ → EuclideanSpace ℝ (Fin 4)} {m : ℕ}

/-! ### Exponential decay of all derivatives of an end-normalized vortex -/

/-- Rotating the section coordinates of a smooth field `Y` by `referenceSection f m` preserves
smoothness and `O(ρ)` bounds on iterated derivatives at infinity. -/
private theorem contDiff_and_isBigO_iteratedFDeriv_referenceSection
    {Y : ℂ → EuclideanSpace ℝ (Fin 4)} (hY : ContDiff ℝ ∞ Y) (f : ContDiffBump (0 : ℝ)) (m : ℕ) :
    ContDiff ℝ ∞ (fun z ↦ !₂[Y z 0, Y z 1,
      (referenceSection f m z).re * Y z 2 - (referenceSection f m z).im * Y z 3,
      (referenceSection f m z).im * Y z 2 + (referenceSection f m z).re * Y z 3]) ∧
    ∀ {ρ : ℂ → ℝ}, (∀ j, iteratedFDeriv ℝ j Y =O[cocompact ℂ] ρ) → ∀ n : ℕ,
      iteratedFDeriv ℝ n (fun z ↦ !₂[Y z 0, Y z 1,
        (referenceSection f m z).re * Y z 2 - (referenceSection f m z).im * Y z 3,
        (referenceSection f m z).im * Y z 2 + (referenceSection f m z).re * Y z 3])
        =O[cocompact ℂ] ρ := by
  set s := referenceSection f m
  set G : ℂ → EuclideanSpace ℝ (Fin 4) := fun z ↦
    !₂[Y z 0, Y z 1,
      (s z).re * Y z 2 - (s z).im * Y z 3,
      (s z).im * Y z 2 + (s z).re * Y z 3]
  have hYc_cd (k : Fin 4) : ContDiff ℝ ∞ (fun z ↦ Y z k) := contDiff_euclidean.1 hY k
  have hs_cd : ContDiff ℝ ∞ s := contDiff_referenceSection f m
  have hr : ContDiff ℝ ∞ (fun z ↦ (s z).re) := reCLM.contDiff.comp hs_cd
  have hi : ContDiff ℝ ∞ (fun z ↦ (s z).im) := imCLM.contDiff.comp hs_cd
  have hG : ContDiff ℝ ∞ G := by
    refine contDiff_euclidean.2 fun i ↦ ?_
    match i with
    | 0 => simpa only [G, Fin.isValue, Matrix.cons_val] using hYc_cd 0
    | 1 => simpa only [G, Fin.isValue, Matrix.cons_val] using hYc_cd 1
    | 2 =>
      simpa only [G, Fin.isValue, Matrix.cons_val] using
        (hr.mul (hYc_cd 2)).sub (hi.mul (hYc_cd 3))
    | 3 =>
      simpa only [G, Fin.isValue, Matrix.cons_val] using
        (hi.mul (hYc_cd 2)).add (hr.mul (hYc_cd 3))
  refine ⟨hG, fun {ρ} hY_dec n ↦ ?_⟩
  have hYc_dec (k : Fin 4) (j : ℕ) : iteratedFDeriv ℝ j (fun z ↦ Y z k) =O[cocompact ℂ] ρ :=
    (EuclideanSpace.proj k).isBigO_iteratedFDeriv_comp_left hY (by simp) (hY_dec j)
  have hmul (ℓ : ℂ →L[ℝ] ℝ) (k : Fin 4) :
      iteratedFDeriv ℝ n (fun z ↦ ℓ (s z) * Y z k) =O[cocompact ℂ] ρ := by
    have hℓs_bdd (j : ℕ) :
        iteratedFDeriv ℝ j (fun z ↦ ℓ (s z)) =O[cocompact ℂ] fun _ ↦ (1 : ℝ) := by
      obtain ⟨C, hC⟩ := exists_norm_iteratedFDeriv_referenceSection_le f m j
      exact ℓ.isBigO_iteratedFDeriv_comp_left hs_cd (by simp)
        (IsBigO.of_bound (max C 0) (Eventually.of_forall fun z ↦ by
          simpa using (hC z).trans (le_max_left C 0)))
    simpa only [ContinuousLinearMap.mul_apply', Function.comp_apply, one_mul] using
      (ContinuousLinearMap.mul ℝ ℝ).isBigO_iteratedFDeriv_of_bilinear
        (ℓ.contDiff.comp hs_cd) (hYc_cd k) (by simp)
        (fun j _ ↦ hℓs_bdd j) (fun j _ ↦ hYc_dec k j)
  have hG_coord (i : Fin 4) : iteratedFDeriv ℝ n (fun z ↦ G z i) =O[cocompact ℂ] ρ := by
    match i with
    | 0 => simpa only [G, Fin.isValue, Matrix.cons_val] using hYc_dec 0 n
    | 1 => simpa only [G, Fin.isValue, Matrix.cons_val] using hYc_dec 1 n
    | 2 =>
      simp only [G, Fin.isValue, Matrix.cons_val]
      rw [fun_iteratedFDeriv_sub ((hr.mul (hYc_cd 2)).of_le (by simp))
        ((hi.mul (hYc_cd 3)).of_le (by simp))]
      exact (hmul reCLM 2).sub (hmul imCLM 3)
    | 3 =>
      simp only [G, Fin.isValue, Matrix.cons_val]
      rw [fun_iteratedFDeriv_add ((hi.mul (hYc_cd 2)).of_le (by simp))
        ((hr.mul (hYc_cd 3)).of_le (by simp))]
      exact (hmul imCLM 2).add (hmul reCLM 3)
  rw [← (PiLp.continuousLinearEquiv 2 ℝ fun _ : Fin 4 ↦ ℝ).isBigO_iteratedFDeriv_comp_left_iff,
    ((PiLp.continuousLinearEquiv 2 ℝ fun _ : Fin 4 ↦ ℝ).comp_contDiff_iff.2
      hG).isBigO_iteratedFDeriv_pi (by simp)]
  exact hG_coord

/-- Build a globally smooth exterior surrogate `G` that agrees on neighborhoods at infinity with
`x - referenceField f m` and has `O(exp (-c |z|))` derivatives for all `c < 1 / 2`, by rotating the
smooth end-trivialized surrogate `Y` by `referenceSection f m`. -/
private theorem exists_contDiff_eventuallyEq_sub_referenceField
    (hp : ContDiff ℝ 2 (fun w ↦ x w 2)) (hq : ContDiff ℝ 2 (fun w ↦ x w 3))
    (hsol : ∀ z, equation x z = 0)
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    (hphase : ∀ᶠ z in cocompact ℂ, sectionValue x z = ‖sectionValue x z‖ * windingPhase m z)
    (f : ContDiffBump (0 : ℝ)) :
    ∃ G : ℂ → EuclideanSpace ℝ (Fin 4), ContDiff ℝ ∞ G ∧
      (∀ᶠ z in cocompact ℂ, x - referenceField f m =ᶠ[𝓝 z] G) ∧
      ∀ {c : ℝ}, c < 1 / 2 → ∀ n,
        iteratedFDeriv ℝ n G =O[cocompact ℂ] fun z ↦ Real.exp (-(c * ‖z‖)) := by
  obtain ⟨Y, hY, hY_ev, hY_dec⟩ :=
    exists_contDiff_eventuallyEq_gaugeTransform_inv_sub_vacuumField hp hq hsol hlim hphase
  obtain ⟨hG_cd, hG_bigO⟩ := contDiff_and_isBigO_iteratedFDeriv_referenceSection hY f m
  refine ⟨_, hG_cd, TauCeti.eventually_cocompact_nhds.2 ?_, fun {c} hc n ↦ ?_⟩
  · filter_upwards [tendsto_norm_cocompact_atTop.eventually_gt_atTop (max 1 f.rOut), hY_ev]
      with z hzR hYz_nhds
    have hrOut : f.rOut ≤ ‖z‖ ^ 2 := rOut_le_norm_sq f hzR
    have hs_eq : referenceSection f m z = (windingPhase m z : ℂ) :=
      (referenceSection_eq_phase f m hrOut).trans
        (coe_windingPhase m (ne_zero_of_rOut_le_norm_sq f hrOut)).symm
    set V := gaugeLinearAction (windingPhase m)⁻¹ (x - referenceField f m)
    have hYz : Y z = V z := by
      have hsub := congrFun
        (gaugeTransform_sub_gaugeTransform (windingPhase m)⁻¹ x (referenceField f m)) z
      rw [Pi.sub_apply, gaugeTransform_inv_windingPhase_referenceField f m hrOut] at hsub
      exact hYz_nhds.eq_of_nhds.symm.trans hsub
    calc (x - referenceField f m) z
        = gaugeLinearAction (windingPhase m) V z := by
          rw [← gaugeLinearAction_gaugeLinearAction_inv (windingPhase m) (x - referenceField f m)]
      _ = _ := by simp only [gaugeLinearAction_apply, hs_eq, hYz]
  · exact (hG_bigO (fun j ↦ hY_dec (max_lt hc (by norm_num)) j) n).trans
      (isBigO_exp_neg_mul_norm_of_le (le_max_left c 0) _)

/-- **Coordinate derivative decay for an end-normalized vortex.** Let `x` be a plane vortex with
`C²` section, `|α| → 1` at infinity, and section equal to `|α|` times `windingPhase m` outside a
compact set. Then for every cutoff `f`, every rate `c < 1 / 2`, every coordinate `i`, and every
order `n`, `Dⁿ(xᵢ - (x_ref)ᵢ) = O(exp (-c |z|))` at infinity. No global regularity assumption on
the connection components of `x` is needed. -/
theorem isBigO_iteratedFDeriv_sub_referenceField_apply
    (hp : ContDiff ℝ 2 (fun w ↦ x w 2)) (hq : ContDiff ℝ 2 (fun w ↦ x w 3))
    (hsol : ∀ z, equation x z = 0)
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    (hphase : ∀ᶠ z in cocompact ℂ, sectionValue x z = ‖sectionValue x z‖ * windingPhase m z)
    (f : ContDiffBump (0 : ℝ)) {c : ℝ} (hc : c < 1 / 2) (i : Fin 4) (n : ℕ) :
    iteratedFDeriv ℝ n (fun z ↦ x z i - referenceField f m z i) =O[cocompact ℂ]
      fun z ↦ Real.exp (-(c * ‖z‖)) := by
  obtain ⟨G, hG, hG_ev, hG_dec⟩ :=
    exists_contDiff_eventuallyEq_sub_referenceField hp hq hsol hlim hphase f
  refine ((EuclideanSpace.proj i).isBigO_iteratedFDeriv_comp_left hG (by simp)
    (hG_dec hc n)).congr' ?_ EventuallyEq.rfl
  filter_upwards [hG_ev] with z hz
  have hc_nhds : (fun w ↦ G w i) =ᶠ[𝓝 z] fun w ↦ x w i - referenceField f m w i :=
    hz.symm.mono fun _ hw ↦ congrArg (fun v : EuclideanSpace ℝ (Fin 4) ↦ v i) hw
  exact (hc_nhds.iteratedFDeriv ℝ n).eq_of_nhds

/-- **Derivative decay of an end-normalized vortex.** Let `x` be a plane vortex with `C²`
section, `|α| → 1` at infinity, and section equal to `|α|` times `windingPhase m` outside a compact
set. Then for every cutoff `f`, every rate `c < 1 / 2`, and every order `n`,
`Dⁿ(x - referenceField f m) = O(exp (-c |z|))` at infinity. -/
theorem isBigO_iteratedFDeriv_sub_referenceField
    (hp : ContDiff ℝ 2 (fun w ↦ x w 2)) (hq : ContDiff ℝ 2 (fun w ↦ x w 3))
    (hsol : ∀ z, equation x z = 0)
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    (hphase : ∀ᶠ z in cocompact ℂ, sectionValue x z = ‖sectionValue x z‖ * windingPhase m z)
    (f : ContDiffBump (0 : ℝ)) {c : ℝ} (hc : c < 1 / 2) (n : ℕ) :
    iteratedFDeriv ℝ n (x - referenceField f m) =O[cocompact ℂ]
      fun z ↦ Real.exp (-(c * ‖z‖)) := by
  obtain ⟨G, -, hG_ev, hG_dec⟩ :=
    exists_contDiff_eventuallyEq_sub_referenceField hp hq hsol hlim hphase f
  exact (hG_dec hc n).congr'
    (hG_ev.mono fun _ hz ↦ (hz.iteratedFDeriv ℝ n).eq_of_nhds.symm) EventuallyEq.rfl

/-- **Global exponential decay of the `n`-th derivative of an end-normalized vortex.** For a `C^n`
plane vortex with `C²` section and `|α| → 1` at infinity whose section equals `|α|` times
`windingPhase m` outside a compact set, the order-`n` iterated derivative of
`x - referenceField f m` decays at every rate `c < 1 / 2`:
`‖Dⁿ(x - referenceField f m)(z)‖ ≤ K exp (-c |z|)`. -/
theorem exists_norm_iteratedFDeriv_sub_referenceField_le_mul_exp {n : ℕ} (hx : ContDiff ℝ n x)
    (hp : ContDiff ℝ 2 (fun w ↦ x w 2)) (hq : ContDiff ℝ 2 (fun w ↦ x w 3))
    (hsol : ∀ z, equation x z = 0)
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    (hphase : ∀ᶠ z in cocompact ℂ, sectionValue x z = ‖sectionValue x z‖ * windingPhase m z)
    (f : ContDiffBump (0 : ℝ)) {c : ℝ} (hc : c < 1 / 2) :
    ∃ K, ∀ z, ‖iteratedFDeriv ℝ n (x - referenceField f m) z‖ ≤ K * Real.exp (-(c * ‖z‖)) := by
  obtain ⟨K, hK⟩ := (isBigO_iteratedFDeriv_sub_referenceField hp hq hsol hlim hphase f hc n).bound
  have hcont : Continuous fun z ↦ ‖iteratedFDeriv ℝ n (x - referenceField f m) z‖ :=
    ((hx.sub ((contDiff_referenceField f m).of_le (by simp))).continuous_iteratedFDeriv
      le_rfl).norm
  refine exists_forall_le_mul_exp_of_eventually_le hcont (K := K) ?_
  filter_upwards [hK] with z hz
  simpa [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using hz

/-- **Sobolev membership of a smooth end-normalized vortex.** A smooth plane vortex with `|α| → 1`
at infinity whose section equals `|α|` times `windingPhase m` outside a compact set lies in the
affine Sobolev field space `framedFieldSpace f m s` for every cutoff `f` and real order `s`. -/
theorem mem_framedFieldSpace_of_sectionValue_eq_mul_windingPhase (hx : ContDiff ℝ ∞ x)
    (hsol : ∀ z, equation x z = 0)
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    (hphase : ∀ᶠ z in cocompact ℂ, sectionValue x z = ‖sectionValue x z‖ * windingPhase m z)
    (f : ContDiffBump (0 : ℝ)) (s : ℝ) :
    x ∈ framedFieldSpace f m s := by
  rw [mem_framedFieldSpace, mem_sobolevFields]
  intro i
  have hcoord : ContDiff ℝ ∞ fun z ↦ (x - referenceField f m) z i :=
    (contDiff_euclidean.1 hx i).sub (contDiff_euclidean.1 (contDiff_referenceField f m) i)
  exact TemperedDistribution.mem_realSobolevFunctions_of_isBigO_iteratedFDeriv_exp hcoord
    (c := 1 / 4) (by norm_num)
    (isBigO_iteratedFDeriv_sub_referenceField_apply
      ((contDiff_euclidean.1 hx 2).of_le (by simp)) ((contDiff_euclidean.1 hx 3).of_le (by simp))
      hsol hlim hphase f (by norm_num) i) s

/-! ### Smooth framed gauge representatives in `A_m^s` -/

/-- **Smooth framed gauge representative in `A_m^s` with all-order exponential decay.** Every
smooth plane vortex with the degree-`m` end framing `α(z) (z / |z|)⁻ᵐ → 1` has a smooth framed
gauge transform `u • x` whose section is `|α|` times `windingPhase m` outside a compact set, which
belongs to `framedFieldSpace f m s` for every cutoff `f` and real order `s`, and whose difference
from `referenceField f m` has all iterated derivatives globally bounded by multiples of
`exp (-c |z|)` for every `f` and every rate `c < 1 / 2`. -/
theorem exists_framedGaugeGroup_smul_mem_framedFieldSpace_norm_iteratedFDeriv_le_mul_exp
    (hx : ContDiff ℝ ∞ x) (hsol : ∀ z, equation x z = 0)
    (hframe : Tendsto (fun z ↦ sectionValue x z * ((z / (‖z‖ : ℂ)) ^ m)⁻¹) (cocompact ℂ) (𝓝 1)) :
    ∃ u : framedGaugeGroup,
      (∀ᶠ z in cocompact ℂ,
        sectionValue (u • x) z = ‖sectionValue (u • x) z‖ * windingPhase m z) ∧
      (∀ (f : ContDiffBump (0 : ℝ)) (s : ℝ), u • x ∈ framedFieldSpace f m s) ∧
      ∀ (f : ContDiffBump (0 : ℝ)), ∀ c < 1 / 2, ∀ n : ℕ, ∃ K, ∀ z,
        ‖iteratedFDeriv ℝ n (u • x - referenceField f m) z‖ ≤ K * Real.exp (-(c * ‖z‖)) := by
  obtain ⟨u, hu⟩ := exists_framedGaugeGroup_sectionValue_smul_eq hx hframe
  have hy := contDiff_framedGaugeGroup_smul u hx
  have hsol' (z : ℂ) : equation (u • x) z = 0 :=
    (equation_framedGaugeGroup_smul_eq_zero_iff u
      (hx.contDiffAt.differentiableAt (by simp))).2 (hsol z)
  have hlim := tendsto_normSq_of_tendsto_sectionValue_mul_inv_pow
    (tendsto_sectionValue_framedGaugeGroup_smul u hframe)
  exact ⟨u, hu,
    fun f s ↦ mem_framedFieldSpace_of_sectionValue_eq_mul_windingPhase hy hsol' hlim hu f s,
    fun f _ hc n ↦ exists_norm_iteratedFDeriv_sub_referenceField_le_mul_exp (hy.of_le (by simp))
      ((contDiff_euclidean.1 hy 2).of_le (by simp)) ((contDiff_euclidean.1 hy 3).of_le (by simp))
      hsol' hlim hu f hc⟩

end TauCeti.Vortex
