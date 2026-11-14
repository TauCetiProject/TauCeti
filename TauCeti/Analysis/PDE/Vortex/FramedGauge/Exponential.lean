/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.FunctionalSpaces.BesselPotentialSpace
public import TauCeti.Analysis.PDE.Vortex.FramedGauge.Sobolev
import TauCeti.Analysis.Sobolev.BesselPotential.Embedding
import TauCeti.Analysis.Sobolev.BesselPotential.PowerSeries
import TauCeti.Analysis.SpecialFunctions.Complex.Circle.Lp
import TauCeti.MeasureTheory.Measure.OpenPos

/-!
# The exponential map of the Sobolev framed gauge group

For a real order `s > 1`, the Sobolev framed gauge group `G_s` (`sobolevGaugeGroup`) consists of
the continuous circle-valued maps `u` on the plane with `u - 1 ∈ H^s(ℂ; ℂ)`. This file studies the
exponential `f ↦ exp (i f)` on continuous real phases `f ∈ H^s(ℂ; ℝ)`, and proves the
ingredients of a chart of `G_s` at the identity modelled on `H^s(ℂ; ℝ)`.

* **The exponential lands in `G_s`.** For a continuous real `f ∈ H^s`, the gauge `exp (i f)` lies
  in `G_s` (`TauCeti.Vortex.exp_mem_sobolevGaugeGroup`), because `cos f - 1` and `sin f` lie in
  `H^s` (`TemperedDistribution.cos_sub_one_mem_realSobolevFunctions`,
  `TemperedDistribution.sin_mem_realSobolevFunctions`).
* **It is injective.** Two continuous real phases in `H^s` with the same exponential are equal
  (`TauCeti.Vortex.injOn_exp`): their difference takes values in `2πℤ`, so it is constant on the
  connected plane, and it tends to zero at infinity by the Sobolev embedding.
* **Its image contains an `H^s` neighbourhood of the identity.** There is `δ > 0` such that every
  `u ∈ G_s` with `‖u - 1‖_{H^s} < δ` is `exp (i f)` for a continuous real `f ∈ H^s`
  (`TauCeti.Vortex.exists_continuous_mem_realSobolevFunctions_eq_exp`). The proof takes
  `f = arg u`: here `log u = log (1 + (u - 1))` is the logarithm series in `u - 1`, which
  converges in `H^s` once `‖u - 1‖_{H^s}` is small
  (`TemperedDistribution.exists_memSobolev_ae_eq_log_one_add`), and `log u = i arg u` because
  `|u| = 1`.
* **It is locally Lipschitz in `H^s` coordinates.** If the complexified phases `F, G` have
  `H^s` norm at most `R`, then `‖(exp (i f) - 1) - (exp (i g) - 1)‖_{H^s} ≤ exp (C R) ‖F - G‖_{H^s}`
  (`TauCeti.Vortex.exists_norm_toBesselPotentialSpace_sub_le_of_ae_eq_exp`), by the Lipschitz
  estimate for the exponential series on `H^s`
  (`TemperedDistribution.exists_norm_toBesselPotentialSpace_sub_le_of_ae_eq_exp_sub_one`).
* **Its inverse is Lipschitz near the identity.** If `‖u - 1‖_{H^s}, ‖u' - 1‖_{H^s} ≤ R` with
  `C R < 1`, then the phases `arg u, arg u'` lie in `H^s` and
  `‖arg u - arg u'‖_{H^s} ≤ (1 - C R)⁻¹ ‖u - u'‖_{H^s}`
  (`TauCeti.Vortex.exists_memSobolev_ae_eq_arg_and_norm_sub_le`), since
  `i arg u = log (1 + (u - 1))` and the logarithm series is Lipschitz on `H^s`
  (`TemperedDistribution.exists_norm_toBesselPotentialSpace_sub_le_of_ae_eq_log_one_add`).

Since `G_s` is abelian and `exp (i (f + g)) = exp (i f) exp (i g)`, the exponential is an
injective homomorphism from the additive group of continuous real `H^s` phases into `G_s`, whose
image contains every element of `G_s` that is `H^s`-close to `1`. In the coordinates `F` of the
phase and `u - 1` of the gauge, the exponential is Lipschitz on `H^s` balls about `0`, and the
phase `arg u` lies in `H^s` and is Lipschitz in `u - 1` on small `H^s` balls about `0`. These are
the estimates for a chart of `G_s` at the identity; no topology or manifold structure on `G_s` is
constructed here.

## Main results

* `TauCeti.Vortex.exp_mem_sobolevGaugeGroup`: `exp (i f) ∈ G_s` for continuous real `f ∈ H^s`.
* `TauCeti.Vortex.injOn_exp`: the exponential is injective on continuous real `H^s` phases.
* `TauCeti.Vortex.exists_continuous_mem_realSobolevFunctions_eq_exp`: the elements of `G_s` close
  to `1` in `H^s` are exponentials of continuous real `H^s` phases.
* `TauCeti.Vortex.exists_norm_toBesselPotentialSpace_sub_le_of_ae_eq_exp`: the exponential is
  locally Lipschitz from `H^s` phases to `H^s` coordinates of gauges.
* `TauCeti.Vortex.exists_memSobolev_ae_eq_arg_and_norm_sub_le`: near the identity,
  the phase `arg u` lies in `H^s` and is Lipschitz in the coordinate `u - 1`.

## References

* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III.
* M. E. Taylor, *Partial Differential Equations III: Nonlinear Equations*, 2nd ed., Applied
  Mathematical Sciences 117, Springer, 2011, Chapter 13, Section 3.
-/

public section

noncomputable section

namespace TauCeti.Vortex

open Complex Filter MeasureTheory Module TemperedDistribution
open scoped Real Topology SchwartzMap

/-- **The exponential of a Sobolev phase is a Sobolev gauge.** For `s > 1` and a continuous real
function `f ∈ H^s(ℂ)`, the gauge `exp (i f)` lies in `G_s`. In particular this holds for smooth
compactly supported `f`. -/
theorem exp_mem_sobolevGaugeGroup {s : ℝ} (hs : 1 < s) {f : ℂ → ℝ} (hf : Continuous f)
    (hfs : f ∈ realSobolevFunctions ℂ s 2) :
    (fun z ↦ Circle.exp (f z)) ∈ sobolevGaugeGroup hs := by
  have hs' := finrank_real_complex_lt_two_mul hs
  refine (mem_sobolevGaugeGroup hs _).2 ⟨Circle.exp.continuous.comp hf, ?_, ?_⟩
  · simpa only [Circle.coe_exp, exp_ofReal_mul_I_re] using
      cos_sub_one_mem_realSobolevFunctions hs' hfs
  · simpa only [Circle.coe_exp, exp_ofReal_mul_I_im] using sin_mem_realSobolevFunctions hs' hfs

/-- **The exponential is injective on continuous Sobolev phases.** For `s > 1`, two continuous
real functions in `H^s(ℂ)` with the same exponential `exp (i f)` are equal. -/
theorem injOn_exp {s : ℝ} (hs : 1 < s) :
    Set.InjOn (fun (f : ℂ → ℝ) (z : ℂ) ↦ Circle.exp (f z))
      {f | Continuous f ∧ f ∈ realSobolevFunctions ℂ s 2} := by
  rintro f ⟨hf, hfs⟩ g ⟨hg, hgs⟩ hfg
  have hD : Continuous (f - g) := hf.sub hg
  -- `f - g` takes values in `2πℤ`, so it is constant on the connected plane.
  have hmaps : Set.MapsTo (f - g) Set.univ (AddSubgroup.zmultiples (2 * π) : Set ℝ) := by
    intro z _
    have h : Circle.exp ((f - g) z) = 1 := by
      rw [Pi.sub_apply, Circle.exp_sub]
      exact div_eq_one.2 (congrFun hfg z)
    obtain ⟨n, hn⟩ := Circle.exp_eq_one.1 h
    exact ⟨n, by simp [hn, zsmul_eq_mul]⟩
  have hconst (z w : ℂ) : (f - g) z = (f - g) w :=
    isPreconnected_univ.constant_of_mapsTo
      (isDiscrete_iff_discreteTopology.2 (NormedSpace.discreteTopology_zmultiples (2 * π)))
      hD.continuousOn hmaps (Set.mem_univ z) (Set.mem_univ w)
  -- `f - g` tends to zero at infinity, so the constant is zero.
  have hlim := tendsto_cocompact_of_mem_realSobolevFunctions (finrank_real_complex_lt_two_mul hs)
    (sub_mem hfs hgs) hD
  funext z
  exact sub_eq_zero.1 (tendsto_nhds_unique (tendsto_const_nhds.congr fun w ↦ hconst z w) hlim)

/-- **Elements of `G_s` near the identity are exponentials.** For `s > 1` there is `δ > 0` such
that every `u ∈ G_s` with `‖u - 1‖_{H^s} < δ` is `exp (i f)` for a continuous real function
`f ∈ H^s(ℂ)`. Here `u - 1` is represented by an `L²` function `h` in `H^s(ℂ; ℂ)`, as in
`exists_memSobolev_ae_eq_of_mem_sobolevGaugeGroup`. -/
theorem exists_continuous_mem_realSobolevFunctions_eq_exp {s : ℝ} (hs : 1 < s) :
    ∃ δ, 0 < δ ∧ ∀ u ∈ sobolevGaugeGroup hs, ∀ {h : Lp ℂ 2 (volume : Measure ℂ)},
      h =ᵐ[volume] (fun z ↦ (u z : ℂ) - 1) → ∀ hh : MemSobolev s 2 (h : 𝓢'(ℂ, ℂ)),
      ‖hh.toBesselPotentialSpace‖ < δ →
      ∃ f : ℂ → ℝ, Continuous f ∧ f ∈ realSobolevFunctions ℂ s 2 ∧
        u = fun z ↦ Circle.exp (f z) := by
  have hs' := finrank_real_complex_lt_two_mul hs
  obtain ⟨C, hC, hlog⟩ := exists_memSobolev_ae_eq_log_one_add hs'
  obtain ⟨C₂, hC₂, hsup⟩ :=
    exists_forall_ae_norm_le_mul_norm_toBesselPotentialSpace (E := ℂ) (F := ℂ) hs'
  refine ⟨(C + C₂ + 1)⁻¹, by positivity,
    fun u hu {h} hhu (hh : MemSobolev s 2 (h : 𝓢'(ℂ, ℂ))) hδ ↦ ?_⟩
  set R := ‖hh.toBesselPotentialSpace‖
  have hR0 : 0 ≤ R := norm_nonneg _
  have hR : (C + C₂ + 1) * R < 1 :=
    calc (C + C₂ + 1) * R < (C + C₂ + 1) * (C + C₂ + 1)⁻¹ := by gcongr
      _ = 1 := mul_inv_cancel₀ (by positivity)
  have hCR : C * R < 1 := by nlinarith
  have hC₂R : C₂ * R < 1 := by nlinarith
  obtain ⟨v, hv, hvs⟩ := hlog hh hCR
  have hu_cont : Continuous fun z ↦ (u z : ℂ) :=
    continuous_subtype_val.comp ((mem_sobolevGaugeGroup hs u).1 hu).1
  -- Pointwise, `‖u - 1‖ < 1` everywhere: almost everywhere by the Sobolev embedding, then
  -- everywhere by continuity.
  have hsmall : ∀ z, ‖(u z : ℂ) - 1‖ ≤ C₂ * R :=
    (Continuous.ae_le_iff_le volume (f := fun z ↦ ‖(u z : ℂ) - 1‖)
      (hu_cont.sub continuous_const).norm continuous_const).1 <| by
      filter_upwards [hsup hh, hhu] with z hz hz'
      rwa [← hz']
  have hslit (z : ℂ) : (u z : ℂ) ∈ slitPlane := by
    simpa using mem_slitPlane_of_norm_lt_one ((hsmall z).trans_lt hC₂R)
  refine ⟨fun z ↦ arg (u z : ℂ), ?_, ?_, ?_⟩
  · exact continuous_iff_continuousAt.2 fun z ↦
      (continuousAt_arg (hslit z)).comp_of_eq hu_cont.continuousAt rfl
  · -- `arg u = -i log u`, and `log u = log (1 + (u - 1))` lies in `H^s`.
    exact mem_realSobolevFunctions_of_ae_eq_ofReal (v := (-I) • v)
      (hvs.toTemperedDistribution_smul _) (Circle.neg_I_smul_ae_eq_arg hhu hv)
  · funext z
    exact (Circle.exp_arg (u z)).symm

/-- **The exponential chart is locally Lipschitz in `H^s` coordinates.** For `s > 1` there is a
constant `C` with the following property. Let `f, g` be real phases on the plane whose
complexifications are `L²` functions `F, G ∈ H^s(ℂ; ℂ)` with `‖F‖_{H^s}, ‖G‖_{H^s} ≤ R`, and let
`h, h'` be `L²` functions in `H^s` agreeing almost everywhere with `exp (i f) - 1` and
`exp (i g) - 1`. When `f` and `g` are continuous, these are the coordinates of the gauges
`exp (i f)` and `exp (i g)` of `G_s` (`exp_mem_sobolevGaugeGroup`). Then
`‖h - h'‖_{H^s} ≤ exp (C R) ‖F - G‖_{H^s}`. -/
theorem exists_norm_toBesselPotentialSpace_sub_le_of_ae_eq_exp {s : ℝ}
    (hs : 1 < s) :
    ∃ C, 0 ≤ C ∧ ∀ {f g : ℂ → ℝ} {F G : Lp ℂ 2 (volume : Measure ℂ)},
      F =ᵐ[volume] (fun z ↦ (f z : ℂ)) → G =ᵐ[volume] (fun z ↦ (g z : ℂ)) →
      ∀ (hF : MemSobolev s 2 (F : 𝓢'(ℂ, ℂ))) (hG : MemSobolev s 2 (G : 𝓢'(ℂ, ℂ))) {R : ℝ},
      ‖hF.toBesselPotentialSpace‖ ≤ R → ‖hG.toBesselPotentialSpace‖ ≤ R →
      ∀ {h h' : Lp ℂ 2 (volume : Measure ℂ)},
      h =ᵐ[volume] (fun z ↦ (Circle.exp (f z) : ℂ) - 1) →
      h' =ᵐ[volume] (fun z ↦ (Circle.exp (g z) : ℂ) - 1) →
      ∀ (hh : MemSobolev s 2 (h : 𝓢'(ℂ, ℂ))) (hh' : MemSobolev s 2 (h' : 𝓢'(ℂ, ℂ))),
      ‖hh.toBesselPotentialSpace - hh'.toBesselPotentialSpace‖ ≤
        Real.exp (C * R) * ‖hF.toBesselPotentialSpace - hG.toBesselPotentialSpace‖ := by
  obtain ⟨C, hC, hlip⟩ :=
    exists_norm_toBesselPotentialSpace_sub_le_of_ae_eq_exp_sub_one
      (finrank_real_complex_lt_two_mul hs)
  refine ⟨C, hC, fun {f g F G} hFf hGg hF hG {R} hFR hGR {h h'} hhf hhg hh hh' ↦ ?_⟩
  -- `exp (i f) - 1 = exp (U) - 1` for the `H^s` function `U = i F`.
  have hU := hF.toTemperedDistribution_smul I
  have hW := hG.toTemperedDistribution_smul I
  have hUF := hF.toBesselPotentialSpace_toTemperedDistribution_smul I hU
  have hWG := hG.toBesselPotentialSpace_toTemperedDistribution_smul I hW
  have hexp {X : Lp ℂ 2 (volume : Measure ℂ)} {k : ℂ → ℝ} {Y : Lp ℂ 2 (volume : Measure ℂ)}
      (hXk : X =ᵐ[volume] (fun z ↦ (k z : ℂ)))
      (hY : Y =ᵐ[volume] (fun z ↦ (Circle.exp (k z) : ℂ) - 1)) :
      Y =ᵐ[volume] (fun z ↦ exp ((I • X : Lp ℂ 2 (volume : Measure ℂ)) z) - 1) := by
    filter_upwards [hY, hXk, Lp.coeFn_smul I X] with z hz hzk hzI
    rw [hz, hzI, Pi.smul_apply, hzk, smul_eq_mul, Circle.coe_exp, mul_comm]
  have h := hlip hU hW (R := R) (by rwa [hUF, norm_smul, norm_I, one_mul])
    (by rwa [hWG, norm_smul, norm_I, one_mul]) hh hh' (hexp hFf hhf) (hexp hGg hhg)
  rwa [hUF, hWG, ← smul_sub, norm_smul, norm_I, one_mul] at h

/-- **The inverse of the exponential chart is Lipschitz near the identity.** For `s > 1` there is a
constant `C` with the following property. Let `u, u'` be circle-valued maps on the plane whose
coordinates `u - 1`, `u' - 1` are represented by `L²` functions `h, h' ∈ H^s(ℂ; ℂ)` with
`‖h‖_{H^s}, ‖h'‖_{H^s} ≤ R` and `C R < 1`. Then the phases `arg u` and `arg u'` are represented by
`L²` functions `F, F' ∈ H^s`, and `‖F - F'‖_{H^s} ≤ (1 - C R)⁻¹ ‖h - h'‖_{H^s}`. -/
theorem exists_memSobolev_ae_eq_arg_and_norm_sub_le {s : ℝ}
    (hs : 1 < s) :
    ∃ C, 0 ≤ C ∧ ∀ {u u' : ℂ → Circle} {h h' : Lp ℂ 2 (volume : Measure ℂ)},
      h =ᵐ[volume] (fun z ↦ (u z : ℂ) - 1) → h' =ᵐ[volume] (fun z ↦ (u' z : ℂ) - 1) →
      ∀ (hh : MemSobolev s 2 (h : 𝓢'(ℂ, ℂ))) (hh' : MemSobolev s 2 (h' : 𝓢'(ℂ, ℂ))) {R : ℝ},
      ‖hh.toBesselPotentialSpace‖ ≤ R → ‖hh'.toBesselPotentialSpace‖ ≤ R → C * R < 1 →
      ∃ F F' : Lp ℂ 2 (volume : Measure ℂ),
        F =ᵐ[volume] (fun z ↦ (arg (u z : ℂ) : ℂ)) ∧
        F' =ᵐ[volume] (fun z ↦ (arg (u' z : ℂ) : ℂ)) ∧
        ∃ (hF : MemSobolev s 2 (F : 𝓢'(ℂ, ℂ))) (hF' : MemSobolev s 2 (F' : 𝓢'(ℂ, ℂ))),
        ‖hF.toBesselPotentialSpace - hF'.toBesselPotentialSpace‖ ≤
          (1 - C * R)⁻¹ * ‖hh.toBesselPotentialSpace - hh'.toBesselPotentialSpace‖ := by
  have hs' := finrank_real_complex_lt_two_mul hs
  obtain ⟨C₁, hC₁, hlip⟩ := exists_norm_toBesselPotentialSpace_sub_le_of_ae_eq_log_one_add hs'
  obtain ⟨C₂, hC₂, hlog⟩ := exists_memSobolev_ae_eq_log_one_add hs'
  refine ⟨max C₁ C₂, le_max_of_le_left hC₁,
    fun {u u' h h'} hhu hhu' hh hh' {R} hhR hhR' hCR ↦ ?_⟩
  have hR : 0 ≤ R := (norm_nonneg _).trans hhR
  have hC₁R : C₁ * R ≤ max C₁ C₂ * R := mul_le_mul_of_nonneg_right (le_max_left _ _) hR
  have hC₂R : C₂ * R ≤ max C₁ C₂ * R := mul_le_mul_of_nonneg_right (le_max_right _ _) hR
  -- `log (1 + h)` lies in `H^s`, and `arg u = -i log u = -i log (1 + h)`, since `|u| = 1`.
  have harg {v : ℂ → Circle} {X : Lp ℂ 2 (volume : Measure ℂ)}
      (hX : X =ᵐ[volume] (fun z ↦ (v z : ℂ) - 1)) (hXs : MemSobolev s 2 (X : 𝓢'(ℂ, ℂ)))
      (hXR : ‖hXs.toBesselPotentialSpace‖ ≤ R) :
      ∃ L : Lp ℂ 2 (volume : Measure ℂ), L =ᵐ[volume] (fun z ↦ log (1 + X z)) ∧
        ∃ _ : MemSobolev s 2 (L : 𝓢'(ℂ, ℂ)),
        ((-I) • L : Lp ℂ 2 (volume : Measure ℂ)) =ᵐ[volume] (fun z ↦ (arg (v z : ℂ) : ℂ)) := by
    obtain ⟨L, hL, hLs⟩ := hlog hXs ((mul_le_mul_of_nonneg_left hXR hC₂).trans_lt
      (hC₂R.trans_lt hCR))
    exact ⟨L, hL, hLs, Circle.neg_I_smul_ae_eq_arg hX hL⟩
  obtain ⟨L, hL, hLs, hLu⟩ := harg hhu hh hhR
  obtain ⟨L', hL', hLs', hLu'⟩ := harg hhu' hh' hhR'
  have h := hlip hh hh' hhR hhR' (hC₁R.trans_lt hCR) hLs hLs' hL hL'
  have hF := hLs.toTemperedDistribution_smul (-I)
  have hF' := hLs'.toTemperedDistribution_smul (-I)
  refine ⟨_, _, hLu, hLu', hF, hF', ?_⟩
  rw [hLs.toBesselPotentialSpace_toTemperedDistribution_smul (-I) hF,
    hLs'.toBesselPotentialSpace_toTemperedDistribution_smul (-I) hF', ← smul_sub, norm_smul,
    norm_neg, norm_I, one_mul]
  exact h.trans (mul_le_mul_of_nonneg_right (inv_anti₀ (by linarith) (by linarith))
    (norm_nonneg _))

end TauCeti.Vortex
