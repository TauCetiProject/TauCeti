/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.FunctionalSpaces.BesselPotentialSpace
public import TauCeti.Analysis.PDE.Vortex.FramedGauge.Sobolev
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import TauCeti.Analysis.Distribution.TemperedDistribution.Lp
import TauCeti.Analysis.Sobolev.BesselPotential.Embedding
import TauCeti.Analysis.Sobolev.BesselPotential.PowerSeries
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
  (`TemperedDistribution.exists_hasSum_mul_pow`), and `log u = i arg u` because `|u| = 1`.

Since `G_s` is abelian and `exp (i (f + g)) = exp (i f) exp (i g)`, the exponential is an
injective homomorphism from the additive group of continuous real `H^s` phases into `G_s`, whose
image contains every element of `G_s` that is `H^s`-close to `1`. No topology on `G_s` is
constructed here, and the continuity of the exponential and of its inverse is not treated, so
these results do not yet make the exponential a chart.

## Main results

* `TauCeti.Vortex.exp_mem_sobolevGaugeGroup`: `exp (i f) ∈ G_s` for continuous real `f ∈ H^s`.
* `TauCeti.Vortex.injOn_exp`: the exponential is injective on continuous real `H^s` phases.
* `TauCeti.Vortex.exists_continuous_mem_realSobolevFunctions_eq_exp`: the elements of `G_s` close
  to `1` in `H^s` are exponentials of continuous real `H^s` phases.

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
  obtain ⟨C, hC, hser⟩ := exists_hasSum_mul_pow hs'
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
  -- The logarithm series `∑ₙ (-1)ⁿ wⁿ⁺¹ / (n + 1)`, majorized by the geometric series.
  set a : ℕ → ℂ := fun n ↦ (-1) ^ n / (n + 1)
  have hsum : Summable fun n ↦ ‖a n‖ * (C * R) ^ n := by
    refine (summable_geometric_of_lt_one (by positivity) hCR).of_nonneg_of_le
      (fun n ↦ by positivity) fun n ↦ ?_
    refine mul_le_of_le_one_left (by positivity) ?_
    rw [norm_div, norm_pow, norm_neg, norm_one, one_pow]
    refine div_le_one_of_le₀ ?_ (norm_nonneg _)
    rw [← Nat.cast_add_one, Complex.norm_natCast]
    exact_mod_cast Nat.le_add_left 1 n
  obtain ⟨v, hv, hvs, -⟩ := hser hh hsum
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
  · -- `arg u = -i log u`, and `log u` is the sum of the logarithm series in `u - 1`.
    refine mem_realSobolevFunctions_of_ae_eq_ofReal (v := (-I) • v) ?_ ?_
    · rw [Lp.toTemperedDistribution_smul]
      exact hvs.smul _
    · filter_upwards [Lp.coeFn_smul (-I) v, hv, hhu] with z hz hvz hhz
      rw [hhz] at hvz
      have hlog := (hasSum_nat_add_iff' 1).2
        (hasSum_taylorSeries_log ((hsmall z).trans_lt hC₂R))
      simp only [Finset.range_one, Finset.sum_singleton, pow_zero, CharP.cast_eq_zero, div_zero,
        sub_zero, add_sub_cancel] at hlog
      have hval : v z = log (u z : ℂ) := hvz.unique <| by
        convert hlog using 1
        ext n
        simp only [a]
        push_cast
        ring
      rw [hz, Pi.smul_apply, smul_eq_mul, hval]
      apply Complex.ext <;> simp [log_re, log_im]
  · funext z
    exact (Circle.exp_arg (u z)).symm

end TauCeti.Vortex
