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

/-!
# The exponential chart of the Sobolev framed gauge group

For a real order `s > 1`, the Sobolev framed gauge group `G_s` (`sobolevGaugeGroup`) consists of
the continuous circle-valued maps `u` on the plane with `u - 1 ∈ H^s(ℂ; ℂ)`. Its Lie algebra is
the space of real phases `f ∈ H^s(ℂ; ℝ)`, and this file shows that the exponential
`f ↦ exp (i f)` is a chart of `G_s` at the identity.

* **The exponential lands in `G_s`.** For a continuous real `f ∈ H^s`, the gauge `exp (i f)` lies
  in `G_s` (`TauCeti.Vortex.exp_mem_sobolevGaugeGroup`). Indeed `exp (± i f) - 1` is a power
  series in `f` without constant term, which converges in the algebra `H^s`
  (`TemperedDistribution.MemSobolev.exists_hasSum_mul_pow`), and `cos f - 1` and `sin f` are the
  half sum and half difference of these two series.
* **It is injective.** Two continuous real phases in `H^s` with the same exponential are equal
  (`TauCeti.Vortex.injOn_exp`): their difference takes values in `2πℤ`, so it is constant on the
  connected plane, and it tends to zero at infinity by the Sobolev embedding.
* **It covers an `H^s` neighbourhood of the identity.** There is `δ > 0` such that every
  `u ∈ G_s` with `‖u - 1‖_{H^s} < δ` is `exp (i f)` for a continuous real `f ∈ H^s`
  (`TauCeti.Vortex.exists_continuous_mem_realSobolevFunctions_eq_exp`), namely `f = arg u`. Here
  `log u = log (1 + (u - 1))` is the logarithm series in `u - 1`, which converges in `H^s` once
  `‖u - 1‖_{H^s}` is small, and `log u = i arg u` because `|u| = 1`.

Since `G_s` is abelian and `exp (i (f + g)) = exp (i f) exp (i g)`, the exponential is an
injective homomorphism from the additive group of continuous real `H^s` phases into `G_s`, whose
image contains every element of `G_s` that is `H^s`-close to `1`. This is the chart in which `G_s`
is modelled on the Hilbert space `H^s(ℂ; ℝ)`. The topology of `G_s` and the continuity of the
chart maps are not treated here.

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
open scoped Nat Real Topology SchwartzMap

/-- For a real `f ∈ H^s`, `s > 1`, and a complex constant `c`, the function `exp (c f) - 1` is an
`L²` function in `H^s`: it is the exponential series of `c f` without its constant term. -/
private theorem exists_memSobolev_ae_eq_exp_mul_sub_one {s : ℝ} (hs : 1 < s) {f : ℂ → ℝ}
    (hf : f ∈ realSobolevFunctions ℂ s 2) (c : ℂ) :
    ∃ v : Lp ℂ 2 (volume : Measure ℂ), v =ᵐ[volume] (fun z ↦ cexp (c * f z) - 1) ∧
      MemSobolev s 2 (v : 𝓢'(ℂ, ℂ)) := by
  obtain ⟨u, huf, hu⟩ := mem_realSobolevFunctions.1 hf
  set U := c • ofRealCLM.compLp u
  have hU : MemSobolev s 2 (U : 𝓢'(ℂ, ℂ)) := by
    rw [Lp.toTemperedDistribution_smul]
    exact hu.smul c
  obtain ⟨C, hC0, hC⟩ := MemSobolev.exists_hasSum_mul_pow (finrank_real_complex_lt_two_mul hs)
  set R := C * ‖hU.toBesselPotentialSpace‖
  -- The exponential series `∑ₙ w ^ (n + 1) / (n + 1)!`, majorized by `∑ₙ Rⁿ / n!`.
  have hsum : Summable fun n ↦ ‖(((n + 1)! : ℂ))⁻¹‖ * R ^ n := by
    refine (Real.summable_pow_div_factorial R).of_nonneg_of_le (fun n ↦ by positivity)
      fun n ↦ ?_
    rw [norm_inv, Complex.norm_natCast, div_eq_inv_mul]
    gcongr
    exact_mod_cast n.le_succ
  obtain ⟨v, hv, hvs, -⟩ := hC hU hsum
  refine ⟨v, ?_, hvs⟩
  filter_upwards [hv, Lp.coeFn_smul c (ofRealCLM.compLp u),
    ofRealCLM.coeFn_compLp (p := 2) (μ := volume) u, huf] with z hz hUz hcz hfz
  have hw : U z = c * f z := by
    rw [hUz, Pi.smul_apply, hcz, ofRealCLM_apply, hfz, smul_eq_mul]
  rw [hw] at hz
  refine hz.unique ?_
  have h := (hasSum_nat_add_iff' 1).2 (NormedSpace.expSeries_div_hasSum_exp (c * f z))
  simp only [Finset.range_one, Finset.sum_singleton, pow_zero, Nat.factorial_zero, Nat.cast_one,
    div_one, ← exp_eq_exp_ℂ] at h
  simpa only [div_eq_inv_mul] using h

/-- **The exponential of a Sobolev phase is a Sobolev gauge.** For `s > 1` and a continuous real
function `f ∈ H^s(ℂ)`, the gauge `exp (i f)` lies in `G_s`. In particular this holds for smooth
compactly supported `f`. -/
theorem exp_mem_sobolevGaugeGroup {s : ℝ} (hs : 1 < s) {f : ℂ → ℝ} (hf : Continuous f)
    (hfs : f ∈ realSobolevFunctions ℂ s 2) :
    (fun z ↦ Circle.exp (f z)) ∈ sobolevGaugeGroup hs := by
  obtain ⟨vp, hvp, hsp⟩ := exists_memSobolev_ae_eq_exp_mul_sub_one hs hfs I
  obtain ⟨vm, hvm, hsm⟩ := exists_memSobolev_ae_eq_exp_mul_sub_one hs hfs (-I)
  refine (mem_sobolevGaugeGroup hs _).2 ⟨Circle.exp.continuous.comp hf, ?_, ?_⟩
  · -- `cos f - 1` is the half sum of `exp (i f) - 1` and `exp (-i f) - 1`.
    refine mem_realSobolevFunctions_of_ae_eq_ofReal (v := (2⁻¹ : ℂ) • (vp + vm)) ?_ ?_
    · rw [Lp.toTemperedDistribution_smul, Lp.toTemperedDistribution_add]
      exact (hsp.add hsm).smul _
    · filter_upwards [Lp.coeFn_smul (2⁻¹ : ℂ) (vp + vm), Lp.coeFn_add vp vm, hvp, hvm]
        with z h h' hp hm
      rw [h, Pi.smul_apply, h', Pi.add_apply, hp, hm, Circle.coe_exp, exp_ofReal_mul_I_re,
        smul_eq_mul, ofReal_sub, ofReal_cos, ofReal_one]
      have h2 := two_cos (f z : ℂ)
      simp only [neg_mul, mul_comm I] at h2 ⊢
      linear_combination (-2⁻¹ : ℂ) * h2
  · -- `sin f` is the half difference of `exp (i f) - 1` and `exp (-i f) - 1`, divided by `i`.
    refine mem_realSobolevFunctions_of_ae_eq_ofReal (v := (-(2⁻¹ * I) : ℂ) • (vp - vm)) ?_ ?_
    · rw [Lp.toTemperedDistribution_smul, Lp.toTemperedDistribution_sub]
      exact (hsp.sub hsm).smul _
    · filter_upwards [Lp.coeFn_smul (-(2⁻¹ * I) : ℂ) (vp - vm), Lp.coeFn_sub vp vm, hvp, hvm]
        with z h h' hp hm
      rw [h, Pi.smul_apply, h', Pi.sub_apply, hp, hm, Circle.coe_exp, exp_ofReal_mul_I_im,
        smul_eq_mul, ofReal_sin]
      have h2 := two_sin (f z : ℂ)
      simp only [neg_mul, mul_comm I] at h2 ⊢
      linear_combination (-2⁻¹ : ℂ) * h2

/-- **The exponential chart is injective.** For `s > 1`, two continuous real functions in `H^s(ℂ)`
with the same exponential `exp (i f)` are equal. -/
theorem injOn_exp {s : ℝ} (hs : 1 < s) :
    Set.InjOn (fun (f : ℂ → ℝ) (z : ℂ) ↦ Circle.exp (f z))
      {f | Continuous f ∧ f ∈ realSobolevFunctions ℂ s 2} := by
  rintro f ⟨hf, hfs⟩ g ⟨hg, hgs⟩ hfg
  set D := f - g
  have hD : Continuous D := hf.sub hg
  -- `D` takes values in `2πℤ`, so it is constant on the connected plane.
  have hmaps : Set.MapsTo D Set.univ (AddSubgroup.zmultiples (2 * π) : Set ℝ) := by
    intro z _
    have h : Circle.exp (D z) = 1 := by
      rw [show D z = f z - g z from rfl, Circle.exp_sub]
      exact div_eq_one.2 (congrFun hfg z)
    obtain ⟨n, hn⟩ := Circle.exp_eq_one.1 h
    exact ⟨n, by simp [hn, zsmul_eq_mul]⟩
  have hconst (z w : ℂ) : D z = D w :=
    isPreconnected_univ.constant_of_mapsTo
      (isDiscrete_iff_discreteTopology.2 (NormedSpace.discreteTopology_zmultiples (2 * π)))
      hD.continuousOn hmaps (Set.mem_univ z) (Set.mem_univ w)
  -- `D` tends to zero at infinity, so the constant is zero.
  have hlim := tendsto_cocompact_of_mem_realSobolevFunctions (finrank_real_complex_lt_two_mul hs)
    (sub_mem hfs hgs) hD
  funext z
  have h0 : D z = 0 :=
    tendsto_nhds_unique (tendsto_const_nhds.congr fun w ↦ hconst z w) hlim
  exact sub_eq_zero.1 h0

/-- **The logarithm chart of `G_s` at the identity.** For `s > 1` there is `δ > 0` such that
every `u ∈ G_s` with `‖u - 1‖_{H^s} < δ` is `exp (i f)` for a continuous real function
`f ∈ H^s(ℂ)`, namely `f = arg u`. Here `u - 1` is represented by an `L²` function `h` in
`H^s(ℂ; ℂ)`, as in `exists_memSobolev_ae_eq_of_mem_sobolevGaugeGroup`. -/
theorem exists_continuous_mem_realSobolevFunctions_eq_exp {s : ℝ} (hs : 1 < s) :
    ∃ δ, 0 < δ ∧ ∀ u ∈ sobolevGaugeGroup hs, ∀ {h : Lp ℂ 2 (volume : Measure ℂ)},
      h =ᵐ[volume] (fun z ↦ (u z : ℂ) - 1) → ∀ hh : MemSobolev s 2 (h : 𝓢'(ℂ, ℂ)),
      ‖hh.toBesselPotentialSpace‖ < δ →
      ∃ f : ℂ → ℝ, Continuous f ∧ f ∈ realSobolevFunctions ℂ s 2 ∧
        u = fun z ↦ Circle.exp (f z) := by
  have hs' := finrank_real_complex_lt_two_mul hs
  obtain ⟨C, hC, hser⟩ := MemSobolev.exists_hasSum_mul_pow hs'
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
    refine (summable_geometric_of_lt_one (by positivity) hCR).of_norm_bounded fun n ↦ ?_
    rw [Real.norm_eq_abs, abs_mul, abs_norm, abs_pow, abs_of_nonneg (by positivity)]
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
  have hsmall : ∀ z, ‖(u z : ℂ) - 1‖ ≤ C₂ * R := by
    have hcont : Continuous fun z ↦ ‖(u z : ℂ) - 1‖ := (hu_cont.sub continuous_const).norm
    have hae : (fun z ↦ min ‖(u z : ℂ) - 1‖ (C₂ * R)) =ᵐ[volume] fun z ↦ ‖(u z : ℂ) - 1‖ := by
      filter_upwards [hsup hh, hhu] with z hz hz'
      rw [← hz']
      exact min_eq_left hz
    have heq := (hcont.min continuous_const).ae_eq_iff_eq volume hcont |>.1 hae
    exact fun z ↦ (congrFun heq z).symm.trans_le (min_le_right _ _) |>.trans_eq' rfl
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
