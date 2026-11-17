/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.FramedGauge.Chart
public import TauCeti.Analysis.PDE.Vortex.FramedGauge.FieldTopology
import TauCeti.Analysis.Complex.Circle
import TauCeti.Analysis.SpecialFunctions.Complex.Arg
import TauCeti.Analysis.Sobolev.BesselPotential.Operator
import TauCeti.MeasureTheory.Function.LpSeminorm.Tendsto

/-!
# Gauges between convergent framed fields converge in `G_(k+1)`

Framed degree-`m` plane vortex fields form the affine space `A_m^k = x_m + H^k(ℂ; ℝ⁴)`
(`TauCeti.Vortex.framedFieldSpace`), whose continuous fields carry the Sobolev topology of
`TauCeti.Vortex.SobolevFieldSpace`, and the Sobolev gauge group `G_(k+1)`
(`TauCeti.Vortex.SobolevTopologicalGaugeGroup`) carries the topology of `u - 1 ∈ H^(k+1)(ℂ)`.
This file proves, for an integer `k ≥ 3`, that a gauge carrying one field of `A_m^k` to another
depends continuously on the pair of fields: if `xᵢ → x` and `yᵢ → y` in `A_m^k`, and
`uᵢ, u ∈ G_(k+1)` satisfy `uᵢ · xᵢ = yᵢ` and `u · x = y`, then `uᵢ → u` in `G_(k+1)`
(`TauCeti.Vortex.SobolevFieldSpace.tendsto_of_gaugeTransform_eq`). Together with the closedness of
the orbit relation
(`TauCeti.Vortex.exists_mem_sobolevGaugeGroup_gaugeTransform_eq_and_tendstoLocallyUniformly`),
the gauges converge whenever the fields do
(`TauCeti.Vortex.SobolevFieldSpace.exists_gaugeTransform_eq_and_tendsto`). This is the sequential
form of the properness of the action of `G_(k+1)` on `A_m^k`, the property of the action that the
quotient `A_m^k / G_(k+1)` needs besides a slice.

The argument has three steps.

* **Phases.** A gauge `w ∈ G_(k+1)` with `|w - 1| < 1` everywhere is `exp (i F)` for the real
  phase `F = arg w ∈ H^(k+1)`, whose derivative in a direction `v` is the logarithmic derivative
  `Im (w⁻¹ ∂_v w)` and whose modulus is at most `(π / 2) |w - 1|`
  (`TauCeti.Vortex.SobolevTopologicalGaugeGroup.exists_expGauge_eq_of_forall_norm_sub_one_lt`).
  Unlike `w - 1`, the phase depends linearly on the logarithmic derivative.
* **A convergence criterion in `G_(k+1)`.** Gauges `wᵢ` converge to `1` in `G_(k+1)` as soon as
  `wᵢ → 1` uniformly and in `L²`, and their logarithmic derivatives tend to zero in `H^k`
  (`TauCeti.Vortex.SobolevTopologicalGaugeGroup.tendsto_one_of_tendsto_gaugeForm`). The phases
  `Fᵢ` then tend to zero in `L²` and their derivatives tend to zero in `H^k`, so `Fᵢ → 0` in
  `H^(k+1)` (`BesselPotentialSpace.tendsto_of_tendsto_inclusionLp_of_tendsto_lineDerivCLM`), and
  `wᵢ = exp (i Fᵢ) → 1` by the continuity of the exponential chart.
* **The fields.** For `wᵢ = u⁻¹ uᵢ`, the logarithmic derivative is the difference of the
  connection differences of `(xᵢ, yᵢ)` and of `(x, y)`, which tends to zero in `H^k`. The sections
  satisfy `(uᵢ - u) α = uᵢ (α - αᵢ) + (βᵢ - β)` for `α, αᵢ, β, βᵢ` the sections of `x, xᵢ, y, yᵢ`,
  so `|uᵢ - u| ≤ 2 (|α - αᵢ| + |βᵢ - β|)` where `|α| ≥ 1 / 2`. The rest of the plane is compact,
  because `|α| → 1` at infinity
  (`TauCeti.Vortex.SobolevFieldSpace.isCompact_setOf_norm_sectionValue_le`), and there the
  gauges converge uniformly by the limit theorem for gauge equivalences. Since convergence in
  `A_m^k` gives `L²` convergence of the coordinates
  (`TauCeti.Vortex.SobolevFieldSpace.tendsto_eLpNorm_sub_of_tendsto`), `uᵢ - u` tends to zero
  uniformly and in `L²`.

## Main results

* `TauCeti.Vortex.SobolevTopologicalGaugeGroup.exists_expGauge_eq_of_forall_norm_sub_one_lt`: a
  gauge uniformly close to one is the exponential of its argument.
* `TauCeti.Vortex.SobolevTopologicalGaugeGroup.tendsto_one_of_tendsto_gaugeForm`: the
  convergence criterion in `G_(k+1)`.
* `TauCeti.Vortex.SobolevFieldSpace.tendsto_of_gaugeTransform_eq`: gauges between convergent
  fields converge to the gauge between the limits.
* `TauCeti.Vortex.SobolevFieldSpace.exists_gaugeTransform_eq_and_tendsto`: the sequential
  properness of the action.

## References

* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III.
* S. K. Donaldson and P. B. Kronheimer, *The Geometry of Four-Manifolds*, Oxford University Press,
  1990, Section 4.2.
-/

public section

noncomputable section

namespace TauCeti.Vortex

open Complex Filter MeasureTheory Metric Set Topology TemperedDistribution BesselPotentialSpace
open scoped ENNReal Real SchwartzMap BesselPotentialSpace

variable {k : ℕ} {hs : 1 < (k : ℝ) + 1}

namespace SobolevTopologicalGaugeGroup

/-- The argument `φ = arg u` of a gauge `u ∈ G_(k+1)`, `k ≥ 2`, with `|u - 1| < 1` everywhere: it is
`C¹` with `dφ = Im (u⁻¹ du)` and `|φ| ≤ (π / 2) |u - 1|`, and it lies in `H^(k+1)`. -/
private theorem arg_spec (hk : 1 < k) {u : ℂ → Circle} (huG : u ∈ sobolevGaugeGroup hs)
    (hw : ∀ z, ‖(u z : ℂ) - 1‖ < 1) :
    ContDiff ℝ 1 (fun z ↦ arg (u z : ℂ)) ∧
      (∀ z, fderiv ℝ (fun z ↦ arg (u z : ℂ)) z = gaugeForm u z) ∧
      (∀ z, ‖((arg (u z : ℂ) : ℝ) : ℂ)‖ ≤ π / 2 * ‖(u z : ℂ) - 1‖) ∧
      (fun z ↦ arg (u z : ℂ)) ∈ realSobolevFunctions ℂ ((k : ℝ) + 1) 2 := by
  have hk' : ((1 : ℕ) : ℝ) + 1 < (k : ℝ) + 1 := by
    have : (1 : ℝ) < k := by exact_mod_cast hk
    push_cast
    linarith
  have hC1 : ContDiff ℝ 1 fun z ↦ (u z : ℂ) := contDiff_of_mem_sobolevGaugeGroup hk' huG
  -- The values of `u` lie in the slit plane, where the argument is smooth.
  have hslit (z : ℂ) : (u z : ℂ) ∈ slitPlane := by
    simpa using mem_slitPlane_of_norm_lt_one (hw z)
  set φ : ℂ → ℝ := fun z ↦ arg (u z : ℂ)
  have hφ : ContDiff ℝ 1 φ := contDiff_iff_contDiffAt.2 fun z ↦
    (contDiffAt_arg (hslit z)).comp (f := fun z ↦ (u z : ℂ)) z hC1.contDiffAt
  have hexp : (fun z ↦ Circle.exp (φ z)) = u := funext fun z ↦ Circle.exp_arg (u z)
  have hdφ (z : ℂ) : fderiv ℝ φ z = gaugeForm u z := by
    rw [← gaugeForm_exp (hφ.differentiable one_ne_zero z), hexp]
  have hbound (z : ℂ) : ‖(φ z : ℂ)‖ ≤ π / 2 * ‖(u z : ℂ) - 1‖ := by
    have hre : 0 ≤ (u z : ℂ).re := by
      have := (abs_re_le_norm ((u z : ℂ) - 1)).trans (hw z).le
      rw [sub_re, one_re] at this
      linarith [neg_abs_le ((u z : ℂ).re - 1)]
    rw [norm_real, Real.norm_eq_abs]
    exact abs_arg_le_pi_div_two_mul_norm_sub_one (Circle.norm_coe _) hre
  -- The phase lies in `L²`, since `u - 1` does.
  obtain ⟨g, hg, -⟩ := exists_memSobolev_ae_eq_of_mem_sobolevGaugeGroup huG
  have hL2 : MemLp φ 2 volume :=
    (((Lp.memLp g).ae_eq hg).norm.const_mul (π / 2)).of_le hφ.continuous.aestronglyMeasurable
      (Eventually.of_forall fun z ↦ by
        have h := hbound z
        rw [norm_real] at h
        rwa [norm_mul, norm_norm, Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ π / 2)])
  -- Its derivatives are the coefficients of the logarithmic derivative, which lie in `H^k`.
  have hd (v : ℂ) : (fun z ↦ fderiv ℝ φ z v) ∈ realSobolevFunctions ℂ k 2 := by
    simp_rw [hdφ]
    exact gaugeForm_apply_mem_realSobolevFunctions (s := k) (by exact_mod_cast (by omega : 1 < k))
      huG v
  have hmem (j : ℕ) (hj : j ≤ k + 1) : φ ∈ realSobolevFunctions ℂ j 2 := by
    induction j with
    | zero => simpa using mem_realSobolevFunctions_zero_iff.2 hL2
    | succ j ih =>
      push_cast
      exact mem_realSobolevFunctions_add_one_of_fderiv_apply (by norm_num) (by norm_num) hφ
        (ih (by omega)) fun v ↦ realSobolevFunctions_mono (by norm_num) (by norm_num)
          (by exact_mod_cast (by omega : j ≤ k)) (hd v)
  exact ⟨hφ, hdφ, hbound, by simpa using hmem (k + 1) le_rfl⟩

/-- **Sobolev gauges uniformly close to one are exponentials of their argument.** Let `k ≥ 2` and
let `w ∈ G_(k+1)` satisfy `|w - 1| < 1` everywhere. Then `w = exp (i F)` for a real phase
`F ∈ H^(k+1)(ℂ)`, namely `arg w`, whose `L²` function is at most `(π / 2) |w - 1|` and whose
derivative in each direction `v` has the `L²` function `Im (w⁻¹ ∂_v w)`. -/
theorem exists_expGauge_eq_of_forall_norm_sub_one_lt (hk : 1 < k)
    (w : SobolevTopologicalGaugeGroup hs)
    (hw : ∀ z, ‖((toSubgroup hs w : ℂ → Circle) z : ℂ) - 1‖ < 1) :
    ∃ F : realSubmodule ℂ (zero_le_one.trans hs.le), expGauge hs F = w ∧
      (∀ᵐ z ∂volume, ‖inclusionLp (zero_le_one.trans hs.le) (F : H^{(k : ℝ) + 1}(ℂ)) z‖ ≤
        π / 2 * ‖((toSubgroup hs w : ℂ → Circle) z : ℂ) - 1‖) ∧
      ∀ v : ℂ, inclusionLp (Nat.cast_nonneg (α := ℝ) k)
          (lineDerivCLM (by norm_num) (by norm_num) v (F : H^{(k : ℝ) + 1}(ℂ))) =ᵐ[volume]
        fun z ↦ (gaugeForm (toSubgroup hs w) z v : ℂ) := by
  set u : ℂ → Circle := ↑(toSubgroup hs w)
  have h0 : (0 : ℝ) ≤ (k : ℝ) + 1 := zero_le_one.trans hs.le
  obtain ⟨hφ, hdφ, hbound, hφk⟩ := arg_spec hk (toSubgroup hs w).2 hw
  set φ : ℂ → ℝ := fun z ↦ arg (u z : ℂ)
  have hexp : (fun z ↦ Circle.exp (φ z)) = u := funext fun z ↦ Circle.exp_arg (u z)
  obtain ⟨U, hU⟩ := (mem_realSobolevFunctions_iff_exists_inclusionLp_ae_eq h0).1 hφk
  have hUreal : U ∈ realSubmodule ℂ h0 := (mem_realSubmodule_iff h0).2 <| by
    filter_upwards [hU] with z hz
    rw [hz, ofReal_im]
  refine ⟨⟨U, hUreal⟩, ?_, ?_, fun v ↦ ?_⟩
  · rw [expGauge_eq_iff]
    rw [continuousRep_eq_of_ae_eq (finrank_real_complex_lt_two_mul hs) hφ.continuous hU]
    exact hexp
  · filter_upwards [hU] with z hz
    rw [hz]
    exact hbound z
  · filter_upwards [coeFn_inclusionLp_lineDerivCLM_ae_eq (by norm_num) (by norm_num)
      (Nat.cast_nonneg (α := ℝ) k) hφ hU v] with z hz
    rw [hz, hdφ]

/-- **A convergence criterion in `G_(k+1)`.** For `k ≥ 2`, Sobolev gauges `wᵢ` converge to `1` in
`G_(k+1)` when `wᵢ → 1` uniformly, `‖wᵢ - 1‖_{L²} → 0`, and their logarithmic derivatives
`Im (wᵢ⁻¹ ∂_v wᵢ)`, represented by `gᵢ v ∈ H^k(ℂ)`, tend to zero in `H^k` in every direction `v`. -/
theorem tendsto_one_of_tendsto_gaugeForm (hk : 1 < k) {ι : Type*} {l : Filter ι}
    {w : ι → SobolevTopologicalGaugeGroup hs}
    (hunif : TendstoUniformly (fun i z ↦ ((toSubgroup hs (w i) : ℂ → Circle) z : ℂ)) (fun _ ↦ 1) l)
    (hL2 : Tendsto (fun i ↦ eLpNorm (fun z ↦ ((toSubgroup hs (w i) : ℂ → Circle) z : ℂ) - 1) 2
      volume) l (𝓝 0))
    {g : ι → ℂ → H^{(k : ℝ)}(ℂ)}
    (hg : ∀ i v, inclusionLp (Nat.cast_nonneg (α := ℝ) k) (g i v) =ᵐ[volume]
      fun z ↦ (gaugeForm (toSubgroup hs (w i)) z v : ℂ))
    (hg₀ : ∀ v, Tendsto (fun i ↦ g i v) l (𝓝 0)) :
    Tendsto w l (𝓝 1) := by
  have h0 : (0 : ℝ) ≤ (k : ℝ) + 1 := zero_le_one.trans hs.le
  rcases l.eq_or_neBot with rfl | hl
  · exact tendsto_bot
  -- The phases `Fᵢ = arg wᵢ`, defined where `|wᵢ - 1| < 1`.
  obtain ⟨F, hF⟩ := Eventually.choice (r := fun i (F : realSubmodule ℂ h0) ↦
    expGauge hs F = w i ∧
      (∀ᵐ z ∂volume, ‖inclusionLp h0 (F : H^{(k : ℝ) + 1}(ℂ)) z‖ ≤
        π / 2 * ‖((toSubgroup hs (w i) : ℂ → Circle) z : ℂ) - 1‖) ∧
      ∀ v : ℂ, inclusionLp (Nat.cast_nonneg (α := ℝ) k)
          (lineDerivCLM (by norm_num) (by norm_num) v (F : H^{(k : ℝ) + 1}(ℂ))) =ᵐ[volume]
        fun z ↦ (gaugeForm (toSubgroup hs (w i)) z v : ℂ)) <| by
    filter_upwards [Metric.tendstoUniformly_iff.1 hunif 1 one_pos] with i hi
    refine exists_expGauge_eq_of_forall_norm_sub_one_lt hk (w i) fun z ↦ ?_
    rw [← dist_eq_norm, dist_comm]
    exact hi z
  -- The phases tend to zero in `L²`.
  have hFL2 : Tendsto (fun i ↦ inclusionLp h0 (F i : H^{(k : ℝ) + 1}(ℂ))) l (𝓝 0) := by
    rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm']
    have hlim := ENNReal.Tendsto.const_mul hL2 (Or.inr (ENNReal.ofReal_ne_top (r := π / 2)))
    rw [mul_zero] at hlim
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
      (Eventually.of_forall fun _ ↦ bot_le) ?_
    filter_upwards [hF] with i hi
    have hz0 : (⇑(inclusionLp h0 (F i : H^{(k : ℝ) + 1}(ℂ))) - ⇑(0 : Lp ℂ 2 (volume : Measure ℂ)))
        =ᵐ[volume] ⇑(inclusionLp h0 (F i : H^{(k : ℝ) + 1}(ℂ))) := by
      filter_upwards [Lp.coeFn_zero ℂ 2 (volume : Measure ℂ)] with z hz
      rw [Pi.sub_apply, hz, Pi.zero_apply, sub_zero]
    rw [eLpNorm_congr_ae hz0]
    exact eLpNorm_le_mul_eLpNorm_of_ae_le_mul (Lp.aestronglyMeasurable _) hi.2.1 2
  -- Their derivatives tend to zero in `H^k`.
  have hFd (v : ℂ) : Tendsto (fun i ↦
      lineDerivCLM (by norm_num) (by norm_num) v (F i : H^{(k : ℝ) + 1}(ℂ))) l (𝓝 0) := by
    refine (hg₀ v).congr' ?_
    filter_upwards [hF] with i hi
    refine inclusionLp_injective (Nat.cast_nonneg (α := ℝ) k) (Lp.ext ?_)
    exact (hg i v).trans (hi.2.2 v).symm
  have hF0 : Tendsto F l (𝓝 0) := by
    rw [tendsto_subtype_rng]
    refine tendsto_of_tendsto_inclusionLp_of_tendsto_lineDerivCLM (by norm_num)
      (by norm_num) Complex.orthonormalBasisOneI (u₀ := 0) ?_ fun j ↦ ?_
    · simpa using hFL2
    · simpa using hFd _
  have hexp := ((continuous_expGauge hs).tendsto 0).comp hF0
  rw [AddChar.map_zero_eq_one] at hexp
  refine hexp.congr' ?_
  filter_upwards [hF] with i hi
  exact hi.1

end SobolevTopologicalGaugeGroup

open SobolevTopologicalGaugeGroup

/-! ### Gauges between fields -/

/-- Where the section of `x` has modulus at least `1 / 2`, a gauge `u` carrying `x` to `y` and a
gauge `v` carrying `x'` to `y'` differ by at most twice the differences of the sections:
`(v - u) α = v (α - α') + (β' - β)` for the sections `α, α', β, β'` of `x, x', y, y'`. -/
private theorem norm_coe_sub_coe_le {u v : ℂ → Circle} {x x' y y' : ℂ → EuclideanSpace ℝ (Fin 4)}
    (hu : gaugeTransform u x = y) (hv : gaugeTransform v x' = y') {z : ℂ}
    (hz : 1 / 2 ≤ ‖sectionValue x z‖) :
    ‖(v z : ℂ) - u z‖ ≤
      2 * (‖sectionValue x' z - sectionValue x z‖ + ‖sectionValue y' z - sectionValue y z‖) := by
  have hα := ((gaugeTransform_eq_iff.1 hu) z).2
  have hα' := ((gaugeTransform_eq_iff.1 hv) z).2
  have hid : ((v z : ℂ) - u z) * sectionValue x z =
      (v z : ℂ) * (sectionValue x z - sectionValue x' z) +
        (sectionValue y' z - sectionValue y z) := by
    rw [← hα, ← hα']
    ring
  have hle : ‖(v z : ℂ) - u z‖ * ‖sectionValue x z‖ ≤
      ‖sectionValue x' z - sectionValue x z‖ + ‖sectionValue y' z - sectionValue y z‖ := by
    rw [← norm_mul, hid]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, Circle.norm_coe, one_mul, norm_sub_rev]
  have hpos : (0 : ℝ) < ‖sectionValue x z‖ := lt_of_lt_of_le (by norm_num) hz
  rw [← le_div_iff₀ hpos] at hle
  refine hle.trans ?_
  rw [div_le_iff₀ hpos]
  nlinarith [norm_nonneg (sectionValue x' z - sectionValue x z),
    norm_nonneg (sectionValue y' z - sectionValue y z)]

/-- For unit complex numbers, `a⁻¹ b - 1 = a⁻¹ (b - a)`. -/
private theorem coe_inv_mul_sub_one (a b : Circle) :
    ((a⁻¹ * b : Circle) : ℂ) - 1 = ((a⁻¹ : Circle) : ℂ) * ((b : ℂ) - a) := by
  have ha : ((a⁻¹ : Circle) : ℂ) * a = 1 := by
    rw [← Circle.coe_mul, inv_mul_cancel, Circle.coe_one]
  rw [Circle.coe_mul]
  linear_combination ha

/-- The difference of two sections is bounded by the differences of the section coordinates. -/
private theorem norm_sectionValue_sub_le (x x' : ℂ → EuclideanSpace ℝ (Fin 4)) (z : ℂ) :
    ‖sectionValue x' z - sectionValue x z‖ ≤ 2 * (|x' z 2 - x z 2| + |x' z 3 - x z 3|) := by
  rw [← sectionValue_sub, sectionValue_apply, norm_mul, show ‖(2 : ℂ)‖ = 2 by norm_num]
  gcongr
  refine (norm_add_le _ _).trans ?_
  simp only [Pi.sub_apply, PiLp.sub_apply, ofReal_sub, norm_mul, norm_I, mul_one]
  rw [← ofReal_sub, ← ofReal_sub, norm_real, norm_real, Real.norm_eq_abs, Real.norm_eq_abs]

namespace SobolevFieldSpace

variable {f : ContDiffBump (0 : ℝ)} {m : ℕ}

/-- **Convergence in `A_m^s` gives `L²` convergence of the coordinates**, for `s ≥ 0`: if fields
`xᵢ → x` in `A_m^s`, then each coordinate `xᵢ(z)ⱼ - x(z)ⱼ` tends to zero in `L²`. -/
theorem tendsto_eLpNorm_sub_of_tendsto {s : ℝ} (h : 0 ≤ s) {ι : Type*} {l : Filter ι}
    {xs : ι → SobolevFieldSpace f m s} {x : SobolevFieldSpace f m s} (hx : Tendsto xs l (𝓝 x))
    (j : Fin 4) : Tendsto (fun i ↦ eLpNorm (fun z ↦ xs i z j - x z j) 2 volume) l (𝓝 0) := by
  set T : ι → Lp ℂ 2 (volume : Measure ℂ) := fun i ↦
    (inclusion h (subRef (xs i) j - subRef x j)).toLp
  have hT : Tendsto T l (𝓝 0) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hsub := tendsto_iff_norm_sub_tendsto_zero.1 (tendsto_iff.1 hx j)
    refine squeeze_zero (fun _ ↦ norm_nonneg _) (fun i ↦ ?_) hsub
    rw [sub_zero, norm_toLp_eq]
    exact norm_inclusion_apply_le h _
  have hae (i : ι) : (T i : ℂ → ℂ) =ᵐ[volume] fun z ↦ ((xs i z j - x z j : ℝ) : ℂ) := by
    filter_upwards [coeFn_toLp_inclusion_subRef h (xs i) j, coeFn_toLp_inclusion_subRef h x j,
      Lp.coeFn_sub (inclusion h (subRef (xs i) j)).toLp (inclusion h (subRef x j)).toLp]
      with z h₁ h₂ h₃
    simp only [T, map_sub, toLp_sub, h₃, Pi.sub_apply, h₁, h₂]
    push_cast
    ring
  have hlim := ((continuous_eNorm.tendsto 0).comp hT)
  rw [eNorm_zero] at hlim
  refine hlim.congr fun i ↦ ?_
  simp only [Function.comp_apply, Lp.eNorm_def]
  rw [eLpNorm_congr_ae (hae i)]
  have hc : Continuous fun z ↦ xs i z j - x z j :=
    ((EuclideanSpace.proj j).continuous.comp (xs i).continuous).sub
      ((EuclideanSpace.proj j).continuous.comp x.continuous)
  exact eLpNorm_congr_norm_ae (continuous_ofReal.comp hc).aestronglyMeasurable
    hc.aestronglyMeasurable (Eventually.of_forall fun z ↦ by rw [norm_real])

/-- **The set where the section is small is compact.** For `s > 1` and `c < 1`, the points where
the section of a field of `A_m^s` has modulus at most `c` form a compact set, since `|α| → 1` at
infinity. -/
theorem isCompact_setOf_norm_sectionValue_le {s : ℝ} (hs : 1 < s) (x : SobolevFieldSpace f m s)
    {c : ℝ} (hc : c < 1) : IsCompact {z | ‖sectionValue x z‖ ≤ c} := by
  have hαc : Continuous fun z ↦ sectionValue x z := by
    simp only [sectionValue_apply]
    exact continuous_const.mul ((continuous_ofReal.comp
      ((EuclideanSpace.proj (2 : Fin 4)).continuous.comp x.continuous)).add
      ((continuous_ofReal.comp
        ((EuclideanSpace.proj (3 : Fin 4)).continuous.comp x.continuous)).mul continuous_const))
  have hev : ∀ᶠ z in cocompact ℂ, c < ‖sectionValue x z‖ := by
    rcases lt_or_ge c 0 with hc0 | hc0
    · exact Eventually.of_forall fun z ↦ hc0.trans_le (norm_nonneg _)
    filter_upwards [(tendsto_normSq_of_mem_framedFieldSpace hs x.mem_framedFieldSpace
      x.continuous).eventually (lt_mem_nhds (by nlinarith : c ^ 2 < 1))] with z hz
    rw [← sq_norm_sectionValue] at hz
    nlinarith [norm_nonneg (sectionValue x z)]
  obtain ⟨t, ht, hts⟩ := mem_cocompact.1 hev
  refine ht.of_isClosed_subset (isClosed_le hαc.norm continuous_const) fun z hz ↦ ?_
  by_contra hzt
  have h1 : c < ‖sectionValue x z‖ := hts hzt
  exact absurd hz (not_le.2 h1)

section Convergence

variable {ι : Type*} {l : Filter ι} {xs ys : ι → SobolevFieldSpace f m k}
  {x y : SobolevFieldSpace f m k} {us : ι → SobolevTopologicalGaugeGroup hs}
  {u : SobolevTopologicalGaugeGroup hs}

private theorem two_lt_add_one (hk : 2 < k) : (2 : ℝ) < (k : ℝ) + 1 := by
  have : (2 : ℝ) < k := by exact_mod_cast hk
  linarith

/-- Gauges between convergent fields converge locally uniformly to the gauge between the limits. -/
private theorem tendstoLocallyUniformly_of_gaugeTransform_eq (hk : 2 < k) [l.NeBot]
    (hxy : ∀ i, gaugeTransform (toSubgroup hs (us i) : ℂ → Circle) (xs i) = ys i)
    (huxy : gaugeTransform (toSubgroup hs u : ℂ → Circle) x = y)
    (hx : Tendsto xs l (𝓝 x)) (hy : Tendsto ys l (𝓝 y)) :
    TendstoLocallyUniformly (fun i z ↦ ((toSubgroup hs (us i) : ℂ → Circle) z : ℂ))
      (fun z ↦ ((toSubgroup hs u : ℂ → Circle) z : ℂ)) l := by
  have hk1 : (1 : ℝ) < k := by exact_mod_cast (by omega : 1 < k)
  have h2 := two_lt_add_one hk
  obtain ⟨v, hvG, hv, hconv⟩ :=
    exists_mem_sobolevGaugeGroup_gaugeTransform_eq_and_tendstoLocallyUniformly hk
      (fun i ↦ differentiable_of_mem_sobolevGaugeGroup h2 (toSubgroup hs (us i)).2) hxy
      (tendstoUniformly_of_tendsto hk1 hx).tendstoLocallyUniformly
      (tendstoUniformly_of_tendsto hk1 hy).tendstoLocallyUniformly
      x.continuous y.continuous x.mem_framedFieldSpace y.mem_framedFieldSpace
  -- The limit is `u`, since the action of `G_(k+1)` on `A_m^k` is free.
  have : Fact (1 < k) := ⟨by omega⟩
  have hvu : (⟨v, hvG⟩ : sobolevGaugeGroup hs) = toSubgroup hs u :=
    IsCancelSMul.right_cancel _ _ x.toFramedFieldSpace (Subtype.ext (hv.trans huxy.symm))
  rwa [show v = (toSubgroup hs u : ℂ → Circle) from congrArg Subtype.val hvu] at hconv

/-- Off the compact set where `|α| ≤ 1 / 2`, the gauges differ by at most four times the
differences of the section coordinates. -/
private theorem norm_sub_le_of_gaugeTransform_eq
    (hxy : ∀ i, gaugeTransform (toSubgroup hs (us i) : ℂ → Circle) (xs i) = ys i)
    (huxy : gaugeTransform (toSubgroup hs u : ℂ → Circle) x = y) (i : ι) {z : ℂ}
    (hz : z ∉ {z | ‖sectionValue x z‖ ≤ 1 / 2}) :
    ‖((toSubgroup hs (us i) : ℂ → Circle) z : ℂ) - (toSubgroup hs u : ℂ → Circle) z‖ ≤
      4 * (|xs i z 2 - x z 2| + |xs i z 3 - x z 3| +
        (|ys i z 2 - y z 2| + |ys i z 3 - y z 3|)) := by
  refine (norm_coe_sub_coe_le huxy (hxy i) (not_le.1 hz).le).trans ?_
  linarith [norm_sectionValue_sub_le x (xs i) z, norm_sectionValue_sub_le y (ys i) z]

/-- Gauges between convergent fields converge uniformly on the whole plane. -/
private theorem tendstoUniformly_of_gaugeTransform_eq (hk : 2 < k) [l.NeBot]
    (hxy : ∀ i, gaugeTransform (toSubgroup hs (us i) : ℂ → Circle) (xs i) = ys i)
    (huxy : gaugeTransform (toSubgroup hs u : ℂ → Circle) x = y)
    (hx : Tendsto xs l (𝓝 x)) (hy : Tendsto ys l (𝓝 y)) :
    TendstoUniformly (fun i z ↦ ((toSubgroup hs (us i) : ℂ → Circle) z : ℂ))
      (fun z ↦ ((toSubgroup hs u : ℂ → Circle) z : ℂ)) l := by
  have hk1 : (1 : ℝ) < k := by exact_mod_cast (by omega : 1 < k)
  have hcoord (a b : EuclideanSpace ℝ (Fin 4)) (j : Fin 4) : |a j - b j| ≤ ‖a - b‖ := by
    simpa [Real.norm_eq_abs] using PiLp.norm_apply_le (a - b) j
  have hUK := tendstoLocallyUniformly_iff_forall_isCompact.1
    (tendstoLocallyUniformly_of_gaugeTransform_eq hk hxy huxy hx hy) _
    (isCompact_setOf_norm_sectionValue_le hk1 x (by norm_num : (1 : ℝ) / 2 < 1))
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  filter_upwards [Metric.tendstoUniformly_iff.1 (tendstoUniformly_of_tendsto hk1 hx) (ε / 16)
      (by positivity), Metric.tendstoUniformly_iff.1 (tendstoUniformly_of_tendsto hk1 hy) (ε / 16)
      (by positivity), Metric.tendstoUniformlyOn_iff.1 hUK ε hε] with i hxi hyi hKi z
  by_cases hz : z ∈ {z | ‖sectionValue x z‖ ≤ 1 / 2}
  · exact hKi z hz
  · have hx' := hxi z
    have hy' := hyi z
    rw [dist_comm, dist_eq_norm] at hx' hy'
    rw [dist_comm, dist_eq_norm]
    refine (norm_sub_le_of_gaugeTransform_eq hxy huxy i hz).trans_lt ?_
    linarith [hcoord (xs i z) (x z) 2, hcoord (xs i z) (x z) 3, hcoord (ys i z) (y z) 2,
      hcoord (ys i z) (y z) 3]

/-- The coordinate differences of convergent fields tend to zero in `L²`, in the combination that
bounds the gauges off the compact set where `|α| ≤ 1 / 2`. -/
private theorem tendsto_eLpNorm_coord (hx : Tendsto xs l (𝓝 x)) (hy : Tendsto ys l (𝓝 y)) :
    Tendsto (fun i ↦ eLpNorm (fun z ↦ 4 * (|xs i z 2 - x z 2| + |xs i z 3 - x z 3| +
      (|ys i z 2 - y z 2| + |ys i z 3 - y z 3|))) 2 volume) l (𝓝 0) := by
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hcd (a b : SobolevFieldSpace f m k) (j : Fin 4) : Continuous fun z ↦ a z j - b z j :=
    ((EuclideanSpace.proj j).continuous.comp a.continuous).sub
      ((EuclideanSpace.proj j).continuous.comp b.continuous)
  have habs (a b : SobolevFieldSpace f m k) (j : Fin 4) :
      eLpNorm (fun z ↦ |a z j - b z j|) 2 volume = eLpNorm (fun z ↦ a z j - b z j) 2 volume := by
    simpa only [Real.norm_eq_abs] using eLpNorm_norm _ (hcd a b j).aestronglyMeasurable
  have hS := ENNReal.Tendsto.const_mul (((tendsto_eLpNorm_sub_of_tendsto hk0 hx 2).add
    (tendsto_eLpNorm_sub_of_tendsto hk0 hx 3)).add ((tendsto_eLpNorm_sub_of_tendsto hk0 hy 2).add
      (tendsto_eLpNorm_sub_of_tendsto hk0 hy 3))) (Or.inr (by norm_num : (4 : ℝ≥0∞) ≠ ∞))
  simp only [add_zero, mul_zero] at hS
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hS (fun _ ↦ bot_le)
    fun i ↦ ?_
  rw [show (fun z ↦ 4 * (|xs i z 2 - x z 2| + |xs i z 3 - x z 3| +
      (|ys i z 2 - y z 2| + |ys i z 3 - y z 3|))) = (4 : ℝ) • fun z ↦ |xs i z 2 - x z 2| +
        |xs i z 3 - x z 3| + (|ys i z 2 - y z 2| + |ys i z 3 - y z 3|) from rfl, eLpNorm_const_smul,
    Real.eNorm_eq_ofReal (by norm_num), ENNReal.ofReal_ofNat]
  gcongr
  refine (eLpNorm_add_le one_le_two).trans (add_le_add ?_ ?_)
  · rw [← habs (xs i) x 2, ← habs (xs i) x 3]
    exact eLpNorm_add_le one_le_two
  · rw [← habs (ys i) y 2, ← habs (ys i) y 3]
    exact eLpNorm_add_le one_le_two

/-- Gauges between convergent fields converge in `L²`. -/
private theorem tendsto_eLpNorm_of_gaugeTransform_eq (hk : 2 < k) [l.NeBot]
    (hxy : ∀ i, gaugeTransform (toSubgroup hs (us i) : ℂ → Circle) (xs i) = ys i)
    (huxy : gaugeTransform (toSubgroup hs u : ℂ → Circle) x = y)
    (hx : Tendsto xs l (𝓝 x)) (hy : Tendsto ys l (𝓝 y)) :
    Tendsto (fun i ↦ eLpNorm (fun z ↦
      ((toSubgroup hs (us i) : ℂ → Circle) z : ℂ) - (toSubgroup hs u : ℂ → Circle) z) 2 volume)
      l (𝓝 0) := by
  have hk1 : (1 : ℝ) < k := by exact_mod_cast (by omega : 1 < k)
  have h2 := two_lt_add_one hk
  have hK := isCompact_setOf_norm_sectionValue_le hk1 x (by norm_num : (1 : ℝ) / 2 < 1)
  set K := {z | ‖sectionValue x z‖ ≤ 1 / 2}
  set G : ι → ℂ → ℝ := fun i z ↦ 4 *
    (|xs i z 2 - x z 2| + |xs i z 3 - x z 3| + (|ys i z 2 - y z 2| + |ys i z 3 - y z 3|))
  set D : ι → ℂ → ℂ := fun i z ↦
    ((toSubgroup hs (us i) : ℂ → Circle) z : ℂ) - (toSubgroup hs u : ℂ → Circle) z
  have hDc (i : ι) : Continuous (D i) :=
    (differentiable_of_mem_sobolevGaugeGroup h2 (toSubgroup hs (us i)).2).continuous.sub
      (differentiable_of_mem_sobolevGaugeGroup h2 (toSubgroup hs u).2).continuous
  -- Off `K` the gauges are controlled by the sections; on `K` they converge uniformly.
  have hG : Tendsto (fun i ↦ eLpNorm (G i) 2 volume) l (𝓝 0) := tendsto_eLpNorm_coord hx hy
  have hDK : Tendsto (fun i ↦ eLpNorm (K.indicator (D i)) 2 volume) l (𝓝 0) := by
    refine tendsto_eLpNorm_zero_of_eventually_le_mul (b := K.indicator fun _ ↦ (1 : ℝ))
      (by rw [eLpNorm_indicator_const hK.isClosed.measurableSet.nullMeasurableSet two_ne_zero
          ENNReal.ofNat_ne_top]
          exact ENNReal.mul_ne_top eNorm_ne_top
            (ENNReal.rpow_ne_top_of_nonneg (by positivity) hK.measure_lt_top.ne))
      (Eventually.of_forall fun i ↦ ((hDc i).aestronglyMeasurable.indicator
        hK.isClosed.measurableSet)) fun δ hδ ↦ ?_
    filter_upwards [Metric.tendstoUniformlyOn_iff.1 (tendstoLocallyUniformly_iff_forall_isCompact.1
      (tendstoLocallyUniformly_of_gaugeTransform_eq hk hxy huxy hx hy) _ hK) δ
        (NNReal.coe_pos.2 hδ)] with i hi
    refine Eventually.of_forall fun z ↦ ?_
    by_cases hz : z ∈ K
    · have := hi z hz
      rw [dist_comm, dist_eq_norm] at this
      rw [Set.indicator_of_mem hz, Set.indicator_of_mem hz, ← ofReal_norm,
        ← ofReal_norm, norm_one, ENNReal.ofReal_one, mul_one, ← ENNReal.ofReal_coe_nnreal]
      exact ENNReal.ofReal_le_ofReal this.le
    · simp [Set.indicator_of_notMem hz]
  have hle (i : ι) : eLpNorm (D i) 2 volume ≤
      eLpNorm (G i) 2 volume + eLpNorm (K.indicator (D i)) 2 volume := by
    rw [← eLpNorm_norm (K.indicator (D i))
      ((hDc i).aestronglyMeasurable.indicator hK.isClosed.measurableSet)]
    refine (eLpNorm_mono_ae (g := G i + fun z ↦ ‖K.indicator (D i) z‖)
      (hDc i).aestronglyMeasurable (Eventually.of_forall fun z ↦ ?_)).trans
      (eLpNorm_add_le one_le_two)
    rw [Pi.add_apply, Real.norm_eq_abs]
    refine le_trans ?_ (le_abs_self _)
    by_cases hz : z ∈ K
    · rw [Set.indicator_of_mem hz]
      linarith [show 0 ≤ G i z by positivity]
    · rw [Set.indicator_of_notMem hz, norm_zero, add_zero]
      exact norm_sub_le_of_gaugeTransform_eq hxy huxy i hz
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (by simpa using hG.add hDK) (fun _ ↦ bot_le) hle

/-- The logarithmic derivatives of `u⁻¹ uᵢ` are represented in `H^k(ℂ)` by elements tending to
zero: in each direction they are differences of the connection differences of `(xᵢ, yᵢ)` and of
`(x, y)`. -/
private theorem exists_tendsto_gaugeForm_inv_mul (hk : 2 < k)
    (hxy : ∀ i, gaugeTransform (toSubgroup hs (us i) : ℂ → Circle) (xs i) = ys i)
    (huxy : gaugeTransform (toSubgroup hs u : ℂ → Circle) x = y)
    (hx : Tendsto xs l (𝓝 x)) (hy : Tendsto ys l (𝓝 y)) :
    ∃ g : ι → ℂ → H^{(k : ℝ)}(ℂ),
      (∀ i v, inclusionLp (Nat.cast_nonneg (α := ℝ) k) (g i v) =ᵐ[volume]
        fun z ↦ (gaugeForm (toSubgroup hs (u⁻¹ * us i) : ℂ → Circle) z v : ℂ)) ∧
      ∀ v, Tendsto (fun i ↦ g i v) l (𝓝 0) := by
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have h2 := two_lt_add_one hk
  have hdiff (v : SobolevTopologicalGaugeGroup hs) :=
    differentiable_of_mem_sobolevGaugeGroup h2 (toSubgroup hs v).2
  have hsubRef (a : SobolevFieldSpace f m k) (j : Fin 4) :
      (inclusionLp hk0 (subRef a j) : ℂ → ℂ) =ᵐ[volume]
        fun z ↦ ((a z j - referenceField f m z j : ℝ) : ℂ) := by
    rw [← toLp_inclusion]
    exact coeFn_toLp_inclusion_subRef hk0 a j
  set G : ι → Fin 4 → H^{(k : ℝ)}(ℂ) := fun i j ↦
    subRef (xs i) j - subRef (ys i) j - (subRef x j - subRef y j)
  have hGae (i : ι) (j : Fin 4) : (inclusionLp hk0 (G i j) : ℂ → ℂ) =ᵐ[volume]
      fun z ↦ ((xs i z j - ys i z j - (x z j - y z j) : ℝ) : ℂ) := by
    simp only [G, map_sub]
    filter_upwards [hsubRef (xs i) j, hsubRef (ys i) j, hsubRef x j, hsubRef y j,
      Lp.coeFn_sub (inclusionLp hk0 (subRef (xs i) j) - inclusionLp hk0 (subRef (ys i) j))
        (inclusionLp hk0 (subRef x j) - inclusionLp hk0 (subRef y j)),
      Lp.coeFn_sub (inclusionLp hk0 (subRef (xs i) j)) (inclusionLp hk0 (subRef (ys i) j)),
      Lp.coeFn_sub (inclusionLp hk0 (subRef x j)) (inclusionLp hk0 (subRef y j))]
      with z h₁ h₂ h₃ h₄ h₅ h₆ h₇
    rw [h₅, Pi.sub_apply, h₆, h₇, Pi.sub_apply, Pi.sub_apply, h₁, h₂, h₃, h₄]
    push_cast
    ring
  have hgf (i : ι) (z v : ℂ) : gaugeForm (toSubgroup hs (u⁻¹ * us i) : ℂ → Circle) z v =
      (xs i z 0 - ys i z 0 - (x z 0 - y z 0)) * v.re +
        (xs i z 1 - ys i z 1 - (x z 1 - y z 1)) * v.im := by
    have hinv : DifferentiableAt ℝ
        (fun z ↦ (((toSubgroup hs u : ℂ → Circle)⁻¹ : ℂ → Circle) z : ℂ)) z :=
      Circle.differentiableAt_coe_inv (hdiff u z)
    rw [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv,
      gaugeForm_mul hinv (hdiff (us i) z), gaugeForm_inv (hdiff u z), add_apply, neg_apply,
      ((gaugeTransform_eq_iff.1 (hxy i)) z).1, ((gaugeTransform_eq_iff.1 huxy) z).1]
    simp only [add_apply, smul_apply, reCLM_apply, imCLM_apply, smul_eq_mul]
    ring
  refine ⟨fun i v ↦ (v.re : ℂ) • G i 0 + (v.im : ℂ) • G i 1, fun i v ↦ ?_, fun v ↦ ?_⟩
  · simp only [map_add, map_smul]
    filter_upwards [hGae i 0, hGae i 1,
      Lp.coeFn_add ((v.re : ℂ) • inclusionLp hk0 (G i 0)) ((v.im : ℂ) • inclusionLp hk0 (G i 1)),
      Lp.coeFn_smul (v.re : ℂ) (inclusionLp hk0 (G i 0)),
      Lp.coeFn_smul (v.im : ℂ) (inclusionLp hk0 (G i 1))] with z h₀ h₁ h₂ h₃ h₄
    rw [h₂, Pi.add_apply, h₃, h₄, Pi.smul_apply, Pi.smul_apply, h₀, h₁, hgf]
    push_cast
    simp only [smul_eq_mul]
    ring
  · have hG (j : Fin 4) : Tendsto (fun i ↦ G i j) l (𝓝 0) := by
      have := ((tendsto_iff.1 hx j).sub (tendsto_iff.1 hy j)).sub
        (tendsto_const_nhds (x := subRef x j - subRef y j))
      simpa only [sub_self] using this
    simpa only [smul_zero, add_zero] using
      ((hG 0).const_smul (v.re : ℂ)).add ((hG 1).const_smul (v.im : ℂ))

/-- **Gauges between convergent fields converge in `G_(k+1)`.** Let `k ≥ 3`. If fields `xᵢ → x`
and `yᵢ → y` converge in `A_m^k`, and the Sobolev gauges `uᵢ, u ∈ G_(k+1)` satisfy `uᵢ · xᵢ = yᵢ`
and `u · x = y`, then `uᵢ → u` in `G_(k+1)`. -/
theorem tendsto_of_gaugeTransform_eq (hk : 2 < k)
    (hxy : ∀ i, gaugeTransform (toSubgroup hs (us i) : ℂ → Circle) (xs i) = ys i)
    (huxy : gaugeTransform (toSubgroup hs u : ℂ → Circle) x = y)
    (hx : Tendsto xs l (𝓝 x)) (hy : Tendsto ys l (𝓝 y)) : Tendsto us l (𝓝 u) := by
  rcases l.eq_or_neBot with rfl | hl
  · exact tendsto_bot
  -- The quotients `wᵢ = u⁻¹ uᵢ` satisfy `|wᵢ - 1| = |uᵢ - u|`.
  have hwn (i : ι) (z : ℂ) : ((toSubgroup hs (u⁻¹ * us i) : ℂ → Circle) z : ℂ) - 1 =
      ((((toSubgroup hs u : ℂ → Circle) z)⁻¹ : Circle) : ℂ) *
        (((toSubgroup hs (us i) : ℂ → Circle) z : ℂ) - (toSubgroup hs u : ℂ → Circle) z) := by
    rw [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv, Pi.mul_apply, Pi.inv_apply,
      coe_inv_mul_sub_one]
  have hunif := tendstoUniformly_of_gaugeTransform_eq hk hxy huxy hx hy
  have hL2 := tendsto_eLpNorm_of_gaugeTransform_eq hk hxy huxy hx hy
  obtain ⟨g, hg, hg₀⟩ := exists_tendsto_gaugeForm_inv_mul hk hxy huxy hx hy
  have hw : Tendsto (fun i ↦ u⁻¹ * us i) l (𝓝 1) := by
    refine SobolevTopologicalGaugeGroup.tendsto_one_of_tendsto_gaugeForm (by omega) ?_ ?_ hg hg₀
    · rw [Metric.tendstoUniformly_iff] at hunif ⊢
      intro ε hε
      filter_upwards [hunif ε hε] with i hi z
      rw [dist_comm, dist_eq_norm, hwn, norm_mul, Circle.norm_coe, one_mul, ← dist_eq_norm,
        dist_comm]
      exact hi z
    · refine hL2.congr fun i ↦ eLpNorm_congr_norm_ae ?_ ?_ (Eventually.of_forall fun z ↦ ?_)
      · exact ((differentiable_of_mem_sobolevGaugeGroup (two_lt_add_one hk)
          (toSubgroup hs (us i)).2).continuous.sub (differentiable_of_mem_sobolevGaugeGroup
            (two_lt_add_one hk) (toSubgroup hs u).2).continuous).aestronglyMeasurable
      · exact ((differentiable_of_mem_sobolevGaugeGroup (two_lt_add_one hk)
          (toSubgroup hs (u⁻¹ * us i)).2).continuous.sub continuous_const).aestronglyMeasurable
      · rw [hwn, norm_mul, Circle.norm_coe, one_mul]
  simpa using (tendsto_const_nhds (x := u)).mul hw

end Convergence

/-- **The Sobolev gauge group acts properly on `A_m^k`**, `k ≥ 3`: if fields `xᵢ → x` and
`yᵢ → y` converge in `A_m^k` and `uᵢ · xᵢ = yᵢ` for Sobolev gauges `uᵢ ∈ G_(k+1)`, then the gauges
converge in `G_(k+1)` to a gauge `u` with `u · x = y`. -/
theorem exists_gaugeTransform_eq_and_tendsto (hk : 2 < k) {ι : Type*} {l : Filter ι} [l.NeBot]
    {xs ys : ι → SobolevFieldSpace f m k} {x y : SobolevFieldSpace f m k}
    {us : ι → SobolevTopologicalGaugeGroup hs}
    (hxy : ∀ i, gaugeTransform (toSubgroup hs (us i) : ℂ → Circle) (xs i) = ys i)
    (hx : Tendsto xs l (𝓝 x)) (hy : Tendsto ys l (𝓝 y)) :
    ∃ u : SobolevTopologicalGaugeGroup hs,
      gaugeTransform (toSubgroup hs u : ℂ → Circle) x = y ∧ Tendsto us l (𝓝 u) := by
  have hk1 : (1 : ℝ) < k := by exact_mod_cast (by omega : 1 < k)
  have h2 := two_lt_add_one hk
  obtain ⟨v, hvG, hv, -⟩ :=
    exists_mem_sobolevGaugeGroup_gaugeTransform_eq_and_tendstoLocallyUniformly hk
      (fun i ↦ differentiable_of_mem_sobolevGaugeGroup h2 (toSubgroup hs (us i)).2) hxy
      (tendstoUniformly_of_tendsto hk1 hx).tendstoLocallyUniformly
      (tendstoUniformly_of_tendsto hk1 hy).tendstoLocallyUniformly
      x.continuous y.continuous x.mem_framedFieldSpace y.mem_framedFieldSpace
  refine ⟨(toSubgroup hs).symm ⟨v, hvG⟩, ?_, tendsto_of_gaugeTransform_eq hk hxy ?_ hx hy⟩ <;>
    simpa using hv

end SobolevFieldSpace

end TauCeti.Vortex
