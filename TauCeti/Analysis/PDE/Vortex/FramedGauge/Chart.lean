/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Algebra.LieGroup
public import TauCeti.Analysis.PDE.Vortex.FramedGauge.Topology
public import TauCeti.Analysis.Sobolev.BesselPotential.Real
import TauCeti.Analysis.PDE.Vortex.FramedGauge.Exponential
import TauCeti.Analysis.Sobolev.BesselPotential.Embedding

/-!
# The exponential charts and the Lie group structure of the Sobolev framed gauge group

For a real order `s > 1`, the Sobolev framed gauge group
`G_s = {1 + h : h ∈ H^s(ℂ; ℂ), |1 + h| = 1}` (`TauCeti.Vortex.SobolevTopologicalGaugeGroup`) is a
Hausdorff topological group for the topology of `u - 1` in `H^s(ℂ)`. Its infinitesimal gauge
transformations are the real phases, the real Hilbert space `H^s(ℂ; ℝ)`, here the closed real
subspace `BesselPotentialSpace.realSubmodule` of `H^s(ℂ)`. This file shows that the exponential map
`F ↦ exp (i F)` is an open embedding of `H^s(ℂ; ℝ)` into `G_s`, and that its translates form an
atlas making `G_s` an analytic Banach Lie group modelled on `H^s(ℂ; ℝ)`.

The exponential `expGauge hs F` is the gauge `z ↦ exp (i F(z))` of the continuous representative
of `F` (`BesselPotentialSpace.realContinuousRep`), which lies in `G_s` by
`TauCeti.Vortex.exp_mem_sobolevGaugeGroup`. The exponential turns sums into products
(`expGauge_add`), so it is a homomorphism from the additive group of `H^s(ℂ; ℝ)` to `G_s`, and:

* **It is injective** (`expGauge_injective`). Two continuous phases with the same exponential differ
  by a constant in `2πℤ`, which vanishes since both phases vanish at infinity
  (`TauCeti.Vortex.injOn_exp`). No restriction to a small ball is needed.
* **It is locally Lipschitz** in the coordinate `u - 1` of `G_s`
  (`exists_norm_subOne_expGauge_sub_le`), hence continuous (`continuous_expGauge`).
* **Its image contains a neighbourhood of the identity, with a Lipschitz inverse there**
  (`exists_forall_exists_expGauge_eq_and_norm_le`): there are `δ > 0` and `K` such that every
  `u ∈ G_s` with `‖u - 1‖_{H^s} < δ` is `exp (i F)` for a real `F` with
  `‖F‖_{H^s} ≤ K ‖u - 1‖_{H^s}`. The phase is `F = arg u`, which lies in `H^s` by the logarithm
  series (`TauCeti.Vortex.exists_memSobolev_ae_eq_arg_and_norm_sub_le`).

The last statement makes the exponential open at `0`, and the homomorphism property makes it open
everywhere (`isOpenEmbedding_expGauge`). The exponential chart `expGaugeChart hs` is the resulting
open partial homeomorphism from `H^s(ℂ; ℝ)` onto the image of the exponential, an open subgroup of
`G_s`. The chart at `u ∈ G_s` is its translate `v ↦ F` with `u⁻¹ v = exp (i F)`. Since `G_s` is
abelian, the coordinate change between the charts at `u` and `w` is the translation by the phase of
`w⁻¹ u` (`exists_chartAt_symm_trans_chartAt_eq`), and in these charts multiplication and inversion
are the addition and negation of phases. Hence `G_s` is an analytic manifold and an analytic Lie
group modelled on `H^s(ℂ; ℝ)`, with the model with corners `𝓘(ℝ, H^s(ℂ; ℝ))`. Whether every element
of `G_s` is an exponential, which would make the exponential chart global, is not treated here.

## Main declarations

* `TauCeti.Vortex.SobolevTopologicalGaugeGroup.expGauge`: the exponential
  `H^s(ℂ; ℝ) → G_s`, `F ↦ exp (i F)`; `expGauge_add`, `expGauge_zero` and `expGauge_neg`: it is a
  homomorphism.
* `TauCeti.Vortex.SobolevTopologicalGaugeGroup.isOpenEmbedding_expGauge`: it is an open embedding.
* `TauCeti.Vortex.SobolevTopologicalGaugeGroup.expGaugeChart`: the exponential chart.
* `TauCeti.Vortex.SobolevTopologicalGaugeGroup.instChartedSpace`: the charted space structure of
  `G_s` modelled on `H^s(ℂ; ℝ)`, with an analytic `IsManifold` structure and a `LieGroup`
  structure of class `ω` for `𝓘(ℝ, H^s(ℂ; ℝ))`.

## References

* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III.
* M. E. Taylor, *Partial Differential Equations III: Nonlinear Equations*, 2nd ed., Applied
  Mathematical Sciences 117, Springer, 2011, Chapter 13, Section 3.
-/

public section

noncomputable section

namespace TauCeti.Vortex

open Complex Filter MeasureTheory Module TemperedDistribution BesselPotentialSpace Topology
  Manifold
open scoped SchwartzMap BesselPotentialSpace ContDiff

variable {s : ℝ}

namespace SobolevTopologicalGaugeGroup

variable {hs : 1 < s}

variable (hs) in
/-- **The exponential of a real Sobolev phase**, `F ↦ exp (i F)`, from the real subspace
`H^s(ℂ; ℝ)` of `H^s(ℂ)` to the Sobolev gauge group `G_s`, `s > 1`. The gauge is
`z ↦ exp (i F(z))` for the continuous representative of `F`
(`BesselPotentialSpace.realContinuousRep`). -/
def expGauge (F : realSubmodule (E := ℂ) (zero_le_one.trans hs.le)) :
    SobolevTopologicalGaugeGroup hs :=
  (toSubgroup hs).symm
    ⟨fun z ↦ Circle.exp (realContinuousRep (finrank_real_complex_lt_two_mul hs) F z),
      exp_mem_sobolevGaugeGroup hs (realContinuousRep _ F).continuous
        (realContinuousRep_mem_realSobolevFunctions _ F)⟩

/-- The gauge `exp (i F)` is pointwise the exponential of the continuous representative of `F`. -/
@[simp]
theorem toSubgroup_expGauge_apply (F : realSubmodule (E := ℂ) (zero_le_one.trans hs.le)) (z : ℂ) :
    (toSubgroup hs (expGauge hs F) : ℂ → Circle) z =
      Circle.exp (realContinuousRep (finrank_real_complex_lt_two_mul hs) F z) := by
  simp only [expGauge, MulEquiv.apply_symm_apply]

/-- Two elements of `G_s` with the same values are equal. -/
private theorem ext_toSubgroup {u v : SobolevTopologicalGaugeGroup hs}
    (h : ∀ z, (toSubgroup hs u : ℂ → Circle) z = (toSubgroup hs v : ℂ → Circle) z) : u = v :=
  (toSubgroup hs).injective (Subtype.ext (funext h))

/-- The exponential of the zero phase is the identity gauge. -/
@[simp]
theorem expGauge_zero : expGauge hs 0 = 1 :=
  ext_toSubgroup fun z ↦ by simp

/-- **The exponential turns sums into products**: `exp (i (F + G)) = exp (i F) exp (i G)`. -/
@[simp]
theorem expGauge_add (F G : realSubmodule (E := ℂ) (zero_le_one.trans hs.le)) :
    expGauge hs (F + G) = expGauge hs F * expGauge hs G :=
  ext_toSubgroup fun z ↦ by simp [Circle.exp_add]

/-- The exponential of `-F` is the inverse of the exponential of `F`. -/
@[simp]
theorem expGauge_neg (F : realSubmodule (E := ℂ) (zero_le_one.trans hs.le)) :
    expGauge hs (-F) = (expGauge hs F)⁻¹ :=
  eq_inv_of_mul_eq_one_left (by rw [← expGauge_add, neg_add_cancel, expGauge_zero])

/-- **The exponential of real Sobolev phases is injective**: two continuous phases in `H^s` with
the same exponential are equal, since their difference is a constant in `2πℤ` vanishing at
infinity. -/
theorem expGauge_injective : Function.Injective (expGauge hs) := by
  intro F G hFG
  have hs' := finrank_real_complex_lt_two_mul hs
  refine realContinuousRep_injective hs' (DFunLike.coe_injective ?_)
  refine injOn_exp hs ⟨(realContinuousRep hs' F).continuous,
    realContinuousRep_mem_realSobolevFunctions hs' F⟩ ⟨(realContinuousRep hs' G).continuous,
    realContinuousRep_mem_realSobolevFunctions hs' G⟩ (funext fun z ↦ ?_)
  simpa using congrFun (congrArg (fun u ↦ (toSubgroup hs u : ℂ → Circle)) hFG) z

/-- The `L²` function of the coordinate `exp (i F) - 1` is `exp (i F) - 1`. -/
theorem coeFn_toLp_inclusion_subOne_expGauge (h : 0 ≤ s)
    (F : realSubmodule (E := ℂ) (zero_le_one.trans hs.le)) :
    ⇑(inclusion h (subOne (expGauge hs F))).toLp =ᵐ[volume]
      fun z ↦
        (Circle.exp (realContinuousRep (finrank_real_complex_lt_two_mul hs) F z) : ℂ) - 1 := by
  simpa only [toSubgroup_expGauge_apply] using coeFn_toLp_inclusion_subOne h (expGauge hs F)

/-- **The exponential is locally Lipschitz in the coordinate `u - 1`.** There is a constant `C`
such that for real phases `F, G` of `H^s` norm at most `R`,
`‖(exp (i F) - 1) - (exp (i G) - 1)‖_{H^s} ≤ exp (C R) ‖F - G‖_{H^s}`. -/
theorem exists_norm_subOne_expGauge_sub_le (hs : 1 < s) :
    ∃ C, 0 ≤ C ∧ ∀ {F G : realSubmodule (E := ℂ) (zero_le_one.trans hs.le)} {R : ℝ},
      ‖F‖ ≤ R → ‖G‖ ≤ R →
      ‖subOne (expGauge hs F) - subOne (expGauge hs G)‖ ≤ Real.exp (C * R) * ‖F - G‖ := by
  obtain ⟨C, hC, hlip⟩ := exists_norm_toBesselPotentialSpace_sub_le_of_ae_eq_exp hs
  refine ⟨C, hC, fun {F G R} hFR hGR ↦ ?_⟩
  have h : (0 : ℝ) ≤ s := zero_le_one.trans hs.le
  have hs' := finrank_real_complex_lt_two_mul hs
  have hle := hlip (coeFn_toLp_inclusion_ae_eq_realContinuousRep hs' F)
    (coeFn_toLp_inclusion_ae_eq_realContinuousRep hs' G) (memSobolev_toLp_inclusion h F.1)
    (memSobolev_toLp_inclusion h G.1) (R := R)
    (by rwa [toBesselPotentialSpace_memSobolev_toLp_inclusion])
    (by rwa [toBesselPotentialSpace_memSobolev_toLp_inclusion])
    (coeFn_toLp_inclusion_subOne_expGauge (hs := hs) h F)
    (coeFn_toLp_inclusion_subOne_expGauge (hs := hs) h G)
    (memSobolev_toLp_inclusion h _) (memSobolev_toLp_inclusion h _)
  simpa only [toBesselPotentialSpace_memSobolev_toLp_inclusion, ← Submodule.coe_sub,
    Submodule.norm_coe] using hle

/-- The coordinate `exp (i F) - 1` depends continuously on the real phase `F`. -/
theorem continuous_subOne_expGauge : Continuous fun F ↦ subOne (expGauge hs F) := by
  obtain ⟨C, -, hlip⟩ := exists_norm_subOne_expGauge_sub_le hs
  refine continuous_iff_continuousAt.2 fun F ↦ tendsto_iff_norm_sub_tendsto_zero.2 ?_
  -- Near `F` the phases have norm at most `‖F‖ + 1`, where the exponential is Lipschitz.
  refine squeeze_zero' (Eventually.of_forall fun _ ↦ norm_nonneg _) ?_
    (by simpa using (tendsto_norm_sub_self F).const_mul (Real.exp (C * (‖F‖ + 1))))
  filter_upwards [(continuous_norm.tendsto F).eventually (gt_mem_nhds (lt_add_one ‖F‖))]
    with G hG
  exact hlip hG.le (le_add_of_nonneg_right zero_le_one)

/-- **The exponential `H^s(ℂ; ℝ) → G_s` is continuous.** -/
@[fun_prop, continuity]
theorem continuous_expGauge : Continuous (expGauge hs) :=
  continuous_iff.2 ⟨continuous_subOne_expGauge,
    ((continuous_subOne_expGauge (hs := hs)).comp continuous_neg).congr fun F ↦ by simp⟩

/-- An `L²` function in `H^s` representing the phase `arg u` of a gauge `u ∈ G_s` is a real phase
whose exponential is `u`. -/
private theorem exists_expGauge_eq_of_ae_eq_arg {u : SobolevTopologicalGaugeGroup hs}
    {F : Lp ℂ 2 (volume : Measure ℂ)}
    (hF : F =ᵐ[volume] fun z ↦ (arg ((toSubgroup hs u : ℂ → Circle) z : ℂ) : ℂ))
    (hFs : MemSobolev s 2 (F : 𝓢'(ℂ, ℂ))) :
    ∃ Φ : realSubmodule (E := ℂ) (zero_le_one.trans hs.le),
      expGauge hs Φ = u ∧ (Φ : H^{s}(ℂ)) = hFs.toBesselPotentialSpace := by
  have h : (0 : ℝ) ≤ s := zero_le_one.trans hs.le
  have hs' := finrank_real_complex_lt_two_mul hs
  have hLF := toLp_inclusion_toBesselPotentialSpace h hFs rfl
  have hreal : hFs.toBesselPotentialSpace ∈ realSubmodule h := by
    rw [mem_realSubmodule]
    filter_upwards [hF] with z hz
    rw [hLF, hz, ofReal_im]
  refine ⟨⟨_, hreal⟩, ext_toSubgroup fun z ↦ ?_, rfl⟩
  -- The continuous representative of the phase is `arg u` almost everywhere, so its exponential
  -- is `exp (i arg u) = u` almost everywhere, hence everywhere by continuity.
  have hrep : (⇑(realContinuousRep hs' ⟨_, hreal⟩) : ℂ → ℝ) =ᵐ[volume]
      fun z ↦ arg ((toSubgroup hs u : ℂ → Circle) z : ℂ) := by
    filter_upwards [coeFn_toLp_inclusion_ae_eq_realContinuousRep hs' ⟨_, hreal⟩ (h := h), hF]
      with z hz hz'
    have hFz : (F : ℂ → ℂ) z = (realContinuousRep hs' ⟨_, hreal⟩ z : ℂ) :=
      (congrArg (fun g : Lp ℂ 2 (volume : Measure ℂ) ↦ (g : ℂ → ℂ) z) hLF.symm).trans hz
    exact ofReal_injective (hFz.symm.trans hz')
  have hu_cont : Continuous (toSubgroup hs u : ℂ → Circle) :=
    ((mem_sobolevGaugeGroup hs _).1 (toSubgroup hs u).2).1
  rw [toSubgroup_expGauge_apply]
  refine congrFun ((Continuous.ae_eq_iff_eq volume
    (Circle.exp.continuous.comp (realContinuousRep hs' ⟨_, hreal⟩).continuous) hu_cont).1 ?_) z
  filter_upwards [hrep] with z hz
  rw [Function.comp_apply, hz, Circle.exp_arg]

/-- **Elements of `G_s` near the identity are exponentials, with a Lipschitz phase.** There are
`δ > 0` and `K` such that every `u ∈ G_s` with `‖u - 1‖_{H^s} < δ` is `exp (i F)` for a real phase
`F ∈ H^s` with `‖F‖_{H^s} ≤ K ‖u - 1‖_{H^s}`. -/
theorem exists_forall_exists_expGauge_eq_and_norm_le (hs : 1 < s) :
    ∃ δ, 0 < δ ∧ ∃ K, 0 ≤ K ∧ ∀ u : SobolevTopologicalGaugeGroup hs, ‖subOne u‖ < δ →
      ∃ F : realSubmodule (E := ℂ) (zero_le_one.trans hs.le),
        expGauge hs F = u ∧ ‖F‖ ≤ K * ‖subOne u‖ := by
  obtain ⟨C, hC, harg⟩ := exists_memSobolev_ae_eq_arg_and_norm_sub_le hs
  have h : (0 : ℝ) ≤ s := zero_le_one.trans hs.le
  refine ⟨(2 * (C + 1))⁻¹, by positivity, 2, zero_le_two, fun u hu ↦ ?_⟩
  set R := ‖subOne u‖
  have hR : 0 ≤ R := norm_nonneg _
  have hCR : C * R ≤ 1 / 2 := by
    have : 2 * (C + 1) * R < 1 :=
      (lt_inv_mul_iff₀ (by positivity)).1 (by simpa [mul_comm] using hu)
    nlinarith
  -- The phases `arg u` and `arg 1 = 0` lie in `H^s`, with the Lipschitz bound between them.
  obtain ⟨F, F', hF, hF', hFs, hF's, hle⟩ := harg (coeFn_toLp_inclusion_subOne h u)
    (coeFn_toLp_inclusion_subOne h (1 : SobolevTopologicalGaugeGroup hs))
    (memSobolev_toLp_inclusion h _)
    (memSobolev_toLp_inclusion h _) (R := R)
    (by rw [toBesselPotentialSpace_memSobolev_toLp_inclusion])
    (by rw [toBesselPotentialSpace_memSobolev_toLp_inclusion, subOne_one, norm_zero]; exact hR)
    (by linarith)
  have hF'0 : hF's.toBesselPotentialSpace = 0 := by
    refine toLp_inclusion_injective h (?_ : (inclusion h _).toLp = (inclusion h 0).toLp)
    rw [toLp_inclusion_toBesselPotentialSpace h hF's rfl, map_zero, toLp_zero]
    refine Lp.ext ?_
    filter_upwards [hF', Lp.coeFn_zero ℂ 2 (volume : Measure ℂ)] with z hz hz₀
    rw [hz, hz₀]
    simp
  rw [toBesselPotentialSpace_memSobolev_toLp_inclusion,
    toBesselPotentialSpace_memSobolev_toLp_inclusion, subOne_one, sub_zero, hF'0, sub_zero] at hle
  obtain ⟨Φ, hΦ, hΦF⟩ := exists_expGauge_eq_of_ae_eq_arg hF hFs
  refine ⟨Φ, hΦ, ?_⟩
  calc ‖Φ‖ = ‖hFs.toBesselPotentialSpace‖ := by rw [← Submodule.norm_coe, hΦF]
    _ ≤ (1 - C * R)⁻¹ * R := hle
    _ ≤ 2 * R := by
      gcongr
      rw [inv_le_comm₀ (by linarith) two_pos]
      linarith

/-- **The exponential is open at the identity**: it maps every neighbourhood of `0` in
`H^s(ℂ; ℝ)` onto a neighbourhood of `1` in `G_s`. -/
theorem nhds_one_le_map_expGauge_nhds_zero :
    𝓝 (1 : SobolevTopologicalGaugeGroup hs) ≤ map (expGauge hs) (𝓝 0) := by
  obtain ⟨δ, hδ, K, hK, hexp⟩ := exists_forall_exists_expGauge_eq_and_norm_le hs
  intro V hV
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 (mem_map.1 hV)
  -- Gauges with `‖u - 1‖ < min δ (ε / (K + 1))` are exponentials of phases in the `ε`-ball.
  have hW : {u : SobolevTopologicalGaugeGroup hs | ‖subOne u‖ < min δ (ε / (K + 1))} ∈ 𝓝 1 :=
    (isOpen_lt (continuous_norm.comp continuous_subOne) continuous_const).mem_nhds
      (by simpa using lt_min hδ (div_pos hε (by linarith)))
  refine mem_of_superset hW fun u hu ↦ ?_
  rw [Set.mem_ofPred_eq] at hu
  obtain ⟨F, rfl, hF⟩ := hexp u (hu.trans_le (min_le_left _ _))
  refine hball (mem_ball_zero_iff.2 (hF.trans_lt ?_))
  have hu' := hu.trans_le (min_le_right _ _)
  calc K * ‖subOne (expGauge hs F)‖ ≤ (K + 1) * ‖subOne (expGauge hs F)‖ := by
        gcongr; linarith
    _ < (K + 1) * (ε / (K + 1)) := by gcongr
    _ = ε := mul_div_cancel₀ _ (by linarith)

/-- **The exponential `H^s(ℂ; ℝ) → G_s` is an open map.** -/
theorem isOpenMap_expGauge : IsOpenMap (expGauge hs) := by
  refine isOpenMap_iff_nhds_le.2 fun F ↦ ?_
  -- Translate the statement at `0` by the homomorphism property.
  have hcomp : (expGauge hs F * ·) ∘ expGauge hs = expGauge hs ∘ (F + ·) :=
    funext fun G ↦ (expGauge_add F G).symm
  calc 𝓝 (expGauge hs F) = map (expGauge hs F * ·) (𝓝 1) := (map_mul_left_nhds_one _).symm
    _ ≤ map (expGauge hs F * ·) (map (expGauge hs) (𝓝 0)) :=
        map_mono nhds_one_le_map_expGauge_nhds_zero
    _ = map (expGauge hs) (𝓝 F) := by
        rw [map_map, hcomp, ← map_map, map_add_left_nhds_zero]

/-- **The exponential chart of `G_s`**: `F ↦ exp (i F)` is an open embedding of the real Hilbert
space `H^s(ℂ; ℝ)` into the Sobolev gauge group `G_s`, `s > 1`. -/
theorem isOpenEmbedding_expGauge : IsOpenEmbedding (expGauge hs) :=
  .of_continuous_injective_isOpenMap continuous_expGauge expGauge_injective isOpenMap_expGauge

/-- The image of the exponential is an open subset of `G_s`, a neighbourhood of the identity. -/
theorem isOpen_range_expGauge : IsOpen (Set.range (expGauge hs)) :=
  isOpenEmbedding_expGauge.isOpen_range

/-! ### The exponential atlas -/

/-- The Sobolev gauge group is commutative. -/
protected theorem mul_comm (u v : SobolevTopologicalGaugeGroup hs) : u * v = v * u :=
  (toSubgroup hs).injective (by rw [map_mul, map_mul, mul_comm])

variable (hs) in
/-- **The exponential chart at the identity**: the open partial homeomorphism `F ↦ exp (i F)` from
`H^s(ℂ; ℝ)` onto the image of the exponential, an open neighbourhood of `1` in `G_s`. -/
def expGaugeChart :
    OpenPartialHomeomorph (realSubmodule (E := ℂ) (zero_le_one.trans hs.le))
      (SobolevTopologicalGaugeGroup hs) :=
  isOpenEmbedding_expGauge.toOpenPartialHomeomorph (expGauge hs)

/-- The exponential chart is the exponential. -/
@[simp]
theorem coe_expGaugeChart : ⇑(expGaugeChart hs) = expGauge hs :=
  isOpenEmbedding_expGauge.toOpenPartialHomeomorph_apply _

/-- The exponential chart is defined on all real phases. -/
@[simp]
theorem expGaugeChart_source : (expGaugeChart hs).source = Set.univ :=
  isOpenEmbedding_expGauge.toOpenPartialHomeomorph_source _

/-- The image of the exponential chart is the image of the exponential. -/
@[simp]
theorem expGaugeChart_target : (expGaugeChart hs).target = Set.range (expGauge hs) :=
  isOpenEmbedding_expGauge.toOpenPartialHomeomorph_target _

/-- The inverse of the exponential chart recovers the phase of an exponential. -/
@[simp]
theorem expGaugeChart_symm_expGauge (F : realSubmodule (E := ℂ) (zero_le_one.trans hs.le)) :
    (expGaugeChart hs).symm (expGauge hs F) = F :=
  isOpenEmbedding_expGauge.toOpenPartialHomeomorph_left_inv _

/-- **The charted space structure of `G_s`**, modelled on the real Hilbert space `H^s(ℂ; ℝ)`. The
chart at `u` is the exponential chart translated by `u`: it sends `v` to the phase `F` with
`u⁻¹ v = exp (i F)`, and is defined where `u⁻¹ v` is an exponential. -/
instance instChartedSpace : ChartedSpace (realSubmodule (E := ℂ) (zero_le_one.trans hs.le))
    (SobolevTopologicalGaugeGroup hs) where
  atlas := Set.range fun u : SobolevTopologicalGaugeGroup hs ↦
    (Homeomorph.mulLeft u⁻¹).toOpenPartialHomeomorph.trans (expGaugeChart hs).symm
  chartAt u := (Homeomorph.mulLeft u⁻¹).toOpenPartialHomeomorph.trans (expGaugeChart hs).symm
  mem_chart_source u := by
    simp only [OpenPartialHomeomorph.trans_source, Homeomorph.toOpenPartialHomeomorph_source,
      OpenPartialHomeomorph.symm_source, expGaugeChart_target, Set.univ_inter, Set.mem_preimage,
      Homeomorph.toOpenPartialHomeomorph_apply, Homeomorph.coe_mulLeft, inv_mul_cancel]
    exact ⟨0, expGauge_zero⟩
  chart_mem_atlas u := ⟨u, rfl⟩

/-- The chart of `G_s` at `u` sends `v` to the phase of `u⁻¹ v`. -/
theorem chartAt_apply (u v : SobolevTopologicalGaugeGroup hs) :
    chartAt (realSubmodule (E := ℂ) (zero_le_one.trans hs.le)) u v =
      (expGaugeChart hs).symm (u⁻¹ * v) :=
  (rfl)

/-- The inverse of the chart of `G_s` at `u` sends the phase `F` to `u exp (i F)`. -/
theorem chartAt_symm_apply (u : SobolevTopologicalGaugeGroup hs)
    (F : realSubmodule (E := ℂ) (zero_le_one.trans hs.le)) :
    (chartAt (realSubmodule (E := ℂ) (zero_le_one.trans hs.le)) u).symm F = u * expGauge hs F := by
  simp [chartAt, ChartedSpace.chartAt, Homeomorph.mulLeft_symm]

/-- The chart of `G_s` at `u` is defined at the `v` for which `u⁻¹ v` is an exponential. -/
theorem chartAt_source (u : SobolevTopologicalGaugeGroup hs) :
    (chartAt (realSubmodule (E := ℂ) (zero_le_one.trans hs.le)) u).source =
      {v | u⁻¹ * v ∈ Set.range (expGauge hs)} := by
  ext v
  simp only [chartAt, ChartedSpace.chartAt, OpenPartialHomeomorph.trans_source,
    Homeomorph.toOpenPartialHomeomorph_source, OpenPartialHomeomorph.symm_source,
    expGaugeChart_target, Set.univ_inter, Set.mem_preimage,
    Homeomorph.toOpenPartialHomeomorph_apply, Homeomorph.coe_mulLeft, Set.mem_ofPred_eq]

/-- In the exponential charts, the coordinate change from the chart at `u` to the chart at `w` is
the translation `F ↦ c + F` by the phase `c` of `w⁻¹ u`, wherever it is defined. -/
theorem exists_chartAt_symm_trans_chartAt_eq (u w : SobolevTopologicalGaugeGroup hs) :
    ∃ c : realSubmodule (E := ℂ) (zero_le_one.trans hs.le),
      ∀ F ∈ ((chartAt (realSubmodule (E := ℂ) (zero_le_one.trans hs.le)) u).symm ≫ₕ
        chartAt (realSubmodule (E := ℂ) (zero_le_one.trans hs.le)) w).source,
      ((chartAt (realSubmodule (E := ℂ) (zero_le_one.trans hs.le)) u).symm ≫ₕ
        chartAt (realSubmodule (E := ℂ) (zero_le_one.trans hs.le)) w) F = c + F := by
  rcases Set.eq_empty_or_nonempty ((chartAt (realSubmodule (E := ℂ) (zero_le_one.trans hs.le))
      u).symm ≫ₕ chartAt (realSubmodule (E := ℂ) (zero_le_one.trans hs.le)) w).source with
    h | ⟨F₀, hF₀⟩
  · exact ⟨0, fun F hF ↦ absurd (h ▸ hF) (Set.notMem_empty F)⟩
  -- On a nonempty overlap, `w⁻¹ u` is an exponential `exp (i c)`.
  rw [OpenPartialHomeomorph.trans_source, Set.mem_inter_iff, Set.mem_preimage, chartAt_source,
    chartAt_symm_apply] at hF₀
  obtain ⟨G, hG⟩ := hF₀.2
  refine ⟨G - F₀, fun F _ ↦ ?_⟩
  have hc : expGauge hs (G - F₀) = w⁻¹ * u := by
    rw [sub_eq_add_neg, expGauge_add, expGauge_neg, hG, mul_assoc, mul_inv_cancel_right]
  rw [OpenPartialHomeomorph.coe_trans, Function.comp_apply, chartAt_symm_apply, chartAt_apply,
    ← mul_assoc, ← hc, ← expGauge_add, expGaugeChart_symm_expGauge]

/-- **`G_s` is an analytic Banach manifold** modelled on `H^s(ℂ; ℝ)`: its coordinate changes are
translations. -/
instance : IsManifold 𝓘(ℝ, realSubmodule (E := ℂ) (zero_le_one.trans hs.le)) ω
    (SobolevTopologicalGaugeGroup hs) :=
  isManifold_of_contDiffOn _ _ _ fun e e' he he' ↦ by
    obtain ⟨u, rfl⟩ := he
    obtain ⟨w, rfl⟩ := he'
    obtain ⟨c, hc⟩ := exists_chartAt_symm_trans_chartAt_eq (hs := hs) u w
    simp only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, Function.id_comp,
      Function.comp_id, Set.range_id, Set.preimage_id_eq, id_eq, Set.inter_univ]
    exact (contDiff_const.add contDiff_id).contDiffOn.congr fun F hF ↦ hc F hF

/-- In the exponential charts at `u`, `v` and `u v`, multiplication is the addition of phases. -/
private theorem chartAt_mul_chartAt_symm (u v : SobolevTopologicalGaugeGroup hs)
    (F G : realSubmodule (E := ℂ) (zero_le_one.trans hs.le)) :
    chartAt (realSubmodule (E := ℂ) (zero_le_one.trans hs.le)) (u * v)
      ((chartAt (realSubmodule (E := ℂ) (zero_le_one.trans hs.le)) u).symm F *
        (chartAt (realSubmodule (E := ℂ) (zero_le_one.trans hs.le)) v).symm G) = F + G := by
  have h : (u * v)⁻¹ * (u * expGauge hs F * (v * expGauge hs G)) = expGauge hs (F + G) := by
    have hcomm : u * expGauge hs F * (v * expGauge hs G) =
        u * v * (expGauge hs F * expGauge hs G) := by
      rw [mul_assoc u, mul_assoc u, ← mul_assoc (expGauge hs F) v,
        SobolevTopologicalGaugeGroup.mul_comm (expGauge hs F) v, mul_assoc v]
    rw [hcomm, inv_mul_cancel_left, expGauge_add]
  rw [chartAt_symm_apply, chartAt_symm_apply, chartAt_apply, h, expGaugeChart_symm_expGauge]

/-- In the exponential charts at `u` and `u⁻¹`, inversion is the negation of phases. -/
private theorem chartAt_inv_chartAt_symm (u : SobolevTopologicalGaugeGroup hs)
    (F : realSubmodule (E := ℂ) (zero_le_one.trans hs.le)) :
    chartAt (realSubmodule (E := ℂ) (zero_le_one.trans hs.le)) u⁻¹
      ((chartAt (realSubmodule (E := ℂ) (zero_le_one.trans hs.le)) u).symm F)⁻¹ = -F := by
  rw [chartAt_symm_apply, chartAt_apply, inv_inv, mul_inv_rev,
    SobolevTopologicalGaugeGroup.mul_comm _ u⁻¹, mul_inv_cancel_left, ← expGauge_neg,
    expGaugeChart_symm_expGauge]

/-- **`G_s` is an analytic Banach Lie group** modelled on `H^s(ℂ; ℝ)`: in the exponential charts,
multiplication and inversion are the addition and negation of phases. -/
instance : LieGroup 𝓘(ℝ, realSubmodule (E := ℂ) (zero_le_one.trans hs.le)) ω
    (SobolevTopologicalGaugeGroup hs) where
  contMDiff_mul p := by
    rw [contMDiffAt_iff]
    refine ⟨continuous_mul.continuousAt, ?_⟩
    have h : extChartAt 𝓘(ℝ, realSubmodule (E := ℂ) (zero_le_one.trans hs.le)) (p.1 * p.2) ∘
        (fun q : SobolevTopologicalGaugeGroup hs × SobolevTopologicalGaugeGroup hs ↦ q.1 * q.2) ∘
        (extChartAt (𝓘(ℝ, realSubmodule (E := ℂ) (zero_le_one.trans hs.le)).prod
          𝓘(ℝ, realSubmodule (E := ℂ) (zero_le_one.trans hs.le))) p).symm =
        fun q ↦ q.1 + q.2 := by
      funext q
      -- The product chart at `p` is the product of the charts at `p.1` and `p.2`.
      exact chartAt_mul_chartAt_symm p.1 p.2 q.1 q.2
    rw [h]
    exact (contDiff_fst.add contDiff_snd).contDiffWithinAt
  contMDiff_inv u := by
    rw [contMDiffAt_iff]
    refine ⟨continuous_inv.continuousAt, ?_⟩
    have h : extChartAt 𝓘(ℝ, realSubmodule (E := ℂ) (zero_le_one.trans hs.le)) u⁻¹ ∘
        (fun v : SobolevTopologicalGaugeGroup hs ↦ v⁻¹) ∘
        (extChartAt 𝓘(ℝ, realSubmodule (E := ℂ) (zero_le_one.trans hs.le)) u).symm = Neg.neg := by
      funext F
      simpa using chartAt_inv_chartAt_symm u F
    rw [h]
    exact contDiff_neg.contDiffWithinAt

end SobolevTopologicalGaugeGroup

end TauCeti.Vortex
