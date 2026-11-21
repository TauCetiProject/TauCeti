/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.IsManifold.Basic
public import TauCeti.Analysis.PDE.Vortex.FramedGauge.Exponential
public import TauCeti.Analysis.PDE.Vortex.FramedGauge.Topology
public import TauCeti.Analysis.Sobolev.BesselPotential.Real

/-!
# Banach charts on the Sobolev framed gauge group

For a real order `s > 1`, the Sobolev framed gauge group `G_s` of plane vortices
(`TauCeti.Vortex.SobolevTopologicalGaugeGroup`) consists of the continuous circle-valued maps `u`
on the plane with `u - 1 ∈ H^s(ℂ)`, with the topology of the distance `‖u - v‖_{H^s}`. This file
makes `G_s` a manifold modelled on the real Hilbert space of real `H^s` phases, the closed
subspace `BesselPotentialSpace.realSubmodule ℂ h` of `H^s(ℂ)`, through the exponential
`F ↦ exp (i F)`.

**The exponential.** `TauCeti.Vortex.expGauge hs F` is the gauge `exp (i F)`, computed from the
continuous representative of the phase `F` (`TauCeti.Vortex.toSubgroup_expGauge`). It is an
additive character, that is a homomorphism from the additive group of phases to `G_s`, which is
injective (`TauCeti.Vortex.expGauge_injective`) and locally Lipschitz in
`H^s` (`TauCeti.Vortex.exists_norm_subOne_expGauge_sub_le`). Conversely every gauge `u` with
`C ‖u - 1‖_{H^s} < 1` is `exp (i F)` for a phase with
`‖F‖_{H^s} ≤ (1 - C ‖u - 1‖_{H^s})⁻¹ ‖u - 1‖_{H^s}`
(`TauCeti.Vortex.exists_expGauge_eq_and_norm_le`), namely `F = arg u`. Together these say that
the exponential is an open embedding (`TauCeti.Vortex.isOpenEmbedding_expGauge`), so its image is
an open subgroup of `G_s`.

**The charts.** The chart of `G_s` at `u` (`TauCeti.Vortex.gaugeChart`) is the inverse of
`F ↦ u exp (i F)`, defined on the open coset of `u` by the image of the exponential. Since the
exponential is a homomorphism, two charts differ by a translation of the model space on their
common domain (`TauCeti.Vortex.gaugeChart_symm_trans_eqOn_add`), so `G_s` is a manifold of every
smoothness class `n` over `ℝ`, analytic included
(`TauCeti.Vortex.SobolevTopologicalGaugeGroup.instIsManifold`). The group operations are smooth
in these charts (`TauCeti.Analysis.PDE.Vortex.FramedGauge.LieGroup`); the action of `G_(k+1)` on
the field space `A_m^k` is not treated here.

## References

* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Birkhäuser, 1980, Chapter III.
* C. H. Taubes, *Gr ⇒ SW: From pseudo-holomorphic curves to Seiberg–Witten solutions*,
  J. Differential Geom. 51 (1999), 203–334.
-/

public section

noncomputable section

namespace TauCeti.Vortex

open Complex Filter MeasureTheory Module Set TemperedDistribution BesselPotentialSpace Topology
open scoped SchwartzMap BesselPotentialSpace Manifold

variable {s : ℝ}

/-! ### The exponential -/

open SobolevTopologicalGaugeGroup

/-- **The exponential of a real phase**, as an additive character: the gauge `exp (i F) ∈ G_s` of
a real phase `F ∈ H^s(ℂ)`, `s > 1`, computed from its continuous representative
(`toSubgroup_expGauge`). It is an injective homomorphism from the additive group of phases
(`expGauge_injective`) and an open embedding (`isOpenEmbedding_expGauge`). -/
def expGauge (hs : 1 < s) :
    AddChar (realSubmodule ℂ (zero_le_one.trans hs.le)) (SobolevTopologicalGaugeGroup hs) where
  toFun F := (toSubgroup hs).symm
    ⟨fun z ↦ Circle.exp (continuousRep F z),
      exp_mem_sobolevGaugeGroup hs (continuous_continuousRep (finrank_real_complex_lt_two_mul hs) F)
        (continuousRep_mem_realSobolevFunctions (finrank_real_complex_lt_two_mul hs) F)⟩
  map_zero_eq_one' := by
    rw [MulEquiv.symm_apply_eq, map_one]
    refine Subtype.ext (funext fun z ↦ ?_)
    simp
  map_add_eq_mul' F G := by
    rw [MulEquiv.symm_apply_eq, map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
    refine Subtype.ext (funext fun z ↦ ?_)
    simp [Circle.exp_add]

/-- The gauge `expGauge hs F` is `z ↦ exp (i F(z))`, for the continuous representative of `F`. -/
@[simp]
theorem toSubgroup_expGauge (hs : 1 < s) (F : realSubmodule ℂ (zero_le_one.trans hs.le)) :
    (toSubgroup hs (expGauge hs F) : ℂ → Circle) = fun z ↦ Circle.exp (continuousRep F z) := by
  rw [expGauge, AddChar.coe_mk, MulEquiv.apply_symm_apply]

/-- The exponential of `F` is the gauge `u` exactly when `exp (i F(z)) = u(z)` for every `z`, for
the continuous representative of `F`. -/
theorem expGauge_eq_iff (hs : 1 < s) {F : realSubmodule ℂ (zero_le_one.trans hs.le)}
    {u : SobolevTopologicalGaugeGroup hs} :
    expGauge hs F = u ↔
      (fun z ↦ Circle.exp (continuousRep F z)) = (toSubgroup hs u : ℂ → Circle) := by
  rw [← (toSubgroup hs).injective.eq_iff, ← Subtype.coe_inj, toSubgroup_expGauge]

/-- **The exponential is injective**, since a continuous `H^s` phase is determined by its
exponential (`TauCeti.Vortex.injOn_exp`). -/
theorem expGauge_injective (hs : 1 < s) : Function.Injective (expGauge hs) := by
  intro F G hFG
  have hd := finrank_real_complex_lt_two_mul hs
  refine continuousRep_injective hd <| injOn_exp hs
    ⟨continuous_continuousRep hd F, continuousRep_mem_realSobolevFunctions hd F⟩
    ⟨continuous_continuousRep hd G, continuousRep_mem_realSobolevFunctions hd G⟩ ?_
  simpa only [toSubgroup_expGauge] using congrArg (fun u ↦ (toSubgroup hs u : ℂ → Circle)) hFG

/-- The `L²` function of `expGauge hs F - 1` is `exp (i F) - 1`. -/
theorem coeFn_toLp_inclusion_subOne_expGauge (hs : 1 < s) (h : 0 ≤ s)
    (F : realSubmodule ℂ (zero_le_one.trans hs.le)) :
    (inclusion h (subOne (expGauge hs F))).toLp =ᵐ[volume]
      fun z ↦ (Circle.exp (continuousRep F z) : ℂ) - 1 := by
  filter_upwards [coeFn_toLp_inclusion_subOne h (expGauge hs F)] with z hz
  rw [hz, toSubgroup_expGauge]

/-- **The exponential is locally Lipschitz in `H^s`.** For `s > 1` there is `C ≥ 0` such that
`‖exp (i F) - exp (i G)‖_{H^s} ≤ exp (C R) ‖F - G‖_{H^s}` for real phases with
`‖F‖_{H^s}, ‖G‖_{H^s} ≤ R`. -/
theorem exists_norm_subOne_expGauge_sub_le (hs : 1 < s) :
    ∃ C, 0 ≤ C ∧ ∀ {F G : realSubmodule ℂ (zero_le_one.trans hs.le)} {R : ℝ}, ‖F‖ ≤ R → ‖G‖ ≤ R →
      ‖subOne (expGauge hs F) - subOne (expGauge hs G)‖ ≤ Real.exp (C * R) * ‖F - G‖ := by
  obtain ⟨C, hC, hlip⟩ := exists_norm_toBesselPotentialSpace_sub_le_of_ae_eq_exp hs
  refine ⟨C, hC, fun {F G R} hFR hGR ↦ ?_⟩
  have h : 0 ≤ s := zero_le_one.trans hs.le
  have hd := finrank_real_complex_lt_two_mul hs
  have hae (F : realSubmodule ℂ h) :
      (inclusion h (F : H^{s}(ℂ))).toLp =ᵐ[volume] fun z ↦ (continuousRep F z : ℂ) := by
    rw [toLp_inclusion]
    exact coeFn_inclusionLp_ae_eq_continuousRep hd F
  have key := hlip (hae F) (hae G)
    (memSobolev_toLp_inclusion h _) (memSobolev_toLp_inclusion h _) (R := R)
    (by rwa [toBesselPotentialSpace_memSobolev_toLp_inclusion])
    (by rwa [toBesselPotentialSpace_memSobolev_toLp_inclusion])
    (coeFn_toLp_inclusion_subOne_expGauge hs h F) (coeFn_toLp_inclusion_subOne_expGauge hs h G)
    (memSobolev_toLp_inclusion h _) (memSobolev_toLp_inclusion h _)
  simp only [toBesselPotentialSpace_memSobolev_toLp_inclusion] at key
  exact key

/-- **The exponential is continuous** from the real phases to `G_s`. -/
@[fun_prop, continuity]
theorem continuous_expGauge (hs : 1 < s) : Continuous (expGauge hs) := by
  obtain ⟨C, -, hlip⟩ := exists_norm_subOne_expGauge_sub_le hs
  refine continuous_iff.2 (continuous_iff_continuousAt.2 fun F₀ ↦ ?_)
  refine continuousAt_of_locally_lipschitz zero_lt_one (Real.exp (C * (‖F₀‖ + 1))) fun F hF ↦ ?_
  rw [dist_eq_norm, dist_eq_norm]
  rw [dist_eq_norm] at hF
  refine hlip ?_ (by linarith [norm_nonneg F₀])
  linarith [norm_le_insert' F F₀]

/-- **Gauges near the identity are exponentials of small phases.** For `s > 1` there is `C ≥ 0`
such that every `u ∈ G_s` with `‖u - 1‖_{H^s} ≤ R` and `C R < 1` is `exp (i F)` for a real phase
with `‖F‖_{H^s} ≤ (1 - C R)⁻¹ ‖u - 1‖_{H^s}`. The phase is `arg u`. -/
theorem exists_expGauge_eq_and_norm_le (hs : 1 < s) :
    ∃ C, 0 ≤ C ∧ ∀ {u : SobolevTopologicalGaugeGroup hs} {R : ℝ}, ‖subOne u‖ ≤ R → C * R < 1 →
      ∃ F : realSubmodule ℂ (zero_le_one.trans hs.le),
        expGauge hs F = u ∧ ‖F‖ ≤ (1 - C * R)⁻¹ * ‖subOne u‖ := by
  obtain ⟨C, hC, harg⟩ := exists_memSobolev_ae_eq_arg_and_norm_sub_le hs
  refine ⟨C, hC, fun {u R} huR hCR ↦ ?_⟩
  have h : 0 ≤ s := zero_le_one.trans hs.le
  obtain ⟨A, A', hA, hA', hAs, hAs', hle⟩ := harg (coeFn_toLp_inclusion_subOne h u)
    (coeFn_toLp_inclusion_subOne h (1 : SobolevTopologicalGaugeGroup hs))
    (memSobolev_toLp_inclusion h _)
    (memSobolev_toLp_inclusion h _) (R := R)
    (by rwa [toBesselPotentialSpace_memSobolev_toLp_inclusion])
    (by rw [toBesselPotentialSpace_memSobolev_toLp_inclusion, subOne_one, norm_zero]
        exact (norm_nonneg _).trans huR) hCR
  simp only [toBesselPotentialSpace_memSobolev_toLp_inclusion, subOne_one, sub_zero] at hle
  -- The phase of the identity is zero.
  have hA'0 : hAs'.toBesselPotentialSpace = 0 := by
    have hA'z : A' = 0 := Lp.ext <| by
      filter_upwards [hA', Lp.coeFn_zero ℂ 2 (volume : Measure ℂ)] with z hz hz'
      rw [hz, hz']
      simp
    refine inclusionLp_injective h ?_
    rw [map_zero, inclusionLp_eq_iff, MemSobolev.toBesselPotentialSpace_toDistr, hA'z]
  rw [hA'0, sub_zero] at hle
  -- The phase of `u` is a real phase whose exponential is `u`.
  have hincl : inclusionLp h hAs.toBesselPotentialSpace = A := by
    rw [inclusionLp_eq_iff, MemSobolev.toBesselPotentialSpace_toDistr]
  have hmem : hAs.toBesselPotentialSpace ∈ realSubmodule ℂ h := by
    rw [mem_realSubmodule_iff, hincl]
    filter_upwards [hA] with z hz
    rw [hz, ofReal_im]
  refine ⟨⟨_, hmem⟩, ?_, hle⟩
  have hd := finrank_real_complex_lt_two_mul hs
  have hexp :
      Continuous fun z ↦ (Circle.exp (continuousRep (⟨_, hmem⟩ : realSubmodule ℂ h) z) : ℂ) :=
    continuous_subtypeVal.comp (Circle.exp.continuous.comp (continuous_continuousRep hd _))
  have heq := (Continuous.ae_eq_iff_eq volume hexp (continuous_coe_toSubgroup u)).1 <| by
    filter_upwards [coeFn_inclusionLp_ae_eq_continuousRep hd (⟨_, hmem⟩ : realSubmodule ℂ h), hA]
      with w hw hw'
    rw [hincl, hw'] at hw
    rw [← ofReal_injective hw, Circle.exp_arg]
  rw [expGauge_eq_iff]
  funext z
  exact Subtype.ext (congrFun heq z)

/-- Small gauges are exponentials of small phases. -/
private theorem exists_forall_norm_subOne_lt (hs : 1 < s) {ε : ℝ} (hε : 0 < ε) :
    ∃ η, 0 < η ∧ ∀ u : SobolevTopologicalGaugeGroup hs, ‖subOne u‖ < η →
      ∃ F : realSubmodule ℂ (zero_le_one.trans hs.le), ‖F‖ < ε ∧ expGauge hs F = u := by
  obtain ⟨C, hC, hex⟩ := exists_expGauge_eq_and_norm_le hs
  refine ⟨min (ε / 2) (2 * (C + 1))⁻¹, by positivity, fun u hu ↦ ?_⟩
  have hu₁ : ‖subOne u‖ < ε / 2 := hu.trans_le (min_le_left _ _)
  have hu₂ : ‖subOne u‖ < (2 * (C + 1))⁻¹ := hu.trans_le (min_le_right _ _)
  have hCR : C * ‖subOne u‖ ≤ 1 / 2 := by
    have h₁ : C * ‖subOne u‖ ≤ (C + 1) * (2 * (C + 1))⁻¹ :=
      mul_le_mul (by linarith) hu₂.le (norm_nonneg _) (by linarith)
    have h₂ : (C + 1) * (2 * (C + 1))⁻¹ = 1 / 2 := by field_simp
    linarith
  obtain ⟨F, hF, hFn⟩ := hex le_rfl (by linarith)
  refine ⟨F, ?_, hF⟩
  have h2 : (1 - C * ‖subOne u‖)⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ (by linarith) two_pos]
    linarith
  calc ‖F‖ ≤ (1 - C * ‖subOne u‖)⁻¹ * ‖subOne u‖ := hFn
    _ ≤ 2 * ‖subOne u‖ := mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
    _ < ε := by linarith

/-- **The exponential is an open map** from the real phases to `G_s`: a homomorphism that is
open at the identity, by `exists_forall_norm_subOne_lt`. -/
theorem isOpenMap_expGauge (hs : 1 < s) : IsOpenMap (expGauge hs) := by
  -- `expGauge hs` is the monoid homomorphism `(expGauge hs).toMonoidHom` on the multiplicative
  -- copy of the phases, precomposed with `ofAdd`.
  have hcomp : ⇑(expGauge hs) = (expGauge hs).toMonoidHom ∘ Multiplicative.ofAdd := by
    ext F
    rw [Function.comp_apply, AddChar.toMonoidHom_apply, toAdd_ofAdd]
  rw [hcomp]
  refine IsOpenMap.comp (IsTopologicalGroup.isOpenMap_iff_nhds_one.2 fun U hU ↦ ?_) isOpenMap_ofAdd
  rw [← ofAdd_zero, nhds_ofAdd, map_map, ← hcomp, mem_map] at hU
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hU
  obtain ⟨η, hη, hsmall⟩ := exists_forall_norm_subOne_lt hs hε
  have hnhds : {v : SobolevTopologicalGaugeGroup hs | ‖subOne v‖ < η} ∈ 𝓝 1 :=
    (isOpen_lt (continuous_norm.comp continuous_subOne) continuous_const).mem_nhds
      (by simpa using hη)
  refine mem_of_superset hnhds fun v hv ↦ ?_
  obtain ⟨F, hF, rfl⟩ := hsmall v hv
  exact hball (mem_ball_zero_iff.2 hF)

/-- **The exponential is an open embedding** of the real phases into `G_s`: an injective,
continuous and open homomorphism. Its image is the open subgroup of the gauges that have a global
real `H^s` phase. -/
theorem isOpenEmbedding_expGauge (hs : 1 < s) : IsOpenEmbedding (expGauge hs) :=
  .of_continuous_injective_isOpenMap (continuous_expGauge hs) (expGauge_injective hs)
    (isOpenMap_expGauge hs)

/-! ### The charts -/

variable {hs : 1 < s}

/-- `F ↦ u exp (i F)` is an open embedding of the real phases into `G_s`. -/
theorem isOpenEmbedding_mul_expGauge (u : SobolevTopologicalGaugeGroup hs) :
    IsOpenEmbedding fun F : realSubmodule ℂ (zero_le_one.trans hs.le) ↦ u * expGauge hs F :=
  (Homeomorph.mulLeft u).isOpenEmbedding.comp (isOpenEmbedding_expGauge hs)

/-- **The chart of `G_s` at `u`**: the inverse of `F ↦ u exp (i F)`, defined on the open coset
of `u` by the gauges with a global real `H^s` phase (`gaugeChart_source`). It sends `u` to `0`
(`gaugeChart_self`). -/
def gaugeChart (u : SobolevTopologicalGaugeGroup hs) :
    OpenPartialHomeomorph (SobolevTopologicalGaugeGroup hs)
      (realSubmodule ℂ (zero_le_one.trans hs.le)) :=
  ((isOpenEmbedding_mul_expGauge u).toOpenPartialHomeomorph _).symm

@[simp]
theorem gaugeChart_symm_apply (u : SobolevTopologicalGaugeGroup hs)
    (F : realSubmodule ℂ (zero_le_one.trans hs.le)) :
    (gaugeChart u).symm F = u * expGauge hs F := by
  simp [gaugeChart]

@[simp]
theorem gaugeChart_source (u : SobolevTopologicalGaugeGroup hs) :
    (gaugeChart u).source =
      range fun F : realSubmodule ℂ (zero_le_one.trans hs.le) ↦ u * expGauge hs F := by
  simp [gaugeChart]

@[simp]
theorem gaugeChart_target (u : SobolevTopologicalGaugeGroup hs) :
    (gaugeChart u).target = univ := by
  simp [gaugeChart]

/-- On its domain, the chart at `u` inverts `F ↦ u exp (i F)`. -/
theorem mul_expGauge_gaugeChart {u v : SobolevTopologicalGaugeGroup hs}
    (hv : v ∈ (gaugeChart u).source) : u * expGauge hs (gaugeChart u v) = v := by
  rw [← gaugeChart_symm_apply, OpenPartialHomeomorph.left_inv _ hv]

@[simp]
theorem gaugeChart_mul_expGauge (u : SobolevTopologicalGaugeGroup hs)
    (F : realSubmodule ℂ (zero_le_one.trans hs.le)) : gaugeChart u (u * expGauge hs F) = F := by
  rw [← gaugeChart_symm_apply, OpenPartialHomeomorph.right_inv _ (by simp)]

@[simp]
theorem gaugeChart_self (u : SobolevTopologicalGaugeGroup hs) : gaugeChart u u = 0 := by
  simpa using gaugeChart_mul_expGauge u 0

theorem mem_gaugeChart_source_self (u : SobolevTopologicalGaugeGroup hs) :
    u ∈ (gaugeChart u).source :=
  ⟨0, by simp⟩

/-- **The transition maps are translations.** On the common domain of the charts at `u` and `v`,
the transition map `F ↦ φ_v (u exp (i F))` is `F ↦ F + c` for a fixed phase `c`. -/
theorem gaugeChart_symm_trans_eqOn_add (u v : SobolevTopologicalGaugeGroup hs) :
    ∃ c : realSubmodule ℂ (zero_le_one.trans hs.le),
      EqOn ((gaugeChart u).symm ≫ₕ gaugeChart v) (· + c)
        ((gaugeChart u).symm ≫ₕ gaugeChart v).source := by
  rcases ((gaugeChart u).symm ≫ₕ gaugeChart v).source.eq_empty_or_nonempty with he | ⟨F₀, hF₀⟩
  · exact ⟨0, he ▸ eqOn_empty _ _⟩
  -- `v exp (i T(F)) = u exp (i F)` on the common domain, so `T(F) - F` is constant.
  have key {F} (hF : F ∈ ((gaugeChart u).symm ≫ₕ gaugeChart v).source) :
      v * expGauge hs (((gaugeChart u).symm ≫ₕ gaugeChart v) F) = u * expGauge hs F := by
    rw [OpenPartialHomeomorph.trans_source] at hF
    rw [OpenPartialHomeomorph.trans_apply, mul_expGauge_gaugeChart hF.2, gaugeChart_symm_apply]
  refine ⟨((gaugeChart u).symm ≫ₕ gaugeChart v) F₀ - F₀, fun F hF ↦ expGauge_injective hs ?_⟩
  have h₁ := key hF
  have h₀ := key hF₀
  dsimp only
  rw [add_comm, sub_eq_add_neg, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul,
    AddChar.map_neg_eq_inv]
  calc expGauge hs (((gaugeChart u).symm ≫ₕ gaugeChart v) F)
      = v⁻¹ * (u * expGauge hs F) := by rw [← h₁, inv_mul_cancel_left]
    _ = v⁻¹ * (u * expGauge hs F₀) * (expGauge hs F₀)⁻¹ * expGauge hs F := by group
    _ = _ := by rw [← h₀, inv_mul_cancel_left]

namespace SobolevTopologicalGaugeGroup

/-- **The charted space structure of `G_s`**, modelled on the real phases: the chart at `u` is
`gaugeChart u`, the inverse of `F ↦ u exp (i F)`. -/
instance instChartedSpace :
    ChartedSpace (realSubmodule ℂ (zero_le_one.trans hs.le)) (SobolevTopologicalGaugeGroup hs) where
  atlas := range gaugeChart
  chartAt := gaugeChart
  mem_chart_source := mem_gaugeChart_source_self
  chart_mem_atlas u := mem_range_self u

/-- The chart of `G_s` at `u` is `gaugeChart u`. -/
@[simp]
theorem chartAt_eq (u : SobolevTopologicalGaugeGroup hs) :
    chartAt (realSubmodule ℂ (zero_le_one.trans hs.le)) u = gaugeChart u :=
  rfl

/-- The charts of the atlas of `G_s` are the charts `gaugeChart u`. -/
theorem mem_atlas_iff
    {e : OpenPartialHomeomorph (SobolevTopologicalGaugeGroup hs)
      (realSubmodule ℂ (zero_le_one.trans hs.le))} :
    e ∈ atlas (realSubmodule ℂ (zero_le_one.trans hs.le)) (SobolevTopologicalGaugeGroup hs) ↔
      ∃ u, gaugeChart u = e :=
  Iff.rfl

/-- **`G_s` is a manifold of every smoothness class over `ℝ`**, including analytic: its transition
maps are translations of the model space (`gaugeChart_symm_trans_eqOn_add`). -/
instance instIsManifold (n : WithTop ℕ∞) :
    IsManifold 𝓘(ℝ, realSubmodule ℂ (zero_le_one.trans hs.le)) n
      (SobolevTopologicalGaugeGroup hs) := by
  refine isManifold_of_contDiffOn _ _ _ fun e e' he he' ↦ ?_
  obtain ⟨u, rfl⟩ := he
  obtain ⟨v, rfl⟩ := he'
  obtain ⟨c, hc⟩ := gaugeChart_symm_trans_eqOn_add u v
  simp only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, range_id, preimage_id,
    inter_univ, Function.id_comp, Function.comp_id]
  exact (contDiff_id.add contDiff_const).contDiffOn.congr hc

end SobolevTopologicalGaugeGroup

end TauCeti.Vortex
