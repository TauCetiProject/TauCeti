/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.FramedGauge.Exponential
public import TauCeti.Analysis.PDE.Vortex.FramedGauge.Topology
public import Mathlib.Geometry.Manifold.ChartedSpace

/-!
# The exponential charts of the Sobolev framed gauge group

For a real order `s > 1`, the Sobolev framed gauge group `G_s = {1 + h : h ∈ H^s, |1 + h| = 1}`
with its Sobolev topology (`TauCeti.Vortex.SobolevTopologicalGaugeGroup`) is a Hausdorff
topological group, and its elements near the identity are exponentials `exp (i f)` of continuous
real phases `f ∈ H^s(ℂ)` (`TauCeti.Vortex.exists_continuous_mem_realSobolevFunctions_eq_exp`).
This file assembles these facts into charts of `G_s` modelled on the real Banach space
`H^s(ℂ; ℝ)` of phases, the infinitesimal gauge transformations of the vortex field space.

**The model space.** The real phases form the closed real subspace
`TauCeti.Vortex.realPhaseSpace hs` of the Hilbert space `H^s(ℂ)`, consisting of the elements
whose `L²` function is real almost everywhere (`TauCeti.Vortex.mem_realPhaseSpace`,
`TauCeti.Vortex.isClosed_realPhaseSpace`); it is complete. By the Sobolev embedding each real
phase `F` has a unique continuous real representative, which depends linearly on `F`
(`TauCeti.Vortex.realPhaseSpace.phase`, `TauCeti.Vortex.realPhaseSpace.coeFn_toLp_inclusion`,
`TauCeti.Vortex.realPhaseSpace.phase_eq_of_ae_eq`), and every continuous real function in `H^s`
is the representative of a real phase (`TauCeti.Vortex.realPhaseSpace.exists_phase_eq`).

**The exponential.** The map `TauCeti.Vortex.expGauge hs : F ↦ exp (i F)` from real phases to
`G_s` is a group homomorphism from the additive group of real phases
(`TauCeti.Vortex.expGauge_add`, bundled as `TauCeti.Vortex.expGaugeHom`), and:

* it is injective (`TauCeti.Vortex.expGauge_injective`), since a continuous phase tending to zero
  at infinity is determined by its exponential;
* it is continuous (`TauCeti.Vortex.continuous_expGauge`), because it is locally Lipschitz from
  `H^s` phases to the coordinate `u - 1 ∈ H^s(ℂ)` of `G_s`
  (`TauCeti.Vortex.exists_norm_subOne_expGauge_sub_le`);
* it maps every neighbourhood of `0` onto a neighbourhood of the identity: an element `u` with
  `‖u - 1‖_{H^s}` small is `exp (i arg u)`, and the phase `arg u` lies in `H^s` with
  `‖arg u‖_{H^s} ≤ 2 ‖u - 1‖_{H^s}` (`TauCeti.Vortex.exists_expGauge_eq_and_norm_le`).

Since it is a homomorphism of topological groups, the last property makes it an open map
(`TauCeti.Vortex.isOpenMap_expGauge`). Hence the exponential is an open embedding
(`TauCeti.Vortex.isOpenEmbedding_expGauge`): a homeomorphism from the phases onto an open
subgroup of `G_s` (`TauCeti.Vortex.isOpen_range_expGauge`).

**The charts.** Composing the inverse of the exponential with the translation `v ↦ u⁻¹ v` gives
the chart `TauCeti.Vortex.gaugeChart hs u` at each `u ∈ G_s`, the open partial homeomorphism
`u exp (i F) ↦ F` defined on the open coset `u · exp (H^s(ℂ; ℝ))`. These charts make `G_s` a
charted space modelled on `H^s(ℂ; ℝ)` (the `ChartedSpace` instance). Since `G_s` is abelian and
the exponential is a homomorphism, the transition maps are translations of the model space: if
`v⁻¹ u = exp (i H)`, the chart at `v` sends the point with coordinate `F` in the chart at `u` to
`H + F` (`TauCeti.Vortex.gaugeChart_gaugeChart_symm`).

## Main definitions

* `TauCeti.Vortex.realPhaseSpace hs`: the real phases `H^s(ℂ; ℝ)`, a closed real subspace of
  `H^s(ℂ)`.
* `TauCeti.Vortex.realPhaseSpace.phase`: the continuous real representative of a real phase.
* `TauCeti.Vortex.expGauge hs`: the exponential `F ↦ exp (i F)` into `G_s` with its Sobolev
  topology, and `TauCeti.Vortex.expGaugeHom hs`, the same map as a group homomorphism.
* `TauCeti.Vortex.gaugeChart hs u`: the exponential chart of `G_s` at `u`.

## Main results

* `TauCeti.Vortex.isOpenEmbedding_expGauge`: the exponential is an open embedding of the real
  phases into `G_s`.
* `TauCeti.Vortex.exists_expGauge_eq_and_norm_le`: near the identity, every element `u` of `G_s`
  is the exponential of a phase of `H^s` norm at most `2 ‖u - 1‖_{H^s}`.
* `TauCeti.Vortex.gaugeChart_gaugeChart_symm`: the transition maps between the exponential charts
  are translations.

## References

* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III.
* C. H. Taubes, *Gr ⇒ SW: From pseudo-holomorphic curves to Seiberg–Witten solutions*,
  J. Differential Geom. 51 (1999), 203–334.
-/

public section

noncomputable section

namespace TauCeti.Vortex

open Complex Filter MeasureTheory Module Metric TemperedDistribution BesselPotentialSpace Topology
open scoped BesselPotentialSpace SchwartzMap ZeroAtInfty

variable {s : ℝ}

/-- The imaginary part of the inclusion `H^s(ℂ) ⊆ L²(ℂ)`, whose kernel is `realPhaseSpace`. -/
private def imInclusionCLM (hs : 0 ≤ s) : H^{s}(ℂ) →L[ℝ] Lp ℝ 2 (volume : Measure ℂ) :=
  (imCLM.compLpL 2 (volume : Measure ℂ)).comp
    ((inclusionLp hs : H^{s}(ℂ) →L[ℂ] _).restrictScalars ℝ)

/-- **The real phases `H^s(ℂ; ℝ)`**, `s ≥ 0`: the elements of `H^s(ℂ)` whose `L²` function is
real almost everywhere (`mem_realPhaseSpace`). It is the kernel of the imaginary part of the
inclusion `H^s(ℂ) ⊆ L²(ℂ)`, so it is a closed real subspace (`isClosed_realPhaseSpace`), and a
real Banach space. For `s > 1` it is the model space of the charts of the Sobolev framed gauge
group `G_s` (`gaugeChart`). -/
def realPhaseSpace (hs : 0 ≤ s) : Submodule ℝ H^{s}(ℂ) :=
  LinearMap.ker (imInclusionCLM hs : H^{s}(ℂ) →ₗ[ℝ] Lp ℝ 2 (volume : Measure ℂ))

/-- An element of `H^s(ℂ)` is a real phase exactly when its `L²` function is real almost
everywhere. -/
theorem mem_realPhaseSpace {hs : 0 ≤ s} {F : H^{s}(ℂ)} :
    F ∈ realPhaseSpace hs ↔
      ∀ᵐ z ∂volume, ((inclusion hs F).toLp z).im = 0 := by
  simp only [realPhaseSpace, imInclusionCLM, LinearMap.mem_ker, ContinuousLinearMap.coe_coe,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_restrictScalars', toLp_inclusion,
    Lp.eq_zero_iff_ae_eq_zero]
  have him := imCLM.coeFn_compLpL (p := 2) (μ := volume) (inclusionLp hs F)
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · filter_upwards [h, him] with z hz h₁
    rw [h₁] at hz
    simpa using hz
  · filter_upwards [h, him] with z hz h₁
    rw [h₁]
    simpa using hz

/-- The real phases form a closed subspace of `H^s(ℂ)`. -/
theorem isClosed_realPhaseSpace (hs : 0 ≤ s) : IsClosed (realPhaseSpace hs : Set H^{s}(ℂ)) :=
  ContinuousLinearMap.isClosed_ker (imInclusionCLM hs)

/-- An `L²` function in `H^s(ℂ)` that is almost everywhere real defines a real phase. -/
theorem toBesselPotentialSpace_mem_realPhaseSpace (hs : 0 ≤ s) {v : Lp ℂ 2 (volume : Measure ℂ)}
    (hv : MemSobolev s 2 (v : 𝓢'(ℂ, ℂ))) {f : ℂ → ℝ} (hvf : v =ᵐ[volume] fun z ↦ (f z : ℂ)) :
    hv.toBesselPotentialSpace ∈ realPhaseSpace hs := by
  refine mem_realPhaseSpace.2 ?_
  rw [toLp_inclusion_toBesselPotentialSpace hs hv rfl]
  filter_upwards [hvf] with z hz
  simp [hz]

instance instCompleteSpaceRealPhaseSpace (hs : 0 ≤ s) : CompleteSpace (realPhaseSpace hs) :=
  (isClosed_realPhaseSpace hs).completeSpace_coe

namespace realPhaseSpace

variable (hs : 1 < s)

/-- A continuous representative of a real phase, vanishing at infinity, by the Sobolev
embedding. -/
private def contRep (F : realPhaseSpace (zero_le_one.trans hs.le)) : C₀(ℂ, ℂ) :=
  (MemSobolev.exists_zeroAtInftyContinuousMap_ae_eq (finrank_real_complex_lt_two_mul hs)
    (memSobolev_toLp_inclusion (zero_le_one.trans hs.le) (F : H^{s}(ℂ)))).choose

private theorem coeFn_toLp_inclusion_ae_eq_contRep (F : realPhaseSpace (zero_le_one.trans hs.le)) :
    ⇑(inclusion (zero_le_one.trans hs.le) (F : H^{s}(ℂ))).toLp =ᵐ[volume] contRep hs F :=
  (MemSobolev.exists_zeroAtInftyContinuousMap_ae_eq (finrank_real_complex_lt_two_mul hs)
    (memSobolev_toLp_inclusion (zero_le_one.trans hs.le) (F : H^{s}(ℂ)))).choose_spec

/-- The continuous representative of a real phase is real everywhere. -/
private theorem im_contRep (F : realPhaseSpace (zero_le_one.trans hs.le)) (z : ℂ) :
    (contRep hs F z).im = 0 := by
  have hae : (fun z ↦ (contRep hs F z).im) =ᵐ[volume] fun _ ↦ (0 : ℝ) := by
    filter_upwards [coeFn_toLp_inclusion_ae_eq_contRep hs F, mem_realPhaseSpace.1 F.2]
      with z h₁ h₂
    rw [← h₁, h₂]
  exact congrFun ((continuous_im.comp (contRep hs F).continuous).ae_eq_iff_eq volume
    continuous_const |>.1 hae) z

/-- The continuous representative of a real phase is real: its complexification is the `L²`
function of the phase almost everywhere. -/
private theorem coeFn_toLp_inclusion_ae_eq_re_contRep
    (F : realPhaseSpace (zero_le_one.trans hs.le)) :
    ⇑(inclusion (zero_le_one.trans hs.le) (F : H^{s}(ℂ))).toLp =ᵐ[volume]
      fun z ↦ ((contRep hs F z).re : ℂ) := by
  filter_upwards [coeFn_toLp_inclusion_ae_eq_contRep hs F] with z hz
  rw [hz]
  exact Complex.ext (by simp) (by simp [im_contRep hs F z])

/-- A continuous real function whose complexification agrees almost everywhere with the `L²`
function of `F` is the real part of the continuous representative. -/
private theorem re_contRep_eq_of_ae_eq (F : realPhaseSpace (zero_le_one.trans hs.le)) {f : ℂ → ℝ}
    (hf : Continuous f)
    (h : ⇑(inclusion (zero_le_one.trans hs.le) (F : H^{s}(ℂ))).toLp =ᵐ[volume]
      fun z ↦ (f z : ℂ)) :
    (fun z ↦ (contRep hs F z).re) = f := by
  have hae : (fun z ↦ ((contRep hs F z).re : ℂ)) =ᵐ[volume] fun z ↦ (f z : ℂ) :=
    (coeFn_toLp_inclusion_ae_eq_re_contRep hs F).symm.trans h
  funext z
  exact ofReal_injective (congrFun
    ((continuous_ofReal.comp (continuous_re.comp (contRep hs F).continuous)).ae_eq_iff_eq
      volume (continuous_ofReal.comp hf) |>.1 hae) z)

/-- **The continuous real representative** of a real phase `F ∈ H^s(ℂ; ℝ)`, `s > 1`: the
continuous real function whose complexification is the `L²` function of `F` almost everywhere
(`realPhaseSpace.coeFn_toLp_inclusion`). It is unique (`realPhaseSpace.phase_eq_of_ae_eq`), and
it depends linearly on `F`. -/
def phase : realPhaseSpace (zero_le_one.trans hs.le) →ₗ[ℝ] ℂ → ℝ where
  toFun F z := (contRep hs F z).re
  map_add' F G := by
    refine re_contRep_eq_of_ae_eq hs _ ((continuous_re.comp (contRep hs F).continuous).add
      (continuous_re.comp (contRep hs G).continuous)) ?_
    filter_upwards [coeFn_toLp_inclusion_add (zero_le_one.trans hs.le) (F : H^{s}(ℂ))
        (G : H^{s}(ℂ)), coeFn_toLp_inclusion_ae_eq_re_contRep hs F,
      coeFn_toLp_inclusion_ae_eq_re_contRep hs G] with z h h₁ h₂
    simp only [Submodule.coe_add, h, Pi.add_apply, h₁, h₂, ofReal_add]
  map_smul' c F := by
    refine re_contRep_eq_of_ae_eq hs _
      ((continuous_re.comp (contRep hs F).continuous).const_smul c) ?_
    filter_upwards [coeFn_toLp_inclusion_smul (zero_le_one.trans hs.le) (c : ℂ) (F : H^{s}(ℂ)),
      coeFn_toLp_inclusion_ae_eq_re_contRep hs F] with z h h₁
    simp only [Submodule.coe_smul, ← Complex.coe_smul, h, Pi.smul_apply, h₁, RingHom.id_apply,
      smul_eq_mul, ofReal_mul]

theorem continuous_phase (F : realPhaseSpace (zero_le_one.trans hs.le)) : Continuous (phase hs F) :=
  continuous_re.comp (contRep hs F).continuous

/-- The `L²` function of a real phase is almost everywhere its continuous real representative. -/
theorem coeFn_toLp_inclusion (F : realPhaseSpace (zero_le_one.trans hs.le)) :
    ⇑(inclusion (zero_le_one.trans hs.le) (F : H^{s}(ℂ))).toLp =ᵐ[volume]
      fun z ↦ (phase hs F z : ℂ) :=
  coeFn_toLp_inclusion_ae_eq_re_contRep hs F

/-- The continuous real representative of a real phase lies in `realSobolevFunctions ℂ s 2`. -/
theorem phase_mem_realSobolevFunctions (F : realPhaseSpace (zero_le_one.trans hs.le)) :
    phase hs F ∈ realSobolevFunctions ℂ s 2 :=
  mem_realSobolevFunctions_of_ae_eq_ofReal
    (memSobolev_toLp_inclusion (zero_le_one.trans hs.le) (F : H^{s}(ℂ))) (coeFn_toLp_inclusion hs F)

/-- **Uniqueness of the continuous representative.** A continuous real function whose
complexification agrees almost everywhere with the `L²` function of the real phase `F` is the
continuous representative of `F`. -/
theorem phase_eq_of_ae_eq (F : realPhaseSpace (zero_le_one.trans hs.le)) {f : ℂ → ℝ}
    (hf : Continuous f)
    (h : ⇑(inclusion (zero_le_one.trans hs.le) (F : H^{s}(ℂ))).toLp =ᵐ[volume]
      fun z ↦ (f z : ℂ)) :
    phase hs F = f :=
  re_contRep_eq_of_ae_eq hs F hf h

/-- **Every continuous real `H^s` function is the continuous representative of a real phase.** -/
theorem exists_phase_eq {f : ℂ → ℝ} (hf : Continuous f) (hfs : f ∈ realSobolevFunctions ℂ s 2) :
    ∃ F : realPhaseSpace (zero_le_one.trans hs.le), phase hs F = f := by
  have h₀ := zero_le_one.trans hs.le
  obtain ⟨u, huf, hu⟩ := mem_realSobolevFunctions.1 hfs
  have hvf : ofRealCLM.compLp u =ᵐ[volume] fun z ↦ (f z : ℂ) := by
    filter_upwards [ofRealCLM.coeFn_compLp (p := 2) (μ := volume) u, huf] with z h₁ h₂
    rw [h₁, ofRealCLM_apply, h₂]
  refine ⟨⟨hu.toBesselPotentialSpace, toBesselPotentialSpace_mem_realPhaseSpace h₀ hu hvf⟩,
    phase_eq_of_ae_eq hs _ hf ?_⟩
  rw [toLp_inclusion_toBesselPotentialSpace h₀ hu rfl]
  exact hvf

/-- A real phase is determined by its continuous real representative. -/
theorem phase_injective : Function.Injective (phase hs) := by
  intro F G hFG
  refine Subtype.ext (toLp_inclusion_injective (zero_le_one.trans hs.le) (Lp.ext ?_))
  refine (coeFn_toLp_inclusion hs F).trans ?_
  rw [hFG]
  exact (coeFn_toLp_inclusion hs G).symm

end realPhaseSpace

open realPhaseSpace SobolevTopologicalGaugeGroup

variable (hs : 1 < s)

/-- **The exponential of real phases** `F ↦ exp (i F)`, from the real Hilbert space
`H^s(ℂ; ℝ)` to the Sobolev framed gauge group `G_s` with its Sobolev topology, `s > 1`. The
exponential is taken of the continuous real representative `realPhaseSpace.phase F`
(`expGauge_apply`). It is an open embedding (`isOpenEmbedding_expGauge`). -/
def expGauge (F : realPhaseSpace (zero_le_one.trans hs.le)) : SobolevTopologicalGaugeGroup hs :=
  (toSubgroup hs).symm ⟨fun z ↦ Circle.exp (phase hs F z),
    exp_mem_sobolevGaugeGroup hs (continuous_phase hs F) (phase_mem_realSobolevFunctions hs F)⟩

variable {hs}

@[simp]
theorem expGauge_apply (F : realPhaseSpace (zero_le_one.trans hs.le)) (z : ℂ) :
    (toSubgroup hs (expGauge hs F) : ℂ → Circle) z = Circle.exp (phase hs F z) := by
  simp [expGauge]

@[simp]
theorem expGauge_zero : expGauge hs 0 = 1 := by
  apply (toSubgroup hs).injective
  ext z
  simp [expGauge]

@[simp]
theorem expGauge_add (F G : realPhaseSpace (zero_le_one.trans hs.le)) :
    expGauge hs (F + G) = expGauge hs F * expGauge hs G := by
  apply (toSubgroup hs).injective
  ext z
  simp [expGauge, Circle.exp_add]

variable (hs) in
/-- The exponential `F ↦ exp (i F)` as a group homomorphism from the additive group of real
phases (`expGauge`). -/
def expGaugeHom : Multiplicative (realPhaseSpace (zero_le_one.trans hs.le)) →*
    SobolevTopologicalGaugeGroup hs where
  toFun F := expGauge hs F.toAdd
  map_one' := expGauge_zero
  map_mul' F G := expGauge_add F.toAdd G.toAdd

@[simp]
theorem expGaugeHom_apply (F : Multiplicative (realPhaseSpace (zero_le_one.trans hs.le))) :
    expGaugeHom hs F = expGauge hs F.toAdd :=
  (rfl)

@[simp]
theorem expGauge_neg (F : realPhaseSpace (zero_le_one.trans hs.le)) :
    expGauge hs (-F) = (expGauge hs F)⁻¹ :=
  map_inv (expGaugeHom hs) (Multiplicative.ofAdd F)

@[simp]
theorem expGauge_sub (F G : realPhaseSpace (zero_le_one.trans hs.le)) :
    expGauge hs (F - G) = expGauge hs F * (expGauge hs G)⁻¹ := by
  rw [sub_eq_add_neg, expGauge_add, expGauge_neg]

/-- **The exponential is injective** on real phases, since continuous phases tending to zero at
infinity are determined by their exponentials (`TauCeti.Vortex.injOn_exp`). -/
theorem expGauge_injective : Function.Injective (expGauge hs) := by
  intro F G hFG
  apply phase_injective hs
  refine injOn_exp hs ⟨continuous_phase hs F, phase_mem_realSobolevFunctions hs F⟩
    ⟨continuous_phase hs G, phase_mem_realSobolevFunctions hs G⟩ ?_
  funext z
  simpa using congrFun (congrArg (fun u ↦ (toSubgroup hs u : ℂ → Circle)) hFG) z

/-- **Local Lipschitz bound for the exponential.** There is `C ≥ 0` such that real phases `F, G`
of `H^s` norm at most `R` satisfy `‖exp (i F) - exp (i G)‖_{H^s} ≤ exp (C R) ‖F - G‖_{H^s}`. -/
theorem exists_norm_subOne_expGauge_sub_le :
    ∃ C, 0 ≤ C ∧ ∀ {F G : realPhaseSpace (zero_le_one.trans hs.le)} {R : ℝ}, ‖F‖ ≤ R → ‖G‖ ≤ R →
      ‖subOne (expGauge hs F) - subOne (expGauge hs G)‖ ≤ Real.exp (C * R) * ‖F - G‖ := by
  have h₀ := zero_le_one.trans hs.le
  obtain ⟨C, hC, hlip⟩ := exists_norm_toBesselPotentialSpace_sub_le_of_ae_eq_exp hs
  refine ⟨C, hC, fun {F G R} hF hG ↦ ?_⟩
  have key := hlip (coeFn_toLp_inclusion hs F) (coeFn_toLp_inclusion hs G)
    (memSobolev_toLp_inclusion h₀ (F : H^{s}(ℂ))) (memSobolev_toLp_inclusion h₀ (G : H^{s}(ℂ)))
    (R := R) (by rwa [toBesselPotentialSpace_memSobolev_toLp_inclusion, Submodule.norm_coe])
    (by rwa [toBesselPotentialSpace_memSobolev_toLp_inclusion, Submodule.norm_coe])
    (h := (inclusion h₀ (subOne (expGauge hs F))).toLp)
    (h' := (inclusion h₀ (subOne (expGauge hs G))).toLp)
    (by
      filter_upwards [coeFn_toLp_inclusion_subOne h₀ (expGauge hs F)] with z hz
      rw [hz, expGauge_apply])
    (by
      filter_upwards [coeFn_toLp_inclusion_subOne h₀ (expGauge hs G)] with z hz
      rw [hz, expGauge_apply])
    (memSobolev_toLp_inclusion h₀ _) (memSobolev_toLp_inclusion h₀ _)
  simpa only [toBesselPotentialSpace_memSobolev_toLp_inclusion, ← Submodule.coe_sub,
    Submodule.norm_coe] using key

/-- **The exponential is continuous** from the real phases to `G_s` with its Sobolev topology. -/
@[fun_prop, continuity]
theorem continuous_expGauge : Continuous (expGauge hs) := by
  obtain ⟨C, -, hlip⟩ := exists_norm_subOne_expGauge_sub_le (hs := hs)
  refine SobolevTopologicalGaugeGroup.continuous_iff.2 (continuous_iff_continuousAt.2 fun F ↦
    continuousAt_of_locally_lipschitz one_pos (Real.exp (C * (‖F‖ + 1))) fun G hG ↦ ?_)
  simpa only [dist_eq_norm] using hlip
    (by linarith [norm_le_norm_add_norm_sub' G F, dist_eq_norm G F])
    (le_add_of_nonneg_right zero_le_one)

/-- **The phase of a gauge near the identity.** There is `C ≥ 0` such that for every `u ∈ G_s`
with `C ‖u - 1‖_{H^s} < 1`, the phase `arg u` is almost everywhere an `L²` function in `H^s`, of
`H^s` norm at most `(1 - C ‖u - 1‖_{H^s})⁻¹ ‖u - 1‖_{H^s}`. This is the case `u' = 1` of
`TauCeti.Vortex.exists_memSobolev_ae_eq_arg_and_norm_sub_le`. -/
theorem exists_memSobolev_ae_eq_arg_and_norm_le :
    ∃ C, 0 ≤ C ∧ ∀ u : SobolevTopologicalGaugeGroup hs, C * ‖subOne u‖ < 1 →
      ∃ F : Lp ℂ 2 (volume : Measure ℂ),
        F =ᵐ[volume] (fun z ↦ (arg ((toSubgroup hs u : ℂ → Circle) z : ℂ) : ℂ)) ∧
        ∃ hF : MemSobolev s 2 (F : 𝓢'(ℂ, ℂ)),
          ‖hF.toBesselPotentialSpace‖ ≤ (1 - C * ‖subOne u‖)⁻¹ * ‖subOne u‖ := by
  have h₀ := zero_le_one.trans hs.le
  obtain ⟨C, hC, harg⟩ := exists_memSobolev_ae_eq_arg_and_norm_sub_le hs
  refine ⟨C, hC, fun u hu ↦ ?_⟩
  obtain ⟨F, F', hFu, hF'1, hF, hF', hbound⟩ := harg
    (coeFn_toLp_inclusion_subOne h₀ u)
    (coeFn_toLp_inclusion_subOne h₀ (1 : SobolevTopologicalGaugeGroup hs))
    (memSobolev_toLp_inclusion h₀ (subOne u)) (memSobolev_toLp_inclusion h₀ (subOne 1))
    (R := ‖subOne u‖) (by rw [toBesselPotentialSpace_memSobolev_toLp_inclusion])
    (by rw [toBesselPotentialSpace_memSobolev_toLp_inclusion, subOne_one, norm_zero]
        exact norm_nonneg _) hu
  -- The phase of the identity gauge is zero.
  have hF'0 : hF'.toBesselPotentialSpace = 0 := by
    have : F' = 0 := by
      refine Lp.ext (hF'1.trans ?_)
      filter_upwards with z
      simp
    subst this
    exact BesselPotentialSpace.ext (by simp [← Lp.toTemperedDistributionCLM_apply])
  rw [hF'0, sub_zero, toBesselPotentialSpace_memSobolev_toLp_inclusion,
    toBesselPotentialSpace_memSobolev_toLp_inclusion, subOne_one, sub_zero] at hbound
  exact ⟨F, hFu, hF, hbound⟩

/-- **Every element of `G_s` near the identity is an exponential, with a norm bound.** There is
`δ > 0` such that every `u ∈ G_s` with `‖u - 1‖_{H^s} < δ` is `exp (i F)` for a real phase `F`
with `‖F‖_{H^s} ≤ 2 ‖u - 1‖_{H^s}`; the phase is `arg u` almost everywhere. -/
theorem exists_expGauge_eq_and_norm_le :
    ∃ δ, 0 < δ ∧ ∀ u : SobolevTopologicalGaugeGroup hs, ‖subOne u‖ < δ →
      ∃ F : realPhaseSpace (zero_le_one.trans hs.le), expGauge hs F = u ∧ ‖F‖ ≤ 2 * ‖subOne u‖ := by
  have h₀ := zero_le_one.trans hs.le
  obtain ⟨C, hC, harg⟩ := exists_memSobolev_ae_eq_arg_and_norm_le (hs := hs)
  refine ⟨(2 * C + 1)⁻¹, by positivity, fun u hu ↦ ?_⟩
  set R := ‖subOne u‖
  have hR : 0 ≤ R := norm_nonneg _
  have hδ : (2 * C + 1) * R < 1 := by
    have := mul_lt_mul_of_pos_left hu (by positivity : (0 : ℝ) < 2 * C + 1)
    rwa [mul_inv_cancel₀ (by positivity)] at this
  -- The phase `arg u` is a real phase with norm at most `2 ‖u - 1‖`.
  obtain ⟨F, hFu, hF, hbound⟩ := harg u (by nlinarith)
  set Φ : realPhaseSpace h₀ :=
    ⟨hF.toBesselPotentialSpace, toBesselPotentialSpace_mem_realPhaseSpace h₀ hF hFu⟩
  refine ⟨Φ, ?_, ?_⟩
  · -- `exp (i Φ)` and `u` are continuous and agree almost everywhere, where `Φ = arg u`.
    have hΦ := coeFn_toLp_inclusion hs Φ
    rw [toLp_inclusion_toBesselPotentialSpace h₀ hF rfl] at hΦ
    have hae : (fun z ↦ (Circle.exp (phase hs Φ z) : ℂ)) =ᵐ[volume]
        fun z ↦ ((toSubgroup hs u : ℂ → Circle) z : ℂ) := by
      filter_upwards [hΦ, hFu] with z h₁ h₂
      rw [ofReal_injective (h₁.symm.trans h₂), Circle.exp_arg]
    have heq := (continuous_subtype_val.comp (Circle.exp.continuous.comp
      (continuous_phase hs Φ))).ae_eq_iff_eq volume (continuous_coe_toSubgroup u) |>.1 hae
    refine (toSubgroup hs).injective (Subtype.ext (funext fun z ↦ Subtype.ext ?_))
    rw [expGauge_apply]
    exact congrFun heq z
  · calc ‖Φ‖ = ‖hF.toBesselPotentialSpace‖ := (Submodule.norm_coe Φ).symm
      _ ≤ (1 - C * R)⁻¹ * R := hbound
      _ ≤ 2 * R := by
          gcongr
          rw [inv_le_comm₀ (by nlinarith) two_pos]
          nlinarith

/-- **The exponential maps neighbourhoods of `0` onto neighbourhoods of the identity.** -/
theorem nhds_one_le_map_expGauge :
    𝓝 (1 : SobolevTopologicalGaugeGroup hs) ≤
      (𝓝 (0 : realPhaseSpace (zero_le_one.trans hs.le))).map (expGauge hs) := by
  obtain ⟨δ, hδ, hexp⟩ := exists_expGauge_eq_and_norm_le (hs := hs)
  refine (nhds_basis_ball.map _).ge_iff.2 fun ε hε ↦ ?_
  have hU : {u : SobolevTopologicalGaugeGroup hs | ‖subOne u‖ < min δ (ε / 2)} ∈ 𝓝 1 :=
    (isOpen_lt (continuous_norm.comp continuous_subOne) continuous_const).mem_nhds
      (by simp [hδ, hε])
  filter_upwards [hU] with u hu
  obtain ⟨F, rfl, hF⟩ := hexp u (hu.trans_le (min_le_left _ _))
  refine ⟨F, mem_ball_zero_iff.2 (hF.trans_lt ?_), rfl⟩
  linarith [hu.trans_le (min_le_right _ _)]

/-- **The exponential is an open map** from the real phases to `G_s`: it is a homomorphism of
topological groups which maps neighbourhoods of `0` onto neighbourhoods of the identity. -/
theorem isOpenMap_expGauge : IsOpenMap (expGauge hs) :=
  (IsTopologicalGroup.isOpenMap_iff_nhds_one (f := expGaugeHom hs)).2 nhds_one_le_map_expGauge

/-- **The exponential is an open embedding.** For `s > 1`, the exponential `F ↦ exp (i F)` is an
open embedding of the real phases `H^s(ℂ; ℝ)` into the Sobolev framed gauge group `G_s` with its
Sobolev topology. -/
theorem isOpenEmbedding_expGauge : IsOpenEmbedding (expGauge hs) :=
  .of_continuous_injective_isOpenMap continuous_expGauge expGauge_injective isOpenMap_expGauge

/-- The exponentials of real phases form an open subgroup of `G_s`; it contains a neighbourhood of
the identity. -/
theorem isOpen_range_expGauge : IsOpen (Set.range (expGauge hs)) :=
  isOpenEmbedding_expGauge.isOpen_range

/-! ### Charts -/

variable (hs) in
/-- **The exponential chart of `G_s` at `u`**: the open partial homeomorphism sending
`u exp (i F)` to the real phase `F`. Its source is the open coset `u · exp (H^s(ℂ; ℝ))`
(`source_gaugeChart`) and its inverse is `F ↦ u exp (i F)` (`gaugeChart_symm_apply`). -/
def gaugeChart (u : SobolevTopologicalGaugeGroup hs) :
    OpenPartialHomeomorph (SobolevTopologicalGaugeGroup hs)
      (realPhaseSpace (zero_le_one.trans hs.le)) :=
  (Homeomorph.mulLeft u⁻¹).toOpenPartialHomeomorph.trans
    (isOpenEmbedding_expGauge.toOpenPartialHomeomorph (expGauge hs)).symm

theorem source_gaugeChart (u : SobolevTopologicalGaugeGroup hs) :
    (gaugeChart hs u).source = {v | u⁻¹ * v ∈ Set.range (expGauge hs)} := by
  ext v
  simp [gaugeChart]

@[simp]
theorem target_gaugeChart (u : SobolevTopologicalGaugeGroup hs) :
    (gaugeChart hs u).target = Set.univ := by
  simp [gaugeChart]

/-- On its source, the chart at `u` sends `v` to the phase of `u⁻¹ v`. -/
theorem expGauge_gaugeChart {u v : SobolevTopologicalGaugeGroup hs}
    (hv : v ∈ (gaugeChart hs u).source) : expGauge hs (gaugeChart hs u v) = u⁻¹ * v := by
  rw [source_gaugeChart] at hv
  simpa [gaugeChart] using isOpenEmbedding_expGauge.toOpenPartialHomeomorph_right_inv _ hv

@[simp]
theorem gaugeChart_symm_apply (u : SobolevTopologicalGaugeGroup hs)
    (F : realPhaseSpace (zero_le_one.trans hs.le)) :
    (gaugeChart hs u).symm F = u * expGauge hs F := by
  simp [gaugeChart, Homeomorph.mulLeft_symm]

@[simp]
theorem gaugeChart_mul_expGauge (u : SobolevTopologicalGaugeGroup hs)
    (F : realPhaseSpace (zero_le_one.trans hs.le)) :
    gaugeChart hs u (u * expGauge hs F) = F := by
  simp [gaugeChart, IsOpenEmbedding.toOpenPartialHomeomorph_left_inv]

/-- **The transition maps between exponential charts are translations.** If
`v⁻¹ u = exp (i H)`, then the chart at `v` sends the point with coordinate `F` in the chart at
`u` to `H + F`. -/
theorem gaugeChart_gaugeChart_symm {u v : SobolevTopologicalGaugeGroup hs}
    {H : realPhaseSpace (zero_le_one.trans hs.le)}
    (h : v⁻¹ * u = expGauge hs H) (F : realPhaseSpace (zero_le_one.trans hs.le)) :
    gaugeChart hs v ((gaugeChart hs u).symm F) = H + F := by
  rw [gaugeChart_symm_apply, ← mul_inv_cancel_left v u, mul_assoc, h, ← expGauge_add,
    gaugeChart_mul_expGauge]

/-- **`G_s` is a charted space** modelled on the real Hilbert space `H^s(ℂ; ℝ)` of phases, with
the exponential charts `gaugeChart hs u` at the points `u ∈ G_s`. -/
instance : ChartedSpace (realPhaseSpace (zero_le_one.trans hs.le))
    (SobolevTopologicalGaugeGroup hs) where
  atlas := Set.range (gaugeChart hs)
  chartAt := gaugeChart hs
  mem_chart_source u := by
    rw [source_gaugeChart, Set.mem_ofPred_eq, inv_mul_cancel]
    exact ⟨0, expGauge_zero⟩
  chart_mem_atlas u := ⟨u, rfl⟩

@[simp]
theorem chartAt_eq_gaugeChart (u : SobolevTopologicalGaugeGroup hs) :
    chartAt (realPhaseSpace (zero_le_one.trans hs.le)) u = gaugeChart hs u :=
  (rfl)

end TauCeti.Vortex
