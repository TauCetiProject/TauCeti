/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.Sobolev
public import TauCeti.Analysis.Sobolev.BesselPotential.Inclusion
import TauCeti.Analysis.Sobolev.BesselPotential.Conj
import TauCeti.Analysis.Sobolev.BesselPotential.Embedding

/-!
# The real elements of the Bessel-potential space `H^s`

For an order `s ≥ 0`, the elements of the complex Bessel-potential space `H^s(E) = H^{s,2}(E, ℂ)`
are `L²` functions. This file studies those whose `L²` function is real almost everywhere. They
form a closed real subspace `BesselPotentialSpace.realSubmodule E h` of `H^s(E)`
(`BesselPotentialSpace.mem_realSubmodule_iff`, `BesselPotentialSpace.isClosed_realSubmodule`),
which with the norm of `H^s(E)` is a real Hilbert space. Unlike
`TemperedDistribution.realSobolevSubmodule E s 2`, a subspace of `Lp ℝ 2` with the `L²` norm, it
carries the `H^s` norm, so it is a model space for spaces of real `H^s` functions, for instance
the phases of Sobolev gauges.

Above the Sobolev threshold `s > dim E / 2`, every element `F` of this subspace has a unique
continuous real representative `BesselPotentialSpace.continuousRep F`
(`BesselPotentialSpace.coeFn_inclusionLp_ae_eq_continuousRep`,
`BesselPotentialSpace.continuousRep_eq_of_ae_eq`), by the Sobolev embedding into continuous
functions. It lies in the real `H^s` functions `TemperedDistribution.realSobolevFunctions E s 2`
and is `ℝ`-linear in `F` (`BesselPotentialSpace.continuousRep` is a linear map), and it
determines `F` (`BesselPotentialSpace.continuousRep_injective`). Convergence in `H^s` makes the
continuous representatives converge uniformly
(`BesselPotentialSpace.tendstoUniformly_continuousRep`). Above `s > n + dim E / 2` the continuous
representative is a `Cⁿ` function (`BesselPotentialSpace.contDiff_continuousRep`).

Complex conjugation of the `L²` function is a real-linear isometric involution
`BesselPotentialSpace.conjCLM` of `H^s(E)` (`BesselPotentialSpace.norm_conjCLM`,
`BesselPotentialSpace.conjCLM_conjCLM`), conjugate-linear over `ℂ`
(`BesselPotentialSpace.conjCLM_smul`), by `TemperedDistribution.MemSobolev.of_ae_eq_conj`; the
real elements are its fixed points (`BesselPotentialSpace.mem_realSubmodule_iff_conjCLM_eq`). The
real part `(F + conj F) / 2` is therefore a bounded real-linear projection
`BesselPotentialSpace.realPartCLM` of `H^s(E)` onto the real subspace
(`BesselPotentialSpace.realPartCLM_coe`). Composing with it turns a smooth map into `H^s(E)` that
takes real values into a smooth map into the real subspace, with the same order of smoothness,
analytic included.
-/

public section

noncomputable section

open MeasureTheory Module TemperedDistribution ComplexConjugate
open scoped SchwartzMap BesselPotentialSpace Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

namespace BesselPotentialSpace

variable {s : ℝ}

variable (E) in
/-- **The real elements of `H^s(E)`**, `0 ≤ s`: the closed real subspace of the elements whose
`L²` function is real almost everywhere (`mem_realSubmodule_iff`). It is the kernel of the
imaginary part of the inclusion into `L²`. -/
def realSubmodule (h : 0 ≤ s) : Submodule ℝ H^{s}(E) :=
  LinearMap.ker (((Complex.imCLM.compLpL 2 (volume : Measure E)).comp
    ((inclusionLp h).restrictScalars ℝ) : H^{s}(E) →L[ℝ] Lp ℝ 2 (volume : Measure E)) :
      H^{s}(E) →ₗ[ℝ] Lp ℝ 2 (volume : Measure E))

/-- An element of `H^s(E)` is real exactly when its `L²` function is real almost everywhere. -/
theorem mem_realSubmodule_iff (h : 0 ≤ s) {F : H^{s}(E)} :
    F ∈ realSubmodule E h ↔ ∀ᵐ z ∂volume, (inclusionLp h F z).im = 0 := by
  rw [realSubmodule, LinearMap.mem_ker]
  simp only [ContinuousLinearMap.coe_coe, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_restrictScalars', Lp.eq_zero_iff_ae_eq_zero]
  have hc := Complex.imCLM.coeFn_compLpL (p := 2) (μ := volume) (inclusionLp h F)
  constructor
  · intro h0
    filter_upwards [h0, hc] with z h₁ h₂
    rw [← Complex.imCLM_apply, ← h₂, h₁, Pi.zero_apply]
  · intro h0
    filter_upwards [h0, hc] with z h₁ h₂
    rw [h₂, Pi.zero_apply, Complex.imCLM_apply, h₁]

/-- The real elements form a closed subspace of `H^s(E)`. -/
theorem isClosed_realSubmodule (h : 0 ≤ s) : IsClosed (realSubmodule E h : Set H^{s}(E)) :=
  ContinuousLinearMap.isClosed_ker _

instance (h : 0 ≤ s) : CompleteSpace (realSubmodule E h) :=
  (isClosed_realSubmodule h).completeSpace_coe

/-- **The continuous representative of a real element.** Above the Sobolev threshold
`s > dim E / 2`, the `L²` function of a real element `F ∈ H^s(E)` agrees almost everywhere with a
continuous real function. -/
theorem exists_continuous_ae_eq_of_mem_realSubmodule (hs : finrank ℝ E < 2 * s) {h : 0 ≤ s}
    (F : realSubmodule E h) :
    ∃ f : E → ℝ, Continuous f ∧ inclusionLp h (F : H^{s}(E)) =ᵐ[volume] fun z ↦ (f z : ℂ) := by
  obtain ⟨g, hg⟩ :=
    (memSobolev_toLp_inclusion h (F : H^{s}(E))).exists_zeroAtInftyContinuousMap_ae_eq hs
  rw [toLp_inclusion] at hg
  -- The imaginary part of the continuous representative vanishes almost everywhere, hence
  -- everywhere.
  have him : (fun z ↦ (g z).im) = fun _ ↦ (0 : ℝ) := by
    refine (Continuous.ae_eq_iff_eq volume (by fun_prop) continuous_const).1 ?_
    filter_upwards [(mem_realSubmodule_iff h).1 F.property, hg] with z hz hz'
    rw [← hz', hz]
  refine ⟨fun z ↦ (g z).re, by fun_prop, ?_⟩
  filter_upwards [hg] with z hz
  rw [hz]
  exact Complex.ext rfl (by simpa using congrFun him z)

/-- Two continuous real representatives of the same element of `H^s(E)` agree. -/
private theorem eq_of_ae_eq_of_ae_eq {h : 0 ≤ s} {F : H^{s}(E)} {f g : E → ℝ}
    (hf : Continuous f) (hg : Continuous g)
    (hFf : inclusionLp h F =ᵐ[volume] fun z ↦ (f z : ℂ))
    (hFg : inclusionLp h F =ᵐ[volume] fun z ↦ (g z : ℂ)) : f = g := by
  refine (Continuous.ae_eq_iff_eq volume hf hg).1 ?_
  filter_upwards [hFf.symm.trans hFg] with z hz
  exact_mod_cast hz

variable {h : 0 ≤ s}

open Classical in
/-- **The continuous representative of a real element** `F ∈ H^s(E)`, as an `ℝ`-linear map:
above the Sobolev threshold `s > dim E / 2`, the continuous real function whose values agree
almost everywhere with the `L²` function of `F` (`coeFn_inclusionLp_ae_eq_continuousRep`). It is
unique (`continuousRep_eq_of_ae_eq`). Below the threshold, where `F` need not have a continuous
representative, it is the junk value `0`. -/
def continuousRep : realSubmodule E h →ₗ[ℝ] (E → ℝ) :=
  if hs : finrank ℝ E < 2 * s then
    { toFun F := (exists_continuous_ae_eq_of_mem_realSubmodule hs F).choose
      map_add' F G := by
        have hF := (exists_continuous_ae_eq_of_mem_realSubmodule hs F).choose_spec
        have hG := (exists_continuous_ae_eq_of_mem_realSubmodule hs G).choose_spec
        have hFG := (exists_continuous_ae_eq_of_mem_realSubmodule hs (F + G)).choose_spec
        refine eq_of_ae_eq_of_ae_eq hFG.1 (hF.1.add hG.1) hFG.2 ?_
        rw [Submodule.coe_add, map_add]
        filter_upwards [Lp.coeFn_add (inclusionLp h (F : H^{s}(E))) (inclusionLp h (G : H^{s}(E))),
          hF.2, hG.2] with z hz hFz hGz
        rw [hz, Pi.add_apply, hFz, hGz, Pi.add_apply, Complex.ofReal_add]
      map_smul' c F := by
        have hF := (exists_continuous_ae_eq_of_mem_realSubmodule hs F).choose_spec
        have hcF := (exists_continuous_ae_eq_of_mem_realSubmodule hs (c • F)).choose_spec
        refine eq_of_ae_eq_of_ae_eq hcF.1 (hF.1.const_smul c) hcF.2 ?_
        rw [Submodule.coe_smul, ← Complex.coe_smul, map_smul]
        filter_upwards [Lp.coeFn_smul (c : ℂ) (inclusionLp h (F : H^{s}(E))), hF.2] with z hz hFz
        rw [hz, Pi.smul_apply, hFz, RingHom.id_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul,
          Complex.ofReal_mul] }
  else 0

private theorem continuousRep_spec (hs : finrank ℝ E < 2 * s) (F : realSubmodule E h) :
    Continuous (continuousRep F) ∧
      inclusionLp h (F : H^{s}(E)) =ᵐ[volume] fun z ↦ (continuousRep F z : ℂ) := by
  simp only [continuousRep, hs, ↓reduceDIte, LinearMap.coe_mk, AddHom.coe_mk]
  exact (exists_continuous_ae_eq_of_mem_realSubmodule hs F).choose_spec

theorem continuous_continuousRep (hs : finrank ℝ E < 2 * s) (F : realSubmodule E h) :
    Continuous (continuousRep F) :=
  (continuousRep_spec hs F).1

theorem coeFn_inclusionLp_ae_eq_continuousRep (hs : finrank ℝ E < 2 * s) (F : realSubmodule E h) :
    inclusionLp h (F : H^{s}(E)) =ᵐ[volume] fun z ↦ (continuousRep F z : ℂ) :=
  (continuousRep_spec hs F).2

/-- The continuous representative is the only continuous function representing `F`. -/
theorem continuousRep_eq_of_ae_eq (hs : finrank ℝ E < 2 * s) {F : realSubmodule E h}
    {f : E → ℝ} (hf : Continuous f)
    (hF : inclusionLp h (F : H^{s}(E)) =ᵐ[volume] fun z ↦ (f z : ℂ)) :
    continuousRep F = f :=
  eq_of_ae_eq_of_ae_eq (continuous_continuousRep hs F) hf
    (coeFn_inclusionLp_ae_eq_continuousRep hs F) hF

/-- Above the Sobolev threshold, a real element of `H^s(E)` is determined by its continuous
representative. -/
theorem continuousRep_injective (hs : finrank ℝ E < 2 * s) :
    Function.Injective (continuousRep : realSubmodule E h → E → ℝ) := by
  intro F G hFG
  refine Subtype.ext (ext_of_ae_eq_inclusionLp h ?_)
  filter_upwards [coeFn_inclusionLp_ae_eq_continuousRep hs F,
    coeFn_inclusionLp_ae_eq_continuousRep hs G] with z hF hG
  rw [hF, hG, hFG]

/-- The continuous representative lies in the real `H^s` functions. -/
theorem continuousRep_mem_realSobolevFunctions (hs : finrank ℝ E < 2 * s)
    (F : realSubmodule E h) : continuousRep F ∈ realSobolevFunctions E s 2 :=
  mem_realSobolevFunctions_of_ae_eq_ofReal (memSobolev_toLp_inclusion h (F : H^{s}(E)))
    (by simpa using coeFn_inclusionLp_ae_eq_continuousRep hs F)

/-- **Continuous representatives converge uniformly.** Above the Sobolev threshold
`s > dim E / 2`, if real elements `F` of `H^s(E)` tend to `F₀` in `H^s`, their continuous
representatives tend uniformly to that of `F₀`. -/
theorem tendstoUniformly_continuousRep (hs : finrank ℝ E < 2 * s) (F₀ : realSubmodule E h) :
    TendstoUniformly (fun F : realSubmodule E h ↦ continuousRep F) (continuousRep F₀) (𝓝 F₀) := by
  have hae (F : realSubmodule E h) :
      (inclusion h (F : H^{s}(E))).toLp =ᵐ[volume] fun z ↦ (continuousRep F z : ℂ) := by
    rw [toLp_inclusion]
    exact coeFn_inclusionLp_ae_eq_continuousRep hs F
  have hT := tendstoUniformly_of_tendsto_toBesselPotentialSpace hs
    (fun F : realSubmodule E h ↦ memSobolev_toLp_inclusion h (F : H^{s}(E)))
    (memSobolev_toLp_inclusion h (F₀ : H^{s}(E))) (l := 𝓝 F₀)
    (by simpa only [toBesselPotentialSpace_memSobolev_toLp_inclusion] using
      continuous_subtypeVal.tendsto F₀)
    (fun F ↦ Complex.continuous_ofReal.comp (continuous_continuousRep hs F))
    (Complex.continuous_ofReal.comp (continuous_continuousRep hs F₀)) hae (hae F₀)
  rw [Metric.tendstoUniformly_iff] at hT ⊢
  simpa only [Function.comp_apply, Complex.dist_eq, ← Complex.ofReal_sub, Complex.norm_real,
    Real.dist_eq, Real.norm_eq_abs] using hT

/-- Above the threshold `s > n + dim E / 2`, the continuous representative of a real element of
`H^s(E)` is a `Cⁿ` function. -/
theorem contDiff_continuousRep {n : ℕ} (hs : finrank ℝ E + 2 * n < 2 * s)
    (F : realSubmodule E h) : ContDiff ℝ n (continuousRep F) := by
  have hs' : (finrank ℝ E : ℝ) < 2 * s := by
    linarith [show (0 : ℝ) ≤ 2 * n by positivity]
  exact contDiff_of_mem_realSobolevFunctions hs (continuousRep_mem_realSobolevFunctions hs' F)
    (continuous_continuousRep hs' F)

/-! ### Complex conjugation and the real part -/

/-- The element of `H^s(E)` whose `L²` function is the conjugate of that of `F`. -/
private def conjAux (h : 0 ≤ s) (F : H^{s}(E)) : H^{s}(E) :=
  (MemSobolev.of_ae_eq_conj (memSobolev_toLp_inclusion h F) (u' := star (inclusion h F).toLp)
    (Lp.coeFn_star _)).toBesselPotentialSpace

private theorem coeFn_inclusionLp_conjAux (F : H^{s}(E)) :
    inclusionLp h (conjAux h F) =ᵐ[volume] fun z ↦ conj (inclusionLp h F z) := by
  rw [conjAux, ← toLp_inclusion, toLp_inclusion_toBesselPotentialSpace h _ rfl, toLp_inclusion]
  exact Lp.coeFn_star _

private theorem conjAux_smul (c : ℂ) (F : H^{s}(E)) :
    conjAux h (c • F) = conj c • conjAux h F :=
  ext_of_ae_eq_inclusionLp h <| by
    filter_upwards [coeFn_inclusionLp_conjAux (h := h) (c • F),
      coeFn_inclusionLp_conjAux (h := h) F, Lp.coeFn_smul c (inclusionLp h F),
      Lp.coeFn_smul (conj c) (inclusionLp h (conjAux h F))] with z h₁ h₂ h₃ h₄
    simp only [(inclusionLp h).map_smul, h₁, h₂, h₃, h₄, Pi.smul_apply, smul_eq_mul, map_mul]

private theorem norm_conjAux (F : H^{s}(E)) : ‖conjAux h F‖ = ‖F‖ :=
  (MemSobolev.norm_toBesselPotentialSpace_of_ae_eq_conj (memSobolev_toLp_inclusion h F)
    (Lp.coeFn_star _) _).trans
    (congrArg norm (toBesselPotentialSpace_memSobolev_toLp_inclusion h F))

variable (E h) in
/-- **Complex conjugation on `H^s(E)`**, `0 ≤ s`: the element whose `L²` function is the complex
conjugate of the `L²` function of `F` (`coeFn_inclusionLp_conjCLM`). It is a real-linear isometry
(`norm_conjCLM`). -/
def conjCLM : H^{s}(E) →L[ℝ] H^{s}(E) :=
  LinearMap.mkContinuous
    { toFun := conjAux h
      map_add' F G := ext_of_ae_eq_inclusionLp h <| by
        filter_upwards [coeFn_inclusionLp_conjAux (h := h) (F + G),
          coeFn_inclusionLp_conjAux (h := h) F, coeFn_inclusionLp_conjAux (h := h) G,
          Lp.coeFn_add (inclusionLp h (conjAux h F)) (inclusionLp h (conjAux h G)),
          Lp.coeFn_add (inclusionLp h F) (inclusionLp h G)] with z h₁ h₂ h₃ h₄ h₅
        simp only [map_add, h₁, h₂, h₃, h₄, h₅, Pi.add_apply]
      map_smul' c F := by
        rw [RingHom.id_apply, ← Complex.coe_smul, ← Complex.coe_smul, conjAux_smul,
          Complex.conj_ofReal] }
    1 fun F ↦ (norm_conjAux F).le.trans (one_mul _).symm.le

/-- The `L²` function of `conjCLM E h F` is the complex conjugate of the `L²` function of `F`. -/
theorem coeFn_inclusionLp_conjCLM (F : H^{s}(E)) :
    inclusionLp h (conjCLM E h F) =ᵐ[volume] fun z ↦ conj (inclusionLp h F z) :=
  coeFn_inclusionLp_conjAux F

/-- Complex conjugation is an isometry of `H^s(E)`. -/
@[simp]
theorem norm_conjCLM (F : H^{s}(E)) : ‖conjCLM E h F‖ = ‖F‖ :=
  norm_conjAux F

/-- Complex conjugation is an isometry of `H^s(E)`. -/
theorem isometry_conjCLM : Isometry (conjCLM E h) :=
  AddMonoidHomClass.isometry_of_norm _ norm_conjCLM

/-- Complex conjugation on `H^s(E)` is conjugate-linear over `ℂ`. -/
@[simp]
theorem conjCLM_smul (c : ℂ) (F : H^{s}(E)) : conjCLM E h (c • F) = conj c • conjCLM E h F :=
  conjAux_smul (h := h) c F

/-- Complex conjugation on `H^s(E)` is an involution. -/
@[simp]
theorem conjCLM_conjCLM (F : H^{s}(E)) : conjCLM E h (conjCLM E h F) = F :=
  ext_of_ae_eq_inclusionLp h <| by
    filter_upwards [coeFn_inclusionLp_conjCLM (h := h) (conjCLM E h F),
      coeFn_inclusionLp_conjCLM (h := h) F] with z h₁ h₂
    rw [h₁, h₂, Complex.conj_conj]

/-- Complex conjugation fixes the real elements of `H^s(E)`. -/
@[simp]
theorem conjCLM_coe (F : realSubmodule E h) : conjCLM E h (F : H^{s}(E)) = F :=
  ext_of_ae_eq_inclusionLp h <| by
    filter_upwards [coeFn_inclusionLp_conjCLM (h := h) (F : H^{s}(E)),
      (mem_realSubmodule_iff h).1 F.property] with z h₁ h₂
    rw [h₁, Complex.conj_eq_iff_im.2 h₂]

/-- An element of `H^s(E)` is real exactly when complex conjugation fixes it. -/
theorem mem_realSubmodule_iff_conjCLM_eq {F : H^{s}(E)} :
    F ∈ realSubmodule E h ↔ conjCLM E h F = F := by
  refine ⟨fun hF ↦ conjCLM_coe ⟨F, hF⟩, fun hF ↦ (mem_realSubmodule_iff h).2 ?_⟩
  filter_upwards [coeFn_inclusionLp_conjCLM (h := h) F] with z hz
  rw [hF] at hz
  exact Complex.conj_eq_iff_im.1 hz.symm

private theorem norm_two_inv_smul_add_conjCLM_le (F : H^{s}(E)) :
    ‖(2⁻¹ : ℂ) • (F + conjCLM E h F)‖ ≤ ‖F‖ := by
  rw [norm_smul, norm_inv, Complex.norm_two]
  calc 2⁻¹ * ‖F + conjCLM E h F‖ ≤ 2⁻¹ * (‖F‖ + ‖conjCLM E h F‖) := by
        gcongr; exact norm_add_le _ _
    _ = ‖F‖ := by rw [norm_conjCLM]; ring

private theorem two_inv_smul_add_conjCLM_mem (F : H^{s}(E)) :
    (2⁻¹ : ℂ) • (F + conjCLM E h F) ∈ realSubmodule E h := by
  have h2 : (2⁻¹ : ℂ) = ((2⁻¹ : ℝ) : ℂ) := by norm_num
  rw [mem_realSubmodule_iff_conjCLM_eq, h2, Complex.coe_smul, (conjCLM E h).map_smul, map_add,
    conjCLM_conjCLM, add_comm]

variable (E h) in
/-- **The real part** `(F + conj F) / 2` of `F ∈ H^s(E)`, `0 ≤ s`: a bounded real-linear
projection of `H^s(E)` onto its real elements (`realPartCLM_coe`). -/
def realPartCLM : H^{s}(E) →L[ℝ] realSubmodule E h :=
  ContinuousLinearMap.codRestrict
    (LinearMap.mkContinuous
      { toFun F := (2⁻¹ : ℂ) • (F + conjCLM E h F)
        map_add' F G := by
          rw [map_add]
          module
        map_smul' c F := by
          rw [RingHom.id_apply, (conjCLM E h).map_smul, ← smul_add, smul_comm] }
      1 fun F ↦ (norm_two_inv_smul_add_conjCLM_le F).trans (one_mul _).symm.le)
    (realSubmodule E h) two_inv_smul_add_conjCLM_mem

/-- The real part of `F` is `(F + conj F) / 2`. -/
theorem coe_realPartCLM (F : H^{s}(E)) :
    (realPartCLM E h F : H^{s}(E)) = (2⁻¹ : ℂ) • (F + conjCLM E h F) :=
  (rfl)

/-- The real part fixes the real elements of `H^s(E)`. -/
@[simp]
theorem realPartCLM_coe (F : realSubmodule E h) : realPartCLM E h (F : H^{s}(E)) = F := by
  ext1
  rw [coe_realPartCLM, conjCLM_coe]
  module

end BesselPotentialSpace
