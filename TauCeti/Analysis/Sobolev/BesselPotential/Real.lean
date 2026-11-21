/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.Sobolev
public import TauCeti.Analysis.Sobolev.BesselPotential.Inclusion
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
determines `F` (`BesselPotentialSpace.continuousRep_injective`).
-/

public section

noncomputable section

open MeasureTheory Module TemperedDistribution
open scoped SchwartzMap BesselPotentialSpace

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
  refine Subtype.ext (inclusionLp_injective h (Lp.ext ?_))
  filter_upwards [coeFn_inclusionLp_ae_eq_continuousRep hs F,
    coeFn_inclusionLp_ae_eq_continuousRep hs G] with z hF hG
  rw [hF, hG, hFG]

/-- The continuous representative lies in the real `H^s` functions. -/
theorem continuousRep_mem_realSobolevFunctions (hs : finrank ℝ E < 2 * s)
    (F : realSubmodule E h) : continuousRep F ∈ realSobolevFunctions E s 2 :=
  mem_realSobolevFunctions_of_ae_eq_ofReal (memSobolev_toLp_inclusion h (F : H^{s}(E)))
    (by simpa using coeFn_inclusionLp_ae_eq_continuousRep hs F)

end BesselPotentialSpace
