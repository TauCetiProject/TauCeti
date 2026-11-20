/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.Sobolev
public import TauCeti.Analysis.Sobolev.BesselPotential.Inclusion
import TauCeti.Analysis.Sobolev.BesselPotential.ZeroAtInfty

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
`BesselPotentialSpace.continuousRep_eq_of_ae_eq`), the real part of its image under the Sobolev
embedding `BesselPotentialSpace.toZeroAtInfty` into continuous functions. It lies in the real
`H^s` functions `TemperedDistribution.realSobolevFunctions E s 2` and is `ℝ`-linear in `F`
(`BesselPotentialSpace.continuousRep` is a linear map), and it determines `F`
(`BesselPotentialSpace.continuousRep_injective`).
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

variable {h : 0 ≤ s}

open Classical in
/-- **The continuous representative of a real element** `F ∈ H^s(E)`, as an `ℝ`-linear map:
above the Sobolev threshold `s > dim E / 2`, the continuous real function whose values agree
almost everywhere with the `L²` function of `F` (`coeFn_inclusionLp_ae_eq_continuousRep`), namely
the real part of its Sobolev embedding `toZeroAtInfty`. It is unique (`continuousRep_eq_of_ae_eq`).
Below the threshold, where `F` need not have a continuous representative, it is the junk
value `0`. -/
def continuousRep : realSubmodule E h →ₗ[ℝ] (E → ℝ) :=
  if hs : finrank ℝ E < 2 * s then
    { toFun F z := (toZeroAtInfty hs (F : H^{s}(E)) z).re
      map_add' F G := by ext z; simp
      map_smul' c F := by ext z; simp }
  else 0

private theorem continuousRep_spec (hs : finrank ℝ E < 2 * s) (F : realSubmodule E h) :
    Continuous (continuousRep F) ∧
      inclusionLp h (F : H^{s}(E)) =ᵐ[volume] fun z ↦ (continuousRep F z : ℂ) := by
  simp only [continuousRep, hs, ↓reduceDIte, LinearMap.coe_mk, AddHom.coe_mk]
  refine ⟨by fun_prop, ?_⟩
  filter_upwards [(mem_realSubmodule_iff h).1 F.property,
    coeFn_inclusionLp_ae_eq_toZeroAtInfty (hs := hs) h (F : H^{s}(E))] with z hz hz'
  rw [← hz']
  exact Complex.ext rfl (by simpa using hz)

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
    continuousRep F = f := by
  refine (Continuous.ae_eq_iff_eq volume (continuous_continuousRep hs F) hf).1 ?_
  filter_upwards [(coeFn_inclusionLp_ae_eq_continuousRep hs F).symm.trans hF] with z hz
  exact_mod_cast hz

/-- **The continuous representative of a real element.** Above the Sobolev threshold
`s > dim E / 2`, the `L²` function of a real element `F ∈ H^s(E)` agrees almost everywhere with a
continuous real function. -/
theorem exists_continuous_ae_eq_of_mem_realSubmodule (hs : finrank ℝ E < 2 * s)
    (F : realSubmodule E h) :
    ∃ f : E → ℝ, Continuous f ∧ inclusionLp h (F : H^{s}(E)) =ᵐ[volume] fun z ↦ (f z : ℂ) :=
  ⟨continuousRep F, continuous_continuousRep hs F, coeFn_inclusionLp_ae_eq_continuousRep hs F⟩

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
  mem_realSobolevFunctions_of_ae_eq_ofReal (memSobolev_inclusionLp h (F : H^{s}(E)))
    (by simpa using coeFn_inclusionLp_ae_eq_continuousRep hs F)

end BesselPotentialSpace
