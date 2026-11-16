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
and is `ℝ`-linear in `F` (`BesselPotentialSpace.continuousRep_add`,
`BesselPotentialSpace.continuousRep_smul`), and it determines `F`
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
    filter_upwards [(mem_realSubmodule_iff h).1 F.2, hg] with z hz hz'
    rw [← hz', hz]
  refine ⟨fun z ↦ (g z).re, by fun_prop, ?_⟩
  filter_upwards [hg] with z hz
  rw [hz]
  exact Complex.ext rfl (by simpa using congrFun him z)

variable {h : 0 ≤ s}

open Classical in
/-- **The continuous representative of a real element** `F ∈ H^s(E)`: above the Sobolev
threshold `s > dim E / 2`, the continuous real function whose values agree almost everywhere with
the `L²` function of `F` (`coeFn_inclusionLp_ae_eq_continuousRep`). It is unique
(`continuousRep_eq_of_ae_eq`). If `F` has no continuous representative, which can only happen
below the threshold, it is the junk value `0`. -/
def continuousRep (F : realSubmodule E h) : E → ℝ :=
  if hF : ∃ f : E → ℝ, Continuous f ∧ inclusionLp h (F : H^{s}(E)) =ᵐ[volume] fun z ↦ (f z : ℂ)
  then hF.choose else 0

private theorem continuousRep_spec (hs : finrank ℝ E < 2 * s) (F : realSubmodule E h) :
    Continuous (continuousRep F) ∧
      inclusionLp h (F : H^{s}(E)) =ᵐ[volume] fun z ↦ (continuousRep F z : ℂ) := by
  have hF := exists_continuous_ae_eq_of_mem_realSubmodule hs F
  simp only [continuousRep, hF, ↓reduceDIte]
  exact hF.choose_spec

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
  have hFf := (coeFn_inclusionLp_ae_eq_continuousRep hs F).symm.trans hF
  refine (Continuous.ae_eq_iff_eq volume (continuous_continuousRep hs F) hf).1 ?_
  filter_upwards [hFf] with z hz
  exact_mod_cast hz

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

theorem continuousRep_add (hs : finrank ℝ E < 2 * s) (F G : realSubmodule E h) :
    continuousRep (F + G) = continuousRep F + continuousRep G := by
  refine continuousRep_eq_of_ae_eq hs
    ((continuous_continuousRep hs F).add (continuous_continuousRep hs G)) ?_
  rw [Submodule.coe_add, map_add]
  filter_upwards [Lp.coeFn_add (inclusionLp h (F : H^{s}(E))) (inclusionLp h (G : H^{s}(E))),
    coeFn_inclusionLp_ae_eq_continuousRep hs F, coeFn_inclusionLp_ae_eq_continuousRep hs G]
    with z hz hF hG
  rw [hz, Pi.add_apply, hF, hG, Pi.add_apply, Complex.ofReal_add]

theorem continuousRep_zero (hs : finrank ℝ E < 2 * s) :
    continuousRep (0 : realSubmodule E h) = 0 := by
  refine continuousRep_eq_of_ae_eq hs continuous_const ?_
  rw [Submodule.coe_zero, map_zero]
  filter_upwards [Lp.coeFn_zero ℂ 2 (volume : Measure E)] with z hz
  rw [hz, Pi.zero_apply, Pi.zero_apply, Complex.ofReal_zero]

theorem continuousRep_smul (hs : finrank ℝ E < 2 * s) (c : ℝ) (F : realSubmodule E h) :
    continuousRep (c • F) = c • continuousRep F := by
  refine continuousRep_eq_of_ae_eq hs ((continuous_continuousRep hs F).const_smul c) ?_
  rw [Submodule.coe_smul, ← Complex.coe_smul, map_smul]
  filter_upwards [Lp.coeFn_smul (c : ℂ) (inclusionLp h (F : H^{s}(E))),
    coeFn_inclusionLp_ae_eq_continuousRep hs F] with z hz hF
  rw [hz, Pi.smul_apply, hF, Pi.smul_apply, smul_eq_mul, smul_eq_mul, Complex.ofReal_mul]

theorem continuousRep_neg (hs : finrank ℝ E < 2 * s) (F : realSubmodule E h) :
    continuousRep (-F) = -continuousRep F := by
  rw [← neg_one_smul ℝ F, continuousRep_smul hs, neg_one_smul]

theorem continuousRep_sub (hs : finrank ℝ E < 2 * s) (F G : realSubmodule E h) :
    continuousRep (F - G) = continuousRep F - continuousRep G := by
  rw [sub_eq_add_neg, continuousRep_add hs, continuousRep_neg hs, sub_eq_add_neg]

end BesselPotentialSpace
