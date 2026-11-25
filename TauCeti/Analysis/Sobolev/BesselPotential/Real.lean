/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.Sobolev
public import TauCeti.Analysis.Sobolev.BesselPotential.Inclusion
import TauCeti.Analysis.Sobolev.BesselPotential.Conj
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
(`BesselPotentialSpace.continuousRep_injective`). Convergence in `H^s` makes the continuous
representatives converge uniformly (`BesselPotentialSpace.tendstoUniformly_continuousRep`). Above
`s > n + dim E / 2` the continuous representative is a `Cⁿ` function
(`BesselPotentialSpace.contDiff_continuousRep`).

Complex conjugation of the `L²` function is a real-linear isometric involution
`BesselPotentialSpace.conjCLM` of `H^s(E)` (`BesselPotentialSpace.norm_conjCLM`,
`BesselPotentialSpace.conjCLM_conjCLM`), conjugate-linear over `ℂ`
(`BesselPotentialSpace.conjCLM_smul`), by `TemperedDistribution.MemSobolev.of_ae_eq_conj`; the
real elements are its fixed points (`BesselPotentialSpace.mem_realSubmodule_iff_conjCLM_eq`). The
real part `(F + conj F) / 2` is therefore a bounded real-linear projection
`BesselPotentialSpace.realPartCLM` of `H^s(E)` onto the real subspace
(`BesselPotentialSpace.realPartCLM_coe`), whose `L²` function is the real part of that of `F`
(`BesselPotentialSpace.coeFn_inclusionLp_realPartCLM`). Composing with it turns a smooth map into
`H^s(E)` that takes real values into a smooth map into the real subspace, with the same order of
smoothness, analytic included.

The real action on `H^s(E)` is restricted from the complex one
(`BesselPotentialSpace.isScalarTower_real_complex`), so `ℂ`-bilinear maps of `H^s(E)` restrict
to real ones.

Applied in each coordinate, the inclusion of the real subspace and the real part give bounded
real-linear maps `BesselPotentialSpace.coordInclusion` and `BesselPotentialSpace.realPartPi`
between `(realSubmodule E h)^ι` and `H^s(E)^ι`, the second a left inverse of the first
(`BesselPotentialSpace.realPartPi_coordInclusion`).

The inclusions `H^s(E) ⊆ H^r(E)`, `r ≤ s`, preserve real elements
(`BesselPotentialSpace.inclusion_mem_realSubmodule`). For equal orders `s = t` written differently
they identify the two real subspaces (`BesselPotentialSpace.realSubmoduleCongr`).
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
  refine Subtype.ext (ext_of_ae_eq_inclusionLp h ?_)
  filter_upwards [coeFn_inclusionLp_ae_eq_continuousRep hs F,
    coeFn_inclusionLp_ae_eq_continuousRep hs G] with z hF hG
  rw [hF, hG, hFG]

/-- The continuous representative lies in the real `H^s` functions. -/
theorem continuousRep_mem_realSobolevFunctions (hs : finrank ℝ E < 2 * s)
    (F : realSubmodule E h) : continuousRep F ∈ realSobolevFunctions E s 2 :=
  mem_realSobolevFunctions_of_ae_eq_ofReal (memSobolev_inclusionLp h (F : H^{s}(E)))
    (by simpa using coeFn_inclusionLp_ae_eq_continuousRep hs F)

/-- **Continuous representatives converge uniformly.** Above the Sobolev threshold
`s > dim E / 2`, if real elements `F` of `H^s(E)` tend to `F₀` in `H^s`, their continuous
representatives tend uniformly to that of `F₀`. -/
theorem tendstoUniformly_continuousRep (hs : finrank ℝ E < 2 * s) (F₀ : realSubmodule E h) :
    TendstoUniformly (fun F : realSubmodule E h ↦ continuousRep F) (continuousRep F₀) (𝓝 F₀) := by
  have happ (F : realSubmodule E h) (z : E) :
      continuousRep F z = (toZeroAtInfty hs (F : H^{s}(E)) z).re := by
    simp only [continuousRep, hs, ↓reduceDIte, LinearMap.coe_mk, AddHom.coe_mk]
  have hT := ZeroAtInftyContinuousMap.tendsto_iff_tendstoUniformly.1
    (((toZeroAtInfty hs).continuous.comp continuous_subtypeVal).tendsto F₀)
  rw [Metric.tendstoUniformly_iff] at hT ⊢
  intro ε hε
  filter_upwards [hT ε hε] with F hF z
  rw [happ, happ, Real.dist_eq, ← Complex.sub_re]
  exact (Complex.abs_re_le_norm _).trans_lt (by simpa [dist_eq_norm] using hF z)

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
  (MemSobolev.of_ae_eq_conj (memSobolev_inclusionLp h F) (u' := star (inclusionLp h F))
    (Lp.coeFn_star _)).toBesselPotentialSpace

private theorem coeFn_inclusionLp_conjAux (F : H^{s}(E)) :
    inclusionLp h (conjAux h F) =ᵐ[volume] fun z ↦ conj (inclusionLp h F z) := by
  rw [conjAux, ← toLp_inclusion, toLp_inclusion_toBesselPotentialSpace h _ rfl]
  exact Lp.coeFn_star _

private theorem conjAux_smul (c : ℂ) (F : H^{s}(E)) :
    conjAux h (c • F) = conj c • conjAux h F :=
  ext_of_ae_eq_inclusionLp h <| by
    filter_upwards [coeFn_inclusionLp_conjAux (h := h) (c • F),
      coeFn_inclusionLp_conjAux (h := h) F, Lp.coeFn_smul c (inclusionLp h F),
      Lp.coeFn_smul (conj c) (inclusionLp h (conjAux h F))] with z h₁ h₂ h₃ h₄
    simp only [(inclusionLp h).map_smul, h₁, h₂, h₃, h₄, Pi.smul_apply, smul_eq_mul, map_mul]

private theorem norm_conjAux (F : H^{s}(E)) : ‖conjAux h F‖ = ‖F‖ :=
  (MemSobolev.norm_toBesselPotentialSpace_of_ae_eq_conj (memSobolev_inclusionLp h F)
    (Lp.coeFn_star _) _).trans
    (congrArg norm (toBesselPotentialSpace_memSobolev_inclusionLp h F))

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

/-- The `L²` function of the real part of `F ∈ H^s(E)` is the real part of the `L²` function of
`F`. -/
theorem coeFn_inclusionLp_realPartCLM (F : H^{s}(E)) :
    ⇑(inclusionLp h (realPartCLM E h F : H^{s}(E))) =ᵐ[volume]
      fun z ↦ ((inclusionLp h F z).re : ℂ) := by
  rw [coe_realPartCLM]
  filter_upwards [coeFn_inclusionLp_smul_ae_eq h (2⁻¹ : ℂ)
    (coeFn_inclusionLp_add_ae_eq h (u := F) (v := conjCLM E h F) (F := ⇑(inclusionLp h F))
      (F' := fun z ↦ conj (inclusionLp h F z)) (Filter.Eventually.of_forall fun _ ↦ rfl)
      (coeFn_inclusionLp_conjCLM F))] with z hz
  rw [hz, Complex.re_eq_add_conj]
  ring

/-! ### The real and complex scalar actions -/

/-- The scalar tower `ℝ → ℂ → H^s(E)`. Instance search does not find it: the real action on
`H^s(E)` comes from its complex normed space structure, and agrees with the action restricted
from `ℂ` only up to definitional unfolding. With it, `ℂ`-linear and `ℂ`-bilinear maps of `H^s(E)`
restrict to real ones (`ContinuousLinearMap.bilinearRestrictScalars`). -/
instance isScalarTower_real_complex : IsScalarTower ℝ ℂ H^{s}(E) :=
  ⟨fun r c v ↦ by rw [Complex.real_smul, mul_smul, Complex.coe_smul]; rfl⟩

/-! ### Coordinatewise inclusion and real part -/

variable (E h) in
/-- **The inclusion of real coordinates**: the bounded real-linear map
`(ι → realSubmodule E h) → (ι → H^s(E))` including each coordinate into `H^s(E)`. -/
@[expose] def coordInclusion {ι : Type*} : (ι → realSubmodule E h) →L[ℝ] (ι → H^{s}(E)) :=
  ContinuousLinearMap.piMap fun _ ↦ (realSubmodule E h).subtypeL

@[simp]
theorem coordInclusion_apply {ι : Type*} (u : ι → realSubmodule E h) (i : ι) :
    coordInclusion E h u i = u i :=
  (rfl)

variable (E h) in
/-- **The real part, coordinatewise**: the bounded real-linear projection
`(ι → H^s(E)) → (ι → realSubmodule E h)` applying `realPartCLM` in each coordinate. -/
def realPartPi {ι : Type*} : (ι → H^{s}(E)) →L[ℝ] (ι → realSubmodule E h) :=
  ContinuousLinearMap.piMap fun _ ↦ realPartCLM E h

@[simp]
theorem realPartPi_apply {ι : Type*} (v : ι → H^{s}(E)) (i : ι) :
    realPartPi E h v i = realPartCLM E h (v i) :=
  (rfl)

/-- The coordinatewise real part is a left inverse of the inclusion of real coordinates. -/
@[simp]
theorem realPartPi_coordInclusion {ι : Type*} (u : ι → realSubmodule E h) :
    realPartPi E h (coordInclusion E h u) = u :=
  funext fun i ↦ by rw [realPartPi_apply, coordInclusion_apply, realPartCLM_coe]

/-! ### Inclusions between orders -/

/-- The inclusion `H^s(E) ⊆ H^r(E)`, `0 ≤ r ≤ s`, maps real elements to real elements. -/
theorem inclusion_mem_realSubmodule {r : ℝ} (hrs : r ≤ s) (hr : 0 ≤ r) (F : realSubmodule E h) :
    inclusion hrs (F : H^{s}(E)) ∈ realSubmodule E hr := by
  rw [mem_realSubmodule_iff, inclusionLp_inclusion]
  exact (mem_realSubmodule_iff h).1 F.property

variable (E) in
/-- **The real elements of `H^s(E)` for equal orders.** For `s = t`, the inclusions identify the
real elements of `H^s(E)` and of `H^t(E)`, as real Hilbert spaces. This transports real
elements between two expressions of the same order. -/
def realSubmoduleCongr {t : ℝ} (hst : s = t) (h : 0 ≤ s) (ht : 0 ≤ t) :
    realSubmodule E h ≃L[ℝ] realSubmodule E ht :=
  ContinuousLinearEquiv.ofContinuousLinearMap
    ((((inclusion hst.ge).restrictScalars ℝ).comp (realSubmodule E h).subtypeL).codRestrict _
      (inclusion_mem_realSubmodule hst.ge ht))
    ((((inclusion hst.le).restrictScalars ℝ).comp (realSubmodule E ht).subtypeL).codRestrict _
      (inclusion_mem_realSubmodule hst.le h))
    (ContinuousLinearMap.ext fun _ ↦ Subtype.ext <| inclusion_inclusion hst.le hst.ge _ |>.trans
      (inclusion_self _))
    (ContinuousLinearMap.ext fun _ ↦ Subtype.ext <| inclusion_inclusion hst.ge hst.le _ |>.trans
      (inclusion_self _))

@[simp]
theorem coe_realSubmoduleCongr {t : ℝ} (hst : s = t) (ht : 0 ≤ t) (F : realSubmodule E h) :
    (realSubmoduleCongr E hst h ht F : H^{t}(E)) = inclusion hst.ge (F : H^{s}(E)) :=
  (rfl)

/-- The inverse of `realSubmoduleCongr` is `realSubmoduleCongr` for the reversed equality. -/
@[simp]
theorem realSubmoduleCongr_symm {t : ℝ} (hst : s = t) (ht : 0 ≤ t) :
    (realSubmoduleCongr E hst h ht).symm = realSubmoduleCongr E hst.symm ht h :=
  (rfl)

/-- `realSubmoduleCongr` does not change the `L²` function. -/
theorem inclusionLp_realSubmoduleCongr {t : ℝ} (hst : s = t) (ht : 0 ≤ t)
    (F : realSubmodule E h) :
    inclusionLp ht (realSubmoduleCongr E hst h ht F : H^{t}(E)) = inclusionLp h (F : H^{s}(E)) :=
  inclusionLp_inclusion hst.ge ht _

/-- `realSubmoduleCongr` does not change the continuous representative. -/
theorem continuousRep_realSubmoduleCongr (hs : finrank ℝ E < 2 * s) {t : ℝ} (hst : s = t)
    (ht : 0 ≤ t) (F : realSubmodule E h) :
    continuousRep (realSubmoduleCongr E hst h ht F) = continuousRep F :=
  continuousRep_eq_of_ae_eq (hst ▸ hs) (continuous_continuousRep hs F) <| by
    rw [inclusionLp_realSubmoduleCongr]
    exact coeFn_inclusionLp_ae_eq_continuousRep hs F

end BesselPotentialSpace
