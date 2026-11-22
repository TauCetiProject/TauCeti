/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.FunctionalSpaces.BesselPotentialSpace
public import TauCeti.Analysis.Normed.Interpolation.CompatibleCouple
import TauCeti.Analysis.Distribution.TemperedDistribution.Lp

/-!
# Bessel-potential spaces as spaces of tempered distributions

An element `u` of Mathlib's Bessel-potential space `H^{s,p}(E, F)` is a tempered distribution
`u.toDistr`, namely `J^{-s} f` for its `Lᵖ` function `f`. This file bundles this inclusion as a
continuous linear map, so that the spaces `H^{s,p}` for different `s` can be compared inside
`𝓢'(E, F)`, for example as compatible couples for interpolation.

## Main declarations

* `BesselPotentialSpace.toDistrCLM`: the inclusion `H^{s,p}(E, F) →L[ℂ] 𝓢'(E, F)`.
* `BesselPotentialSpace.toDistrCLM_injective`: it is injective.
* `BesselPotentialSpace.toDistr_eq_toDistr_iff`: elements of `H^{s,p₀}` and `H^{s,p₁}` are the
  same tempered distribution exactly when their `Lᵖ` functions agree almost everywhere.
* `BesselPotentialSpace.norm_copy`, `BesselPotentialSpace.memSobolev_toDistr_of_eq`: moving an
  element along an equality of orders `s = s'`.
* `BesselPotentialSpace.enorm_toLp_eq`, `BesselPotentialSpace.integrable_toLp_iff`,
  `BesselPotentialSpace.toLp_intervalIntegral`: the isometry `u ↦ J^s u` of `H^{s,p}` onto `Lᵖ`
  transfers extended norms, Bochner integrability of `H^{s,p}`-valued functions and their
  interval integrals.
* `BesselPotentialSpace.toOrderZeroₗᵢ`: the real-order Bessel potential `J^s` as an isometry
  `H^{s,p}(E, F) ≃ₗᵢ[ℂ] H^{0,p}(E, F)`.
* `TauCeti.CompatibleCouple.besselPotentialSpace E F s₀ p₀ s₁ p₁`: the compatible couple
  `(H^{s₀,p₀}, H^{s₁,p₁})` inside `𝓢'(E, F)`.
-/

public section

noncomputable section

open MeasureTheory TemperedDistribution
open scoped ENNReal SchwartzMap BesselPotentialSpace

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

namespace BesselPotentialSpace

variable (E F) in
/-- The inclusion of the Bessel-potential space `H^{s,p}` into the tempered distributions, as a
continuous linear map: an element is the tempered distribution `J^{-s} f` of its `Lᵖ`
function `f`. -/
def toDistrCLM (s : ℝ) (p : ℝ≥0∞) [Fact (1 ≤ p)] : H^{s, p}(E, F) →L[ℂ] 𝓢'(E, F) :=
  besselPotential E F (-s) ∘L Lp.toTemperedDistributionCLM F volume p ∘L
    (toLpₗᵢ E F s p).toContinuousLinearEquiv.toContinuousLinearMap

@[simp]
theorem toDistrCLM_apply {s : ℝ} {p : ℝ≥0∞} [Fact (1 ≤ p)] (u : H^{s, p}(E, F)) :
    toDistrCLM E F s p u = u.toDistr := by
  simp [toDistrCLM]

theorem toDistrCLM_injective {s : ℝ} {p : ℝ≥0∞} [Fact (1 ≤ p)] :
    Function.Injective (toDistrCLM E F s p) := fun u v h ↦
  ext (by simpa using h)

section Exponents

variable {s : ℝ} {p₀ p₁ : ℝ≥0∞} [Fact (1 ≤ p₀)] [Fact (1 ≤ p₁)]

/-- Elements `u₀ ∈ H^{s,p₀}` and `u₁ ∈ H^{s,p₁}` of one order `s` are the same tempered
distribution exactly when their `Lᵖ` functions `J^s u₀` and `J^s u₁` agree almost everywhere. -/
theorem toDistr_eq_toDistr_iff {u₀ : H^{s, p₀}(E, F)} {u₁ : H^{s, p₁}(E, F)} :
    u₀.toDistr = u₁.toDistr ↔ u₀.toLp =ᵐ[volume] u₁.toLp := by
  rw [← Lp.toTemperedDistribution_eq_toTemperedDistribution_iff]
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rw [← u₀.bessel_toDistr_eq_toLp, ← u₁.bessel_toDistr_eq_toLp, h]
  · rw [← besselPotential_neg_toLp_eq (f := u₀), ← besselPotential_neg_toLp_eq (f := u₁), h]

end Exponents

/-- Transferring an element of `H^{s,p}` to `H^{s',p}` along `s = s'` keeps its norm. -/
@[simp]
theorem norm_copy {s s' : ℝ} {p : ℝ≥0∞} [Fact (1 ≤ p)] (u : H^{s, p}(E, F)) (hs : s = s') :
    ‖u.copy s' hs‖ = ‖u‖ := by
  rw [← norm_toLp_eq, toLp_copy _ hs, norm_toLp_eq]

/-- The extended norm of an element `u` of `H^{s,p}` is that of its `Lᵖ` function `J^s u`. -/
@[simp]
theorem enorm_toLp_eq {s : ℝ} {p : ℝ≥0∞} [Fact (1 ≤ p)] (u : H^{s, p}(E, F)) :
    ‖u.toLp‖ₑ = ‖u‖ₑ := by
  rw [← ofReal_norm, ← ofReal_norm, norm_toLp_eq]

/-- A function with values in `H^{s,p}` is Bochner integrable exactly when the `Lᵖ` functions
of its values are. -/
theorem integrable_toLp_iff {s : ℝ} {p : ℝ≥0∞} [Fact (1 ≤ p)] {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {G : α → H^{s, p}(E, F)} :
    Integrable (fun a ↦ (G a).toLp) μ ↔ Integrable G μ := by
  simpa only [toLpₗᵢ_apply] using (toLpₗᵢ E F s p).integrable_comp_iff

/-- The `Lᵖ` function of an interval integral in `H^{s,p}` is the interval integral of the `Lᵖ`
functions: `J^s ∫_a^b g = ∫_a^b J^s g`. -/
theorem toLp_intervalIntegral {s : ℝ} {p : ℝ≥0∞} [Fact (1 ≤ p)] (g : ℝ → H^{s, p}(E, F))
    (a b : ℝ) : (∫ τ in a..b, g τ).toLp = ∫ τ in a..b, (g τ).toLp := by
  simpa only [LinearIsometryEquiv.coe_toLinearIsometry, toLpₗᵢ_apply] using
    ((toLpₗᵢ E F s p).toLinearIsometry.intervalIntegral_comp_comm g).symm

/-- The tempered distribution of an element of `H^{t,p}` lies in `H^{s,p}` when `t = s`. -/
theorem memSobolev_toDistr_of_eq {s t : ℝ} {p : ℝ≥0∞} [Fact (1 ≤ p)] (u : H^{t, p}(E, F))
    (h : t = s) : MemSobolev s p u.toDistr :=
  h ▸ u.memSobolev_toDistr

section OrderZero

variable {s : ℝ} {p : ℝ≥0∞} [Fact (1 ≤ p)]

variable (E F) in
/-- The Bessel potential `J^s` as a linear isometry equivalence
`H^{s,p}(E, F) ≃ₗᵢ[ℂ] H^{0,p}(E, F)`: both spaces are identified with `Lᵖ` by
`BesselPotentialSpace.toLpₗᵢ`. -/
def toOrderZeroₗᵢ (s : ℝ) (p : ℝ≥0∞) [Fact (1 ≤ p)] : H^{s, p}(E, F) ≃ₗᵢ[ℂ] H^{0, p}(E, F) :=
  (toLpₗᵢ E F s p).trans (toLpₗᵢ E F 0 p).symm

/-- `toOrderZeroₗᵢ` acts on the underlying tempered distributions as the Bessel potential `J^s`. -/
@[simp]
theorem toDistr_toOrderZeroₗᵢ (u : H^{s, p}(E, F)) :
    (toOrderZeroₗᵢ E F s p u).toDistr = besselPotential E F s u.toDistr := by
  have h : (toOrderZeroₗᵢ E F s p u).toDistr = besselPotential E F (-0) u.toLp := by
    simp [toOrderZeroₗᵢ]
  rw [h, neg_zero, besselPotential_zero, ContinuousLinearMap.id_apply,
    ← u.bessel_toDistr_eq_toLp]

/-- The inverse of `toOrderZeroₗᵢ` acts on the underlying tempered distributions as the Bessel
potential `J^{-s}`. -/
@[simp]
theorem toDistr_toOrderZeroₗᵢ_symm (u : H^{0, p}(E, F)) :
    ((toOrderZeroₗᵢ E F s p).symm u).toDistr = besselPotential E F (-s) u.toDistr := by
  have h : ((toOrderZeroₗᵢ E F s p).symm u).toDistr = besselPotential E F (-s) u.toLp := by
    simp [toOrderZeroₗᵢ]
  rw [h, ← u.bessel_toDistr_eq_toLp, besselPotential_zero, ContinuousLinearMap.id_apply]

end OrderZero

end BesselPotentialSpace

namespace TauCeti.CompatibleCouple

open BesselPotentialSpace

variable (E F) in
/-- The compatible couple `(H^{s₀,p₀}, H^{s₁,p₁})` of Bessel-potential spaces, both embedded into
the tempered distributions. -/
def besselPotentialSpace (s₀ : ℝ) (p₀ : ℝ≥0∞) (s₁ : ℝ) (p₁ : ℝ≥0∞) [Fact (1 ≤ p₀)]
    [Fact (1 ≤ p₁)] : CompatibleCouple ℂ H^{s₀, p₀}(E, F) H^{s₁, p₁}(E, F) 𝓢'(E, F) where
  embed₀ := toDistrCLM E F s₀ p₀
  embed₁ := toDistrCLM E F s₁ p₁
  embed₀_injective := toDistrCLM_injective
  embed₁_injective := toDistrCLM_injective

variable {s₀ s₁ : ℝ} {p₀ p₁ : ℝ≥0∞} [Fact (1 ≤ p₀)] [Fact (1 ≤ p₁)]

@[simp]
theorem besselPotentialSpace_embed₀_apply (u : H^{s₀, p₀}(E, F)) :
    (besselPotentialSpace E F s₀ p₀ s₁ p₁).embed₀ u = u.toDistr :=
  toDistrCLM_apply u

@[simp]
theorem besselPotentialSpace_embed₁_apply (u : H^{s₁, p₁}(E, F)) :
    (besselPotentialSpace E F s₀ p₀ s₁ p₁).embed₁ u = u.toDistr :=
  toDistrCLM_apply u

end TauCeti.CompatibleCouple
