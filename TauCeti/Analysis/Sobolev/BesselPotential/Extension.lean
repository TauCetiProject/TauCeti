/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.BesselPotential.Inclusion
import TauCeti.Analysis.Distribution.SchwartzSpace.Fourier

/-!
# Extensions of Schwartz-space operators to Bessel-potential spaces

A continuous linear map `A : 𝓢(E, F) →L[ℂ] 𝓢(E, G)` *extends* to a bounded operator
`H^s(E, F) → H^r(E, G)` between Mathlib's Bessel-potential spaces `H^s = H^{s,2}` if some
`T : H^s(E, F) →L[ℂ] H^r(E, G)` agrees with `A` on Schwartz functions
(`SchwartzMap.HasSobolevExtension`). Operators such as pseudodifferential operators are first
defined and estimated on Schwartz functions, and their Sobolev mapping properties are statements of
this form.

This file proves that such extensions are closed under composition and linear combinations, that
the target order may be lowered, and that the Bessel multiplier `J^t`, the Fourier multiplier with
symbol `⟨ξ⟩ ^ t = (1 + ‖ξ‖ ^ 2) ^ (t / 2)`, extends to an operator `H^s → H^{s - t}`.

## Main declarations

* `SchwartzMap.HasSobolevExtension`: `A` extends to a bounded operator `H^s → H^r`, characterised
  by `SchwartzMap.hasSobolevExtension_iff`.
* `SchwartzMap.hasSobolevExtension_zero`, `SchwartzMap.hasSobolevExtension_id`: the zero map and the
  identity extend.
* `SchwartzMap.HasSobolevExtension.comp`, `SchwartzMap.HasSobolevExtension.add`,
  `SchwartzMap.HasSobolevExtension.neg`, `SchwartzMap.HasSobolevExtension.smul`,
  `SchwartzMap.HasSobolevExtension.sub`: extensions compose and form a vector space.
* `SchwartzMap.HasSobolevExtension.mono`: an extension into `H^r` is one into every `H^{r'}` with
  `r' ≤ r`.
* `SchwartzMap.hasSobolevExtension_besselMultiplier`: `J^t` extends to `H^s → H^{s - t}`.
-/

public section

noncomputable section

open MeasureTheory
open scoped SchwartzMap BesselPotentialSpace

namespace SchwartzMap

variable {E F G K : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- A continuous linear map `A` of Schwartz spaces extends to a bounded operator `H^s → H^r`: some
continuous linear map `T : H^s(E, F) →L[ℂ] H^r(E, G)` agrees with `A` on Schwartz functions. -/
def HasSobolevExtension (A : 𝓢(E, F) →L[ℂ] 𝓢(E, G)) (s r : ℝ) : Prop :=
  ∃ T : H^{s}(E, F) →L[ℂ] H^{r}(E, G),
    T ∘L toBesselPotentialSpaceCLM s 2 = toBesselPotentialSpaceCLM r 2 ∘L A

/-- `A` extends to a bounded operator `H^s → H^r` if and only if some continuous linear map
`T : H^s(E, F) →L[ℂ] H^r(E, G)` agrees with `A` on Schwartz functions. -/
theorem hasSobolevExtension_iff {A : 𝓢(E, F) →L[ℂ] 𝓢(E, G)} {s r : ℝ} :
    HasSobolevExtension A s r ↔ ∃ T : H^{s}(E, F) →L[ℂ] H^{r}(E, G),
      T ∘L toBesselPotentialSpaceCLM s 2 = toBesselPotentialSpaceCLM r 2 ∘L A :=
  Iff.rfl

/-- The zero map extends to a bounded operator `H^s → H^r`. -/
theorem hasSobolevExtension_zero (s r : ℝ) :
    HasSobolevExtension (0 : 𝓢(E, F) →L[ℂ] 𝓢(E, G)) s r :=
  ⟨0, by rw [ContinuousLinearMap.zero_comp, ContinuousLinearMap.comp_zero]⟩

/-- The identity extends to a bounded operator `H^s → H^s`. -/
theorem hasSobolevExtension_id (s : ℝ) :
    HasSobolevExtension (ContinuousLinearMap.id ℂ 𝓢(E, F)) s s :=
  ⟨ContinuousLinearMap.id ℂ _, by rw [ContinuousLinearMap.id_comp, ContinuousLinearMap.comp_id]⟩

namespace HasSobolevExtension

variable {A B : 𝓢(E, F) →L[ℂ] 𝓢(E, G)} {s r q : ℝ}

/-- Extensions `H^s → H^r` and `H^r → H^q` compose to an extension `H^s → H^q`. -/
theorem comp {C : 𝓢(E, G) →L[ℂ] 𝓢(E, K)} (hC : HasSobolevExtension C r q)
    (hA : HasSobolevExtension A s r) : HasSobolevExtension (C ∘L A) s q := by
  obtain ⟨T, hT⟩ := hA
  obtain ⟨T', hT'⟩ := hC
  exact ⟨T' ∘L T, by rw [ContinuousLinearMap.comp_assoc, hT, ← ContinuousLinearMap.comp_assoc,
    hT', ContinuousLinearMap.comp_assoc]⟩

/-- The sum of operators extending to `H^s → H^r` extends to `H^s → H^r`. -/
theorem add (hA : HasSobolevExtension A s r) (hB : HasSobolevExtension B s r) :
    HasSobolevExtension (A + B) s r := by
  obtain ⟨T, hT⟩ := hA
  obtain ⟨T', hT'⟩ := hB
  exact ⟨T + T', by rw [ContinuousLinearMap.add_comp, hT, hT', ContinuousLinearMap.comp_add]⟩

/-- The negative of an operator extending to `H^s → H^r` extends to `H^s → H^r`. -/
theorem neg (hA : HasSobolevExtension A s r) : HasSobolevExtension (-A) s r := by
  obtain ⟨T, hT⟩ := hA
  exact ⟨-T, by rw [ContinuousLinearMap.neg_comp, hT, ContinuousLinearMap.comp_neg]⟩

/-- A complex multiple of an operator extending to `H^s → H^r` extends to `H^s → H^r`. -/
theorem smul (hA : HasSobolevExtension A s r) (c : ℂ) : HasSobolevExtension (c • A) s r := by
  obtain ⟨T, hT⟩ := hA
  exact ⟨c • T, by rw [ContinuousLinearMap.smul_comp, hT, ContinuousLinearMap.comp_smul]⟩

/-- A real multiple of an operator extending to `H^s → H^r` extends to `H^s → H^r`. -/
theorem smul_real (hA : HasSobolevExtension A s r) (c : ℝ) : HasSobolevExtension (c • A) s r := by
  simpa only [Complex.coe_smul] using hA.smul (c : ℂ)

/-- The difference of operators extending to `H^s → H^r` extends to `H^s → H^r`. -/
theorem sub (hA : HasSobolevExtension A s r) (hB : HasSobolevExtension B s r) :
    HasSobolevExtension (A - B) s r := by
  simpa only [sub_eq_add_neg] using hA.add hB.neg

/-- Extensions into `H^r` are extensions into every `H^{r'}` with `r' ≤ r`. -/
theorem mono (hA : HasSobolevExtension A s r) {r' : ℝ} (h : r' ≤ r) :
    HasSobolevExtension A s r' := by
  obtain ⟨T, hT⟩ := hA
  refine ⟨BesselPotentialSpace.inclusion h ∘L T, ?_⟩
  rw [ContinuousLinearMap.comp_assoc, hT, ← ContinuousLinearMap.comp_assoc]
  congr 1
  exact ContinuousLinearMap.ext (BesselPotentialSpace.inclusion_toBesselPotentialSpaceCLM h)

end HasSobolevExtension

/-- The Bessel multiplier `J^t`, the Fourier multiplier with symbol `⟨ξ⟩ ^ t`, extends to a
bounded operator `H^s → H^r` when `r + t = s`. -/
theorem hasSobolevExtension_besselMultiplier {s r : ℝ} (t : ℝ) (h : r + t = s) :
    HasSobolevExtension (fourierMultiplierCLM F
      (fun ζ : E ↦ (((1 + ‖ζ‖ ^ 2) ^ (t / 2) : ℝ) : ℂ))) s r := by
  refine ⟨((BesselPotentialSpace.toLpₗᵢ E F r 2).symm.toContinuousLinearEquiv :
      Lp F 2 (volume : Measure E) →L[ℂ] H^{r}(E, F)) ∘L
    ((BesselPotentialSpace.toLpₗᵢ E F s 2).toContinuousLinearEquiv :
      H^{s}(E, F) →L[ℂ] Lp F 2 (volume : Measure E)), ?_⟩
  ext1 u
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv, BesselPotentialSpace.toLpₗᵢ_apply,
    toLp_toBesselPotentialSpaceCLM, LinearIsometryEquiv.symm_apply_eq,
    fourierMultiplierCLM_one_add_norm_sq_rpow_fourierMultiplierCLM, h]

end SchwartzMap
