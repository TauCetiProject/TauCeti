/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.LocalRegularity
public import TauCeti.Analysis.Distribution.MicrolocalRegularity
public import TauCeti.Analysis.Distribution.WaveFrontSet.Sobolev.Tempered
import TauCeti.Analysis.Distribution.WaveFrontSet.ChangeOfVariables
import TauCeti.Analysis.Distribution.WaveFrontSet.Sobolev.Decomposition
import TauCeti.Analysis.Sobolev.BesselPotential.Local

/-!
# Sobolev regularity under smooth changes of variables

Let `e` be a smooth open partial homeomorphism of a finite-dimensional real inner product space
`E` with smooth inverse, `U` an open subset of its source and `Ω` an open set containing `e '' U`.
A complex distribution `T` on `Ω` pulls back to the distribution `e^* T` on `U`
(`Distribution.compCLMOfOpenPartialHomeomorph`). This file proves that being `H^s` near a point
(`Distribution.IsLocallySobolevAt`) is invariant under this pullback, for every real `s`:

`e^* T` is `H^s` near `x` if and only if `T` is `H^s` near `e x`

(`Distribution.isLocallySobolevAt_compCLMOfOpenPartialHomeomorph_iff`), so the `H^s` singular
support transforms by `e`: `singsupp_s (e^* T) = U ∩ e⁻¹ (singsupp_s T)`
(`Distribution.sobolevSingularSupport_compCLMOfOpenPartialHomeomorph`). Since chart transitions
are such maps `e`, this is the chart-change invariance needed to define the local Sobolev spaces
`H^s_loc` on manifolds chart by chart. For sections of vector bundles, invariance under frame
changes (multiplication by smooth matrix-valued functions) is needed in addition; this file does
not prove it.

The same holds microlocally: covectors pull back by the transpose of the derivative,

`e^* T` is microlocally `H^s` at `(x, ξ)` if and only if `T` is microlocally `H^s` at
`(e x, (De⁻¹(e x))ᵀ ξ)`

(`Distribution.isMicrolocallySobolevAt_compCLMOfOpenPartialHomeomorph_iff`), so the `H^s` wave
front set of `e^* T` is the pullback of that of `T`
(`Distribution.sobolevWaveFrontSet_compCLMOfOpenPartialHomeomorph`). This is the `H^s` refinement
of the invariance of the wave front set
(`Distribution.waveFrontSet_compCLMOfOpenPartialHomeomorph`), and what makes the `H^s` wave front
set a well-defined subset of the cotangent bundle of a manifold.

## The argument

This is the case `p = 2` of the invariance of local `H^{s,p}` regularity
(`Distribution.isLocallyMemSobolevAt_compCLMOfOpenPartialHomeomorph_iff`), since being `H^s` near
a point is being `H^{s,2}` near it (`Distribution.isLocallyMemSobolevAt_two_iff`). Near `x`, `e`
agrees with a bijection `Φ` of `E` whose derivatives are bounded, on a neighbourhood of `x` the
pullback `e^* T` is the tempered pullback `Φ^* (χ T)` of a cut-off `χ T`
(`Distribution.restrictCLM_compCLMOfOpenPartialHomeomorph_eq_toDistribution`), and `Φ^*`
preserves `H^s` (`TemperedDistribution.MemSobolev.compCLM_of_norm_iteratedFDeriv_le_natCeil`).
Being `H^s` near a point is therefore an invariant notion of local regularity
(`Distribution.isInvariantLocalRegularity_isLocallySobolevAt`).

For the microlocal statement, a distribution `T` that is microlocally `H^s` at `(e x, η)` is
`u + (T - u)` for an element `u` of `H^s` and a distribution `T - u` that is microlocally smooth
at `(e x, η)` (`Distribution.IsMicrolocallySobolevAt.exists_memSobolev_isMicrolocallySmoothAt_sub`).
The pullback of `u` is `H^s` near `x` by the local statement, and the pullback of `T - u` is
microlocally smooth at the pulled back covector by the invariance of the wave front set
(`Distribution.IsMicrolocallySmoothAt.compCLMOfOpenPartialHomeomorph`).

## Main results

* `Distribution.IsLocallySobolevAt.compCLMOfOpenPartialHomeomorph`,
  `Distribution.isLocallySobolevAt_compCLMOfOpenPartialHomeomorph_iff`: invariance of local
  Sobolev regularity.
* `Distribution.isInvariantLocalRegularity_isLocallySobolevAt`: being `H^s` near a point is an
  invariant notion of local regularity (`Distribution.IsInvariantLocalRegularity`).
* `Distribution.sobolevSingularSupport_compCLMOfOpenPartialHomeomorph`: the `H^s` singular
  support of a pullback.
* `Distribution.IsMicrolocallySobolevAt.compCLMOfOpenPartialHomeomorph`,
  `Distribution.isMicrolocallySobolevAt_compCLMOfOpenPartialHomeomorph_iff`: invariance of
  microlocal Sobolev regularity.
* `Distribution.isInvariantMicrolocalRegularity_isMicrolocallySobolevAt`: being microlocally `H^s`
  is an invariant notion of microlocal regularity
  (`Distribution.IsInvariantMicrolocalRegularity`).
* `Distribution.sobolevWaveFrontSet_compCLMOfOpenPartialHomeomorph`: the `H^s` wave front set of a
  pullback.

## References

* M. E. Taylor, *Partial Differential Equations I*, 2nd ed., Springer, 2011, Chapter 4, §1
  (invariance of `H^s` under diffeomorphisms, and the local Sobolev spaces on manifolds).
* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, Springer, 1985,
  Appendix B.1 (`H^s_loc` is invariant under diffeomorphisms).
* L. Hörmander, *Lectures on Nonlinear Hyperbolic Differential Equations*, Springer, 1997,
  §11.1 (the `H^s` wave front set and its invariance under diffeomorphisms).
-/

public section

noncomputable section

open Set Filter Metric TopologicalSpace TestFunction
open scoped Distributions Topology ContDiff InnerProduct

namespace Distribution

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {e : OpenPartialHomeomorph E E} {U Ω : Opens E}
  {he : ContDiffOn ℝ (⊤ : ℕ∞) e e.source} {he' : ContDiffOn ℝ (⊤ : ℕ∞) e.symm e.target}
  {hU : (U : Set E) ⊆ e.source} {hUΩ : MapsTo e U Ω}

/-- **Local Sobolev regularity is invariant under changes of variables.** The pullback `e^* T` of
a distribution `T` along `e` is `H^s` near a point `x ∈ U` exactly when `T` is `H^s` near
`e x`. -/
theorem isLocallySobolevAt_compCLMOfOpenPartialHomeomorph_iff {s : ℝ} {T : 𝓓'(Ω, ℂ)} {x : E}
    (hx : x ∈ U) :
    (compCLMOfOpenPartialHomeomorph e he he' hU hUΩ T).IsLocallySobolevAt s x ↔
      T.IsLocallySobolevAt s (e x) := by
  rw [← isLocallyMemSobolevAt_two_iff, ← isLocallyMemSobolevAt_two_iff,
    isLocallyMemSobolevAt_compCLMOfOpenPartialHomeomorph_iff ENNReal.one_lt_two
      ENNReal.ofNat_ne_top hx]

/-- **Pulling back preserves local Sobolev regularity.** If `T` is `H^s` near `e x`, then its
pullback `e^* T` along `e` is `H^s` near `x`. -/
theorem IsLocallySobolevAt.compCLMOfOpenPartialHomeomorph {s : ℝ} {T : 𝓓'(Ω, ℂ)} {x : E}
    (hx : x ∈ U) (hT : T.IsLocallySobolevAt s (e x)) :
    (compCLMOfOpenPartialHomeomorph e he he' hU hUΩ T).IsLocallySobolevAt s x :=
  (isLocallySobolevAt_compCLMOfOpenPartialHomeomorph_iff hx).2 hT

/-- Being `H^s` near a point is an invariant notion of local regularity: it is open, linear,
preserved by smooth multiples and pullback along smooth changes of variables, and unchanged by
restriction to smaller open sets. -/
theorem isInvariantLocalRegularity_isLocallySobolevAt (s : ℝ) :
    IsInvariantLocalRegularity fun (Ω : Opens E) (T : 𝓓'(Ω, ℂ)) x ↦ T.IsLocallySobolevAt s x where
  isOpen_setOf _ T := isOpen_setOf_isLocallySobolevAt s T
  zero hx := isLocallySobolevAt_zero_iff.2 hx
  add hS hT := hS.add hT
  smul c hT := hT.smul c
  smulLeftCLM hg hT := hT.smulLeftCLM hg
  restrictCLM_iff h _ _ hx := isLocallySobolevAt_restrictCLM_iff h hx
  compCLMOfOpenPartialHomeomorph _ _ _ _ _ _ hx hT := hT.compCLMOfOpenPartialHomeomorph hx

/-- **The `H^s` singular support of a pullback.** Pulling back along `e` transforms the `H^s`
singular support by `e`: `singsupp_s (e^* T) = U ∩ e⁻¹ (singsupp_s T)`. -/
theorem sobolevSingularSupport_compCLMOfOpenPartialHomeomorph (s : ℝ) (T : 𝓓'(Ω, ℂ)) :
    sobolevSingularSupport s (compCLMOfOpenPartialHomeomorph e he he' hU hUΩ T) =
      (U : Set E) ∩ e ⁻¹' sobolevSingularSupport s T := by
  ext x
  simp only [mem_sobolevSingularSupport_iff, mem_inter_iff, mem_preimage, SetLike.mem_coe]
  constructor
  · rintro ⟨hx, h⟩
    exact ⟨hx, hUΩ hx, fun h' ↦ h ((isLocallySobolevAt_compCLMOfOpenPartialHomeomorph_iff hx).2 h')⟩
  · rintro ⟨hx, -, h⟩
    exact ⟨hx, fun h' ↦ h ((isLocallySobolevAt_compCLMOfOpenPartialHomeomorph_iff hx).1 h')⟩

/-! ### Microlocal Sobolev regularity -/

/-- **Microlocal Sobolev regularity under a change of variables.** If `T` is microlocally `H^s` at
`(e x, (De⁻¹(e x))ᵀ ξ)`, then its pullback `e^* T` along `e` is microlocally `H^s` at `(x, ξ)`. -/
theorem IsMicrolocallySobolevAt.compCLMOfOpenPartialHomeomorph {s : ℝ} {T : 𝓓'(Ω, ℂ)} {x ξ : E}
    (hx : x ∈ U) (h : T.IsMicrolocallySobolevAt s (e x) (((fderiv ℝ e.symm (e x))†) ξ)) :
    (compCLMOfOpenPartialHomeomorph e he he' hU hUΩ T).IsMicrolocallySobolevAt s x ξ := by
  -- `T = u + (T - u)` with `u ∈ H^s` and `T - u` microlocally smooth at the image covector. Local
  -- `H^s` regularity and microlocal smoothness are both invariant under pullback.
  obtain ⟨u, hu, hTu⟩ := h.exists_memSobolev_isMicrolocallySmoothAt_sub
  have h₁ : (Distribution.compCLMOfOpenPartialHomeomorph e he he' hU hUΩ
      (TemperedDistribution.toDistribution Ω u)).IsMicrolocallySobolevAt s x ξ :=
    ((hu.isLocallySobolevAt_toDistribution (hUΩ hx)).compCLMOfOpenPartialHomeomorph
      hx).isMicrolocallySobolevAt ξ
  have h₂ := (hTu.compCLMOfOpenPartialHomeomorph e he he' hU hUΩ hx).isMicrolocallySobolevAt s
  rw [map_sub] at h₂
  simpa using h₁.add h₂

/-- Being microlocally `H^s` is an invariant notion of microlocal regularity: it is open, linear,
conic, preserved by smooth multiples and pullback along smooth changes of variables, and unchanged
by restriction to smaller open sets. -/
theorem isInvariantMicrolocalRegularity_isMicrolocallySobolevAt (s : ℝ) :
    IsInvariantMicrolocalRegularity
      fun (Ω : Opens E) (T : 𝓓'(Ω, ℂ)) x ξ ↦ T.IsMicrolocallySobolevAt s x ξ where
  isOpen_setOf _ T := isOpen_setOf_isMicrolocallySobolevAt s T
  zero hx ξ := (isMicrolocallySmoothAt_zero hx ξ).isMicrolocallySobolevAt s
  add hS hT := hS.add hT
  smul c hT := hT.smul c
  smul_covector hr hT := (isMicrolocallySobolevAt_smul_iff hr).2 hT
  smulLeftCLM hg hT := hT.smulLeftCLM hg
  smulLeftCLM_iff hg hx := isMicrolocallySobolevAt_smulLeftCLM_iff hg hx
  restrictCLM_iff h _ _ hx _ := isMicrolocallySobolevAt_restrictCLM_iff h hx
  compCLMOfOpenPartialHomeomorph _ _ _ _ _ _ _ hx hT := hT.compCLMOfOpenPartialHomeomorph hx

/-- **Microlocal Sobolev regularity under a change of variables, pointwise.** For `x ∈ U`, the
pullback `e^* T` is microlocally `H^s` at `(x, ξ)` exactly when `T` is microlocally `H^s` at
`(e x, (De⁻¹(e x))ᵀ ξ)`. -/
theorem isMicrolocallySobolevAt_compCLMOfOpenPartialHomeomorph_iff {s : ℝ} {T : 𝓓'(Ω, ℂ)}
    {x ξ : E} (hx : x ∈ U) :
    (compCLMOfOpenPartialHomeomorph e he he' hU hUΩ T).IsMicrolocallySobolevAt s x ξ ↔
      T.IsMicrolocallySobolevAt s (e x) (((fderiv ℝ e.symm (e x))†) ξ) :=
  (isInvariantMicrolocalRegularity_isMicrolocallySobolevAt s).compCLMOfOpenPartialHomeomorph_iff hx

/-- **The `H^s` wave front set under a change of variables.** The `H^s` wave front set of the
pullback `e^* T` consists of the `(x, ξ)` with `x ∈ U` and `(e x, (De⁻¹(e x))ᵀ ξ) ∈ WF_s(T)`:
covectors pull back by the transpose of the derivative, for every real `s`. -/
theorem sobolevWaveFrontSet_compCLMOfOpenPartialHomeomorph (s : ℝ) (T : 𝓓'(Ω, ℂ)) :
    (compCLMOfOpenPartialHomeomorph e he he' hU hUΩ T).sobolevWaveFrontSet s =
      {p : E × E | p.1 ∈ U ∧
        (e p.1, ((fderiv ℝ e.symm (e p.1))†) p.2) ∈ T.sobolevWaveFrontSet s} := by
  ext ⟨x, ξ⟩
  have h := IsInvariantMicrolocalRegularity.setOf_compCLMOfOpenPartialHomeomorph
    (isInvariantMicrolocalRegularity_isMicrolocallySobolevAt s) (he := he) (he' := he') (hU := hU)
    (hUΩ := hUΩ) T
  simpa only [mem_sobolevWaveFrontSet_iff, mem_ofPred_eq] using Set.ext_iff.1 h (x, ξ)

end Distribution
