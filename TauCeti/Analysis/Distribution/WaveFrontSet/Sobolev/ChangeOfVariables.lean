/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.ChangeOfVariables
public import TauCeti.Analysis.Distribution.WaveFrontSet.Sobolev.Tempered
import TauCeti.Analysis.Sobolev.BesselPotential.Local

/-!
# Local Sobolev regularity under smooth changes of variables

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

## The argument

This is the case `p = 2` of the invariance of local `H^{s,p}` regularity
(`Distribution.isLocallyMemSobolevAt_compCLMOfOpenPartialHomeomorph_iff`), since being `H^s` near
a point is being `H^{s,2}` near it (`Distribution.isLocallyMemSobolevAt_two_iff`). Near `x`, `e`
agrees with a bijection `Φ` of `E` whose derivatives are bounded, on a neighbourhood of `x` the
pullback `e^* T` is the tempered pullback `Φ^* (χ T)` of a cut-off `χ T`
(`Distribution.restrictCLM_compCLMOfOpenPartialHomeomorph_eq_toDistribution`), and `Φ^*`
preserves `H^s` (`TemperedDistribution.MemSobolev.compCLM_of_norm_iteratedFDeriv_le_natCeil`).

## Main results

* `Distribution.IsLocallySobolevAt.compCLMOfOpenPartialHomeomorph`,
  `Distribution.isLocallySobolevAt_compCLMOfOpenPartialHomeomorph_iff`: invariance of local
  Sobolev regularity.
* `Distribution.sobolevSingularSupport_compCLMOfOpenPartialHomeomorph`: the `H^s` singular
  support of a pullback.

## References

* M. E. Taylor, *Partial Differential Equations I*, 2nd ed., Springer, 2011, Chapter 4, §1
  (invariance of `H^s` under diffeomorphisms, and the local Sobolev spaces on manifolds).
* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, Springer, 1985,
  Appendix B.1 (`H^s_loc` is invariant under diffeomorphisms).
-/

public section

noncomputable section

open Set Filter Metric TopologicalSpace TestFunction
open scoped Distributions Topology ContDiff

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

end Distribution
