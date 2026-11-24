/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.LocalRegularity
public import TauCeti.Analysis.Distribution.WaveFrontSet.Sobolev.Tempered
import TauCeti.Analysis.Distribution.ChangeOfVariables.Tempered
import TauCeti.Analysis.Sobolev.BesselPotential.ChangeOfVariables

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

Pullback along a bijection `Φ` of `E` such that `Φ` and `Φ⁻¹` are smooth with bounded
derivatives of every positive order preserves the Bessel-potential space `H^s`
(`TemperedDistribution.MemSobolev.compCLM_of_norm_iteratedFDeriv_le_natCeil` at `p = 2`). Near
`x`, the pullback `e^* T` is the tempered pullback `Φ^* (χ T)` of a cut-off distribution along
such a bijection, with `χ` supported in any prescribed neighbourhood of `e x`
(`Distribution.exists_restrictCLM_compCLMOfOpenPartialHomeomorph_eq_toDistribution`). If `T` is
`H^s` near `e x`, then `χ T ∈ H^s` for such `χ`, so `Φ^* (χ T) ∈ H^s`, and `e^* T` is `H^s` near
`x`. Being `H^s` near a point is therefore an invariant notion of local regularity
(`Distribution.isInvariantLocalRegularity_isLocallySobolevAt`), and the converse follows as for
any such notion, by pulling back along `e⁻¹`.

## Main results

* `Distribution.IsLocallySobolevAt.compCLMOfOpenPartialHomeomorph`,
  `Distribution.isLocallySobolevAt_compCLMOfOpenPartialHomeomorph_iff`: invariance of local
  Sobolev regularity.
* `Distribution.isInvariantLocalRegularity_isLocallySobolevAt`: being `H^s` near a point is an
  invariant notion of local regularity (`Distribution.IsInvariantLocalRegularity`).
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

open Set TopologicalSpace
open scoped Distributions ContDiff

namespace Distribution

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {e : OpenPartialHomeomorph E E} {U Ω : Opens E}
  {he : ContDiffOn ℝ (⊤ : ℕ∞) e e.source} {he' : ContDiffOn ℝ (⊤ : ℕ∞) e.symm e.target}
  {hU : (U : Set E) ⊆ e.source} {hUΩ : MapsTo e U Ω}

/-- **Pulling back preserves local Sobolev regularity.** If `T` is `H^s` near `e x`, then its
pullback `e^* T` along `e` is `H^s` near `x`. -/
theorem IsLocallySobolevAt.compCLMOfOpenPartialHomeomorph {s : ℝ} {T : 𝓓'(Ω, ℂ)} {x : E}
    (hx : x ∈ U) (hT : T.IsLocallySobolevAt s (e x)) :
    (compCLMOfOpenPartialHomeomorph e he he' hU hUΩ T).IsLocallySobolevAt s x := by
  -- `φ T ∈ H^s` for every test function `φ` supported in a neighbourhood `W` of `e x`.
  obtain ⟨W, hW, hWT⟩ := hT.exists_nhds_forall_memSobolev_cutoffTempered
  obtain ⟨Φ, hΦ, hΨ, N, hNU, χ, hΦb, hΨb, hxN, hχW, hT⟩ :=
    exists_restrictCLM_compCLMOfOpenPartialHomeomorph_eq_toDistribution (he := he) (he' := he')
      (hUΩ := hUΩ) hx hW T
  rw [← isLocallySobolevAt_restrictCLM_iff hNU hxN, hT]
  exact ((hWT χ hχW).compCLM_of_norm_iteratedFDeriv_le_natCeil ENNReal.one_lt_two
    ENNReal.ofNat_ne_top hΦ hΨ (fun n hn _ ↦ hΦb n hn) (fun n hn _ ↦ hΨb n hn))
    |>.isLocallySobolevAt_toDistribution hxN

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

/-- **Local Sobolev regularity is invariant under changes of variables.** The pullback `e^* T` of
a distribution `T` along `e` is `H^s` near a point `x ∈ U` exactly when `T` is `H^s` near
`e x`. -/
theorem isLocallySobolevAt_compCLMOfOpenPartialHomeomorph_iff {s : ℝ} {T : 𝓓'(Ω, ℂ)} {x : E}
    (hx : x ∈ U) :
    (compCLMOfOpenPartialHomeomorph e he he' hU hUΩ T).IsLocallySobolevAt s x ↔
      T.IsLocallySobolevAt s (e x) :=
  (isInvariantLocalRegularity_isLocallySobolevAt s).compCLMOfOpenPartialHomeomorph_iff hx

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
