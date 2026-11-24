/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.LocalRegularity
public import TauCeti.Analysis.FunctionalSpaces.BesovSpace.Local
import TauCeti.Analysis.Distribution.ChangeOfVariables.Tempered
import TauCeti.Analysis.FunctionalSpaces.BesovSpace.ChangeOfVariables

/-!
# Local Besov regularity under smooth changes of variables

Let `e` be a smooth open partial homeomorphism of a finite-dimensional real inner product space
`E` with smooth inverse, `U` an open subset of its source and `Ω` an open set containing `e '' U`.
A complex distribution `T` on `Ω` pulls back to the distribution `e^* T` on `U`
(`Distribution.compCLMOfOpenPartialHomeomorph`). This file proves that being `B^s_{p,q}` near a
point (`Distribution.IsLocallyMemBesovAt`) is invariant under this pullback, for every real `s` and
all `1 ≤ p, q ≤ ∞`:

`e^* T` is `B^s_{p,q}` near `x` if and only if `T` is `B^s_{p,q}` near `e x`

(`Distribution.isLocallyMemBesovAt_compCLMOfOpenPartialHomeomorph_iff`). For `p = q = ∞` this is
the invariance of the local Hölder–Zygmund spaces `𝒞^s_loc`, including negative orders. Since chart
transitions are such maps `e`, this is the chart-change invariance needed to define local Besov and
Zygmund regularity on manifolds chart by chart.

## The argument

This is the argument for the Sobolev scale
(`Distribution.IsLocallySobolevAt.compCLMOfOpenPartialHomeomorph`), with the Besov pullback
theorem in place of the Sobolev one. Pullback along a bijection `Φ` of `E` such that `Φ` and `Φ⁻¹`
are smooth with bounded derivatives of every positive order preserves `B^s_{p,q}`
(`TemperedDistribution.MemBesov.compCLM`). Near `x`, the pullback `e^* T` is the tempered pullback
`Φ^* (χ T)` of a cut-off distribution along such a bijection, with `χ` supported in any prescribed
neighbourhood of `e x`
(`Distribution.exists_restrictCLM_compCLMOfOpenPartialHomeomorph_eq_toDistribution`). If `T` is
`B^s_{p,q}` near `e x`, then `χ T ∈ B^s_{p,q}` for such `χ`, so `Φ^* (χ T) ∈ B^s_{p,q}`, and
`e^* T` is `B^s_{p,q}` near `x`. Being `B^s_{p,q}` near a point is therefore an invariant notion of
local regularity (`Distribution.isInvariantLocalRegularity_isLocallyMemBesovAt`), and the converse
follows as for any such notion, by pulling back along `e⁻¹`.

## Main results

* `Distribution.IsLocallyMemBesovAt.compCLMOfOpenPartialHomeomorph`,
  `Distribution.isLocallyMemBesovAt_compCLMOfOpenPartialHomeomorph_iff`: invariance of local Besov
  regularity under smooth changes of variables.
* `Distribution.isLocalRegularity_isLocallyMemBesovAt`,
  `Distribution.isInvariantLocalRegularity_isLocallyMemBesovAt`: being `B^s_{p,q}` near a point
  is a notion of local regularity (`Distribution.IsLocalRegularity`), invariant for `1 ≤ q`
  (`Distribution.IsInvariantLocalRegularity`).

## References

* H. Triebel, *Theory of Function Spaces*, Birkhäuser, 1983, §2.10.2 (diffeomorphisms of `ℝⁿ`
  preserve the Besov spaces) and §3.2.2 (Besov spaces on manifolds, defined chart by chart).
-/

public section

noncomputable section

open Set TopologicalSpace
open scoped Distributions ContDiff ENNReal

namespace Distribution

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {e : OpenPartialHomeomorph E E} {U Ω : Opens E}
  {he : ContDiffOn ℝ (⊤ : ℕ∞) e e.source} {he' : ContDiffOn ℝ (⊤ : ℕ∞) e.symm e.target}
  {hU : (U : Set E) ⊆ e.source} {hUΩ : MapsTo e U Ω}
  {φ : ContDiffBump (0 : E)} {p q : ℝ≥0∞} [Fact (1 ≤ p)]

variable (φ p q) in
/-- Being `B^s_{p,q}` near a point is a notion of local regularity: it is open and linear. -/
theorem isLocalRegularity_isLocallyMemBesovAt (s : ℝ) :
    IsLocalRegularity fun (Ω : Opens E) (T : 𝓓'(Ω, ℂ)) x ↦ T.IsLocallyMemBesovAt φ s p q x where
  isOpen_setOf _ T := isOpen_setOf_isLocallyMemBesovAt φ s p q T
  zero hx := isLocallyMemBesovAt_zero_iff.2 hx
  add hS hT := hS.add hT
  smul c hT := hT.smul c

variable [Fact (1 ≤ q)]

/-- **Pulling back preserves local Besov regularity.** If `T` is `B^s_{p,q}` near `e x`, then its
pullback `e^* T` along `e` is `B^s_{p,q}` near `x`. -/
theorem IsLocallyMemBesovAt.compCLMOfOpenPartialHomeomorph {s : ℝ} {T : 𝓓'(Ω, ℂ)} {x : E}
    (hx : x ∈ U) (hT : T.IsLocallyMemBesovAt φ s p q (e x)) :
    (compCLMOfOpenPartialHomeomorph e he he' hU hUΩ T).IsLocallyMemBesovAt φ s p q x := by
  -- `ψ T ∈ B^s_{p,q}` for every test function `ψ` supported in a neighbourhood `W` of `e x`.
  obtain ⟨W, hW, -, hWT⟩ := isLocallyMemBesovAt_iff.1 hT
  obtain ⟨Φ, hΦ, hΨ, N, hNU, χ, hΦb, hΨb, hxN, hχW, hT⟩ :=
    exists_restrictCLM_compCLMOfOpenPartialHomeomorph_eq_toDistribution (he := he) (he' := he')
      (hUΩ := hUΩ) hx hW T
  rw [← isLocallyMemBesovAt_restrictCLM_iff hNU hxN, hT]
  exact ((hWT χ hχW).compCLM hΦ hΨ (fun n hn _ ↦ hΦb n hn) (fun n hn _ ↦ hΨb n hn))
    |>.isLocallyMemBesovAt_toDistribution hxN

variable (φ p q) in
/-- For `1 ≤ q`, being `B^s_{p,q}` near a point is an invariant notion of local regularity: it is
open, linear, preserved by smooth multiples and pullback along smooth changes of variables, and
unchanged by restriction to smaller open sets. -/
theorem isInvariantLocalRegularity_isLocallyMemBesovAt (s : ℝ) :
    IsInvariantLocalRegularity
      fun (Ω : Opens E) (T : 𝓓'(Ω, ℂ)) x ↦ T.IsLocallyMemBesovAt φ s p q x where
  toIsLocalRegularity := isLocalRegularity_isLocallyMemBesovAt φ p q s
  smulLeftCLM hg hT := hT.smulLeftCLM hg
  restrictCLM_iff h _ _ hx := isLocallyMemBesovAt_restrictCLM_iff h hx
  compCLMOfOpenPartialHomeomorph _ _ _ _ _ _ hx hT := hT.compCLMOfOpenPartialHomeomorph hx

/-- **Local Besov regularity is invariant under changes of variables.** The pullback `e^* T` of
a distribution `T` along `e` is `B^s_{p,q}` near a point `x ∈ U` exactly when `T` is
`B^s_{p,q}` near `e x`. -/
theorem isLocallyMemBesovAt_compCLMOfOpenPartialHomeomorph_iff {s : ℝ} {T : 𝓓'(Ω, ℂ)} {x : E}
    (hx : x ∈ U) :
    (compCLMOfOpenPartialHomeomorph e he he' hU hUΩ T).IsLocallyMemBesovAt φ s p q x ↔
      T.IsLocallyMemBesovAt φ s p q (e x) :=
  (isInvariantLocalRegularity_isLocallyMemBesovAt φ p q s).compCLMOfOpenPartialHomeomorph_iff hx

end Distribution
