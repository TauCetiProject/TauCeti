/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Meromorphic.NormalForm

/-!
# Identity principles for meromorphic functions

Equality of punctured germs propagates through a preconnected set of meromorphicity.
For functions in meromorphic normal form this also determines the values, including the
canonical value zero at poles. For arbitrary meromorphic representatives it does not.

The propagation uses Mathlib's
`MeromorphicOn.meromorphicOrderAt_eq_top_of_isPreconnected`, applied to the difference.
-/

public section

open Filter Set
open scoped Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {f g : 𝕜 → E} {U : Set 𝕜} {x y : 𝕜}

/-- Equality of meromorphic punctured germs propagates over a preconnected set. -/
theorem MeromorphicOn.eventuallyEq_of_isPreconnected
    (hf : MeromorphicOn f U) (hg : MeromorphicOn g U) (hU : IsPreconnected U)
    (hx : x ∈ U) (hy : y ∈ U) (hfg : f =ᶠ[𝓝[≠] x] g) :
    f =ᶠ[𝓝[≠] y] g := by
  rw [eventuallyEq_iff_sub] at hfg ⊢
  exact meromorphicOrderAt_eq_top_iff.mp <|
    (hf.sub hg).meromorphicOrderAt_eq_top_of_isPreconnected hU hx hy
      (meromorphicOrderAt_eq_top_iff.mpr hfg)

/-- For meromorphic normal forms, one punctured germ determines all values on a
preconnected set. -/
theorem MeromorphicNFOn.eqOn_of_isPreconnected
    (hf : MeromorphicNFOn f U) (hg : MeromorphicNFOn g U) (hU : IsPreconnected U)
    (hx : x ∈ U) (hfg : f =ᶠ[𝓝[≠] x] g) : EqOn f g U := by
  intro y hy
  exact ((hf hy).eventuallyEq_nhdsNE_iff_eventuallyEq_nhds (hg hy) |>.mp
    (hf.meromorphicOn.eventuallyEq_of_isPreconnected hg.meromorphicOn hU hx hy hfg)).eq_of_nhds
