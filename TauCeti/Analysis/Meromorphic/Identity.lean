/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Meromorphic.NormalForm
import TauCeti.Analysis.Complex.HalfPlaneIdentity

/-!
# Identity principles for meromorphic functions

Equality of punctured germs propagates through a preconnected set of meromorphicity.
For functions in meromorphic normal form this also determines the values, including the
canonical value zero at poles. For arbitrary meromorphic representatives it does not.

The propagation uses Mathlib's
`MeromorphicOn.meromorphicOrderAt_eq_top_of_isPreconnected`, applied to the difference.
In the complex plane, two functions meromorphic at `a : ℂ` that agree on the `Re z > a.re` side of
a neighbourhood of `a` also agree on a punctured neighbourhood of `a`
(`MeromorphicAt.eventuallyEq_nhdsNE_of_eventuallyEq_re_gt`).
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

/-- **Punctured-neighbourhood identity theorem for meromorphic functions on a half-plane
boundary.** Two functions meromorphic at `a : ℂ` that agree on the `Re z > a.re` side of a
neighbourhood of `a` agree on a punctured neighbourhood of `a`. -/
theorem MeromorphicAt.eventuallyEq_nhdsNE_of_eventuallyEq_re_gt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    {f g : ℂ → E} {a : ℂ} (hf : MeromorphicAt f a) (hg : MeromorphicAt g a)
    (hfg : f =ᶠ[𝓝[{z : ℂ | a.re < z.re}] a] g) :
    f =ᶠ[𝓝[≠] a] g :=
  TauCeti.eventuallyEq_nhdsNE_of_differentiableAt_of_eventuallyEq_re_gt
    (hf.eventually_analyticAt.mono fun _ h ↦ h.differentiableAt)
    (hg.eventually_analyticAt.mono fun _ h ↦ h.differentiableAt) hfg
