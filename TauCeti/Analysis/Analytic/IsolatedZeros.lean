/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Analytic.Basic

-- Proof-only: the codiscreteness of the zero set comes from Mathlib's identity principle
-- `AnalyticOnNhd.eqOn_zero_or_eventually_ne_zero_of_preconnected`.
import Mathlib.Analysis.Analytic.IsolatedZeros

/-!
# The zero set of an analytic function

An analytic function that does not vanish identically has isolated zeros, and this file records
what that gives on a compact set: only finitely many zeros lie there. It is the fact any zero
count rests on, and it mentions neither the analytic order nor any particular field, so it lives
apart from both the order calculus of `TauCeti.Analysis.Analytic.Order` and the complex-specific
estimates of `TauCeti.Analysis.Complex.IsolatedZero`. The name follows Mathlib's own
`Mathlib.Analysis.Analytic.IsolatedZeros`, where the identity principle and the codiscreteness of
the zero set live.

## Main declarations

* `AnalyticOnNhd.finite_setOf_mem_and_eq_zero_of_isCompact`: an analytic function somewhere
  nonzero on a preconnected set has finitely many zeros in any compact subset of it.

## References

* The AINTLIB `LeanModularForms` valence-formula development
  (`ForMathlib/ValenceFormula/PVChain/ResidueSideInfra.lean`), whose modular-form-specific
  finiteness this generalises.
-/

public section

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

/-- **An analytic function somewhere nonzero has finitely many zeros in a compact.** If `g` is
analytic on a neighbourhood of a preconnected set `U` and nonzero at some point of `U`, then
every compact subset of `U` contains only finitely many zeros of `g`. -/
theorem AnalyticOnNhd.finite_setOf_mem_and_eq_zero_of_isCompact {E : Type*}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] {g : 𝕜 → E} {U K : Set 𝕜} {x : 𝕜}
    (hg : AnalyticOnNhd 𝕜 g U) (hU : IsPreconnected U) (hx : x ∈ U) (hgx : g x ≠ 0)
    (hK : IsCompact K) (hKU : K ⊆ U) : {z ∈ K | g z = 0}.Finite := by
  have hcod : ∀ᶠ z in Filter.codiscreteWithin K, g z ≠ 0 :=
    ((hg.eqOn_zero_or_eventually_ne_zero_of_preconnected hU).resolve_left fun h => hgx (h hx))
      |>.filter_mono (Filter.codiscreteWithin_mono hKU)
  exact (hK.finite_sdiff_of_mem_codiscreteWithin hcod).subset fun z hz =>
    ⟨hz.1, by simpa using hz.2⟩

end
