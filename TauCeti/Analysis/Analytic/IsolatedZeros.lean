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
what that gives near a point and on a compact set: it has no zeros in a punctured neighbourhood of
any point, and only finitely many zeros lie in a compact set. It is the fact any zero
count rests on, and it mentions neither the analytic order nor any particular field, so it lives
apart from both the order calculus of `TauCeti.Analysis.Analytic.Order` and the complex-specific
estimates of `TauCeti.Analysis.Complex.IsolatedZero`. The name follows Mathlib's own
`Mathlib.Analysis.Analytic.IsolatedZeros`, where the identity principle and the codiscreteness of
the zero set live.

## Main declarations

* `AnalyticOnNhd.eventually_ne_zero_nhdsNE_of_preconnected`: an analytic function somewhere
  nonzero on a preconnected set has no zeros in a punctured neighbourhood of any point of it.
* `AnalyticOnNhd.finite_setOf_mem_and_eq_zero_of_isCompact`: an analytic function somewhere
  nonzero on a preconnected set has finitely many zeros in any compact subset of it.
* `AnalyticOnNhd.tendsto_norm_cofinite_atTop_of_injective_of_eq_zero`: over a proper preconnected
  field, the zeros of an analytic function on the whole field that is not identically zero,
  listed by an injective family, escape to infinity along the cofinite filter.

## References

* The AINTLIB `LeanModularForms` valence-formula development
  (`ForMathlib/ValenceFormula/PVChain/ResidueSideInfra.lean`), whose modular-form-specific
  finiteness this generalises.
-/

public section

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

open scoped Topology in
/-- **An analytic function somewhere nonzero has isolated zeros.** If `g` is analytic on a
neighbourhood of a preconnected set `U` and nonzero at some point of `U`, then near every point `z`
of `U`, `g` vanishes nowhere except possibly at `z` itself. -/
theorem AnalyticOnNhd.eventually_ne_zero_nhdsNE_of_preconnected {E : Type*}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] {g : 𝕜 → E} {U : Set 𝕜} {x z : 𝕜}
    (hg : AnalyticOnNhd 𝕜 g U) (hU : IsPreconnected U) (hx : x ∈ U) (hgx : g x ≠ 0)
    (hz : z ∈ U) : ∀ᶠ u in 𝓝[≠] z, g u ≠ 0 :=
  (hg z hz).eventually_eq_zero_or_eventually_ne_zero.resolve_left fun h =>
    hgx (hg.eqOn_zero_of_preconnected_of_eventuallyEq_zero hU hz h hx)

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

/-- **The zeros of a nonzero entire function escape to infinity.** If `g` is analytic on the whole
of a proper preconnected field `𝕜` (such as `ℝ` or `ℂ`) and nonzero somewhere, then any injective
family `α` of zeros of `g` has `‖α i‖ → ∞` along the cofinite filter. -/
theorem AnalyticOnNhd.tendsto_norm_cofinite_atTop_of_injective_of_eq_zero [ProperSpace 𝕜]
    [PreconnectedSpace 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {g : 𝕜 → E}
    {x : 𝕜} (hg : AnalyticOnNhd 𝕜 g Set.univ) (hgx : g x ≠ 0) {ι : Type*} {α : ι → 𝕜}
    (hinj : Function.Injective α) (hα : ∀ i, g (α i) = 0) :
    Filter.Tendsto (fun i ↦ ‖α i‖) Filter.cofinite Filter.atTop := by
  refine Filter.tendsto_atTop.2 fun R ↦ Filter.eventually_cofinite.2 ?_
  have hfin := hg.finite_setOf_mem_and_eq_zero_of_isCompact isPreconnected_univ (Set.mem_univ x)
    hgx (isCompact_closedBall 0 R) (Set.subset_univ _)
  exact (hfin.preimage hinj.injOn).subset fun i hi ↦
    ⟨mem_closedBall_zero_iff.2 (not_le.1 hi).le, hα i⟩

end
