/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Analytic.Order

/-!
# The analytic order of products and power-compositions

Three extensions of Mathlib's `analyticOrderAt` calculus: the order is additive over finite
products, composing with `q ↦ q ^ N` at `0` multiplies the order by `N`, and an analytic
function somewhere nonzero on a preconnected set has finitely many zeros in any compact
subset.

## Main declarations

* `TauCeti.analyticOrderAt_prod`: the order of `∏ i ∈ s, F i` is `∑ i ∈ s`, of the orders.
* `TauCeti.analyticOrderAt_comp_pow_zero`: the order of `q ↦ f (q ^ N)` at `0` is `N` times
  the order of `f` at `0`.
* `TauCeti.finite_setOfPred_mem_and_eq_zero_of_isCompact`: an analytic function somewhere
  nonzero on a preconnected set has finitely many zeros in any compact subset.

## References

* [Mathlib PR #39083](https://github.com/leanprover-community/mathlib4/pull/39083)
  (Chris Birkbeck) — the upstream draft this file ports onto the current Mathlib pin.
-/

public section

namespace TauCeti

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {f : 𝕜 → 𝕜} {z₀ : 𝕜}

/-- The order is additive when taking a finite product of analytic functions. -/
theorem analyticOrderAt_prod {ι : Type*} {s : Finset ι} {F : ι → 𝕜 → 𝕜}
    (hF : ∀ i ∈ s, AnalyticAt 𝕜 (F i) z₀) :
    analyticOrderAt (∏ i ∈ s, F i) z₀ = ∑ i ∈ s, analyticOrderAt (F i) z₀ := by
  induction s using Finset.cons_induction with
  | empty => simp [analyticOrderAt_eq_zero]
  | cons a s ha ih =>
    rw [Finset.prod_cons, Finset.sum_cons,
      analyticOrderAt_mul (hF a (Finset.mem_cons_self a s))
        (Finset.analyticAt_prod _ fun i hi ↦ hF i (Finset.mem_cons_of_mem hi)),
      ih fun i hi ↦ hF i (Finset.mem_cons_of_mem hi)]

/-- The analytic order of `q ↦ f (q ^ N)` at `0` is `N` times the analytic order of `f`
at `0`. -/
lemma analyticOrderAt_comp_pow_zero (hf : AnalyticAt 𝕜 f 0) {N : ℕ} (hN : 0 < N) :
    analyticOrderAt (fun q : 𝕜 ↦ f (q ^ N)) 0 = analyticOrderAt f 0 * N := by
  set g : 𝕜 → 𝕜 := fun q ↦ q ^ N with hg_def
  have hzero : g 0 = 0 := zero_pow hN.ne'
  have h_sub_eq : (fun x : 𝕜 ↦ g x - 0) = (id : 𝕜 → 𝕜) ^ N := funext fun x ↦ by simp [hg_def]
  -- The composite is definitionally the power lambda; `show … from rfl` records the
  -- identification once so the composition rule applies.
  rw [show (fun q : 𝕜 ↦ f (q ^ N)) = f ∘ g from rfl,
    AnalyticAt.analyticOrderAt_comp (hzero.symm ▸ hf) (analyticAt_id.pow N), hzero, h_sub_eq,
    analyticOrderAt_pow analyticAt_id, analyticOrderAt_id]
  simp


/-- **An analytic function somewhere nonzero has finitely many zeros in a compact.** If `f` is
analytic on a neighbourhood of a preconnected set `U` and nonzero at some point of `U`, then
every compact subset of `U` contains only finitely many zeros of `f`: the zeros are isolated, so
the complement of the zero set is codiscrete within `U`, and a compact meets the complement of a
codiscrete set in a finite set.

Generalized from the modular-form-specific finiteness of the AINTLIB `LeanModularForms`
valence-formula development (`ForMathlib/ValenceFormula/PVChain/ResidueSideInfra.lean`) to
arbitrary analytic functions on a preconnected set. -/
theorem finite_setOfPred_mem_and_eq_zero_of_isCompact {E : Type*}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] {g : 𝕜 → E} {U K : Set 𝕜} {x : 𝕜}
    (hg : AnalyticOnNhd 𝕜 g U) (hU : IsPreconnected U) (hx : x ∈ U) (hgx : g x ≠ 0)
    (hK : IsCompact K) (hKU : K ⊆ U) : {z ∈ K | g z = 0}.Finite := by
  have hcod : g ⁻¹' {0}ᶜ ∈ Filter.codiscreteWithin K :=
    Filter.codiscreteWithin_mono hKU
      (hg.preimage_zero_mem_codiscreteWithin hgx hx ⟨⟨x, hx⟩, hU⟩)
  exact (hK.finite_sdiff_of_mem_codiscreteWithin hcod).subset fun z hz =>
    ⟨hz.1, by simpa using hz.2⟩

end TauCeti

end
