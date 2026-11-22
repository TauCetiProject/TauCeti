/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Padics.Complex

import TauCeti.NumberTheory.Padics.Complex.Basic

/-!
# The maximal ideal of the integers of `ℂ_p`

The maximal ideal of `𝓞_ℂ_[p]` is not finitely generated. This is the case `K = ℂ_[p]` of
`TauCeti.not_fg_maximalIdeal_integer`, since `ℂ_[p]` is densely normed. That theorem concerns
the closed unit ball of the norm, while `𝓞_ℂ_[p]` is cut out by the valuation of `ℂ_[p]`; the
two are the same subring. Thus the valuation ring of `ℂ_p` satisfies the non-finite-generation
condition used in almost mathematics.

## References

* P. Scholze, *Perfectoid spaces*, §4, Lemma 4.2 and its proof.
-/

public section

namespace TauCeti.PadicComplexInt

open IsLocalRing

variable (p : ℕ) [Fact p.Prime]

/-- The maximal ideal of the ring of integers of `ℂ_p` is not finitely generated. -/
theorem not_fg_maximalIdeal : ¬ (maximalIdeal 𝓞_ℂ_[p]).FG := by
  intro hfg
  refine TauCeti.not_fg_maximalIdeal_integer (K := ℂ_[p]) ?_
  -- Transport `hfg` along the identity of `𝓞_ℂ_[p]` with the closed unit ball of the norm.
  have hmem (x : ℂ_[p]) : x ∈ 𝓞_ℂ_[p] ↔ ‖x‖ ≤ 1 := by
    rw [PadicComplexInt, Valuation.mem_valuationSubring_iff, ← NNReal.coe_le_coe,
      PadicComplex.valuation_coe, NNReal.coe_one]
  let f : 𝓞_ℂ_[p] →+* _ := 𝓞_ℂ_[p].subtype.codRestrict _
    fun x ↦ Valued.integer.mem_iff.2 ((hmem x).1 x.property)
  have hf : Function.Surjective f := fun y ↦
    ⟨⟨y, (hmem y).2 (Valued.integer.mem_iff.1 y.property)⟩, rfl⟩
  exact map_maximalIdeal_of_surjective f hf ▸ hfg.map f

end TauCeti.PadicComplexInt
