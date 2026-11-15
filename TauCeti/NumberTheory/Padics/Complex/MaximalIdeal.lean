/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Padics.Complex
public import TauCeti.RingTheory.Valuation.IdempotentMaximalIdeal

/-!
# The maximal ideal of the integers of `ℂ_p`

The maximal ideal of `𝓞_ℂ_[p]` is not finitely generated. Algebraic closedness makes the
ideal idempotent, while `p` is a nonzero element of it. Thus the valuation ring of `ℂ_p`
satisfies the non-finite-generation condition used in almost mathematics.

## References

* P. Scholze, *Perfectoid spaces*, §4, Lemma 4.2 and its proof.
-/

public section

namespace TauCeti.PadicComplexInt

open IsLocalRing
open scoped NNReal

variable (p : ℕ) [Fact p.Prime]

/-- The maximal ideal of the ring of integers of `ℂ_p` is not finitely generated. -/
theorem not_fg_maximalIdeal : ¬ (maximalIdeal 𝓞_ℂ_[p]).FG := by
  have hp : (1 : ℝ≥0) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hpv : Valued.v (p : ℂ_[p]) < 1 := by
    rw [PadicComplex.valuation_p]
    exact (div_lt_one (zero_lt_one.trans hp)).mpr hp
  let x : 𝓞_ℂ_[p] := ⟨p, hpv.le⟩
  have hx : x ∈ maximalIdeal 𝓞_ℂ_[p] :=
    (Valuation.mem_maximalIdeal_iff (v := (PadicComplex.valued p).v)).mpr hpv
  have hne : maximalIdeal 𝓞_ℂ_[p] ≠ ⊥ := by
    intro h
    have hx0 : x = 0 := by simpa [h] using hx
    have : (p : ℂ_[p]) = 0 := congrArg Subtype.val hx0
    exact (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero) this
  exact (ValuationRing.isIdempotentElem_maximalIdeal_iff hne).mp
    (Valuation.isIdempotentElem_maximalIdeal_of_isAlgClosed (PadicComplex.valued p).v)

end TauCeti.PadicComplexInt
