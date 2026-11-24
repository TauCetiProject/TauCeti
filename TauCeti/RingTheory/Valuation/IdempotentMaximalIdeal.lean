/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.RingTheory.Valuation.ValuationRing

import Mathlib.RingTheory.Nakayama

/-!
# Idempotent maximal ideals of valuation rings

The maximal ideal of a valuation ring is idempotent if it is not finitely generated.
Conversely, a nonzero idempotent maximal ideal cannot be finitely generated. This is the
algebraic input for almost mathematics over nondiscrete valuation rings; no rank or
completeness assumption is needed.

Both results are stated for a nontrivial commutative ring in which any two elements are comparable
by divisibility (a `PreValuationRing`); valuation domains are the main example. They need no domain
assumption, so they also cover such rings with zero divisors.

## References

* O. Gabber and L. Ramero, *Almost ring theory*, §2.1, Example 2.1.2(i).
* P. Scholze, *Perfectoid spaces*, §4, Lemma 4.2 and its proof.
-/

public section

open IsLocalRing

namespace TauCeti.ValuationRing

variable {V : Type*} [CommRing V] [Nontrivial V] [PreValuationRing V]

/-- The maximal ideal of a nontrivial commutative ring in which any two elements are comparable by
divisibility, such as a valuation ring, is idempotent when it is not finitely generated. -/
theorem isIdempotentElem_maximalIdeal_of_not_fg (hfg : ¬ (maximalIdeal V).FG) :
    IsIdempotentElem (maximalIdeal V) := by
  apply le_antisymm Ideal.mul_le_left
  intro x hx
  -- Some `y ∈ m` is not a multiple of `x`, since otherwise `m = (x)` would be finitely generated.
  obtain ⟨y, hy, hxy⟩ : ∃ y ∈ maximalIdeal V, ¬ x ∣ y := by
    by_contra! h
    have heq : Ideal.span {x} = maximalIdeal V := le_antisymm
      ((Ideal.span_singleton_le_iff_mem _).mpr hx) fun y hy ↦ Ideal.mem_span_singleton.mpr (h y hy)
    exact hfg (heq ▸ Submodule.fg_span_singleton x)
  obtain ⟨z, rfl⟩ := (_root_.ValuationRing.dvd_total x y).resolve_left hxy
  -- The cofactor `z` is not a unit, since otherwise `x = y * z` would divide `y`.
  have hz : z ∈ maximalIdeal V := by
    by_contra hz
    exact hxy ((notMem_maximalIdeal.mp hz).mul_right_dvd.mpr dvd_rfl)
  exact Ideal.mul_mem_mul hy hz

/-- A nonzero maximal ideal of a nontrivial commutative ring in which any two elements are
comparable by divisibility, such as a valuation ring, is idempotent exactly when it is not finitely
generated. The nonzero assumption excludes the maximal ideal of a field. -/
theorem isIdempotentElem_maximalIdeal_iff (hne : maximalIdeal V ≠ ⊥) :
    IsIdempotentElem (maximalIdeal V) ↔ ¬ (maximalIdeal V).FG := by
  refine ⟨fun hi hfg ↦ hne ?_, isIdempotentElem_maximalIdeal_of_not_fg⟩
  -- Nakayama's lemma: a finitely generated `m` with `m = m • m` vanishes.
  exact Submodule.eq_bot_of_le_smul_of_le_jacobson _ _ hfg (by rw [smul_eq_mul, hi.eq])
    (ringJacobson_eq_maximalIdeal V).ge

end TauCeti.ValuationRing
