/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Valuation.ValuationSubring

/-!
# Nonunits and domination for valuation subrings

A valuation subring `A` of a field is determined by its nonunits, and a valuation subring
dominating `A` (containing it, with every nonunit of `A` a nonunit) is `A` itself. Pulling a
valuation subring back along a field homomorphism `f` detects nonunits through `f`, so a
valuation subring dominates its pullback.

## Main results

* `ValuationSubring.mem_nonunits_comap`: nonunits of a pulled-back valuation subring.
* `ValuationSubring.eq_of_le_of_nonunits_le`: a valuation subring equals any valuation subring
  dominating it.
* `ValuationSubring.isLocalHom_restrict`: a valuation subring dominates its pullback.

## References

* [Stacks Project, Tag 00IA](https://stacks.math.columbia.edu/tag/00IA) (valuation rings
  dominating a local ring).
-/

public section

open IsLocalRing

namespace ValuationSubring

variable {K L : Type*} [Field K] [Field L]

/-- An element lies in the nonunits of a pulled-back valuation subring exactly when its image
lies in the nonunits of the original one. -/
@[simp]
theorem mem_nonunits_comap {A : ValuationSubring L} {f : K →+* L} {x : K} :
    x ∈ (A.comap f).nonunits ↔ f x ∈ A.nonunits := by
  simp [mem_nonunits_iff_or, map_inv₀]

/-- A valuation subring is determined by any valuation subring dominating it: if `A ≤ B` and
every nonunit of `A` is a nonunit of `B`, then `A = B`. -/
theorem eq_of_le_of_nonunits_le {A B : ValuationSubring K} (h : A ≤ B)
    (h' : A.nonunits ≤ B.nonunits) : A = B :=
  nonunits_injective (le_antisymm h' (nonunits_le_nonunits.mpr h))

/-- The inclusion of a pulled-back valuation subring `A.comap f` into `A` is a local
homomorphism: a valuation subring dominates its pullback. -/
theorem isLocalHom_restrict (A : ValuationSubring L) (f : K →+* L) {B : ValuationSubring K}
    (hB : B = A.comap f) : IsLocalHom (f.restrict B A fun _ hx ↦ mem_comap.mp (hB ▸ hx)) := by
  refine ⟨fun ⟨x, hx⟩ ha ↦ ?_⟩
  subst hB
  rw [← notMem_maximalIdeal, ← coe_mem_nonunits_iff] at ha ⊢
  exact mem_nonunits_comap.not.mpr ha

end ValuationSubring
