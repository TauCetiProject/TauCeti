/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic

/-!
# Roots of rational polynomials at infinite places

Let `p` be a rational polynomial that splits in a characteristic-zero field `L`, such as a number
field. At every infinite place `w` of `L`, the embedding `w.embedding : L →+* ℂ` carries the roots
of `p` in `L` bijectively, with multiplicity, onto the complex roots of `p`. Consequently the
product of `max (w r) 1` over the roots `r` of `p` in `L` equals the product of `max 1 ‖z‖` over
the complex roots `z` of `p`, the root product appearing in the Mahler measure of `p`.

## Main results

* `NumberField.InfinitePlace.prod_aroots_max_one_eq`: the root-product comparison.
-/

public section

open Polynomial

namespace NumberField.InfinitePlace

variable {L : Type*} [Field L] [CharZero L]

/-- If `p` splits in the characteristic-zero field `L`, then at every infinite place `w` of `L` the
product of `max (w r) 1` over the roots `r` of `p` in `L` is the product of `max 1 ‖z‖` over the
complex roots `z` of `p`. -/
theorem prod_aroots_max_one_eq (w : InfinitePlace L) {p : ℚ[X]}
    (hs : (p.map (algebraMap ℚ L)).Splits) :
    ((p.aroots L).map fun r ↦ max (w r) 1).prod = ((p.aroots ℂ).map fun z ↦ max 1 ‖z‖).prod := by
  have h : p.aroots ℂ = (p.aroots L).map w.embedding := by
    rw [aroots_def, aroots_def, ← hs.roots_map, Polynomial.map_map,
      Subsingleton.elim (w.embedding.comp (algebraMap ℚ L)) (algebraMap ℚ ℂ)]
  simp [h, norm_embedding_eq, max_comm]

end NumberField.InfinitePlace
