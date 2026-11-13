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
multiset of the absolute values `w r` of the roots `r` of `p` in `L` is the multiset of the norms
of the complex roots of `p`. Every symmetric function of these absolute values, such as the root
product `∏ max 1 ‖z‖` appearing in the Mahler measure of `p`, can therefore be computed in `L`.

## Main results

* `NumberField.InfinitePlace.map_aroots_eq_map_norm_aroots`: the absolute values at `w` of the
  roots of `p` in `L` are the norms of the complex roots of `p`, with multiplicity.
-/

public section

open Polynomial

namespace NumberField.InfinitePlace

variable {L : Type*} [Field L] [CharZero L]

/-- If `p` splits in the characteristic-zero field `L`, then at every infinite place `w` of `L` the
absolute values `w r` of the roots `r` of `p` in `L` are, with multiplicity, the norms of the
complex roots of `p`. -/
theorem map_aroots_eq_map_norm_aroots (w : InfinitePlace L) {p : ℚ[X]}
    (hs : (p.map (algebraMap ℚ L)).Splits) :
    (p.aroots L).map w = (p.aroots ℂ).map (‖·‖) := by
  have h : p.aroots ℂ = (p.aroots L).map w.embedding := by
    rw [aroots_def, aroots_def, ← hs.roots_map, Polynomial.map_map,
      Subsingleton.elim (w.embedding.comp (algebraMap ℚ L)) (algebraMap ℚ ℂ)]
  simp [h, norm_embedding_eq]

end NumberField.InfinitePlace
