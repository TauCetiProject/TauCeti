/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.Setoid.Basic
public import Mathlib.SetTheory.Cardinal.Basic
import TauCeti.Data.Setoid.Basic

/-!
# Cardinality of the classes met by a set

For a setoid `s` on `α` and a set `K ⊆ α`, `Setoid.comapValQuotientEquiv` puts the quotient of `K`
by the restricted setoid `s.comap (↑)` in bijection with the image `Quotient.mk s '' K` of `K` in
`Quotient s`. Consequently the two have the same cardinality, and the number of restricted classes
is monotone in `K`.

## Main results

* `Setoid.mk_quotient_comap_val_eq_mk_image`: the restriction of `s` to `K` has as many classes as
  the image `Quotient.mk s '' K`.
* `Setoid.mk_quotient_comap_val_le_of_subset`: a subset meets at most as many classes of `s` as a
  superset.
-/

public section

open Cardinal

namespace Setoid

/-- The restriction of a setoid `s` to a set `K` has as many classes as the image of `K` in
`Quotient s`. -/
theorem mk_quotient_comap_val_eq_mk_image {α : Type*} (s : Setoid α) (K : Set α) :
    #(Quotient (s.comap ((↑) : K → α))) = #(Quotient.mk s '' K) :=
  Cardinal.mk_congr (comapValQuotientEquiv s K)

/-- If `K ⊆ K'`, then the restriction of `s` to `K` has at most as many classes as its restriction
to `K'`. -/
theorem mk_quotient_comap_val_le_of_subset {α : Type*} {s : Setoid α} {K K' : Set α}
    (h : K ⊆ K') :
    #(Quotient (s.comap ((↑) : K → α))) ≤ #(Quotient (s.comap ((↑) : K' → α))) := by
  rw [mk_quotient_comap_val_eq_mk_image, mk_quotient_comap_val_eq_mk_image]
  exact Cardinal.mk_le_mk_of_subset (Set.image_mono h)

end Setoid
