/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.List.Basic
public import Mathlib.Algebra.Star.Basic
import Mathlib.Algebra.BigOperators.Group.List.Lemmas

/-!
# Adjoints of list products

In a monoid with a product-reversing involution (`StarMul`), taking `star` of a list product gives
the product of the adjoints in reversed order. Mathlib's `Mathlib.Algebra.Star.BigOperators` covers
commutative `Finset` products; this file supplies the ordered `List.prod` counterpart.

## Main results

* `TauCeti.star_list_prod`: `star l.prod = (l.map star).reverse.prod`.
-/

public section

namespace TauCeti

/-- In a star monoid, the adjoint of a list product is the product of the adjoints in reversed
order. -/
theorem star_list_prod {M : Type*} [Monoid M] [StarMul M] (l : List M) :
    star l.prod = (l.map star).reverse.prod :=
  unop_map_list_prod (starMulEquiv : M ≃* Mᵐᵒᵖ) l

end TauCeti
