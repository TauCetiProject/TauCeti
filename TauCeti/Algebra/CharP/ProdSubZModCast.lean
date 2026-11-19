/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic

/-!
# The product of the translates of an element by the residues of `ZMod p`

In a commutative ring of prime characteristic `p`, the polynomial identity
`∏ i ∈ 𝔽_p, (X - i) = X ^ p - X` specializes to `∏ i : ZMod p, (x - i) = x ^ p - x` for every
element `x`.

## Main results

* `TauCeti.prod_sub_zmodCast`: `∏ i : ZMod p, (x - i) = x ^ p - x` in characteristic `p`.
-/

public section

open Polynomial

namespace TauCeti

variable {R : Type*} [CommRing R] (p : ℕ) [hp : Fact p.Prime] [CharP R p]

/-- In characteristic `p`, `x ^ p - x` is the product of the translates `x - i` over all
residues `i ∈ ZMod p`. -/
theorem prod_sub_zmodCast (x : R) : ∏ i : ZMod p, (x - (i.cast : R)) = x ^ p - x := by
  have hpoly : ∏ i : ZMod p, (X - C i) = (X ^ p - X : (ZMod p)[X]) := by
    have hroots : (X ^ p - X : (ZMod p)[X]).roots = Finset.univ.val := by
      simpa using FiniteField.roots_X_pow_card_sub_X (ZMod p)
    have h := prod_multiset_X_sub_C_of_monic_of_roots_card_eq
      (monic_X_pow_sub (p := (X : (ZMod p)[X])) (by
        rw [degree_X]; exact_mod_cast hp.out.one_lt))
      (by rw [natDegree_X_pow_sub_X hp.out.one_lt, hroots]; simp)
    rwa [hroots] at h
  simpa [map_prod] using congrArg (eval₂RingHom (ZMod.castHom dvd_rfl R) x) hpoly

end TauCeti
