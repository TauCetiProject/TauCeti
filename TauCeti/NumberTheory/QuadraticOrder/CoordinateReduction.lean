/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: pi
-/
module

public import TauCeti.Algebra.CharP.Interval
public import TauCeti.Algebra.QuadraticAlgebra.CoordinateSet
public import Mathlib.Data.ZMod.Basic
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# Reduction of coordinate rectangles

At positive modulus `m`, a coordinate rectangle with injectively reduced coordinates
has cardinality at most `m ^ 2`. Reduction is injective on rectangles of half-open integer
intervals with signed endpoint differences at most `m`, and of closed integer intervals
with signed endpoint differences strictly less than `m`. Thus a closed interval cannot
contain both endpoints of a full period. No squarefreeness or irreducibility assumption
on the quadratic presentation is needed.

General coordinate-rectangle injectivity and image cardinality for coefficient maps are
provided in `TauCeti.Algebra.QuadraticAlgebra.CoordinateSet`, without a positivity assumption.
-/

public section

namespace QuadraticAlgebra

variable (a b : ℤ) (m : ℕ)

/-- At positive modulus, a rectangle with injectively reduced coordinates has at most
`m²` elements. The positivity hypothesis is essential for this finite ambient bound. -/
theorem ncard_setOf_re_mem_im_mem_le_sq [NeZero m] {U V : Set ℤ}
    (hU : Set.InjOn (Int.cast : ℤ → ZMod m) U)
    (hV : Set.InjOn (Int.cast : ℤ → ZMod m) V) :
    {z : QuadraticAlgebra ℤ a b | z.re ∈ U ∧ z.im ∈ V}.ncard ≤ m ^ 2 := by
  have : Finite (QuadraticAlgebra (ZMod m) (a : ZMod m) (b : ZMod m)) :=
    Finite.of_equiv (ZMod m × ZMod m) (equivProd _ _).symm
  have h := Set.ncard_le_card
    ((mapRingHom (Int.castRingHom (ZMod m)) a b) ''
      {z : QuadraticAlgebra ℤ a b | z.re ∈ U ∧ z.im ∈ V})
  rw [ncard_image_mapRingHom_setOf_re_mem_im_mem a b _ hU hV] at h
  simpa [Nat.card_congr (equivProd ((a : ZMod m)) ((b : ZMod m))),
    Nat.card_prod, Nat.card_zmod, pow_two, ncard_setOf_re_mem_im_mem] using h

/-- Two half-open coordinate intervals with signed endpoint differences at most the modulus
reduce injectively, with arbitrary integer endpoints. -/
theorem injOn_mapRingHom_setOf_re_mem_Ico_im_mem_Ico
    (s t u v : ℤ) (hst : t - s ≤ m) (huv : v - u ≤ m) :
    Set.InjOn (mapRingHom (Int.castRingHom (ZMod m)) a b)
      {z : QuadraticAlgebra ℤ a b | z.re ∈ Set.Ico s t ∧ z.im ∈ Set.Ico u v} :=
  injOn_mapRingHom_setOf_re_mem_im_mem a b _
    (CharP.intCast_injOn_Ico_of_sub_le (ZMod m) m hst)
    (CharP.intCast_injOn_Ico_of_sub_le (ZMod m) m huv)

/-- Two closed coordinate intervals with signed endpoint differences strictly less than the
modulus reduce injectively, with arbitrary integer endpoints. -/
theorem injOn_mapRingHom_setOf_re_mem_Icc_im_mem_Icc
    (s t u v : ℤ) (hst : t - s < m) (huv : v - u < m) :
    Set.InjOn (mapRingHom (Int.castRingHom (ZMod m)) a b)
      {z : QuadraticAlgebra ℤ a b |
        z.re ∈ Set.Icc s t ∧ z.im ∈ Set.Icc u v} :=
  injOn_mapRingHom_setOf_re_mem_im_mem a b _
    (CharP.intCast_injOn_Icc_of_sub_lt (ZMod m) m hst)
    (CharP.intCast_injOn_Icc_of_sub_lt (ZMod m) m huv)

end QuadraticAlgebra
