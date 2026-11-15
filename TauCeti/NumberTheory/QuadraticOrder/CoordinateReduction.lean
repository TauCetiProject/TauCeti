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

Coefficientwise reduction of an integral quadratic algebra is injective on a coordinate
rectangle whenever integer reduction is injective on each coordinate set. At a positive
modulus its image has the product cardinality, bounded by the square of the modulus.
In particular, any two half-open integer intervals of length at most the modulus give
an injectively reduced rectangle. Closed intervals must omit the last endpoint of a full
period. No squarefreeness or irreducibility assumption on the quadratic presentation is needed.
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

/-- Two half-open coordinate intervals of length at most the positive modulus reduce
injectively, with arbitrary integer starting points. -/
theorem injOn_mapRingHom_setOf_re_mem_Ico_im_mem_Ico [NeZero m]
    (s t u v : ℤ) (hst : t - s ≤ m) (huv : v - u ≤ m) :
    Set.InjOn (mapRingHom (Int.castRingHom (ZMod m)) a b)
      {z : QuadraticAlgebra ℤ a b | z.re ∈ Set.Ico s t ∧ z.im ∈ Set.Ico u v} :=
  injOn_mapRingHom_setOf_re_mem_im_mem a b _
    ((CharP.intCast_injOn_Ico_iff (ZMod m) m s t).mpr hst)
    ((CharP.intCast_injOn_Ico_iff (ZMod m) m u v).mpr huv)

/-- The endpoint-removed closed intervals `[s, s + m - 1]` and `[t, t + m - 1]`
give an injectively reduced coordinate rectangle. -/
theorem injOn_mapRingHom_setOf_re_mem_Icc_im_mem_Icc [NeZero m] (s t : ℤ) :
    Set.InjOn (mapRingHom (Int.castRingHom (ZMod m)) a b)
      {z : QuadraticAlgebra ℤ a b |
        z.re ∈ Set.Icc s (s + m - 1) ∧ z.im ∈ Set.Icc t (t + m - 1)} :=
  injOn_mapRingHom_setOf_re_mem_im_mem a b _
    ((CharP.intCast_injOn_Icc_iff (ZMod m) m s (s + m - 1)).mpr (by omega))
    ((CharP.intCast_injOn_Icc_iff (ZMod m) m t (t + m - 1)).mpr (by omega))

end QuadraticAlgebra
