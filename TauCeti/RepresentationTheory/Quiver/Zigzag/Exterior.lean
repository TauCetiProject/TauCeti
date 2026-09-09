/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.Zigzag.Skew

/-!
# The exterior skew-zigzag parameter

A skew-zigzag parameter labels each ordered pair of incident edges of a simple graph by the
unit-valued ratio between the two backtracks they carry.  The **exterior** parameter of a graph in
which no vertex has three pairwise distinct neighbours, that is of a graph all of whose degrees are
at most two, gives distinct incident edges the ratio `-1`, so its relation makes the two backtracks
at a vertex sum to zero.  The degree hypothesis is what guarantees the signs are a cocycle over
every coefficient ring: at a vertex with three pairwise distinct neighbours the three signs would
multiply to `-1`, which obstructs the cocycle identity unless `2` is zero, where the sign collapses
anyway.

This is the parameter carried by the basic algebra of the exterior skew group algebra of an odd
cyclic subgroup of `SU(2)`.  When `2` is zero in the coefficient ring the sign collapses, the
exterior parameter is the constant parameter, and its relation ideal is the ordinary zigzag ideal.

## Main definitions

* `TauCeti.SkewZigzagParameter.exterior`: the exterior skew-zigzag parameter of a graph whose
  degrees are at most two.

## Main results

* `TauCeti.SkewZigzagParameter.exterior_ratio`: the exterior ratio of two incident edges is `1` if
  they agree and `-1` otherwise.
* `TauCeti.SkewZigzagParameter.exterior_eq_one`: in characteristic two the exterior parameter is
  the constant parameter.
* `TauCeti.skewZigzagMk_exterior_backtrackElem_add_backtrackElem_eq_zero`: in the exterior
  relation quotient the two backtracks at a vertex sum to zero.
* `TauCeti.skewZigzagIdeal_exterior_eq_zigzagIdeal`: in characteristic two the exterior parameter
  presents the ordinary zigzag relations.

## References

C. Couture, *Skew-Zigzag Algebras*, Sections 3 and 4, https://arxiv.org/abs/1509.08405, for the
skew parameters and their gauge relation.

S. Huerfano and M. Khovanov, *A category for the adjoint representation*, Section 3,
https://arxiv.org/abs/math/0002060, for the exterior skew group algebras this relation matches.
-/

public section

namespace TauCeti

open DoubledQuiver

universe u w

namespace SkewZigzagParameter

section Exterior

variable (k : Type w) [CommRing k] {V : Type u} [DecidableEq V] {G : SimpleGraph V}
  (hG : ∀ ⦃i j j' j'' : V⦄, G.Adj i j → G.Adj i j' → G.Adj i j'' → j = j' ∨ j' = j'' ∨ j'' = j)

/-- The two signs comparing a pair of neighbours in either order cancel. -/
private theorem exteriorSign_mul_exteriorSign (a b : V) :
    (if a = b then (1 : kˣ) else -1) * (if b = a then 1 else -1) = 1 := by
  rcases eq_or_ne a b with rfl | hne
  · rw [ite_eq_left rfl, one_mul]
  · rw [ite_eq_right hne, ite_eq_right hne.symm, neg_mul_neg, one_mul]

/-- The **exterior skew-zigzag parameter** of a graph no vertex of which has three pairwise
distinct neighbours, that is, of a graph all of whose degrees are at most two: the ratio between
the backtracks along two distinct incident edges is `-1`, so the relation it imposes makes the two
backtracks at a vertex sum to zero.  The degree hypothesis is what makes the ratios a cocycle over
every coefficient ring: at a vertex with three pairwise distinct neighbours the three signs would
multiply to `-1`, which obstructs the cocycle identity unless `2` is zero, where the sign collapses
anyway.

The odd cycles are the McKay graphs of the odd cyclic subgroups of `SU(2)`, and it is this
relation, rather than the ordinary one, that the exterior skew group algebras of those subgroups
carry. -/
def exterior : SkewZigzagParameter k G where
  ratio _ j j' _ _ := if j = j' then 1 else -1
  ratio_self := by intro i j h; exact ite_eq_left rfl
  ratio_inv := by
    intro i j j' h h'
    exact exteriorSign_mul_exteriorSign k j j'
  ratio_cocycle := by
    intro i j j' j'' h h' h''
    rcases hG h h' h'' with rfl | rfl | rfl
    · rw [ite_eq_left rfl, one_mul, exteriorSign_mul_exteriorSign]
    · rw [ite_eq_left rfl, mul_one, exteriorSign_mul_exteriorSign]
    · rw [ite_eq_left rfl, mul_one, exteriorSign_mul_exteriorSign]

variable {k}

/-- **The exterior ratio of two incident edges** is one when they agree and minus one otherwise. -/
@[simp]
theorem exterior_ratio {i j j' : V} (h : G.Adj i j) (h' : G.Adj i j') :
    (exterior k hG).ratio h h' = if j = j' then 1 else -1 := (rfl)

/-- **The exterior ratio of two distinct incident edges is minus one.** -/
theorem exterior_ratio_of_ne {i j j' : V} (h : G.Adj i j) (h' : G.Adj i j') (hne : j ≠ j') :
    (exterior k hG).ratio h h' = -1 :=
  (exterior_ratio hG h h').trans (ite_eq_right hne)

/-- **In characteristic two the exterior parameter is the constant parameter.** The sign
distinguishing the two backtracks at a vertex collapses, so the exterior and the ordinary zigzag
presentations agree identically. -/
theorem exterior_eq_one (h2 : (2 : k) = 0) : exterior k hG = 1 := by
  have hneg : (-1 : kˣ) = 1 :=
    Units.ext (by rw [Units.val_neg, Units.val_one]; linear_combination -h2)
  ext i j j' h h'
  rw [← Units.ext_iff]
  rcases eq_or_ne j j' with rfl | hne
  · rw [one_ratio]
    exact (exterior k hG).ratio_self h
  · rw [exterior_ratio_of_ne hG h h' hne, one_ratio, hneg]

end Exterior

end SkewZigzagParameter

section ExteriorRelations

variable (k : Type w) [CommRing k] {V : Type u} [DecidableEq V] [Finite V] (G : SimpleGraph V)
  (hG : ∀ ⦃i j j' j'' : V⦄, G.Adj i j → G.Adj i j' → G.Adj i j'' → j = j' ∨ j' = j'' ∨ j'' = j)

/-- **In the exterior relation quotient the two backtracks at a vertex sum to zero.** This is the
shape in which the exterior relation appears for the basic algebra of an exterior skew group
algebra. -/
theorem skewZigzagMk_exterior_backtrackElem_add_backtrackElem_eq_zero {i j j' : V}
    (h : G.Adj i j) (h' : G.Adj i j') (hne : j ≠ j') :
    skewZigzagMk k G (SkewZigzagParameter.exterior k hG) (backtrackElem G k h) +
        skewZigzagMk k G (SkewZigzagParameter.exterior k hG) (backtrackElem G k h') = 0 := by
  rw [skewZigzagMk_backtrackElem_eq_smul k G _ h h',
    SkewZigzagParameter.exterior_ratio_of_ne hG h h' hne, Units.val_neg, Units.val_one,
    neg_one_smul, neg_add_cancel]

/-- **In characteristic two the exterior parameter presents the ordinary zigzag relations.** -/
theorem skewZigzagIdeal_exterior_eq_zigzagIdeal (h2 : (2 : k) = 0) :
    skewZigzagIdeal k G (SkewZigzagParameter.exterior k hG) = zigzagIdeal k G := by
  rw [SkewZigzagParameter.exterior_eq_one hG h2, skewZigzagIdeal_one_eq_zigzagIdeal]

end ExteriorRelations

end TauCeti
