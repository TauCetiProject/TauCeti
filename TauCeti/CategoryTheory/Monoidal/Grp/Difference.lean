/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp

/-!
# The difference of a morphism to a group object

Let `G` be a group object in a cartesian monoidal category `C` and `X` an object of `C`. The
**difference** of a morphism `a : X ⟶ G` is the morphism `X ⊗ X ⟶ G`, `(x, y) ↦ a y / a x`, in
Mathlib's multiplicative notation for the group of points `T ⟶ G`. It vanishes on the diagonal,
is inverted by swapping the factors, satisfies the cocycle relation `d(y, z) * d(x, y) = d(x, z)`,
and is unchanged when `a` is right-translated by a global point. None of this needs `G` to be
commutative.

For a curve `X` over a base `S` with a degree-one point and Abel map `a : X ⟶ J` to its relative
Jacobian, working in `Over S` (where `⊗` is the fibre product over `S`), the difference of `a` is
the curve difference `j(x, y) = [y] − [x]`. Since every statement here is an equality of
morphisms, it holds on points with values in every `S`-scheme, nonreduced ones included.

The difference commutes with a monoidal, equivalently finite-product-preserving, functor
`F : C ⥤ D` (for instance base change along `S' ⟶ S`) through the product comparison map
`prodComparison`, with `F.obj G` carrying the image group structure.

## Main definitions

* `TauCeti.GrpObj.difference a`: the morphism `(x, y) ↦ a y / a x`.

## Main results

* `TauCeti.GrpObj.lift_comp_difference`: the difference on points with values in an object.
* `TauCeti.GrpObj.lift_comp_difference_mul_lift_comp_difference`: the cocycle relation.
* `TauCeti.GrpObj.difference_mul_toUnit_comp`: the difference does not see right translation by a
  global point.
* `TauCeti.GrpObj.map_difference`: compatibility with monoidal functors.

## References

* V. Dimitrov, Z. Gao, P. Habegger, *Uniformity in Mordell–Lang for curves*, Ann. of Math. 194
  (2021), arXiv:2001.10276v3, §6.1, equation (6.3).
* X. Yuan, *Arithmetic bigness and a uniform Bogomolov-type result*, arXiv:2108.05625v4, §2.2.1.
-/

public section

open CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj

namespace TauCeti.GrpObj

universe v v' u u'

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C] {X G : C} [GrpObj G]

/-- The **difference** of a morphism `a : X ⟶ G` to a group object: the morphism `X ⊗ X ⟶ G`
sending a pair of points `(x, y)` to `a y / a x` (`lift_comp_difference`). -/
noncomputable def difference (a : X ⟶ G) : X ⊗ X ⟶ G :=
  snd X X ≫ a / fst X X ≫ a

theorem difference_def (a : X ⟶ G) : difference a = snd X X ≫ a / fst X X ≫ a :=
  (rfl)

/-- The difference of `a` sends a pair of points `(x, y)` to `a y / a x`. -/
@[reassoc (attr := simp)]
theorem lift_comp_difference {T : C} (x y : T ⟶ X) (a : X ⟶ G) :
    lift x y ≫ difference a = y ≫ a / x ≫ a := by
  simp [difference_def, GrpObj.comp_div]

/-- The difference vanishes on the diagonal. -/
theorem lift_self_comp_difference {T : C} (x : T ⟶ X) (a : X ⟶ G) :
    lift x x ≫ difference a = 1 := by
  simp

/-- Swapping the two points inverts the difference. -/
theorem lift_comp_difference_swap {T : C} (x y : T ⟶ X) (a : X ⟶ G) :
    lift y x ≫ difference a = (lift x y ≫ difference a)⁻¹ := by
  simp

/-- The **cocycle relation** of the difference, `d(y, z) * d(x, y) = d(x, z)`. The order of the
factors matters when `G` is not commutative. -/
theorem lift_comp_difference_mul_lift_comp_difference {T : C} (x y z : T ⟶ X) (a : X ⟶ G) :
    (lift y z ≫ difference a) * (lift x y ≫ difference a) = lift x z ≫ difference a := by
  simp

/-- Right-translating `a` by a global point `c` of `G` does not change its difference. -/
@[simp]
theorem difference_mul_toUnit_comp (a : X ⟶ G) (c : 𝟙_ C ⟶ G) :
    difference (a * (toUnit X ≫ c)) = difference a := by
  simp [difference_def, MonObj.comp_mul, mul_div_mul_right_eq_div]

/-- Composing `a` with a homomorphism of group objects composes its difference. -/
theorem difference_comp {H : C} [GrpObj H] (a : X ⟶ G) (f : G ⟶ H) [IsMonHom f] :
    difference (a ≫ f) = difference a ≫ f := by
  simp [difference_def, GrpObj.div_comp]

/-- Precomposing `a` with `g : Y ⟶ X` precomposes its difference with `g ⊗ g`. -/
theorem tensorHom_comp_difference {Y : C} (g : Y ⟶ X) (a : X ⟶ G) :
    (g ⊗ₘ g) ≫ difference a = difference (g ≫ a) := by
  simp [difference_def, GrpObj.comp_div]

open scoped CategoryTheory.Obj in
/-- A monoidal functor sends the difference of `a` to the difference of `F.map a` through the
product comparison map, where `F.obj G` carries the image group structure. -/
theorem map_difference {D : Type u'} [Category.{v'} D] [CartesianMonoidalCategory D] (F : C ⥤ D)
    [F.Monoidal] (a : X ⟶ G) :
    F.map (difference a) = prodComparison F X X ≫ difference (F.map a) := by
  simp only [difference_def, div_eq_mul_inv, Functor.map_mul, Functor.map_inv', F.map_comp,
    MonObj.comp_mul, GrpObj.comp_inv, CartesianMonoidalCategory.prodComparison_fst_assoc,
    CartesianMonoidalCategory.prodComparison_snd_assoc]

end TauCeti.GrpObj
