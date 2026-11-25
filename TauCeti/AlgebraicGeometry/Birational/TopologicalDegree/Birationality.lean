/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Birational.TopologicalDegree.Basic

/-!
# Topological degree one

For a dominant rational map `f : X ⤏ Y` of integral schemes, the topological degree
`e(f) = [K(X) : f^*K(Y)]` is `1` exactly when the pullback of rational functions `f^*` is
surjective, equivalently bijective, since a homomorphism of fields is injective
(`AlgebraicGeometry.Scheme.RationalMap.topologicalDegree_eq_one_iff_bijective`). No hypothesis on
dimensions is needed.

A dominant rational map with a dominant inverse on one side has topological degree `1`, and so has
the inverse: by multiplicativity `e(f) · e(g) = e(g ∘ f) = e(id) = 1`. The inverse is then
two-sided, because `f^*` is bijective and a dominant rational map is determined by its pullback
(`AlgebraicGeometry.Scheme.RationalMap.eq_of_functionFieldMap_eq`). These are the directions of
the birationality criterion of the topological degree that need no realization of field maps by
rational maps.

## Main results

* `AlgebraicGeometry.Scheme.RationalMap.topologicalDegree_eq_one_iff_surjective`,
  `AlgebraicGeometry.Scheme.RationalMap.topologicalDegree_eq_one_iff_bijective`: `e(f) = 1`
  exactly when `f^*` is surjective, equivalently bijective.
* `AlgebraicGeometry.Scheme.RationalMap.topologicalDegree_eq_one_iff_isIso`: `e(f) = 1` exactly
  when `f^*` is an isomorphism of fields.
* `AlgebraicGeometry.Scheme.RationalMap.topologicalDegree_eq_one_of_comp_eq_id`: if `g ∘ f = id`
  for dominant `f` and `g`, then `e(f) = e(g) = 1`.
* `AlgebraicGeometry.Scheme.RationalMap.comp_eq_id_of_comp_eq_id`: a one-sided inverse of a
  dominant rational map by a dominant rational map is two-sided.

## References

* The Stacks Project, Tag 0BXN (the degree of a dominant generically finite morphism of integral
  schemes as the degree of the extension of function fields).
-/

public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]

/-- **Topological degree one.** A dominant rational map of integral schemes has topological
degree `1` exactly when its pullback of rational functions is surjective. -/
theorem RationalMap.topologicalDegree_eq_one_iff_surjective (f : X ⤏ Y) [f.IsDominant] :
    f.topologicalDegree = 1 ↔ Function.Surjective f.functionFieldMap.hom := by
  rw [topologicalDegree_def, ← Subfield.relfinrank_top_right, Subfield.relfinrank_eq_one_iff,
    top_le_iff, RingHom.fieldRange_eq_top_iff]

/-- **Topological degree one.** A dominant rational map of integral schemes has topological
degree `1` exactly when its pullback of rational functions is bijective: a homomorphism of fields
is injective. -/
theorem RationalMap.topologicalDegree_eq_one_iff_bijective (f : X ⤏ Y) [f.IsDominant] :
    f.topologicalDegree = 1 ↔ Function.Bijective f.functionFieldMap.hom :=
  (topologicalDegree_eq_one_iff_surjective f).trans
    ⟨fun h => ⟨f.functionFieldMap.hom.injective, h⟩, And.right⟩

/-- **Topological degree one.** A dominant rational map of integral schemes has topological
degree `1` exactly when its pullback of rational functions is an isomorphism. -/
theorem RationalMap.topologicalDegree_eq_one_iff_isIso (f : X ⤏ Y) [f.IsDominant] :
    f.topologicalDegree = 1 ↔ IsIso f.functionFieldMap :=
  (topologicalDegree_eq_one_iff_bijective f).trans
    (ConcreteCategory.isIso_iff_bijective f.functionFieldMap).symm

/-- If `g ∘ f = id` for dominant rational maps `f : X ⤏ Y` and `g : Y ⤏ X` of integral schemes,
then `e(f) = e(g) = 1`: their product is `e(id) = 1`. -/
theorem RationalMap.topologicalDegree_eq_one_of_comp_eq_id (f : X ⤏ Y) [f.IsDominant]
    (g : Y ⤏ X) [g.IsDominant] (h : f.comp g = RationalMap.id X) :
    f.topologicalDegree = 1 ∧ g.topologicalDegree = 1 :=
  mul_eq_one.1 <| (topologicalDegree_comp f g).symm.trans <|
    (topologicalDegree_congr h).trans topologicalDegree_id

/-- **One-sided inverses are two-sided.** If `g ∘ f = id` for dominant rational maps
`f : X ⤏ Y` and `g : Y ⤏ X` of integral schemes, then `f ∘ g = id`: `f^*` is bijective with
inverse `g^*`, and a dominant rational map is determined by its pullback. -/
theorem RationalMap.comp_eq_id_of_comp_eq_id (f : X ⤏ Y) [f.IsDominant] (g : Y ⤏ X)
    [g.IsDominant] (h : f.comp g = RationalMap.id X) : g.comp f = RationalMap.id Y := by
  have hfg : f.functionFieldMap.hom.comp g.functionFieldMap.hom = RingHom.id _ := by
    rw [← CommRingCat.hom_comp, ← functionFieldMap_comp, functionFieldMap_congr h,
      functionFieldMap_id, CommRingCat.hom_id]
  refine eq_of_functionFieldMap_eq ?_
  rw [functionFieldMap_comp, functionFieldMap_id]
  ext x
  exact Function.LeftInverse.rightInverse_of_injective (g := g.functionFieldMap.hom)
    (fun y => congr($hfg y)) f.functionFieldMap.hom.injective x

end AlgebraicGeometry.Scheme
