/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Relrank
public import TauCeti.AlgebraicGeometry.Birational.FunctionField.Basic

/-!
# The topological degree of a dominant rational map

For a dominant rational map `f : X ⤏ Y` of integral schemes, the *topological degree*
`e(f) = [K(X) : f^*K(Y)]` is the dimension of `K(X)` over the image of the pullback of rational
functions `f^*` (`AlgebraicGeometry.Scheme.RationalMap.topologicalDegree`). It counts inseparable
degree, and takes the junk value `0` when the extension is infinite, for instance for the
projection `ℙ² ⤏ ℙ¹` from a point. For dominant `f` and `g` it is multiplicative under
composition without any hypothesis on dimensions, because the tower law for `Module.finrank` holds
with the junk value.

## Main definitions

* `AlgebraicGeometry.Scheme.RationalMap.topologicalDegree`: the topological degree
  `[K(X) : f^*K(Y)]` of a dominant rational map of integral schemes.

## Main results

* `AlgebraicGeometry.Scheme.RationalMap.topologicalDegree_id` and
  `AlgebraicGeometry.Scheme.RationalMap.topologicalDegree_comp`: `e(id) = 1` and
  `e(g ∘ f) = e(f)·e(g)`.
* `AlgebraicGeometry.Scheme.Hom.toRationalMap_comp` and
  `AlgebraicGeometry.Scheme.Hom.topologicalDegree_comp`: the rational map of a composite of
  morphisms with dominant first factor is the composite of their rational maps, so the topological
  degree is multiplicative for dominant morphisms.

## References

* The Stacks Project, Tag 0BXN (the degree of a dominant generically finite morphism of integral
  schemes as the degree of the extension of function fields).
* T.-C. Dinh and N. Sibony, *Une borne supérieure pour l'entropie topologique d'une application
  rationnelle*, Ann. of Math. 161 (2005), for the topological degree of a rational map.
-/

public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme

variable {X Y Z : Scheme.{u}} [IsIntegral X] [IsIntegral Y] [IsIntegral Z]

/-- The **topological degree** `e(f) = [K(X) : f^*K(Y)]` of a dominant rational map `f : X ⤏ Y`
of integral schemes: the dimension of `K(X)` over the image of the pullback of rational functions
`f^*`. It counts inseparable degree, and is `0` when `K(X)` is infinite-dimensional over
`f^*K(Y)`. -/
noncomputable def RationalMap.topologicalDegree (f : X ⤏ Y) [f.IsDominant] : ℕ :=
  Module.finrank f.functionFieldMap.hom.fieldRange X.functionField

/-- The topological degree is the dimension of `K(X)` over the image of `f^*`. -/
theorem RationalMap.topologicalDegree_def (f : X ⤏ Y) [f.IsDominant] :
    f.topologicalDegree = Module.finrank f.functionFieldMap.hom.fieldRange X.functionField := by
  rw [topologicalDegree]

/-- Equal dominant rational maps have equal topological degrees, whatever the `IsDominant`
instances: rewriting along `f = g` is blocked by the instance argument. -/
theorem RationalMap.topologicalDegree_congr {f g : X ⤏ Y} [f.IsDominant] [g.IsDominant]
    (h : f = g) : f.topologicalDegree = g.topologicalDegree := by
  subst h
  rfl

/-- The topological degree of the rational map of a dominant morphism `g` is the dimension of
`K(X)` over the image of the pullback of rational functions along `g`. -/
theorem Hom.topologicalDegree_toRationalMap (g : X ⟶ Y) [IsDominant g] :
    g.toRationalMap.topologicalDegree =
      Module.finrank g.functionFieldMap.hom.fieldRange X.functionField := by
  rw [RationalMap.topologicalDegree_def, functionFieldMap_toRationalMap]

/-- The identity rational map has topological degree `1`. -/
@[simp]
theorem RationalMap.topologicalDegree_id : (RationalMap.id X).topologicalDegree = 1 := by
  rw [topologicalDegree_def, functionFieldMap_id, CommRingCat.hom_id,
    RingHom.fieldRange_eq_top_iff.mpr Function.surjective_id, ← Subfield.relfinrank_top_right,
    Subfield.relfinrank_top_left]

/-- **Multiplicativity of the topological degree**: `e(g ∘ f) = e(f)·e(g)` for dominant rational
maps `f : X ⤏ Y` and `g : Y ⤏ Z` of integral schemes. No hypothesis on dimensions is needed: if
one side involves an infinite extension, both sides are the junk value `0`. -/
theorem RationalMap.topologicalDegree_comp (f : X ⤏ Y) [f.IsDominant] (g : Y ⤏ Z)
    [g.IsDominant] :
    (f.comp g).topologicalDegree = f.topologicalDegree * g.topologicalDegree := by
  have hle : (f.functionFieldMap.hom.comp g.functionFieldMap.hom).fieldRange ≤
      f.functionFieldMap.hom.fieldRange := by
    simpa only [← SetLike.coe_subset_coe, RingHom.coe_fieldRange, RingHom.coe_comp] using
      Set.range_comp_subset_range g.functionFieldMap.hom f.functionFieldMap.hom
  -- `f^*` carries `g^*K(Z) ⊆ K(Y)` onto `(g ∘ f)^*K(Z) ⊆ f^*K(Y)`
  have htransport : Subfield.relfinrank
      (f.functionFieldMap.hom.comp g.functionFieldMap.hom).fieldRange
      f.functionFieldMap.hom.fieldRange = g.topologicalDegree := by
    rw [← RingHom.map_fieldRange, RingHom.fieldRange_eq_map f.functionFieldMap.hom,
      Subfield.relfinrank_map_map, Subfield.relfinrank_top_right, topologicalDegree_def]
  rw [topologicalDegree_def, functionFieldMap_comp, CommRingCat.hom_comp,
    ← Subfield.relfinrank_mul_finrank_top hle, htransport, ← topologicalDegree_def, mul_comm]

omit [IsIntegral Z] in
/-- The rational map of a composite `a ≫ b` of morphisms, with `a` dominant, is the composite of
their rational maps. -/
theorem Hom.toRationalMap_comp (a : X ⟶ Y) [IsDominant a] (b : Y ⟶ Z) :
    (a ≫ b).toRationalMap = a.toRationalMap.comp b.toRationalMap := by
  rw [RationalMap.comp_toRationalMap]
  rfl

/-- **Multiplicativity of the topological degree for morphisms**: `e(a ≫ b) = e(a)·e(b)` for
dominant morphisms `a : X ⟶ Y` and `b : Y ⟶ Z` of integral schemes. -/
theorem Hom.topologicalDegree_comp (a : X ⟶ Y) [IsDominant a] (b : Y ⟶ Z) [IsDominant b] :
    (a ≫ b).toRationalMap.topologicalDegree =
      a.toRationalMap.topologicalDegree * b.toRationalMap.topologicalDegree := by
  rw [RationalMap.topologicalDegree_congr (Hom.toRationalMap_comp a b),
    RationalMap.topologicalDegree_comp]

end AlgebraicGeometry.Scheme
