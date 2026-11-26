/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Birational.TopologicalDegree.Basic
public import TauCeti.AlgebraicGeometry.Birational.FunctionField.Determination
public import TauCeti.AlgebraicGeometry.Birational.PartialIso

/-!
# Topological degree one

For a dominant rational map `f : X ⤏ Y` of integral schemes, the topological degree
`e(f) = [K(X) : f^*K(Y)]` is `1` exactly when the pullback of rational functions `f^*` is
surjective, equivalently bijective, since a homomorphism of fields is injective
(`AlgebraicGeometry.Scheme.RationalMap.topologicalDegree_eq_one_iff_bijective`). No hypothesis on
dimensions is needed.

A dominant rational map with a dominant inverse on one side has topological degree `1`, and so has
the inverse: by multiplicativity `e(f) · e(g) = e(g ∘ f) = e(id) = 1`. The inverse is then
two-sided (`AlgebraicGeometry.Scheme.RationalMap.comp_eq_id_of_comp_eq_id`).

A partial isomorphism `φ` of integral schemes, an isomorphism between dense opens of `X` and `Y`
(Mathlib's `AlgebraicGeometry.Scheme.PartialIso`), has rational map `φ.toRationalMap` with inverse
`φ.symm.toRationalMap` on both sides
(`AlgebraicGeometry.Scheme.PartialIso.toRationalMap_comp_symm`, in
`TauCeti.AlgebraicGeometry.Birational.PartialIso`). So the rational map of a partial
isomorphism has topological degree `1`, and its pullback of rational functions is an isomorphism:
a birational map has topological degree `1`.

Conversely, over a ring `k`, a dominant `k`-rational map `f : X ⤏ Y` of integral `k`-schemes, with
`X` locally of finite type over `k`, has topological degree `1` exactly when it has a two-sided
inverse among dominant `k`-rational maps
(`AlgebraicGeometry.Scheme.RationalMap.topologicalDegree_eq_one_iff_exists_comp_eq_id`): the
inverse is the rational map whose pullback is `(f^*)^{-1}`, which exists because a dominant
`k`-rational map into `X` is determined by, and can be built from, its pullback.

## Main results

* `AlgebraicGeometry.Scheme.RationalMap.topologicalDegree_eq_one_iff_surjective`,
  `AlgebraicGeometry.Scheme.RationalMap.topologicalDegree_eq_one_iff_bijective`: `e(f) = 1`
  exactly when `f^*` is surjective, equivalently bijective.
* `AlgebraicGeometry.Scheme.RationalMap.topologicalDegree_eq_one_iff_isIso`: `e(f) = 1` exactly
  when `f^*` is an isomorphism of fields.
* `AlgebraicGeometry.Scheme.RationalMap.topologicalDegree_eq_one_of_comp_eq_id`: if `g ∘ f = id`
  for dominant `f` and `g`, then `e(f) = e(g) = 1`.
* `AlgebraicGeometry.Scheme.PartialIso.topologicalDegree_toRationalMap`: the rational map of a
  partial isomorphism has topological degree `1`.
* `AlgebraicGeometry.Scheme.RationalMap.topologicalDegree_eq_one_iff_exists_comp_eq_id`: a
  dominant `k`-rational map has topological degree `1` exactly when it has a two-sided dominant
  `k`-rational inverse.

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

/-- **A birational map has topological degree one**: the rational map of a partial isomorphism
of integral schemes has topological degree `1`. -/
@[simp]
theorem PartialIso.topologicalDegree_toRationalMap (φ : X.PartialIso Y) :
    φ.toRationalMap.topologicalDegree = 1 :=
  (RationalMap.topologicalDegree_eq_one_of_comp_eq_id _ _ φ.toRationalMap_comp_symm).1

/-- The pullback of rational functions along the rational map of a partial isomorphism of
integral schemes is an isomorphism of function fields. -/
instance PartialIso.isIso_functionFieldMap_toRationalMap (φ : X.PartialIso Y) :
    IsIso φ.toRationalMap.functionFieldMap :=
  (RationalMap.topologicalDegree_eq_one_iff_isIso _).1 φ.topologicalDegree_toRationalMap

section Inverse

variable (k : Type u) [CommRing k] [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
  [LocallyOfFiniteType (X ↘ Spec (.of k))]

/-- A dominant `k`-rational map `f : X ⤏ Y` of integral `k`-schemes of topological degree `1`,
with `X` locally of finite type over `k`, has a two-sided inverse among dominant `k`-rational
maps: the rational map whose pullback of rational functions is `(f^*)^{-1}`. -/
theorem RationalMap.exists_comp_eq_id_of_topologicalDegree_eq_one (f : X ⤏ Y) [f.IsDominant]
    [f.IsOver (X ↘ Spec (.of k)) (Y ↘ Spec (.of k))] (h : f.topologicalDegree = 1) :
    ∃ (g : Y ⤏ X) (_ : g.IsDominant), g.IsOver (Y ↘ Spec (.of k)) (X ↘ Spec (.of k)) ∧
      f.comp g = RationalMap.id X ∧ g.comp f = RationalMap.id Y := by
  have hb : Function.Bijective (f.functionFieldAlgHom k) := by
    have := (topologicalDegree_eq_one_iff_bijective f).1 h
    convert this using 1
    ext a
    exact functionFieldAlgHom_apply k f a
  let e := AlgEquiv.ofBijective (f.functionFieldAlgHom k) hb
  let g := ofFunctionFieldAlgHom k e.symm.toAlgHom
  have hcomp : f.comp g = RationalMap.id X := by
    have := isOver_comp (sX := X ↘ Spec (.of k)) (sY := Y ↘ Spec (.of k))
      (sZ := X ↘ Spec (.of k)) f inferInstance g inferInstance
    refine eq_of_functionFieldAlgHom_eq k ?_
    rw [functionFieldAlgHom_comp, functionFieldAlgHom_id,
      functionFieldAlgHom_ofFunctionFieldAlgHom]
    ext a
    exact e.apply_symm_apply a
  exact ⟨g, inferInstance, inferInstance, hcomp, comp_eq_id_of_comp_eq_id f g hcomp⟩

/-- **Topological degree one and inverses.** A dominant `k`-rational map `f : X ⤏ Y` of integral
`k`-schemes, with `X` locally of finite type over `k`, has topological degree `1` exactly when it
has a two-sided inverse among dominant `k`-rational maps. -/
theorem RationalMap.topologicalDegree_eq_one_iff_exists_comp_eq_id (f : X ⤏ Y) [f.IsDominant]
    [f.IsOver (X ↘ Spec (.of k)) (Y ↘ Spec (.of k))] :
    f.topologicalDegree = 1 ↔ ∃ (g : Y ⤏ X) (_ : g.IsDominant),
      g.IsOver (Y ↘ Spec (.of k)) (X ↘ Spec (.of k)) ∧
        f.comp g = RationalMap.id X ∧ g.comp f = RationalMap.id Y :=
  ⟨exists_comp_eq_id_of_topologicalDegree_eq_one k f, fun ⟨_, _, _, h, _⟩ =>
    (topologicalDegree_eq_one_of_comp_eq_id f _ h).1⟩

end Inverse

end AlgebraicGeometry.Scheme
