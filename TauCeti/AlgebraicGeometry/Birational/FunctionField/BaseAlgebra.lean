/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Birational.FunctionField.Basic
public import TauCeti.AlgebraicGeometry.Scheme.BaseAlgebra

/-!
# The pullback of function fields along a `k`-rational map as a `k`-algebra map

Over a base ring `k`, the pullback `f^* : K(Y) ⟶ K(X)` of rational functions along a dominant
`k`-rational map `f : X ⤏ Y` of integral schemes is a `k`-algebra homomorphism
(`AlgebraicGeometry.Scheme.RationalMap.functionFieldAlgHom`), and the composition law for it needs
both maps to be dominant. This adapts the `k`-algebra pullback along a dominant `k`-morphism,
`AlgebraicGeometry.Scheme.Hom.functionFieldAlgHom` and its lemmas in
`TauCeti.AlgebraicGeometry.Scheme.BaseAlgebra`, to rational maps.

## Main definitions

* `AlgebraicGeometry.Scheme.RationalMap.functionFieldAlgHom`: the pullback as a `k`-algebra
  homomorphism, for a dominant `k`-rational map of integral `k`-schemes.
-/

public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme

variable {X Y Z : Scheme.{u}}

variable (k : Type u) [CommRing k] [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
  [Z.Over (Spec (.of k))] [IsIntegral X] [IsIntegral Y] [IsIntegral Z]

/-- The pullback of rational functions along a dominant `k`-rational map of integral schemes over
`Spec k` is compatible with the `k`-algebra structures of the function fields. -/
theorem RationalMap.functionFieldMap_algebraMap (f : X ⤏ Y) [f.IsDominant]
    [f.IsOver (X ↘ Spec (.of k)) (Y ↘ Spec (.of k))] (c : k) :
    f.functionFieldMap (algebraMap k Y.functionField c) = algebraMap k X.functionField c :=
  (specMap_comp_fromSpecStalk_genericPoint_comp_over_iff k f.functionFieldMap).mp
    (by rw [SpecMap_functionFieldMap_fromSpecStalk]
        exact f.fromFunctionField_comp_over (X ↘ Spec (.of k)) (Y ↘ Spec (.of k))) c

/-- `RationalMap.functionFieldMap_algebraMap` in simp-normal form, where a scalar `c : k` is the
germ of its pullback along the structure morphism. -/
@[simp]
theorem RationalMap.functionFieldMap_germToFunctionField_appTop (f : X ⤏ Y) [f.IsDominant]
    [f.IsOver (X ↘ Spec (.of k)) (Y ↘ Spec (.of k))] (c : k) :
    f.functionFieldMap
        (Y.germToFunctionField ⊤ ((Y ↘ Spec (.of k)).appTop ((ΓSpecIso (.of k)).inv c))) =
      X.germToFunctionField ⊤ ((X ↘ Spec (.of k)).appTop ((ΓSpecIso (.of k)).inv c)) := by
  simpa using f.functionFieldMap_algebraMap k c

/-- The pullback of rational functions `f^* : k(Y) → k(X)` along a dominant `k`-rational map
`f : X ⤏ Y` of integral schemes over `Spec k`, as a `k`-algebra homomorphism. -/
noncomputable def RationalMap.functionFieldAlgHom (f : X ⤏ Y) [f.IsDominant]
    [f.IsOver (X ↘ Spec (.of k)) (Y ↘ Spec (.of k))] :
    Y.functionField →ₐ[k] X.functionField where
  __ := f.functionFieldMap.hom
  commutes' := f.functionFieldMap_algebraMap k

/-- The `k`-algebra pullback `RationalMap.functionFieldAlgHom` is `RationalMap.functionFieldMap`
on elements. -/
@[simp]
theorem RationalMap.functionFieldAlgHom_apply (f : X ⤏ Y) [f.IsDominant]
    [f.IsOver (X ↘ Spec (.of k)) (Y ↘ Spec (.of k))] (a : Y.functionField) :
    f.functionFieldAlgHom k a = f.functionFieldMap a :=
  (rfl)

/-- The `k`-algebra pullback along the rational map of a dominant `k`-morphism `g` is the
`k`-algebra pullback along `g`. -/
@[simp]
theorem Hom.functionFieldAlgHom_toRationalMap (g : X ⟶ Y) [IsDominant g]
    [g.IsOver (Spec (.of k))] :
    g.toRationalMap.functionFieldAlgHom k = g.functionFieldAlgHom k := by
  ext
  simp

/-- The `k`-algebra pullback along the identity rational map is the identity. -/
theorem RationalMap.functionFieldAlgHom_id :
    (RationalMap.id X).functionFieldAlgHom k = AlgHom.id k X.functionField := by
  ext
  simp

/-- **Functoriality of the `k`-algebra pullback**: `(g ∘ f)^* = f^* ∘ g^*` for dominant
`k`-rational maps `f : X ⤏ Y` and `g : Y ⤏ Z` of integral schemes over `Spec k`. -/
@[simp]
theorem RationalMap.functionFieldAlgHom_comp (f : X ⤏ Y) [f.IsDominant]
    [f.IsOver (X ↘ Spec (.of k)) (Y ↘ Spec (.of k))] (g : Y ⤏ Z) [g.IsDominant]
    [g.IsOver (Y ↘ Spec (.of k)) (Z ↘ Spec (.of k))] :
    haveI : (f.comp g).IsOver (X ↘ Spec (.of k)) (Z ↘ Spec (.of k)) :=
      isOver_comp (sY := Y ↘ Spec (.of k)) f inferInstance g inferInstance
    (f.comp g).functionFieldAlgHom k =
      (f.functionFieldAlgHom k).comp (g.functionFieldAlgHom k) := by
  ext
  simp

end AlgebraicGeometry.Scheme
