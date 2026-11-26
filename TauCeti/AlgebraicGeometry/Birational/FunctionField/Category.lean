/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import TauCeti.AlgebraicGeometry.Birational.FunctionField.Determination

/-!
# The function-field functor on dominant rational maps

Let `k` be a commutative ring. Integral `k`-schemes locally of finite type over `k`, with dominant
`k`-rational maps as morphisms, form a category
`TauCeti.AlgebraicGeometry.DominantRationalMapCat k`: composition is Mathlib's
`Scheme.RationalMap.comp` and the identities are `Scheme.RationalMap.id`, with laws
`Scheme.RationalMap.comp_assoc`, `Scheme.RationalMap.id_comp` and `Scheme.RationalMap.comp_id`;
`Scheme.RationalMap.isOver_comp` keeps composites over `k`.

Pulling back rational functions, `f ↦ f^*`, is a functor to the opposite of the category of
commutative `k`-algebras (`TauCeti.AlgebraicGeometry.DominantRationalMapCat.functionFieldFunctor`),
by functoriality of `Scheme.RationalMap.functionFieldAlgHom`. By determination
(`Scheme.RationalMap.equivFunctionFieldAlgHom`) it is fully faithful
(`TauCeti.AlgebraicGeometry.DominantRationalMapCat.functionFieldFunctorFullyFaithful`): every
`k`-algebra map `k(Y) → k(X)` is the pullback along exactly one dominant `k`-rational map
`X ⤏ Y`.

## Main definitions

* `TauCeti.AlgebraicGeometry.DominantRationalMapCat k`: integral `k`-schemes locally of finite
  type over `k`, with dominant `k`-rational maps.
* `TauCeti.AlgebraicGeometry.DominantRationalMapCat.functionFieldFunctor k`: the function-field
  functor `X ↦ k(X)` to `(CommAlgCat k)ᵒᵖ`.
* `TauCeti.AlgebraicGeometry.DominantRationalMapCat.functionFieldFunctorFullyFaithful k`: it is
  fully faithful.

## References

* R. Hartshorne, *Algebraic Geometry*, GTM 52, Springer, 1977, Theorem I.4.4.
-/

public section

open CategoryTheory AlgebraicGeometry Opposite

universe u

namespace TauCeti.AlgebraicGeometry

variable (k : Type u) [CommRing k]

/-- Integral schemes over `Spec k`, locally of finite type over `k`, with the dominant
`k`-rational maps as morphisms. -/
structure DominantRationalMapCat where
  /-- The underlying scheme. -/
  toScheme : Scheme.{u}
  [over : toScheme.Over (Spec (.of k))]
  [isIntegral : IsIntegral toScheme]
  [locallyOfFiniteType : LocallyOfFiniteType (toScheme ↘ Spec (.of k))]

attribute [instance] DominantRationalMapCat.over DominantRationalMapCat.isIntegral
  DominantRationalMapCat.locallyOfFiniteType

namespace DominantRationalMapCat

variable {k}

/-- The type of morphisms in `DominantRationalMapCat k`: the dominant `k`-rational maps. -/
@[ext]
structure Hom (X Y : DominantRationalMapCat k) where
  /-- The underlying rational map. -/
  toRationalMap : X.toScheme ⤏ Y.toScheme
  [isDominant : toRationalMap.IsDominant]
  [isOver : toRationalMap.IsOver (X.toScheme ↘ Spec (.of k)) (Y.toScheme ↘ Spec (.of k))]

attribute [instance] Hom.isDominant Hom.isOver

/-- Integral `k`-schemes locally of finite type form a category with the dominant `k`-rational
maps as morphisms. -/
noncomputable instance : Category (DominantRationalMapCat k) where
  Hom := Hom
  id X := ⟨Scheme.RationalMap.id X.toScheme⟩
  comp f g :=
    haveI := Scheme.RationalMap.isOver_comp (sX := _ ↘ Spec (.of k)) (sY := _ ↘ Spec (.of k))
      (sZ := _ ↘ Spec (.of k)) f.toRationalMap inferInstance g.toRationalMap inferInstance
    ⟨f.toRationalMap.comp g.toRationalMap⟩
  id_comp _ := Hom.ext (Scheme.RationalMap.id_comp _)
  comp_id _ := Hom.ext (Scheme.RationalMap.comp_id _)
  assoc _ _ _ := Hom.ext (Scheme.RationalMap.comp_assoc _ _ _)

@[simp]
lemma id_toRationalMap (X : DominantRationalMapCat k) :
    Hom.toRationalMap (𝟙 X) = Scheme.RationalMap.id X.toScheme :=
  (rfl)

@[simp]
lemma comp_toRationalMap {X Y Z : DominantRationalMapCat k} (f : X ⟶ Y) (g : Y ⟶ Z) :
    Hom.toRationalMap (f ≫ g) = (Hom.toRationalMap f).comp (Hom.toRationalMap g) :=
  (rfl)

@[ext]
lemma hom_ext {X Y : DominantRationalMapCat k} {f g : X ⟶ Y}
    (h : Hom.toRationalMap f = Hom.toRationalMap g) : f = g :=
  Hom.ext h

variable (k) in
/-- **The function-field functor**: an integral `k`-scheme goes to its function field, and a
dominant `k`-rational map `f : X ⤏ Y` to its pullback of rational functions
`f^* : k(Y) → k(X)`. -/
@[expose, simps obj]
noncomputable def functionFieldFunctor : DominantRationalMapCat k ⥤ (CommAlgCat.{u} k)ᵒᵖ where
  obj X := op (CommAlgCat.of k X.toScheme.functionField)
  map f := (CommAlgCat.ofHom ((Hom.toRationalMap f).functionFieldAlgHom k)).op
  map_id X := by
    apply Quiver.Hom.unop_inj
    ext : 1
    exact Scheme.RationalMap.functionFieldAlgHom_id k
  map_comp f g := by
    apply Quiver.Hom.unop_inj
    ext : 1
    exact Scheme.RationalMap.functionFieldAlgHom_comp k (Hom.toRationalMap f) (Hom.toRationalMap g)

@[simp]
lemma functionFieldFunctor_map_unop_hom {X Y : DominantRationalMapCat k} (f : X ⟶ Y) :
    ((functionFieldFunctor k).map f).unop.hom = (Hom.toRationalMap f).functionFieldAlgHom k :=
  (rfl)

variable (k) in
/-- **Determination, categorically**: the function-field functor is fully faithful. Every
`k`-algebra map `k(Y) → k(X)` is the pullback of rational functions along exactly one dominant
`k`-rational map `X ⤏ Y` (`Scheme.RationalMap.equivFunctionFieldAlgHom`). -/
noncomputable def functionFieldFunctorFullyFaithful : (functionFieldFunctor k).FullyFaithful where
  preimage {X Y} φ :=
    let f := (Scheme.RationalMap.equivFunctionFieldAlgHom k).symm
      (φ.unop.hom : Y.toScheme.functionField →ₐ[k] X.toScheme.functionField)
    { toRationalMap := f.val, isDominant := f.prop.1, isOver := f.prop.2 }
  map_preimage φ := by
    apply Quiver.Hom.unop_inj
    ext : 1
    rw [functionFieldFunctor_map_unop_hom, ← Scheme.RationalMap.equivFunctionFieldAlgHom_apply]
    exact (Scheme.RationalMap.equivFunctionFieldAlgHom k).apply_symm_apply _
  preimage_map f := by
    apply hom_ext
    dsimp only
    rw [functionFieldFunctor_map_unop_hom, ← Scheme.RationalMap.equivFunctionFieldAlgHom_apply,
      Equiv.symm_apply_apply]

instance : (functionFieldFunctor k).Full := (functionFieldFunctorFullyFaithful k).full

instance : (functionFieldFunctor k).Faithful := (functionFieldFunctorFullyFaithful k).faithful

end DominantRationalMapCat

end TauCeti.AlgebraicGeometry
