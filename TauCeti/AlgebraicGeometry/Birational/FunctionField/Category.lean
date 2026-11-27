/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import TauCeti.AlgebraicGeometry.Birational.FunctionField.Determination
public import TauCeti.AlgebraicGeometry.Morphisms.FiniteType.Basic
public import TauCeti.AlgebraicGeometry.Scheme.FunctionField
public import TauCeti.RingTheory.EssentialFiniteness

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
(`TauCeti.AlgebraicGeometry.DominantRationalMapCat.fullyFaithfulFunctionFieldFunctor`): every
`k`-algebra map `k(Y) → k(X)` is the pullback along exactly one dominant `k`-rational map
`X ⤏ Y`.

Over a field `k`, its essential image is the finitely generated field extensions of `k`, written
as fields essentially of finite type over `k` as in Mathlib's `IntermediateField.fg_top_iff`
(`TauCeti.AlgebraicGeometry.DominantRationalMapCat.essImage_functionFieldFunctor`). Such a field
`L` is the fraction field of a finitely generated `k`-subalgebra `A`, and `Spec A` has function
field `L`.

## Main definitions

* `TauCeti.AlgebraicGeometry.DominantRationalMapCat k`: integral `k`-schemes locally of finite
  type over `k`, with dominant `k`-rational maps.
* `TauCeti.AlgebraicGeometry.DominantRationalMapCat.functionFieldFunctor k`: the function-field
  functor `X ↦ k(X)` to `(CommAlgCat k)ᵒᵖ`.
* `TauCeti.AlgebraicGeometry.DominantRationalMapCat.fullyFaithfulFunctionFieldFunctor k`: it is
  fully faithful.

## Main results

* `TauCeti.AlgebraicGeometry.DominantRationalMapCat.essImage_functionFieldFunctor`: over a
  field, the essential image is the fields essentially of finite type over `k`.

## References

* R. Hartshorne, *Algebraic Geometry*, GTM 52, Springer, 1977, Theorem I.4.4.
* [Stacks Project, Tag 0BXN](https://stacks.math.columbia.edu/tag/0BXN).
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
noncomputable def fullyFaithfulFunctionFieldFunctor : (functionFieldFunctor k).FullyFaithful where
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

/-- The dominant rational map recovered from a `k`-algebra map of function fields is
`Scheme.RationalMap.ofFunctionFieldAlgHom`. -/
@[simp]
lemma fullyFaithfulFunctionFieldFunctor_preimage_toRationalMap {X Y : DominantRationalMapCat k}
    (φ : (functionFieldFunctor k).obj X ⟶ (functionFieldFunctor k).obj Y) :
    Hom.toRationalMap ((fullyFaithfulFunctionFieldFunctor k).preimage φ) =
      Scheme.RationalMap.ofFunctionFieldAlgHom k
        (φ.unop.hom : Y.toScheme.functionField →ₐ[k] X.toScheme.functionField) :=
  Scheme.RationalMap.equivFunctionFieldAlgHom_symm_apply_coe k _

instance : (functionFieldFunctor k).Full := (fullyFaithfulFunctionFieldFunctor k).full

instance : (functionFieldFunctor k).Faithful := (fullyFaithfulFunctionFieldFunctor k).faithful

section EssImage

variable {k : Type u} [Field k]

/-- A `k`-algebra isomorphic to the function field of an object of `DominantRationalMapCat k` is a
field essentially of finite type over `k`, by
`TauCeti.AlgebraicGeometry.essFiniteType_functionField`. -/
private lemma isField_essFiniteType_of_iso {L : CommAlgCat.{u} k} (X : DominantRationalMapCat k)
    (e : L ≅ CommAlgCat.of k X.toScheme.functionField) :
    IsField L ∧ Algebra.EssFiniteType k L := by
  let f := CommAlgCat.algEquivOfIso e
  refine ⟨f.toMulEquiv.isField (Field.toIsField X.toScheme.functionField), ?_⟩
  exact .of_surjective f.symm.toAlgHom f.symm.surjective

/-- A field `L` that is essentially of finite type over `k` is the function field of the affine
scheme of a finitely generated `k`-subalgebra `A` of `L` whose fraction field is `L`. -/
private lemma exists_iso_functionFieldFunctor_obj (L : Type u) [Field L] [Algebra k L]
    [Algebra.EssFiniteType k L] :
    ∃ X : DominantRationalMapCat k, Nonempty (CommAlgCat.of k L ≅
      CommAlgCat.of k X.toScheme.functionField) := by
  let A := Algebra.EssFiniteType.subalgebra k L
  have := Algebra.EssFiniteType.isFractionRing_subalgebra k L
  let _ : (Spec (.of A)).Over (Spec (.of k)) := ⟨Spec.algebraMap k A⟩
  have : LocallyOfFiniteType (Spec (.of A) ↘ Spec (.of k)) :=
    inferInstanceAs (LocallyOfFiniteType (Spec.algebraMap k A))
  let X : DominantRationalMapCat k := ⟨Spec (.of A)⟩
  exact ⟨X, ⟨(CommAlgCat.isoMk (Scheme.Hom.functionFieldAlgEquivOfIsOpenImmersion
    (𝟙 (Spec (.of A))) (Category.id_comp _) L)).symm⟩⟩

/-- **The essential image of the function-field functor** consists of the finitely generated field
extensions of `k`: a commutative `k`-algebra is isomorphic to the function field of an integral
`k`-scheme locally of finite type exactly when it is a field essentially of finite type over `k`
(Stacks Project, Tag 0BXN). -/
theorem essImage_functionFieldFunctor (L : CommAlgCat.{u} k) :
    (functionFieldFunctor k).essImage (op L) ↔ IsField L ∧ Algebra.EssFiniteType k L := by
  -- `(functionFieldFunctor k).obj X` is `op (CommAlgCat.of k k(X))` by definition.
  refine ⟨fun ⟨X, ⟨e⟩⟩ ↦ isField_essFiniteType_of_iso X
    (show L ≅ CommAlgCat.of k X.toScheme.functionField from e.unop), fun ⟨hL, _⟩ ↦ ?_⟩
  let _ := hL.toField
  obtain ⟨X, ⟨e⟩⟩ := exists_iso_functionFieldFunctor_obj (k := k) L
  exact ⟨X, ⟨show op (CommAlgCat.of k X.toScheme.functionField) ≅ op L from e.op⟩⟩

end EssImage

end DominantRationalMapCat

end TauCeti.AlgebraicGeometry
