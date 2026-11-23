/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Birational.Composition
public import Mathlib.FieldTheory.Relrank
public import TauCeti.AlgebraicGeometry.Morphisms.Dominant
public import TauCeti.AlgebraicGeometry.Scheme.BaseAlgebra

/-!
# Pullback of function fields along a dominant rational map, and the topological degree

A dominant rational map `f : X ⤏ Y` of irreducible schemes sends the generic point of `X` to the
generic point of `Y`: Mathlib's `Scheme.RationalMap.fromFunctionField f : Spec K(X) ⟶ Y` hits the
generic point of `Y`, and its map of stalks there is the *pullback of rational functions*
`f^* : K(Y) ⟶ K(X)` (`AlgebraicGeometry.Scheme.RationalMap.functionFieldMap`). It is
characterized by `Spec f^* ≫ (Spec K(Y) ⟶ Y) = f.fromFunctionField`, so it does not depend on a
representative of `f`. For the rational map of a dominant morphism it is Tau Ceti's
`AlgebraicGeometry.Scheme.Hom.functionFieldMap`, and it is contravariantly functorial for
Mathlib's composition of rational maps, `(g ∘ f)^* = f^* ∘ g^*`. Over a base ring `k`, the
pullback along a `k`-rational map of integral schemes is a `k`-algebra map
(`AlgebraicGeometry.Scheme.RationalMap.functionFieldAlgHom`).

For integral `X` and `Y`, the *topological degree* `e(f) = [K(X) : f^*K(Y)]` is the dimension of
`K(X)` over the image of `f^*` (`AlgebraicGeometry.Scheme.RationalMap.topologicalDegree`). It
counts inseparable degree, and takes the junk value `0` when the extension is infinite, for
instance for the projection `ℙ² ⤏ ℙ¹` from a point. It is multiplicative under composition
without any hypothesis on dimensions, because the tower law for `Module.finrank` holds with the
junk value.

## Main definitions

* `AlgebraicGeometry.Scheme.RationalMap.functionFieldMap`: the pullback `f^* : K(Y) ⟶ K(X)` of
  rational functions along a dominant rational map of irreducible schemes.
* `AlgebraicGeometry.Scheme.RationalMap.functionFieldAlgHom`: the same map as a `k`-algebra
  homomorphism, for a `k`-rational map of integral `k`-schemes.
* `AlgebraicGeometry.Scheme.RationalMap.topologicalDegree`: the topological degree
  `[K(X) : f^*K(Y)]` of a dominant rational map of integral schemes.

## Main results

* `AlgebraicGeometry.Scheme.RationalMap.SpecMap_functionFieldMap_fromSpecStalk` and
  `AlgebraicGeometry.Scheme.RationalMap.eq_functionFieldMap_iff`: the characterization of `f^*`.
* `AlgebraicGeometry.Scheme.Hom.functionFieldMap_toRationalMap`: for a dominant morphism, `f^*`
  is the pullback of rational functions along the morphism.
* `AlgebraicGeometry.Scheme.RationalMap.functionFieldMap_id` and
  `AlgebraicGeometry.Scheme.RationalMap.functionFieldMap_comp`: functoriality.
* `AlgebraicGeometry.Scheme.RationalMap.topologicalDegree_id` and
  `AlgebraicGeometry.Scheme.RationalMap.topologicalDegree_comp`: `e(id) = 1` and
  `e(g ∘ f) = e(f)·e(g)`.

## References

* The Stacks Project, Tag 0BXN (the degree of a dominant generically finite morphism of integral
  schemes as the degree of the extension of function fields).
* T.-C. Dinh and N. Sibony, *Une borne supérieure pour l'entropie topologique d'une application
  rationnelle*, Ann. of Math. 161 (2005), for the topological degree of a rational map.
-/

public section

open CategoryTheory IsLocalRing

universe u

namespace AlgebraicGeometry.Scheme

variable {X Y Z : Scheme.{u}}

section Irreducible

variable [IrreducibleSpace X] [IrreducibleSpace Y]

/-- A partial map of irreducible schemes whose underlying morphism is dominant sends the closed
point of `Spec K(X)` to the generic point of `Y`. -/
theorem PartialMap.fromFunctionField_closedPoint (f : X.PartialMap Y) [IsDominant f.hom] :
    f.fromFunctionField (closedPoint _) = genericPoint Y := by
  have : Nonempty f.domain := f.dense_domain.nonempty.to_subtype
  have : IrreducibleSpace f.domain := f.domain.ι.isOpenEmbedding.irreducibleSpace
  have hη : genericPoint X ∈ f.domain :=
    (genericPoint_specializes _).mem_open f.domain.is_open' f.dense_domain.nonempty.some_mem
  have hp : f.domain.fromSpecStalkOfMem (genericPoint X) hη (closedPoint _) =
      genericPoint f.domain := f.domain.ι.isOpenEmbedding.injective <|
    (Scheme.Hom.comp_apply _ _ _).symm.trans <|
      congr($(Opens.fromSpecStalkOfMem_ι f.domain _ hη) _).trans <|
        fromSpecStalk_closedPoint.trans f.domain.ι.genericPoint_eq_of_isDominant.symm
  exact (Scheme.Hom.comp_apply _ _ _).trans
    ((congrArg f.hom hp).trans f.hom.genericPoint_eq_of_isDominant)

/-- A dominant rational map of irreducible schemes sends the closed point of `Spec K(X)` to the
generic point of `Y`. -/
theorem RationalMap.fromFunctionField_closedPoint (f : X ⤏ Y) [f.IsDominant] :
    f.fromFunctionField (closedPoint _) = genericPoint Y := by
  obtain ⟨g, rfl⟩ := f.exists_rep
  have : IsDominant g.hom := g.isDominant_toRationalMap_iff.mp ‹_›
  exact g.fromFunctionField_closedPoint

/-- The **pullback of rational functions** `f^* : K(Y) ⟶ K(X)` along a dominant rational map
`f : X ⤏ Y` of irreducible schemes: the map of stalks of `f.fromFunctionField : Spec K(X) ⟶ Y`
at the closed point, which it sends to the generic point of `Y`
(`RationalMap.fromFunctionField_closedPoint`). It is characterized by
`RationalMap.SpecMap_functionFieldMap_fromSpecStalk` and `RationalMap.eq_functionFieldMap_iff`. -/
noncomputable def RationalMap.functionFieldMap (f : X ⤏ Y) [f.IsDominant] :
    Y.functionField ⟶ X.functionField :=
  Y.presheaf.stalkSpecializes (specializes_of_eq f.fromFunctionField_closedPoint) ≫
    stalkClosedPointTo f.fromFunctionField

/-- **The pullback of rational functions describes the rational map at the generic point**: for
a dominant rational map `f : X ⤏ Y` of irreducible schemes, `Spec f^*` followed by the canonical
morphism `Spec K(Y) ⟶ Y` is `f.fromFunctionField : Spec K(X) ⟶ Y`. -/
@[reassoc (attr := simp)]
theorem RationalMap.SpecMap_functionFieldMap_fromSpecStalk (f : X ⤏ Y) [f.IsDominant] :
    Spec.map f.functionFieldMap ≫ Y.fromSpecStalk (genericPoint Y) = f.fromFunctionField := by
  rw [functionFieldMap, Spec.map_comp, Category.assoc, SpecMap_stalkSpecializes_fromSpecStalk,
    Spec_stalkClosedPointTo_fromSpecStalk]

/-- **The pullback of rational functions is unique**: a homomorphism `φ : K(Y) ⟶ K(X)` is the
pullback `f^*` along a dominant rational map `f : X ⤏ Y` of irreducible schemes exactly when
`Spec φ` followed by the canonical morphism `Spec K(Y) ⟶ Y` is `f.fromFunctionField`. -/
theorem RationalMap.eq_functionFieldMap_iff (f : X ⤏ Y) [f.IsDominant]
    (φ : Y.functionField ⟶ X.functionField) :
    φ = f.functionFieldMap ↔
      Spec.map φ ≫ Y.fromSpecStalk (genericPoint Y) = f.fromFunctionField := by
  rw [← f.SpecMap_functionFieldMap_fromSpecStalk, cancel_mono, Spec.map_inj]

/-- The pullback of rational functions along the rational map of a dominant morphism `g` is the
pullback of rational functions along `g`. -/
@[simp]
theorem Hom.functionFieldMap_toRationalMap (g : X ⟶ Y) [IsDominant g] :
    g.toRationalMap.functionFieldMap = g.functionFieldMap := by
  rw [eq_comm, RationalMap.eq_functionFieldMap_iff, RationalMap.fromFunctionField_toRationalMap,
    PartialMap.fromFunctionField, PartialMap.fromSpecStalkOfMem_toPartialMap,
    SpecMap_functionFieldMap_fromSpecStalk]

/-- The pullback of rational functions along the identity rational map is the identity. -/
theorem RationalMap.functionFieldMap_id : (RationalMap.id X).functionFieldMap = 𝟙 _ :=
  (Hom.functionFieldMap_toRationalMap (𝟙 X)).trans Hom.functionFieldMap_id

/-- The morphism `Spec K(X) ⟶ Z` of a composite `g ∘ f` of partial maps is `Spec f^*` followed by
the morphism `Spec K(Y) ⟶ Z` of `g`. -/
theorem PartialMap.fromFunctionField_comp (f : X.PartialMap Y) [IsDominant f.hom]
    (g : Y.PartialMap Z) :
    (f.comp g).fromFunctionField =
      Spec.map f.toRationalMap.functionFieldMap ≫ g.fromFunctionField := by
  have hf := f.toRationalMap.SpecMap_functionFieldMap_fromSpecStalk
  rw [RationalMap.fromFunctionField_toRationalMap] at hf
  have hX : genericPoint X ∈ f.domain.ι ''ᵁ f.hom ⁻¹ᵁ g.domain :=
    (genericPoint_specializes _).mem_open (f.comp g).domain.is_open'
      (f.comp g).dense_domain.nonempty.some_mem
  have hY : genericPoint Y ∈ g.domain :=
    (genericPoint_specializes _).mem_open g.domain.is_open' g.dense_domain.nonempty.some_mem
  have key : (f.domain.ι ''ᵁ f.hom ⁻¹ᵁ g.domain).fromSpecStalkOfMem (genericPoint X) hX ≫
      (f.domain.ι.isoImage _).inv ≫ f.hom ∣_ g.domain =
      Spec.map f.toRationalMap.functionFieldMap ≫
        g.domain.fromSpecStalkOfMem (genericPoint Y) hY := by
    rw [← cancel_mono g.domain.ι, Category.assoc, Category.assoc, morphismRestrict_ι,
      Category.assoc, Opens.fromSpecStalkOfMem_ι, hf, PartialMap.fromFunctionField,
      PartialMap.fromSpecStalkOfMem, ← Category.assoc, ← Category.assoc]
    congr 1
    rw [← cancel_mono f.domain.ι]
    simp [Opens.fromSpecStalkOfMem_ι]
  exact (reassoc_of% key) g.hom

/-- The morphism `Spec K(X) ⟶ Z` of a composite `g ∘ f` of rational maps is `Spec f^*` followed
by the morphism `Spec K(Y) ⟶ Z` of `g`. -/
theorem RationalMap.fromFunctionField_comp (f : X ⤏ Y) [f.IsDominant] (g : Y ⤏ Z) :
    (f.comp g).fromFunctionField = Spec.map f.functionFieldMap ≫ g.fromFunctionField := by
  obtain ⟨f, rfl⟩ := f.exists_rep
  obtain ⟨g, rfl⟩ := g.exists_rep
  have : IsDominant f.hom := f.isDominant_toRationalMap_iff.mp ‹_›
  rw [toRationalMap_comp, fromFunctionField_toRationalMap, fromFunctionField_toRationalMap,
    PartialMap.fromFunctionField_comp]

/-- **Functoriality of the pullback of rational functions**: `(g ∘ f)^* = f^* ∘ g^*` for dominant
rational maps `f : X ⤏ Y` and `g : Y ⤏ Z` of irreducible schemes. -/
theorem RationalMap.functionFieldMap_comp [IrreducibleSpace Z] (f : X ⤏ Y) [f.IsDominant]
    (g : Y ⤏ Z) [g.IsDominant] :
    (f.comp g).functionFieldMap = g.functionFieldMap ≫ f.functionFieldMap := by
  rw [eq_comm, eq_functionFieldMap_iff, Spec.map_comp, Category.assoc,
    SpecMap_functionFieldMap_fromSpecStalk, fromFunctionField_comp]

end Irreducible

section Over

variable {S : Scheme.{u}} [X.Over S] [Y.Over S]

/-- The rational map of an `S`-morphism is an `S`-rational map. -/
instance Hom.isOver_toRationalMap (g : X ⟶ Y) [g.IsOver S] :
    g.toRationalMap.IsOver (X ↘ S) (Y ↘ S) :=
  haveI := Hom.isOver_toPartialMap (comp_over g S)
  inferInstance

/-- For an `S`-rational map `f : X ⤏ Y` from an irreducible scheme, the morphism
`Spec K(X) ⟶ Y` of `f` is a morphism over `S`. -/
theorem RationalMap.fromFunctionField_comp_over [IrreducibleSpace X] (f : X ⤏ Y)
    [f.IsOver (X ↘ S) (Y ↘ S)] :
    f.fromFunctionField ≫ Y ↘ S = X.fromSpecStalk (genericPoint X) ≫ X ↘ S := by
  obtain ⟨g, hg, rfl⟩ := f.exists_partialMap_over (X ↘ S) (Y ↘ S)
  rw [fromFunctionField_toRationalMap, PartialMap.fromFunctionField,
    PartialMap.fromSpecStalkOfMem, Category.assoc, hg.over, ← Category.assoc,
    Opens.fromSpecStalkOfMem_ι]

end Over

section BaseRing

variable (k : Type u) [CommRing k] [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
  [Z.Over (Spec (.of k))] [IsIntegral X] [IsIntegral Y] [IsIntegral Z]

/-- The pullback of rational functions along a dominant `k`-rational map of integral schemes over
`Spec k` is compatible with the `k`-algebra structures of the function fields. -/
theorem RationalMap.functionFieldMap_algebraMap (f : X ⤏ Y) [f.IsDominant]
    [f.IsOver (X ↘ Spec (.of k)) (Y ↘ Spec (.of k))] (c : k) :
    f.functionFieldMap (algebraMap k Y.functionField c) = algebraMap k X.functionField c := by
  have h : Spec.map (CommRingCat.ofHom (algebraMap k Y.functionField) ≫ f.functionFieldMap) =
      Spec.map (CommRingCat.ofHom (algebraMap k X.functionField)) := by
    rw [Spec.map_comp, ← Scheme.fromSpecStalk_genericPoint_comp_over,
      ← Scheme.fromSpecStalk_genericPoint_comp_over,
      SpecMap_functionFieldMap_fromSpecStalk_assoc, fromFunctionField_comp_over]
  exact congr($(Spec.map_injective h) c)

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

/-- **Functoriality of the `k`-algebra pullback**: `(g ∘ f)^* = f^* ∘ g^*` for dominant
`k`-rational maps `f : X ⤏ Y` and `g : Y ⤏ Z` of integral schemes over `Spec k`. -/
theorem RationalMap.functionFieldAlgHom_comp (f : X ⤏ Y) [f.IsDominant]
    [f.IsOver (X ↘ Spec (.of k)) (Y ↘ Spec (.of k))] (g : Y ⤏ Z) [g.IsDominant]
    [g.IsOver (Y ↘ Spec (.of k)) (Z ↘ Spec (.of k))] :
    haveI : (f.comp g).IsOver (X ↘ Spec (.of k)) (Z ↘ Spec (.of k)) :=
      isOver_comp (sY := Y ↘ Spec (.of k)) f inferInstance g inferInstance
    (f.comp g).functionFieldAlgHom k =
      (f.functionFieldAlgHom k).comp (g.functionFieldAlgHom k) := by
  ext
  simp [functionFieldMap_comp]

end BaseRing

section TopologicalDegree

variable [IsIntegral X] [IsIntegral Y] [IsIntegral Z]

/-- The **topological degree** `e(f) = [K(X) : f^*K(Y)]` of a dominant rational map `f : X ⤏ Y`
of integral schemes: the dimension of `K(X)` over the image of the pullback of rational functions
`f^*`. It counts inseparable degree, and is `0` when `K(X)` is infinite-dimensional over
`f^*K(Y)`. -/
noncomputable def RationalMap.topologicalDegree (f : X ⤏ Y) [f.IsDominant] : ℕ :=
  Module.finrank f.functionFieldMap.hom.fieldRange X.functionField

/-- The topological degree of the rational map of a dominant morphism `g` is the dimension of
`K(X)` over the image of the pullback of rational functions along `g`. -/
theorem Hom.topologicalDegree_toRationalMap (g : X ⟶ Y) [IsDominant g] :
    g.toRationalMap.topologicalDegree =
      Module.finrank g.functionFieldMap.hom.fieldRange X.functionField := by
  rw [RationalMap.topologicalDegree, functionFieldMap_toRationalMap]

/-- The identity rational map has topological degree `1`. -/
@[simp]
theorem RationalMap.topologicalDegree_id : (RationalMap.id X).topologicalDegree = 1 := by
  rw [topologicalDegree, functionFieldMap_id, CommRingCat.hom_id,
    RingHom.fieldRange_eq_top_iff.mpr Function.surjective_id, ← Subfield.relfinrank_top_right,
    Subfield.relfinrank_self]

/-- **Multiplicativity of the topological degree**: `e(g ∘ f) = e(f)·e(g)` for dominant rational
maps `f : X ⤏ Y` and `g : Y ⤏ Z` of integral schemes. No hypothesis on dimensions is needed: if
one side involves an infinite extension, both sides are the junk value `0`. -/
theorem RationalMap.topologicalDegree_comp (f : X ⤏ Y) [f.IsDominant] (g : Y ⤏ Z)
    [g.IsDominant] :
    (f.comp g).topologicalDegree = f.topologicalDegree * g.topologicalDegree := by
  have hle : (f.functionFieldMap.hom.comp g.functionFieldMap.hom).fieldRange ≤
      f.functionFieldMap.hom.fieldRange := by
    rintro _ ⟨x, rfl⟩
    exact ⟨_, rfl⟩
  rw [topologicalDegree, topologicalDegree, topologicalDegree, functionFieldMap_comp,
    CommRingCat.hom_comp, ← Subfield.relfinrank_top_right, ← Subfield.relfinrank_top_right,
    ← Subfield.relfinrank_top_right, ← Subfield.relfinrank_mul_relfinrank hle le_top, mul_comm]
  congr 1
  rw [← RingHom.map_fieldRange, RingHom.fieldRange_eq_map f.functionFieldMap.hom,
    Subfield.relfinrank_map_map]

end TopologicalDegree

end AlgebraicGeometry.Scheme
