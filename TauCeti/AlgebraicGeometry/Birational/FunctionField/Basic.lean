/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Birational.Composition
public import TauCeti.AlgebraicGeometry.Birational.RationalMap.Basic
public import TauCeti.AlgebraicGeometry.Morphisms.Dominant

/-!
# Pullback of function fields along a dominant rational map

A dominant rational map `f : X ⤏ Y` of irreducible schemes sends the generic point of `X` to the
generic point of `Y`: Mathlib's `Scheme.RationalMap.fromFunctionField f : Spec K(X) ⟶ Y` hits the
generic point of `Y`, and its map of stalks there is the *pullback of rational functions*
`f^* : K(Y) ⟶ K(X)` (`AlgebraicGeometry.Scheme.RationalMap.functionFieldMap`). It is
characterized by `Spec f^* ≫ (Spec K(Y) ⟶ Y) = f.fromFunctionField`, so it does not depend on a
representative of `f`, and for an integral source it determines `f`. For the rational map of a
dominant morphism it is Tau Ceti's `AlgebraicGeometry.Scheme.Hom.functionFieldMap`, and for
dominant rational maps `f` and `g` it is contravariantly functorial for Mathlib's composition of
rational maps, `(g ∘ f)^* = f^* ∘ g^*`. The description of the composite at the generic point,
`(g ∘ f).fromFunctionField = Spec f^* ≫ g.fromFunctionField`, only needs `f` to be dominant.

The characterization and functoriality lemmas are modelled on those of the pullback along a
dominant morphism in `TauCeti.AlgebraicGeometry.Morphisms.Dominant`:
`AlgebraicGeometry.Scheme.Hom.SpecMap_functionFieldMap_fromSpecStalk`,
`AlgebraicGeometry.Scheme.Hom.eq_functionFieldMap_iff` and
`AlgebraicGeometry.Scheme.Hom.functionFieldMap_comp`.

## Main definitions

* `AlgebraicGeometry.Scheme.RationalMap.functionFieldMap`: the pullback `f^* : K(Y) ⟶ K(X)` of
  rational functions along a dominant rational map of irreducible schemes.

## Main results

* `AlgebraicGeometry.Scheme.RationalMap.isDominant_iff_fromFunctionField_closedPoint`: a rational
  map of irreducible schemes is dominant exactly when it sends the closed point of `Spec K(X)` to
  the generic point of `Y`, and
  `AlgebraicGeometry.Scheme.RationalMap.isDominant_of_fromFunctionField_eq`: a rational map whose
  restriction to `Spec K(X)` factors through `Spec K(Y)` is dominant.
* `AlgebraicGeometry.Scheme.RationalMap.SpecMap_functionFieldMap_fromSpecStalk` and
  `AlgebraicGeometry.Scheme.RationalMap.eq_functionFieldMap_iff`: the characterization of `f^*`,
  and `AlgebraicGeometry.Scheme.RationalMap.eq_of_functionFieldMap_eq`: a dominant rational map
  from an integral scheme is determined by `f^*`.
* `AlgebraicGeometry.Scheme.Hom.functionFieldMap_toRationalMap`: for a dominant morphism, `f^*`
  is the pullback of rational functions along the morphism.
* `AlgebraicGeometry.Scheme.RationalMap.functionFieldMap_id` and
  `AlgebraicGeometry.Scheme.RationalMap.functionFieldMap_comp`: functoriality, for dominant `f`
  and `g`.
* `AlgebraicGeometry.Scheme.RationalMap.comp_eq_id_of_comp_eq_id`: a one-sided inverse of a
  dominant rational map of integral schemes by a dominant rational map is two-sided.

## References

* The Stacks Project, Tag 0BXN.
-/

public section

open CategoryTheory IsLocalRing

universe u

namespace AlgebraicGeometry.Scheme

variable {X Y Z : Scheme.{u}}

/-- A partial map `f` from an irreducible scheme sends the closed point of `Spec K(X)` to the
image under `f.hom` of the generic point of `X`, which lies in the domain of `f`. -/
theorem PartialMap.fromFunctionField_closedPoint_eq_hom [IrreducibleSpace X] (f : X.PartialMap Y) :
    f.fromFunctionField (closedPoint _) = f.hom ⟨genericPoint X, f.genericPoint_mem_domain⟩ := by
  have hp : f.domain.fromSpecStalkOfMem (genericPoint X) f.genericPoint_mem_domain
      (closedPoint _) = ⟨genericPoint X, f.genericPoint_mem_domain⟩ := by
    apply f.domain.ι.isOpenEmbedding.injective
    -- evaluate `fromSpecStalkOfMem ≫ ι = fromSpecStalk` at the closed point
    have h := congr($(Opens.fromSpecStalkOfMem_ι f.domain _ f.genericPoint_mem_domain)
      (closedPoint _))
    exact (Scheme.Hom.comp_apply _ _ _).symm.trans (h.trans fromSpecStalk_closedPoint)
  exact (Scheme.Hom.comp_apply _ _ _).trans (congrArg f.hom hp)

section Irreducible

variable [IrreducibleSpace X] [IrreducibleSpace Y]

/-- The underlying morphism of a partial map `f` of irreducible schemes is dominant exactly when it
sends the generic point of `X`, which lies in the domain of `f`, to the generic point of `Y`. -/
theorem PartialMap.isDominant_hom_iff_genericPoint_eq (f : X.PartialMap Y) :
    IsDominant f.hom ↔ f.hom ⟨genericPoint X, f.genericPoint_mem_domain⟩ = genericPoint Y := by
  have : Nonempty f.domain := f.dense_domain.nonempty.to_subtype
  have : IrreducibleSpace f.domain := f.domain.ι.isOpenEmbedding.irreducibleSpace
  -- the generic point of `X` is the generic point of the domain
  have hη : (⟨genericPoint X, f.genericPoint_mem_domain⟩ : f.domain) = genericPoint f.domain :=
    f.domain.ι.isOpenEmbedding.injective f.domain.ι.genericPoint_eq_of_isDominant.symm
  rw [hη, isDominant_iff_genericPoint_eq]

/-- A partial map of irreducible schemes whose underlying morphism is dominant sends the closed
point of `Spec K(X)` to the generic point of `Y`. -/
theorem PartialMap.fromFunctionField_closedPoint (f : X.PartialMap Y) [IsDominant f.hom] :
    f.fromFunctionField (closedPoint _) = genericPoint Y :=
  f.fromFunctionField_closedPoint_eq_hom.trans (f.isDominant_hom_iff_genericPoint_eq.mp ‹_›)

/-- A dominant rational map of irreducible schemes sends the closed point of `Spec K(X)` to the
generic point of `Y`. -/
theorem RationalMap.fromFunctionField_closedPoint (f : X ⤏ Y) [f.IsDominant] :
    f.fromFunctionField (closedPoint _) = genericPoint Y := by
  obtain ⟨g, rfl⟩ := f.exists_rep
  have : IsDominant g.hom := g.isDominant_toRationalMap_iff.mp ‹_›
  exact g.fromFunctionField_closedPoint

/-- A rational map of irreducible schemes is dominant exactly when it sends the closed point of
`Spec K(X)` to the generic point of `Y`. -/
theorem RationalMap.isDominant_iff_fromFunctionField_closedPoint (f : X ⤏ Y) :
    f.IsDominant ↔ f.fromFunctionField (closedPoint _) = genericPoint Y := by
  refine ⟨fun _ ↦ f.fromFunctionField_closedPoint, fun h ↦ ?_⟩
  obtain ⟨g, rfl⟩ := f.exists_rep
  rw [fromFunctionField_toRationalMap, g.fromFunctionField_closedPoint_eq_hom] at h
  exact g.isDominant_toRationalMap_iff.mpr (g.isDominant_hom_iff_genericPoint_eq.mpr h)

/-- **A rational map whose restriction to `Spec K(X)` factors through `Spec K(Y)` is dominant.**
If `f.fromFunctionField = Spec φ ≫ (Spec K(Y) ⟶ Y)` for a ring map `φ : K(Y) ⟶ K(X)`, then `f`
sends the closed point of `Spec K(X)` into the image of `Spec K(Y)`, whose only point is the
generic point of `Y`. -/
theorem RationalMap.isDominant_of_fromFunctionField_eq (f : X ⤏ Y)
    (φ : Y.functionField ⟶ X.functionField)
    (h : f.fromFunctionField = Spec.map φ ≫ Y.fromSpecStalk (genericPoint Y)) : f.IsDominant := by
  rw [isDominant_iff_fromFunctionField_closedPoint, h]
  exact eq_genericPoint_of_mem_range_fromSpecStalk ⟨_, (Scheme.Hom.comp_apply _ _ _).symm⟩

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
  simp only [functionFieldMap, Spec.map_comp, Category.assoc,
    SpecMap_stalkSpecializes_fromSpecStalk, Spec_stalkClosedPointTo_fromSpecStalk]

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
  refine ((RationalMap.eq_functionFieldMap_iff _ _).mpr ?_).symm
  simp only [SpecMap_functionFieldMap_fromSpecStalk, RationalMap.fromFunctionField_toRationalMap,
    PartialMap.fromFunctionField, PartialMap.fromSpecStalkOfMem_toPartialMap]

/-- Equal dominant rational maps have equal pullbacks of rational functions, whatever the
`IsDominant` instances: rewriting along `f = g` is blocked by the instance argument. -/
theorem RationalMap.functionFieldMap_congr {f g : X ⤏ Y} [f.IsDominant] [g.IsDominant]
    (h : f = g) : f.functionFieldMap = g.functionFieldMap := by
  subst h
  rfl

/-- The pullback of rational functions along the identity rational map is the identity. -/
theorem RationalMap.functionFieldMap_id : (RationalMap.id X).functionFieldMap = 𝟙 _ :=
  (Hom.functionFieldMap_toRationalMap (𝟙 X)).trans Hom.functionFieldMap_id

/-- The morphism `Spec K(X) ⟶ Z` of a composite `g ∘ f` of partial maps, with the underlying
morphism of `f` dominant, is `Spec f^*` followed by the morphism `Spec K(Y) ⟶ Z` of `g`. -/
theorem PartialMap.fromFunctionField_comp (f : X.PartialMap Y) [IsDominant f.hom]
    (g : Y.PartialMap Z) :
    (f.comp g).fromFunctionField =
      Spec.map f.toRationalMap.functionFieldMap ≫ g.fromFunctionField := by
  have hf := f.toRationalMap.SpecMap_functionFieldMap_fromSpecStalk
  rw [RationalMap.fromFunctionField_toRationalMap] at hf
  have hX := (f.comp g).genericPoint_mem_domain
  have hY := g.genericPoint_mem_domain
  -- the two maps `Spec K(X) ⟶ f.domain` agree, since they agree after the inclusion of `f.domain`
  have hdom : (f.domain.ι ''ᵁ f.hom ⁻¹ᵁ g.domain).fromSpecStalkOfMem (genericPoint X) hX ≫
      (f.domain.ι.isoImage _).inv ≫ (f.hom ⁻¹ᵁ g.domain).ι =
      f.domain.fromSpecStalkOfMem (genericPoint X) f.genericPoint_mem_domain := by
    rw [← cancel_mono f.domain.ι]
    simp only [Category.assoc, Hom.isoImage_inv_ι, Opens.fromSpecStalkOfMem_ι]
    exact Opens.fromSpecStalkOfMem_ι (f.domain.ι ''ᵁ f.hom ⁻¹ᵁ g.domain) _ hX
  have key : (f.domain.ι ''ᵁ f.hom ⁻¹ᵁ g.domain).fromSpecStalkOfMem (genericPoint X) hX ≫
      (f.domain.ι.isoImage _).inv ≫ f.hom ∣_ g.domain =
      Spec.map f.toRationalMap.functionFieldMap ≫
        g.domain.fromSpecStalkOfMem (genericPoint Y) hY := by
    rw [← cancel_mono g.domain.ι]
    simp only [Category.assoc, morphismRestrict_ι, Opens.fromSpecStalkOfMem_ι, hf]
    rw [reassoc_of% hdom, PartialMap.fromFunctionField, PartialMap.fromSpecStalkOfMem]
  simp only [PartialMap.fromFunctionField, PartialMap.fromSpecStalkOfMem, PartialMap.comp_hom,
    Opens.fromSpecStalkOfMem, Category.assoc] at key ⊢
  exact (reassoc_of% key) g.hom

/-- The morphism `Spec K(X) ⟶ Z` of a composite `g ∘ f` of rational maps, with `f` dominant, is
`Spec f^*` followed by the morphism `Spec K(Y) ⟶ Z` of `g`. -/
theorem RationalMap.fromFunctionField_comp (f : X ⤏ Y) [f.IsDominant] (g : Y ⤏ Z) :
    (f.comp g).fromFunctionField = Spec.map f.functionFieldMap ≫ g.fromFunctionField := by
  obtain ⟨f, rfl⟩ := f.exists_rep
  obtain ⟨g, rfl⟩ := g.exists_rep
  have : IsDominant f.hom := f.isDominant_toRationalMap_iff.mp ‹_›
  simp only [toRationalMap_comp, fromFunctionField_toRationalMap,
    PartialMap.fromFunctionField_comp]

/-- **Functoriality of the pullback of rational functions**: `(g ∘ f)^* = f^* ∘ g^*` for dominant
rational maps `f : X ⤏ Y` and `g : Y ⤏ Z` of irreducible schemes. -/
@[simp]
theorem RationalMap.functionFieldMap_comp [IrreducibleSpace Z] (f : X ⤏ Y) [f.IsDominant]
    (g : Y ⤏ Z) [g.IsDominant] :
    (f.comp g).functionFieldMap = g.functionFieldMap ≫ f.functionFieldMap := by
  refine ((eq_functionFieldMap_iff _ _).mpr ?_).symm
  simp only [Spec.map_comp, Category.assoc, SpecMap_functionFieldMap_fromSpecStalk,
    fromFunctionField_comp]

end Irreducible

/-- **A dominant rational map from an integral scheme is determined by its pullback of rational
functions.** No finiteness or separatedness is needed, since `f` is determined by
`f.fromFunctionField` (`RationalMap.eq_of_fromFunctionField_eq`). -/
theorem RationalMap.eq_of_functionFieldMap_eq [IsIntegral X] [IrreducibleSpace Y] {f g : X ⤏ Y}
    [f.IsDominant] [g.IsDominant] (h : f.functionFieldMap = g.functionFieldMap) : f = g :=
  eq_of_fromFunctionField_eq f g <| by
    rw [← SpecMap_functionFieldMap_fromSpecStalk, h, SpecMap_functionFieldMap_fromSpecStalk]

/-- **One-sided inverses are two-sided.** If `g ∘ f = id` for dominant rational maps
`f : X ⤏ Y` and `g : Y ⤏ X` of integral schemes, then `f ∘ g = id`: `f^*` is bijective with
inverse `g^*`, and a dominant rational map is determined by its pullback. -/
theorem RationalMap.comp_eq_id_of_comp_eq_id [IsIntegral X] [IsIntegral Y] (f : X ⤏ Y)
    [f.IsDominant] (g : Y ⤏ X) [g.IsDominant] (h : f.comp g = RationalMap.id X) :
    g.comp f = RationalMap.id Y := by
  have hfg : f.functionFieldMap.hom.comp g.functionFieldMap.hom = RingHom.id _ := by
    rw [← CommRingCat.hom_comp, ← functionFieldMap_comp, functionFieldMap_congr h,
      functionFieldMap_id, CommRingCat.hom_id]
  refine eq_of_functionFieldMap_eq ?_
  rw [functionFieldMap_comp, functionFieldMap_id]
  ext x
  exact Function.LeftInverse.rightInverse_of_injective (f := f.functionFieldMap.hom)
    (g := g.functionFieldMap.hom) (fun y => congr($hfg y)) f.functionFieldMap.hom.injective x

end AlgebraicGeometry.Scheme
