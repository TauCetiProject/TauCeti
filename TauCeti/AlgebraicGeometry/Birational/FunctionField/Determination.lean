/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Birational.FunctionField.BaseAlgebra

/-!
# Dominant rational maps are determined by their pullback of function fields

Let `k` be a commutative ring and `X`, `Y` integral `k`-schemes with `Y` locally of finite type
over `k`. Every `k`-algebra homomorphism `φ : k(Y) → k(X)` is the pullback of rational functions
along a dominant `k`-rational map `X ⤏ Y`, namely
`AlgebraicGeometry.Scheme.RationalMap.ofFunctionFieldAlgHom k φ`, and that map is unique
(`AlgebraicGeometry.Scheme.RationalMap.eq_of_functionFieldAlgHom_eq`). So `f ↦ f^*` is a
bijection between dominant `k`-rational maps `X ⤏ Y` and `k`-algebra maps `k(Y) → k(X)`.

The rational map is Mathlib's `Scheme.RationalMap.ofFunctionField` of the `k`-morphism
`Spec φ ≫ (Spec k(Y) ⟶ Y)` from `Spec k(X)`, which is defined because `Y` is locally of finite
type. It is dominant because it sends the generic point of `X` into the image of
`Spec k(Y) ⟶ Y`, whose only point is the generic point of `Y`
(`AlgebraicGeometry.Scheme.RationalMap.isDominant_of_fromFunctionField_eq`).

## Main definitions

* `AlgebraicGeometry.Scheme.RationalMap.ofFunctionFieldAlgHom`: the dominant `k`-rational map
  whose pullback of rational functions is a given `k`-algebra map `k(Y) → k(X)`.

## Main results

* `AlgebraicGeometry.Scheme.RationalMap.isDominant_of_fromFunctionField_eq`: a rational map whose
  restriction to `Spec K(X)` factors through `Spec K(Y)` is dominant.
* `AlgebraicGeometry.Scheme.RationalMap.eq_of_functionFieldAlgHom_eq`: a dominant `k`-rational
  map is determined by its `k`-algebra pullback.
* `AlgebraicGeometry.Scheme.RationalMap.functionFieldAlgHom_ofFunctionFieldAlgHom` and
  `AlgebraicGeometry.Scheme.RationalMap.ofFunctionFieldAlgHom_functionFieldAlgHom`: the
  construction is inverse to the pullback.
* `AlgebraicGeometry.Scheme.RationalMap.exists_functionFieldAlgHom_eq`: **determination**, every
  `k`-algebra map of function fields is the pullback along a dominant `k`-rational map.
* `AlgebraicGeometry.Scheme.RationalMap.existsUnique_functionFieldAlgHom_eq`: and only one.
-/

public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme

variable {X Y : Scheme.{u}}

/-- **A rational map whose restriction to `Spec K(X)` factors through `Spec K(Y)` is dominant.**
If `f.fromFunctionField = Spec φ ≫ (Spec K(Y) ⟶ Y)` for a ring map `φ : K(Y) ⟶ K(X)`, then `f`
sends the closed point of `Spec K(X)` into the image of `Spec K(Y)`, whose only point is the
generic point of `Y`. -/
theorem RationalMap.isDominant_of_fromFunctionField_eq [IrreducibleSpace X] [IrreducibleSpace Y]
    (f : X ⤏ Y) (φ : Y.functionField ⟶ X.functionField)
    (h : f.fromFunctionField = Spec.map φ ≫ Y.fromSpecStalk (genericPoint Y)) : f.IsDominant := by
  rw [isDominant_iff_fromFunctionField_closedPoint]
  have hf : f.fromFunctionField (IsLocalRing.closedPoint _) ∈
      Set.range (Y.fromSpecStalk (genericPoint Y)) := by
    rw [h]
    exact ⟨_, (Scheme.Hom.comp_apply _ _ _).symm⟩
  rw [Scheme.range_fromSpecStalk] at hf
  exact (hf.antisymm (genericPoint_specializes _)).eq

variable (k : Type u) [CommRing k] [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))] [IsIntegral X]
  [IsIntegral Y]

/-- **A dominant `k`-rational map is determined by its `k`-algebra pullback**: dominant
`k`-rational maps `f g : X ⤏ Y` of integral `k`-schemes with `f^* = g^*` are equal. -/
theorem RationalMap.eq_of_functionFieldAlgHom_eq {f g : X ⤏ Y} [f.IsDominant] [g.IsDominant]
    [f.IsOver (X ↘ Spec (.of k)) (Y ↘ Spec (.of k))]
    [g.IsOver (X ↘ Spec (.of k)) (Y ↘ Spec (.of k))]
    (h : f.functionFieldAlgHom k = g.functionFieldAlgHom k) : f = g :=
  eq_of_functionFieldMap_eq <| CommRingCat.hom_ext <| RingHom.ext fun a ↦ by
    simpa only [functionFieldAlgHom_apply] using congr($h a)

variable [LocallyOfFiniteType (Y ↘ Spec (.of k))]

/-- **The rational map induced by a map of function fields**: for integral `k`-schemes `X` and
`Y` with `Y` locally of finite type over `k`, the dominant `k`-rational map `X ⤏ Y` whose
pullback of rational functions is the `k`-algebra map `φ : k(Y) → k(X)`
(`RationalMap.functionFieldAlgHom_ofFunctionFieldAlgHom`). It is Mathlib's
`RationalMap.ofFunctionField` of `Spec φ ≫ (Spec k(Y) ⟶ Y)`. -/
noncomputable def RationalMap.ofFunctionFieldAlgHom (φ : Y.functionField →ₐ[k] X.functionField) :
    X ⤏ Y :=
  ofFunctionField (X ↘ Spec (.of k)) (Y ↘ Spec (.of k))
    (Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ Y.fromSpecStalk (genericPoint Y))
    (specMap_comp_fromSpecStalk_genericPoint_comp_over k _ φ.commutes)

variable (φ : Y.functionField →ₐ[k] X.functionField)

/-- On `Spec K(X)`, `RationalMap.ofFunctionFieldAlgHom k φ` is `Spec φ ≫ (Spec K(Y) ⟶ Y)`. -/
theorem RationalMap.fromFunctionField_ofFunctionFieldAlgHom :
    (ofFunctionFieldAlgHom k φ).fromFunctionField =
      Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ Y.fromSpecStalk (genericPoint Y) :=
  fromFunctionField_ofFunctionField ..

/-- `RationalMap.ofFunctionFieldAlgHom k φ` is dominant. -/
instance : (RationalMap.ofFunctionFieldAlgHom k φ).IsDominant :=
  RationalMap.isDominant_of_fromFunctionField_eq _ _
    (RationalMap.fromFunctionField_ofFunctionFieldAlgHom k φ)

/-- `RationalMap.ofFunctionFieldAlgHom k φ` is a rational map over `k`. -/
instance :
    (RationalMap.ofFunctionFieldAlgHom k φ).IsOver (X ↘ Spec (.of k)) (Y ↘ Spec (.of k)) :=
  (RationalMap.equivFunctionFieldOver (X ↘ Spec (.of k)) (Y ↘ Spec (.of k))
    ⟨_, specMap_comp_fromSpecStalk_genericPoint_comp_over k _ φ.commutes⟩).property

/-- **The pullback of rational functions along `RationalMap.ofFunctionFieldAlgHom k φ` is
`φ`.** -/
@[simp]
theorem RationalMap.functionFieldMap_ofFunctionFieldAlgHom :
    (ofFunctionFieldAlgHom k φ).functionFieldMap = CommRingCat.ofHom φ.toRingHom :=
  ((eq_functionFieldMap_iff _ _).mpr (fromFunctionField_ofFunctionFieldAlgHom k φ).symm).symm

/-- **The pullback of rational functions along `RationalMap.ofFunctionFieldAlgHom k φ` is
`φ`**, as a `k`-algebra map. -/
@[simp]
theorem RationalMap.functionFieldAlgHom_ofFunctionFieldAlgHom :
    (ofFunctionFieldAlgHom k φ).functionFieldAlgHom k = φ := by
  ext a
  simp

/-- **A dominant `k`-rational map is induced by its pullback of rational functions**: a dominant
`k`-rational map `f : X ⤏ Y` is `RationalMap.ofFunctionFieldAlgHom` of `f^* : k(Y) → k(X)`. -/
@[simp]
theorem RationalMap.ofFunctionFieldAlgHom_functionFieldAlgHom (f : X ⤏ Y) [f.IsDominant]
    [f.IsOver (X ↘ Spec (.of k)) (Y ↘ Spec (.of k))] :
    ofFunctionFieldAlgHom k (f.functionFieldAlgHom k) = f :=
  eq_of_functionFieldAlgHom_eq k (functionFieldAlgHom_ofFunctionFieldAlgHom k _)

/-- **Determination.** For integral `k`-schemes `X` and `Y` with `Y` locally of finite type over
`k`, every `k`-algebra map `φ : k(Y) → k(X)` is the pullback of rational functions along a
dominant `k`-rational map `X ⤏ Y`. -/
theorem RationalMap.exists_functionFieldAlgHom_eq :
    ∃ (f : X ⤏ Y) (_ : f.IsDominant) (_ : f.IsOver (X ↘ Spec (.of k)) (Y ↘ Spec (.of k))),
      f.functionFieldAlgHom k = φ :=
  ⟨ofFunctionFieldAlgHom k φ, inferInstance, inferInstance,
    functionFieldAlgHom_ofFunctionFieldAlgHom k φ⟩

/-- **Determination, with uniqueness.** For integral `k`-schemes `X` and `Y` with `Y` locally of
finite type over `k`, every `k`-algebra map `φ : k(Y) → k(X)` is the pullback of rational
functions along exactly one dominant `k`-rational map `X ⤏ Y`. -/
theorem RationalMap.existsUnique_functionFieldAlgHom_eq :
    ∃! f : X ⤏ Y, ∃ (_ : f.IsDominant) (_ : f.IsOver (X ↘ Spec (.of k)) (Y ↘ Spec (.of k))),
      f.functionFieldAlgHom k = φ :=
  ⟨ofFunctionFieldAlgHom k φ,
    ⟨inferInstance, inferInstance, functionFieldAlgHom_ofFunctionFieldAlgHom k φ⟩,
    fun _ ⟨_, _, hφ⟩ ↦ eq_of_functionFieldAlgHom_eq k
      (hφ.trans (functionFieldAlgHom_ofFunctionFieldAlgHom k φ).symm)⟩

end AlgebraicGeometry.Scheme
