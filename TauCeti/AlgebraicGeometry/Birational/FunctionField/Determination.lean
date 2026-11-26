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
bijection between dominant `k`-rational maps `X ⤏ Y` and `k`-algebra maps `k(Y) → k(X)`
(`AlgebraicGeometry.Scheme.RationalMap.equivFunctionFieldAlgHom`).

The rational map is Mathlib's `Scheme.RationalMap.ofFunctionField` of the `k`-morphism
`Spec φ ≫ (Spec k(Y) ⟶ Y)` from `Spec k(X)`, which is defined because `Y` is locally of finite
type. It is dominant because it sends the generic point of `X` into the image of
`Spec k(Y) ⟶ Y`, whose only point is the generic point of `Y`
(`AlgebraicGeometry.Scheme.RationalMap.isDominant_of_fromFunctionField_eq`).

## Main definitions

* `AlgebraicGeometry.Scheme.RationalMap.ofFunctionFieldAlgHom`: the dominant `k`-rational map
  whose pullback of rational functions is a given `k`-algebra map `k(Y) → k(X)`.
* `AlgebraicGeometry.Scheme.RationalMap.equivFunctionFieldAlgHom`: **determination**, the
  bijection `f ↦ f^*` between dominant `k`-rational maps `X ⤏ Y` and `k`-algebra maps
  `k(Y) → k(X)`.

## Main results

* `AlgebraicGeometry.Scheme.RationalMap.eq_of_functionFieldAlgHom_eq`: a dominant `k`-rational
  map is determined by its `k`-algebra pullback.
* `AlgebraicGeometry.Scheme.RationalMap.functionFieldAlgHom_ofFunctionFieldAlgHom` and
  `AlgebraicGeometry.Scheme.RationalMap.ofFunctionFieldAlgHom_functionFieldAlgHom`: the
  construction is inverse to the pullback, and
  `AlgebraicGeometry.Scheme.RationalMap.eq_ofFunctionFieldAlgHom_iff` characterizes it.
* `AlgebraicGeometry.Scheme.RationalMap.ofFunctionFieldAlgHom_id` and
  `AlgebraicGeometry.Scheme.RationalMap.ofFunctionFieldAlgHom_comp`: functoriality.
* `AlgebraicGeometry.Scheme.RationalMap.existsUnique_functionFieldAlgHom_eq`: every `k`-algebra
  map of function fields is the pullback along exactly one dominant `k`-rational map.

## References

* R. Hartshorne, *Algebraic Geometry*, GTM 52, Springer, 1977, Theorem I.4.4.
-/

public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme

variable {X Y : Scheme.{u}}

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
    (RationalMap.ofFunctionFieldAlgHom k φ).IsOver (X ↘ Spec (.of k)) (Y ↘ Spec (.of k)) := by
  -- `ofFunctionField` is the rational map of Mathlib's partial map `ofFromSpecStalk`, which is
  -- over `k` by `ofFromSpecStalk_comp`
  unfold RationalMap.ofFunctionFieldAlgHom RationalMap.ofFunctionField
  exact ⟨⟨_, ⟨PartialMap.ofFromSpecStalk_comp _ _ _ _⟩, rfl⟩⟩

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

/-- A dominant `k`-morphism `g : X ⟶ Y` is induced by its pullback of rational functions:
`RationalMap.ofFunctionFieldAlgHom` of `g^* : k(Y) → k(X)` is the rational map of `g`. -/
@[simp]
theorem Hom.ofFunctionFieldAlgHom_functionFieldAlgHom (g : X ⟶ Y) [IsDominant g]
    [g.IsOver (Spec (.of k))] :
    RationalMap.ofFunctionFieldAlgHom k (g.functionFieldAlgHom k) = g.toRationalMap := by
  rw [← Hom.functionFieldAlgHom_toRationalMap,
    RationalMap.ofFunctionFieldAlgHom_functionFieldAlgHom]

/-- **Characterization of `RationalMap.ofFunctionFieldAlgHom`**: a dominant `k`-rational map
`f : X ⤏ Y` is `RationalMap.ofFunctionFieldAlgHom k φ` exactly when `f^* = φ`. -/
theorem RationalMap.eq_ofFunctionFieldAlgHom_iff (f : X ⤏ Y) [f.IsDominant]
    [f.IsOver (X ↘ Spec (.of k)) (Y ↘ Spec (.of k))] :
    f = ofFunctionFieldAlgHom k φ ↔ f.functionFieldAlgHom k = φ := by
  refine ⟨fun h ↦ ?_, fun h ↦ eq_of_functionFieldAlgHom_eq k
    (h.trans (functionFieldAlgHom_ofFunctionFieldAlgHom k φ).symm)⟩
  subst h
  exact functionFieldAlgHom_ofFunctionFieldAlgHom k φ

/-- The identity of `k(Y)` induces the identity rational map of `Y`. -/
@[simp]
theorem RationalMap.ofFunctionFieldAlgHom_id :
    ofFunctionFieldAlgHom k (AlgHom.id k Y.functionField) = RationalMap.id Y :=
  ((eq_ofFunctionFieldAlgHom_iff k _ _).mpr (functionFieldAlgHom_id k)).symm

/-- **Functoriality of `RationalMap.ofFunctionFieldAlgHom`**: `k`-algebra maps
`k(Z) → k(Y) → k(X)` induce the composite `X ⤏ Y ⤏ Z`. -/
theorem RationalMap.ofFunctionFieldAlgHom_comp {Z : Scheme.{u}} [Z.Over (Spec (.of k))]
    [IsIntegral Z] [LocallyOfFiniteType (Z ↘ Spec (.of k))]
    (ψ : Z.functionField →ₐ[k] Y.functionField) :
    (ofFunctionFieldAlgHom k φ).comp (ofFunctionFieldAlgHom k ψ) =
      ofFunctionFieldAlgHom k (φ.comp ψ) := by
  have := isOver_comp (sX := X ↘ Spec (.of k)) (sY := Y ↘ Spec (.of k))
    (sZ := Z ↘ Spec (.of k)) (ofFunctionFieldAlgHom k φ) inferInstance
    (ofFunctionFieldAlgHom k ψ) inferInstance
  exact (eq_ofFunctionFieldAlgHom_iff k _ _).mpr (by simp)

/-- **Determination.** For integral `k`-schemes `X` and `Y` with `Y` locally of finite type over
`k`, `f ↦ f^*` is a bijection between dominant `k`-rational maps `X ⤏ Y` and `k`-algebra maps
`k(Y) → k(X)`, with inverse `RationalMap.ofFunctionFieldAlgHom`. -/
noncomputable def RationalMap.equivFunctionFieldAlgHom :
    {f : X ⤏ Y // f.IsDominant ∧ f.IsOver (X ↘ Spec (.of k)) (Y ↘ Spec (.of k))} ≃
      (Y.functionField →ₐ[k] X.functionField) where
  toFun f := haveI := f.property.left; haveI := f.property.right; f.val.functionFieldAlgHom k
  invFun φ := ⟨ofFunctionFieldAlgHom k φ, inferInstance, inferInstance⟩
  left_inv f := by
    obtain ⟨f, _, _⟩ := f
    exact Subtype.ext (ofFunctionFieldAlgHom_functionFieldAlgHom k f)
  right_inv := functionFieldAlgHom_ofFunctionFieldAlgHom k

/-- `RationalMap.equivFunctionFieldAlgHom k` sends a dominant `k`-rational map to its
`k`-algebra pullback of rational functions. -/
@[simp]
theorem RationalMap.equivFunctionFieldAlgHom_apply (f : X ⤏ Y) [f.IsDominant]
    [f.IsOver (X ↘ Spec (.of k)) (Y ↘ Spec (.of k))] :
    equivFunctionFieldAlgHom k ⟨f, ‹_›, ‹_›⟩ = f.functionFieldAlgHom k :=
  (rfl)

/-- The inverse of `RationalMap.equivFunctionFieldAlgHom k` is
`RationalMap.ofFunctionFieldAlgHom k`. -/
@[simp]
theorem RationalMap.equivFunctionFieldAlgHom_symm_apply_coe :
    ((equivFunctionFieldAlgHom k).symm φ : X ⤏ Y) = ofFunctionFieldAlgHom k φ :=
  (rfl)

/-- **Determination, with uniqueness.** For integral `k`-schemes `X` and `Y` with `Y` locally of
finite type over `k`, every `k`-algebra map `φ : k(Y) → k(X)` is the pullback of rational
functions along exactly one dominant `k`-rational map `X ⤏ Y`. -/
theorem RationalMap.existsUnique_functionFieldAlgHom_eq :
    ∃! f : X ⤏ Y, ∃ (_ : f.IsDominant) (_ : f.IsOver (X ↘ Spec (.of k)) (Y ↘ Spec (.of k))),
      f.functionFieldAlgHom k = φ :=
  ⟨ofFunctionFieldAlgHom k φ,
    ⟨inferInstance, inferInstance, functionFieldAlgHom_ofFunctionFieldAlgHom k φ⟩,
    fun f ⟨_, _, hφ⟩ ↦ (eq_ofFunctionFieldAlgHom_iff k φ f).mpr hφ⟩

end AlgebraicGeometry.Scheme
