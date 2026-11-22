/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.Topology.NoetherianSpace
public import Mathlib.Topology.Sober
import TauCeti.Topology.Sober

/-!
# Generic points of fibres

A point `x` of a scheme `X` is a *generic point of its fibre* under `f : X ⟶ Y`
(`AlgebraicGeometry.Scheme.Hom.IsFiberGenericPoint f x`) when it is the generic point of an
irreducible component of the fibre `f⁻¹(f x)`, as a subspace of `X`.

## Main declarations

* `AlgebraicGeometry.Scheme.Hom.IsFiberGenericPoint f x`: `x` is the generic point of an
  irreducible component of its fibre.
* `AlgebraicGeometry.Scheme.Hom.isFiberGenericPoint_of_injective`: if `f` is injective on points,
  every point is a generic point of its fibre.
* `AlgebraicGeometry.Scheme.Hom.finite_setOf_mem_and_apply_eq_and_isFiberGenericPoint`: a
  Noetherian open subset contains finitely many generic points of a given fibre.
-/

public section

open Topology TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {X Y : Scheme.{u}}

/-- A point `x` of `X` is a generic point of its fibre under `f : X ⟶ Y` when it is the generic
point of an irreducible component of the fibre `f⁻¹(f x)`. -/
def IsFiberGenericPoint (f : X ⟶ Y) (x : X) : Prop :=
  (⟨x, rfl⟩ : f ⁻¹' {f x}) ∈ genericPoints (f ⁻¹' {f x})

/-- Unfolding `IsFiberGenericPoint`. -/
lemma isFiberGenericPoint_iff (f : X ⟶ Y) (x : X) :
    IsFiberGenericPoint f x ↔ (⟨x, rfl⟩ : f ⁻¹' {f x}) ∈ genericPoints (f ⁻¹' {f x}) :=
  Iff.rfl

/-- If `f` is injective on points, every point of `X` is a generic point of its fibre. -/
lemma isFiberGenericPoint_of_injective (f : X ⟶ Y) (hf : Function.Injective f) (x : X) :
    IsFiberGenericPoint f x := by
  have : Subsingleton (f ⁻¹' {f x}) :=
    ⟨fun a b ↦ Subtype.ext (hf (a.property.trans b.property.symm))⟩
  have : IrreducibleSpace (f ⁻¹' {f x}) :=
    { isPreirreducible_univ := Set.subsingleton_univ.isPreirreducible
      toNonempty := ⟨⟨x, rfl⟩⟩ }
  rw [isFiberGenericPoint_iff, genericPoints, Set.mem_ofPred_eq,
    irreducibleComponents_eq_singleton, Set.mem_singleton_iff]
  exact Set.eq_univ_of_forall fun b ↦ Subsingleton.elim (⟨x, rfl⟩ : f ⁻¹' {f x}) b ▸
    subset_closure rfl

/-- An open subset `U` of `X` that is a Noetherian space contains only finitely many generic
points of the fibre of `f` over a given point. -/
lemma finite_setOf_mem_and_apply_eq_and_isFiberGenericPoint (f : X ⟶ Y) {U : Set X} (hU : IsOpen U)
    [NoetherianSpace U] (y : Y) :
    {x | x ∈ U ∧ f x = y ∧ IsFiberGenericPoint f x}.Finite := by
  let V : Set (f ⁻¹' {y}) := Subtype.val ⁻¹' U
  have hV : IsOpen V := hU.preimage continuous_subtypeVal
  -- `V` is the part of the fibre in `U`, a subspace of the Noetherian space `U`.
  have : NoetherianSpace V :=
    ((IsInducing.subtypeVal.comp IsInducing.subtypeVal).codRestrict
      (s := U) fun v ↦ v.property).noetherianSpace
  refine ((genericPoints.finite NoetherianSpace.finite_irreducibleComponents).image
    fun v : V ↦ (v : f ⁻¹' {y}).val).subset ?_
  rintro x ⟨hxU, rfl, hx⟩
  exact ⟨⟨⟨x, rfl⟩, hxU⟩,
    (hV.isOpenEmbedding_subtypeVal.mem_genericPoints_iff (⟨⟨x, rfl⟩, hxU⟩ : V)).mp hx, rfl⟩

end AlgebraicGeometry.Scheme.Hom
