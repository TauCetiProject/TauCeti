/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.Topology.NoetherianSpace
public import Mathlib.Topology.Sober
import TauCeti.Topology.Sober

/-!
# Generic points of fibres

A point `x` of a scheme `X` is a *generic point of its fibre* under `f : X ⟶ Y`
(`AlgebraicGeometry.Scheme.Hom.IsFiberGenericPoint f x`) when it is the generic point of an
irreducible component of the fibre `f⁻¹(f x)`, as a subspace of `X`. The pullback of algebraic
cycles along `f` is supported on these points, and its local finiteness comes from there being
finitely many of them in each fibre over a Noetherian open. For a morphism over a field `k`, of
pure relative dimension `n`, between schemes locally of finite type over `k`, the closure of such
a point has dimension that of the closure of its image plus `n`
(`TauCeti.AlgebraicGeometry.height_eq_height_add_of_isFiberGenericPoint`). These are the uses in
`TauCeti.AlgebraicGeometry.Fibers.Dimension` and
`TauCeti.AlgebraicGeometry.AlgebraicCycle.Pullback`.

## Main declarations

* `AlgebraicGeometry.Scheme.Hom.IsFiberGenericPoint f x`: `x` is the generic point of an
  irreducible component of its fibre.
* `AlgebraicGeometry.Scheme.Hom.isFiberGenericPoint_iff_asFiber_mem_genericPoints` and
  `AlgebraicGeometry.Scheme.Hom.isFiberGenericPoint_iff_forall_specializes`: the same condition
  read in the scheme-theoretic fibre, and as having no proper generization in the fibre.
* `AlgebraicGeometry.Scheme.Hom.isFiberGenericPoint_of_isPreimmersion` and
  `AlgebraicGeometry.Scheme.Hom.isFiberGenericPoint_comp_iff_of_isOpenImmersion`: behaviour under
  preimmersions and restriction to open subschemes.
* `AlgebraicGeometry.Scheme.Hom.isFiberGenericPoint_of_injective`: if `f` is injective on points,
  every point is a generic point of its fibre.
* `AlgebraicGeometry.Scheme.Hom.finite_setOf_mem_and_apply_eq_and_isFiberGenericPoint`: a
  Noetherian open subset contains finitely many generic points of a given fibre.
-/

public section

open CategoryTheory Topology TopologicalSpace

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

/-- `x` is a generic point of its fibre exactly when the corresponding point `f.asFiber x` of the
scheme-theoretic fibre `f.fiber (f x)` is the generic point of an irreducible component. -/
lemma isFiberGenericPoint_iff_asFiber_mem_genericPoints (f : X ⟶ Y) (x : X) :
    IsFiberGenericPoint f x ↔ f.asFiber x ∈ genericPoints (f.fiber (f x)) := by
  have h : f.fiberHomeo (f x) (f.asFiber x) = ⟨x, rfl⟩ := Subtype.ext (f.fiberι_asFiber x)
  rw [← (f.fiberHomeo (f x)).isOpenEmbedding.mem_genericPoints_iff, h]
  exact isFiberGenericPoint_iff f x

/-- `x` is a generic point of its fibre exactly when it has no proper generization in its
fibre. -/
lemma isFiberGenericPoint_iff_forall_specializes (f : X ⟶ Y) (x : X) :
    IsFiberGenericPoint f x ↔ ∀ z, f z = f x → z ⤳ x → z = x := by
  have : QuasiSober (f ⁻¹' {f x}) := (f.fiberHomeo (f x)).symm.isOpenEmbedding.quasiSober
  rw [isFiberGenericPoint_iff, TauCeti.mem_genericPoints_iff, Subtype.forall]
  refine forall_congr' fun z ↦ forall_congr' fun _ ↦ ?_
  rw [subtype_specializes_iff, Subtype.ext_iff]

/-- Under a preimmersion, every point is a generic point of its fibre. -/
@[simp]
lemma isFiberGenericPoint_of_isPreimmersion (f : X ⟶ Y) [IsPreimmersion f] (x : X) :
    IsFiberGenericPoint f x :=
  f.isFiberGenericPoint_of_injective f.isEmbedding.injective x

/-- For an open immersion `j : U ⟶ X`, a point `u` is a generic point of its fibre under `j ≫ f`
exactly when `j u` is a generic point of its fibre under `f`: the generizations of `j u` lie in
the open image of `j`. -/
@[simp]
lemma isFiberGenericPoint_comp_iff_of_isOpenImmersion {U : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] (f : X ⟶ Y) (u : U) :
    IsFiberGenericPoint (j ≫ f) u ↔ IsFiberGenericPoint f (j u) := by
  simp only [isFiberGenericPoint_iff_forall_specializes, Scheme.Hom.comp_apply]
  constructor
  · intro h w hw hwu
    obtain ⟨z, rfl⟩ := hwu.mem_open j.isOpenEmbedding.isOpen_range (Set.mem_range_self u)
    rw [h z hw (j.isOpenEmbedding.isInducing.specializes_iff.mp hwu)]
  · intro h z hz hzu
    exact j.isOpenEmbedding.injective (h (j z) hz (hzu.map j.continuous))

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
