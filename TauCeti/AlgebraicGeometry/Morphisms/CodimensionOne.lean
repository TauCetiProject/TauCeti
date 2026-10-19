/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import TauCeti.AlgebraicGeometry.Morphisms.Dominant
public import TauCeti.AlgebraicGeometry.Morphisms.LocallyQuasiFinite
public import TauCeti.AlgebraicGeometry.Scheme.CodimensionOnePoint
public import TauCeti.AlgebraicGeometry.Scheme.GenericPoint

/-!
# Codimension-one points under quasi-finite morphisms

Let `f : X ⟶ Y` be a locally quasi-finite dominant morphism of irreducible schemes, for instance a
finite dominant morphism of integral schemes. A point of `X` lying over a point of codimension one
of `Y` has codimension one: its codimension is at most that of its image
(`AlgebraicGeometry.Scheme.Hom.coheight_le_coheight_apply`), and it is not the generic point of
`X`, which `f` sends to the generic point of `Y`.

Whether, conversely, `f` sends points of codimension one to points of codimension one depends on
the target; it holds when `Y` is normal (going down) or of finite type over a field, and fails in
general (Stacks, Section 110.19 (02JE)). The map `codimensionOneMap f hf` on codimension-one points
therefore takes this property as the argument `hf`. When `f` is moreover surjective (for instance
finite and dominant) the map is surjective, and when `f` is quasi-compact its fibres are finite.

## Main definitions

* `AlgebraicGeometry.Scheme.Hom.codimensionOneMap`: the map on codimension-one points induced by
  a morphism that preserves codimension one.

## Main results

* `AlgebraicGeometry.Scheme.Hom.coheight_eq_one_of_coheight_apply_eq_one`: a point over a point
  of codimension one has codimension one.
* `AlgebraicGeometry.Scheme.Hom.codimensionOneMap_surjective`: for a surjective, locally
  quasi-finite morphism of irreducible schemes, every codimension-one point of the target is the
  image of a codimension-one point.
* `AlgebraicGeometry.Scheme.Hom.codimensionOneMap_finite_preimage_singleton`: the fibres of
  `codimensionOneMap` of a quasi-compact locally quasi-finite morphism are finite.
* `AlgebraicGeometry.Scheme.Hom.codimensionOneMap_comp` and
  `AlgebraicGeometry.Scheme.Hom.codimensionOneMap_id`: functoriality.

## References

* [Stacks Project, Lemma 10.36.20](https://stacks.math.columbia.edu/tag/00GT): incomparability
  for integral ring maps, of which the specialization-order argument used here is the
  quasi-finite scheme analogue.
* Ported from T. Dupuy, T. Tucker and Z. Wang,
  [pcfawd-formalization](https://github.com/tdupu/pcfawd-formalization) at commit
  `9a20b3f351446d64e6015d704198bc71c7002008` (Apache-2.0). `codimensionOneMap_surjective` is its
  `Pcf.SchemeDivisorPoint.mapFiniteDominantNormal_surjective` (there for a normal target), in
  `lean/Pcf/Bounding/SchemeDynamics.lean`; `coheight_eq_one_of_coheight_apply_eq_one` is the
  scheme form of its `Pcf.height_eq_one_of_liesOver_heightOne`, in
  `lean/Pcf/Bounding/Divisors.lean`; and `codimensionOneMap_finite_preimage_singleton` is its
  `Pcf.schemeDivisorMap_finite_fiber`, in `lean/Pcf/Bounding/SchemeWiring.lean`.
-/

public section

open CategoryTheory AlgebraicGeometry Order

namespace AlgebraicGeometry.Scheme.Hom

universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- For a locally quasi-finite dominant morphism of irreducible schemes, a point lying over a point
of coheight one has coheight one. -/
theorem coheight_eq_one_of_coheight_apply_eq_one [LocallyQuasiFinite f] [IsDominant f]
    [IrreducibleSpace X] [IrreducibleSpace Y] (x : X) (hx : coheight (f x) = 1) :
    coheight x = 1 := by
  -- The coheight of `x` is at most that of `f x`, and `x` is not the generic point of `X`,
  -- which `f` sends to the generic point of `Y`, of coheight zero.
  have hle : coheight x ≤ 1 := hx ▸ f.coheight_le_coheight_apply x
  have hne : coheight x ≠ 0 := by
    intro h0
    have hgen : x = genericPoint X :=
      TauCeti.AlgebraicGeometry.Scheme.eq_genericPoint_of_isMax (coheight_eq_zero.mp h0)
    have himage : coheight (f x) = 0 := by
      rw [hgen, f.genericPoint_eq_of_isDominant, coheight_eq_zero]
      exact TauCeti.AlgebraicGeometry.Scheme.isMax_genericPoint
    rw [himage] at hx
    exact zero_ne_one hx
  exact le_antisymm hle (Order.one_le_iff_ne_zero.mpr hne)

/-- The map on codimension-one points induced by a morphism `f` that sends points of coheight
one to points of coheight one. -/
def codimensionOneMap (hf : ∀ x : X, coheight x = 1 → coheight (f x) = 1) :
    TauCeti.AlgebraicGeometry.CodimensionOnePoint X →
      TauCeti.AlgebraicGeometry.CodimensionOnePoint Y :=
  fun x => ⟨f x, hf x x.2⟩

@[simp]
theorem codimensionOneMap_apply (hf : ∀ x : X, coheight x = 1 → coheight (f x) = 1)
    (x : TauCeti.AlgebraicGeometry.CodimensionOnePoint X) :
    (codimensionOneMap f hf x : Y) = f x :=
  (rfl)

/-- For a surjective locally quasi-finite morphism of irreducible schemes (for instance a finite
dominant morphism of integral schemes), every codimension-one point of the target is the image of
a codimension-one point. -/
theorem codimensionOneMap_surjective [Surjective f] [LocallyQuasiFinite f]
    [IrreducibleSpace X] [IrreducibleSpace Y]
    (hf : ∀ x : X, coheight x = 1 → coheight (f x) = 1) :
    Function.Surjective (codimensionOneMap f hf) := by
  intro y
  obtain ⟨x, hx⟩ := f.surjective y
  have hcodim : coheight x = 1 :=
    coheight_eq_one_of_coheight_apply_eq_one f x (hx ▸ y.2)
  exact ⟨⟨x, hcodim⟩, Subtype.ext hx⟩

/-- The fibres of the map on codimension-one points of a quasi-compact locally quasi-finite
morphism are finite. -/
theorem codimensionOneMap_finite_preimage_singleton [LocallyQuasiFinite f] [QuasiCompact f]
    (hf : ∀ x : X, coheight x = 1 → coheight (f x) = 1)
    (y : TauCeti.AlgebraicGeometry.CodimensionOnePoint Y) :
    (codimensionOneMap f hf ⁻¹' {y}).Finite := by
  have hfiber : (f ⁻¹' {(y : Y)}).Finite := f.finite_preimage_singleton y
  refine (hfiber.preimage Subtype.val_injective.injOn).subset fun x hx ↦ ?_
  simpa using congrArg Subtype.val hx

/-- The map on codimension-one points of a composite is the composite of the maps. -/
@[simp]
theorem codimensionOneMap_comp {Z : Scheme.{u}} (g : Y ⟶ Z)
    (hf : ∀ x : X, coheight x = 1 → coheight (f x) = 1)
    (hg : ∀ y : Y, coheight y = 1 → coheight (g y) = 1) :
    codimensionOneMap (f ≫ g) (fun x hx ↦ by simpa using hg (f x) (hf x hx)) =
      codimensionOneMap g hg ∘ codimensionOneMap f hf := by
  funext x
  apply Subtype.ext
  simp

/-- The map on codimension-one points of the identity is the identity. -/
@[simp]
theorem codimensionOneMap_id :
    codimensionOneMap (𝟙 X) (fun x hx ↦ by simpa using hx) = id := by
  funext x
  apply Subtype.ext
  simp

end AlgebraicGeometry.Scheme.Hom
