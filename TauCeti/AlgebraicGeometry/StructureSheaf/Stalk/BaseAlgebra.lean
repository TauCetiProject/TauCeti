/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Scheme.BaseAlgebra
public import Mathlib.AlgebraicGeometry.Group.Affine

/-!
# The map from a `k`-algebra to the stalks of its spectrum

For a `k`-algebra `R`, the scheme `Spec R` lies over `Spec k` (Mathlib's
`AlgebraicGeometry.specOverSpec`), so each of its stalks is a `k`-algebra
(`Scheme.stalkBaseAlgebra`). This file shows that the localization map
`StructureSheaf.toStalk R x` is a `k`-algebra map for that structure, and that at the closed
point of a local ring it is bijective.

This lives apart from `TauCeti.AlgebraicGeometry.Scheme.BaseAlgebra` because importing
`specOverSpec` there makes it a second `Over` instance on `Spec k` over itself, which breaks
instance search for `Scheme.Hom.IsOver` in importers of that file.

## Main declarations

* `TauCeti.AlgebraicGeometry.StructureSheaf.toStalkAlgHom`: the map from `R` to the stalk of
  `Spec R` at `x`, as a `k`-algebra map.
* `TauCeti.AlgebraicGeometry.StructureSheaf.toStalkAlgHom_closedPoint_bijective`: for a local
  `k`-algebra `R`, the map to the stalk at the closed point is bijective.
-/

public section

open AlgebraicGeometry CategoryTheory

universe u

noncomputable section

namespace TauCeti.AlgebraicGeometry.StructureSheaf

variable (k : Type u) [CommRing k] (R : CommRingCat.{u}) [Algebra k R]

/-- For a `k`-algebra `R`, the map `StructureSheaf.toStalk R x` from `R` to the stalk of `Spec R`
at `x`, as a `k`-algebra map for the base-ring algebra structure `Scheme.stalkBaseAlgebra` of the
stalk of `Spec R` over `Spec k`. -/
def toStalkAlgHom (x : Spec R) : R →ₐ[k] (Spec R).presheaf.stalk x where
  __ := (StructureSheaf.toStalk R x).hom
  commutes' c := by
    -- `Scheme.fromSpecStalk_comp_over` identifies the stalk's algebra map `k → 𝒪_{Spec R, x}`
    -- with the ring map underlying `Spec 𝒪_{Spec R, x} ⟶ Spec R ⟶ Spec k`, which by
    -- `Spec.fromSpecStalk_eq'` and `specOverSpec_over` is `toStalk R x` composed with
    -- `algebraMap k R`.
    have h := Scheme.fromSpecStalk_comp_over k (Spec R) x
    rw [Spec.fromSpecStalk_eq', specOverSpec_over] at h
    exact congr($(Spec.map_injective ((Spec.map_comp _ _).trans h)) c)

/-- The `k`-algebra map `toStalkAlgHom k R x` is `StructureSheaf.toStalk R x`. -/
@[simp]
lemma coe_toStalkAlgHom (x : Spec R) :
    ⇑(toStalkAlgHom k R x) = StructureSheaf.toStalk R x :=
  (rfl)

/-- For a local `k`-algebra `R`, the map from `R` to the stalk of `Spec R` at its closed point is
bijective. -/
lemma toStalkAlgHom_closedPoint_bijective [IsLocalRing R] :
    Function.Bijective (toStalkAlgHom k R (IsLocalRing.closedPoint R)) := by
  have h := ConcreteCategory.bijective_of_isIso (stalkClosedPointIso R).inv
  rw [stalkClosedPointIso_inv] at h
  exact coe_toStalkAlgHom k R _ ▸ h

end TauCeti.AlgebraicGeometry.StructureSheaf

end
