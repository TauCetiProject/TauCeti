/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Stalk

/-!
# Germs of pulled-back sections and stalk algebras over a specified image

For a morphism of schemes `f : X ⟶ Y`, opens `U` of `Y` and `V ≤ f ⁻¹ᵁ U` of `X`, and a point
`x ∈ V`, the square `appLE_germ` moves the germ at `x` past the pulled-back sections
`f.appLE U V e` through the stalk map at `x`. It is a simp lemma, after which `simp` continues
with Mathlib's `germ_stalkMap`; `appLE_germ_of_apply_eq` is its version at a point `y` specified
to equal `f x`.

For such a point `y`, `stalkAlgebraOfApplyEq` makes `𝒪_{X,x}` an algebra over `𝒪_{Y,y}` through
the specialization map of stalks and the stalk map of `f`. It is characterised by
`algebraMap_stalkAlgebraOfApplyEq`, its compatibility with germs
`algebraMap_stalkAlgebraOfApplyEq_comp_germ`, and its value
`algebraMap_stalkAlgebraOfApplyEq_rfl` at `y = f x`; its algebra map is local by
`isLocalHom_algebraMap_stalkAlgebraOfApplyEq`. Stating these over a specified `y` avoids
transporting along an equation of points when the image is only known propositionally, as for
points of a fibre.

These declarations are adapted from the
[lookahead formalization](https://github.com/roed-math/TauCeti-w2-fresh/tree/678c1bad7a8c53d6cffb49946b9fefc73d4c0435).
-/

public section

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Hom

universe u

variable {X Y : Scheme.{u}}

/-- Pullback to a smaller open commutes with taking germs at a point over a specified image. -/
@[reassoc]
theorem appLE_germ_of_apply_eq (f : X ⟶ Y) (U : Y.Opens) (V : X.Opens)
    (e : V ≤ f ⁻¹ᵁ U) {x : X} {y : Y} (h : f x = y) (hx : x ∈ V) (hy : y ∈ U) :
    f.appLE U V e ≫ X.presheaf.germ V x hx =
      Y.presheaf.germ U y hy ≫ Y.presheaf.stalkSpecializes (specializes_of_eq h) ≫
        f.stalkMap x := by
  subst y
  simp only [TopCat.Presheaf.stalkSpecializes_refl, Category.id_comp]
  rw [Scheme.Hom.germ_stalkMap, Scheme.Hom.app_eq_appLE,
    ← X.presheaf.germ_res (homOfLE e) x hx, Scheme.Hom.appLE_map_assoc]

/-- Pullback to a smaller open commutes with taking germs at a point, through the stalk map at
that point. The membership `f x ∈ U` is stated through `mem_preimage`, so that `simp` continues
with Mathlib's `germ_stalkMap`. -/
@[reassoc (attr := simp)]
theorem appLE_germ (f : X ⟶ Y) (U : Y.Opens) (V : X.Opens) (e : V ≤ f ⁻¹ᵁ U) {x : X}
    (hx : x ∈ V) :
    f.appLE U V e ≫ X.presheaf.germ V x hx =
      Y.presheaf.germ U (f x) (f.mem_preimage.mp (e hx)) ≫ f.stalkMap x := by
  have := f.appLE_germ_of_apply_eq U V e rfl hx (f.mem_preimage.mp (e hx))
  rwa [TopCat.Presheaf.stalkSpecializes_refl, Category.id_comp] at this

/-- The local ring `𝒪_{Y,y}` maps to the local ring `𝒪_{X,x}` of a point over `y`, through the
stalk map of `f` at `x`. -/
@[instance_reducible]
noncomputable def stalkAlgebraOfApplyEq (f : X ⟶ Y) {x : X} {y : Y} (h : f x = y) :
    Algebra (Y.presheaf.stalk y) (X.presheaf.stalk x) :=
  (Y.presheaf.stalkSpecializes (specializes_of_eq h) ≫ f.stalkMap x).hom.toAlgebra

/-- The algebra map of `stalkAlgebraOfApplyEq` is the specialization map of stalks followed by
the stalk map of `f`. -/
theorem algebraMap_stalkAlgebraOfApplyEq (f : X ⟶ Y) {x : X} {y : Y} (h : f x = y) :
    letI := f.stalkAlgebraOfApplyEq h
    algebraMap (Y.presheaf.stalk y) (X.presheaf.stalk x) =
      (Y.presheaf.stalkSpecializes (specializes_of_eq h) ≫ f.stalkMap x).hom := by
  -- The definition is unexposed; its body is `RingHom.toAlgebra` of this ring hom.
  unfold stalkAlgebraOfApplyEq
  rfl

/-- The algebra map on stalks at equal image points commutes with germs of pulled-back sections. -/
theorem algebraMap_stalkAlgebraOfApplyEq_comp_germ (f : X ⟶ Y)
    (U : Y.Opens) (V : X.Opens) (e : V ≤ f ⁻¹ᵁ U)
    {x : X} {y : Y} (h : f x = y) (hx : x ∈ V) (hy : y ∈ U) :
    letI := f.stalkAlgebraOfApplyEq h
    (algebraMap (Y.presheaf.stalk y) (X.presheaf.stalk x)).comp
        (Y.presheaf.germ U y hy).hom =
      (X.presheaf.germ V x hx).hom.comp (f.appLE U V e).hom := by
  let _ := f.stalkAlgebraOfApplyEq h
  rw [f.algebraMap_stalkAlgebraOfApplyEq h]
  exact (congrArg CommRingCat.Hom.hom (f.appLE_germ_of_apply_eq U V e h hx hy)).symm

/-- Over the image point itself, the algebra map of `stalkAlgebraOfApplyEq` is the stalk map
of `f`. -/
@[simp]
theorem algebraMap_stalkAlgebraOfApplyEq_rfl (f : X ⟶ Y) (x : X) :
    letI := f.stalkAlgebraOfApplyEq (rfl : f x = f x)
    algebraMap (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) = (f.stalkMap x).hom := by
  simp [algebraMap_stalkAlgebraOfApplyEq]

/-- The algebra map of `stalkAlgebraOfApplyEq` is a local homomorphism, so it induces a map of
residue fields. -/
theorem isLocalHom_algebraMap_stalkAlgebraOfApplyEq (f : X ⟶ Y) {x : X} {y : Y} (h : f x = y) :
    letI := f.stalkAlgebraOfApplyEq h
    IsLocalHom (algebraMap (Y.presheaf.stalk y) (X.presheaf.stalk x)) := by
  subst h
  rw [algebraMap_stalkAlgebraOfApplyEq_rfl]
  infer_instance

end AlgebraicGeometry.Scheme.Hom
