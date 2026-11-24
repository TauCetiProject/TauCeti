/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp

/-!
# The triangular change of coordinates on a power of a group object

Let `G` be a group object in a cartesian monoidal category `C`, let `J` be an index type with a
distinguished head index `i₀`, and let `∏ᶜ (fun _ : J => G)` be the `J`-th power of `G`. In terms
of points `q : J → (T ⟶ G)` with values in an object `T`, the triangular change of coordinates keeps
the head coordinate and right-divides every other coordinate by it:
`R(q)_{i₀} = q_{i₀}` and `R(q)_i = q_i / q_{i₀}` for `i ≠ i₀`.
Its inverse keeps the head coordinate and right-multiplies every other coordinate by it,
`r ↦ (r_{i₀}, r_i * r_{i₀})`. The two composites are the identity by cancellation in the group
`T ⟶ G`, so no commutativity of `G` is needed; the right-hand position of the head in the inverse
is essential when `G` is not commutative.

For a group scheme `G` over a base `S`, this is an automorphism of the fibre power
`G ×_S ⋯ ×_S G` over `S`, given by the same formulas on points with values in every `S`-scheme,
nonreduced ones included. For a Jacobian (written additively), with the head coordinate
`i_ω(x₁) + y` and the other coordinates `i_ω(x_r) + y`, it subtracts the common shift `y`;
this is the coordinate change in Yuan's proof that the shifted canonical power of a curve factors
through a multiplication isogeny on the tail coordinates.

A monoidal functor `F : C ⥤ D` (for instance base change of group schemes along `S' ⟶ S`)
commutes with both coordinate changes through the canonical comparison
`piComparison F : F (∏ᶜ G) ⟶ ∏ᶜ F G`, where `F.obj G` carries the image group structure
`Functor.grpObjObj`. The comparison need not be an isomorphism for this.

## Main definitions

* `TauCeti.GrpObj.triangularIso G i₀`: the triangular automorphism of `∏ᶜ (fun _ : J => G)` with
  head index `i₀`.

## Main results

* `TauCeti.GrpObj.triangularIso_hom_π_of_ne`, `TauCeti.GrpObj.triangularIso_inv_π_of_ne`: the
  non-head coordinates are right-divided, respectively right-multiplied, by the head coordinate.
* `TauCeti.GrpObj.lift_comp_triangularIso_hom`, `TauCeti.GrpObj.lift_comp_triangularIso_inv`:
  the action of both coordinate changes on points with values in an object.
* `TauCeti.GrpObj.map_triangularIso_hom_comp_piComparison`,
  `TauCeti.GrpObj.map_triangularIso_inv_comp_piComparison`: both coordinate changes commute with
  a monoidal functor through the product comparison map.

## References

* X. Yuan, *Arithmetic bigness and a uniform Bogomolov-type result*, arXiv:2108.05625v4,
  proof of Theorem 4.17(5).
-/

public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj

namespace TauCeti.GrpObj

universe w v v' u u'

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C] (G : C) [GrpObj G]
  {J : Type w} [DecidableEq J] (i₀ : J) [HasProduct fun _ : J => G]

/-- **The triangular change of coordinates** on the power `∏ᶜ (fun _ : J => G)` of a group object
with head index `i₀`. On points it keeps the head coordinate `q_{i₀}` and replaces every other
coordinate `q_i` by `q_i / q_{i₀}`; its inverse replaces `r_i` by `r_i * r_{i₀}`
(`lift_comp_triangularIso_hom`, `lift_comp_triangularIso_inv`). -/
noncomputable def triangularIso : ∏ᶜ (fun _ : J => G) ≅ ∏ᶜ (fun _ : J => G) where
  hom := Pi.lift fun i =>
    if i = i₀ then Pi.π (fun _ : J => G) i
    else Pi.π (fun _ : J => G) i / Pi.π (fun _ : J => G) i₀
  inv := Pi.lift fun i =>
    if i = i₀ then Pi.π (fun _ : J => G) i
    else Pi.π (fun _ : J => G) i * Pi.π (fun _ : J => G) i₀
  hom_inv_id := Pi.hom_ext _ _ fun i => by
    by_cases h : i = i₀ <;> simp [h, MonObj.comp_mul]
  inv_hom_id := Pi.hom_ext _ _ fun i => by
    by_cases h : i = i₀ <;> simp [h, GrpObj.comp_div]

/-- The triangular change of coordinates keeps the head coordinate. -/
@[reassoc (attr := simp)]
theorem triangularIso_hom_π_self :
    (triangularIso G i₀).hom ≫ Pi.π (fun _ : J => G) i₀ = Pi.π (fun _ : J => G) i₀ := by
  simp [triangularIso]

/-- The triangular change of coordinates right-divides each non-head coordinate by the head
coordinate. -/
@[reassoc (attr := simp)]
theorem triangularIso_hom_π_of_ne {i : J} (h : i ≠ i₀) :
    (triangularIso G i₀).hom ≫ Pi.π (fun _ : J => G) i =
      Pi.π (fun _ : J => G) i / Pi.π (fun _ : J => G) i₀ := by
  simp [triangularIso, h]

/-- The inverse triangular change of coordinates keeps the head coordinate. -/
@[reassoc (attr := simp)]
theorem triangularIso_inv_π_self :
    (triangularIso G i₀).inv ≫ Pi.π (fun _ : J => G) i₀ = Pi.π (fun _ : J => G) i₀ := by
  simp [triangularIso]

/-- The inverse triangular change of coordinates right-multiplies each non-head coordinate by the
head coordinate. -/
@[reassoc (attr := simp)]
theorem triangularIso_inv_π_of_ne {i : J} (h : i ≠ i₀) :
    (triangularIso G i₀).inv ≫ Pi.π (fun _ : J => G) i =
      Pi.π (fun _ : J => G) i * Pi.π (fun _ : J => G) i₀ := by
  simp [triangularIso, h]

/-- On a point `q` with values in `T`, the triangular change of coordinates keeps `q_{i₀}` and
replaces `q_i` by `q_i / q_{i₀}` for `i ≠ i₀`. -/
@[reassoc (attr := simp)]
theorem lift_comp_triangularIso_hom {T : C} (q : J → (T ⟶ G)) :
    Pi.lift q ≫ (triangularIso G i₀).hom =
      Pi.lift fun i => if i = i₀ then q i else q i / q i₀ :=
  Pi.hom_ext _ _ fun i => by by_cases h : i = i₀ <;> simp [h, GrpObj.comp_div]

/-- On a point `r` with values in `T`, the inverse triangular change of coordinates keeps
`r_{i₀}` and replaces `r_i` by `r_i * r_{i₀}` for `i ≠ i₀`. -/
@[reassoc (attr := simp)]
theorem lift_comp_triangularIso_inv {T : C} (r : J → (T ⟶ G)) :
    Pi.lift r ≫ (triangularIso G i₀).inv =
      Pi.lift fun i => if i = i₀ then r i else r i * r i₀ :=
  Pi.hom_ext _ _ fun i => by by_cases h : i = i₀ <;> simp [h, MonObj.comp_mul]

/-- For a single factor the triangular change of coordinates is the identity. -/
theorem triangularIso_eq_refl [Subsingleton J] : triangularIso G i₀ = Iso.refl _ :=
  Iso.ext <| Pi.hom_ext _ _ fun i => by simp [Subsingleton.elim i i₀]

section Functor

open scoped CategoryTheory.Obj

variable {D : Type u'} [Category.{v'} D] [CartesianMonoidalCategory D] (F : C ⥤ D) [F.Monoidal]
  [HasProduct fun _ : J => F.obj G]

/-- A monoidal functor commutes with the triangular change of coordinates through the product
comparison map, where `F.obj G` carries the image group structure. -/
@[reassoc]
theorem map_triangularIso_hom_comp_piComparison :
    F.map (triangularIso G i₀).hom ≫ piComparison F (fun _ : J => G) =
      piComparison F (fun _ : J => G) ≫ (triangularIso (F.obj G) i₀).hom :=
  Pi.hom_ext _ _ fun i => by
    by_cases h : i = i₀
    · subst h
      simp [← F.map_comp]
    · simp [← F.map_comp, h, div_eq_mul_inv, Functor.map_mul, MonObj.comp_mul, GrpObj.comp_inv]

/-- A monoidal functor commutes with the inverse triangular change of coordinates through the
product comparison map, where `F.obj G` carries the image group structure. -/
@[reassoc]
theorem map_triangularIso_inv_comp_piComparison :
    F.map (triangularIso G i₀).inv ≫ piComparison F (fun _ : J => G) =
      piComparison F (fun _ : J => G) ≫ (triangularIso (F.obj G) i₀).inv :=
  Pi.hom_ext _ _ fun i => by
    by_cases h : i = i₀
    · subst h
      simp [← F.map_comp]
    · simp [← F.map_comp, h, MonObj.comp_mul, Functor.map_mul]

end Functor

end TauCeti.GrpObj
