/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Pullbacks
public import TauCeti.CategoryTheory.Monoidal.Cartesian.Ring

/-!
# Affine space is a commutative ring scheme

For a type `n` and a scheme `S`, morphisms `T ⟶ 𝔸(n; S)` over `S` are the same as `n`-tuples of
global functions on `T` (Mathlib's `AffineSpace.homOverEquiv`). These form the commutative ring
`Γ(T, ⊤)ⁿ`, and pulling back along a morphism `T' ⟶ T` over `S` is a ring homomorphism, so by the
Yoneda lemma `𝔸(n; S)` is a commutative ring object of the cartesian monoidal category `Over S`:
a commutative ring scheme over `S`, whose operations are the coordinatewise sum and product of
functions. For `n` a singleton this is the affine line `𝔸¹_S`, the ring of scalars of linear
schemes over `S`.

## Main declarations

* `AlgebraicGeometry.AffineSpace.homAsOverEquiv`: morphisms `T ⟶ 𝔸(n; S)` in `Over S` are
  `n`-tuples of global functions on `T`;
* `AlgebraicGeometry.AffineSpace.commRingObjAsOver`: `𝔸(n; S)` is a commutative ring object of
  `Over S`;
* `AlgebraicGeometry.AffineSpace.homAsOverRingEquiv`: its ring of `T`-points is `Γ(T, ⊤)ⁿ`.

## References

* A. Grothendieck, J. Dieudonné, *Éléments de géométrie algébrique II*, 1.7.
-/

public section

open CategoryTheory Opposite

namespace AlgebraicGeometry.AffineSpace

universe u

noncomputable section

variable (n : Type u) (S : Scheme.{u})

/-- The presheaf of commutative rings `T ↦ Γ(T, ⊤)ⁿ` of `n`-tuples of global functions on schemes
over `S`, whose restriction maps pull back functions. It is represented by `𝔸(n; S)`. -/
-- exposed so that its rings are seen to be the rings `Γ(T, ⊤)ⁿ`
@[expose, simps obj]
def functionsPresheaf : (Over S)ᵒᵖ ⥤ CommRingCat.{u} where
  obj T := .of (n → Γ(T.unop.left, ⊤))
  map g := CommRingCat.ofHom (g.unop.left.appTop.hom.compLeft n)

/-- The restriction maps of `functionsPresheaf` pull back each function. -/
@[simp]
lemma functionsPresheaf_map_apply {T T' : (Over S)ᵒᵖ} (g : T ⟶ T')
    (v : n → Γ(T.unop.left, ⊤)) (i : n) :
    (functionsPresheaf n S).map g v i = g.unop.left.appTop (v i) :=
  (rfl)

variable {n S}

/-- **Points of affine space over `S`.** Morphisms `T ⟶ 𝔸(n; S)` in `Over S` correspond to
`n`-tuples of global functions on `T`, by pulling back the coordinates. This is
`AffineSpace.homOverEquiv` stated in the category `Over S`. -/
def homAsOverEquiv (T : Over S) : (T ⟶ 𝔸(n; S).asOver S) ≃ (n → Γ(T.left, ⊤)) where
  toFun f i := f.left.appTop (coord S i)
  invFun v := Over.homMk (homOfVector T.hom v) (homOfVector_over _ _)
  left_inv f := by
    ext1
    exact hom_ext ((homOfVector_over T.hom _).trans (Over.w f).symm)
      fun i ↦ homOfVector_appTop_coord _ _ i
  right_inv v := funext fun i ↦ homOfVector_appTop_coord _ _ i

/-- The tuple of functions of a point of affine space is the tuple of pulled-back coordinates. -/
@[simp]
lemma homAsOverEquiv_apply (T : Over S) (f : T ⟶ 𝔸(n; S).asOver S) (i : n) :
    homAsOverEquiv T f i = f.left.appTop (coord S i) :=
  (rfl)

/-- The point of affine space of a tuple of functions `v` is `homOfVector T.hom v`. -/
@[simp]
lemma homAsOverEquiv_symm_apply_left (T : Over S) (v : n → Γ(T.left, ⊤)) :
    ((homAsOverEquiv T).symm v).left = homOfVector T.hom v :=
  (rfl)

/-- `homAsOverEquiv` is natural in the scheme over `S`: composing with `g : T' ⟶ T` pulls back
the functions along `g`. -/
lemma homAsOverEquiv_comp {T' T : Over S} (g : T' ⟶ T) (f : T ⟶ 𝔸(n; S).asOver S) (i : n) :
    homAsOverEquiv T' (g ≫ f) i = g.left.appTop (homAsOverEquiv T f i) := by
  simp only [homAsOverEquiv_apply, Over.comp_left, Scheme.Hom.comp_appTop]
  exact CommRingCat.comp_apply _ _ _

/-- `𝔸(n; S)` represents the presheaf `T ↦ Γ(T, ⊤)ⁿ` on schemes over `S`. -/
def representableByAsOver :
    (functionsPresheaf n S ⋙ forget _).RepresentableBy (𝔸(n; S).asOver S) where
  homEquiv {T} := homAsOverEquiv T
  homEquiv_comp g f := funext (homAsOverEquiv_comp g f)

/-- **Affine space is a commutative ring scheme.** `𝔸(n; S)` is a commutative ring object of
`Over S`, for the structure in which `T`-points form the ring `Γ(T, ⊤)ⁿ`
(`homAsOverRingEquiv`). -/
instance commRingObjAsOver : CommRingObj (𝔸(n; S).asOver S) :=
  .ofRepresentableBy _ _ representableByAsOver

open scoped CommRingObj

/-- **The ring of points of affine space.** For a scheme `T` over `S`, the ring of morphisms
`T ⟶ 𝔸(n; S)` over `S`, for the ring structure of `commRingObjAsOver`, is the ring `Γ(T, ⊤)ⁿ`
of `n`-tuples of global functions on `T`. -/
def homAsOverRingEquiv (T : Over S) : (T ⟶ 𝔸(n; S).asOver S) ≃+* (n → Γ(T.left, ⊤)) :=
  CommRingObj.homRingEquivOfRepresentableBy _ _ representableByAsOver T

/-- The ring isomorphism `homAsOverRingEquiv` is `homAsOverEquiv`. -/
@[simp]
lemma homAsOverRingEquiv_apply (T : Over S) (f : T ⟶ 𝔸(n; S).asOver S) :
    homAsOverRingEquiv T f = homAsOverEquiv T f :=
  CommRingObj.homRingEquivOfRepresentableBy_apply _ (functionsPresheaf n S) representableByAsOver
    T f

/-- The inverse of the ring isomorphism `homAsOverRingEquiv` is the inverse of
`homAsOverEquiv`. -/
@[simp]
lemma homAsOverRingEquiv_symm_apply (T : Over S) (v : n → Γ(T.left, ⊤)) :
    (homAsOverRingEquiv T).symm v = (homAsOverEquiv T).symm v :=
  CommRingObj.homRingEquivOfRepresentableBy_symm_apply _ (functionsPresheaf n S)
    representableByAsOver T v

/-- The point `1` of affine space is the tuple of constant functions `1`. -/
@[simp]
lemma homAsOverEquiv_one (T : Over S) : homAsOverEquiv (n := n) T 1 = 1 := by
  rw [← homAsOverRingEquiv_apply, map_one]

/-- The tuple of functions of a product of points of affine space is the product of their tuples
of functions. -/
@[simp]
lemma homAsOverEquiv_mul (T : Over S) (f g : T ⟶ 𝔸(n; S).asOver S) :
    homAsOverEquiv T (f * g) = homAsOverEquiv T f * homAsOverEquiv T g := by
  simp only [← homAsOverRingEquiv_apply, map_mul]

/-- The tuple of functions of a sum of points of affine space is the sum of their tuples of
functions. -/
@[simp]
lemma homAsOverEquiv_add (T : Over S) (f g : T ⟶ 𝔸(n; S).asOver S) :
    homAsOverEquiv T (f + g) = homAsOverEquiv T f + homAsOverEquiv T g := by
  simp only [← homAsOverRingEquiv_apply, map_add]

end

end AlgebraicGeometry.AffineSpace
