/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, Axel Delaval, Jie Xu, Shitan Xu
-/
module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import Mathlib.CategoryTheory.Monoidal.Cartesian.GrpLimits
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over

/-!
# Points of the base change of a group scheme

The base change of a group scheme `G` over `X` along `s : Y ⟶ X` is the pullback functor on the
over category, lifted to group objects. This file identifies the points of the base change with
points of `G` over the same test scheme viewed over the old base, through the pullback
adjunction, and shows that this identification is multiplicative. On underlying morphisms, the
identity, product and inverse of points of the base change project to those of `G`. Base change
of group schemes preserves finite limits.

More generally, let `g : G' ⟶ G` be a morphism of group schemes lying over `f : S' ⟶ S`, not
necessarily exhibiting `G'` as a base change of `G`. If `g` is compatible with multiplication, it
carries products of points of `G'` to products of points of `G`, and hence also preserves the
identity and inversion.

## Main declarations

* `TauCeti.GroupScheme.baseChangePointMulEquiv`: the multiplicative point-group identification
  furnished by the pullback adjunction.
* `TauCeti.GroupScheme.baseChangePointMulEquiv_apply_left`: the identification is
  postcomposition with the first pullback projection.
* `TauCeti.GroupScheme.pullback_mapGrp_mul_left_fst` (and its `one`/`inv` analogues): the group
  law of a base change projects to the group law of the original group scheme.
* `TauCeti.GroupScheme.pullbackMapGrp_preservesFiniteLimits`: base change of group schemes
  preserves finite limits.
* `TauCeti.GroupScheme.mul_left_comp_of_mul_left_comp`,
  `TauCeti.GroupScheme.one_left_comp_of_mul_left_comp` and
  `TauCeti.GroupScheme.inv_left_comp_of_mul_left_comp`: a morphism `g : G' ⟶ G` of group schemes
  over a morphism of bases which is compatible with multiplication preserves products of points,
  the identity and inversion.

The naturality lemma in the test scheme is adapted from Axel Delaval, Jie Xu, and Shitan Xu's
Jacobian library, release `baef7723da528551b7d2f93bd9a9a53303b04dbc`,
`Jacobian/AlgebraicGeometry/BaseChange/GroupPoints.lean`, declaration
`AlgebraicGeometry.baseChangeHomMulEquiv_naturality_left`.

## References

* Mathlib's `Over.mapPullbackAdj` and the cartesian-monoidal structure on `Over.pullback` provide
  the point identification and its compatibility with multiplication.
-/

public section

open CategoryTheory
open scoped CategoryTheory.MonObj
namespace TauCeti.GroupScheme

open AlgebraicGeometry

universe u

variable {X Y : Scheme.{u}}

/-- The underlying map of the inverse pullback-adjunction equivalence is postcomposition with the
first pullback projection. -/
private theorem mapPullbackAdj_homEquiv_symm_left
    (s : Y ⟶ X) (G : Grp (Over X)) (T : Over Y)
    (p : T ⟶ ((Over.pullback s).mapGrp.obj G).X) :
    Over.Hom.left (((Over.mapPullbackAdj s).homEquiv T G.X).symm p) =
      Over.Hom.left p ≫ Limits.pullback.fst G.X.hom s := by
  -- `mapPullbackAdj` has no projection lemma for its hom-equivalence; this is exactly the
  -- computation rule in its public definition.
  rfl

/-- After the pullback functor's lax-monoidal map and the pulled-back multiplication, the first
projection agrees with multiplication after projecting the pair. -/
private theorem pullback_laxMonoidal_map_mul_fst
    (s : Y ⟶ X) (G : Grp (Over X)) (T : Over Y)
    (pLeft qLeft : ((Over.map s).obj T).left ⟶ Limits.pullback G.X.hom s)
    (hpq : pLeft ≫ Limits.pullback.snd G.X.hom s =
      qLeft ≫ Limits.pullback.snd G.X.hom s) :
    (((Limits.pullback.lift pLeft qLeft hpq ≫
          Over.Hom.left (Functor.LaxMonoidal.μ (Over.pullback s) G.X G.X)) ≫
        Over.Hom.left ((Over.pullback s).map μ[G.X])) ≫
      (Limits.pullback.fst G.X.hom s :
        ((Over.pullback s).mapGrp.obj G).X.left ⟶ G.X.left)) =
    (((Limits.pullback.lift pLeft qLeft hpq ≫
          Over.Hom.left (Functor.LaxMonoidal.μ (Over.pullback s) G.X G.X)) ≫
        Limits.pullback.fst (MonoidalCategoryStruct.tensorObj G.X G.X).hom s) ≫
      Over.Hom.left μ[G.X]) := by
  have hmap :
      Over.Hom.left ((Over.pullback s).map μ[G.X]) ≫
          (Limits.pullback.fst G.X.hom s :
            ((Over.pullback s).mapGrp.obj G).X.left ⟶ G.X.left) =
        Limits.pullback.fst (MonoidalCategoryStruct.tensorObj G.X G.X).hom s ≫
          Over.Hom.left μ[G.X] := by
    simp only [Over.pullback_map_left, Limits.pullback.lift_fst]
  simp only [Category.assoc, hmap]

/-- Pairing two points, applying the pullback functor's lax-monoidal map, and then projecting to
the original tensor product pairs the two projected points. -/
private theorem pullback_laxMonoidal_pair_fst
    (s : Y ⟶ X) (G : Grp (Over X)) (T : Over Y)
    (pLeft qLeft : ((Over.map s).obj T).left ⟶ Limits.pullback G.X.hom s)
    (hpq : pLeft ≫ Limits.pullback.snd G.X.hom s =
      qLeft ≫ Limits.pullback.snd G.X.hom s) :
    (Limits.pullback.lift pLeft qLeft hpq ≫
        Over.Hom.left (Functor.LaxMonoidal.μ (Over.pullback s) G.X G.X)) ≫
      Limits.pullback.fst _ s =
    Limits.pullback.lift
      (pLeft ≫ Limits.pullback.fst G.X.hom s)
      (qLeft ≫ Limits.pullback.fst G.X.hom s)
      (by
        simp only [Category.assoc, Limits.pullback.condition]
        simpa only [Category.assoc] using congrArg (fun z ↦ z ≫ s) hpq) := by
  apply Limits.pullback.hom_ext
  · rw [Category.assoc, Category.assoc,
      Over.μ_pullback_left_fst_fst G.X G.X]
    simp only [Over.pullback_obj_hom, Limits.pullback.lift_fst_assoc,
      Limits.pullback.lift_fst]
  · rw [Category.assoc, Category.assoc,
      Over.μ_pullback_left_fst_snd G.X G.X]
    simp only [Over.pullback_obj_hom, Limits.pullback.lift_snd_assoc,
      Limits.pullback.lift_snd]

/-- The adjunction between postcomposition and pullback identifies points of a base-changed group
scheme with points of the original group scheme over the same test scheme viewed over the old
base. This identification is multiplicative. -/
noncomputable def baseChangePointMulEquiv
    (s : Y ⟶ X) (G : Grp (Over X)) (T : Over Y) :
    (T ⟶ ((Over.pullback s).mapGrp.obj G).X) ≃*
      ((Over.map s).obj T ⟶ G.X) where
  toFun p := ((Over.mapPullbackAdj s).homEquiv T G.X).symm p
  invFun p := (Over.mapPullbackAdj s).homEquiv T G.X p
  left_inv := (Over.mapPullbackAdj s).homEquiv T G.X |>.right_inv
  right_inv := (Over.mapPullbackAdj s).homEquiv T G.X |>.left_inv
  map_mul' p q := by
    let pLeft : ((Over.map s).obj T).left ⟶ Limits.pullback G.X.hom s := p.left
    let qLeft : ((Over.map s).obj T).left ⟶ Limits.pullback G.X.hom s := q.left
    have hpq :
        pLeft ≫ Limits.pullback.snd G.X.hom s =
          qLeft ≫ Limits.pullback.snd G.X.hom s :=
      p.w.trans q.w.symm
    ext
    rw [mapPullbackAdj_homEquiv_symm_left]
    simp only [Hom.mul_def, Over.comp_left, Over.lift_left,
      mapPullbackAdj_homEquiv_symm_left]
    rw [Functor.mapGrp_obj_X] at p q
    erw [congrArg Over.Hom.left (Functor.obj.μ_def (F := Over.pullback s) G.X), Over.comp_left]
    exact (pullback_laxMonoidal_map_mul_fst s G T pLeft qLeft hpq).trans
      (congrArg (fun z ↦ z ≫ Over.Hom.left μ[G.X])
        (pullback_laxMonoidal_pair_fst s G T pLeft qLeft hpq))

/-- The point-group equivalence is the underlying pullback-adjunction equivalence. -/
@[simp]
theorem baseChangePointMulEquiv_apply
    (s : Y ⟶ X) (G : Grp (Over X)) (T : Over Y)
    (p : T ⟶ ((Over.pullback s).mapGrp.obj G).X) :
    baseChangePointMulEquiv s G T p =
      ((Over.mapPullbackAdj s).homEquiv T G.X).symm p := (rfl)

/-- The inverse point-group equivalence is the forward pullback-adjunction equivalence. -/
@[simp]
theorem baseChangePointMulEquiv_symm_apply
    (s : Y ⟶ X) (G : Grp (Over X)) (T : Over Y)
    (p : (Over.map s).obj T ⟶ G.X) :
    (baseChangePointMulEquiv s G T).symm p =
      (Over.mapPullbackAdj s).homEquiv T G.X p := (rfl)

/-- The underlying morphism of the point of `G` attached to a point of the base change is
postcomposition with the first pullback projection. -/
theorem baseChangePointMulEquiv_apply_left
    (s : Y ⟶ X) (G : Grp (Over X)) (T : Over Y)
    (p : T ⟶ ((Over.pullback s).mapGrp.obj G).X) :
    (baseChangePointMulEquiv s G T p).left = p.left ≫ Limits.pullback.fst G.X.hom s := by
  rw [baseChangePointMulEquiv_apply, mapPullbackAdj_homEquiv_symm_left]

/-- The identity point of a base change projects to the identity point of the original group
scheme. -/
theorem pullback_mapGrp_one_left_fst (s : Y ⟶ X) (G : Grp (Over X)) (T : Over Y) :
    (1 : T ⟶ ((Over.pullback s).mapGrp.obj G).X).left ≫ Limits.pullback.fst G.X.hom s =
      T.hom ≫ s ≫ η[G.X].left := by
  rw [← baseChangePointMulEquiv_apply_left, map_one, Hom.one_def, Over.comp_left]
  simp

/-- The product of two points of a base change projects to the product of their projections in
the original group scheme. -/
theorem pullback_mapGrp_mul_left_fst (s : Y ⟶ X) (G : Grp (Over X)) (T : Over Y)
    (p q : T ⟶ ((Over.pullback s).mapGrp.obj G).X) :
    (p * q).left ≫ Limits.pullback.fst G.X.hom s =
      Limits.pullback.lift (p.left ≫ Limits.pullback.fst G.X.hom s)
          (q.left ≫ Limits.pullback.fst G.X.hom s)
          (by rw [← baseChangePointMulEquiv_apply_left, ← baseChangePointMulEquiv_apply_left,
            Over.w, Over.w]) ≫
        μ[G.X].left := by
  rw [← baseChangePointMulEquiv_apply_left, map_mul, Hom.mul_def, Over.comp_left]
  refine congrArg (· ≫ μ[G.X].left) (Limits.pullback.hom_ext ?_ ?_) <;>
    simp only [Over.lift_left, Limits.pullback.lift_fst, Limits.pullback.lift_snd,
      baseChangePointMulEquiv_apply_left]

/-- The inverse of a point of a base change projects to the inverse of its projection in the
original group scheme. -/
theorem pullback_mapGrp_inv_left_fst (s : Y ⟶ X) (G : Grp (Over X)) (T : Over Y)
    (p : T ⟶ ((Over.pullback s).mapGrp.obj G).X) :
    p⁻¹.left ≫ Limits.pullback.fst G.X.hom s =
      p.left ≫ Limits.pullback.fst G.X.hom s ≫ ι[G.X].left := by
  rw [← baseChangePointMulEquiv_apply_left, map_inv, Hom.inv_def, Over.comp_left,
    baseChangePointMulEquiv_apply_left]
  -- `rw` cannot see through the type of `p.left`, so reassociate by unification
  exact Category.assoc _ _ _

/-- Restriction along a map of test schemes commutes with the point-group equivalence. -/
theorem baseChangePointMulEquiv_naturality_left
    (s : Y ⟶ X) (G : Grp (Over X)) {T U : Over Y} (f : U ⟶ T)
    (p : T ⟶ ((Over.pullback s).mapGrp.obj G).X) :
    baseChangePointMulEquiv s G U (f ≫ p) =
      (Over.map s).map f ≫ baseChangePointMulEquiv s G T p := by
  simp only [baseChangePointMulEquiv_apply]
  exact (Over.mapPullbackAdj s).homEquiv_naturality_left_symm f p

/-- Pullback of group schemes along an arbitrary base morphism preserves finite limits. In
particular, it preserves kernels. -/
noncomputable instance pullbackMapGrp_preservesFiniteLimits (s : Y ⟶ X) :
    Limits.PreservesFiniteLimits (Over.pullback s).mapGrp :=
  -- Forgetting the group structure after the lifted pullback functor is definitionally the same
  -- functor as first forgetting and then applying pullback in the over category.
  have : Limits.PreservesFiniteLimits ((Over.pullback s).mapGrp ⋙ Grp.forget (Over Y)) :=
    ⟨fun J _ _ ↦ inferInstanceAs
      (Limits.PreservesLimitsOfShape J (Grp.forget (Over X) ⋙ Over.pullback s))⟩
  have : Limits.ReflectsFiniteLimits (Grp.forget (Over Y)) := ⟨fun _ _ _ ↦ inferInstance⟩
  Limits.preservesFiniteLimits_of_reflects_of_preserves _ (Grp.forget (Over Y))

/-! ### Multiplicative morphisms of group schemes over different bases -/

section MulLeftComp

open MonoidalCategory

variable {S S' : Scheme.{u}} {f : S' ⟶ S} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G']
  {g : G'.left ⟶ G.left} (w : g ≫ G.hom = G'.hom ≫ f)
  (hμ : μ[G'].left ≫ g = Limits.pullback.map _ _ _ _ g g f w.symm w.symm ≫ μ[G].left)
include hμ

/-- **A multiplicative morphism of group schemes preserves products of points.** If `g : G' ⟶ G`
lies over `f : S' ⟶ S` and is compatible with multiplication, then it carries the product of two
points of `G'` with values in an `S'`-scheme `T` to the product of their images, as points of `G`
with values in `T` over `f`. -/
theorem mul_left_comp_of_mul_left_comp {T : Over S'} (a b : T ⟶ G') :
    (a * b).left ≫ g =
      Limits.pullback.lift (a.left ≫ g) (b.left ≫ g) (by simp [w]) ≫ μ[G].left := by
  rw [Hom.mul_def, Over.comp_left, Category.assoc, hμ, ← Category.assoc]
  congr 1
  apply Limits.pullback.hom_ext <;> simp

/-- **A multiplicative morphism of group schemes preserves the identity.** If `g : G' ⟶ G` lies
over `f : S' ⟶ S` and is compatible with multiplication, then it carries the identity section of
`G'` to the base change along `f` of that of `G`. -/
theorem one_left_comp_of_mul_left_comp : η[G'].left ≫ g = f ≫ η[G].left := by
  -- `e = η ≫ g` is an idempotent in the group of `S'`-points of `G` over `f`
  let e : Over.mk f ⟶ G := Over.homMk (η[G'].left ≫ g) (by simp [w])
  have he : e * e = e := by
    ext
    have h := mul_left_comp_of_mul_left_comp w hμ (1 : 𝟙_ (Over S') ⟶ G') 1
    rw [mul_one] at h
    simpa [Hom.mul_def, Hom.one_def, e] using h.symm
  simpa [e, Hom.one_def] using congr($(mul_eq_left.mp he).left)

/-- **A multiplicative morphism of group schemes preserves inversion.** If `g : G' ⟶ G` lies over
`f : S' ⟶ S` and is compatible with multiplication, then it intertwines the inversions of `G'` and
`G`. -/
theorem inv_left_comp_of_mul_left_comp : ι[G'].left ≫ g = g ≫ ι[G].left := by
  -- `g` and `ι ≫ g` are mutually inverse points of `G` with values in `G'` over `G'.hom ≫ f`
  let a : Over.mk (G'.hom ≫ f) ⟶ G := Over.homMk g w
  let b : Over.mk (G'.hom ≫ f) ⟶ G := Over.homMk (ι[G'].left ≫ g) (by simp [w])
  have hab : a * b = 1 := by
    ext
    have h := mul_left_comp_of_mul_left_comp w hμ (𝟙 G') ι[G']
    rw [Hom.mul_def, GrpObj.right_inv, Over.comp_left, Category.assoc,
      one_left_comp_of_mul_left_comp w hμ] at h
    simpa [Hom.mul_def, Hom.one_def, a, b] using h.symm
  simpa [a, b, Hom.inv_def] using congr($(eq_inv_of_mul_eq_one_right hab).left)

end MulLeftComp

end TauCeti.GroupScheme
