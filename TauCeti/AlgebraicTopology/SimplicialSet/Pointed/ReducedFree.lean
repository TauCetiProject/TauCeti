/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialSet.Pointed.Smash.Basic
public import TauCeti.LinearAlgebra.Finsupp.ReducedFree

/-!
# The reduced free module on a pointed simplicial set

For a ring `R` and a pointed simplicial set `X`, the reduced free module `R~[X]` has as
`n`-simplices the reduced free `R`-module on the pointed set `X_n`: the free module on `X_n`
modulo the generator of the basepoint. Simplicial operators act on generators, and the basepoint
is zero. This is the functor `PointedSSet.reducedFree R`, and the generators give the based map
`PointedSSet.reducedFreeι R X : X ⟶ R~[X]`, natural in `X` (`PointedSSet.toReducedFree R`).

For a commutative ring `R`, the external product of generators `[x] ∧ [y] ↦ [x ∧ y]` extends
bilinearly to based maps `R~[X] ∧ R~[Y] ⟶ R~[X ∧ Y]`. With the unit `S⁰ ⟶ R~[S⁰]` given by the
generators, they make `R~[-]` a lax braided functor on pointed simplicial sets with the smash
product, and `X ⟶ R~[X]` a monoidal natural transformation. Applied to the spheres
`Sⁿ = (S¹)^∧n`, this gives the commutative ring structure of the Eilenberg–MacLane symmetric
spectrum `HR`, with levels `R~[Sⁿ]`, and its unit map from the sphere spectrum.

## Main definitions

* `PointedSSet.reducedFree R`: the reduced free `R`-module functor `X ↦ R~[X]`.
* `PointedSSet.reducedFreeι R X`: the based map `X ⟶ R~[X]` sending a simplex to its generator,
  and `PointedSSet.toReducedFree R`: the corresponding natural transformation.
* `PointedSSet.reducedFreeμ R X Y`: the external product `R~[X] ∧ R~[Y] ⟶ R~[X ∧ Y]`.

## Main statements

* The instance `(PointedSSet.reducedFree R).LaxBraided`, and the instance stating that
  `PointedSSet.toReducedFree R` is a monoidal natural transformation.

## References

* P. G. Goerss and J. F. Jardine, *Simplicial homotopy theory*, Progress in Mathematics 174,
  Birkhäuser, 1999, Chapter III.
* M. Hovey, B. Shipley and J. Smith, *Symmetric spectra*, J. Amer. Math. Soc. 13 (2000),
  Section 1.
-/

public section

universe u

open CategoryTheory MonoidalCategory Simplicial

namespace TauCeti.PointedSSet

noncomputable section

section Ring

variable (R : Type u) [Ring R]

/-- The reduced free `R`-module `R~[X]` on a pointed simplicial set `X`: its `n`-simplices form the
reduced free module on the `n`-simplices of `X` pointed at the basepoint, simplicial operators act
on generators, and the basepoint is zero. -/
-- The `n`-simplices of `R~[X]` unfold at implicit transparency to the module
-- `ReducedFreeModule R (X.point n)`, so that the module API applies to them.
@[expose, implicit_reducible]
def reducedFree : PointedSSet.{u} ⥤ PointedSSet.{u} where
  obj X :=
    { left := ⟨⟨⟩⟩
      right :=
        { obj n := ReducedFreeModule R (X.point n)
          map f := ↾(ReducedFreeModule.map R (X.right.map f ·) (X.map_point f))
          map_id n := by
            ext v
            induction v using ReducedFreeModule.induction_on <;> simp_all
          map_comp f g := by
            ext v
            induction v using ReducedFreeModule.induction_on <;> simp_all }
      hom :=
        { app n := ↾fun _ ↦ (0 : ReducedFreeModule R (X.point n))
          naturality _ _ _ := by ext; simp } }
  map {X Y} f := Under.homMk
    { app n := ↾(ReducedFreeModule.map R (f.right.app n ·) (app_point f n))
      naturality n m g := by
        ext v
        induction v using ReducedFreeModule.induction_on with
        | zero => simp
        | add v w hv hw => simp_all
        | smul_mk r x => simp }
    (by ext; simp)
  map_id X := by
    ext n v
    induction v using ReducedFreeModule.induction_on <;> simp_all
  map_comp f g := by
    ext n v
    induction v using ReducedFreeModule.induction_on <;> simp_all

variable {R} {X Y : PointedSSet.{u}} {n m : SimplexCategoryᵒᵖ}

@[simp]
lemma reducedFree_obj_point (X : PointedSSet.{u}) (n : SimplexCategoryᵒᵖ) :
    ((reducedFree R).obj X).point n = (0 : ReducedFreeModule R (X.point n)) :=
  -- The structure map of `R~[X]` is the constant map to `0` by definition, so the right-hand side
  -- of `hom_app` is `0` up to unfolding `reducedFree`.
  (hom_app ((reducedFree R).obj X) n (SSet.stdSimplex.const 0 0 n)).symm

/-- Simplicial operators act on `R~[X]` through their action on generators. -/
@[simp]
lemma reducedFree_obj_map (f : n ⟶ m) (v : ((reducedFree R).obj X).right.obj n) :
    ((reducedFree R).obj X).right.map f v =
      ReducedFreeModule.map R (X.right.map f ·) (X.map_point f) v := (rfl)

/-- A based map `f` acts on `R~[X]` through its action on generators. -/
@[simp]
lemma reducedFree_map_app (f : X ⟶ Y) (v : ((reducedFree R).obj X).right.obj n) :
    ((reducedFree R).map f).right.app n v =
      ReducedFreeModule.map R (f.right.app n ·) (app_point f n) v := (rfl)

variable (R) in
/-- The based map `X ⟶ R~[X]` sending each simplex to its generator; the basepoint goes to
zero. -/
def reducedFreeι (X : PointedSSet.{u}) : X ⟶ (reducedFree R).obj X :=
  Under.homMk
    { app n := ↾fun x : X.right.obj n ↦
        (ReducedFreeModule.mk R x : ((reducedFree R).obj X).right.obj n)
      naturality n m f := by
        ext x
        exact (ReducedFreeModule.map_mk R _ _ x).symm }
    (by
      ext n x
      exact (congrArg (ReducedFreeModule.mk R) (X.hom_app n x)).trans
        (ReducedFreeModule.mk_self R))

@[simp]
lemma reducedFreeι_right_app (x : X.right.obj n) :
    (reducedFreeι R X).right.app n x = ReducedFreeModule.mk R x := (rfl)

variable (R) in
/-- The natural based map `X ⟶ R~[X]` sending each simplex to its generator. -/
def toReducedFree : 𝟭 PointedSSet.{u} ⟶ reducedFree R where
  app X := reducedFreeι R X
  naturality X Y f := by
    ext n x
    exact (ReducedFreeModule.map_mk R _ _ x).symm

@[simp]
lemma toReducedFree_app (X : PointedSSet.{u}) : (toReducedFree R).app X = reducedFreeι R X :=
  (rfl)

end Ring

section CommRing

variable (R : Type u) [CommRing R]

/-- The external product of reduced free modules along the smash product commutes with
simplicial operators. -/
private lemma map₂_smashMk_map {X Y : PointedSSet.{u}} {n m : SimplexCategoryᵒᵖ} (f : n ⟶ m)
    (v : ReducedFreeModule R (X.point n)) (w : ReducedFreeModule R (Y.point n)) :
    ReducedFreeModule.map₂ R (smashMk (X := X) (Y := Y) (n := m))
        (fun _ ↦ smashMk_point_left _) (fun _ ↦ smashMk_point_right _)
        (ReducedFreeModule.map R (X.right.map f ·) (X.map_point f) v)
        (ReducedFreeModule.map R (Y.right.map f ·) (Y.map_point f) w) =
      ReducedFreeModule.map R ((X ⊗ Y).right.map f ·) ((X ⊗ Y).map_point f)
        (ReducedFreeModule.map₂ R (smashMk (X := X) (Y := Y) (n := n))
          (fun _ ↦ smashMk_point_left _) (fun _ ↦ smashMk_point_right _) v w) := by
  simp [ReducedFreeModule.map_map₂, ReducedFreeModule.map₂_map_left,
    ReducedFreeModule.map₂_map_right]

/-- The external product `R~[X] ∧ R~[Y] ⟶ R~[X ∧ Y]`, the bilinear extension of
`[x] ∧ [y] ↦ [x ∧ y]` on generators. -/
def reducedFreeμ (X Y : PointedSSet.{u}) :
    (reducedFree R).obj X ⊗ (reducedFree R).obj Y ⟶ (reducedFree R).obj (X ⊗ Y) :=
  smashLift
    { app n := ↾fun v : ((reducedFree R).obj X).right.obj n ×
          ((reducedFree R).obj Y).right.obj n ↦
        (ReducedFreeModule.map₂ R (smashMk (X := X) (Y := Y) (n := n))
          (fun _ ↦ smashMk_point_left _) (fun _ ↦ smashMk_point_right _) v.1 v.2 :
          ((reducedFree R).obj (X ⊗ Y)).right.obj n)
      naturality n m f := by
        ext ⟨v, w⟩
        exact map₂_smashMk_map R f v w }
    (fun _ _ ↦ by
      rw [reducedFree_obj_point, reducedFree_obj_point]
      exact LinearMap.map_zero₂ (ReducedFreeModule.map₂ R (smashMk (X := X) (Y := Y)) _ _) _)
    (fun _ _ ↦ by
      rw [reducedFree_obj_point, reducedFree_obj_point]
      exact LinearMap.map_zero (ReducedFreeModule.map₂ R (smashMk (X := X) (Y := Y)) _ _ _))

variable {R} {X Y Z X' Y' : PointedSSet.{u}} {n : SimplexCategoryᵒᵖ}

/-- The external product sends a pair of elements to the bilinear extension of
`[x] ∧ [y] ↦ [x ∧ y]`. -/
@[simp]
lemma reducedFreeμ_app_smashMk (v : ((reducedFree R).obj X).right.obj n)
    (w : ((reducedFree R).obj Y).right.obj n) :
    (reducedFreeμ R X Y).right.app n (smashMk v w) =
      ReducedFreeModule.map₂ R (smashMk (X := X) (Y := Y) (n := n))
        (fun _ ↦ smashMk_point_left _) (fun _ ↦ smashMk_point_right _) v w :=
  smashLift_app_smashMk _ _ _ v w

/-- The reduced free module functor is lax monoidal for the smash product: the unit is the
generator map `S⁰ ⟶ R~[S⁰]` and the tensorator is the external product. -/
instance : (reducedFree R).LaxMonoidal where
  ε := reducedFreeι R (𝟙_ PointedSSet)
  μ := reducedFreeμ R
  μ_natural_left f X' := by
    ext n v w
    simp [ReducedFreeModule.map_map₂, ReducedFreeModule.map₂_map_left]
  μ_natural_right X' f := by
    ext n v w
    simp [ReducedFreeModule.map_map₂, ReducedFreeModule.map₂_map_right]
  associativity X Y Z := by
    ext n u w
    induction u using smashMk_induction with | h u v
    simp only [comp_right_app_apply, whiskerRight_app_smashMk, associator_hom_app_smashMk,
      whiskerLeft_app_smashMk, reducedFreeμ_app_smashMk, reducedFree_map_app,
      ReducedFreeModule.map_map₂]
    exact ReducedFreeModule.map₂_assoc _ _ _ _ _ _ _ _ _ _ _ _ _
      (fun _ _ _ ↦ associator_hom_app_smashMk _ _ _) _ _ _
  left_unitality X := by
    ext n s v
    rcases eq_point_or_eq_tensorUnitSimplex s with rfl | rfl
    · simp
    · simp
  right_unitality X := by
    ext n v s
    rcases eq_point_or_eq_tensorUnitSimplex s with rfl | rfl
    · simp
    · simp

@[simp]
lemma reducedFree_ε : Functor.LaxMonoidal.ε (reducedFree R) = reducedFreeι R (𝟙_ PointedSSet) :=
  (rfl)

@[simp]
lemma reducedFree_μ (X Y : PointedSSet.{u}) :
    Functor.LaxMonoidal.μ (reducedFree R) X Y = reducedFreeμ R X Y := (rfl)

/-- The external product is compatible with the swap of smash factors, so the reduced free module
functor is lax braided. -/
instance : (reducedFree R).LaxBraided where
  braided X Y := by
    ext n v w
    simp only [reducedFree_μ, comp_right_app_apply, braiding_hom_app_smashMk,
      reducedFreeμ_app_smashMk, reducedFree_map_app, ReducedFreeModule.map_map₂]
    exact (ReducedFreeModule.map₂_swap R _ _ _ w v).symm

/-- Sending simplices to their generators is a monoidal natural transformation `X ⟶ R~[X]`. -/
instance : NatTrans.IsMonoidal (toReducedFree R) where
  unit := by simp
  tensor X Y := by
    ext n x y
    simp

end CommRing

end

end TauCeti.PointedSSet
