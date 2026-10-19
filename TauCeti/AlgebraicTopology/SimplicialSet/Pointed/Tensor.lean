/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialSet.Pointed.Closed

-- The degreewise formulas below compute through the native undercategory presentation.
import all TauCeti.AlgebraicTopology.SimplicialSet.Pointed.Basic

/-!
# Simplicial tensors and cotensors of pointed simplicial sets

An unpointed simplicial set acts on pointed simplicial sets after adjoining a disjoint
basepoint.  The tensor of `K` and `X` is `K₊ ∧ X`, while the cotensor is the pointed mapping
simplicial set `Map_*(K₊, X)`.  Their characteristic hom-set equivalences identify both with
maps from `K` to the underlying pointed mapping simplicial set.

This supplies the tensors and cotensors for the simplicial enrichment of pointed simplicial
sets.  In particular, the construction uses the disjoint-basepoint functor and is distinct from
one-point compactification.

## Main definitions

* `PointedSSet.addBasepoint`: adjoin a disjoint basepoint to a simplicial set.
* `PointedSSet.simplicialTensor`: the bifunctor `(K, X) ↦ K₊ ∧ X`.
* `PointedSSet.simplicialCotensor`: the bifunctor `(K, X) ↦ Map_*(K₊, X)`.
* `PointedSSet.simplicialTensorHomEquiv`: the tensor hom-set equivalence.
* `PointedSSet.homSimplicialCotensorEquiv`: the cotensor hom-set equivalence.

## References

* M. Hovey, B. Shipley and J. Smith, *Symmetric spectra*, J. Amer. Math. Soc. 13 (2000),
  Section 1.
-/

public section

universe u

open CategoryTheory CategoryTheory.ConcreteCategory MonoidalCategory

namespace TauCeti.PointedSSet

/-- Adjoin a disjoint basepoint degreewise to a simplicial set. -/
@[expose]
def addBasepoint : SSet.{u} ⥤ PointedSSet.{u} where
  obj K := Under.mk (Y := K ⋙ typeToPointed ⋙ forget Pointed)
    { app := fun _ ↦ ↾fun _ ↦ none
      naturality := fun _ _ _ ↦ rfl }
  map {K L} f := Under.homMk
    { app := fun n ↦ (typeToPointed ⋙ forget Pointed).map (f.app n)
      naturality := fun n m g ↦ by
        ext x
        cases x with
        | none => rfl
        | some x => exact congrArg some (congr_hom (f.naturality g) x) }
    rfl
  map_id K := by
    ext n x
    cases x <;> rfl
  map_comp f g := by
    ext n x
    cases x <;> rfl

@[simp]
lemma addBasepoint_obj_right_obj (K : SSet.{u}) (n : SimplexCategoryᵒᵖ) :
    ((addBasepoint.obj K).right.obj n) = Option (K.obj n) :=
  (rfl)

@[simp]
lemma addBasepoint_obj_point (K : SSet.{u}) (n : SimplexCategoryᵒᵖ) :
    (addBasepoint.obj K).point n = none :=
  (rfl)

@[simp]
lemma addBasepoint_obj_map_none (K : SSet.{u}) {n m : SimplexCategoryᵒᵖ} (f : n ⟶ m) :
    (addBasepoint.obj K).right.map f none = none :=
  (rfl)

@[simp]
lemma addBasepoint_obj_map_some (K : SSet.{u}) {n m : SimplexCategoryᵒᵖ} (f : n ⟶ m)
    (x : K.obj n) :
    (addBasepoint.obj K).right.map f (some x) = some (K.map f x) :=
  (rfl)

@[simp]
lemma addBasepoint_map_right_app_none {K L : SSet.{u}} (f : K ⟶ L)
    (n : SimplexCategoryᵒᵖ) :
    (addBasepoint.map f).right.app n none = none :=
  (rfl)

@[simp]
lemma addBasepoint_map_right_app_some {K L : SSet.{u}} (f : K ⟶ L)
    (n : SimplexCategoryᵒᵖ) (x : K.obj n) :
    (addBasepoint.map f).right.app n (some x) = some (f.app n x) :=
  (rfl)

/-- Based maps from `K₊` are the same as unpointed maps from `K`. -/
def addBasepointHomEquiv (K : SSet.{u}) (X : PointedSSet.{u}) :
    (addBasepoint.obj K ⟶ X) ≃ (K ⟶ X.right) where
  toFun f :=
    { app := fun n ↦ ↾fun x ↦ f.right.app n (some x)
      naturality := fun _ _ g ↦ by
        ext x
        change f.right.app _ (some (K.map g x)) =
          X.right.map g (f.right.app _ (some x))
        exact congr_hom (f.right.naturality g)
          (show (addBasepoint.obj K).right.obj _ from some x) }
  invFun f := Under.homMk
    { app := fun n ↦ ↾fun x ↦ x.elim (X.point n) (f.app n)
      naturality := fun n m g ↦ by
        ext x
        change Option (K.obj n) at x
        cases x with
        | none => exact (X.map_point g).symm
        | some x => exact congr_hom (f.naturality g) x }
    (by
      ext n x
      exact (hom_app X n x).symm)
  left_inv f := by
    ext n x
    change Option (K.obj n) at x
    cases x with
    | none =>
        change X.point n = f.right.app n none
        simpa only [addBasepoint_obj_point] using (app_point f n).symm
    | some _ => rfl
  right_inv _ := rfl

@[simp]
lemma addBasepointHomEquiv_apply_app {K : SSet.{u}} {X : PointedSSet.{u}}
    (f : addBasepoint.obj K ⟶ X) (n : SimplexCategoryᵒᵖ) (x : K.obj n) :
    (addBasepointHomEquiv K X f).app n x = f.right.app n (some x) :=
  (rfl)

@[simp]
lemma addBasepointHomEquiv_symm_app_none {K : SSet.{u}} {X : PointedSSet.{u}}
    (f : K ⟶ X.right) (n : SimplexCategoryᵒᵖ) :
    ((addBasepointHomEquiv K X).symm f).right.app n none = X.point n :=
  (rfl)

@[simp]
lemma addBasepointHomEquiv_symm_app_some {K : SSet.{u}} {X : PointedSSet.{u}}
    (f : K ⟶ X.right) (n : SimplexCategoryᵒᵖ) (x : K.obj n) :
    ((addBasepointHomEquiv K X).symm f).right.app n (some x) = f.app n x :=
  (rfl)

/-- Forget the basepoint of a pointed simplicial set. -/
abbrev forgetBasepoint : PointedSSet.{u} ⥤ SSet.{u} :=
  Under.forget _

/-- Adjoining a disjoint basepoint is left adjoint to forgetting the basepoint. -/
def addBasepointForgetAdjunction :
    addBasepoint ⊣ forgetBasepoint :=
  Adjunction.mkOfHomEquiv
    { homEquiv := addBasepointHomEquiv
      homEquiv_naturality_right := fun f g ↦ by
        ext n x
        change g.right.app n (f.right.app n (some x)) =
          g.right.app n (f.right.app n (some x))
        rfl
      homEquiv_naturality_left_symm := fun f g ↦ by
        ext n x
        dsimp [addBasepointHomEquiv, addBasepoint, types_comp_apply] at x ⊢
        cases x <;> rfl }

/-- Tensoring a pointed simplicial set by an unpointed simplicial set:
`K ⊗ X = K₊ ∧ X`. -/
noncomputable def simplicialTensor : SSet.{u} ⥤ PointedSSet.{u} ⥤ PointedSSet.{u} :=
  addBasepoint ⋙ tensoringLeft PointedSSet.{u}

/-- Cotensoring a pointed simplicial set by an unpointed simplicial set:
`X^K = Map_*(K₊, X)`. -/
noncomputable def simplicialCotensor : SSet.{u}ᵒᵖ ⥤ PointedSSet.{u} ⥤ PointedSSet.{u} :=
  addBasepoint.op ⋙ MonoidalClosed.internalHom

@[simp]
lemma simplicialTensor_obj_obj (K : SSet.{u}) (X : PointedSSet.{u}) :
    (simplicialTensor.obj K).obj X = addBasepoint.obj K ⊗ X :=
  (rfl)

@[simp]
lemma simplicialCotensor_obj_obj (K : SSet.{u}ᵒᵖ) (X : PointedSSet.{u}) :
    (simplicialCotensor.obj K).obj X = (PointedSSet.ihom (addBasepoint.obj K.unop)).obj X :=
  (rfl)

/-- The tensor universal property, expressed using the underlying simplicial set of based maps. -/
noncomputable def simplicialTensorHomEquiv (K : SSet.{u}) (X Y : PointedSSet.{u}) :
    ((simplicialTensor.obj K).obj X ⟶ Y) ≃
      (K ⟶ ((PointedSSet.ihom X).obj Y).right) :=
  (((β_ (addBasepoint.obj K) X).homCongr (Iso.refl Y)).trans
    (PointedSSet.tensorHomEquiv X (addBasepoint.obj K) Y)).trans
      (addBasepointHomEquiv K ((PointedSSet.ihom X).obj Y))

/-- The cotensor universal property, expressed using the underlying simplicial set of based maps. -/
noncomputable def homSimplicialCotensorEquiv (K : SSet.{u}) (X Y : PointedSSet.{u}) :
    (X ⟶ (simplicialCotensor.obj (Opposite.op K)).obj Y) ≃
      (K ⟶ ((PointedSSet.ihom X).obj Y).right) :=
  (PointedSSet.tensorHomEquiv (addBasepoint.obj K) X Y).symm.trans
    (simplicialTensorHomEquiv K X Y)

/-- For each simplicial set `K`, tensor by `K` is left adjoint to cotensor by `K`. -/
noncomputable def simplicialTensorCotensorAdjunction (K : SSet.{u}) :
    simplicialTensor.obj K ⊣ simplicialCotensor.obj (Opposite.op K) :=
  ihom.adjunction (addBasepoint.obj K)

end TauCeti.PointedSSet
