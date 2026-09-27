/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Curved.Dual
public import TauCeti.CommutativeAlgebra.MatrixFactorization.Basic

/-!
# Duality for matrix factorizations

The dual of a finite-projective matrix factorization `P` of `w` is the factorization
```
(Pᵛ)₀ = P₀ᵛ                    (Pᵛ)₁ = P₁ᵛ
d₀ᵛ = (d₁)ᵗ : P₀ᵛ ⟶ P₁ᵛ        d₁ᵛ = -(d₀)ᵗ : P₁ᵛ ⟶ P₀ᵛ
```
of `-w`: the two composites are multiplication by `-w`, because a crossed pair of transposes is
the transpose of the original composite and the single minus sign turns `w` into `-w`.
`TauCeti.Algebra.Homology.Curved.Dual` proves the same statement for curved duplexes of
projective modules, and the crossed transposes are exactly the convention used there.

Duality is **contravariant**: a morphism `f : X ⟶ Y` of matrix factorizations dualizes to a
morphism `dualMap f : Yᵛ ⟶ Xᵛ`, whose two components are the transposes of the components of
`f`, and whose commutativity conditions are the commutativity conditions of `f` with the two
differentials exchanged. The two are packaged together as the contravariant functor
`MatrixFactorization.dualFunctor` from the opposite category of matrix factorizations of `w` to
the category of matrix factorizations of `-w`, so duality is available through the category
API.
The object-level double dual is also here, and is isomorphic to the original: dualizing twice
lands back at the potential `w` and at an isomorphic factorization.

## Main definitions

* `MatrixFactorization.dual`: the dual of a matrix factorization of `w`, of potential `-w`.
* `MatrixFactorization.dualMap`: the dual of a morphism, contravariantly.
* `MatrixFactorization.dualFunctor`: duality as the contravariant functor
  `(MatrixFactorization S w)ᵒᵖ ⥤ MatrixFactorization S (-w)`.
* `MatrixFactorization.doubleDual`, `MatrixFactorization.doubleDualIso`: the double dual, of the
  original potential, and its isomorphism with the original factorization.

## Main results

* `MatrixFactorization.dualMap_f₀`, `MatrixFactorization.dualMap_f₁`: the components of a dual
  morphism.
* `MatrixFactorization.dualMap_id`, `MatrixFactorization.dualMap_comp`: the dual of a morphism
  reverses identity and composition, which is what makes duality contravariant.
* `MatrixFactorization.dualFunctor_obj`, `MatrixFactorization.dualFunctor_map`: the object and
  morphism maps of the contravariant duality functor.
* `MatrixFactorization.doubleDualIso`, `MatrixFactorization.doubleDualIso_f₀`,
  `MatrixFactorization.doubleDualIso_f₁`, `MatrixFactorization.doubleDualIso_inv_f₀`,
  `MatrixFactorization.doubleDualIso_inv_f₁`: a double dual is isomorphic to the original
  matrix factorization, by the evaluation pairing with the single minus sign on the even
  component, and its two components and the two components of its inverse are the evaluation
  isomorphisms.

## References

* D. Eisenbud, *Homological algebra on a complete intersection, with an application to group
  representations*, Trans. Amer. Math. Soc. **260** (1980), Section 5, for duality of matrix
  factorizations of finite free modules.
* The finite-projective formulation and the ambient curved-duplex convention follow
  `TauCeti.CommutativeAlgebra.MatrixFactorization.Basic` and
  `TauCeti.Algebra.Homology.Curved.Duplex`.
-/

public section

universe u

namespace TauCeti

open CategoryTheory

variable (S : Type u) [CommRing S] (w : S)

namespace MatrixFactorization

variable {S w}

/-- The dual of a finite-projective matrix factorization of `w` is a finite-projective matrix
factorization of `-w` whose differentials are the crossed transposes. -/
abbrev dual (X : MatrixFactorization S w) : MatrixFactorization S (-w) :=
  ofCurvedDuplex X.obj.dual inferInstance inferInstance

@[simp] theorem dual_obj (X : MatrixFactorization S w) :
    (dual (S := S) (w := w) X).obj = CurvedDuplex.dual X.obj := rfl

@[simp] theorem dual_obj_X₀ (X : MatrixFactorization S w) :
    (dual (S := S) (w := w) X).obj.X₀ = FGModuleCat.dual S X.obj.X₀ := rfl

@[simp] theorem dual_obj_X₁ (X : MatrixFactorization S w) :
    (dual (S := S) (w := w) X).obj.X₁ = FGModuleCat.dual S X.obj.X₁ := rfl

@[simp] theorem dual_obj_d₀ (X : MatrixFactorization S w) :
    (dual (S := S) (w := w) X).obj.d₀ = FGModuleCat.dualMap S X.obj.d₁ := rfl

@[simp] theorem dual_obj_d₁ (X : MatrixFactorization S w) :
    (dual (S := S) (w := w) X).obj.d₁ = -FGModuleCat.dualMap S X.obj.d₀ := rfl

/-- The dual of a morphism of matrix factorizations is a morphism from the dual of the target to
the dual of the source, with transposed components. -/
def dualMap {X Y : MatrixFactorization S w} (f : X ⟶ Y) :
    dual (S := S) (w := w) Y ⟶ dual (S := S) (w := w) X :=
  InducedCategory.homMk (CurvedDuplex.dualMap f.hom)

/-- The underlying curved-duplex morphism of a dual morphism of matrix factorizations. -/
theorem dualMap_hom {X Y : MatrixFactorization S w} (f : X ⟶ Y) :
    (dualMap f).hom = CurvedDuplex.dualMap f.hom := (rfl)

@[simp] theorem dualMap_f₀ {X Y : MatrixFactorization S w} (f : X ⟶ Y) :
    (dualMap f).hom.f₀ = FGModuleCat.dualMap S f.hom.f₀ := by
  rw [dualMap_hom, CurvedDuplex.dualMap_f₀]

@[simp] theorem dualMap_f₁ {X Y : MatrixFactorization S w} (f : X ⟶ Y) :
    (dualMap f).hom.f₁ = FGModuleCat.dualMap S f.hom.f₁ := by
  rw [dualMap_hom, CurvedDuplex.dualMap_f₁]

@[simp] theorem dualMap_id (X : MatrixFactorization S w) :
    dualMap (𝟙 X) = 𝟙 (dual (S := S) (w := w) X) :=
  InducedCategory.hom_ext (CurvedDuplex.dualMap_id _)

@[simp] theorem dualMap_comp {X Y Z : MatrixFactorization S w} (f : X ⟶ Y) (g : Y ⟶ Z) :
    dualMap (f ≫ g) = dualMap g ≫ dualMap f :=
  InducedCategory.hom_ext (CurvedDuplex.dualMap_comp _ _)

/-- **Duality of matrix factorizations is contravariant**: a morphism of matrix factorizations of
`w` dualizes to a morphism of matrix factorizations of `-w` from the dual of its target to the
dual of its source, and duality reverses identity and composition. The morphism map is
`MatrixFactorization.dualMap` and the two functor laws are `MatrixFactorization.dualMap_id` and
`MatrixFactorization.dualMap_comp`, so the dual is available through the category API rather than
only as a pair of separate functions. -/
def dualFunctor : (MatrixFactorization S w)ᵒᵖ ⥤ MatrixFactorization S (-w) where
  obj X := MatrixFactorization.dual (S := S) (w := w) X.unop
  map f := MatrixFactorization.dualMap f.unop
  map_id X := MatrixFactorization.dualMap_id X.unop
  map_comp f g := MatrixFactorization.dualMap_comp g.unop f.unop

@[simp] theorem dualFunctor_obj (X : (MatrixFactorization S w)ᵒᵖ) :
    (dualFunctor (S := S) (w := w)).obj X = MatrixFactorization.dual (S := S) (w := w) X.unop := by
  unfold dualFunctor
  rfl

/-- The morphism part of `dualFunctor` is the transpose `MatrixFactorization.dualMap`, along the
two canonical identifications that its object part exhibits. The form is the one of the finite
convolution dual in `FiniteLocallyFreeBicommutativeHopfAlgCat.dualFunctor_map`, so that the
definition of the functor itself can stay opaque. -/
@[simp] theorem dualFunctor_map {X Y : (MatrixFactorization S w)ᵒᵖ} (f : X ⟶ Y) :
    (dualFunctor (S := S) (w := w)).map f =
      eqToHom (dualFunctor_obj (S := S) (w := w) X) ≫ MatrixFactorization.dualMap f.unop
        ≫ eqToHom (dualFunctor_obj (S := S) (w := w) Y).symm := by
  unfold dualFunctor
  rfl

/-- The double dual of a matrix factorization is a matrix factorization of the *same* potential: the
two minus signs contributed by the two duals cancel, so it is a factorization of `w` and not of
`- -w`. -/
abbrev doubleDual (X : MatrixFactorization S w) : MatrixFactorization S w :=
  ofCurvedDuplex X.obj.doubleDual inferInstance inferInstance

@[simp] theorem doubleDual_obj (X : MatrixFactorization S w) :
    (doubleDual (S := S) (w := w) X).obj = CurvedDuplex.doubleDual X.obj := rfl

@[simp] theorem doubleDual_obj_X₀ (X : MatrixFactorization S w) :
    (doubleDual (S := S) (w := w) X).obj.X₀ =
      FGModuleCat.dual S (FGModuleCat.dual S X.obj.X₀) := rfl

@[simp] theorem doubleDual_obj_X₁ (X : MatrixFactorization S w) :
    (doubleDual (S := S) (w := w) X).obj.X₁ =
      FGModuleCat.dual S (FGModuleCat.dual S X.obj.X₁) := rfl

@[simp] theorem doubleDual_obj_d₀ (X : MatrixFactorization S w) :
    (doubleDual (S := S) (w := w) X).obj.d₀ =
      -FGModuleCat.dualMap S (FGModuleCat.dualMap S X.obj.d₀) := rfl

@[simp] theorem doubleDual_obj_d₁ (X : MatrixFactorization S w) :
    (doubleDual (S := S) (w := w) X).obj.d₁ =
      -FGModuleCat.dualMap S (FGModuleCat.dualMap S X.obj.d₁) := rfl

/-- A double dual of a matrix factorization is isomorphic to the original, by the evaluation
pairing with the single minus sign on the even component. -/
noncomputable def doubleDualIso (X : MatrixFactorization S w) :
    doubleDual (S := S) (w := w) X ≅ X :=
  ObjectProperty.isoMk (P := MatrixFactorization.isProjective S w)
    (CurvedDuplex.doubleDualIso X.obj)

theorem doubleDualIso_hom_hom (X : MatrixFactorization S w) :
    (X.doubleDualIso).hom.hom = (CurvedDuplex.doubleDualIso X.obj).hom := (rfl)

theorem doubleDualIso_inv_hom (X : MatrixFactorization S w) :
    (X.doubleDualIso).inv.hom = (CurvedDuplex.doubleDualIso X.obj).inv := (rfl)

@[simp] theorem doubleDualIso_f₀ (X : MatrixFactorization S w) :
    (X.doubleDualIso).hom.hom.f₀ = -(FGModuleCat.dualEvalIso S X.obj.X₀).hom :=
  by rw [doubleDualIso_hom_hom, CurvedDuplex.doubleDualIso_f₀]

@[simp] theorem doubleDualIso_f₁ (X : MatrixFactorization S w) :
    (X.doubleDualIso).hom.hom.f₁ = (FGModuleCat.dualEvalIso S X.obj.X₁).hom :=
  by rw [doubleDualIso_hom_hom, CurvedDuplex.doubleDualIso_f₁]

/-- The even component of the inverse of the double dual isomorphism is the negated inverse
evaluation isomorphism. -/
@[simp] theorem doubleDualIso_inv_f₀ (X : MatrixFactorization S w) :
    (X.doubleDualIso).inv.hom.f₀ = -(FGModuleCat.dualEvalIso S X.obj.X₀).inv :=
  by rw [doubleDualIso_inv_hom, CurvedDuplex.doubleDualIso_inv_f₀]

/-- The odd component of the inverse of the double dual isomorphism is the inverse evaluation
isomorphism. -/
@[simp] theorem doubleDualIso_inv_f₁ (X : MatrixFactorization S w) :
    (X.doubleDualIso).inv.hom.f₁ = (FGModuleCat.dualEvalIso S X.obj.X₁).inv :=
  by rw [doubleDualIso_inv_hom, CurvedDuplex.doubleDualIso_inv_f₁]

end MatrixFactorization

end TauCeti
