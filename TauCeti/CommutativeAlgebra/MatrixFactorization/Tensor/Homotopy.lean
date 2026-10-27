/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CommutativeAlgebra.MatrixFactorization.Tensor.Basic
public import TauCeti.CategoryTheory.Preadditive.MorphismIdeal.Bifunctor

/-!
# Tensor products on the homotopy category of matrix factorizations

The tensor product of a matrix factorization of `v` with one of `w` is a matrix factorization
of `v + w`, and tensoring with a null-homotopic map on either side gives a null-homotopic map.
Hence the tensor product descends to an `S`-bilinear bifunctor

```text
HMF(S,v) ⥤ HMF(S,w) ⥤ HMF(S,v+w)
```

on the homotopy categories, given on classes of factorizations and of closed maps by the class
of their tensor product. Tensoring with the class of a fixed factorization, on either side, is
the functor induced on homotopy categories by tensoring with that factorization. In particular,
a homotopy equivalence in either variable induces an isomorphism of tensor products in
`HMF(S,v+w)`.

The descent is the general one for bifunctors on morphism-ideal quotients,
`TauCeti.MorphismIdeal.map₂`, applied to the null-homotopic ideals.

## Main definitions

* `TauCeti.MatrixFactorization.homotopyTensor`: the tensor-product bifunctor on homotopy
  categories of matrix factorizations.

## References

* H. Knörrer, *Cohen–Macaulay modules on hypersurface singularities I*, Invent. Math. **88**
  (1987), 153–164, Section 2.
* D. Orlov, *Triangulated categories of singularities and D-branes in Landau–Ginzburg models*,
  Proc. Steklov Inst. Math. **246** (2004), Sections 1.2 and 3.
-/

public section

universe u

namespace TauCeti.MatrixFactorization

open CategoryTheory

variable (S : Type u) [CommRing S] (v w : S)

/-- The **tensor-product bifunctor** on homotopy categories of matrix factorizations, from
`HMF(S,v)` and `HMF(S,w)` to `HMF(S,v+w)`. On classes of factorizations and of closed maps it
is the class of their tensor product. -/
-- Exposed so that its values on classes of factorizations have computed types.
@[expose]
noncomputable def homotopyTensor :
    HomotopyCategory (S := S) (w := v) ⥤ HomotopyCategory (S := S) (w := w) ⥤
      HomotopyCategory (S := S) (w := v + w) :=
  MorphismIdeal.map₂ _ _ _ (tensor S v w) nullHomotopic_le_comap_tensor_flip_obj
    nullHomotopic_le_comap_tensor_obj

variable {S v w}

/-- Tensoring on the left with the class of a fixed factorization `X` is the functor induced on
homotopy categories by tensoring on the left with `X`. -/
theorem homotopyTensor_obj_quotientFunctor_obj (X : MatrixFactorization S v) :
    (homotopyTensor S v w).obj ((nullHomotopic (S := S) (w := v)).quotientFunctor.obj X) =
      (nullHomotopic (S := S) (w := w)).map _ ((tensor S v w).obj X)
        (nullHomotopic_le_comap_tensor_obj X) :=
  MorphismIdeal.map₂_obj_quotientFunctor_obj ..

/-- Tensoring on the right with the class of a fixed factorization `Y` is the functor induced on
homotopy categories by tensoring on the right with `Y`. -/
theorem homotopyTensor_flip_obj_quotientFunctor_obj (Y : MatrixFactorization S w) :
    (homotopyTensor S v w).flip.obj ((nullHomotopic (S := S) (w := w)).quotientFunctor.obj Y) =
      (nullHomotopic (S := S) (w := v)).map _ ((tensor S v w).flip.obj Y)
        (nullHomotopic_le_comap_tensor_flip_obj Y) :=
  MorphismIdeal.map₂_flip_obj_quotientFunctor_obj ..

/-- The tensor product of the classes of two factorizations is the class of their tensor
product. -/
@[simp]
theorem homotopyTensor_obj_obj (X : MatrixFactorization S v) (Y : MatrixFactorization S w) :
    ((homotopyTensor S v w).obj ((nullHomotopic (S := S) (w := v)).quotientFunctor.obj X)).obj
        ((nullHomotopic (S := S) (w := w)).quotientFunctor.obj Y) =
      (nullHomotopic (S := S) (w := v + w)).quotientFunctor.obj (tensorObj X Y) :=
  (rfl)

/-- Tensoring a class with the class of a closed map in the second variable gives the class of
their tensor product. -/
@[simp]
theorem homotopyTensor_obj_map (X : MatrixFactorization S v) {Y Y' : MatrixFactorization S w}
    (g : Y ⟶ Y') :
    ((homotopyTensor S v w).obj ((nullHomotopic (S := S) (w := v)).quotientFunctor.obj X)).map
        ((nullHomotopic (S := S) (w := w)).quotientFunctor.map g) =
      (nullHomotopic (S := S) (w := v + w)).quotientFunctor.map (tensorHom (𝟙 X) g) :=
  (rfl)

/-- Tensoring the class of a closed map in the first variable with a class gives the class of
their tensor product. -/
@[simp]
theorem homotopyTensor_map_app {X X' : MatrixFactorization S v} (f : X ⟶ X')
    (Y : MatrixFactorization S w) :
    ((homotopyTensor S v w).map ((nullHomotopic (S := S) (w := v)).quotientFunctor.map f)).app
        ((nullHomotopic (S := S) (w := w)).quotientFunctor.obj Y) =
      (nullHomotopic (S := S) (w := v + w)).quotientFunctor.map (tensorHom f (𝟙 Y)) :=
  (rfl)

/-- The tensor product on homotopy categories agrees with the tensor product of matrix
factorizations followed by passage to homotopy classes. -/
theorem quotientFunctor_comp_homotopyTensor_comp_whiskeringLeft :
    (nullHomotopic (S := S) (w := v)).quotientFunctor ⋙ homotopyTensor S v w ⋙
        (Functor.whiskeringLeft _ _ _).obj (nullHomotopic (S := S) (w := w)).quotientFunctor =
      tensor S v w ⋙
        (Functor.whiskeringRight _ _ _).obj (nullHomotopic (S := S) (w := v + w)).quotientFunctor :=
  MorphismIdeal.quotientFunctor_comp_map₂_comp_whiskeringLeft ..

instance : (homotopyTensor S v w).Additive := by
  unfold homotopyTensor
  infer_instance

instance (X : HomotopyCategory (S := S) (w := v)) : ((homotopyTensor S v w).obj X).Additive := by
  unfold homotopyTensor
  infer_instance

instance (Y : HomotopyCategory (S := S) (w := w)) :
    ((homotopyTensor S v w).flip.obj Y).Additive := by
  unfold homotopyTensor
  infer_instance

instance : (homotopyTensor S v w).Linear S := by
  unfold homotopyTensor
  infer_instance

instance (X : HomotopyCategory (S := S) (w := v)) : ((homotopyTensor S v w).obj X).Linear S := by
  unfold homotopyTensor
  infer_instance

instance (Y : HomotopyCategory (S := S) (w := w)) :
    ((homotopyTensor S v w).flip.obj Y).Linear S := by
  unfold homotopyTensor
  infer_instance

end TauCeti.MatrixFactorization
