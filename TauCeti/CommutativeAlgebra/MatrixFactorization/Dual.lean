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

Duality is **contravariant**, as the roadmap records: a morphism `f : X ⟶ Y` of matrix
factorizations dualizes to a morphism `dualHom f : Yᵛ ⟶ Xᵛ`, whose two components are the
transposes of the components of `f`, and whose commutativity conditions are the commutativity
conditions of `f` with the two differentials exchanged. Both the objects and the morphisms are
here; the double dual, which turns duality into an equivalence of the two potentials, is the next
step.

## Main definitions

* `MatrixFactorization.dual`: the dual of a matrix factorization of `w`, of potential `-w`.
* `MatrixFactorization.dualHom`: the dual of a morphism, contravariantly.

## Main results

* `MatrixFactorization.dualHom_f₀`, `MatrixFactorization.dualHom_f₁`: the components of a dual
  morphism.
* `MatrixFactorization.dualHom_id`, `MatrixFactorization.dualHom_comp`: the dual of a morphism
  reverses identity and composition, which is what makes duality contravariant.

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
    (dual (S := S) (w := w) X).obj.d₀ = FGModuleCat.dualHom S X.obj.d₁ := rfl

@[simp] theorem dual_obj_d₁ (X : MatrixFactorization S w) :
    (dual (S := S) (w := w) X).obj.d₁ = -FGModuleCat.dualHom S X.obj.d₀ := rfl

/-- The dual of a morphism of matrix factorizations is a morphism from the dual of the target to
the dual of the source, with transposed components. -/
@[expose] def dualHom {X Y : MatrixFactorization S w} (f : X ⟶ Y) :
    dual (S := S) (w := w) Y ⟶ dual (S := S) (w := w) X :=
  InducedCategory.homMk (CurvedDuplex.dualHom f.hom)

@[simp] theorem dualHom_f₀ {X Y : MatrixFactorization S w} (f : X ⟶ Y) :
    (dualHom f).hom.f₀ = FGModuleCat.dualHom S f.hom.f₀ := rfl

@[simp] theorem dualHom_f₁ {X Y : MatrixFactorization S w} (f : X ⟶ Y) :
    (dualHom f).hom.f₁ = FGModuleCat.dualHom S f.hom.f₁ := rfl

@[simp] theorem dualHom_id (X : MatrixFactorization S w) :
    dualHom (𝟙 X) = 𝟙 (dual (S := S) (w := w) X) :=
  InducedCategory.hom_ext (CurvedDuplex.dualHom_id _)

@[simp] theorem dualHom_comp {X Y Z : MatrixFactorization S w} (f : X ⟶ Y) (g : Y ⟶ Z) :
    dualHom (f ≫ g) = dualHom g ≫ dualHom f :=
  InducedCategory.hom_ext (CurvedDuplex.dualHom_comp _ _)

end MatrixFactorization

end TauCeti
