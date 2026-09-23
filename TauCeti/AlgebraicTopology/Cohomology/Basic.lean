/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.SingularHomology.Basic
public import TauCeti.Algebra.Homology.LinearYoneda

/-!
# Singular cochains and singular cohomology

Let `C` be a `k`-linear abelian category with coproducts, and let `R` and `M` be objects of `C`.
The singular cochain complex of a topological space `X` is obtained by applying the contravariant
functor `Hom(-, M)` to the singular chain complex of `X` with coefficients in `R`: in degree `n`
it is the `k`-module of morphisms `Cₙ(X; R) ⟶ M`, and its differential is precomposition with the
singular boundary.  Its cohomology is the singular cohomology of `X`.  A continuous map
`f : X ⟶ Y` induces a cochain map from the cochains of `Y` to those of `X`, precomposition with the
chain map induced by `f`, so singular cohomology is a contravariant functor of the space.

For the usual cohomology of `X` with coefficients in a module `M` over a commutative ring `k`,
take `C := ModuleCat k` and `R := k`: then `Cₙ(X; k)` is the free `k`-module on the singular
`n`-simplices, and a cochain is a `k`-valued, respectively `M`-valued, function on them.

## Main declarations

* `TopCat.singularCochainComplex`: the singular cochain complex of a space.
* `TopCat.singularCochainComplexMap`: the cochain map induced by a continuous map.
* `TopCat.singularCohomology` and `TopCat.singularCohomologyMap`: singular cohomology and the
  maps induced on it by continuous maps, with `TauCeti.singularCohomologyFunctor` the resulting
  functor `TopCatᵒᵖ ⥤ ModuleCat k`.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.1.
-/

public section

noncomputable section

open CategoryTheory Limits Opposite

universe w v u

namespace TopCat

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C]
  (R : C) (k : Type*) [Ring k] [Linear k C] (M : C)

/-- The singular cochain complex of a space `X`: in degree `n`, the `k`-module of morphisms from
the singular `n`-chains of `X` with coefficients in `R` to `M`. -/
abbrev singularCochainComplex (X : TopCat.{w}) : CochainComplex (ModuleCat.{v} k) ℕ :=
  ((toSSet.obj X).chainComplex R).linearYonedaObj k M

variable {R k M}

/-- The cochain map on singular cochains induced by a continuous map `f : X ⟶ Y`: precomposition
with the chain map induced by `f`. -/
abbrev singularCochainComplexMap {X Y : TopCat.{w}} (f : X ⟶ Y) :
    Y.singularCochainComplex R k M ⟶ X.singularCochainComplex R k M :=
  (TauCeti.ChainComplex.linearYonedaFunctor k M).map (SSet.chainComplexMap (toSSet.map f) R).op

/-- The degree-`n` component of the cochain map induced by `f` acts by precomposition with the
degree-`n` component of the induced singular chain map. -/
@[simp]
lemma singularCochainComplexMap_f_apply {X Y : TopCat.{w}} (f : X ⟶ Y) (n : ℕ)
    (g : (Y.singularCochainComplex R k M).X n) :
    (singularCochainComplexMap (R := R) (k := k) (M := M) f).f n g =
      (SSet.chainComplexMap (toSSet.map f) R).f n ≫ g := rfl

@[simp]
lemma singularCochainComplexMap_id (X : TopCat.{w}) :
    singularCochainComplexMap (R := R) (k := k) (M := M) (𝟙 X) = 𝟙 _ := by
  simp [singularCochainComplexMap, SSet.chainComplexMap]

@[reassoc]
lemma singularCochainComplexMap_comp {X Y Z : TopCat.{w}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    singularCochainComplexMap (R := R) (k := k) (M := M) (f ≫ g) =
      singularCochainComplexMap g ≫ singularCochainComplexMap f := by
  simp [singularCochainComplexMap, SSet.chainComplexMap]

variable (R k M)

/-- The singular cohomology of a space `X` in degree `n`: the cohomology of the complex of
morphisms from the singular chains of `X` with coefficients in `R` to `M`. -/
protected abbrev singularCohomology (X : TopCat.{w}) (n : ℕ) : ModuleCat.{v} k :=
  (X.singularCochainComplex R k M).homology n

variable {R k M}

/-- The map on singular cohomology induced by a continuous map `f : X ⟶ Y`. -/
protected abbrev singularCohomologyMap {X Y : TopCat.{w}} (f : X ⟶ Y) (n : ℕ) :
    Y.singularCohomology R k M n ⟶ X.singularCohomology R k M n :=
  HomologicalComplex.homologyMap (singularCochainComplexMap f) n

@[simp]
lemma singularCohomologyMap_id (X : TopCat.{w}) (n : ℕ) :
    TopCat.singularCohomologyMap (R := R) (k := k) (M := M) (𝟙 X) n = 𝟙 _ := by
  simp [TopCat.singularCohomologyMap]

@[reassoc]
lemma singularCohomologyMap_comp {X Y Z : TopCat.{w}} (f : X ⟶ Y) (g : Y ⟶ Z) (n : ℕ) :
    TopCat.singularCohomologyMap (R := R) (k := k) (M := M) (f ≫ g) n =
      TopCat.singularCohomologyMap g n ≫ TopCat.singularCohomologyMap f n := by
  simp [TopCat.singularCohomologyMap, singularCochainComplexMap_comp,
    HomologicalComplex.homologyMap_comp]

end TopCat

namespace TauCeti

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C]
  (R : C) (k : Type*) [Ring k] [Linear k C] (M : C)

/-- Singular cohomology in degree `n` as a contravariant functor from topological spaces to
`k`-modules. -/
@[expose, simps]
def singularCohomologyFunctor (n : ℕ) : TopCat.{w}ᵒᵖ ⥤ ModuleCat.{v} k where
  obj X := X.unop.singularCohomology R k M n
  map f := TopCat.singularCohomologyMap f.unop n
  map_comp f g := TopCat.singularCohomologyMap_comp g.unop f.unop n

end TauCeti
