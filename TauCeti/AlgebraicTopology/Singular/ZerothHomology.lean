/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Reduced

/-!
# Morphisms out of zeroth singular homology

Zeroth singular homology `H₀(X; R)` is the coproduct of copies of the coefficient object `R`
indexed by the path components of `X` (`TopCat.singularHomology₀Iso`), with the class of a point
`x` (`TauCeti.singularHomology₀Section`) the inclusion indexed by the path component of `x`. So
points joined by a path have the same class (`TauCeti.singularHomology₀Section_eq_of_joined`), and
a morphism out of `H₀(X; R)` is the same as a family of morphisms out of `R`, one for each point,
that is constant along paths: such a family is the family of values on the classes of points of a
morphism (`TauCeti.singularHomology₀Desc`), which is unique by `TauCeti.singularHomology₀_hom_ext`.

## Main definitions and results

* `TauCeti.singularHomology₀Section_eq_of_joined`: points joined by a path have the same class.
* `TauCeti.singularHomology₀Desc`: the morphism out of `H₀(X; R)` with prescribed values on the
  classes of points, for values that are constant along paths.

## References

* A. Hatcher, *Algebraic Topology*, Section 2.1, Proposition 2.7.
-/

public section

noncomputable section

open CategoryTheory Limits AlgebraicTopology

universe w v u

namespace TauCeti

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Preadditive C]
  [CategoryWithHomology C] (R : C) {X : TopCat.{w}}

/-- Points joined by a path have the same class in zeroth singular homology. -/
lemma singularHomology₀Section_eq_of_joined {x y : X} (h : Joined x y) :
    singularHomology₀Section R x = singularHomology₀Section R y := by
  rw [← cancel_mono (X.singularHomology₀Iso R).hom,
    singularHomology₀Section_singularHomology₀Iso_hom,
    singularHomology₀Section_singularHomology₀Iso_hom, ZerothHomotopy.sound h.somePath]

/-- The morphism out of zeroth singular homology with prescribed values `v x` on the classes of
the points `x`, for values that are constant along paths. It is unique by
`TauCeti.singularHomology₀_hom_ext`. -/
def singularHomology₀Desc {Y : C} (v : X → (R ⟶ Y)) (hv : ∀ ⦃x y : X⦄, Path x y → v x = v y) :
    ((singularHomologyFunctor C 0).obj R).obj X ⟶ Y :=
  (X.singularHomology₀Iso R).hom ≫ Sigma.desc (ZerothHomotopy.lift v hv)

@[reassoc (attr := simp)]
lemma singularHomology₀Section_singularHomology₀Desc {Y : C} (v : X → (R ⟶ Y))
    (hv : ∀ ⦃x y : X⦄, Path x y → v x = v y) (x : X) :
    singularHomology₀Section R x ≫ singularHomology₀Desc R v hv = v x := by
  simp [singularHomology₀Desc]

end TauCeti
