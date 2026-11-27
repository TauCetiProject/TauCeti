/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Linear
public import TauCeti.CategoryTheory.Sites.SheafCohomology.Cech.Coefficients
public import TauCeti.CategoryTheory.Sites.SheafCohomology.Cech.Colimit
public import TauCeti.CategoryTheory.Linear.FunctorCategory

/-!
# Linearity of Čech cohomology in the coefficient presheaf

Let `A` be an `R`-linear category. The Čech complex of a family is linear in the coefficient
presheaf (`TauCeti.CategoryTheory.cechComplexFunctor_linear`) and so is homology in each degree
(`HomologicalComplex.homologyFunctor`), so the Čech cohomology `P ↦ Hⁿ(Č(U, P))` of a fixed
family is an `R`-linear functor of `P`. Since `colim` and the flip of an objectwise linear functor
are linear (`CategoryTheory.Limits.colim_linear`, `CategoryTheory.Functor.flip_linear`), the same
holds for the Čech cohomology of a system of families, the colimit over refinements
(`TauCeti.CategoryTheory.cechCohomology_linear`). In particular, for a sheaf of complex vector
spaces on a topological space, the map induced on cover-colimit Čech cohomology by `c • φ` is
`c` times the map induced by `φ`.

This is the scalar counterpart of the additivity `TauCeti.CategoryTheory.cechCohomology_additive`.
It is needed to compare the maps induced on `H¹` by sheaf morphisms that differ by a scalar
multiple of another, as for the multiplication maps `𝒪_D → 𝒪_E` by `f` and by `f - λ` on a
Riemann surface (Forster, proof of Theorem 17.3).

## Main results

* `TauCeti.CategoryTheory.cechCohomologyDiagram_obj_linear`: fixed-family Čech cohomology is
  linear in the coefficient presheaf.
* `TauCeti.CategoryTheory.cechCohomology_linear`: Čech cohomology for a system of families is
  linear in the coefficient presheaf.

## References

* O. Forster, *Lectures on Riemann Surfaces*, GTM 81, §§12 and 17.
-/

public section

noncomputable section

open CategoryTheory Limits

universe w t v v' u u'

namespace TauCeti.CategoryTheory

variable {C : Type u} [Category.{v} C] [HasFiniteProducts C] {A : Type u'} [Category.{v'} A]
  [Preadditive A] [HasProducts.{w} A] [CategoryWithHomology A]
  {J : Type t} [Preorder J] (E : J → FormalCoproduct.{w} C)
  (hE : ∀ ⦃i j : J⦄, i ≤ j → Nonempty (E j ⟶ E i)) (n : ℕ)
  (R : Type*) [Semiring R] [Linear R A]

/-- Fixed-family Čech cohomology is linear in the coefficient presheaf. -/
instance cechCohomologyDiagram_obj_linear (j : J) :
    ((cechCohomologyDiagram A E hE n).obj j).Linear R :=
  inferInstanceAs (Functor.Linear R (cechComplexFunctor (A := A) (E j).obj ⋙
    HomologicalComplex.homologyFunctor A (ComplexShape.up ℕ) n))

variable [HasColimitsOfShape J A]

/-- **Čech cohomology is linear in the coefficient presheaf.** For an `R`-linear category `A`, the
Čech cohomology for a system of families, the colimit over the system of the fixed-family Čech
cohomologies, is an `R`-linear functor of the coefficient presheaf. -/
instance cechCohomology_linear : (cechCohomology A E hE n).Linear R :=
  inferInstanceAs (Functor.Linear R ((cechCohomologyDiagram A E hE n).flip ⋙ colim))

end TauCeti.CategoryTheory
